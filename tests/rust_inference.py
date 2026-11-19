"""Check native field inference, analyst priority and automatic regeneration.

    python tests/rust_inference.py <executable> <fixture-output.json> <database.bndb>
    python tests/rust_inference.py --cold <database.bndb>
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = 'go-rust.test.rust-layouts'
cold = sys.argv[1] == '--cold'
if cold:
    binary, database = None, Path(sys.argv[2])
else:
    binary, oracle_path, database = map(Path, sys.argv[1:])

with bn.load(str(database if cold else binary)) as view:
    if cold:
        oracle = view.query_metadata(KEY)
    else:
        fixture = json.loads(oracle_path.read_text())
        oracle = fixture['layouts']
        oracle['dispatch'] = fixture.get('dispatch')
        oracle['sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
        view.store_metadata(KEY, oracle)
    functions = {name: view.get_function_at(oracle[name])
                 for name in ['root', 'read', 'forward', 'store', 'user_variable', 'user_prototype']}
    assert all(functions.values())
    dispatch = oracle.get('dispatch')
    local = view.get_function_at(dispatch['local']) if dispatch and dispatch.get('local') else None
    if local and not cold:
        oracle['local_indirect_sites'] = [i.address for i in local.mlil.ssa_form.instructions
            if i.operation in (bn.MediumLevelILOperation.MLIL_CALL_SSA, bn.MediumLevelILOperation.MLIL_TAILCALL_SSA)
            and i.dest.operation != bn.MediumLevelILOperation.MLIL_CONST_PTR]
        view.store_metadata(KEY, oracle)

    def command(name, function=None):
        context = bn.PluginCommandContext(view)
        context.function = function or functions['root']
        bn.PluginCommand.get_valid_list(context)['Go and Rust\\' + name].execute(context)
        view.update_analysis_and_wait()

    def fields(name):
        parameters = list(functions[name].parameter_vars)
        if not parameters:
            return []
        target = getattr(parameters[0].type, 'target', None)
        return [(member.offset, member.type.width) for member in getattr(target, 'members', [])]

    def check():
        count = oracle['count_offset']
        status = oracle['status_offset']
        assert fields('read') == [(count, 8)], fields('read')
        assert fields('forward') == [(count, 8)], fields('forward')
        assert fields('store') == [(status, 4)], fields('store')
        returns = [i for i in functions['read'].hlil.instructions
                   if i.operation == bn.HighLevelILOperation.HLIL_RET]
        assert len(returns) == 1 and len(returns[0].src) == 1
        load = returns[0].src[0]
        assert load.size == 8
        if count:
            assert load.operation == bn.HighLevelILOperation.HLIL_DEREF_FIELD and load.offset == count
        else:
            # A load of the entire observed extent can remain a plain dereference.
            assert load.operation == bn.HighLevelILOperation.HLIL_DEREF
            assert load.src.operation == bn.HighLevelILOperation.HLIL_VAR
        assert any(f'->field_{status:x} =' in str(i) for i in functions['store'].hlil.instructions)
        assert str(list(functions['user_variable'].parameter_vars)[0].type) == 'uint32_t*'
        assert list(functions['user_variable'].parameter_vars)[0].name == 'analyst_variable'
        assert str(list(functions['user_prototype'].parameter_vars)[0].type) == 'uint16_t*'
        assert list(functions['user_prototype'].parameter_vars)[0].name == 'analyst_parameter'

    def check_local():
        expected = view.read_pointer(dispatch['tables'][0] + 3 * view.address_size)
        calls = [i for i in local.mlil.ssa_form.instructions
                 if i.operation in (bn.MediumLevelILOperation.MLIL_CALL_SSA, bn.MediumLevelILOperation.MLIL_TAILCALL_SSA)]
        methods = [i for i in calls if i.dest.operation == bn.MediumLevelILOperation.MLIL_CONST_PTR
                   and i.dest.constant == expected]
        assert methods
        for address in oracle['local_indirect_sites']:
            call = next(i for i in methods if i.address == address)
            assert expected in list(view.get_code_refs_from(address, local))
            assert [i.address for i in call.dest.llils] == [address]
        model = json.loads(view.query_metadata('go-rust.rust.layouts.v1'))
        assert model['status'] == 'Complete'
        source = next(i for i in model['inputs'] if i['key']['address'] == local.start)
        assert {int(address): target for address, target in source['overlaid'].items()} == {
            address: expected for address in oracle['local_indirect_sites']}

    if not cold:
        variable = functions['user_variable']
        variable.create_user_var(list(variable.parameter_vars)[0], 'uint32_t*', 'analyst_variable')
        functions['user_prototype'].set_user_type('uint64_t chosen(uint16_t* analyst_parameter)')
        view.update_analysis_and_wait()
        command('Infer Rust layouts')
    check()
    if cold and local:
        check_local()
    if dispatch:
        dispatch_root = view.get_function_at(dispatch['root'])
        shared = view.get_function_at(dispatch['function'])
        command('Infer Rust layouts', dispatch_root)
        model = json.loads(view.query_metadata('go-rust.rust.layouts.v1'))
        assert model['status'] == 'Complete'
        contexts = [row for row in model['contexts'] if row['function']['address'] == shared.start]
        assert len(contexts) == 2, contexts
        for row in contexts:
            tables = set(row['registers'].values()) & set(dispatch['tables'])
            assert len(tables) == 1, row
            expected = view.read_pointer(tables.pop() + 3 * view.address_size)
            assert [call['target']['address'] for call in row['calls'] if call['indirect']] == [expected]
            assert any(layout['function']['address'] == expected and layout['fields'] for layout in model['layouts'])
        for variable, offset in zip(dispatch_root.parameter_vars, (0, 8), strict=True):
            members = getattr(getattr(variable.type, 'target', None), 'members', [])
            assert [(member.offset, member.type.width) for member in members] == [(offset, 8)]
        shared_layout = next(layout for layout in model['layouts'] if layout['function']['address'] == shared.start)
        assert not any(field['place']['root'] == {'Parameter': 0} for field in shared_layout['fields'])
        assert any(i.dest.operation != bn.MediumLevelILOperation.MLIL_CONST_PTR
                   for i in shared.mlil.ssa_form.instructions
                   if i.operation in (bn.MediumLevelILOperation.MLIL_CALL_SSA, bn.MediumLevelILOperation.MLIL_TAILCALL_SSA))
        command('Stop inferring Rust layouts', dispatch_root)
        check()
    if local:
        if not cold:
            command('Infer Rust layouts', local)
        check_local()
        local.reanalyze(bn.FunctionUpdateType.FullAutoFunctionUpdate)
        view.update_analysis_and_wait()
        check_local()
    if not cold:
        assert view.create_database(str(database))
    if local:
        command('Stop inferring Rust layouts', local)
        assert not any(i.dest.operation == bn.MediumLevelILOperation.MLIL_CONST_PTR
            for i in local.mlil.ssa_form.instructions if i.address in oracle['local_indirect_sites']
            and i.operation in (bn.MediumLevelILOperation.MLIL_CALL_SSA, bn.MediumLevelILOperation.MLIL_TAILCALL_SSA))
        check()
    # An analyst call override removes the pointer argument from one forwarding edge.
    forward = functions['forward']
    calls = [i for i in forward.mlil.instructions
             if i.operation == bn.MediumLevelILOperation.MLIL_CALL]
    assert len(calls) == 1, calls
    address = calls[0].address
    forward.set_call_type_adjustment(address, bn.Type.function(bn.Type.int(8, False), []))
    view.update_analysis_and_wait()
    assert not fields('forward'), fields('forward')
    assert fields('read') == [(oracle['count_offset'], 8)]
    forward.set_call_type_adjustment(address, None)
    view.update_analysis_and_wait()
    check()
    # Removing one selected root retains facts reachable from another root.
    command('Infer Rust layouts', forward)
    command('Stop inferring Rust layouts')
    assert fields('forward') == [(oracle['count_offset'], 8)]
    assert not fields('store')
    command('Stop inferring Rust layouts', forward)
    assert not any(fields(name) for name in functions)
    assert str(list(functions['user_variable'].parameter_vars)[0].type) == 'uint32_t*'
    assert str(list(functions['user_prototype'].parameter_vars)[0].type) == 'uint16_t*'
    assert hashlib.sha256(view.file.raw.read(0, view.file.raw.length)).hexdigest() == oracle['sha256']
print('Native Rust field types, call overrides, multiple roots and cold regeneration passed')

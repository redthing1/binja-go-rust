"""Check helper predicates and memory boundaries on x86-64.

    rustc --edition=2024 -Copt-level=0 -Cdebug-assertions=no -Cpanic=abort -Crelocation-model=static tests/fixtures/rust/predicates.rs -o predicates
    ./predicates > predicates.json
    python tests/rust_predicates.py predicates predicates.json predicates.bndb
    python tests/rust_predicates.py --cold predicates.bndb
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = 'go-rust.test.rust-predicates'
cold = sys.argv[1] == '--cold'
if cold:
    database = Path(sys.argv[2])
else:
    binary, oracle_path, database = map(Path, sys.argv[1:])

with bn.load(str(database if cold else binary)) as view:
    if cold:
        oracle = view.query_metadata(KEY)
    else:
        oracle = json.loads(oracle_path.read_text())
        oracle['sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
        view.store_metadata(KEY, oracle)
    addresses = {name: oracle[name] for name in ['read_scalar', 'read_inverted']}
    addresses.update({name: address for name, address in oracle['helpers'].items() if name.startswith('read_')})
    functions = {name: view.get_function_at(address) for name, address in addresses.items()}
    assert all(functions.values())

    def command(name, function):
        context = bn.PluginCommandContext(view)
        context.function = function
        bn.PluginCommand.get_valid_list(context)['Go and Rust\\' + name].execute(context)
        view.update_analysis_and_wait()

    if not cold:
        for function in functions.values():
            command('Infer Rust layouts', function)

    def payload_guards(name, parameter=0, loaded=True):
        model = json.loads(view.query_metadata('go-rust.rust.layouts.v1'))
        assert model['status'] == 'Complete'
        fields = next(row for row in model['inputs'] if row['key']['address'] == addresses[name])['fields']
        payload = [field for field in fields if field['place'] == {'root': {'Parameter': 0}, 'path': [8]}]
        assert payload
        return [[p for p in field['guards']
                 if p['selector']['place'] == {'root': {'Parameter': parameter}, 'path': [0]}
                 and p['selector']['loaded'] == loaded and p['selector']['width'] == 8
                 and p['values'] == [0]] for field in payload]

    for name in functions:
        guards = payload_guards(name)
        if name in ['read_scalar', 'read_inverted', 'read_memory', 'read_nonboolean', 'read_returned']:
            assert all(any(p['is_in'] == (name != 'read_inverted') for p in row) for row in guards), (name, guards)
            assert '->field_8' in '\n'.join(str(i) for i in functions[name].hlil.instructions)
        else:
            assert all(not row for row in guards), (name, guards)
    assert all(any(p['is_in'] for p in row) for row in payload_guards('read_argument', 1, False))
    # Cached values must still use calls made before the tag store.
    for name, helper in [('read_old', 'tag_is_zero'), ('read_copied', 'load_tag')]:
        il = functions[name].hlil.ssa_form
        node = next(i for i in il.instructions if i.operation == bn.HighLevelILOperation.HLIL_IF).condition
        for _ in range(32):
            if node.operation in [bn.HighLevelILOperation.HLIL_CMP_E, bn.HighLevelILOperation.HLIL_CMP_NE,
                                  bn.HighLevelILOperation.HLIL_AND]:
                node = node.left
            elif node.operation == bn.HighLevelILOperation.HLIL_VAR_SSA:
                node = il.get_ssa_var_definition(node.var).src
            elif node.operation in [bn.HighLevelILOperation.HLIL_ZX, bn.HighLevelILOperation.HLIL_LOW_PART]:
                node = node.src
            else:
                break
        assert node.operation == bn.HighLevelILOperation.HLIL_CALL_SSA and node.src_memory == 0, str(node)
        assert node.dest.constant == oracle['helpers'][helper]
    if not cold:
        assert view.create_database(str(database))
    function = functions['read_scalar']
    call = next(i for i in function.mlil.ssa_form.instructions
                if i.operation == bn.MediumLevelILOperation.MLIL_CALL_SSA)
    function.set_call_type_adjustment(call.address, bn.Type.function(bn.Type.int(1, False), []))
    view.update_analysis_and_wait()
    assert all(not row for row in payload_guards('read_scalar'))
    function.set_call_type_adjustment(call.address, None)
    view.update_analysis_and_wait()
    assert all(row for row in payload_guards('read_scalar'))
    for function in functions.values():
        command('Stop inferring Rust layouts', function)
    assert all('->field_' not in '\n'.join(str(i) for i in function.hlil.instructions)
               for function in functions.values())
    assert hashlib.sha256(view.file.raw.read(0, view.file.raw.length)).hexdigest() == oracle['sha256']
print('Native helper predicates, memory boundaries, call priority and cold replay passed')

"""Check finite tag guards, niche helpers and cached tags on x86-64.

    rustc --edition=2021 -Copt-level=2 -Cdebug-assertions=no -Cpanic=abort -Crelocation-model=static tests/fixtures/rust/variants.rs -o variants
    ./variants > variants.json
    python tests/rust_variants.py variants variants.json variants.bndb
    python tests/rust_variants.py --cold variants.bndb
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = 'go-rust.test.rust-variants'
cold = sys.argv[1] == '--cold'
if cold:
    database = Path(sys.argv[2])
else:
    binary, oracle_path, database = map(Path, sys.argv[1:])
expected = {'read_choice': [0, 1, 2], 'read_unsigned': [0, 1, 2],
            'read_signed': [128, 129], 'read_helper': [253, 254, 255], 'read_niche': [253, 254, 255]}
states = {}


def contains_constant(expression, constant):
    value = expression.possible_values
    return ((value.type == bn.RegisterValueType.ConstantValue and value.value == constant)
            or (value.type == bn.RegisterValueType.InSetOfValues and constant in value.values))


with bn.load(str(database if cold else binary), options={'analysis.linearSweep.autorun': False}) as view:
    if cold:
        oracle = view.query_metadata(KEY)
    else:
        oracle = json.loads(oracle_path.read_text())
        oracle['sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
        view.store_metadata(KEY, oracle)
    functions = {name: view.get_function_at(address) for name, address in oracle.items() if name != 'sha256'}

    def command(name, function):
        context = bn.PluginCommandContext(view)
        context.function = function
        bn.PluginCommand.get_valid_list(context)['Go and Rust\\' + name].execute(context)
        view.update_analysis_and_wait()

    def record(label, missing=(), unbound=(), choice=None, semantics=True):
        view.update_analysis_and_wait()
        model = json.loads(view.query_metadata('go-rust.rust.layouts.v1'))
        assert model['status'] == 'Complete', (label, model['status'])
        for name, values in expected.items():
            layout = next(i for i in model['layouts'] if i['function']['address'] == functions[name].start)
            accesses = [a for a in layout['fields'] if a['place']['path'] == [8, 8]]
            assert accesses, (label, name)
            if name in missing:
                assert all(a.get('uncertain', False) for a in accesses), (label, name, accesses)
            elif name in unbound:
                assert all(a.get('uncertain', False) or a['guards'] for a in accesses), (label, name, accesses)
                assert not any(g['selector']['loaded'] and g['selector']['place'] == {'root': {'Parameter': 0}, 'path': [0]}
                               for a in accesses for g in a['guards']), (label, name, accesses)
            else:
                wanted = choice if name == 'read_choice' and choice is not None else values
                assert all(not a.get('uncertain', False) for a in accesses), (label, name, accesses)
                assert any(g['values'] == wanted and g['is_in'] and g['selector']['loaded']
                           and g['selector']['width'] == 1 and g['selector']['place']['path'] == [0]
                           for a in accesses for g in a['guards']), (label, name, accesses)
        dirty = next(i for i in model['layouts'] if i['function']['address'] == functions['read_dirty'].start)
        assert all(a.get('uncertain', False) for a in dirty['fields'] if len(a['place']['path']) > 1)
        if semantics:
            for name, constant in [('read_choice', 13), ('read_unsigned', 17), ('read_signed', 19),
                                   ('read_helper', 23), ('read_niche', 29), ('read_dirty', 31)]:
                il = functions[name].hlil.ssa_form
                payloads = [payload for index in range(il.get_expr_count()) if (node := il.get_expr(index)) is not None
                            and node.operation == bn.HighLevelILOperation.HLIL_ADD
                            for encoded, payload in ((node.left, node.right), (node.right, node.left))
                            if contains_constant(encoded, constant)]
                assert payloads, (label, name)
                assert all(payload.expr_type is not None and payload.expr_type.type_class == bn.TypeClass.IntegerTypeClass
                           for payload in payloads), (label, name, [str(payload) for payload in payloads])
        states[label] = model
        return model

    if not cold:
        for name in ('root', 'read_dirty'):
            command('Infer Rust layouts', functions[name])
    baseline = record('initial')
    functions['root'].reanalyze(bn.FunctionUpdateType.FullAutoFunctionUpdate)
    record('reanalyzed')
    if not cold:
        assert view.create_database(str(database))

    helper = functions['high_tag']
    code = view.read(helper.start, 1)
    view.write(helper.start, b'\xc3')
    record('helper-edited', unbound=('read_helper',))
    view.write(helper.start, code)
    record('helper-restored')

    selected = next(i for i in baseline['inputs'] if i['key']['address'] == functions['read_choice'].start)
    table = next((r for r in selected['readonly'] if r['end'] - r['start'] in (1024, 2048)), None)
    if table is not None:
        width = (table['end'] - table['start']) // 256
        slot = table['start'] + 10 * width
        original = view.read(slot, width)
        view.write(slot, view.read(table['start'], width))
        record('additional-byte-case', choice=[0, 1, 2, 10])
        view.write(slot, original)
        record('table-restored')
        view.define_user_data_var(table['end'] - 1, 'volatile uint8_t')
        record('volatile-table-tail', missing=('read_choice',))
        view.undefine_user_data_var(table['end'] - 1)
        record('table-type-restored')

    function = functions['read_unsigned']
    variable = list(function.parameter_vars)[0]
    chosen = view.parse_type_string('struct AnalystPacket { uint8_t tag; uint64_t word; }*')[0]
    function.create_user_var(variable, chosen, 'packet')
    function.comment = 'Keep this annotation.'
    record('analyst-variable', semantics=False)
    assert variable.name == 'packet' and variable.type == chosen
    for name in ('root', 'read_dirty'):
        command('Stop inferring Rust layouts', functions[name])
    assert 'go-rust.rust.layouts.v1' not in view.auto_metadata
    assert variable.name == 'packet' and variable.type == chosen
    assert function.comment == 'Keep this annotation.'
    function.delete_user_var(variable)
    view.update_analysis_and_wait()
    for name in ('root', 'read_dirty'):
        command('Infer Rust layouts', functions[name])
    record('selected-again')
    for name in ('root', 'read_dirty'):
        command('Stop inferring Rust layouts', functions[name])
    assert 'go-rust.rust.layouts.v1' not in view.auto_metadata
    assert hashlib.sha256(view.file.raw.read(0, view.file.raw.length)).hexdigest() == oracle['sha256']

print('Finite tag guards, niche helpers, stale tags, withdrawal and analyst priority pass')

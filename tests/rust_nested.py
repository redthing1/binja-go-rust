"""Check nested pointers, return aliases and declaration priority on x86-64.

    rustc --edition=2024 -Copt-level=2 -Crelocation-model=static tests/fixtures/rust/nested.rs -o nested
    ./nested > nested.json
    python tests/rust_nested.py nested nested.json nested.bndb
    python tests/rust_nested.py --cold nested.bndb
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = 'go-rust.test.rust-nested'
cold = sys.argv[1] == '--cold'
if cold:
    database = Path(sys.argv[2])
else:
    binary, oracle_path, database = map(Path, sys.argv[1:])


def fields(ty):
    return [(m.offset, m.type.width, fields(m.type))
            for m in getattr(getattr(ty, 'target', None), 'members', [])]


with bn.load(str(database if cold else binary)) as view:
    if cold:
        oracle = view.query_metadata(KEY)
    else:
        oracle = json.loads(oracle_path.read_text())
        oracle['sha256'] = hashlib.sha256(binary.read_bytes()).hexdigest()
        view.store_metadata(KEY, oracle)
    names = ['root', 'nested', 'from_alias', 'from_loaded', 'from_dirty', 'from_ambiguous', 'alias']
    functions = {name: view.get_function_at(oracle[name]) for name in names}
    assert all(functions.values())

    def command(name):
        context = bn.PluginCommandContext(view)
        context.function = functions['root']
        bn.PluginCommand.get_valid_list(context)['Go and Rust\\' + name].execute(context)
        view.update_analysis_and_wait()

    def text(name):
        return '\n'.join(str(i) for i in functions[name].hlil.instructions)

    if not cold:
        command('Infer Rust layouts')
    assert json.loads(view.query_metadata('go-rust.rust.layouts.v1'))['status'] == 'Complete'
    outer, inner, leaf = oracle['offsets']
    assert outer == inner == leaf == 8  # The owned assembly accesses these exact slots.
    for name in ['nested', 'from_loaded']:
        assert fields(list(functions[name].parameter_vars)[0].type) == [(outer, 8, [(inner, 8, [(leaf, 8, [])])])]
    assert fields(list(functions['from_dirty'].parameter_vars)[0].type) == [(outer, 8, [])]
    assert all(not fields(v.type) for v in functions['from_ambiguous'].parameter_vars)
    assert '->field_8' in text('from_dirty') and '->field_8' in text('from_ambiguous')

    if not cold:
        view.define_user_type('ChosenLeaf', bn.Type.structure(members=[
            (bn.Type.int(8, False), 'prefix'), (bn.Type.int(8, False), 'answer')]))
        functions['alias'].set_user_type('ChosenLeaf* alias(ChosenLeaf* chosen)')
        view.update_analysis_and_wait()
    assert '->answer' in text('from_alias'), text('from_alias')
    # A primitive pointer declaration must also take priority over an observed record.
    functions['alias'].set_user_type('uint32_t* alias(uint32_t* chosen)')
    view.update_analysis_and_wait()
    assert '->field_' not in text('from_alias'), text('from_alias')
    anonymous = bn.Type.pointer(view.arch, bn.Type.structure(members=[
        (bn.Type.int(8, False), 'prefix'), (bn.Type.int(8, False), 'inline_answer')]))
    functions['alias'].set_user_type(bn.Type.function(anonymous, [anonymous]))
    view.update_analysis_and_wait()
    assert '->inline_answer' in text('from_alias'), text('from_alias')
    functions['alias'].set_user_type('ChosenLeaf* alias(ChosenLeaf* chosen)')
    view.update_analysis_and_wait()
    assert '->answer' in text('from_alias'), text('from_alias')
    if not cold:
        assert view.create_database(str(database))
    command('Stop inferring Rust layouts')
    for name in ['nested', 'from_loaded', 'from_dirty', 'from_ambiguous']:
        assert all(not fields(v.type) for v in functions[name].parameter_vars)
        assert '->field_' not in text(name), text(name)
    assert '->answer' in text('from_alias'), text('from_alias')
    assert hashlib.sha256(view.file.raw.read(0, view.file.raw.length)).hexdigest() == oracle['sha256']
print('Native nested pointers, returned aliases, analyst declarations and withdrawal passed')

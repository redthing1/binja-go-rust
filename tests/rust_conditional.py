"""Check conditional fields and copied-value semantics on x86-64.

    rustc --edition=2024 -Copt-level=2 -Crelocation-model=static -Cpanic=abort tests/fixtures/rust/conditional.rs -o conditional
    ./conditional > conditional.json
    python tests/rust_conditional.py conditional conditional.json conditional.bndb
    python tests/rust_conditional.py --cold conditional.bndb
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = 'go-rust.test.rust-conditional'
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
    names = ['root', 'read_choice', 'read_raw', 'read_option', 'read_nullable', 'read_dirty', 'read_word_tag']
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
    for name in ['read_choice', 'read_raw']:
        il = functions[name].hlil
        widths = {node.size for i in range(il.get_expr_count()) if (node := il.get_expr(i))
                  and node.operation == bn.HighLevelILOperation.HLIL_DEREF_FIELD
                  and node.offset == oracle['payload_offset']}
        assert widths == {4, 8}, (name, widths, text(name))
    for name in ['read_option', 'read_nullable']:
        assert '->field_8' in text(name), text(name)
    function = functions['read_word_tag']
    slot = next(m for m in list(function.parameter_vars)[0].type.target.members
                if m.offset == oracle['payload_offset'])
    assert slot.type.type_class == bn.TypeClass.IntegerTypeClass, str(slot.type)
    returns = [i.src[0] for i in function.hlil.instructions
               if i.operation == bn.HighLevelILOperation.HLIL_RET]
    addition = next(i for i in returns if i.operation == bn.HighLevelILOperation.HLIL_ADD)
    assert addition.left.expr_type.type_class == bn.TypeClass.IntegerTypeClass
    pointer = next(i for i in returns if i.operation == bn.HighLevelILOperation.HLIL_DEREF_FIELD)
    assert pointer.src.expr_type.type_class == bn.TypeClass.PointerTypeClass
    # Typing the parameter must not replace a cached old tag with a later field read.
    il = functions['read_dirty'].hlil.ssa_form
    branch = next(i for i in il.instructions if i.operation == bn.HighLevelILOperation.HLIL_IF)
    value = branch.condition.left
    assert value.operation == bn.HighLevelILOperation.HLIL_VAR_SSA, str(value)
    for _ in range(16):
        if value.operation != bn.HighLevelILOperation.HLIL_VAR_SSA:
            break
        value = il.get_ssa_var_definition(value.var).src
    assert value.operation == bn.HighLevelILOperation.HLIL_DEREF_SSA and value.src_memory == 0, str(value)
    assert '->field_8' in text('read_dirty'), text('read_dirty')
    if not cold:
        assert view.create_database(str(database))
    function = functions['read_raw']
    parameter = list(function.parameter_vars)[0]
    function.create_user_var(parameter, 'uint8_t*', 'analyst_record')
    view.update_analysis_and_wait()
    assert parameter.name == 'analyst_record' and str(parameter.type) == 'uint8_t*'
    assert '->field_' not in text('read_raw'), text('read_raw')
    command('Stop inferring Rust layouts')
    assert all('->field_' not in text(name) for name in names)
    assert parameter.name == 'analyst_record' and str(parameter.type) == 'uint8_t*'
    assert hashlib.sha256(view.file.raw.read(0, view.file.raw.length)).hexdigest() == oracle['sha256']
print('Native conditional payloads, copied-value semantics, analyst priority and withdrawal passed')

"""Check native word-call typing with Binary Ninja's Python on x86-64 Linux.

Build: cc -nostdlib -no-pie -Wl,-e,root tests/fixtures/rust/calls.S -o calls
Run:   python tests/rust_calls.py calls calls.bndb [--cold]
"""

from pathlib import Path
import subprocess
import sys
import tempfile

import binaryninja as bn
from binaryninja.warp import WarpContainer, WarpProcessor, WARPProcessorIncludedFunctions

binary, database = map(Path, sys.argv[1:3])
cold = '--cold' in sys.argv
options = {'analysis.linearSweep.autorun': False, 'analysis.warp.matcher': False,
           'analysis.warp.apply': False}
assert subprocess.run([str(binary.resolve())], check=False).returncode == 51

with tempfile.TemporaryDirectory(prefix='rust-calls-') as directory:
    if not cold:
        with bn.load(str(binary), options=options) as source:
            function = source.get_functions_by_name('control')[0]
            function.set_user_type(bn.Type.function(bn.Type.int(8, False), [bn.FunctionParameter(
                bn.Type.int(8, False), 'value', bn.ValueLocation.parse('r8', function.arch))],
                calling_convention=function.calling_convention))
            tag = source.create_tag_type('WARP: Selected Function', 'S')
            function.add_tag(tag.name, '')
            source.update_analysis_and_wait()
            processor = WarpProcessor(included_functions=
                WARPProcessorIncludedFunctions.WARPProcessorIncludedFunctionsSelected)
            processor.add_binary_view(source)
            signatures = processor.start()
            assert signatures
            path = Path(directory) / 'word.warp'
            path.write_bytes(bytes(signatures.to_data_buffer()))
            assert WarpContainer.add('rust-calls-test').add_source(str(path))

    with bn.load(str(database if cold else binary), options=options) as view:
        root, callee = [view.get_functions_by_name(name)[0] for name in ('root', 'control')]
        site = next(i.address for i in root.llil.instructions
                    if i.operation == bn.LowLevelILOperation.LLIL_CALL)
        original_type = str(callee.type)

        def command(name):
            context = bn.PluginCommandContext(view)
            context.function = root
            bn.PluginCommand.get_valid_list(context)['Go and Rust\\' + name].execute(context)
            view.update_analysis_and_wait()

        def arguments(expected):
            view.update_analysis_and_wait()
            calls = [i for i in root.mlil.ssa_form.instructions if i.address == site
                     and i.operation == bn.MediumLevelILOperation.MLIL_CALL_SSA]
            assert len(calls) == 1
            assert [p.value.value for p in calls[0].params] == [expected], str(calls[0])

        if not cold:
            command('Infer Rust layouts')
        arguments(51)
        assert str(callee.type) == original_type
        root.reanalyze(bn.FunctionUpdateType.FullAutoFunctionUpdate)
        arguments(51)
        if not cold:
            assert view.create_database(str(database))

        original = view.read(callee.start, 16)
        for code in ['4831c0c3', '4489c0c3', '66480f7ec74c89c0c3', '4889c74c89c0c3']:
            replacement = bytes.fromhex(code)
            view.write(callee.start, replacement + original[len(replacement):])
            view.update_analysis_and_wait()
            assert root.get_call_type_adjustment(site) is None
            view.write(callee.start, original)
            arguments(51)

        automatic = root.get_call_type_adjustment(site)
        assert automatic is not None
        copied = automatic.mutable_copy()
        copied.pure = not bool(automatic.pure)
        copied = copied.immutable_copy()
        root.set_call_type_adjustment(site, copied)
        arguments(51)
        assert root.get_call_type_adjustment(site) == copied
        root.set_call_type_adjustment(site, None)
        arguments(51)

        analyst = bn.Type.function(bn.Type.int(8, False), [bn.FunctionParameter(
            bn.Type.int(8, False), 'chosen', bn.ValueLocation.parse('rdi', root.arch))],
            calling_convention=callee.calling_convention)
        root.set_call_type_adjustment(site, analyst)
        arguments(17)
        command('Stop inferring Rust layouts')
        arguments(17)
        assert root.get_call_type_adjustment(site).parameters[0].name == 'chosen'
        root.set_call_type_adjustment(site, None)
        command('Infer Rust layouts')
        arguments(51)
        command('Stop inferring Rust layouts')
        assert root.get_call_type_adjustment(site) is None
        assert view.file.raw.read(0, view.file.raw.length) == binary.read_bytes()

print('Native word-call typing, withdrawal, analyst priority and original bytes pass')

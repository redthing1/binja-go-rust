"""Exercise native WARP evidence with the Rust fixture and temporary signatures.

Run with Binary Ninja's Python after building and executing the static fixture:
    python tests/rust_library.py <executable> <fixture-output.json> [--disabled]
"""

import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

import binaryninja as bn
from binaryninja import _binaryninjacore as core
from binaryninja.warp import WarpContainer, WarpFunction, WarpProcessor, WARPProcessorIncludedFunctions


class Reports(bn.InteractionHandler):
    def __init__(self):
        super().__init__()
        self.contents = []

    def show_plain_text_report(self, _view, _title, contents):
        self.contents.append(contents.decode() if isinstance(contents, bytes) else contents)


binary, oracle_path = map(Path, sys.argv[1:3])
oracle = json.loads(oracle_path.read_text())
address = oracle['library']
original = hashlib.sha256(binary.read_bytes()).hexdigest()
command = 'Go and Rust\\Inspect Rust library evidence'
with tempfile.TemporaryDirectory(prefix='rust-library-') as directory:
    with bn.load(str(binary)) as view:
        reports = Reports()
        reports.register()
        function = view.get_function_at(address)
        context = bn.PluginCommandContext(view)
        context.function = function
        if '--disabled' in sys.argv:
            settings = bn.Settings()
            enabled = settings.get_bool('corePlugins.warp')
            try:
                settings.set_bool('corePlugins.warp', False)
                assert command not in bn.PluginCommand.get_valid_list(context)
            finally:
                settings.set_bool('corePlugins.warp', enabled)
            assert hashlib.sha256(binary.read_bytes()).hexdigest() == original
            print('WARP-disabled optional adapter passed')
            raise SystemExit(0)

        def inspect():
            before = (function.name, function.comment, str(function.type))
            bn.PluginCommand.get_valid_list(context)[command].execute(context)
            assert before == (function.name, function.comment, str(function.type))
            return reports.contents[-1]

        inspect()
        container = WarpContainer.add('native-library-test')
        selected = None
        for index, declaration in enumerate([
            'uint64_t signature_one(uint64_t value)',
            'uint32_t signature_two(void* data)',
        ]):
            with bn.load(str(binary)) as source:
                control = source.get_function_at(address)
                control.name = f'signature_{"one" if index == 0 else "two"}'
                control.set_user_type(declaration)
                tag = source.create_tag_type('WARP: Selected Function', 'S')
                control.add_tag(tag.name, '')
                source.update_analysis_and_wait()
                processor = WarpProcessor(included_functions=
                    WARPProcessorIncludedFunctions.WARPProcessorIncludedFunctionsSelected)
                processor.add_binary_view(source)
                signatures = processor.start()
                assert signatures
                path = Path(directory) / f'signature-{index}.warp'
                path.write_bytes(bytes(signatures.to_data_buffer()))
                assert container.add_source(str(path))
                if index == 0:
                    selected = next(f for chunk in signatures.chunks for f in chunk.functions
                                    if f.name == 'signature_one')
        function.name = 'analyst_library'
        function.comment = 'Keep this annotation.'
        function.set_user_type('uint64_t analyst_library(uint64_t input)')
        view.update_analysis_and_wait()
        text = inspect()
        assert 'signature_one' in text and 'signature_two' in text, text
        assert 'Type: uint64_t' in text and 'Type: uint32_t' in text, text
        assert 'Current support:' in text
        assert 'Referenced data and unique Rust source identity remain unverified.' in text
        def support(text):
            return {int(matched) for matched in re.findall(r'Current support: (\d+) of', text)}

        before_support = support(text)
        assert before_support and min(before_support) > 0, text
        neighbor = view.get_function_at(view.get_next_function_start_after(function.start))
        assert neighbor
        original_name = neighbor.name
        try:
            neighbor.name = 'analyst_neighbor'
            view.update_analysis_and_wait()
            changed = inspect()
            assert support(changed) and max(support(changed)) < min(before_support), changed
        finally:
            neighbor.name = original_name
            view.update_analysis_and_wait()
        assert support(inspect()) == before_support
        selected.apply(function)
        view.update_analysis_and_wait()
        text = inspect()
        assert 'Recorded WARP match:' in text, text
        assert function.name == 'analyst_library' and function.comment == 'Keep this annotation.'
        assert function.return_type.width == 8
        assert [p.name for p in function.type.parameters] == ['input']
        WarpFunction.remove_matched(function)
        function.reanalyze(bn.FunctionUpdateType.FullAutoFunctionUpdate)
        view.update_analysis_and_wait()
        assert 'Recorded WARP match:' not in inspect()
        assert function.name == 'analyst_library' and function.return_type.width == 8
        view.set_analysis_hold(True)
        function.mark_updates_required(bn.FunctionUpdateType.FullAutoFunctionUpdate)
        assert core.BNIsFunctionUpdateNeeded(function.handle)
        assert 'analysis is unavailable or pending' in inspect()
        view.set_analysis_hold(False)
        view.update_analysis_and_wait()
        assert 'analysis is unavailable or pending' not in inspect()
assert hashlib.sha256(binary.read_bytes()).hexdigest() == original
print('Native WARP candidate ambiguity, types, match removal and analyst priority passed')

"""Exercise an installed native plugin with the compiled Go fixture.

Run with Binary Ninja's Python environment:
    python tests/go_integration.py <executable> <fixture-output.json> <database.bndb>
Run the cold check in a new process:
    python tests/go_integration.py --cold <database.bndb>
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

NAMES = "go-rust.go.type-names.v1"


class Reports(bn.InteractionHandler):
    def __init__(self):
        super().__init__()
        self.contents = []

    def show_plain_text_report(self, view, title, contents):
        self.contents.append(contents.decode() if isinstance(contents, bytes) else contents)


def analyze(view):
    context = bn.PluginCommandContext(view)
    bn.PluginCommand.get_valid_list(context)["Go and Rust\\Analyze Go metadata"].execute(context)
    view.update_analysis_and_wait()


def record(view):
    names = json.loads(view.query_metadata(NAMES))
    matches = [(identity, view.get_type_by_id(identity)) for identity, name in names.items()
               if len(name) == 2 and name[0] == "go" and name[1].startswith("main.Record")]
    assert len(matches) == 1, matches
    return matches[0]


if sys.argv[1] == "--cold":
    with bn.load(sys.argv[2]) as view:
        assert str(view.get_type_name_by_id(record(view)[0])) == "analyst_record"
        assert view.get_functions_by_name("analyst_score")
        assert view.get_functions_by_name("analyst_automatic_score")
        assert view.get_type_by_name(["go", "main.Record"]).width == 1
        assert view.query_metadata("go-rust.test.record-layout") == list(record(view)[1].members[i].offset for i in range(3))
    print("cold persistence passed")
else:
    binary, oracle_path, database = map(Path, sys.argv[1:])
    original_hash = hashlib.sha256(binary.read_bytes()).hexdigest()
    oracle = json.loads(oracle_path.read_text())
    with bn.load(str(binary), options={"analysis.mode": "basic"}, update_analysis=False) as view:
        view.define_user_type(["go", "main.Record"], bn.Type.int(1, False))
        view.update_analysis_and_wait()
        record(view)  # Metadata is available after ordinary initial analysis.
        analyze(view)
        identity, ty = record(view)
        assert (ty.width, ty.alignment) == (oracle["size"], oracle["alignment"])
        assert [member.offset for member in ty.members] == oracle["fields"]
        assert view.get_type_by_name(["go", "main.Record"]).width == 1
        first_names = json.loads(view.query_metadata(NAMES))
        analyze(view)
        assert first_names == json.loads(view.query_metadata(NAMES))
        reports = Reports()
        reports.register()
        source_context = bn.PluginCommandContext(view)
        source_context.address = view.get_functions_by_name("main.score")[0].start
        bn.PluginCommand.get_valid_list(source_context)["Go and Rust\\Show Go source information"].execute(source_context)
        assert reports.contents and "main.score" in reports.contents[-1] and ".go:" in reports.contents[-1]
        scorer = next(identity for identity, name in first_names.items() if name == ["go", "main.Scorer"])
        loaded_before = [(segment.start, view.read(segment.start, segment.length)) for segment in view.segments if segment.readable]
        address = int(scorer.split(":")[-1], 16) + view.start - view.original_image_base
        saved = view.read(address, view.address_size)
        view.write(address, (1).to_bytes(view.address_size, "little"))
        view.update_analysis_and_wait()
        assert view.get_type_by_id(scorer) is None
        view.write(address, saved)
        assert view.read(address, view.address_size) == saved
        assert all(view.read(start, len(data)) == data for start, data in loaded_before), "unexpected executable byte changes"
        view.update_analysis_and_wait()
        assert view.get_type_by_id(scorer) is not None, (scorer, json.loads(view.query_metadata(NAMES)).get(scorer))
        view.rename_type(view.get_type_name_by_id(identity), "analyst_record")
        functions = view.get_functions_by_name("main.score")
        assert len(functions) == 1, functions
        functions[0].name = "analyst_score"
        method = view.get_functions_by_name("main.(*Record).Score")[0]
        view.undefine_auto_symbol(method.symbol)
        view.define_auto_symbol(bn.Symbol(bn.SymbolType.FunctionSymbol, method.start, "analyst_automatic_score"))
        analyze(view)
        analyze(view)
        assert str(view.get_type_name_by_id(identity)) == "analyst_record"
        assert view.get_functions_by_name("analyst_score")
        assert view.get_functions_by_name("analyst_automatic_score")
        raw = view.file.raw
        header = raw.read(0, 4)
        raw.write(0, b"\0ELF")
        view.update_analysis_and_wait()
        assert view.get_type_by_id(scorer) is None
        assert str(view.get_type_name_by_id(identity)) == "analyst_record"
        assert view.get_functions_by_name("analyst_score")
        assert view.get_functions_by_name("analyst_automatic_score")
        raw.write(0, header)
        view.update_analysis_and_wait()
        assert view.get_type_by_id(scorer) is not None
        assert view.get_functions_by_name("analyst_score")
        assert view.get_functions_by_name("analyst_automatic_score")
        view.store_metadata("go-rust.test.record-layout", oracle["fields"])
        assert view.create_database(str(database))
    assert hashlib.sha256(binary.read_bytes()).hexdigest() == original_hash
    print("layout, source, damaged metadata, repeat run, analyst edits and original bytes passed")

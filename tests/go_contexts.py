"""Exercise shared Go generic bodies with two concrete dictionaries.

    python tests/go_contexts.py <executable> <database.bndb>
    python tests/go_contexts.py --cold <database.bndb>
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

INPUT = "go-rust.go.context-input.v1"
RESULT = "go-rust.go.contexts.v1"
COMMAND = "Go and Rust\\Show Go dictionary contexts"


class Reports(bn.InteractionHandler):
    def __init__(self):
        super().__init__()
        self.contents = []

    def show_plain_text_report(self, view, title, contents):
        self.contents.append(contents.decode() if isinstance(contents, bytes) else contents)


def contexts(view):
    view.update_analysis_and_wait()
    model = json.loads(view.query_metadata(INPUT))
    result = json.loads(view.query_metadata(RESULT))
    assert not result["truncated"] and result["unavailable"] == 0
    selected = {row["dictionary"]: row for row in result["contexts"]
                if model["functions"][str(row["function"])].startswith("main.generic[")}
    assert len(selected) == 2, selected
    assert len({row["function"] for row in selected.values()}) == 1
    return selected, model


def allocation(row):
    calls = [call for call in row["calls"] if call["allocation_type"] is not None]
    assert len(calls) == 1, row
    return calls[0]


cold = sys.argv[1] == "--cold"
binary, database = (None, Path(sys.argv[2])) if cold else map(Path, sys.argv[1:])
original = hashlib.sha256(binary.read_bytes()).hexdigest() if binary else None
with bn.load(str(database if cold else binary)) as view:
    before, model = contexts(view)
    descriptors = {allocation(row)["allocation_type"] for row in before.values()}
    assert len(descriptors) == 2
    for row in before.values():
        function = view.get_function_at(row["function"])
        assert function.get_call_type_adjustment(allocation(row)["address"]) is None
        assert any(call["indirect"] and call["target"] is not None for call in row["calls"])
        assert any(call["dictionary"] is not None for call in row["calls"])
    identity = next(identity for identity in model["types"].values()
                    if str(view.get_type_name_by_id(identity)) in ("go::main.First", "analyst_scalar"))
    function = view.get_function_at(next(iter(before.values()))["function"])
    if not cold:
        view.rename_type(view.get_type_name_by_id(identity), "analyst_scalar")
        function.name = "analyst_generic"
    else:
        assert function.name == "analyst_generic"

    binding, row = next(iter(before.items()))
    read, = [read for read in row["reads"] if "allocation type" in read["uses"]]
    address = binding + read["offset"]
    saved = view.read(address, 8)
    view.write(address, function.start.to_bytes(8, "little"))
    damaged, _ = contexts(view)
    assert all(call["allocation_type"] is None for call in damaged[binding]["calls"])
    for other in before.keys() - {binding}:
        assert damaged[other] == before[other]
    view.write(address, saved)
    restored, _ = contexts(view)
    assert restored == before
    assert view.read(address, 8) == saved
    assert function.name == "analyst_generic"
    assert str(view.get_type_name_by_id(identity)) == "analyst_scalar"
    reports = Reports()
    reports.register()
    command_context = bn.PluginCommandContext(view)
    command_context.address = function.start
    bn.PluginCommand.get_valid_list(command_context)[COMMAND].execute(command_context)
    assert "analyst_scalar" in reports.contents[-1] and "main.Second" in reports.contents[-1]
    assert reports.contents[-1].count("allocation ->") == 2
    if not cold:
        assert view.create_database(str(database))
if binary:
    assert hashlib.sha256(binary.read_bytes()).hexdigest() == original
    with bn.load(str(binary), options={"analysis.mode": "basic"}) as view:
        assert COMMAND not in bn.PluginCommand.get_valid_list(bn.PluginCommandContext(view))
print("shared bodies, concrete contexts, slot damage, analyst names and original bytes passed")

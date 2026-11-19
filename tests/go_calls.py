"""Check allocation calls using a compiled amd64 Go fixture.

    python tests/go_calls.py <executable> <database.bndb>
    python tests/go_calls.py --cold <database.bndb>
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn

KEY = "go-rust.test.allocation-sites"


def calls(function):
    return [instruction for instruction in function.mlil.instructions
            if instruction.operation == bn.MediumLevelILOperation.MLIL_CALL]


def pointees(call):
    return [getattr(getattr(value.type, "target", None), "type_id", None)
            for value in call.output]


def current(view, sites):
    view.update_analysis_and_wait()
    results = []
    for owner, address in sites:
        function = view.get_function_at(owner)
        assert not function.analysis_skipped
        matches = [call for call in calls(function) if call.address == address]
        assert len(matches) == 1, (owner, address, matches)
        results.append(matches[0])
    return results


cold = sys.argv[1] == "--cold"
binary, database = (None, Path(sys.argv[2])) if cold else map(Path, sys.argv[1:])
source_hash = hashlib.sha256(binary.read_bytes()).hexdigest() if binary else None
with bn.load(str(database if cold else binary)) as view:
    names = json.loads(view.query_metadata("go-rust.go.type-names.v1"))
    identity = next(identity for identity, name in names.items() if name == ["go", "main.Record"])
    if cold:
        sites = view.query_metadata(KEY)
    else:
        sites = []
        for name in ("main.allocate", "main.records"):
            function, = view.get_functions_by_name(name)
            allocations = [call for call in calls(function) if identity in pointees(call)]
            assert len(allocations) == 1, (name, allocations)
            sites.append((function.start, allocations[0].address))
            if name == "main.allocate":
                lines = [str(line) for line in function.hlil.instructions]
                assert any("Count" in line for line in lines), (name, lines)
        location = bn.ValueLocation([bn.ValueLocationComponent(
            bn.ArchitectureVariable.reg(view.arch, "rax"), 0, 8)])
        override = bn.Type.function(bn.ReturnValue(bn.Type.int(8, False), location), [],
                                    view.platform.default_calling_convention)
        view.get_function_at(sites[0][0]).set_call_type_adjustment(sites[0][1], override)

    automatic = current(view, sites)
    assert len(automatic[0].params) == 0  # Analyst declaration has priority.
    assert len(automatic[1].params) == 3 and identity in pointees(automatic[1])
    descriptor = int(identity.rsplit(":", 1)[1], 16) + view.start - view.original_image_base
    original = view.read(descriptor, 8)
    view.write(descriptor, (1).to_bytes(8, "little"))
    damaged = current(view, sites)
    assert len(damaged[0].params) == 0
    assert identity not in pointees(damaged[1])
    view.write(descriptor, original)
    restored = current(view, sites)
    assert len(restored[0].params) == 0
    assert identity in pointees(restored[1]) and len(restored[1].params) == 3
    assert view.read(descriptor, 8) == original
    if not cold:
        view.store_metadata(KEY, sites)
        assert view.create_database(str(database))
if binary:
    assert hashlib.sha256(binary.read_bytes()).hexdigest() == source_hash
print("allocation types, withdrawal, restoration and analyst priority passed")

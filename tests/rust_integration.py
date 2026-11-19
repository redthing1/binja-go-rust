"""Inspect the compiled Rust fixture using its runtime header addresses.

Build the fixture as a static executable, then run with Binary Ninja's Python:
    python tests/rust_integration.py <executable> <fixture-output.json>
"""

import hashlib
import json
from pathlib import Path
import sys

import binaryninja as bn


class Reports(bn.InteractionHandler):
    def __init__(self):
        super().__init__()
        self.contents = []

    def show_plain_text_report(self, view, title, contents):
        self.contents.append(contents.decode() if isinstance(contents, bytes) else contents)


binary, oracle_path = map(Path, sys.argv[1:])
original = hashlib.sha256(binary.read_bytes()).hexdigest()
oracle = json.loads(oracle_path.read_text())
with bn.load(str(binary), options={"analysis.mode": "basic"}) as view:
    reports = Reports()
    reports.register()
    context = bn.PluginCommandContext(view)
    command = "Go and Rust\\Inspect Rust structure"
    context.address = oracle["vtable"]
    bn.PluginCommand.get_valid_list(context)[command].execute(context)
    assert f"size {oracle['size']}, alignment {oracle['alignment']}" in reports.contents[-1]
    assert "Drop entry: null" in reports.contents[-1]
    assert "method count is unknown" in reports.contents[-1]
    context.address = oracle["span"]
    bn.PluginCommand.get_valid_list(context)[command].execute(context)
    assert "native Rust span" in reports.contents[-1]
    assert "does not distinguish str from a byte slice" in reports.contents[-1]
assert hashlib.sha256(binary.read_bytes()).hexdigest() == original
print("Rust span, nullable-drop vtable, single method and original bytes passed")

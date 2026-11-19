# Development

Build and install the plugin as described in the [README](../README.md#install).
The Binary Ninja Rust SDK is pinned in `Cargo.toml` and `Cargo.lock`; use a core
with the matching ABI.

## Structure

| Directory | Responsibility |
| --- | --- |
| `src/binja/` | Shared Binary Ninja adapters for workflows, IL queries, call types, memory and WARP. |
| `src/go/` | Executable snapshots, metadata validation, type and symbol recovery, ABI layouts, runtime calls and dictionary contexts. |
| `src/rust/` | Structure inspection, field-layout inference and library evidence. |
| `tests/` | Headless integration checks and source fixtures. |

`src/lib.rs` registers workflows and commands. The language modules own their
analysis and annotations; shared core API access belongs in `src/binja/`.

Go analysis reads a snapshot of the current view, parses metadata with unstrip,
validates the type graph and publishes automatic symbols and types. Function
workflows use that model to apply call types and collect dictionary contexts.
`values.rs` and `effects.rs` track concrete values and the evidence needed to
retain them across calls.

Rust's `ssa/` extracts accesses, call contexts and control conditions from
Binary Ninja's intermediate language. `layout.rs` combines those observations;
`inference.rs` manages roots, refresh and publication. `library.rs` connects
optional WARP evidence to verified call behavior.

Keep evidence collection separate from publication. Associate derived facts
with their current inputs, bound traversal, and withdraw automatic annotations
when their evidence no longer holds. Preserve explicit analyst edits.

## Checks

With the build prerequisites available:

```sh
cargo fmt --check
BINARYNINJADIR=/path/to/binaryninja cargo test --locked --lib
```

Integration scripts require the installed native plugin and a Python environment
that can `import binaryninja` and open binaries headlessly. The following examples
use a Linux amd64 host, Go 1.25–1.27, and `rustc` with edition 2024 support.
Run them from the repository root.

### Go metadata

Build and execute the fixture to record its actual type layout, then compare
recovery against that result:

```sh
mkdir -p target/fixtures
go build -ldflags='-s -w' -o target/fixtures/go tests/fixtures/go/main.go
target/fixtures/go > target/fixtures/go.json
python tests/go_integration.py target/fixtures/go target/fixtures/go.json target/fixtures/go.bndb
python tests/go_integration.py --cold target/fixtures/go.bndb
```

### Rust structures and layouts

Use a fixed-address executable so the runtime observations refer to the same
addresses in Binary Ninja:

```sh
mkdir -p target/fixtures
rustc --edition=2024 -Copt-level=2 -Crelocation-model=static tests/fixtures/rust/main.rs -o target/fixtures/rust
target/fixtures/rust > target/fixtures/rust.json
python tests/rust_integration.py target/fixtures/rust target/fixtures/rust.json
python tests/rust_inference.py target/fixtures/rust target/fixtures/rust.json target/fixtures/rust.bndb
python tests/rust_inference.py --cold target/fixtures/rust.bndb
```

Each `--cold` invocation runs in a new process to check database reopening.
These checks also exercise analyst annotation priority and byte preservation.
Additional scripts cover Go runtime calls and dictionary contexts, Rust
conditional and nested layouts, helper predicates, indirect calls and WARP
evidence. Fixture-specific build commands and arguments are in their module
docstrings.

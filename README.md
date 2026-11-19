# binja-go-rust

Native Go and Rust analysis for Binary Ninja.

The Go pass recovers function names and recursive runtime types from ELF, PE and
Mach-O executables during analysis. Its menu command refreshes the metadata.
Source lookup shows file/line information and inline call chains.
Dictionary lookup shows concrete slot uses, allocation types and call targets.
Checked amd64 Go 1.25–1.27 builds also receive allocation and bounds call types;
these annotations refresh when their supporting metadata or helper bytes change.
The Rust inspector examines pointer/length pairs and vtable headers at the
selected address. With WARP enabled, library inspection shows loaded candidates
and recorded matches, retaining ambiguous names and types.
`Infer Rust layouts` follows nested pointers, returned aliases and observed
branch conditions and helper predicates through bounded calls.
It follows contextual indirect-call targets and resolves proven local calls.
Library hints supply call-site types for verified amd64 word identities.
Roots persist in databases, and annotations refresh during analysis.
`Stop inferring Rust layouts` removes a selected root.

Build with Rust 1.91.1 or later, libclang, and Binary Ninja 6.0 (core ABI 187):

```sh
BINARYNINJADIR=/path/to/binaryninja cargo build --release --locked
```

Copy the library from `target/release` into your Binary Ninja plugins directory.
Commands appear under **Plugins → Go and Rust**.

Run unit tests with `cargo test --locked --lib`. The integration tests in `tests/`
use Binary Ninja's Python environment and the included Go/Rust source fixtures.

## References

- [unstrip](https://github.com/riven-labs/unstrip)
- [WARP](https://github.com/Vector35/warp)
- [Oxidizer](https://github.com/sefcom/oxidizer)

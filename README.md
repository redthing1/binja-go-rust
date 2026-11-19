# binja-go-rust

Native Go and Rust analysis for Binary Ninja, including stripped executables.

- **Go:** recover function names, runtime types and source locations, with
  calling conventions and generic dictionary analysis on supported builds.
- **Rust:** inspect runtime structures and library matches, and infer field
  layouts from the code that uses them.

Analysis integrates with Binary Ninja's workflows and saves annotations in the
database. Explicit analyst names and types take precedence.

## Install

The plugin targets **Binary Ninja 6.0, core ABI 187**. Building requires
Rust 1.91.1 or later and libclang.

```sh
BINARYNINJADIR=/path/to/binaryninja cargo build --release --locked
```

Copy the library from `target/release` into your Binary Ninja user plugins
directory: `libbinja_go_rust.so` on Linux, `libbinja_go_rust.dylib` on macOS, or
`binja_go_rust.dll` on Windows. Restart Binary Ninja.

Open an executable and let analysis finish. Go metadata recovery runs
automatically; commands are under **Plugins → Go and Rust**.

## Documentation

- [Usage](doc/usage.md) — commands, analysis behavior and support limits.
- [Development](doc/development.md) — code structure and testing.

## References

- [unstrip](https://github.com/riven-labs/unstrip)
- [WARP](https://github.com/Vector35/warp)
- [Oxidizer](https://github.com/sefcom/oxidizer)

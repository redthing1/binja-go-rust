# Usage

All commands are under **Plugins → Go and Rust**. Address commands use the
cursor location; function commands use the current function.

## Go

Open an executable and allow normal analysis to finish. Metadata recovery adds
function symbols and recursive runtime types, including method signatures where
the calling convention is supported. Recovered types appear in the `go`
namespace.

| Command | Use |
| --- | --- |
| Analyze Go metadata | Reread the current executable and refresh recovered metadata. |
| Show Go source information | Show the source file, line and inline call chain at the cursor. |
| Show Go dictionary contexts | Show concrete generic dictionary slots, allocation types and resolved calls for the containing function. |

Source lookup reads locations embedded in the executable; source files do not
need to be present. Generic dictionaries carry concrete type and method
information. Reports distinguish contexts supplied by different callers,
including receiver and hidden dictionary arguments.

On supported builds, analysis also applies allocation and bounds-check call
types. Dictionary analysis follows concrete values through qualified reads and
calls, resolving targets when the available evidence establishes them.

### Support

Metadata recovery reads ELF, PE and Mach-O executables. Exercised targets include
amd64, arm64 and 386 builds from Go 1.25–1.27. Recovery depends on the runtime
metadata retained in the executable; malformed type descriptors and types that
depend on them are withheld.

Method signatures, runtime call types and dictionary analysis currently require
**amd64 Go 1.25–1.27 with the register calling convention enabled**. Other targets
can still receive metadata recovery and source lookup. A dictionary report may
be incomplete when analysis reaches its limits or cannot establish a value.

## Rust

To inspect data, place the cursor on a candidate structure and run
**Inspect Rust structure**. To infer layouts, select a function that accesses an
object and run **Infer Rust layouts**, then let analysis finish. Use
**Inspect Rust layouts** to review the results and their status.

| Command | Use |
| --- | --- |
| Inspect Rust structure | Examine a pointer/length pair or a candidate vtable header at the cursor. |
| Infer Rust layouts | Add the current function as an inference root. |
| Inspect Rust layouts | Show observed field offsets, contextual results and inference status. |
| Stop inferring Rust layouts | Remove the current function as a root and refresh dependent annotations. |
| Inspect Rust library evidence | Show loaded WARP candidates and the recorded match for the current function. Requires WARP. |

Layout inference follows field accesses, nested pointers and returned aliases
through bounded calls. Branch conditions and helper predicates can distinguish
conditional layouts. Concrete indirect targets are followed when established by
the call context. Verified helpers that return an argument unchanged can
receive call-site types.

### Support

The structure inspector accepts 32- and 64-bit pointers. A pointer/length pair
can describe either text or bytes; a vtable header candidate does not establish
the number of methods or a source type.

Layout inference uses Binary Ninja's lifted intermediate language and has been
exercised on amd64. Library helper call types require the amd64 System V calling
convention. Results describe observed accesses and conditions; they do not
recover original Rust names or guarantee a complete source layout. Overlapping
or unsupported accesses can prevent a layout from being applied.

WARP inspection uses signatures already loaded in Binary Ninja and preserves
ambiguous candidates. A signature candidate alone does not establish a unique
Rust library or source identity.

## Refresh and persistence

Go metadata and Rust inference participate in normal analysis. Changes to
supporting bytes, metadata or call evidence cause dependent annotations to be
refreshed or withdrawn. Commands read the current view, including unsaved byte
edits; the plugin does not patch the executable.

Explicit analyst names, types and call-site adjustments take precedence over
automatic annotations. Rust inference roots persist in saved databases and
results are recomputed after reopening. Removing a root updates any layouts
that depended on it; other selected roots remain active.

If a result is missing, check the Rust layout status or Binary Ninja's log for
Go recovery diagnostics. After cancelling inference, run **Infer Rust layouts**
again to retry. **Analyze Go metadata** forces a metadata refresh.

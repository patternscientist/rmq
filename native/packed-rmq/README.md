# Packed RMQ native route experiment

This is NATIVE-1's route-review checkpoint, not the completed finite-limb/binary
library. The computational core is the proved Lean source in
RMQ/Core/WordRAM/Native, compiled through C. Rust implements the frontend only.
The full nativeExecutionCapstone_holds target remains open.

From the repository root on the tested Windows x64 host:

```powershell
./scripts/packed_native_build.ps1
./scripts/packed_native_route.ps1 -Case smoke
./scripts/packed_native_route.ps1 -Case n9-full
./scripts/packed_native_route.ps1
./scripts/packed_native_controls.ps1
```

The build uses installed Lean 4.22.0 and Rust 1.89.0, compiles one Lean module at
a time, links a GNU-target DLL with Lean's bundled compiler and links MSVC Rust
through raw-dylib. Cargo has no external dependencies and builds offline.
A module cache is local to this worktree, keyed by the exact ordered source
prefix, the actual compiler/import/runtime byte identity, and hashes of both
generated C and object interface. The repository Lean version and commit are
enforced. Old caches without toolchain identity cannot be reused. Native replay
refuses stale, missing or altered source/artifact inventories. Sources are
hashed before the build and checked again before a manifest is published.

Outputs live in .lake/native1/build. Put that directory and Lean's bin directory
on the process DLL search path. The replay script sets the latter and keeps the
DLL beside its executable. Every child process has an owned deadline. JSON
receipts under docs/internal/extensions/native1/commands preserve exits,
stdout/stderr, expected/executed registry IDs and source restoration checks.
The omitted selector runs the full exact sixteen-case phase registry; bound
empty/whitespace, malformed and unknown selectors fail before semantic execution.

The default Rust API call evaluate(program, fixture, false) omits read logs.
The CLI takes PROGRAM FIXTURE and an explicit reads or quiet mode. Counts are
always retained. One RouteRuntime is permitted per process, on its initializing
OS thread. The Lean runtime lifetime is separate from modeled operation costs.
It is retained until process exit. Rust rejects NUL input and text above the
experiment's length limits. The C ABI takes explicit
byte lengths; callers must supply valid readable buffers for those lengths.
It returns an owned result handle. packed_route_text borrows its UTF-8 bytes;
packed_route_free releases it once. Inputs are copied before evaluation.
Initialization and pointer failure return a null handle/nonzero initialization
status; Lean parser rejection is returned as ERROR-prefixed text.
Both Rust and C++ propagate that parser rejection as a failing process exit;
the C++ example releases its result on success and every error path.

The fixture format is the supplied textual experiment format, not binary image
v1. Program input is trusted experimental bytecode. Cell width, destination and
size checks do not establish bounded execution of arbitrary hostile arithmetic.
Finite limbs, arithmetic-fault policy, binary parsing/serialization proof,
canonical all-size instantiation and the final production API are unfinished.
The C++ source under examples demonstrates the intended C consumption pattern;
its compilation status is reported explicitly in the phase report.

The expected fixture files come from the independent baseline Lean exporter.
Their byte hashes and the exact source commit are in fixtures/manifest.json.
program.txt.gz contains the complete exported fixed program, not another RMQ
algorithm. Its decompressed hash is checked before execution. All ordered
reads/replies and six category counts are compared, including missing memory.
No timing or native memory-succinctness claim follows from these experiments.

See docs/internal/extensions/native1/ROUTE_EVIDENCE.md for exact theorem types,
compiler/runtime/FFI assumptions, live limitations and the requested review.

The build now also produces the C++ example and includes its source and binary
in the artifact inventory. The original example was checked on this host; its exact compiler
commands are in the cpp-import-library and cpp-build command receipts. The
installed MSVC lib.exe consumes packed_route.def to create an import library;
Visual Studio clang builds examples/route.cpp against that import library.
Run the resulting packed-rmq-cpp.exe with the same program.txt and fixture paths.
Its n9-full output matched every line of the independent reference. This is a
working consumption example of the experimental text ABI, not completion of
the production binary API contract.

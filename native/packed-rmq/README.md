# Packed RMQ native API

This package calls the checked Lean byte-limb executor through generated C.
The source capstone and its 42 independent field consumers pass. The binary
build and exact startup checks pass for the DLL and both clients. The executable
Lean validator passes 16 cases. Expanded replay and independent acceptance
are still in progress.

The canonical image contains exactly the fixed PQ1 program and counted memory.
The abstract theorem covers all sizes, all fuel values and representable
endpoints. The native API separately checks finite host limits. It does not
promise all-size execution on fixed hardware.

## Build and run

The recorded host is Windows x64, Lean 4.22.0 and Rust 1.89.0. Cargo builds
without external dependencies, offline and with the lockfile. The build records
actual Lean/C/Rust/C++ tool inputs, effective MSVC/SDK dependencies, all source
files, generated C and delivered artifacts. Changed tool inputs invalidate the
module cache. Compiler processes are owned and bounded.

```powershell
./scripts/packed_native_binary_build.ps1
```

Artifacts are written to `.lake/native1/binary-build`:

- `packed_rmq.dll`: Lean-generated computational core and narrow C bridge.
- `packed-rmq-native.exe`: Rust command-line client.
- `packed-rmq-native-cpp.exe`: C++ consumption example using the same C ABI.

Keep the DLL beside the clients and place the pinned Lean `bin` directory on
`PATH` for its runtime libraries. Both clients implement the same commands:

```text
packed-rmq-native load IMAGE
packed-rmq-native query IMAGE LEFT_HEX RIGHT_HEX FUEL READS [REPEAT]
```

Endpoint hex encodes little-endian bytes, with exactly `ceil(width/8)` bytes and
zero high padding. `READS` is 0 or 1; `REPEAT` defaults to 1 and is at most 16.
An image is loaded once for all repeated queries. Canonical query fuel is
837572. A successful observation reports status, executed instruction count,
six category counts, and optional ordered attempted address/reply pairs.
The categories are memory read, register write, arithmetic, comparison, branch,
and control, in that order. A blank line terminates an empty read list. Output
uses exact UTF-8/LF bytes. Rejected requests exit with failure and an error on
stderr. An executed machine fault is a successful observation with status
`fault`; it is distinct from request rejection.

## Rust and C ownership

`src/native.rs` exposes `NativeRuntime::new`, `runtime.load(&bytes)`,
`image.word_bytes()`, and `image.query(&left, &right, fuel, observe_reads)`.
A loaded image owns its load result and borrows its initializing runtime.
Caller input bytes may be released after loading. Query text is copied before
its result handle is released. The runtime and image cannot cross threads;
one Lean runtime is initialized per process, separately from modeled query costs.

`include/packed_rmq.h` defines ABI 1. Callers initialize once and perform every
call and destruction on that same OS thread. Input spans must be readable for
their declared lengths. Load and query results are separate owned handles,
released exactly once with their corresponding DLL functions. Image and text
accessors return borrowed pointers whose owning result must remain alive.
Status 0 is success, 1 is rejection, and 2 represents a NULL bridge/domain
failure. `examples/native.cpp` demonstrates these contracts with RAII.

The image limits are 128 MiB of serialized bytes, width 1 through 4096,
at most 65536 registers, and at most 1000000 instructions and memory words.
Queries require at least three registers, at most 512 bytes per endpoint,
representable input length/endpoints, and fuel at most 1000000. Actual allocator
availability remains a host assumption. Values persist as `Array UInt8` limbs;
there is no cached natural-number state or u128 truncation.

## Binary format 1

The five magic bytes are `52 4d 51 4e 01` (RMQN, version 1). A scalar consists
of k bytes equal to 01, one 00 delimiter, and k little-endian value bytes, using
its minimal positive byte count (zero uses k=1). The header stores width,
input length and register count as scalars. It is followed by the instruction
count and each instruction's field count and words, then the memory count and
memory words. A word stores its byte length as a scalar followed by its raw
little-endian bytes. Words must have exactly `ceil(width/8)` bytes, fit the
width, and have zero unused high bits. The instruction tags/fields are exactly
`PackedWordRAM.Instruction.encoding`.

The loader rejects nonminimal scalar framing, unknown version/tag, trailing or
truncated data, wrong word lengths, nonzero padding and unsupported counts.
Digit and count limits precede accumulation/allocation. Its indexed parser is
proved equal to the specification codec for every byte sequence and limit
record. `scripts/packed_native_image.py` serializes independently pinned numeric
fixtures; it is an export convenience, not a compiler correctness theorem.

## Proof and validation boundaries

| Layer | Established source claim or explicit assumption |
| --- | --- |
| Lean kernel | Limb operations, checked faults, complete run simulation, canonical image roundtrip/injectivity/accounting, total indexed-loader refinement, and the 42-field native source capstone. |
| Identical objects | Loaded code/memory are the counted canonical allocation; results, leftmost ties, counts, ordered reads, positional backing and supplied-store agreement concern that same execution. |
| Generated code | The actual exported Lean declarations produce the generated C. Exact source, C and compiler-input hashes and ABI prototypes are recorded. Correct compilation is an explicit assumption. |
| Foreign bridge | C/Rust/C++ pointer, ABI, ownership, linking and runtime behavior are checked by source review and operational replay; general C/Rust compiler or FFI correctness is not a Lean theorem. |
| Host resources | Checked lengths/indices prevent truncation on supported accesses. Allocation success and OS/runtime behavior remain assumptions. |
| Cost and space | Numeric payload/code/scratch bits, limb rounding, file framing, container overhead, modeled operation counts and observed runtime are distinct. Multiprecision operations have no physical constant-time claim. |

The default core uses a proved accumulator projection and never constructs the
full transition trace. Read observations are omitted when `observe_reads=false`.
Malformed code is rejected at load; missing fetched instructions stop without
an invented transition, failed loads record their attempted read and fault,
and arithmetic rejects underflow, zero divisors, oversized shifts or overflow.
Raw PQ1 uses total natural arithmetic; correspondence on arbitrary inputs
requires its exact safety predicate, discharged for canonical representable
queries by the all-size theorem.

The executable source validator is `RMQ/Validation/PackedNative.lean`, built as
`rmq_packed_native_validate`. The final native and certificate replay scripts
are `scripts/packed_native_binary_replay.ps1`,
`scripts/packed_native_binary_controls.ps1`, and
`scripts/packed_native_contract_replay.ps1`. The final frozen campaigns passed:
109 native cases expand to 214 client/source
checks inside 128 controls, and 44 certificate cases run inside nine controls.
The source validator also passed all 24 process and byte-format controls.
Fresh independent acceptance and aggregate certification are coordinator-scheduled.
Development evidence, exact types, assumptions and retained
failures are in `docs/internal/extensions/native1`. The earlier textual route
experiment and its receipts remain available there as historical evidence.

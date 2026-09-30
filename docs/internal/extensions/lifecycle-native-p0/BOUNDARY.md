# Source-grounded consuming-boundary recommendation

This is the LIFE-NATIVE-P0 native prerequisite at base
`bf31f983205175481fcb659caa4dfb70ef43e361`. It determines ownership questions for
the later adapter after LIFE-1's formal lifecycle interface is source-reviewed.
It implements no production ABI and supplies no Lean heap theorem.

## Pinned runtime definitions

The installed `include/lean/lean.h:754-770` defines allocation requests and
separate size/capacity projections. Lines 815-817 acquire an element reference;
838-846 dispatch shared arrays to copying; 872-881 implement pop by obtaining an
exclusive array, reducing size and decrementing the removed element. The
installed `src/lean/Init/Data/Array/Basic.lean:446-458` defines shrink by repeated
pop. These are actual included definitions, not deductions from `Array.size`.

The corresponding
[runtime object.cpp at the installed compiler commit](https://github.com/leanprover/lean4/blob/ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05/src/runtime/object.cpp)
was retrieved separately because runtime C++ bodies are absent from the installed
source bundle. `RUNTIME_SOURCE.json` pins its exact URL, bytes and local path.
`lean_copy_expand_array` at 2525 preserves the original capacity when expansion
is false; its shared branch increments initialized elements and releases one old
array owner. `lean_array_push` at 2548 reuses an exclusive buffer while space
remains. `lean_del_core` at 332 decrements logical elements then dispatches
capacity-sized deallocation. Deallocation at 213 depends on the runtime build's
allocator configuration. The fatal handler at 90 delegates to internal panic,
which prints its diagnostic and exits (or aborts under the runtime panic policy).
The installed binaries are pinned release artifacts; this task does not claim to
rebuild or formally verify the runtime compiler/allocator implementation.

## Resources and actual producer-to-consumer chains

| Source and resource | Current proposition or operation | Later consuming obligation |
| --- | --- | --- |
| `RMQ/Core/WordRAM/Construction/ArrayRun.lean:20`, `ExecState` | Four arrays: `regs : Array Nat`, `memory : Array (Option Nat)`, `keys : Array (Option Int)`, `keyRegs : Array Int`; plus `pc : Nat`, `status : Status`. `abstract` uses `getD`; numeric extent is `memory.size`. | Inventory every root and nested boxed value. Transfer exact output cells and retire all other arrays, including the separate comparison-key banks. Logical zero/absence does not imply capacity reduction. |
| Same file:57, `ArrayRun` | `final`, `steps`, `categories`, `writes`, `reserves`, `result` are ordinary executable fields. `runArrayAux` collects lists; `finishRun` reverses them. | Release observation lists and obsolete run/state/result roots before the retained boundary, or account for all of their reachable storage. Observations are not erased merely because they describe execution. |
| Same file:414, `ExecState.ofWordInput`, `ofComparisonInput` | Word input stores header and encoded keys in numeric memory; comparison input stores the header numerically and arbitrary `Int` values in separate keys. Both have key registers. | Keep input models distinct. Caller input lists, boxed integers and external element aliases may remain live independently of the array owner. |
| `Construction/Proof/RunFacts.lean:49`, `BuilderRunFacts.outputCells` | For every `outBase` with the builder's final status `halted outBase`, `s0.extent <= outBase`, final extent equals `outBase + (buildMemory xs).length`, and for every `i < (buildMemory xs).length`, final memory at `outBase+i` equals `some ((buildMemory xs).getD i 0)`. `outputProvenance` additionally gives the occurrence and final write at each cell. | Use this exact interval/value producer or its reviewed LIFE-1 successor; copying an independently reconstructed sibling image would need a proved correspondence. |
| Same file:75, `inputRetained` | Every initial numeric cell is preserved and final `keys = s0.keys`; `arrayReflects` links all executable run projections and final abstraction under matching initial state and 400-element register banks. | Existing PRE preserves input. New consuming behavior must establish new retirement obligations; predecessor clean tails and extents cannot discharge them. |
| `RMQ/Core/WordRAM/Native/Binary.lean:17`, `StorageImage` | Fields `width`, `inputLength`, `registerCount`, `code`, `memory`; `Native/Machine.lean:16` defines `Memory = Array Word`, `Code = Array (Array Word)`; `Native/Limbs.lean:15` defines `Word = Array UInt8`. | Account for every nested container, metadata and conversion/parser temporary. Generic object-array tests establish outer-reference mechanics only. |
| `Native/Machine.lean:734`, `runThin_loaded_reference` | Under canonical memory/state, code equality to `encodeCode width program`, fitting instructions, bounded register writes and safety of the reference run, decoding the native final state and statistics equals `observeRun` on that same decoded memory. | Establish these exact premises on the transferred allocation and code. A capacity measurement is not this representation/refinement bridge. |
| `Native/Runtime.lean:25`, `nativeInitialState`, `nativeCore` | `nativeCore` runs supplied image code/memory with freshly encoded registers. `nativeCore_no_reads` states the `readsRev` projection is empty when reads are disabled. | Distinguish temporary endpoints/registers/text/receipts from retained image storage. Existing fresh query setup does not prove charged sequential lifecycle re-entry. |
| `native/packed-rmq/src/native.rs:65`, `LoadOwner`, `QueryOwner`, `NativeImage` | Rust drops call matching C frees. `NativeImage` owns `LoadOwner` and borrows the process-lifetime initializing-thread runtime; query text is copied before dropping `QueryOwner`. | Future success and failure must give explicit owners/borrowed lifetimes, same-thread destruction and exactly-once release obligations. This remains native implementation reasoning outside the kernel. |
| `native/packed-rmq/native_shim.c:52-89` and `include/packed_rmq.h:23` | Loaded image is borrowed from a load result; query increments the image before an owned Lean call, retaining the old load owner. C frees decrement the matching result. | Existing immutable reuse supplies no exclusive consuming transfer. Every outstanding handle and element alias must be covered by the later boundary contract. |

`StorageImage.encoded_bit_accounting` (`Native/Binary.lean:535`) separates numeric
bits, encoded-byte rounding and framing; it explicitly excludes physical object
allocation. `Native/CanonicalImage.lean:9` selects the original `queryProgram`,
so this prerequisite does not imply an existing compact lifecycle native path.

## Recommended ownership semantics

For the measured route, consume-and-clean-up is explicit. On success, acquire one
reference per initialized destination occurrence before releasing its source.
Publish the bounded-capacity output only after all required ownership checks.
Release construction memory, numeric and key registers, separate keys, obsolete
results and observations; separately retain only reviewed query resources.

On controlled failure before allocation, after allocation, during copying, before
handoff, or after old-owner release, release all initialized destination entries,
temporary references and the consumed source; publish no output. Returning the
original owner would be a different viable contract, but cannot be mixed with
this consuming experiment after destructive progress. A real Lean allocator
failure invokes a non-returning fatal path; deterministic injection tests cleanup
of recoverable stages, not recovery from actual out-of-memory termination.

Array uniqueness and element uniqueness are different. An old array alias keeps
its backing allocation and all old element references alive after one owner is
released. An independently retained element can outlive the old container.
The native contract must either rule out such aliases at entry, or report their
retained storage separately and qualify its retained-memory bound accordingly.
The probe enumerates its own roots; it cannot certify absence of arbitrary
foreign aliases in a future program.

The replacement uses `lean_alloc_array(0,m)` and fills at most `m` initialized
slots, acquiring each source with `lean_array_uget`. The observed requested bytes
are `sizeof(lean_array_object) + sizeof(void*) * capacity`. This is a container
allocation request, not allocator usable bytes, process RSS, nested element bytes,
numeric payload bits or a universal heap bound. While both source and destination
live, transient container storage includes both; it belongs in the construction
peak, not the final retained target. The C loops and releases are real measured
native work and are not claimed single charged word-RAM instructions.

## Worked example and next review

The independent fixture is `[101, -7, 303, 303, 505, -19]`, with distinct
destructor-counted objects even for the equal values. Select positions 1 through
4 into capacity four. Each acquired value gains a reference; releasing the sole
old array destroys positions 0 and 5 while positions 1 through 4 survive with one
reference each. If an old array alias remains, the old capacity and all six
objects remain reachable, and selected elements have two references. The same
output values therefore coexist with two different retained-memory outcomes.

The source interval `[1,5)` overlaps the hypothetical in-place destination
`[0,4)`. A separate buffer avoids overwrite dependencies; prefix, overlap, tail
and empty selections check the actual position arithmetic. Snapshots retain only
integers and counts, never extra Lean references. Finalizer counts concern the
Lean external test objects; their static payload records require no allocation.

The next consumer must source-review LIFE-1's full formal output/resource
interface, then establish that the compiled consuming adapter releases every
construction root and transfers the exact image used by its query refinement.
It must additionally bound nested native allocations and decide how alias freedom
is enforced. Those are explicit later campaign phases, not properties inferred
from the local probe or its candidate status.

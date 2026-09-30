# Consuming the lifecycle owner

This guide describes the candidate interface and its checked Lean connection.
Native startup, all thirteen fixtures, ten clients and twenty-three ABI checks
pass on the current pinned profile. All 48 reviewed transfer controls replay
under the corrected full input recipe, and all 17 Rust misuse cases replay their
exact compiler diagnostics. All 34 formal mutation cases, the 21-declaration
axiom inventory and the required default build pass. REPORT.md and
ACCEPTANCE_MATRIX.md distinguish these evidence layers from final committed
certification and coordinator acceptance; the external delivery receipt binds
the delivered candidate identity.

## A worked request sequence

Choose the word model and input `[3, -1, -1, 7]`. Ask the initializing runtime for
the count-four profile. Encode endpoints in exactly that profile's byte width,
little-endian with zero padding. The comparison model uses the same interface
and also accepts signed integers wider than 128 bits. The word model additionally
requires the existing `InputFits` predicate; rejection does not change the model.

The native ceiling is 4096 inputs, each with 1–4096 magnitude bytes, with at most
16777216 magnitude bytes in total. Sign is a separate 0/1 flag. Negative zero,
empty magnitudes, malformed views, and noncanonical endpoint widths reject.
Magnitude padding is allowed; arithmetic values and answers are never narrowed
to a host `u64` or `u128`. Counts and native allocation sizes use checked host
bounds separately from the all-size Lean statements.

Build with the caller's first interval `[0,4)`. The independent expected leftmost
minimum is index 1, encoded as packet 2. A packet is a natural number: zero means
`none`, and a positive packet means index plus one. No dummy first request is
inserted. The owner then serves `[2,4)` with packet 3, reversed `[3,1)` with packet
0, and `[0,2)` with packet 2. The invalid represented request still follows the
formal guarded route and leaves a reusable owner on successful completion.

The C entry points are `packed_lifecycle_init`, `packed_lifecycle_profile`,
`packed_lifecycle_build_first`, and `packed_lifecycle_query`. Each output slot
starts null. The constructor returns an owner, an independently owned answer,
and an optional independently owned observation object. The query receives an
owner-slot pointer because consumption can replace or empty that slot. Free the
answer and observation when done, and free the final owner on the initializing
thread. The Rust facade encodes these lifetimes and unique mutation in its types;
the C++ example wraps the same C ABI with RAII.

## What executes and what is proved

`nativeInitial` is the existing `Executable.initialOwner`. The checked split
identity is unconditional:

```lean
nativeRunFirst comparison xs.length (nativeInitial comparison xs left right)
  = nativeBuildFirst comparison xs left right
```

The first run uses the existing continuous lifecycle budget and the fixed
`cachedProgram`. Its consuming loop calls the unchanged `executeArray` primitive.
The following equality covers every program, fuel and owner, including stopped,
faulted and missing-fetch states, without an admission or success premise:

```lean
runThin program fuel owner = PackedLifecycle.runOwner program fuel owner
```

`runThin_eq_runOwner` proves this by fuel induction. The analogous boundary
theorem identifies `requestProtocolThin` with `requestProtocolOwner` for every
entry, endpoint pair and owner. These adapters erase temporary transition
records after actual copy measurements exposed retained prestate references.
They do not replace primitive instruction semantics. `cachedProgram_eq` states,
for either input model:

```lean
cachedProgram model = (Layout.program model).toArray
```

`buildFirst_eq` identifies the result with the actual `Ownership.owner`.
The native admission bridge supplies the real decoded list length, source input
domain, and canonical endpoints. `nativeBuildFirst_correct` and
`nativeBuildFirst_packet` derive READY, halted status, and the encoded reference
answer from that admitted execution. They assume no final-memory or answer
equality. The exact premises and all thirteen export projections are in
PROOF_EVIDENCE.md and the independent `LifecycleNativeContract.lean` consumer.

The existing finalizer and retirement instructions run before publication.
The native boundary then creates exact-capacity replacements for all four arrays,
copies the initialized values, checks equality, and releases old roots. The Lean
repacking relation equates all entries, extents, program counter, and status; it
therefore transports the complete owner value and its READY facts. That theorem
does not prove the C implementation, pointer exclusivity, or allocator behavior.
Those require the actual compiled controls and runtime assumptions.

The current native implementation repeats all four replacements after every
successful later query, even when the incoming capacities were already exact.
It copies the whole canonical memory at each publication. This extra native
work and the new physical pointers are separate from the unchanged modeled
memory and the modeled query-step bound.

For a later request, `query_eq` identifies the adapter with
`Executable.queryOwner`. `nativeQueryAdmit_iff` reads the count from produced
memory cell zero, rather than trusting a caller's duplicate. The query starts
with the existing two request-admission and two control-entry events. The first
continuous run has no such external re-entry prefix. The query contract preserves
the actual produced memory and proves the 160257 model-step upper bound. Its
ten mandatory projections are independently consumed at their fixed types.

Optional observations accumulate actual categories and ordered read/reply
occurrences using producing prestates. The scalar accumulator is computed before
the primitive consumes that prestate. `runAccThin_eq_runAcc` proves equality of
both owner and statistics for every program, fuel, owner and initial statistics;
`boundaryAccThin_eq_boundaryAcc` proves the corresponding boundary equality.
Their proved fold-to-trace equations and same-final-owner bridge are listed in
PROOF_EVIDENCE.md. The observation object
is separate from the reusable owner. Model counters, native copying, fixed-code
initialization, host conversion, and elapsed time are different measurements.

## Ownership and failure states

| Call outcome | Incoming owner | Returned resources |
| --- | --- | --- |
| Malformed or unrepresentable later request, before take | Preserved | No answer or observation |
| Represented invalid interval, successful formal execution | Consumed and replaced | Canonical reusable owner and packet zero |
| Successful first/later execution and publication | Exactly one published owner | Separate answer; optional separate observations |
| Controlled failure after irrevocable take | Slot becomes empty | Initialized temporaries released; explicit error |
| Model fault or exhausted fuel | No reusable intermediate builder is published | Distinct error, with temporary resources released |
| Ordinary Lean allocator failure | Pinned runtime may terminate the process | No promise of a recoverable allocation error |

C callers must provide valid buffers and exclusive live handles, avoid racing
calls, and use the initializing thread. Rust exposes no safe raw owner or clone,
requires `&mut Owner` for queries, ties object lifetimes to the runtime, and makes
live native types neither `Send` nor `Sync`. Borrowed result bytes remain tied
to their result object; the result itself can outlive the operational owner.
Finite native controls support these implementation checks and do not quantify
over arbitrary foreign misuse.

Testing receipts count native handles created in the current operation. A
rejected later request may preserve an older-generation handle while reporting
zero current-operation live handles. Preservation is checked by the live owner,
its identity and contents; that counter alone cannot establish global absence
of handles. Likewise, cleared transfer-local pointers are checked alongside the
actual release paths and generated closure, not treated as an external-root
inventory.

## Reading resource evidence

For every retained array, distinguish initialized length, native capacity, and
requested outer-container bytes. Zero-sized banks also have a container.
Reachable boxed objects and their integer limb allocations are counted separately
from shared fixed program/global objects. Overlapping graph inventories must not
be added as if disjoint. The pinned runtime's integer representation and generated
code/FFI are explicit implementation assumptions.

The formal retained-capacity conclusion remains a statement about modeled
payload and machine state. It is not a theorem about native allocator usable
bytes, RSS, or elapsed-time complexity. The native build is certified only for
the declared Windows x64 profile and pinned Lean runtime; no portable native
certification follows from the platform-independent Lean equalities.

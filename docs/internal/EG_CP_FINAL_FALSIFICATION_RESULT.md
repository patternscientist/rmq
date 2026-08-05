# EG-CP final falsification gate — worker result

**Status: INCOMPLETE — in progress.** This document is the durable worker report
required by the checkout contract. It is written and updated as the branch
proceeds so that a successor session can resume from commits alone; it is not a
completion claim. No row of the frozen matrix is closed, and neither
`CANDIDATE_COMPLETE` nor an obstruction is being asserted.

Worker: Claude (Opus 5) runtime, role skill `rmq-proof-sprint`.
Branch: `codex/eg-cp-final-falsification-gate-r1`.
Base: `1490c97b399d136bad4e18953441da433d130d4d`, tree
`4114fe2544ad0a4af4dce3c002e617a8dd55e64b`, both verified.
Frozen acceptance matrix: `0a18548539035f69f68c1b44031fba64df8297f3`, verified
as an ancestor of every commit below.
Governance ref `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` verified as an
ancestor.
Worktree: `C:\Users\poin\.codex\visualizations\2026\07\17\019f6d85-7626-7433-a60b-81f8be29689a\eg-cp-final-falsification-r1`.
Never pushed, never merged, never amended, never squashed.

Last update: 2026-08-04, in the commit titled "Synchronize the report with the
re-target", which was the branch tip when this line was written. Earlier tips this
document described: `4d2ed70`, `5c05016`, `08d63c7`, the header-probe commit, the
physical-read commit, the executed-segment-universe commit, the replay-run commit,
and the three-payload commit.

---

## 1. Preflight

`scripts/project_skill_preflight.ps1` against the governance ref, with
`rmq-proof-sprint` required: **PASS**, twice.

* 2026-08-03, at base `1490c97`, runtime catalog declared as `rmq-proof-sprint`
  alone.
* 2026-08-04, at checkout `6078a29`, runtime catalog declared as the complete
  actual set exposed to the session: `rmq-audit-prompt`, `rmq-coordinator`,
  `rmq-proof-sprint`. Output: governance `f0c7232a...`; checkout `6078a29...`;
  expected, checkout-tracked, working-tree and runtime skill sets all equal to
  those three names; `required=rmq-proof-sprint`;
  `required_mode=role-skills`; `PASS`.

The second run is the one `AGENTS.md` asks for: the runtime list must be the RMQ
skills actually exposed to the task. The first run's smaller declaration could
only make the check stricter, never produce a false pass, but it was not the
declared catalog and is superseded.

## 2. Commit ancestry

```
4d2ed70  Type the logical read address without a shape
293fb45  Replace the unconditional cell pair with a conditional probe plan
6078a29  Compute packed probe addresses from the size and the decoded long count
20497d2  Prove the cell-crossing span theorem
06d3bc3  Name the allocated cells and pair them for the physical lowering
e85b39c  Update the worker report through FG-06
72613b3  Complete the shape-free flat address
3ea5121  Bound the allocated space and prove the residual is little-o linear
06caa3d  Land the durable worker report for the falsification gate
5ab003d  Prove the packed memory round trip
ca11556  Define the packed memory: cells, allocation, and the header cell
52e7988  Fix the K=1 header schema: P n, w n, all-size count fit, decoding
85c58f0  Close the shape-free address-factorization leaf for FG-02 and FG-03
b9ace55  Add a decidable size-only counting guard for the close sources
17d1ddf  Make the rank prefix a Nat-only mirror and prove sparse terminality
63fd605  Mirror the select super geometry and isolate the long-count term
319aabf  Prove the packed close-component base is input-size-only
0a18548  Freeze the EG-CP final falsification acceptance matrix
1490c97  (base)
```

The freeze at `0a18548` precedes every implementation edit, so the freeze is
git-verifiable rather than asserted. Every commit was validated individually
with `scripts/design_decision_check.ps1 -Strict -Base HEAD~1`, which is how CI
evaluates them (`WDD-20260726-007`), and with `git diff --check HEAD~1..HEAD`.

## 3. Modules on this branch

All under `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/`, all imported by
`RMQ.lean`, so all inside `lake build RMQ` and inside the prose hygiene scan.
Import order: `SourceFactorization` → `Payload` → `Header` → `Memory` → `Space`
→ `Address` → `Probe` → `ReadProgram` → `SourceWords` → `SourceGeometry` →
`WordWidth` → `PhysicalRead`. The validation root is
`RMQ/Validation/EGCPFinalFalsification.lean`.

| Module | Row | What it establishes |
| --- | --- | --- |
| `SourceFactorization.lean` | `FG-02`, `FG-03` | Nat-only mirrors and the shape-free flat address |
| `Payload.lean` | `FG-01` | the stored bits are the canonical payload object |
| `Header.lean` | `FG-04` | `P n`, `w n`, count fit, decoding, `n = 0,1,2` |
| `Memory.lean` | `FG-05` | cells, allocation, round trip, cell crossing |
| `Space.lean` | `FG-06` | allocated-bits bound and its little-o residual |
| `Address.lean` | `FG-07`, `FG-08` | bit addresses and the header shift |
| `Probe.lean` | `FG-05`, `FG-08`, `FG-09` | the conditional probe plan; the header probe; the BP code lowered completely |
| `ReadProgram.lean` | `FG-07` | logical reads carry no table content; select geometry is size-only; the controller |
| `SourceWords.lean` | `FG-08` | every source's word array is a payload slice at a size-only count and stride |
| `SourceGeometry.lean` | `FG-08` | the three geometry functions and the aggregate lowering of the word arrays |
| `WordWidth.lean` | `FG-08`, `INV-WORD-WIDTH` | every stored word fits one packed cell |
| `PhysicalRead.lean` | `FG-08` | the physical read, the per-read lowering, and the packed-backed store |
| `ExecutedUniverse.lean` | `FG-08`, `INV-GLOBAL-PHYSICAL-MACHINE` | where the executed store stops agreeing with the flat payload store |

## 4. What is proved

### The raw payload identity (`FG-01` — identity clause proved, row Open)

```
packedPayloadBits (shape : CartesianShape) : List Bool :=
  (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload

packedPayloadBits_eq_canonical :
  packedPayloadBits shape =
    concreteBPNativeSuccinctRMQPayload
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape
```

The proof is `rfl`, so the right-hand side is the canonical definition applied
to the canonical access family; there is no second object to keep in sync.
`packedPayloadBitsOfList_eq_canonical` gives the same identity at the list-facing
front door, and `packedPayloadBits_eq_bpCode_append_aux` expands one level so
that "no hidden table" is checkable: the whole stored string is the BP code
followed by the auxiliary payload.

The identity is consumed rather than merely stated.
`packedSerializedBits shape = packedHeaderBits shape ++ packedPayloadBits shape`,
so `packedPaddedBits`, `packedMemory` and every probe theorem take their bits
from this object, and `packedSerializedBits_drop_header` proves that dropping the
one header cell recovers it exactly.

A length agreement would not have done this: a separately defined payload of the
same length satisfies a length theorem, and `M11-SIBLING-PAYLOAD` exists to
exploit exactly that.

### The K1 address factorization (`FG-02`, `FG-03` — offset half complete, rows Open)

```
packedSourceComponentOffset :
  Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat

packedSourceComponentOffset_eq :
  forall (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource),
    concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source =
      packedSourceComponentOffset shape.size (longCount shape) source
```

The signature carries the claim: with no shape argument no instantiation can
consult shape content. Coverage is elaborator-enforced — the proof is
`cases source`, so a new constructor fails to elaborate until both sides supply
its arm, and the `finalRankBPCodeAlias` alias, the three retired finite-small
slots and the zero arms each appear explicitly rather than under a default.

Component bases: `closeComponent_flatOffset` gives
`componentFlatOffset .closePayload = 2 * shape.size + packedAccessOverhead shape.size`.
The whole select payload, including *both* content-dependent relative tables, is
absorbed by the access padding. This is not arithmetic luck: truncated `Nat`
subtraction makes `a + (B - a) = B` false without `a <= B`, and that hypothesis
is the `BPCloseAccessDirectory.payload_length_le_overhead` structure field, so
the layout cannot be instantiated without it.

Terminality: `selectPayload_eq_prefix_append_sparseRelative` exhibits the select
payload as a prefix that does not mention the sparse relative table, followed by
that table; `selectSourceComponentOffset_le_prefix` gives the addressing
consequence.

The long-count term:

```
longSuperRelativeTable_length_eq :
  (GenericSelect.longSuperRelativeTable shape.bpCode false).payload.length =
    longCount shape *
      (GenericSelect.superStride (2 * shape.size) *
        GenericSelect.wordBits (2 * shape.size))
```

The component bases are also shape-free and need **no** long count, so
`packedSourceFlatOffset_eq` holds with the long count needed only for positions
*within* the select component. That is sharper than "`K = 1` suffices": it says
exactly what the header buys.

### The counting guard (`FG-02` support)

`PackedSummaryActive` and `PackedInteriorReady` are decidable predicates on
`Nat`, with `summaryActive_iff_packed`, `interiorReady_iff_packed` and
`sourceCounted_iff_packed` proving agreement with
`concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat` on every
constructor. This is load-bearing rather than bookkeeping — see section 6.

### The `K = 1` header (`FG-04` — clauses proved, row Open)

`packedPayloadLength n = 2 * n + concreteBPNativeSuccinctRMQOverhead
genericSparseExceptionBPCloseAccessOverhead n`, with `packedPayloadLength_eq` and
its payload-object form `packedPayloadBits_length`;
`packedCellWidth n = SuccinctRank.machineWordBits (packedPayloadLength n + 2)`,
the commissioned expression unchanged; `longCount_lt_two_pow_width` with no size
side condition; `packedHeaderBits_length` (exact one-cell arity);
`packedHeaderBits_decode`.

Small cases are now `n = 0`, `n = 1` **and `n = 2`**. Size two is the first size
carrying more than one shape, so both are instantiated: `packedSizeTwoLeft` and
`packedSizeTwoRight`, proved distinct, each required to have header arity
`packedCellWidth 2` and payload length `packedPayloadLength 2`. That is the
smallest case able to distinguish "the width is a function of the input size"
from "the widths tried so far happened to agree".

`packedCellWidth_ge_two` was added so that boundary-crossing reads exist at all:
a one-bit cell could not be straddled and the crossing instances would be
vacuous.

### The packed memory (`FG-05` — definitions, round trip and crossing proved, row Open)

`packedSerializedBits`, `packedCellCount`, `packedAllocatedBits`,
`packedPaddedBits`, `packedMemory`, with `packedMemory_length`,
`packedMemory_cell_length` (every allocated cell exactly one full width, none
short), `packedMemory_cell_zero` (header is cell zero in full),
`packedMemory_flatten` (join recovers the padded bits exactly) and
`packedMemory_flatten_take`.

Exact slice behaviour: `packedSpan_from_two_cells` for an arbitrary aligned or
unaligned span of at most one cell width, and `packedPayloadSlice` for the header
shift.

### Allocated space (`FG-06` — clauses proved, row Open)

```
packedAllocatedBits_le : packedAllocatedBits n <= 2 * n + packedRho n
packedRho n = concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n
            + 2 * packedCellWidth n
packedRho_littleO : SuccinctSpace.LittleOLinear packedRho
```

Stated on allocated cells times width, over `packedMemory`, not on meaningful
bits. The `2 * packedCellWidth` term is the header cell plus the ceiling
remainder of the final cell; it is logarithmic, hence `o(n)`, but it is charged.
Its little-o proof needed a new lemma, `littleOLinear_machineWordBits_comp`,
because every existing little-o fact is about a function *of* `n` while the cell
width is `machineWordBits` of the payload length.

### The conditional physical probe plan (`FG-05`, `FG-08`, `FG-09` — per-read only)

This replaces the unconditional cell pair described in section 6.

```
packedProbePlan (n bit width : Nat) : List Nat :=
  if width = 0 then []
  else if bit % packedCellWidth n + width <= packedCellWidth n then
    [bit / packedCellWidth n]
  else [bit / packedCellWidth n, bit / packedCellWidth n + 1]

packedProbeCount n bit width = (packedProbePlan n bit width).length
```

Probes are issued through `packedProbeCell = List.getElem?`, so an unallocated
address fails instead of decaying to an empty slice, and `packedFetch` returns
`some` only when every issued address resolved.

Proved:

* `packedProbePlan_lt_cellCount` — every issued address is below
  `packedCellCount n`, from the single hypothesis
  `bit + width <= packedAllocatedBits n`;
* `packedFetch_plan` — a fitted plan fetches to exactly the addressed cells;
* `packedProbe_covers_range` — after skipping the in-cell offset, at least
  `width` bits remain in the fetched window;
* `packedProbeWindow_length` — the window is exactly one full cell per probe;
* `packedProbePlan_decode` — the fetched cells decode to exactly the requested
  window of the packed bit string;
* `packedSourceRead_decode` — the same conclusion stated at the canonical
  payload slice of a typed source;
* `packedProbeCount_le_two`, with the exact conditional values
  `packedProbeCount_eq_zero`, `..._eq_one`, `..._eq_two`, and
  `packedProbeCount_pos`.

Two facts make the repair real rather than cosmetic:

* `packedMemory_getElem?_cellCount : (packedMemory shape)[packedCellCount
  shape.size]? = none` — the address the old plan issued at the end of the memory
  is genuinely absent;
* `packedProbe_final_cell` — a positive-width read contained in the last
  allocated cell issues exactly `[packedCellCount - 1]` and fetches
  successfully. Under the old plan the second issued address would have been
  `packedCellCount`, and the fetch would have returned `none`.

Both branches are exhibited (`packedProbePlan_of_offset`,
`packedProbePlan_of_crossing`), so the conditional is not constant in disguise,
and both are instantiated at sizes 0, 1 and 2 in the validation root.

### The logical read address (`FG-08` — address side only)

`packedSegmentSource?` names the already shape-free segment map
`concreteBPNativeSuccinctRMQFlatPayloadSegmentSource? : Nat -> Option Source`.
`packedLogicalProbePlan : Nat -> Nat -> Nat -> Nat -> Nat -> List Nat` composes
it with the probe plan, `packedLogicalRead_decode` proves the decoding, and
`packedLogicalProbePlan_length_le_two` covers the unmapped-segment case.

The width remains an explicit argument for a general source. The mirror that
would derive it from `(n, longCount, segment)` is deliberately **not** defined in
general; see section 7.

### The header probe (`FG-04`, `FG-07` support)

Every packed address takes `longCount` as an explicit `Nat` argument, and every
agreement theorem instantiates it at `longCount shape`. Read literally, that is a
definition parameterized by a shape-derived quantity, which is what `FG-07`
forbids the controller to receive.

`packedHeaderProbePlan = [0]` is the controller's first probe. `packedHeaderFetch`
proves it is allocated at every size and returns the header cell;
`packedHeaderProbe_decode` proves that decoding that cell with the little-endian
codec yields exactly `longCount shape`, at every size and with no side condition;
`packedHeaderProbePlan_length = 1` charges it. `packedMemory_cell_zero` is the
load-bearing step: cell zero is the header **in full**, so the descriptor is not
split across cells and the first probe needs no crossing case.

This does not close `FG-07`. Nothing sequences the header probe before the
address computation, and no definition consumes the reply. What is available is
that such a definition would need no input beyond `n` to obtain the long count.

### The BP code, lowered completely (`FG-08` — one source)

`packedBitAddress` computes `index * width`, which assumes that a source's stride
and its read width coincide. They do for a `FixedWidthNatTable`: `width` is a
type index of that structure and its `word_length_of_get?` field forces every
stored word to that length. They do **not** for a chunked bit source.
`SuccinctSpace.chunkPayloadWords` leaves the final word short whenever the length
is not a multiple of the word size, and
`chunkPayloadWords_get?_eq_take_drop` states it: word `i` is
`(payload.drop (i * wordSize)).take wordSize`, which truncates at the payload's
end. Four of the twenty-nine typed sources are such chunkings — `bpCode`,
`selectLongFlagBits`, `selectSparseFlagBits` and `finalRankBPCodeAlias`.

Against the packed memory that truncation does not happen, because the next
component follows immediately. Reading the final word at full width would return
the correct prefix followed by foreign bits: a wrong decoded word, not a harmless
over-read.

`packedStridedBitAddress n longCount source index stride` separates the two, with
`packedBitAddress_eq_strided` recording that the uniform-width address is the
special case. For the BP code:

```
packedBpCodeWordWidth n = SuccinctRank.machineWordBits (2 * n)
packedBpCodeReadWidth n index =
  min (packedBpCodeWordWidth n) (2 * n - index * packedBpCodeWordWidth n)

packedBpCodeRead_decode :
  (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape .bpCode)[index]? =
      some word ->
    (packedFetch (packedMemory shape)
        (packedProbePlan shape.size
          (packedStridedBitAddress shape.size (longCount shape) .bpCode index
            (packedBpCodeWordWidth shape.size))
          (packedBpCodeReadWidth shape.size index))).map
      (packedDecodeSpan shape.size ... ) = some word
```

This is the first source lowered completely: the address, the stride and the read
width are all functions of `n` and the index alone, and the decoded bits are
proved equal to the word the flat payload store would have returned.
`packedBpCodeWord_index_lt` derives the in-range condition from the existence of
the word rather than assuming it, so the theorem carries no side condition a
controller would have to discharge from outside its own inputs.

### The controller (`FG-07` — definition built, row Open)

`packedWholeQueryRun (store : WordRAM.ReadStore) (n left right : Nat) :
WordRAM.TraceResult (Option Nat)` runs the fixed
`concreteBPNativeSuccinctRMQWholeQueryProgram`, named inside the definition rather
than accepted from a caller, and

```
packedWholeQueryRun_eq :
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore shape store
      left right =
    packedWholeQueryRun store shape.size left right
```

holds at every shape, store and endpoint pair. The equation is between the
`TraceResult`s, so value, modeled cost and ordered trace all agree. The declared
type has no `CartesianShape`, no `WholeQueryProgram` argument, no `List Int`, no
proof callback and no expected answer.

The row is **not** closed. It also requires the controller to consume the packed
memory's header reply and the `n`-only readiness guard, and its `receipt` to be
the object the capstone's other conjuncts talk about. What exists is a controller
over an abstract `WordRAM.ReadStore`; wiring it to `packedMemory` is `FG-08`.

### The word geometry of all twenty-nine sources (`FG-08` — clause (a) proved)

The flat payload store answers `(segment, index)` with
`(sourceWords shape source)[index]?`, one entry of an `Array (List Bool)`. To
answer the same read by probing, a controller must know from `n` and the header
how many words that array has and where word `index` sits. Both are now supplied:

* `packedWordSlice payload count width i` is the single formula both word
  representations satisfy.
* `packedFixedWidthTable_getElem?` is proved from `FixedWidthNatTable`'s own
  fields, with **no** positivity hypothesis on the width. The count comes from
  `read_exact`, not from the payload length; that matters because the close
  summary's relative width is genuinely `0` when the summary is inactive, and a
  zero-width table still has `entries.length` empty words that
  `flattenPayloadWords` cannot see.
* `packedChunkedWords_getElem?` and `packedChunkedSentinelWords_getElem?` cover
  the four chunked bit sources. `List.take` truncates, so the short final chunk
  needs no separate arm, and the `payload.length + 1` sentinel words
  `ofChunksWithSentinel` appends are absorbed by the same formula with a larger
  count.
* `packedSourceStride`, `packedSourceWordCount` and `packedSourceBitLength`
  collect the geometry; `packedSourceWords_of_some` is the aggregate.

**Exactly one source is not size-only.** `selectSparseRelative`'s entry count is
the number of local slots whose span forced a sparse exception — a property of the
bit pattern, not of its length. `K1` spends its single header count on
`longCount`. The resolution taken (`DD-20260804-022`) is the size-only capacity
`packedSparseRelativeCapacity`, with `packedSparseRelativeEntries_le_capacity`
proving the bound, so every **successful** read still lowers exactly. If some
reachable query ever attempts an out-of-range sparse relative read, that is a
genuine `K1` obstruction; it is the campaign's first concrete obstruction
candidate and is recorded rather than assumed away.

### Every stored word fits one packed cell (`INV-WORD-WIDTH` — stride clause proved)

`packedProbePlan_decode` is stated for reads of at most one cell, so the per-read
lowering could not be stated until every stride was known to fit.
`packedSourceStride_le_cellWidth` supplies it. Three arms needed more than
monotonicity: the final rank block width (residual arithmetic `k * k <= 2 ^ k + 3`
plus the rank directory the payload carries), the close summary relative width
(bounded by the last conjunct of the activity predicate itself), and the close
interior offset width (bounded by the readiness guard — a load-bearing use of the
guard `FG-07` requires the controller to consult).

### The physical read (`FG-08` — per-read clause proved)

`packedSourceRead n longCount memory source index` issues the plan and decodes it.
`packedSourceRead_of_some` proves every successful logical read is reproduced
exactly. The zero-width branch issues no probe at all and is where the sentinel
words land; the positive-width branch derives containment from the successful read
rather than assuming it, which is what rules out the degenerate reading in which
the offset runs past the payload and truncated subtraction hides it.

### The executed segment universe (`FG-08` clause (c), measured)

This is the most consequential result on the branch and it is negative, so it is
stated with its evidence.

`concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global` (pre-existing)
says the store the whole-query evaluator runs against is the *canonical reviewer*
store. `ExecutedUniverse.lean` then computes what that store reads, by `rfl`:

| segment | executed store reads | flat payload store reads |
| --- | --- | --- |
| `0`, `16`, `19` (and `1` .. `18`) | the flat payload's own sources | the same |
| `20` | `canonicalRelativeRmmInteriorComponentStore shape` | close summary baseline column |
| `21` | `bpFringeChunkTable ...` | close summary minRel column |
| `22` | `bpChunkSelectTable ... false` | close summary maxRel column |
| `23` and up | `none` | close summary argOffset, close interior, retired slots |

So the two agree exactly on segments `0` .. `19` and diverge from `20` up. The
divergence is not a renumbering: the three objects the executed store reads at
`20`, `21` and `22` are not sources of the flat payload at all. The flat payload's
close half is `concreteCompactBPCloseLCADirectory`, whose `payload_eq_interior`
field makes it the **compact** interior directory (summary, local, global, under a
readiness guard); the executed close half is
`canonicalRelativeRmmInteriorDirectory` (summary, local, global, **local level,
global level**) followed by the two chunk tables. The module that defines the
reviewer layout says so in its own docstring: the flat close payload "remains
available only through the compatibility layout".

Consequence: `packedMemory`, which serializes the `FG-01` payload object, can back
executed segments `0` .. `19` and nothing beyond. Every per-read theorem in
`PhysicalRead.lean` is therefore sound but partial as a *whole-machine* claim, and
`INV-GLOBAL-PHYSICAL-MACHINE` names precisely this deficit.

**This is not a `K1` obstruction.** The header cell is not involved, and no frozen
`K1` quantifier is contradicted. It is a mismatch between two frozen rows --
`FG-01` names one payload object, `FG-08` requires the execution to probe the
memory built from it — and resolving it is a question about the close route.

### The replay harness (`FG-12`, partially exercised)

`scripts/eg_cp_final_falsification_replay.ps1` encodes the sixteen-entry frozen
registry literally and in the commissioned order. A case is replayed by applying
one textual mutation to one tracked file, rebuilding the named failing surface,
and requiring the commissioned verdict *at that surface* -- a build that fails
somewhere else is reported `WRONG-SURFACE`, not as a pass.

Run on 2026-08-04, full mode, committed clean tree:

| case | outcome | at |
| --- | --- | --- |
| `A01-PRODUCTION-EXPECTED-ACCEPT` | ACCEPT | unchanged candidate builds |
| `M01-WRONG-LONG-COUNT` | REJECT | `PackedCellProbe/SourceGeometry.lean` |
| `M03-SHAPE-PARAMETER` | REJECT | `PackedCellProbe/PhysicalRead.lean` |
| `M05-SIBLING-STORE` | REJECT | `PackedCellProbe/PhysicalRead.lean` |
| `M08-FORGED-PROBE-CAP` | REJECT | `PackedCellProbe/Probe.lean` |
| `M09-WRONG-CELL-CROSSING` | REJECT | `PackedCellProbe/Probe.lean` |
| `M10-SPARSE-COUNT-DEPENDENCY` | REJECT | `PackedCellProbe/SourceGeometry.lean` |
| `M11-SIBLING-PAYLOAD` | REJECT | `PackedCellProbe/Payload.lean` |
| `M14-LONG-COUNT-IGNORED` | REJECT | `PackedCellProbe/SourceGeometry.lean` |
| `A02`, `M02`, `M04`, `M06`, `M07`, `M12`, `M13` | TARGET-ABSENT | no such surface on this candidate |

Three things the harness caught about itself, each of which would have been a
false pass:

1. Restoration through `Set-Content -Encoding utf8` adds a BOM and rewrites CRLF.
   The SHA256 restoration check failed the first time it ran. The harness now
   captures and restores raw bytes.
2. `Start-Process -PassThru` reported a non-zero exit code for a build that
   succeeds when run directly, which would have made every case look like a
   REJECT. The harness drives `System.Diagnostics.Process` itself.
3. `M03` was recorded as rejecting at the exact-signature consumer. It does not:
   adding a parameter breaks the library's own uses first, so the build never
   reaches the consumer. The expectation was corrected downward.

Two records are deliberately weaker than the registry's wording. `M01` and `M14`
reject at the source-geometry equation, which depends on the decoded header value
but is **not** a value-projection liveness witness; `FG-11` still has no `.result`
or next-address inequality and these mutations do not supply one.

### Three payload objects, and which one each layer uses

This is the campaign's terminal finding and it is negative, so it is stated with
its evidence and with its limits.

| object | who uses it | at the size-three left spine |
| --- | --- | --- |
| `concreteBPNativeSuccinctRMQPayload <family> shape` | what `FG-01` pins, what the public `Costed` semantics is payload-backed by, and what `packedMemory` serializes | `21466` bits, close component `0`, the rest padding to the size-only budgets |
| `concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape` | what the word-RAM execution reads, through `concreteBPNativeSuccinctRMQGlobalReadStore` | `305` bits: canonical interior directory `100`, fringe chunk `40`, select chunk `8` |

`FG-01` names a *function* with an access-family parameter, so the first thing to
rule out was that I had instantiated it wrongly. The public payload uses a
different family --
`builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.toWeakFamily`
rather than `builtGenericSparseExceptionSelectBPCloseAccessFamily` -- but the two
produce the same payload value at the witness shape. The instantiation was not the
error.

The two objects are not related by a bridge. `packedStoresNotEqual` proves the
flat payload store and the executed store are unequal whenever the close summary
carries a block, disagreeing at segment `23` where the executed store is silent
and the flat store answers.

**What follows.** `FG-08`'s whole-run clause, and with it `FG-10`, `FG-11` and the
seven `TARGET-ABSENT` replay cases, cannot be closed while `packedMemory`
serializes the object `FG-01` names. This is not a `K1` obstruction: the header
cell appears in none of these theorems and no frozen `K1` quantifier is
contradicted.

**What is deliberately not claimed.** That the project's headline claim conflates
the two objects. Both layers carry their own space bound. Whether any public
statement composes a bound proved for one with an execution performed on the other
is a question about the headline claim rather than about this gate, and it is
outside what has been checked here. It is written down because a reviewer running
`M11-SIBLING-PAYLOAD` at project scale would want to ask it.

## 5. Exact-type consumers

`RMQ/Validation/EGCPFinalFalsification.lean` states each dependency's expected
type independently and discharges it with the library result, so weakening a
library theorem breaks that file rather than being absorbed by it. It imports
`Payload`, `Header`, `Memory`, `Space`, `Address` and `Probe`, and pins: the
payload identity and the header-then-payload decomposition; the shape-free
factorization signature, the close base, terminality, the counting guard and the
long-count term; `P`, `w`, the count fit, header arity and decoding, including
both shapes of size two; the memory round trip and cell arity; the space bound
and residual; the bit-address signature and the header shift; and the probe plan
with allocation, coverage, decoding, charged count, the two boundary facts, and
concrete instances at sizes 0, 1 and 2.

`#print axioms` over a theorem's current type would not do this: it reports what
a declaration happens to say now. These consumers say what it must say.

## 6. The `FG-07` question, settled by proof

The obstacle to reusing the existing supplied-store leaves is that they are built
from `GenericSelect.sparseExceptionSelectData shape.bpCode false`. Two readings
were possible, and they lead to very different campaigns. Either that record
supplies the **replies**, in which case the store is decoration and `FG-07` needs
a different execution architecture; or it supplies only the **geometry** --
strides, field widths, slot counts -- in which case `FG-07` needs the same kind of
`Nat`-only mirror the offsets already have.

It supplies only the geometry, and that is now checked:

```
packedSelectEntryRead_content_free :
  forall (tableLeft  : FixedWidthSparseDenseSelectDenseLocalEntryTable entriesLeft  widthLeft)
         (tableRight : FixedWidthSparseDenseSelectDenseLocalEntryTable entriesRight widthRight)
         (layout) (store) (index),
    tableLeft.readTraceResultRelabeledWithStore  layout store index =
    tableRight.readTraceResultRelabeledWithStore layout store index
```

The two tables share **no** parameter: unrelated entry lists, unrelated field
widths. They nevertheless produce the same trace result — the same reads, in the
same order, with the same replies, and the same decoded entry. A leaf satisfying
this cannot be consulting its table for a reply.

The underlying reason is that `SuccinctSpace.PayloadWordStore.readProgram`
ignores its store argument: its binder is `_store` and its body is
`WordRAM.Program.readWord 0 i`. `packedTableReadProgram_content_free` and
`packedTableReadProgram_eq_readWord` record that at the fixed-width-table level.
All three are `rfl`.

A congruence over shapes of equal size would have been weaker and would have
invited the objection in `DD-20260802-001`: a congruence says the result is
determined, not that a controller can compute it. This is stronger in the
direction that matters — the table is not consulted at all.

**This does not close `FG-07`**, and it is not evidence about the close/LCA
leaves, which have not been examined. It bounds the remaining work on the select
side to a `Nat`-only mirror for a fixed list of scalars. Recorded as
`DD-20260804-006`.

### That list, done except one item

`sparseExceptionSelectData` sets `wordSize := wordBits bits.length`,
`superStride := superStride bits.length`,
`localStride := localStride bits.length` and
`localSlotsPerSuper := localSlotsPerSuper bits.length`. Each is a function of the
code length alone, and the code length is `2 * n`. So:

```
packedSelectWordSize n           = GenericSelect.wordBits (2 * n)
packedSelectSuperStride n        = GenericSelect.superStride (2 * n)
packedSelectLocalStride n        = GenericSelect.localStride (2 * n)
packedSelectLocalSlotsPerSuper n = GenericSelect.localSlotsPerSuper (2 * n)
```

each with an agreement theorem against the record field. The mirrors are defined
at `2 * n` rather than at `shape.bpCode.length` deliberately: a mirror at the code
length would be true and useless, because a controller cannot evaluate
`shape.bpCode.length` without the shape. Taking `bpCode_length` at the definition
site rather than the use site is what makes the expression executable.

The leaf's validity dispatch is `idx < occurrenceCount bits target`, and
`packedSelectOccurrenceCount_eq_size` proves that count is `shape.size`. So the
guard is `idx < n`: evaluable from `n` alone, with no header field and no probe.
Had it been anything else, `K = 1` would have needed a second field — which is
exactly the kind of finding that would have forced an architecture decision. It
does not.

`queryOccurrence` binds its record as `_data` and therefore ignores it;
`packedSelectQueryOccurrence_content_free` records that over two records sharing
no parameter. **That closes the select-side scalar list**: four geometry mirrors
at `2 * n` with agreement theorems, `occurrenceCount = n`, and `queryOccurrence`
content-free. Nothing on the select side needs the shape except through `n`.

### All four of the leaf's read helpers are accounted for

`bpChunkedSelectTraceResultWithStore` reaches the supplied store through four
helpers:

| Helper | Result |
| --- | --- |
| four-field entry-table read | content-free (`packedSelectEntryRead_content_free`) |
| dense two-word select read | content-free at a fixed word size (`packedDenseTwoWordSelectRead_content_free`) |
| relative-offset read | takes no record at all; type is `ReadStore -> Nat -> Nat -> Nat -> TraceResult (Option Nat)` |
| two-level rank read | determined by `queryPos pos`, `wordSize`, `blocksPerSuper` (`packedRankRead_scalar_determined`) |
| sparse-directory read | determined by those three plus `localStride` (`packedSparseDirectoryRead_scalar_determined`) |

The dense two-word case is the informative one among the content-free three: the
two bit stores are over *unrelated* bit strings and share only the word size,
which is a type index rather than stored data.

The rank read is the one helper that genuinely consults its record — but only
through `superIndex`, `wordIndex` and `wordOffset`, which unfold to the three
scalars above. Two records over unrelated bit strings, with unrelated overheads
and unrelated query costs, agree whenever those three agree. That is the property
that matters: it consults the record for scalars, not for data.

### Why the assembly theorem was abandoned, and what replaces it

The obvious next step is an assembly theorem: two `SparseExceptionSelectData`
records agreeing on the scalar list produce the same leaf result. **It does not
go through, and the reason is structural rather than a proof-engineering
nuisance.**

`data.bitWords` has type `BoundedPayloadWordStore bits data.wordSize`. Its word
size is a *type index* carrying the record's own field, and the content-free
theorem for the dense two-word read needs both stores at the same index. From a
propositional `dataLeft.wordSize = dataRight.wordSize` between two distinct
records, closing that gap means transporting a dependent type along an equation
between two projections, neither of which is a local variable — so neither
`subst` nor a plain `rw` applies. The pattern recurs at every geometry scalar that
appears as an index rather than a value.

`DD-20260804-008` records the conclusion: **do not build the controller as a
congruence between dependently-indexed records.** Build it as a definition over a
`Nat`-only geometry record — the mirrors already proved size-only, plus the
decoded `longCount` — and relate it to the existing leaf by instantiating at the
canonical shape, not by comparing two arbitrary records. That route has neither
problem: the record's fields are values, so no transport arises, and it is
something a controller can actually hold.

The five helper theorems are not wasted by that decision; they are what makes the
`Nat`-only record adequate, because they show the leaf reads the supplied store
and consults its record only for the scalars such a record would carry.

### The select-side scalar list is discharged

Every scalar `bpChunkedSelectTraceResultWithStore` consumes is now accounted for:

| Scalar | Status |
| --- | --- |
| `wordSize`, `superStride`, `localStride`, `localSlotsPerSuper` | size-only mirrors at `2 * n`, with agreement theorems |
| `occurrenceCount bits target` | proved equal to `shape.size` — the validity guard is `idx < n` |
| `queryOccurrence` | content-free |
| rank `queryPos` | `Nat.min pos bits.length`; both lengths already mirrored size-only |
| rank `wordSize` | mirrors already existed |
| rank `blocksPerSuper`, both records | literal `1` — `rfl` |
| `sparseDirectory.localStride` | `localStride bits.length`, the mirrored expression |

and all five read helpers are content-free or scalar-determined.

The last two were the ones I expected to be hardest. `longFlagRankBlocksPerSuper`
and `sparseExceptionEffectiveFlagRankBlocksPerSuper` each bind both arguments as
`_bits`/`_target` and return `1`. A literal cannot carry shape content, so
neither needs a mirror at all.

The one scalar supplied *beside* the select data — the fringe chunk width the
layout calls `c` — is mirrored too: `packedFringeChunkBits n =
bpFringeChunkBits (2 * n)`, with `packedFringeChunkBits_eq`.

**So nothing the select leaf consumes still needs the shape.** Every input is the
supplied store, a query index, a literal, or a size-only function of `n`.

### The first controller component exists

Everything above is analysis: it says the record does not affect the result. The
next step removes the record from the *definition*.

```
packedSelectEntryRead
  (layout : SparseDenseEntryTableTraceSegmentBases)
  (store : WordRAM.ReadStore) (index : Nat) :
  WordRAM.TraceResult (Option SparseDenseSelectDenseLocalEntry)

packedSelectEntryRead_eq (table) (layout) (store) (index) :
  table.readTraceResultRelabeledWithStore layout store index =
    packedSelectEntryRead layout store index
```

The definition takes a segment layout, a supplied store and an index — no table,
no shape, no list, no proof argument — and the equation holds for **every** table,
over any entries and any field width, **by `rfl`**. The two sides are the same
term, so nothing needs rewriting at a call site and no dependent transport arises
— which is exactly the failure mode that killed the congruence route.

The technique (`DD-20260804-009`) is to inline: where a helper's use of its
record reduces to a term the record does not influence — as
`PayloadWordStore.readProgram` does, binding its store as `_store` — write the
record-free definition with that term substituted and close by `rfl`. It
generalizes only where the influence is definitionally absent; where a helper
genuinely consults scalars, the record-free version takes those scalars as
arguments and the equation becomes conditional on the mirrors above. That is how
the geometry record earns its fields.

**This is the first component of the `FG-07` controller to exist** — previous
results recorded what a controller could be built *from*; this is something a
controller can *call*.

The second component follows the predicted scalar-taking shape:

```
packedRankRead_eq (data) (store) (segments…) (target) (pos) :
  data.bpChunkedRankTraceResultWithStore … pos =
    packedRankRead … store bits.length data.wordSize data.blocksPerSuper pos
```

also by `rfl`, over records with any bit string, any overheads and any query
cost. It takes three scalars because the two-level rank read genuinely consults
its record for those projections — and those three are exactly the ones already
discharged: `bits.length` is mirrored size-only for both rank records the select
leaf uses, `wordSize` has existing mirrors, and `blocksPerSuper` is the literal
`1`. So a controller can supply all three from `n`.

The third composes the first two: `packedSparseDirectoryRead` is built from
`packedRankRead` and the already record-free relative-offset read, plus the local
stride, and `packedSparseDirectoryRead_eq` is again `rfl`. **That the composition
also closes by `rfl` is the point** — the technique composes, so a record-free
definition built from record-free parts accumulates no rewriting obligations.

All five helpers are now record-free definitions. `packedDenseTwoWordSelectRead`
completed the set — its body never mentions its bit store, only the word size
that reaches it as a type index.

### The whole close-select leaf is record-free

```
packedSelectCloseRead
  (layout) (chunkSegment selectTableSegment) (store) (chunkBits) (target)
  (occurrenceCount superStride wordSize localSlotsPerSuper localStride)
  (longFlagBitLength longFlagWordSize longFlagBlocksPerSuper)
  (sparseBitLength sparseWordSize sparseBlocksPerSuper sparseLocalStride)
  (idx) : WordRAM.TraceResult (Option Nat)

packedSelectCloseRead_eq (data) (layout) (segments…) (store) (chunkBits) (idx) :
  data.bpChunkedSelectTraceResultWithStore … idx =
    packedSelectCloseRead … target (occurrenceCount bits target)
      data.superStride data.wordSize … idx
```

by `rfl`, for **every** `SparseExceptionSelectData`.

The signature is the claim `FG-07` makes: no `CartesianShape`, no source program,
no list, no proof callback — and the elaborator enforces it.

**And every scalar the equation supplies has already been discharged** for the
close-select instance: `occurrenceCount bits target = shape.size`;
`superStride`, `wordSize`, `localSlotsPerSuper`, `localStride` have size-only
mirrors at `2 * n`; both `blocksPerSuper` are the literal `1`; both bit lengths
are mirrored size-only; the sparse local stride is the same `localStride`
expression. So **a controller holding only `n` can supply every argument to this
leaf.**

### The close-side rank leaf reuses the same component

`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore` turns out to be
`bpChunkedRankTraceResultWithStore` on `builtRelativeSplitBPCloseRankData shape`
at a different segment base — so the record-free version is `packedRankRead`
again. `packedRankCloseRead` is a thin renaming and `packedRankCloseRead_eq` is
`rfl`.

That matters because it says the close side does not automatically need new
machinery. Of the whole-query program's four instructions:

| Instruction | Store access |
| --- | --- |
| `selectClose` | record-free (`packedSelectCloseRead`) |
| `rankCloseIfSome` | record-free (`packedRankCloseRead`) |
| `outputPredIfSome` | touches no store at all |
| `lcaClose` | takes a `CartesianShape` **directly** — see below |

The two scalars the close rank leaf needs — `wordSize` and `blocksPerSuper` of
`builtRelativeSplitBPCloseRankData` — are **not** both mirrored size-only yet.
`packedRankWordSize` exists with `rankWordSize_eq_packed`; the `blocksPerSuper`
mirror does not, and nothing is claimed about it.

### Where the shape genuinely enters

`lcaClose` is materially different from the other three, and the difference is
visible in the type rather than inferred.
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore` takes
`CartesianShape` as its **first explicit argument** and passes it straight to
`lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore`. The other leaves took
a *derived record*, and inlining removed those records because the helpers
consulted them only for scalars. Here there is no record to remove: the shape is
an argument of the navigator itself.

Two things are recorded rather than estimated:

* `packedLcaCloseLeafSignature` pins the leaf's type, shape argument included.
  This is deliberately a **negative** record — it names the one surface a
  controller cannot call as it stands, and any later claim that `FG-07` is closed
  must either eliminate that argument or exhibit a replacement navigator.
* `packedLcaCloseRankSeed_eq` discharges the rank seed the leaf supplies: it is
  `packedRankCloseRead` at the close rank segment base, by `rfl`.

The navigator's other arguments are three fixed segment constants, the store and
the two close endpoints — none carry shape content. **So the residual is exactly
the navigator's own use of `shape`.**

That use is now itself partly settled. The navigator's body touches `shape` in
exactly two places: the block size that decides same-block versus cross-block,
and the hand-off to the two sub-navigators. The first is size-only —
`canonicalBPRelativeSummaryBlockSizeRaw shape = 2 * (n.log2 + 1)`, mirrored by
`packedSummaryBlockSizeRaw` with `packedSummaryBlockSizeRaw_eq` proved by `rfl`.
**So the navigator's top-level branch is decided by `n` and the two close
endpoints alone** — exactly the inputs `FG-07` permits.

What remains is the recursive hand-off to the same-block and cross-block
sub-navigators, and the same-block one has now been opened.

`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` binds a
local-BP seed and hands it to a seeded reader. The seed comes from
`localBPSeedFromRankCloseTraceResult`, whose only use of the shape is
`localBPWindowBase shape blockSize close` — and that uses the shape only through
`machineWordBits shape.bpCode.length`, the BP-code word width already mirrored.
So `packedLocalBPSeed n rankCloseTrace blockSize close` is the seed with no shape
argument (`packedLocalBPSeed_eq`), and the rank-close reader it takes is supplied
by the caller as the already record-free `packedRankCloseRead`.

The seeded reader has now been opened too.
`bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore` uses its shape in
exactly three places: the fringe chunk width, the local-BP window base, and the
window reader. The first two are already mirrored size-only, so
`packedSameBlockCloseSeededRead` takes the window trace as a supplied argument —
the same pattern the rank seed used — and `packedSameBlockCloseSeededRead_eq`
discharges the rest.

**The same-block branch is therefore down to one remaining shape-taking
function**: the window reader
`localBPWindowBitsTraceResultWithStore`, which is
`map flattenPayloadWords (localBPBlockWordsTraceResultWithStore shape store
blockSize close)`. That reader has not been examined.

The cross-block branch
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
remains untouched.

`FG-07` is still **not** closed. There is no top-level controller definition, no
header-probe-then-address sequencing, and no `receipt`.

**`FG-07` remains Open.** One component is not a controller: there is no fixed
top-level definition, no header-then-address sequencing, no `receipt`, and the
close/LCA leaf tower has still not been examined at all.

Still open: no controller definition exists; the close and LCA leaves have not
been examined at all; and `SuccinctClose.bpFringeChunkBits shape.bpCode.length`
is supplied beside the select data rather than inside it, so it is a separate
mirror obligation. Recorded as `DD-20260804-007` and its two addenda.

## 7. Two defects found and what happened to them

### The layout's unconditional close-interior offsets (found 2026-08-03, still open upstream)

`concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset` computes the two
close-interior offsets **unconditionally** (`FlatPayload.lean:523-526`), while
`concreteBPNativeSuccinctRMQFlatPayloadSourceCountedInFlat` counts those sources
only when the interior is ready. Outside that regime the offsets point past the
end of the close component.

Today this is discharged only by `CountedInFlat` appearing as a *hypothesis* on
`concreteBPNativeSuccinctRMQFlatPayloadSource_component_slice`. A controller has
no such hypothesis available at run time: it must decide readiness. That is why
`interiorReady_iff_packed` matters — readiness is decidable from `n`, so the
guard costs no header field, but it has to be in the controller rather than in a
proof.

This is plausibly the same phenomenon as the `EG-CP-F01` campaign's escalation to
`F07` (attempted probes returning `none` into segment 0 under canonical stores at
small `n`). That has not been checked and should not be assumed.

### This branch's own unconditional two-cell probe pair (found and repaired 2026-08-04)

The first draft of `Address.lean` computed, for a read starting at bit `b`, the
unconditional pair `(b / w, b / w + 1)`, and `packedRead_from_two_cells`
recovered the requested span from the concatenation of those two cells.

The theorem was true, but for the wrong reason at the end of the memory.
`packedCellAt` is total, built from `List.drop` and `List.take`, so at any index
at or past `packedCellCount` it returns the empty list. A read wholly contained
in the final allocated cell therefore "succeeded" while naming an address that
does not exist, and `cell ++ []` absorbed the difference silently.

That is precisely the claim a cell-probe result must not make. The content of a
cell-probe bound is that the algorithm touches `C` real cells of a real memory.

Repaired by `293fb45`: `packedProbeCells`, `packedProbeOffset` and
`packedRead_from_two_cells` were removed and replaced by the conditional plan of
section 4, which fetches through a failing accessor and proves allocation.
`DD-20260804-001` records the decision and supersedes the `FG-07`/`FG-08`
paragraph appended to `DD-20260802-001` on 2026-08-04, which described the three
removed declarations.

## 8. What is not done

`FG-07` and `FG-10` remain the bulk of the work: a shape-free controller whose
actual execution reproduces the project's reference semantics. Nothing so far
constructs one, so every row that quantifies over "the packed execution" —
including `FG-01` through `FG-06`, whose listed clauses are proved — remains
Open on that dependency.

Specifically not done:

* **`FG-07`** the closed controller. The definition now exists
  (`packedWholeQueryRun`) and is proved equal to the supplied-store whole-query
  execution at every shape. What remains is that it consumes an abstract
  `WordRAM.ReadStore` rather than the packed memory, produces no `receipt`, and
  does not itself sequence the header probe or the readiness guard.
* **`FG-08`** the whole-run lowering. The per-read half is now complete for all
  twenty-nine sources, at strides and widths derived rather than supplied. What
  remains is the whole-run half: there is no ordered-trace theorem with
  multiplicity, because no run's trace has been mapped through
  `packedSourceRead`. The lowering is also still stated against the
  **flat-payload** segment universe; the executed global store numbers segments 21
  and 22 differently (documented in `FlatPayload.lean:280-285`), and no bridge is
  claimed -- and that gap is now measured rather than described: the executed
  store diverges from segment `20` up, not at `21` and `22`, and the three objects
  it reads there are not flat payload sources (`DD-20260804-027`).
  `selectSparseRelative` lowers one-directionally, and closing that gap is
  `FG-09`'s totality clause.
* **`FG-09`** totality and the derived cap. Only a per-read bound of two probes
  exists. `packedProbePlan_lt_cellCount` bounds addresses by `packedCellCount n`,
  which is a host-array bound; `INV-ADDRESS-WIDTH` explicitly rejects that as a
  substitute for `address < 2 ^ w n`, and no capacity theorem exists.
* **`FG-10`** same-run correctness. Not started.
* **`FG-11`** liveness and anti-bypass. Not started.
* **`FG-12`** the committed replay registry. The harness exists and was run once
  in full mode on the committed clean tree: 16 cases considered, **9 as
  commissioned at their named surfaces**, 7 `TARGET-ABSENT`, descendant self-test
  PASS, every mutation restored with a verified SHA256, terminal tree clean,
  exit 7. What remains is that seven commissioned cases -- `A02`, `M02`, `M04`,
  `M06`, `M07`, `M12`, `M13` -- name a run, a trace, a controller over
  `packedMemory`, or a capstone, none of which exist, so full mode is
  `INCOMPLETE` rather than a pass. The row also wants an expected-type consumer
  pinning the full capstone, and there is no capstone.
* **`FG-13`** trust and same-object composition. The hygiene and native-decision
  scans are clean, but there is no capstone whose object identity could be
  traced.
* **`FG-14`** boundaries. Only the packed-representation boundaries exist (final
  allocated cell, crossing, sizes 0/1/2). The query-level boundaries — empty,
  reversed, out-of-range endpoints, the `5488/5489` long crossover, the
  `[1024, 1330]` interior-readiness window — are untouched.
* **`FG-15`** the durable decision set. This document and the design-decision
  entries exist; the completed matrix does not, because the rows are open.

### The next smallest proof target

A shape-free **stride** and a shape-free **read width** per source, with their
agreement theorems. The BP code has both; twenty-eight sources do not.

The BP-code work narrowed the shape of this target: it is not one function.
`DD-20260804-004` records why. For a `FixedWidthNatTable` source the stride and
the read width are the same number, and it is already available as the table's
`width` type index, so the agreement is the structure's own
`word_length_of_get?` field composed with an existing width mirror. For a chunked
bit source they differ, and the read width is a `min` in `(n, index)` exactly as
`packedBpCodeReadWidth` is.

The smallest next step is therefore the generic chunked-source lemma the BP code
should have been an instance of: given a source whose words are
`chunkPayloadWords stride sourcePayload`, whose `sourcePayload` is the canonical
payload slice at its flat offset (which
`concreteBPNativeSuccinctRMQFlatPayloadSource_flat_slice` already supplies under
`CountedInFlat`), and whose stride is at most one cell, the probe plan at the
strided address and the `min` read width decodes to the store word. That closes
`selectLongFlagBits`, `selectSparseFlagBits` and `finalRankBPCodeAlias` together;
their stride mirrors (`packedLongFlagWordSize`, `packedSparseWordSize`) and
payload lengths (`longFlagBits_length_eq_packed`,
`sparseFlagBits_length_eq_packed`) already exist.

The remaining twenty-five fixed-width-table sources then need one
`packedSourceWidth` selection and a 25-arm agreement proof, built on the mirrors
already in `SourceFactorization.lean`: `packedSuperWidth`, `packedLocalWidth`,
`packedRankWordSize`, `packedRankBlockWidth`, `packedSummarySuperWidth`,
`packedSummaryRelativeWidth`, `packedInteriorOffsetWidth`.

Do **not** define a width mirror before its agreement theorem: an unproved mirror
would make the lowering look closed while the only load-bearing step was
missing.

### Approaches tried and rejected

* **A congruence instead of a mirror** (recorded in `DD-20260802-001`): proving
  that equal size and equal long count imply equal offsets would show the offsets
  are *determined* by `(n, longCount)` without producing anything a controller
  could evaluate. Rejected: a controller has to compute addresses, not be
  promised they exist.
* **Synthesizing a canonical shape from `n`** inside the offset function:
  forbidden by registry mutation `M04-CANONICAL-SHAPE-BY-N`.
* **An enumeration/census of executed offsets**: failed three times on this exact
  surface (`DD-20260726-006`), always because the enumeration's completeness
  became a separate and false argument. Replaced by closed-inductive `cases`
  coverage.
* **Keeping the unconditional two-cell pair and adding an in-range hypothesis**:
  rejected in favour of the conditional plan, because with a total accessor the
  decoding theorem holds whether or not the address exists, so no mutation of the
  address arithmetic could be detected by it.

## 8b. State at the handoff, and the enumerated remaining work

This section supersedes section 8 where they disagree. Section 8 was written
before the payload question was settled and still describes the campaign as
targeting the flat payload.

**Where the payload question landed.** `FG-01` names two objects -- the identifier
`concreteBPNativeSuccinctRMQPayload`, and *the object consumed by the accepted RMQ
semantics*, which is `concreteBPNativeSuccinctRMQCanonicalReviewerPayload` because
`buildPayload xs` is defined as exactly that. The frozen registry decides between
them: under the identifier reading the candidate proves space for one payload
while executing another, which is `M11-SIBLING-PAYLOAD`, a commissioned REJECT. So
`payloadBits` is the consumed object (`DD-20260804-038`). Two earlier conclusions
about this were wrong and are retracted in `DD-20260804-036` and `-037`; the
record keeps both the errors and their repairs.

**What that unblocks.** The segment `20`/`21`/`22` deficit of `DD-20260804-027`
disappears, because those three are the reviewer payload's own close component and
chunk tables. `packedStoresNotEqual` remains true about a store the candidate no
longer uses.

**The sparse count, settled.** `DD-20260804-022` recorded one source of
twenty-nine whose word count is not a function of `(n, longCount)`, and it
distorted the design for many commits -- forcing a capacity bound, a
one-directional lowering, and an exclusion in the store equality. It is now proved
vacuous below a located threshold: at unit stride a slot covers one occurrence, so
its span is at most one, so the exception predicate is unsatisfiable, so the table
is empty (`packedSparseExceptionEntries_nil_of_unit_stride`). `localStride (2n)`
is `1` for every size below `2 ^ 96`, first exceeding one at `m = 2 ^ 97`.
Consequently the reviewer payload's length is size-only on that whole range, which
is what the cell machinery needs.

**Enumerated remaining work, in order:**

1. `packedReviewerPayloadLength n` -- the size-only length equation for the new
   payload, under the unit-stride hypothesis. The eighteen live access sources
   already have length mirrors; the close directory, fringe chunk table and select
   chunk table need three more.
2. Re-point `packedSerializedBits`, `packedCellWidth`, `packedCellCount`,
   `packedAllocatedBits` and `packedMemory` at that length. The probe plan,
   address bounds, word-width and word-value theorems are stated over those and
   should transfer with their proofs largely intact.
3. Seven new source word geometries for the close half: the canonical interior
   directory's five tables and the two chunk tables.
4. Then the whole-run lowering: `packedBackedStore` over the new memory, footprint
   agreement, ordered trace with multiplicity, and the constant probe cap derived
   from the run.
5. Then `FG-10`, `FG-11`'s value half, `FG-13`, `FG-15`, and the seven
   `TARGET-ABSENT` replay cases, all of which quantify over that run.

**Until step 2 lands, `packedMemory` still serializes the old object**, `FG-06`'s
bound is still proved over it, and the candidate would still fail `M11`. Nothing
in this document should be read as claiming otherwise.

## 9. What a skeptical reviewer should ask

- `packedSourceComponentOffset` is proved equal to the canonical offset, and now
  `packedLogicalProbePlan` calls it — but nothing *executes* `packedLogicalProbePlan`.
  Is this a factorization of the executed addressing or only of a definition that
  happens to describe it? (The latter. The row says so.)
- The probe plan's allocation theorem bounds addresses by `packedCellCount n`.
  That is a list-length bound. What relates it to `2 ^ packedCellWidth n`?
  (Nothing yet. `INV-ADDRESS-WIDTH` is untouched.)
- `packedProbeCount_le_two` is a bound on **one** read. Multiplying it by a
  logical trace length would presuppose the trace, and the trace is what does not
  exist. Does any prose here suggest otherwise?
- The per-read lowering is stated against the flat-payload segment universe.
  The executed store uses a different numbering at 21 and 22. Which universe does
  a future whole-run theorem lower, and where is the bridge?
- `packedProbe_final_cell` requires `0 < width`. Is the zero-width case a real
  read, or is the three-way plan hiding a case? (Zero-width requests an empty
  range and issues no probe; `packedProbePlan_decode` covers it and returns the
  empty window.)
- `PackedSummaryActive` is a six-conjunct decidable predicate. Is it actually
  decidable in the sense a controller needs, or merely `Decidable` in Lean?
- The close side's step function is non-monotone in `n`. Does any later row
  assume monotonicity?

## 10. Verification

Development-loop checks on this branch's tip:

| Command | Outcome | Observed runtime |
| --- | --- | --- |
| `lake build RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe` | green | 4–13 s incremental |
| `lake build RMQ.Validation.EGCPFinalFalsification` | green | 8 s incremental |
| `lake env lean` on each changed module | green | 2–4 s each |
| hygiene scan over `RMQ lakefile.toml` | clean (no matches) | seconds |
| `rg native_decide\|Lean.ofReduceBool RMQ` | clean (no matches) | seconds |
| `git diff --check`, `git diff --check HEAD~1..HEAD` | clean on every commit | seconds |
| `design_decision_check.ps1 -Strict -Base HEAD~1` | clean on every commit | seconds |

Checks on the tip of this session's work (clean tree, after the header-probe
commit):

| Command | Outcome | Observed runtime |
| --- | --- | --- |
| `lake build RMQ` (whole library, under the heavy-verification mutex) | green | 1.6 s fully cached; 3.9 s on the first post-repair run |
| `git diff --check 6078a29..HEAD` (whole committed range) | clean | seconds |
| `claim_drift_scan.ps1 -Strict` | exit 0, 1498 hits, 0 strict failures | ~1 min |
| `git merge-base --is-ancestor 0a18548 HEAD` | the freeze is still an ancestor | seconds |
| `git merge-base --is-ancestor 6078a29 HEAD` | the session's starting HEAD is still an ancestor | seconds |

The cold `lake build RMQ` baseline recorded at `6078a29` was 683 s; every run in
this session was incremental against a warm tree in this worktree, which has its
own `.lake`. Only one heavy Lean process ran at a time, under the
`Global\RMQHeavyVerification` mutex.

The aggregate `scripts/gate.ps1`, `scripts/headline_axiom_check.lean` and the
replay harness have **not** been run. The first two are reserved for a final tree
that does not yet exist; the third does not exist at all, which is why no
mutation in the frozen registry has been exercised.

## 8c. Re-target step one, and a correction to why the re-target is happening

Supersedes the corresponding parts of section 8b. Sections 8 and 8b stand as
written; this records what changed.

### What landed

`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerLength.lean`, the first of the
five enumerated re-target steps.

```
packedReviewerPayloadLength (n longCount : Nat) : Nat
packedReviewerPayloadBits_length_eq   : exact length, under unit stride
packedReviewerPayloadLength_le_bound  : that length <= 2*n + reviewerOverhead n
packedReviewerAccessLength_eq         : the eighteen-source live access half
packedSparseRelativePayload_length_of_unit_stride
packedReviewerCountedAccessSources_eq : drift guard, by rfl
packedExecutedStore_is_reviewerStore  : the executed store IS the reviewer store
```

Two of section 8b's estimates were wrong in the branch's favour. The close
directory, fringe chunk table and select chunk table were listed as needing three
new length equations; all three already existed as exact size-only equalities
(`canonicalRelativeRmmInteriorDirectory_payload_length_eq_raw`,
`bpFringeChunkTable_payload_length`, `bpChunkSelectTable_payload_length`) and were
consumed directly.

One estimate was wrong against the branch, and it is a design change rather than a
missing lemma. **The consumed payload has no input-size-only length.** It carries
no padding fields, and its `selectLongRelative` source has `longCount`-many rows,
so `FG-04`'s literal `P(n)` does not exist for it. The exact length is
`packedReviewerPayloadLength n longCount`. See `DD-20260804-043`: this is the
"checked equivalence-required correction" `FG-04`'s own text allows, and it makes
`K1`'s header load-bearing rather than decorative -- under the flat payload the
layout was size-only without the header.

The formula was checked against evaluation: at sizes `0..7` it reproduces
`[75, 158, 298, 305, 613, 616, 652, 655]`, the measured payload lengths. The
contrast with the flat object at `n = 3` is `305` against `21466` bits.

The unit-stride hypothesis was also checked rather than assumed. `localStride`
first exceeds `1` at `n >= 2 ^ 97`; evaluated from `0` to `100000` it is `1`
throughout. It is not a small-input restriction.

### The correction

`DD-20260804-038` justified the whole re-target by reading `M11-SIBLING-PAYLOAD`
as forcing the consumed object. **That reading was wrong** -- `M11` is an
anti-vacuity mutation which the existing `rfl` identity already defeats. This is
the third retraction in this campaign of a conclusion drawn from the shape of a
requirement rather than from a definition, and like the other two it was caught by
reading the definition.

The re-target survives on a better basis: the repository theorem
`concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global` proves the
reviewer store *is* the executed store, so the consumed object is settled by a
checked fact rather than by an argument.

A naming trap sits on this exact question: `SuccinctRMQClassic.flatPayloadReadStore`
is an `abbrev` for the **reviewer** store, not for a store over the flat payload,
and it has no consumers in the tree.

### An `FG-01` defect, reported and not resolved

`FG-01` names its object twice and the two identifications diverge. By name it is
`concreteBPNativeSuccinctRMQPayload`, the flat object. By property it is the one
"consumed by the accepted RMQ semantics", which is the reviewer object. The two
are provably different (`packedStoresNotEqual`, and the segment-by-segment
disagreement at `20`, `21`, `22`).

Both clauses are discharged separately, each against the object it names. The
frozen row is **not** rewritten -- amending it is an owner decision and the
standing instruction forbids weakening a frozen requirement. `FG-01` stays `Open`
pending an owner ruling on which clause governs.

This is not a `K1` obstruction and the campaign does not stop for it. `K1` is
untouched; no theorem here shows it needs extra metadata, a new primitive, or an
architecture change.

### Remaining, in order

1. Re-point `packedCellWidth` at the advertised bound `2*n + reviewerOverhead n`.
   The single funnel is `packedMachineWordBits_le_cellWidth`; every stride use
   passes a bound below `2*n` except the rank block square, which needs
   `rankWordSize^2 <= 2*n + reviewerOverhead n + 2`.
2. Re-point `packedSerializedBits`, `packedCellCount`, `packedAllocatedBits` and
   `packedMemory`, with the count taking `longCount` from the header.
3. Seven close-half source word geometries (five interior tables, two chunk
   tables).
4. Whole-run lowering over the new memory; derived probe cap.
5. `FG-10`, `FG-11`'s value half, `FG-13`, `FG-15`, and the seven `TARGET-ABSENT`
   replay cases.

No `FG` row is closed by this section and no `K1` obstruction is proved.

## 8d. The re-target's space half is complete; the execution half is not

State at this section: `77` campaign commits on
`codex/eg-cp-final-falsification-gate-r1`, base `6078a29` and freeze `0a18548`
both verified ancestors, `lake build RMQ` green, `claim_drift_scan -Strict` at
`1498` hits and `0` strict failures, `design_decision_check -Strict` clean per
commit, working tree clean.

### What now exists over the consumed payload

Five additive modules. `packedMemory`, `packedCellWidth` and every flat-payload
theorem are untouched, so the previously recorded evidence still means what it
said and the re-target has stayed reversible throughout.

```
ReviewerPayload.lean   identity to buildPayload, by rfl
ReviewerLength.lean    exact length as a function of (n, longCount)
ReviewerWidth.lean     input-size-only width; all 29 stride arms
ReviewerMemory.lean    header, serialization, count, allocation, cells
ReviewerCrossing.lean  round trip, payload recovery, two-cell span bound
ReviewerSpace.lean     FG-06's form, with a little-o linear residual
```

The load-bearing statements:

```
packedReviewerPayloadBits_eq_buildPayload      : the object is the advertised one
packedReviewerPayloadBits_length_eq            : exact length, under unit stride
packedSourceStride_le_reviewerCellWidth        : INV-WORD-WIDTH's stride clause
packedReviewerHeaderBits_decode                : the header recovers longCount
packedReviewerMemory_cell_length               : every cell exactly one width
packedReviewerMemory_header_cell               : the header is cell zero
packedReviewerMemory_recovers_payload          : no payload bit lives outside
packedReviewerSpan_from_two_cells              : two cells suffice for any span
packedReviewerMemory_length_mul_width_le       : cells * width <= 2n + rho n
packedReviewerRho_littleO
```

### Why the header is now load-bearing

The consumed payload has no input-size-only length, so `packedReviewerCellCount`
takes `longCount` while `packedReviewerCellWidth` takes only `n`. A controller
reads cell zero at the size-only width, decodes `longCount`, and only then knows
how many cells exist.

Under the flat payload the count was already size-only, so a controller could have
computed it from `n` and ignored the header entirely. That is worth stating
plainly: `K1`'s header was decorative against the old target and is on the
critical path of addressing against the new one.

### What is still missing, in order

1. Seven close-half source word geometries -- five interior tables, two chunk
   tables. Until these exist the per-source lowering does not reach the consumed
   payload's close half.
2. A physical read and backed store over `packedReviewerMemory`, mirroring
   `PhysicalRead.lean`.
3. Whole-run lowering: ordered trace with multiplicity, and the probe cap derived
   from the actual run rather than asserted.
4. `FG-10` correctness against the independent reference; `FG-11`'s value half;
   `FG-13`; `FG-15`.
5. The seven `TARGET-ABSENT` replay cases, which need the surfaces above to exist
   before their selectors can be non-vacuous.

### Standing status

**No `FG` row is closed. No `K1` obstruction is proved.** The `FG-01` divergence
recorded in section 8c is a defect in a frozen row, not an architecture
obstruction, and is left for the owner: the row is not rewritten and its status
cell is not touched.

This checkpoint is **not** `CANDIDATE_COMPLETE`.

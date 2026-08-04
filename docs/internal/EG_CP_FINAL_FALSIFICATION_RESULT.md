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

Last update: 2026-08-04, in the commit titled "Probe the header cell for the long
count", which was the branch tip when this line was written. Earlier tips this
document described: `4d2ed70`, `5c05016`, `08d63c7`.

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
→ `Address` → `Probe`. The validation root is
`RMQ/Validation/EGCPFinalFalsification.lean`.

| Module | Row | What it establishes |
| --- | --- | --- |
| `SourceFactorization.lean` | `FG-02`, `FG-03` | Nat-only mirrors and the shape-free flat address |
| `Payload.lean` | `FG-01` | the stored bits are the canonical payload object |
| `Header.lean` | `FG-04` | `P n`, `w n`, count fit, decoding, `n = 0,1,2` |
| `Memory.lean` | `FG-05` | cells, allocation, round trip, cell crossing |
| `Space.lean` | `FG-06` | allocated-bits bound and its little-o residual |
| `Address.lean` | `FG-07`, `FG-08` | bit addresses and the header shift |
| `Probe.lean` | `FG-05`, `FG-08`, `FG-09` | the conditional probe plan; the BP code lowered completely |

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

## 6. Two defects found and what happened to them

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

## 7. What is not done

`FG-07` and `FG-10` remain the bulk of the work: a shape-free controller whose
actual execution reproduces the project's reference semantics. Nothing so far
constructs one, so every row that quantifies over "the packed execution" —
including `FG-01` through `FG-06`, whose listed clauses are proved — remains
Open on that dependency.

Specifically not done:

* **`FG-07`** the closed controller. Not started. The existing whole-query
  evaluator `WholeQueryProgram.evalGlobalWordTraceWithStore` takes `shape` as a
  parameter, and its leaves take `GenericSelect.sparseExceptionSelectData
  shape.bpCode false`, so it cannot be reused unchanged: making it shape-free
  requires factoring each leaf's geometry through `(n, longCount)` the way the
  offsets already are.
* **`FG-08`** the whole-run lowering. Only the per-read half exists: with a
  supplied width for a general source, and with everything supplied for the BP
  code alone. Twenty-eight sources still need a stride and a read width. There is
  no ordered-trace theorem with multiplicity. The lowering is also stated against
  the **flat-payload** segment universe; the executed global store numbers
  segments 21 and 22 differently (documented in `FlatPayload.lean:280-285`), and
  no bridge is claimed.
* **`FG-09`** totality and the derived cap. Only a per-read bound of two probes
  exists. `packedProbePlan_lt_cellCount` bounds addresses by `packedCellCount n`,
  which is a host-array bound; `INV-ADDRESS-WIDTH` explicitly rejects that as a
  substitute for `address < 2 ^ w n`, and no capacity theorem exists.
* **`FG-10`** same-run correctness. Not started.
* **`FG-11`** liveness and anti-bypass. Not started.
* **`FG-12`** the committed replay registry. Not started. `scripts/eg_cp_final_falsification_replay.ps1`
  does not exist, so **no mutation in the frozen registry has been run**, and
  every matrix row whose anti-vacuity challenge is a registry ID has an unrun
  challenge.
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

## 8. What a skeptical reviewer should ask

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

## 9. Verification

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

# BV-1 canonical supplied-store select semantics leaf

Status: INCOMPLETE (whole BV-1 composition). The assigned SelectSemantics leaf
is proved and checked, for coordinator reconstruction. The full BV-1 acceptance
matrix remains OPEN; this leaf does not establish the source/physical-reader
composition or the final allocation theorem.

Governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Continuation checkpoint: `645a0502b9da9ad6444edbe44759e1c2c5661f25`.
The canonical proof-sprint preflight already passed for this worker role at
this continuation. Scope is only `SelectSemantics.lean` and this evidence file;
the coordinator owns integration, shared modules, and ledgers. No independent
commit and no Lean process before an explicit shared build slot grant.

## Frozen target and consumer

For every `bits : List Bool`, `target : Bool`, and arbitrary `idx : Nat`, let
`d := sparseExceptionSelectData bits target` and
`c := SuccinctClose.bpFringeChunkBits (2 * bits.length)`. Prove:

```lean
(packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
  21 22 (genericReadStore bits target) c false
  (occurrenceCount bits target) d.superStride d.wordSize
  d.localSlotsPerSuper d.localStride d.longFlagBits.length
  d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
  d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
  Succinct.select target bits idx
```

This exact scalar computation is the canonical semantic consumer of the
controller worker's arbitrary-store `selectCloseBlock` refinement. The actual
store is `ReaderInterface.genericReadStore bits target`: segment zero normalizes
each present raw word, directory segments 1 through 16 remain unchanged, and
shared segments 21 and 22 are the honest rank table and false-select table.
In particular, flag words at segments 11 and 15 are not normalized.

The controller consumes target-specific geometry and occurrence count while
calling dense operations with target false. A normalization-only List theorem
does not close this leaf. All chunked dense rank calls and the selected chunked
word-select call must be connected to their supplied reads. Invalid occurrences
are included by the controller's existing validity guard.

Coordinator-approved strengthening: the main refinement also accepts an
arbitrary `store : WordRAM.ReadStore` under exactly this agreement:

```lean
def SelectStoreAgrees (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) : Prop :=
  ∀ segment index, segment < 17 ∨ segment = 21 ∨ segment = 22 →
    store.readWord? segment index =
      (genericReadStore bits target).readWord? segment index
```

`selectRead_value_eq_of_agree` compares the same explicit controller expression
with this arbitrary store to the existing chunked value, and
`selectRead_value_of_agree` concludes `Succinct.select target bits idx`.
The original canonical theorem remains the required reflexive-agreement
consumer. Segments 17 through 20 can therefore hold the planned rank extension
without affecting select. No contents, emptiness, or agreement assumption is
made for those segments or for segments above 22.

## Frozen leaf acceptance rows

| ID | Requirement | Planned evidence |
|---|---|---|
| SS-RAW | Show raw bitWords same for true/false builders. | Equality of the actual canonical arrays, by constructor unfolding. |
| SS-GEOM | Derive c positive and all three word sizes at most 8*c canonically. | Existing record word-size bounds, machine-word monotonicity n <= 2*n, existing all-size fringe bound. |
| SS-DENSE | Whole normalized dense computation, including rank/chunk calls. | Shared-table supplied-read exactness, normalization length/rank/select identities, both dense word branches. |
| SS-CONTROLLER | All-size both-target source .value theorem, arbitrary occurrence. | Exact frozen expression above; unchanged entry, long flag, sparse flag and relative reads; SS-DENSE; existing bpChunkedSelectCosted_exact. |
| SS-CONSUMER | Exact typed direct consumer and trust diagnostics. | Narrow source build, exact proposition consumer, axiom reports, hygiene and whitespace scans. |
| SS-EXTEND | Same value refinement for arbitrary stores agreeing only on actual select segments, with canonical consumer retained. | `SelectStoreAgrees` and the explicit arbitrary-store semantic endpoint above. |

Full TraceResult equality to an unnormalized target-aware run is not claimed:
normalizing segment-zero words changes the replies recorded in read events.
The required returned-value transport is the endpoint. No public or process
architecture decision is made here; this implements the coordinator-approved
route. Design and workflow ledgers remain coordinator-owned.

## Proof plan

The generic table agreements first convert supplied-store word-rank/select
calls to existing honest chunk computations. Their exactness returns canonical
List rank/select values, and normalization transports false to the requested
target. The dense two-word computation then returns the original dense leaf's
value for the same original bit store and geometry. Entry tables and exception
paths consume unchanged supplied-store replies. The full branch tree refines
the existing generic select computation, whose all-size theorem yields the
reference List select answer after the three canonical bounds are discharged.

## Checked evidence and object chain

SS-RAW is `canonical_bitWords_target_eq`: for arbitrary bits and target the
actual `.bitWords.store.words` of `sparseExceptionSelectData bits target` equals
the false builder's actual raw array. The proof is `rfl`; both builders select
the same canonical chunk store on the original input list.

SS-GEOM is the exact conjunction `0 < c ∧ d.wordSize ≤ 8*c ∧
d.longFlagRankData.wordSize ≤ 8*c ∧
d.sparseDirectory.rankData.wordSize ≤ 8*c`, for the exact d/c above. No size,
word-size, or positivity assumption remains in the canonical endpoint. The
canonical proof uses each original record's own machine-word bound, then
`machineWordBits bits.length ≤ machineWordBits (2*bits.length) ≤ 8*c`.

SS-DENSE proves, for arbitrary bounded original bit store and any supplied
store returning its normalized word Options, the exact equality
`(packedDenseTwoWordSelectRead wordSegment rankSegment selectSegment c false
store wordSize basePosition baseOccurrence occurrence).value =
(denseTwoWordSelectCosted target bitWords basePosition baseOccurrence occurrence).value`.
Its remaining assumptions are c positive, original wordSize at most 8*c, the
normalized raw read agreement, and honest rank/false-select table agreements.
The successful first and second original reads supply the word-length bounds.
The two first-word ranks and either selected in-word select are each traced
through the supplied shared tables before the previous normalization identities
are applied. Missing replies remain missing; no word is invented.

SS-CONTROLLER and SS-EXTEND are the literal explicit expressions already quoted
above, now compiler checked. For entries1..8 the four supplied reads decode to
the same counted entry table values. Long flag rank9..11, relative12, sparse
rank13..15, and sparse relative16 use the existing supplied-read agreement
theorems. Both flags retain their original target-independent rank-true use;
only raw segment0 is normalized. The branch proof consumes SS-DENSE and then
`bpChunkedDenseTwoWordSelectCosted_value_eq` to identify the same existing
chunked dense value. It establishes the whole controller's value equals
`d.bpChunkedSelectCosted c idx`. Finally `bpChunkedSelectCosted_exact` consumes
the exact d, idx, and all three bounds from SS-GEOM and returns
`Succinct.select target bits idx`.

SS-CONSUMER includes both an in-source explicit expression consumer and a fresh
import consumer whose exact contents are preserved below. The latter checks
seven expected propositions: raw identity, all canonical bounds, complete
canonical expression, complete arbitrary-store expression, one present query,
one invalid query, and the same-domain mutation refutation.

## Anti-vacuity

The accepted predicate P(run) is
`∀ bits target idx, (run bits target idx).value = Succinct.select target bits idx`.
The checked mutation uses exactly that predicate and domain with the run
replaced by `fun _ _ _ => WordRAM.TraceResult.pure none`.
`constant_none_select_rejected` proves its negation using bits `[true]`, target
true, occurrence0, where the expected answer is `some 0`. It has no axioms.
This is a kernel-checked theorem, not an unrecorded terminal mutation. It does
not claim to cover every possible controller mutation or to establish the
physical source refinement by itself.

## Verification record

All Lean invocations used the granted shared build slot, one job, the pinned
direct v4.22.0 Lake binary, unique owned runner stages, and 180-second deadlines.
The direct binary avoids the earlier elan shim network attempt. The slot was
released immediately after the final diagnostic completed.

| Stage | Result | Seconds | Interpretation |
|---|---|---:|---|
| select-semantics-1 | FAIL | 9.248 | Missing direct packed ReadProgram import caused namespace cascades; two `.toCosted.value` rewrites required explicit value projection. |
| select-semantics-2 | FAIL | 11.975 | Three dense simplifications unfolded normalize prematurely; entry decoder needed the existing WordRAM/SuccinctSpace bridge; final let-expression needed reduction before rewriting. |
| select-semantics-3 | PASS | 16.728 | Whole source, no local warnings. Existing dependency simp warnings replayed from SuccinctFinalRAM and ReviewerReachabilitySmall. |
| select-semantics-consumer | PASS | 25.943 | Seven typed consumers and eight axiom reports; no timeout or output cap. |

Command records live in `commands/select-semantics-*.json`. The exact source
byte count at the final check is 21230. Source scans for the required trust
keywords/Mathlib and native-decision escapes found no matches across RMQ.
`git diff --check` passed; explicit untracked-file whitespace checks also passed
(only Git newline-conversion notices). No full build or broad gate was run:
the changed leaf and fresh direct consumer are the appropriate bounded checks,
and final source/allocation integration belongs to the coordinator.

The seven substantive public theorem diagnostics report only standard Lean
`propext`, `Classical.choice`, and `Quot.sound`; the anti-vacuity refutation
reports none. Canonical record definitions themselves contain existing proof
fields, so even the raw-array `rfl` statement's diagnostic traverses those
dependencies. No new trusted declaration or external dependency was added.

## Proof digestion

Conceptually, normalized word replies are now proved sufficient for the whole
generic select computation. False-bit chunk operations on those replies return
the requested original target's ranks and select positions, and all directory
branches retain their original counted data. In plain English, the reader may
flip raw bits when selecting true, and the unchanged controller still finds
exactly the requested occurrence in the original input, including reporting
missing occurrences correctly.

The canonical endpoint has no live semantic side assumptions. The generalized
endpoint assumes agreement only on the actual select read segments. Both are
value theorems; neither asserts equality of altered read-event replies or a
source/physical cost bound. A skeptical grad student should next ask whether
the numeric physical reader really returns these same logical words and
whether the source controller really implements this exact scalar expression.
Those are the independent reader/controller composition obligations; the
coordinator's final Allocation must satisfy the agreement predicate on the same
counted physical memory. The leaf is ready for that composition, and whole BV-1
remains incomplete until it is proved.

## Exact fresh-import consumer

```lean
import RMQ.Core.WordRAM.Bitvector.SelectSemantics
open RMQ RMQ.PackedBitvector RMQ.GenericSelect RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedCellProbe
example (bits : List Bool) (target : Bool) :
  (sparseExceptionSelectData bits target).bitWords.store.words =
    (sparseExceptionSelectData bits false).bitWords.store.words :=
  canonical_bitWords_target_eq bits target
example (bits : List Bool) (target : Bool) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  0 < c ∧ d.wordSize ≤ 8 * c ∧ d.longFlagRankData.wordSize ≤ 8 * c ∧
    d.sparseDirectory.rankData.wordSize ≤ 8 * c :=
  canonical_select_chunk_geometry bits target
example (bits : List Bool) (target : Bool) (idx : Nat) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
    21 22 (genericReadStore bits target) c false (occurrenceCount bits target)
    d.superStride d.wordSize d.localSlotsPerSuper d.localStride d.longFlagBits.length
    d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
    d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
    Succinct.select target bits idx := canonicalSelectRead_value bits target idx
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hagree : ∀ segment index, segment < 17 ∨ segment = 21 ∨ segment = 22 →
    store.readWord? segment index = (genericReadStore bits target).readWord? segment index)
  (idx : Nat) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
    21 22 store c false (occurrenceCount bits target)
    d.superStride d.wordSize d.localSlotsPerSuper d.localStride d.longFlagBits.length
    d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
    d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
    Succinct.select target bits idx := selectRead_value_of_agree bits target store hagree idx
example : (canonicalSelectRead [true] true 0).value = some 0 := by
  rw [canonicalSelectRead_value]
  rfl
example : (canonicalSelectRead [true] true 1).value = none := by
  rw [canonicalSelectRead_value]
  rfl
example : ¬ (∀ (bits : List Bool) (target : Bool) (idx : Nat),
  (WordRAM.TraceResult.pure (none : Option Nat)).value = Succinct.select target bits idx) :=
  constant_none_select_rejected
#print axioms canonical_bitWords_target_eq
#print axioms canonical_select_chunk_geometry
#print axioms normalized_dense_value
#print axioms selectRead_value_eq_of_agree
#print axioms selectRead_value_of_agree
#print axioms canonicalSelectRead_value_eq
#print axioms canonicalSelectRead_value
#print axioms constant_none_select_rejected
```

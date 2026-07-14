# Trust Audit Packet
## U2 Canonical Reviewer Trust Boundary

The active final route has no Ready/Active/zero-block dispatch. One exhaustive
typed 20-source universe, including canonical close, covers every reviewer-live
read source and one pre-execution physical list erases exactly to the public
`buildPayload`.
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted`
and `...Costed_exact` connect the charged trace to semantic RMQ exactness.
The existing supplied-store evaluator reads the supplied flat physical store
through a checked address-translation adapter. Agreement on the first
execution's consumed physical footprint determines the complete physical
trace; the refinement preserves order, failures, and repetitions, while a
projection theorem identifies the answer with the translated supplied-store
evaluator value and a decisive singleton corruption changes `some 0` to
`none`. Producer-level theorems connect every emitted read to its actual
instruction occurrence, actual prefix-fold state, exact instruction-local
event, physical source, logical segment, and concrete component path. Every
counted source has a concrete may-read path; shared-BP consumers carry
same-event paths. A fresh unused segment with a plausible canonical-close label
is rejected because no instruction trace can produce it. Raw
adequacy is exposed only for valid public ranges; invalid ranges share the
guarded none/empty/zero packet. No-synthetic,
linear-capacity, logarithmic-width, stored/returned-word, physical-address, and
primitive-operand bounds are checked at the composed consumer. The transitional
all-size cap is exactly `328`; older route constants are compatibility history.


Snapshot: 2026-07-13 (W18 producer-provenance repair candidate). This is the compact packet to hand to a skeptical
Lean/formalization reviewer before asking for a broader library-readiness
review. It focuses on the public succinct RMQ headline theorem, its alias
chain, its cost/space model, and the main anti-oracle checks.

## Quick Reproduction

From the repository root:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
lake env lean scripts\headline_axiom_check.lean
```

The full gate builds the public roots, checks hygiene, runs curated axiom
scripts, runs succinct cost/space lints, runs compatibility-shim lints, and
finishes with `git diff --check`.

For the focused first-order Word-RAM anti-oracle boundary used by the
interpreted RMQ and rank/select capstones, also see
`docs/WORD_RAM_REVIEW_PACKET.md` and run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\review_wordram.ps1
```

## Public Headline Alias

The most reader-facing public RMQ names live in the narrow RMQ paper surface:
`RMQPaper.lean` imports `RMQ/Headlines/RMQ.lean`, while
`RMQ/Headlines.lean` remains the aggregate full-repository barrel.

```lean
theorem listIntSuccinctRMQPaperMainTheorem : ...

abbrev succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
```

The first theorem is stated over ordinary `xs : List Int`: it exposes
`SuccinctClassic.buildPayload xs`, proves its length is at most
`2 * xs.length + overhead xs.length` with `overhead = o(n)`, and proves that
`SuccinctClassic.queryCosted xs` rejects invalid or empty ranges and answers
valid half-open RMQ queries with leftmost ties under one constant modeled query
bound. Exact physical erasure is separate; the payload is not padded to force
size equality.

The execution story keeps those ordinary-list clauses and also consumes the
final no-synthetic WordRAM story for `Cartesian.shape xs`: one physical word
list erases exactly to `SuccinctClassic.buildPayload xs`; the supplied-store
evaluator reads that flat store through checked translation; physical execution
refines the logical trace; first-footprint agreement determines the result; and
one query-independent reviewer width bounds the whole execution.

The construction-facing RMQ name is:

```lean
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
```

Alias chain:

```text
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
  = RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
    -> builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_n_plus_o_constant_query_profile
    -> builtGenericSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    -> concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
         builtGenericSparseExceptionSelectBPCloseAccessFamily
```

The additive interpreted public alias is:

```lean
abbrev succinctRMQTwoNPlusOConstantQueryInterpreted :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
```

It has the same payload, numeric doubled-Catalan slack comparison, cost, and
exactness theorem shape as the main capstone, but the query clause uses
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted`: a
closed first-order whole-query controller whose leaves are interpreted
close-select, compact close/LCA, and register-backed answer-rank operations.

The encoding-quantified fixed-length lower-bound theorem is not hidden in this
capstone clause. It is separately exposed as
`RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`, backed by
`RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`.

The next flattening checkpoint is:

```lean
abbrev succinctRMQTwoNPlusOConstantQueryLeafTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile
```

It keeps the same theorem shape but has the closed controller evaluate to an
explicit domain-leaf trace before projection back to `Costed`.  This is still
not one unified payload-store trace: the trace records interpreted leaf calls
for close-select, compact close/LCA, and answer-rank.

The current strongest all-size flattening checkpoint is:

```lean
abbrev succinctRMQTwoNPlusOConstantQueryWordTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile
```

It keeps the same theorem shape and has the closed controller emit one
`WordRAM.TraceEvent` stream. The close-select leg, answer-rank leg, and the
rank-seed reads inside compact close/LCA contribute structural
payload/register traces. The all-size compact close/LCA leg now also consumes
`SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural`,
which replaces the former zero-block same-block fallback and cross-block
interior fallback leaves with a structural BP-code zero-block same-block scan
and the all-size structural cross-block interior route.

There is also a large-regime companion:

```lean
abbrev succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile
```

Its query clauses include the explicit hypothesis `2^128 <= shape.size`; under
that premise the compact close/LCA leg routes through the positive-block
local/fringe/interior structural trace replay. This large-regime theorem is now
a compatibility companion: the current public all-size route is structural,
with Ready two-level replay, active non-Ready bounded summary scan, and inactive
pure-none interior replay.

The compact interior route itself is now named by:

```lean
RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total
```

The final trace exclusion theorem remains available:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_noFiniteSmallInteriorSuccessfulRead
```

The stronger store-level facts are now:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore_retiredFiniteSmallInterior_none
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadStore_retiredFiniteSmallInterior_none
RMQ.BPNavigation.concreteBPCloseNavigationGlobalReadStore_retiredFiniteSmallInterior_none
```

They prove legacy interior slots 26 and 27 resolve to `none` in the public final
global store, the public final flat-payload read store, and the concrete
close-navigation store. The trace exclusion theorem is now a compatibility
fact rather than the only reason those slots cannot leak uncounted table data.

The strongest all-size execution-story theorem is the global-store companion:

```lean
abbrev succinctRMQGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story

abbrev succinctRMQGlobalPayloadStoreExtensionalExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story

abbrev succinctRMQGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story

abbrev succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story

abbrev succinctRMQFlatPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story
```

It says the public costed query refines the unified `WordRAM.TraceEvent` stream,
every event is either a payload read or an explicitly counted word primitive,
and every payload read agrees with one concrete global store built from the
final succinct RMQ payload components. The all-size structural companion is:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_allSizeStructural_execution_story
```

with public alias:

```lean
RMQ.Headlines.succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory
```

It packages the same store-backed and bounded execution story after replacing
the two known close-navigation `TraceResult.ofCosted` fallback leaves by
payload-backed traces. The no-synthetic companion additionally proves that no
event in the final all-size global trace is
`TraceEvent.syntheticCostOnlyPrimitive`. That marker is now a dedicated
constructor used by `TraceResult.ofCosted`, not an overloaded `wordRank` event.
The bounded companion adds a concrete trace-local finite bit width and proves
that every payload-read address and every natural operand/result exposed by
word-local primitive events fits that width.
The extensional companion says that any read store agreeing with the concrete
global store on the read events emitted by the final trace validates that same
trace.

A zero-block same-block supplied-store surface remains available as a focused
compatibility-only leaf theorem:

```lean
RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreEqGlobalOfFootprint
RMQ.Headlines.succinctRMQCanonicalReviewerMachineWordsComponentSlice
RMQ.Headlines.succinctRMQCanonicalInteriorPhysicalFootprintFits
RMQ.Headlines.succinctRMQCanonicalReviewerValidQueryOperandsFit
```

There the evaluator is run against a supplied `WordRAM.ReadStore`, and stores
that agree on BP-code segment reads produce the same value and trace. The
whole final query now also has a supplied-store replay:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_reads_subset_footprint
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_exact_of_footprint_global
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_refines_wholeQueryInterpretedCosted
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_exact
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness
```

The footprint theorem uses a safe final-layout overapproximation, not an exact
dynamic read-set theorem. The current capstone proves every emitted supplied-store
and canonical payload-read event lies inside that safe footprint, but it does
not claim the footprint is exact or minimal.

The flat-payload no-synthetic companion additionally exposes the
query-independent `concreteBPNativeSuccinctRMQFlatPayloadLayout`, proves
its payload is the advertised `concreteBPNativeSuccinctRMQPayload`, proves
successful flat-store reads have source/component/offset backing evidence, and
uses that flat store in the same bounded no-synthetic execution-story packet.

The large-regime positive-replay companion is:

```lean
abbrev succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story

abbrev succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story
```

It adds the explicit premise `2^128 <= shape.size` and uses the structural
local/fringe/interior close-navigation replay on the compact close/LCA leg. The
all-size flat-payload theorem remains the main public endpoint; it now avoids
successful-read dependence on the legacy interior witness slots by splitting
cross-block interior replay into Ready two-level, active non-Ready bounded
summary scan, and inactive pure-none cases. As before, these are word-RAM model statements;
they are not compiled Lean execution claims and not a general CPU semantics.

The rank/select spoke now has a fused compressed/FID capstone alias:

```lean
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreFusedProfile
```

It packages the compressed fixed-weight family profile, interpreted replay,
target-independent global store, and bounded trace-local event-width story in
one cited theorem. The bounded target-independent global payload-store
component is:

```lean
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story
```

For each fixed `bits`, it packages the compressed/FID access, rank false/true,
and select false/true traces under one target-independent read store and adds a
finite trace-local width proving that every payload-read address and every
natural operand/result exposed by word-local rank/select primitives fits that
width. The lower-level target-indexed theorem remains available for component
audits; the public endpoint is now the fused theorem. The width is still
trace-local rather than a uniform asymptotic machine-word theorem.
The stronger headline alias
`rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile`
keeps that public surface and additionally checks that successful trace reads
are backed by the relabeled component stores and that no synthetic cost-only
events occur in the compressed/FID access/rank/select traces.

## Theorem Statement

The construction-heavy theorem name is intentionally verbose because it exposes
the model and construction path:

```lean
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile :
    let accessFamily :=
      builtGenericSparseExceptionSelectBPCloseAccessFamily
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (accessFamily.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              accessFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    accessFamily shape left (left + len)).erase =
                    some (scanWindow shape.representative left len))
```

Read literally, this says:

- the auxiliary overhead is `o(n)`;
- the upper bound has `2*n + overhead n` payload bits;
- the capstone includes the ordinary and doubled numeric Catalan-slack
  comparison forms;
- the close-access payload is itself bounded by the advertised overhead;
- every query has a fixed modeled cost bound; and
- every valid half-open query over every Cartesian shape of size `n` erases to
  the reference leftmost RMQ answer `scanWindow shape.representative left len`.

For the built generic sparse-exception close-access family, the canonical
reviewer trace has the checked transitional cap `328`. The earlier route-split
`4144` corollary, Ready `118`, active/inactive fallback leaves, zero-block scan,
and `196727` aggregate remain checked compatibility/history only. They are not
the route summarized by this packet's public alias chain.

## Axiom Excerpt

Run:

```powershell
lake env lean scripts\headline_axiom_check.lean
```

Current excerpt for the public headline path:

```text
'RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The gate rejects `sorryAx` and `Lean.ofReduceBool`. It also scans checked
source for `sorry`, `admit`, custom `axiom`, `unsafe`, `opaque`,
`implemented_by`, `partial`, `extern`, `noncomputable`, `native_decide`, and
`import Mathlib`.

## Dependency Sketch

The final query is:

```lean
concreteBPNativeSuccinctRMQQueryCosted accessFamily shape left right
```

Its shape is:

1. Select the close position of the left endpoint using
   `accessFamily.directory shape.selectCloseCosted`.
2. Select the close position of the right endpoint the same way.
3. Run the compact BP close/LCA directory:
   `SuccinctClose.concreteBPNativeCloseDirectory`.
4. Rank the answer close position back to an inorder index using
   `accessFamily.directory shape.rankCloseCosted`.
5. Return the resulting representative-array index.

The abstract composition surface is named `BPCloseAccessDirectory`. The file
explicitly calls it a weak compatibility surface because its costed methods are
fields. The public headline does not stop at an arbitrary inhabitant of that
surface: its concrete access family is

```lean
builtGenericSparseExceptionSelectBPCloseAccessFamily
```

and its directory is defined by:

```lean
payload :=
  (builtRelativeSplitBPCloseRankData shape).auxPayload ++
    (GenericSelect.sparseExceptionSelectSource shape.bpCode false).payload

selectCloseCosted := fun idx =>
  (GenericSelect.sparseExceptionSelectSource
    shape.bpCode false).selectPositionCosted idx

rankCloseCosted := fun pos =>
  (builtRelativeSplitBPCloseRankData shape).rankCosted false pos
```

The exactness and cost facts for those operations come from:

- `GenericSelect.sparseExceptionSelectSource_profile shape.bpCode false`,
  which proves select payload length, `LittleOLinear` overhead, cost bound,
  exact select semantics, and machine-word-bounded read words;
- `builtRelativeSplitBPCloseRankData`, which is a concrete two-level
  payload-live rank structure over `shape.bpCode`;
- `SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?`, which identifies
  false-select in the BP code with the Cartesian inorder close lookup;
- the compact close/LCA profile for
  `SuccinctClose.concreteBPNativeCloseDirectory`; and
- `concreteBPNativeSuccinctRMQQueryCosted_exact`, which composes select-close,
  LCA-close, rank-close, and the RMQ reference semantics.

So the theorem still uses a generic composition interface, but the headline
inhabitant supplies concrete payload and query definitions from rank/select and
close-navigation components rather than leaving correctness hidden in external
callbacks.

## Model Glossary

- `Costed a`: a value of type `a` plus a natural-number model cost. `erase`
  forgets the cost.
- `RAM.Exec`: a shallow primitive-trace model used for small array/word/read
  executions. It records model steps and converts to `Costed`.
- Payload bits: the modeled stored bits counted by space theorems. These are
  separate from proof fields carried by Lean structures.
- Proof-only fields: certificates and invariants used to prove exactness or
  bounds. They are not charged as stored payload bits.
- Unit-cost indexed read: the standard word-RAM modeling assumption that a
  bounded table/word read costs one primitive step. This is not a claim about
  Lean `List` runtime.
- Machine-word bound: theorems such as read-word-length bounds show that the
  queried words fit under the repository's `machineWordBits` function.
- Bounded register/address value: `WordRAM.Register.FitsInBits` and
  `AddressFitsInBits` state that computed natural register values and payload
  addresses fit a declared machine-bit width.
- No-overflow side condition: `WordRAM.Register.NatExpr.NoOverflow` treats
  address arithmetic as mathematical `Nat` arithmetic, then requires proofs
  that the evaluated result still fits the declared width. The current model
  does not silently wrap on overflow.
- Zero-cost control: register lookup, arithmetic expression evaluation, and
  branching choose later events but do not themselves appear in the trace.
  The event classifiers prove every trace event is a payload read or a
  word-local primitive; zero-cost control is not an information-bearing event.

## Non-Claims

This packet does not claim:

- the algorithmic result is new data-structure theory;
- Lean's native execution of lists or structures has the modeled runtime;
- the final theorem is a production-ready serialized packed implementation;
- all BP tree-navigation operations are already available;
- the compressed/FID rank/select replay is a single closed machine-code
  program rather than a bridge-backed word-RAM model theorem; or
- the current first-order WordRAM layer is a complete CPU semantics with
  built-in bounded machine integers and wraparound behavior; boundedness and
  no-overflow are explicit theorem hypotheses/proofs; or
- the repo is CSLib-ready as-is.

The claim is narrower and stronger in the formalization sense: the repo gives
a machine-checked Lean stack connecting exact RMQ semantics, Cartesian-shape
counting lower bounds, payload-accounted BP/rank/select upper-bound machinery,
and a constant-query word-RAM-style succinct RMQ profile.

## Minimal Imports

Headline aliases:

```lean
import RMQ.Headlines

#check RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
#check RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
```

Standalone spokes:

```lean
import RMQRankSelect
import RMQBPNavigation
import RMQUnionFind
```

Checked downstream examples:

```powershell
lake build RMQExamples
```

Focused spoke checks:

```powershell
lake build RMQRankSelect
lake env lean scripts\rank_select_axiom_check.lean

lake build RMQBPNavigation
lake env lean scripts\bp_navigation_axiom_check.lean

lake build RMQUnionFind
lake env lean scripts\union_find_axiom_check.lean
```

## Reviewer Reading Order

1. `RMQPaper.lean`
2. `RMQ/Headlines/RMQ.lean`
3. `docs/WHAT_IS_PROVED.md`
4. `docs/TRUST_BASE.md`
5. this packet
6. `scripts/headline_axiom_check.lean`
7. `RMQ/Core/SuccinctFinal.lean`, starting at
   `builtGenericSparseExceptionSelectBPCloseAccessDirectory` and
   `builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`

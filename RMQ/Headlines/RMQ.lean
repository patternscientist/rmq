import RMQ.Core.EncodingLowerBound
import RMQ.Core.SuccinctFinalModelAdequacy
import RMQ.Core.SuccinctRMQClassic

/-!
RMQ-only public headline aliases for the paper artifact.

This module is the narrow theorem-import surface for the RMQ paper claims. It
exposes the list-facing theorem, BP-native succinct upper-bound surfaces,
lower-bound surface, final WordRAM/model-adequacy packets, concrete cost
equalities, supplied-store/footprint theorems, and large-regime compatibility
rows without importing standalone rank/select, standalone BP-navigation, or
union-find public headline spokes.
-/

namespace RMQ.Headlines

/-- Tight fixed-length RMQ lower bound with the doubled Catalan slack form. -/
abbrev exactRMQLowerBoundDoubledCatalanSlack :=
  RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack

/--
BP-native succinct RMQ capstone: exact RMQ, `2*n + o(n)`, constant query, and
a numeric doubled-Catalan lower-bound comparison in the same theorem surface.
The encoding-quantified lower-bound theorem is exposed separately as
`exactRMQLowerBoundDoubledCatalanSlack`.
-/
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

/--
Classic list-facing succinct RMQ theorem: for every ordinary `xs : List Int`,
the built payload has length `2*n + o(n)` and valid half-open queries return
the exact leftmost RMQ answer within constant modeled query cost.
-/
abbrev succinctRMQListIntTwoNPlusOConstantQuery :=
  RMQ.SuccinctClassic.listInt_two_n_plus_o_constant_query_profile

/--
List-facing flat-payload no-synthetic execution story: for every ordinary
`xs : List Int`, the same final query keeps the classic half-open/leftmost
RMQ contract and constant modeled query story while its global WordRAM trace is
backed by one query-independent counted flat payload layout/read store: every
actual successful read has source/component/offset evidence, event data are
bounded, and no synthetic cost-only events occur. The flat execution payload is
the advertised `2*n + o(n)` `buildPayload`, with no finite-small same-block
appendix; retired finite-small interior slots have empty stores.
-/
abbrev listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story

/--
List-facing paper main theorem. For every ordinary `xs : List Int`, the
advertised `buildPayload` has length at most `2*n + overhead n` with
`overhead = o(n)`, valid half-open queries return exact leftmost RMQ answers
within the modeled constant query budget, and the final trace is the
no-synthetic flat-payload execution story.
-/
theorem listIntSuccinctRMQPaperMainTheorem :
    RMQ.SuccinctSpace.LittleOLinear RMQ.SuccinctClassic.overhead /\
      forall xs : List Int,
        (RMQ.SuccinctClassic.buildPayload xs).length <=
          2 * xs.length + RMQ.SuccinctClassic.overhead xs.length /\
        (forall left right,
          (RMQ.SuccinctClassic.queryCosted xs left right).cost <=
            RMQ.SuccinctClassic.queryCost) /\
        (forall {left len : Nat},
          0 < len ->
            left + len <= xs.length ->
              (RMQ.SuccinctClassic.queryCosted xs left (left + len)).erase =
                some (RMQ.scanWindow xs left len)) /\
        (forall {left len idx : Nat},
          0 < len ->
            left + len <= xs.length ->
              (RMQ.SuccinctClassic.queryCosted xs left (left + len)).erase =
                some idx ->
                RMQ.LeftmostArgMin xs left (left + len) idx) /\
        (forall left right,
          RMQ.SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory
            xs left right) /\
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          RMQ.SuccinctClassic.storesAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            RMQ.SuccinctClassic.queryTraceResultWithStore
                xs storeA left right =
              RMQ.SuccinctClassic.queryTraceResultWithStore
                xs storeB left right) := by
  rcases
    RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story with
    ⟨hoverhead, hxs⟩
  refine ⟨hoverhead, ?_⟩
  intro xs
  rcases hxs xs with ⟨hpayload, hcost, hexact, hleftmost, hstory⟩
  exact
    ⟨hpayload, hcost, hexact, hleftmost, hstory,
      fun storeA storeB left right hagree =>
        RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint
          xs storeA storeB left right hagree⟩

/-- Exact dynamic-footprint supplied-store determinism. Equality is of the
complete trace result, hence preserves decoded result, cost, ordered trace,
repeated reads, and failures. -/
abbrev listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint :=
  RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint

/-- One physical word list erases exactly to the canonical public payload. -/
abbrev succinctRMQReviewerPhysicalWordsErasePublicPayload :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases

/-- The physical-address footprint is literally the read projection consumed
by the translated whole-query execution. -/
abbrev succinctRMQReviewerPhysicalFootprintRecorded :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint_recorded

/-- Full segmented-to-flat refinement preserving value, cost, ordered trace,
and successful or failed read results. -/
abbrev succinctRMQReviewerPhysicalExecutionRefinesLogical :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical

/-- The exact physical word list has concrete linear capacity. -/
abbrev succinctRMQReviewerPhysicalWordsFitLinearCapacity :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity

/-- The one reviewer width is explicitly logarithmic in input size. -/
abbrev succinctRMQReviewerWordBitsLogarithmic :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits_le_log

/-- Every stored physical machine word fits the one reviewer width. -/
abbrev succinctRMQReviewerPhysicalWordFits :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWord_length_le_wordBits

/-- Every successful logical read returns a word fitting that same width. -/
abbrev succinctRMQReviewerSuccessfulReadWordFits :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSuccessfulRead_word_length_le_wordBits

/-- Every address recorded in the consumed physical footprint fits that width. -/
abbrev succinctRMQReviewerPhysicalFootprintAddressFits :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint_address_fits_reviewerWordBits

/--
List-facing supplied-store equality: if the caller-provided store agrees with
the canonical global store on the final checked footprint, the supplied-store
query is the same costed query as the canonical list-facing path.
-/
theorem listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint
    (xs : List Int) {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs store
        (RMQ.SuccinctClassic.globalReadStore xs))
    (left right : Nat) :
    RMQ.SuccinctClassic.queryCostedWithStore xs store left right =
      RMQ.SuccinctClassic.queryCosted xs left right :=
  RMQ.SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint
    xs hfoot left right

/--
List-facing supplied-store exactness: if the caller-provided store agrees with
the canonical global store on the final checked footprint, valid half-open
queries erase to the same leftmost `List Int` RMQ answer as the canonical path.
-/
theorem listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
    (xs : List Int) {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs store
        (RMQ.SuccinctClassic.globalReadStore xs))
    {left len : Nat} (hlen : 0 < len)
    (hbound : left + len <= xs.length) :
    (RMQ.SuccinctClassic.queryCostedWithStore
      xs store left (left + len)).erase =
        some (RMQ.scanWindow xs left len) :=
  RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal
    xs hfoot hlen hbound

/--
List-facing supplied-store all-size cost transfer under final footprint
agreement with the canonical global store.
-/
theorem listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs store
        (RMQ.SuccinctClassic.globalReadStore xs))
    (left right : Nat) :
    (RMQ.SuccinctClassic.queryCostedWithStore
      xs store left right).cost <=
        RMQ.SuccinctClassic.queryCost :=
  RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal
    xs hfoot left right

/-- List-facing supplied-store canonical transitional U2 cost transfer. -/
theorem listIntSuccinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs store
        (RMQ.SuccinctClassic.globalReadStore xs))
    (left right : Nat) :
    (RMQ.SuccinctClassic.queryCostedWithStore
      xs store left right).cost <=
        RMQ.SuccinctClassic.canonicalTransitionalQueryCost :=
  RMQ.SuccinctClassic.listIntCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
    xs hfoot left right

/--
Whole-query-interpreted BP-native succinct RMQ capstone: the same two-sided
`2*n + o(n)`, constant-query theorem shape, with the final query control routed
through a closed first-order query program whose leaves are the interpreted
close-select, compact close/LCA, and answer-rank operations.
-/
abbrev succinctRMQTwoNPlusOConstantQueryInterpreted :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile

/--
Leaf-trace-preserving BP-native succinct RMQ capstone: the same theorem shape
as the whole-query-interpreted headline, with the closed controller evaluating
to an explicit domain-leaf trace before projection back to `Costed`.
-/
abbrev succinctRMQTwoNPlusOConstantQueryLeafTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile

/--
Unified-`WordRAM.TraceEvent` BP-native succinct RMQ capstone. The final query
control now emits one `TraceEvent` stream. Select-close, answer-rank, and
compact-close rank-seed reads are structural payload/register traces; the
all-size global execution story below uses raw positive block size for
same-block decoding and the canonical component store for every cross-block
interior query; there is no zero-block dispatch in this path.
-/
abbrev succinctRMQTwoNPlusOConstantQueryWordTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile

/--
Large-regime unified-`WordRAM.TraceEvent` BP-native succinct RMQ capstone. This
has the same two-sided `2*n + o(n)`, constant-query theorem shape, but the query
clauses retain an explicit size hypothesis for compatibility. The public
all-size reviewer route is the same unconditional canonical directory route
used at every size.
-/
abbrev succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile

/--
Large-regime globally segmented `WordRAM.TraceEvent` BP-native succinct RMQ
capstone. This strengthens the large-regime word-trace headline by relabeling
the final query's select, rank, and compact close/LCA payload reads into one
shared segment convention. The matching execution-story theorem below proves
those events agree with one concrete payload store.
-/
abbrev succinctRMQTwoNPlusOConstantQueryGlobalWordTraceLargeRegime :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_global_word_trace_large_regime_profile

/--
Public execution-story theorem for the final all-size succinct RMQ query: the
query is the `Costed` projection of one globally segmented `WordRAM` trace,
refines the whole-query interpreter, every event is a payload read or bounded
word primitive, and every payload read agrees with the single concrete global
read store. The final all-size global trace consumes the structural compact
close/LCA path, so the former close-navigation `TraceResult.ofCosted` fallback
leaves are no longer on this path.
-/
abbrev succinctRMQGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story

/--
Store-extensional execution-story theorem for the final all-size succinct RMQ
query. Any read store that agrees with the concrete global store on the
payload-read events emitted by the query validates the same trace.
-/
abbrev succinctRMQGlobalPayloadStoreExtensionalExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story

/--
Whole-query supplied-store replay: every read event emitted by the final RMQ
query reports the word observed from the caller-provided `WordRAM.ReadStore`.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreMatchesReadStore :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore

/--
Concrete-store evaluation theorem for the whole-query supplied-store replay:
instantiating the replay with the final global read store gives the canonical
globally segmented whole-query trace.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreEval :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore

/--
Whole-query store-parametricity over the explicit final segment layout.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreStoreParametric :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric

/--
Whole-query store-parametricity from agreement on the final layout footprint.
The footprint is a safe layout overapproximation covering live final segments
and the dead sentinel used by finite segment maps.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreStoreParametricOfFootprint :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint

/--
Every supplied-store whole-query payload-read event is inside the safe final
layout footprint. The footprint is a layout overapproximation, not a minimal
dynamic read set.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreReadsSubsetFootprint :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint

/--
Every canonical whole-query payload-read event is inside the safe final layout
footprint.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultReadsSubsetFootprint :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_reads_subset_footprint

/--
A supplied-store whole-query replay equals the canonical global trace when the
supplied store agrees with the concrete global store on the safe final layout
footprint.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreEqGlobalOfFootprint :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint

/-- Supplied-store successful reads are backed by the canonical reviewer payload. -/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global

/--
Compatibility alias for the old conservative aggregate all-size cost theorem.
It remains true, but it sums mutually exclusive fallback costs and is no longer
the paper-facing cost alias.
-/
abbrev succinctRMQLegacy196727WholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le

/-- The uniform canonical reviewer trace has the checked transitional U2 bound. -/
abbrev succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional

/-- The checked canonical transitional U2 bound computes to `328`. -/
abbrev succinctRMQCanonicalTransitionalQueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq

/--
The canonical final global trace has modeled cost bounded by the clean fixed
all-size final-query constant, the maximum of the checked route-split leaves.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize

/--
Under agreement with the concrete global store on the safe final layout
footprint, the canonical modeled cost bound transfers to the supplied-store
whole-query replay.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global

/--
Legacy all-size modeled query-cost constant for the final BP-native succinct
RMQ query. This is the old conservative aggregate kept for compatibility.
-/
abbrev succinctRMQLegacy196727QueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost
    RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost

/-- The legacy all-size final-query cost constant computes to `196727`. -/
abbrev succinctRMQLegacy196727QueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost_eq

/--
Clean fixed all-size modeled query-cost constant for the final BP-native
succinct RMQ query.
-/
abbrev succinctRMQQueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost

/-- The clean fixed all-size final-query cost constant computes to `4144`. -/
abbrev succinctRMQQueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq

theorem succinctRMQWholeQueryGlobalWordTraceCostedWithStoreExactOfFootprintGlobal
    {n : Nat} {shape : RMQ.Cartesian.CartesianShape}
    (hshape : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
            shape))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left (left + len)).erase =
        some (RMQ.scanWindow shape.representative left len) :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_exact_of_footprint_global
    hshape hfoot hlen hbound

/--
Whole-query supplied-store replay contains no dedicated synthetic cost-only
marker events.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultWithStoreNoSynthetic :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive

/--
Reviewer-facing model-adequacy packet for the final succinct RMQ query trace:
the costed query is the projection of a `WordRAM.TraceResult`, refines the
whole-query interpreter, has the fixed modeled query-cost bound, reads only
through payload-read or word-primitive events, matches the global read store,
has bounded event data, has no synthetic cost-only events, and backs every
successful read by counted flat payload words.
-/
abbrev succinctRMQFinalTraceModelAdequacy :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy

/-- Exactness alias paired with `succinctRMQFinalTraceModelAdequacy`. -/
theorem succinctRMQFinalTraceModelAdequacyExact
    {n : Nat} {shape : RMQ.Cartesian.CartesianShape}
    (hshape : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left (left + len)).erase =
        some (RMQ.scanWindow shape.representative left len) :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact
    hshape hlen hbound

/--
Reviewer-facing supplied-store adequacy packet for the final whole-query replay:
reads match the caller-provided store, the concrete global store instantiation
recovers the canonical final trace and interpreted query, no synthetic marker
events appear, and footprint agreement gives store-parametricity.
-/
abbrev succinctRMQFinalSuppliedStoreAdequacy :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy

/--
Full model-soundness packet for the final succinct RMQ query inside the
explicit WordRAM/read-store/counted-payload model.
-/
abbrev succinctRMQFinalFullModelSoundness :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness

theorem succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
    {n : Nat} {shape : RMQ.Cartesian.CartesianShape}
    (hshape : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
            shape))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left (left + len)).erase =
        some (RMQ.scanWindow shape.representative left len) :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global
    hshape hfoot hlen hbound

/-- Full-model canonical transitional U2 cost theorem under footprint agreement. -/
theorem succinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
    {shape : RMQ.Cartesian.CartesianShape}
    {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
            shape))
    (left right : Nat) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        3 * RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost +
          RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_canonicalTransitional
    hfoot left right

/--
Bounded execution-story theorem for the final all-size succinct RMQ query. This
extends `succinctRMQGlobalPayloadStoreExecutionStory` with a concrete finite
trace-local compatibility width. The reviewer-native pre-execution word model
is exposed by the canonical reviewer aliases below.
-/
abbrev succinctRMQGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story

/--
All-size structural execution-story theorem for the final all-size succinct
RMQ query. Same-block decoding and canonical cross-block component replay are
the only close/LCA branches consumed by this reviewer path.
-/
abbrev succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_allSizeStructural_execution_story

/--
No-synthetic all-size execution-story theorem for the final succinct RMQ query.
This strengthens the structural story by proving that the globally segmented
trace contains no dedicated `TraceEvent.syntheticCostOnlyPrimitive` events.
-/
abbrev succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story

/--
Flat-payload no-synthetic execution story for the final succinct RMQ query.
This citation packages the final adequacy record: the final query reads from one
query-independent canonical reviewer payload/store, every successful read is
counted, one physical word list erases exactly to the public payload, and no
event is synthetic. Cross-block replay is uniformly the canonical directory
execution for all sizes.
-/
abbrev succinctRMQFlatPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story

/-- Exact canonical-component slice in the physical reviewer machine words. -/
abbrev succinctRMQCanonicalReviewerMachineWordsComponentSlice :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerMachineWords_component_slice

/-- Every consumed canonical interior physical address fits the total word width. -/
abbrev succinctRMQCanonicalInteriorPhysicalFootprintFits :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalInteriorPhysicalFootprint_fits

/-- Valid final-query operands fit the same pre-execution reviewer word width. -/
abbrev succinctRMQCanonicalReviewerValidQueryOperandsFit :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerValidQueryOperands_fit

/-- All-size canonical interior profile, including store and footprint guarantees. -/
abbrev succinctRMQCanonicalInteriorDirectoryProfileAllSize :=
  RMQ.SuccinctClose.canonicalRelativeRmmInteriorDirectory_profile_allSize

/--
Large-regime companion to `succinctRMQGlobalPayloadStoreExecutionStory`; this
uses the positive-block local/fringe/interior close-navigation replay under the
explicit `2^128 <= shape.size` compatibility premise. It is no longer the
theorem used to justify the old numeric compatibility story in the all-size
payload story.
-/
abbrev succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story

/--
Large-regime bounded companion to
`succinctRMQGlobalPayloadStoreBoundedExecutionStory`.
-/
abbrev succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story

end RMQ.Headlines

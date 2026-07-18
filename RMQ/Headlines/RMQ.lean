import RMQ.Core.EncodingLowerBound
import RMQ.Core.SuccinctFinalModelAdequacy
import RMQ.Core.SuccinctRMQClassicProvenance

/-!
RMQ-only public headline aliases for the paper artifact.

This module is the narrow theorem-import surface for the RMQ paper claims. It
exposes one canonical physical-payload/global-trace upper-bound topology, the
list-facing main theorem, the lower-bound surface, final WordRAM/model-adequacy
packets, concrete current cost equalities, and supplied-store/footprint
theorems. Historical query profiles live in `RMQ.Headlines.RMQCompatibility`,
which is deliberately outside the `RMQPaper` import closure.
-/

namespace RMQ.Headlines

/-- Tight fixed-length RMQ lower bound with the doubled Catalan slack form. -/
abbrev exactRMQLowerBoundDoubledCatalanSlack :=
  RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack

/--
Canonical construction-facing capstone. Its checked type combines the
canonical reviewer payload bound and physical erasure with the exact canonical
global execution, direct positional backing in the physical reviewer words for
every successful payload read, both non-synthetic-weight equalities (to trace
length and `Costed.cost`), the literal uniform bound `76`, exact RMQ answers,
and the doubled-Catalan space envelopes.
-/
abbrev succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile

/--
Canonical list-facing succinct RMQ theorem: for every ordinary `xs : List Int`,
the public `buildPayload` has length at most `2*n + overhead n` for an `o(n)`
overhead, and the same physical-payload/global-trace execution answers valid
half-open queries exactly within the canonical modeled query bound.
-/
abbrev succinctRMQListIntTwoNPlusOConstantQuery :=
  RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story

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

/-- Valid List-Int queries inherit indexed occurrence/invocation provenance. -/
abbrev listIntSuccinctRMQOccurrenceProvenanceOfValid :=
  RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_occurrenceProvenance_of_valid

/--
List-facing paper main theorem. For every ordinary `xs : List Int`, the
advertised `buildPayload` has length at most `2*n + overhead n` with
`overhead = o(n)`, valid half-open queries return exact leftmost RMQ answers
within the modeled constant query budget, and the final trace is the
no-synthetic flat-payload execution story. The reviewer-manifest semantic
packet is one query-independent conjunct; raw trace adequacy and indexed
occurrence provenance remain under each current query's validity premise.
-/
theorem listIntSuccinctRMQPaperMainTheorem :
    RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy /\
    RMQ.SuccinctClassic.queryCost = 142 /\
    RMQ.SuccinctSpace.LittleOLinear RMQ.SuccinctClassic.overhead /\
      forall xs : List Int,
        (RMQ.SuccinctClassic.buildPayload xs).length <=
          2 * xs.length + RMQ.SuccinctClassic.overhead xs.length /\
        RMQ.SuccinctSpace.flattenPayloadWords
            (RMQ.SuccinctClassic.reviewerPhysicalWords xs) =
          RMQ.SuccinctClassic.buildPayload xs /\
        (forall left right,
          (RMQ.SuccinctClassic.queryCosted xs left right).cost <=
            RMQ.SuccinctClassic.queryCost) /\
        (forall left right,
          Not (RMQ.ValidRange xs left right) ->
            (RMQ.SuccinctClassic.queryCosted xs left right).erase = none) /\
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
        (forall left right,
          RMQ.ValidRange xs left right ->
            RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
              (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
        (forall left right,
          RMQ.ValidRange xs left right ->
            RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance
              (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
        (forall left right,
          Not (RMQ.ValidRange xs left right) ->
            RMQ.SuccinctClassic.queryTraceResult xs left right =
                RMQ.WordRAM.TraceResult.pure none /\
            RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right =
                RMQ.WordRAM.TraceResult.pure none /\
            RMQ.SuccinctClassic.queryCosted xs left right =
                RMQ.Costed.pure none /\
            RMQ.SuccinctClassic.reviewerPhysicalFootprint xs left right = [] /\
            forall store : RMQ.WordRAM.ReadStore,
              RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                  xs store left right =
                RMQ.WordRAM.TraceResult.pure none) /\
        (forall (store : RMQ.WordRAM.ReadStore) left right,
          RMQ.ValidRange xs left right ->
            (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
              xs store left right).value =
            (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
              (RMQ.SuccinctClassic.cartesianShape xs)
              (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
                (RMQ.SuccinctClassic.cartesianShape xs) store)
              left right).value) /\
        (forall left right,
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
              xs left right).value =
              (RMQ.SuccinctClassic.queryTraceResult xs left right).value /\
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
              xs left right).trace =
              (RMQ.SuccinctClassic.queryTraceResult xs left right).trace.map
                (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent
                  (RMQ.SuccinctClassic.cartesianShape xs)) /\
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
              xs left right).toCosted =
              RMQ.SuccinctClassic.queryCosted xs left right) /\
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right =
              RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right) /\
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
  refine
    ⟨RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy,
      RMQ.SuccinctClassic.queryCost_eq, hoverhead, ?_⟩
  intro xs
  rcases hxs xs with
    ⟨hpayload, hcost, hinvalid, hexact, hleftmost, hstory⟩
  exact
    ⟨hpayload,
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
        (RMQ.SuccinctClassic.cartesianShape xs),
      hcost, hinvalid, hexact, hleftmost, hstory,
      fun left right hvalid =>
        RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid
          xs left right hvalid,
      fun left right hvalid =>
        RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_occurrenceProvenance_of_valid
          xs left right hvalid,
      RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
        xs,
      fun store left right hvalid =>
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator_of_valid
          xs store left right hvalid,
      RMQ.SuccinctClassic.reviewerPhysicalTraceResult_refines_queryTraceResult
        xs,
      fun storeA storeB left right hagree =>
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
          xs storeA storeB left right hagree,
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
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded

/-- Full segmented-to-flat refinement preserving value, cost, ordered trace,
and successful or failed read results. -/
abbrev succinctRMQReviewerPhysicalExecutionRefinesLogical :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical

/-- The supplied flat store is translated before the existing whole-query
evaluator performs each read. -/
abbrev succinctRMQReviewerPhysicalStoreAdapter :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter

/-- Agreement on the first physical execution's consumed footprint determines
the complete physical execution. -/
abbrev succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint

/-- The answer projection is exactly the translated supplied-store evaluator's
answer projection. -/
abbrev succinctRMQReviewerPhysicalValueFromSuppliedStore :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator

/-- If translated supplied-store evaluator answers differ, the corresponding
physical answer projections differ. -/
abbrev succinctRMQReviewerPhysicalValueDependency :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne

/-- List-facing physical refinement, including invalid-range rejection. -/
abbrev listIntSuccinctRMQReviewerPhysicalExecutionRefinesLogical :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResult_refines_queryTraceResult

/-- List-facing consumed-footprint determinism for supplied flat stores. -/
abbrev listIntSuccinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint

/-- The exhaustive live canonical source universe, including canonical close. -/
abbrev succinctRMQReviewerPhysicalSources :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources

/-- Canonical live physical sources are duplicate-free. -/
abbrev succinctRMQReviewerPhysicalSourcesNodup :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup

/-- Named source regions are exclusive. -/
abbrev succinctRMQReviewerSourceRegionInjective :=
  @RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSource_region_injective

/-- Logical segments are covered exactly through segment 20. -/
abbrev succinctRMQReviewerSegmentSourceCoverage :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage

/-- Every emitted logical read, including failures, maps to a listed live
source/region and its checked physical event. -/
abbrev succinctRMQReviewerEveryReadHasListedRegion :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_has_listed_region

/-- Every indexed emitted read retains its exact instruction/local occurrence,
prefix state, invocation parameters, source, and component occurrence. -/
abbrev succinctRMQReviewerEveryReadOccurrenceProvenance :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked

/-- Every counted source has a successful indexed occurrence in an actual
closed whole-query execution under a valid ordinary List query. -/
abbrev succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence

/-- Every named shared-BP consumer has a successful indexed occurrence through
its exact invocation leaf in a closed valid whole-query execution. -/
abbrev succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence

/-- A fresh unused segment with a plausible canonical-close label has no
operational producer witness. -/
abbrev succinctRMQReviewerFreshUnusedSourceNoProducer :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer

/-- Generic indexed fold decomposition to exact instruction/local positions. -/
abbrev succinctRMQProgramOccurrenceActualProducer :=
  RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace_getElem?_producer

/-- Successful common producer claims imply the mutation-side any-result
predicate by a checked bridge. -/
abbrev succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer
    {claim : RMQ.SuccinctFinal.ReviewerProducerClaim}
    (hclaim : claim.HasSuccessfulClosedValidOccurrence) :
    claim.HasOperationalProducer :=
  RMQ.SuccinctFinal.ReviewerProducerClaim.hasOperationalProducer_of_successful hclaim

/-- Equal event values at distinct global indices yield distinct indexed
provenance receipts. -/
abbrev succinctRMQReviewerRepeatedEqualOccurrencesRemainDistinct :=
  RMQ.SuccinctFinal.repeated_equal_read_occurrences_have_distinct_receipts

/-- No legacy duplicate close source occurs in the canonical source list. -/
abbrev succinctRMQReviewerPhysicalSourcesExcludeLegacyClose :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources_exclude_legacy_close

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
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_address_fits_reviewerWordBits

/-- Public invalid-range rejection for the list-facing canonical query. -/
abbrev listIntSuccinctRMQQueryCostedInvalid :=
  RMQ.SuccinctClassic.queryCosted_invalid

/-- Empty, reversed, and out-of-bounds specializations of the invalid contract. -/
abbrev listIntSuccinctRMQQueryCostedEmptyRange :=
  RMQ.SuccinctClassic.queryCosted_empty_range
abbrev listIntSuccinctRMQQueryCostedReversedRange :=
  RMQ.SuccinctClassic.queryCosted_reversed_range
abbrev listIntSuccinctRMQQueryCostedOutOfBounds :=
  RMQ.SuccinctClassic.queryCosted_out_of_bounds

/-- The guarded story exposes raw model adequacy only on valid ranges. -/
abbrev listIntSuccinctRMQRawAdequacyOfValid :=
  RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid

/-- All invalid public inputs share the same none/empty/zero physical and
logical execution packet. -/
abbrev listIntSuccinctRMQInvalidPhysicalSemantics :=
  RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics

/-- Valid list-facing physical answers come from the translated supplied-store
evaluator at the `.value` projection. -/
abbrev listIntSuccinctRMQPhysicalValueFromSuppliedStore :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator_of_valid

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

/-- The canonical final global trace has the principled uniform charged-trace bound. -/
abbrev succinctRMQWholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace

/-- The modeled cost is exactly the emitted charged-event count. -/
abbrev succinctRMQWholeQueryGlobalWordTraceCostedCostEqTraceLength :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_eq_trace_length

/-- Every event in the accepted trace is an actual read, word-rank, or word-select. -/
abbrev succinctRMQWholeQueryGlobalWordTraceResultEventReadWordOrWordRankOrWordSelect :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect

/-- The synthetic fallback marker is absent from the accepted trace. -/
abbrev succinctRMQWholeQueryGlobalWordTraceResultSyntheticCostOnlyPrimitiveNotMem :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_syntheticCostOnlyPrimitive_not_mem

/-- Non-synthetic certificate weights sum exactly to the accepted trace length. -/
abbrev succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqTraceLength :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_trace_length

/--
For the accepted no-synthetic trace, non-synthetic certificate weights sum
exactly to the `Costed.cost` of the same execution.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost

/-- The non-synthetic-weighted actual trace has the checked all-size bound `142`. -/
abbrev succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe142 :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_142

/-- A synthetic marker cannot be classified as a genuine read/rank/select event. -/
abbrev succinctRMQSyntheticCostOnlyPrimitiveNotReadWordOrWordRankOrWordSelect :=
  RMQ.WordRAM.TraceEvent.syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect

/-- Any synthetic occurrence breaks non-synthetic-weight/trace-length equality. -/
abbrev succinctRMQSyntheticCostOnlyPrimitiveMemBreaksNonSyntheticWeightLengthEquality :=
  RMQ.WordRAM.TraceEvent.sum_nonSyntheticWeight_ne_length_of_synthetic_mem

/--
Under agreement with the concrete global store on the safe final layout
footprint, the canonical modeled cost bound transfers to the supplied-store
whole-query replay.
-/
abbrev succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_principledAllSizeChargedTrace

/-- Uniform canonical modeled query-cost constant for the final reviewer path. -/
abbrev succinctRMQQueryCost := RMQ.SuccinctClassic.queryCost

/-- The uniform canonical final-query charged-trace cost computes to `142`. -/
abbrev succinctRMQQueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq

/-- Operation-aligned component cap algebra for the current charged trace. -/
abbrev succinctRMQChargedTraceCostAlgebra :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra

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

/-- Query-independent reviewer-manifest semantic-adequacy packet: every counted
source and shared-BP consumer has some successful closed-valid indexed
occurrence, the positive predicate bridges to the common mutation predicate,
and the fresh source is rejected by that same predicate. -/
abbrev succinctRMQReviewerManifestSemanticAdequacy :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy

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

/-- Canonical full-model charged-trace cost theorem under footprint agreement. -/
theorem succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal
    {shape : RMQ.Cartesian.CartesianShape}
    {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace
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

end RMQ.Headlines

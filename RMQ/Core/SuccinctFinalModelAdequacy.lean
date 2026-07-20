import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.SuccinctFinalStoreParam

/-!
# Model-adequacy bundle for the final succinct RMQ trace

This module packages existing final-query theorem surfaces into compact
reviewer-facing records. It does not introduce a new algorithm, cost model, or
execution path.
-/

namespace RMQ

namespace SuccinctFinal

/--
Reviewer-facing adequacy packet for the final BP-native succinct RMQ query
trace.  The fields collect the existing theorem surfaces that explain what the
modeled constant-query claim means: the `Costed` result is exactly the
projection of a `WordRAM.TraceResult`, the trace refines the interpreted
whole-query program, every emitted event is an actual read/rank/select event,
the `TraceEvent.nonSyntheticWeight` certificate sum equals both trace length
and `Costed.cost` for this canonical no-synthetic trace, successful reads are
backed by counted flat payload words, event data are bounded, and no event is
the synthetic cost-only marker.
-/
structure ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop where
  toCosted_eq :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted
  refines_canonical_interpreted :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
  cost_le :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost
  event_readWord_or_wordRank_or_wordSelect :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        (Exists fun segment : Nat => Exists fun index : Nat =>
          Exists fun word? : Option WordRAM.Word =>
            event = WordRAM.TraceEvent.readWord segment index word?) \/
        (Exists fun target : Bool => Exists fun limit : Nat =>
          Exists fun result : Nat =>
            event = WordRAM.TraceEvent.wordRank target limit result) \/
        (Exists fun target : Bool => Exists fun occurrence : Nat =>
          Exists fun result : Option Nat =>
            event = WordRAM.TraceEvent.wordSelect target occurrence result)
  nonSyntheticWeight_sum_eq_trace_length :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.length
  nonSyntheticWeight_sum_eq_cost :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right).cost
  nonSyntheticWeight_sum_le_210 :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <= 210
  matches_global_read_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
  event_bounds :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event /\
          concreteBPNativeTraceEventPrimitiveOperandsFitInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event
  no_synthetic :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  successful_reads_backed_by_canonical_reviewer_payload :
    forall {segment index : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word
  compatibility_counted_sources_have_component_may_path :
    forall source : ReviewerSource, source.Counted ->
      source.HasProducerMayPath shape
  compatibility_shared_bp_dependencies_have_component_path :
    forall consumer : ReviewerSharedBPConsumer,
      consumer.ProducerConnected shape
  canonical_manifest_nodup :
    List.Nodup concreteBPNativeSuccinctRMQReviewerPhysicalSources
  canonical_regions_exclusive :
    forall {source other : ReviewerSource},
      source.region = other.region -> source = other
  canonical_segments_complete :
    forall segment : Nat,
      (Exists fun source =>
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
          some source) <-> segment < 23
  every_emitted_read_has_listed_region :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        Exists fun source : ReviewerSource =>
          Exists fun region : Nat =>
            source.Counted /\
            concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
              some source /\
            source.region = region /\
            WordRAM.TraceEvent.readWord 0
                (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
                  shape segment index) word? ∈
              (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
                shape left right).trace
  every_emitted_read_has_occurrence_provenance :
    ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance shape left right
  every_emitted_read_has_eventValue_producer_provenance :
    ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance shape left right
  canonical_manifest_excludes_legacy_close :
    forall (source : ReviewerSource),
      source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources ->
      forall legacy : ConcreteBPNativeSuccinctRMQFlatPayloadSource,
        source.legacyOuterSource? = some legacy ->
          Not legacy.LegacyCloseOrInterior
  compatibility_tail_unreachable :
    forall segment index, 23 <= segment ->
      (concreteBPNativeSuccinctRMQCanonicalReviewerReadStore shape).readWord?
          segment index = none
  physical_words_erase_public_payload :
    SuccinctSpace.flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape
  physical_execution_refines_logical :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
          (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).toCosted =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted /\
    (forall segment index word?,
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        WordRAM.TraceEvent.readWord 0
            (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
              shape segment index) word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace)
  physical_footprint_recorded :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
          shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none
  every_recorded_physical_footprint_address_fits :
    forall address,
      address ∈
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
            shape left right ->
        address <
          2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  physical_events_match_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
  successful_physical_reads_backed :
    forall {address : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord 0 address (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        address <
            (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
          (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
            some word
  physical_execution_determined_by_consumed_footprint :
    forall storeB : WordRAM.ReadStore,
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalStoresAgreeOnOrderedFootprint
          shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
          storeB left right ->
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right =
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape storeB left right
  physical_value_is_supplied_store_evaluator_value :
    forall physicalStore : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape physicalStore left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).value
  physical_value_dependency :
    forall storeA storeB : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right).value ->
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right).value
  reviewer_capacity_linear :
    concreteBPNativeSuccinctRMQReviewerCapacity shape.size =
      400000 * (shape.size + 1)
  physical_words_fit_capacity :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length <=
      concreteBPNativeSuccinctRMQReviewerCapacity shape.size
  reviewer_word_bits_logarithmic :
    concreteBPNativeSuccinctRMQReviewerWordBits shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  input_operands_fit_reviewer_word :
    forall operand, operand <= shape.size ->
      operand < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  segment_encodings_fit_reviewer_word :
    forall segment, segment <= concreteBPNativeDeadTraceSegment ->
      segment < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  every_physical_address_fits_reviewer_word :
    forall segment index,
      concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index <
        2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  physical_primitive_operands_fit_reviewer_word :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event
  every_stored_physical_word_fits_reviewer_word :
    forall {word : List Bool},
      word ∈ concreteBPNativeSuccinctRMQReviewerPhysicalWords shape ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  every_successful_returned_word_fits_reviewer_word :
    forall {segment index : Nat} {word : List Bool},
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index = some word ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size

/-- Existing theorem packets collected into the final trace model-adequacy record. -/
theorem concreteBPNativeSuccinctRMQFinalTraceModelAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
      shape left right := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story
      shape left right with
    ⟨hcost, hrefine, _hclass, hstore, hnoSynthetic,
      hreadBits, hprimitiveBits⟩
  exact
    { toCosted_eq := hcost
      refines_canonical_interpreted := hrefine
      cost_le :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
          shape left right
      event_readWord_or_wordRank_or_wordSelect :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect
          shape left right
      nonSyntheticWeight_sum_eq_trace_length :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_trace_length
          shape left right
      nonSyntheticWeight_sum_eq_cost :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost
          shape left right
      nonSyntheticWeight_sum_le_210 :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210
          shape left right
      matches_global_read_store := hstore
      event_bounds := fun event hmem =>
        ⟨hreadBits event hmem, hprimitiveBits event hmem⟩
      no_synthetic := hnoSynthetic
      successful_reads_backed_by_canonical_reviewer_payload := by
        intro segment index word hmem
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
            shape left right hmem
      compatibility_counted_sources_have_component_may_path :=
        concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path shape
      compatibility_shared_bp_dependencies_have_component_path :=
        concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected shape
      canonical_manifest_nodup :=
        concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup
      canonical_regions_exclusive :=
        @concreteBPNativeSuccinctRMQReviewerSource_region_injective
      canonical_segments_complete :=
        concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage
      every_emitted_read_has_listed_region := by
        intro segment index word? hmem
        exact
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_has_listed_region
            shape left right segment index word? hmem
      every_emitted_read_has_occurrence_provenance :=
        concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
          shape left right
      every_emitted_read_has_eventValue_producer_provenance :=
        concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked
          shape left right
      canonical_manifest_excludes_legacy_close :=
        concreteBPNativeSuccinctRMQReviewerPhysicalSources_exclude_legacy_close
      compatibility_tail_unreachable :=
        fun segment index hsegment =>
          concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_legacyTail_none
            shape segment index hsegment
      physical_words_erase_public_payload :=
        concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases shape
      physical_execution_refines_logical :=
        ⟨(concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
            shape left right).1,
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
            shape left right).2.1,
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
            shape left right).2.2,
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_translated
            shape left right⟩
      physical_footprint_recorded :=
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded
          shape left right
      every_recorded_physical_footprint_address_fits :=
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_address_fits_reviewerWordBits
          shape left right
      physical_events_match_store :=
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
          shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
          left right
      successful_physical_reads_backed := by
        intro address word hmem
        exact
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_successful_read_backed
            shape left right hmem
      physical_execution_determined_by_consumed_footprint := by
        intro storeB hagree
        exact
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint
            shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
            storeB left right hagree
      physical_value_is_supplied_store_evaluator_value := by
        intro physicalStore
        exact
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator
            shape physicalStore left right
      physical_value_dependency := by
        intro storeA storeB hneq
        exact
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne
            shape storeA storeB left right hneq
      reviewer_capacity_linear :=
        concreteBPNativeSuccinctRMQReviewerCapacity_linear shape.size
      physical_words_fit_capacity :=
        concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity shape
      reviewer_word_bits_logarithmic :=
        concreteBPNativeSuccinctRMQReviewerWordBits_le_log shape.size
      input_operands_fit_reviewer_word :=
        concreteBPNativeSuccinctRMQReviewerInputOperand_fits shape.size
      segment_encodings_fit_reviewer_word :=
        concreteBPNativeSuccinctRMQReviewerSegmentEncoding_fits shape.size
      every_physical_address_fits_reviewer_word :=
        concreteBPNativeSuccinctRMQReviewerPhysicalAddress_fits shape
      physical_primitive_operands_fit_reviewer_word :=
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_primitiveOperandsFit_reviewerWordBits
          shape left right
      every_stored_physical_word_fits_reviewer_word :=
        concreteBPNativeSuccinctRMQReviewerPhysicalWord_length_le_wordBits shape
      every_successful_returned_word_fits_reviewer_word :=
        concreteBPNativeSuccinctRMQReviewerSuccessfulRead_word_length_le_wordBits
          shape }

/--
Reviewer-native well-formedness certificate for the accepted physical machine.

Unlike the broader trace-adequacy inventory above, this record selects the
facts needed to identify one reviewer execution end to end: the canonical
payload and physical words, the translated physical store, the executed trace
and its exact ordered footprint, successful-read backing, the first-order
controller result, the current charged-trace cost, and the all-size word/address
bounds.  It introduces no new evaluator or execution path.
-/
structure ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop where
  physical_words_erase_canonical_payload :
    SuccinctSpace.flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape
  physical_execution_is_canonical_trace :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
          (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right
  canonical_trace_is_first_order_controller :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
  canonical_physical_store_adapts_to_global_store :
    concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape) =
      concreteBPNativeSuccinctRMQGlobalReadStore shape
  physical_events_match_canonical_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
  successful_physical_reads_backed_by_canonical_words :
    forall {address : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord 0 address (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        address <
            (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
          (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
            some word
  ordered_physical_footprint_recorded :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
          shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none
  supplied_execution_eq_of_exact_read_agreement :
    forall storeB : WordRAM.ReadStore,
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalStoresAgreeOnOrderedFootprint
          shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
          storeB left right ->
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right =
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape storeB left right
  physical_value_is_translated_supplied_store_value :
    forall physicalStore : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape physicalStore left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).value
  physical_value_dependency :
    forall storeA storeB : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right).value ->
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right).value
  no_synthetic_physical_event :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  certificate_weight_eq_trace_length :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.length
  certificate_weight_eq_cost :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right).cost
  certificate_weight_le_210 :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <=
      210
  reviewer_capacity_linear :
    concreteBPNativeSuccinctRMQReviewerCapacity shape.size =
      400000 * (shape.size + 1)
  physical_words_fit_capacity :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length <=
      concreteBPNativeSuccinctRMQReviewerCapacity shape.size
  reviewer_word_bits_logarithmic :
    concreteBPNativeSuccinctRMQReviewerWordBits shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  input_operands_fit_reviewer_word :
    forall operand, operand <= shape.size ->
      operand < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  segment_encodings_fit_reviewer_word :
    forall segment, segment <= concreteBPNativeDeadTraceSegment ->
      segment < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  every_physical_address_fits_reviewer_word :
    forall segment index,
      concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index <
        2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  every_recorded_footprint_address_fits_reviewer_word :
    forall address,
      address ∈
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
            shape left right ->
        address <
          2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  physical_primitive_operands_fit_reviewer_word :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event
  every_stored_physical_word_fits_reviewer_word :
    forall {word : List Bool},
      word ∈ concreteBPNativeSuccinctRMQReviewerPhysicalWords shape ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  every_successful_returned_word_fits_reviewer_word :
    forall {segment index : Nat} {word : List Bool},
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index = some word ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size

/--
Independent typed consumer contract for every mandatory fact in the
reviewer-native machine certificate.

The field names are deliberately distinct from the certificate fields.  The
conversion theorem below must project every certificate field literally; it
may not rebuild these facts from sibling theorems.  This keeps the public
acceptance contract sensitive to field deletion, proposition weakening, and
object substitution while introducing no new evaluator or machine object.
-/
structure ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop where
  requires_physical_words_erase_canonical_payload :
    SuccinctSpace.flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape
  requires_physical_execution_is_canonical_trace :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
          (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right
  requires_canonical_trace_is_first_order_controller :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
  requires_canonical_physical_store_adapts_to_global_store :
    concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape) =
      concreteBPNativeSuccinctRMQGlobalReadStore shape
  requires_physical_events_match_canonical_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
  requires_successful_physical_reads_backed_by_canonical_words :
    forall {address : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord 0 address (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        address <
            (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
          (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
            some word
  requires_ordered_physical_footprint_recorded :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
          shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none
  requires_supplied_execution_eq_of_exact_read_agreement :
    forall storeB : WordRAM.ReadStore,
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalStoresAgreeOnOrderedFootprint
          shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
          storeB left right ->
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right =
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape storeB left right
  requires_physical_value_is_translated_supplied_store_value :
    forall physicalStore : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape physicalStore left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).value
  requires_physical_value_dependency :
    forall storeA storeB : WordRAM.ReadStore,
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right).value ->
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right).value
  requires_no_synthetic_physical_event :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  requires_certificate_weight_eq_trace_length :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.length
  requires_certificate_weight_eq_cost :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right).cost
  requires_certificate_weight_le_210 :
    ((concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map WordRAM.TraceEvent.nonSyntheticWeight).sum <=
      210
  requires_reviewer_capacity_linear :
    concreteBPNativeSuccinctRMQReviewerCapacity shape.size =
      400000 * (shape.size + 1)
  requires_physical_words_fit_capacity :
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length <=
      concreteBPNativeSuccinctRMQReviewerCapacity shape.size
  requires_reviewer_word_bits_logarithmic :
    concreteBPNativeSuccinctRMQReviewerWordBits shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  requires_input_operands_fit_reviewer_word :
    forall operand, operand <= shape.size ->
      operand < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  requires_segment_encodings_fit_reviewer_word :
    forall segment, segment <= concreteBPNativeDeadTraceSegment ->
      segment < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  requires_every_physical_address_fits_reviewer_word :
    forall segment index,
      concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index <
        2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  requires_every_recorded_footprint_address_fits_reviewer_word :
    forall address,
      address ∈
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
            shape left right ->
        address <
          2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  requires_physical_primitive_operands_fit_reviewer_word :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event
  requires_every_stored_physical_word_fits_reviewer_word :
    forall {word : List Bool},
      word ∈ concreteBPNativeSuccinctRMQReviewerPhysicalWords shape ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size
  requires_every_successful_returned_word_fits_reviewer_word :
    forall {segment index : Nat} {word : List Bool},
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          segment index = some word ->
        word.length <=
          concreteBPNativeSuccinctRMQReviewerWordBits shape.size

/--
Project every mandatory certificate field into the independent required-facts
contract.  Every right-hand side is intentionally a literal projection from
`h`; sibling theorems and the canonical constructor are not used here.
-/
theorem ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed.requiredFacts
    {shape : Cartesian.CartesianShape} {left right : Nat}
    (h : ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
      shape left right) :
    ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
      shape left right :=
  { requires_physical_words_erase_canonical_payload :=
      h.physical_words_erase_canonical_payload
    requires_physical_execution_is_canonical_trace :=
      h.physical_execution_is_canonical_trace
    requires_canonical_trace_is_first_order_controller :=
      h.canonical_trace_is_first_order_controller
    requires_canonical_physical_store_adapts_to_global_store :=
      h.canonical_physical_store_adapts_to_global_store
    requires_physical_events_match_canonical_store :=
      h.physical_events_match_canonical_store
    requires_successful_physical_reads_backed_by_canonical_words :=
      h.successful_physical_reads_backed_by_canonical_words
    requires_ordered_physical_footprint_recorded :=
      h.ordered_physical_footprint_recorded
    requires_supplied_execution_eq_of_exact_read_agreement :=
      h.supplied_execution_eq_of_exact_read_agreement
    requires_physical_value_is_translated_supplied_store_value :=
      h.physical_value_is_translated_supplied_store_value
    requires_physical_value_dependency :=
      h.physical_value_dependency
    requires_no_synthetic_physical_event :=
      h.no_synthetic_physical_event
    requires_certificate_weight_eq_trace_length :=
      h.certificate_weight_eq_trace_length
    requires_certificate_weight_eq_cost :=
      h.certificate_weight_eq_cost
    requires_certificate_weight_le_210 :=
      h.certificate_weight_le_210
    requires_reviewer_capacity_linear :=
      h.reviewer_capacity_linear
    requires_physical_words_fit_capacity :=
      h.physical_words_fit_capacity
    requires_reviewer_word_bits_logarithmic :=
      h.reviewer_word_bits_logarithmic
    requires_input_operands_fit_reviewer_word :=
      h.input_operands_fit_reviewer_word
    requires_segment_encodings_fit_reviewer_word :=
      h.segment_encodings_fit_reviewer_word
    requires_every_physical_address_fits_reviewer_word :=
      h.every_physical_address_fits_reviewer_word
    requires_every_recorded_footprint_address_fits_reviewer_word :=
      h.every_recorded_footprint_address_fits_reviewer_word
    requires_physical_primitive_operands_fit_reviewer_word :=
      h.physical_primitive_operands_fit_reviewer_word
    requires_every_stored_physical_word_fits_reviewer_word :=
      h.every_stored_physical_word_fits_reviewer_word
    requires_every_successful_returned_word_fits_reviewer_word :=
      h.every_successful_returned_word_fits_reviewer_word }

/-- The accepted canonical objects satisfy the reviewer-native certificate. -/
theorem concreteBPNativeSuccinctRMQReviewerMachineWellFormed
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
      shape left right := by
  let h := concreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right
  exact
    { physical_words_erase_canonical_payload :=
        h.physical_words_erase_public_payload
      physical_execution_is_canonical_trace :=
        ⟨h.physical_execution_refines_logical.1,
          h.physical_execution_refines_logical.2.1,
          by simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
            using h.physical_execution_refines_logical.2.2.1⟩
      canonical_trace_is_first_order_controller :=
        h.refines_canonical_interpreted
      canonical_physical_store_adapts_to_global_store :=
        concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter_canonical shape
      physical_events_match_canonical_store :=
        h.physical_events_match_store
      successful_physical_reads_backed_by_canonical_words :=
        h.successful_physical_reads_backed
      ordered_physical_footprint_recorded :=
        h.physical_footprint_recorded
      supplied_execution_eq_of_exact_read_agreement :=
        h.physical_execution_determined_by_consumed_footprint
      physical_value_is_translated_supplied_store_value :=
        h.physical_value_is_supplied_store_evaluator_value
      physical_value_dependency := h.physical_value_dependency
      no_synthetic_physical_event :=
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_no_syntheticCostOnlyPrimitive
          shape left right
      certificate_weight_eq_trace_length :=
        h.nonSyntheticWeight_sum_eq_trace_length
      certificate_weight_eq_cost := h.nonSyntheticWeight_sum_eq_cost
      certificate_weight_le_210 := h.nonSyntheticWeight_sum_le_210
      reviewer_capacity_linear := h.reviewer_capacity_linear
      physical_words_fit_capacity := h.physical_words_fit_capacity
      reviewer_word_bits_logarithmic := h.reviewer_word_bits_logarithmic
      input_operands_fit_reviewer_word := h.input_operands_fit_reviewer_word
      segment_encodings_fit_reviewer_word :=
        h.segment_encodings_fit_reviewer_word
      every_physical_address_fits_reviewer_word :=
        h.every_physical_address_fits_reviewer_word
      every_recorded_footprint_address_fits_reviewer_word :=
        h.every_recorded_physical_footprint_address_fits
      physical_primitive_operands_fit_reviewer_word :=
        h.physical_primitive_operands_fit_reviewer_word
      every_stored_physical_word_fits_reviewer_word :=
        h.every_stored_physical_word_fits_reviewer_word
      every_successful_returned_word_fits_reviewer_word :=
        h.every_successful_returned_word_fits_reviewer_word }

/-- The canonical certificate supplies every independently pinned fact. -/
theorem concreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
      shape left right :=
  (concreteBPNativeSuccinctRMQReviewerMachineWellFormed
    shape left right).requiredFacts

/-- Paper-facing exactness alias paired with the model-adequacy bundle. -/
theorem concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

/-- Agreement on the safe final-layout footprint implies agreement on the
first supplied execution's exact ordered dynamic read footprint. -/
theorem concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape storeA storeB)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
      shape storeA storeB left right := by
  rw [concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_iff]
  intro segment index word? hmem
  apply hfoot segment index
  have hlt : segment < 23 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt
      shape storeA left right hmem
  unfold concreteBPNativeSuccinctRMQWholeQueryReadFootprint
  unfold concreteBPNativeDeadTraceSegment
  omega

/--
Safe final-layout agreement determines the complete supplied-store execution
through the exact ordered dynamic-read theorem.  This wrapper has the legacy
safe-footprint proposition but makes the M1 proof route explicit.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint_via_orderedReadFootprint
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape storeA storeB)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
      shape storeA storeB left right
        (concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint
          shape hfoot left right)

/--
Safe-footprint equality with the canonical global trace, routed first through
exact ordered dynamic-read agreement and complete `TraceResult` equality.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint_via_orderedReadFootprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right := by
  calc
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint_via_orderedReadFootprint
        shape hfoot left right
    _ = concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right :=
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
        shape left right

/--
Successful-read backing under safe-footprint agreement, after exact dynamic
agreement has identified the complete supplied and canonical traces.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global_via_orderedReadFootprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word := by
  intro segment index word hmem
  have hmemGlobal :
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace := by
    rw [
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint_via_orderedReadFootprint
        shape store hfoot left right] at hmem
    exact hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
      shape left right hmemGlobal

/--
The principled supplied-store cost bound under safe-footprint agreement,
obtained only after exact dynamic agreement fixes the complete trace result.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_principledAllSizeChargedTrace_via_orderedReadFootprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint_via_orderedReadFootprint
      shape store hfoot left right]
  simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted] using
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
      shape left right

/--
Exact RMQ answers under safe-footprint agreement, after complete-result
equality has been obtained from exact ordered dynamic-read agreement.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_exact_of_footprint_global_via_orderedReadFootprint
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint_via_orderedReadFootprint
      shape store hfoot left (left + len)]
  simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted] using
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound


/--
Small supplied-store adequacy packet for the final whole-query replay.  This is
separate from the canonical global trace packet because it talks about a caller
provided `WordRAM.ReadStore`.
-/
structure ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : Prop where
  matches_supplied_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        event.matchesReadStore store
  global_store_eval :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right
  refines_canonical_interpreted :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
  no_synthetic :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  store_parametric_from_footprint :
    forall {storeB : WordRAM.ReadStore},
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
          shape store storeB ->
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right =
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape storeB left right
  ordered_read_footprint_recorded :
    concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        shape store left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape store left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord segment index _ => some (segment, index)
        | _ => none
  store_parametric_from_ordered_read_footprint :
    forall {storeB : WordRAM.ReadStore},
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
          shape store storeB left right ->
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right =
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape storeB left right

/-- Existing supplied-store theorems collected into one small adequacy packet. -/
theorem concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
      shape store left right := by
  exact
    { matches_supplied_store :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
          shape store left right
      global_store_eval :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
          shape left right
      refines_canonical_interpreted :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_refines_canonicalInterpretedCosted
          shape left right
      no_synthetic :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store left right
      store_parametric_from_footprint := by
        intro storeB hfoot
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
            shape store storeB left right
              (concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint
                shape hfoot left right)
      ordered_read_footprint_recorded :=
        concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore_recorded
          shape store left right
      store_parametric_from_ordered_read_footprint := by
        intro storeB hagree
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
            shape store storeB left right hagree }

/--
Full model-soundness packet for the final succinct RMQ query in the explicit
WordRAM/read-store/counted-payload model.  The packet is deliberately scoped to
the formal model: it combines the canonical trace model adequacy, the
supplied-store replay adequacy, emitted-read containment in the safe final
layout footprint, and the fact that a supplied store agreeing with the concrete
global store on that footprint recovers the canonical trace and costed result.
-/
structure ConcreteBPNativeSuccinctRMQFinalFullModelSoundness
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : Prop where
  trace_model :
    ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
      shape left right
  supplied_store_model :
    ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
      shape store left right
  supplied_reads_subset_footprint :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment
  canonical_reads_subset_footprint :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment
  supplied_eq_global_of_footprint :
    concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape) ->
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape store left right =
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right
  supplied_costed_eq_global_of_footprint :
    concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape) ->
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
          shape store left right =
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
          shape left right

/-- Existing final trace and supplied-store theorems collected into one packet. -/
theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalFullModelSoundness
      shape store left right := by
  exact
    { trace_model :=
        concreteBPNativeSuccinctRMQFinalTraceModelAdequacy
          shape left right
      supplied_store_model :=
        concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
          shape store left right
      supplied_reads_subset_footprint :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint
          shape store left right
      canonical_reads_subset_footprint :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_reads_subset_footprint
          shape left right
      supplied_eq_global_of_footprint := by
        intro hfoot
        calc
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
              shape store left right =
              concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
                shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                left right :=
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
              shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              left right
                (concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint
                  shape hfoot left right)
          _ = concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
                shape left right :=
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
              shape left right
      supplied_costed_eq_global_of_footprint := by
        intro hfoot
        exact congrArg WordRAM.TraceResult.toCosted
          (calc
            concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
                shape store left right =
                concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
                  shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                  left right :=
              concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
                shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                left right
                  (concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint
                    shape hfoot left right)
            _ = concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
                  shape left right :=
              concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
                shape left right) }

/--
Exactness for any supplied store that agrees with the canonical global store on
the safe final layout footprint.
-/
theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [(concreteBPNativeSuccinctRMQFinalFullModelSoundness
    shape store left (left + len)).supplied_costed_eq_global_of_footprint hfoot]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_canonicalTransitional
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost := by
  rw [(concreteBPNativeSuccinctRMQFinalFullModelSoundness
    shape store left right).supplied_costed_eq_global_of_footprint hfoot]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
      shape left right

theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_liveCompatibility
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQLiveCompatibilityQueryCost := by
  rw [(concreteBPNativeSuccinctRMQFinalFullModelSoundness
    shape store left right).supplied_costed_eq_global_of_footprint hfoot]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_liveCompatibility
      shape left right

theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  rw [(concreteBPNativeSuccinctRMQFinalFullModelSoundness
    shape store left right).supplied_costed_eq_global_of_footprint hfoot]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
      shape left right

end SuccinctFinal

end RMQ

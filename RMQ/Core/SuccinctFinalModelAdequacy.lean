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
whole-query program, its events are reads or word primitives, successful reads
are backed by counted flat payload words, event data are bounded, and no event
is the synthetic cost-only marker.
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
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
          SuccinctSelect.sparseDenseFalseSelectQueryCost
  event_read_or_primitive :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive
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
  canonical_manifest_counted_iff_live :
    forall source : ReviewerSource, source.Counted <-> source.Live
  canonical_counted_sources_have_operational_connection :
    forall source : ReviewerSource, source.Counted ->
      (source = .sharedBPCode /\
        Exists fun consumer : ReviewerSharedBPConsumer => consumer.Checked) \/
      (Exists fun leaf : ReviewerReadLeaf => source.OperationallyOwnedBy leaf)
  canonical_counted_sources_reach_evaluator :
    forall source : ReviewerSource, source.Counted ->
      (source = .sharedBPCode /\
        Exists fun consumer : ReviewerSharedBPConsumer =>
        Exists fun instr : WholeQueryInstr =>
          consumer.Checked /\
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram /\
          instr.reviewerReadLeaf? = some consumer.leaf /\
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty consumer.leaf instr) \/
      (Exists fun leaf : ReviewerReadLeaf =>
        Exists fun instr : WholeQueryInstr =>
          source.OperationallyOwnedBy leaf /\
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram /\
          instr.reviewerReadLeaf? = some leaf /\
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty leaf instr)
  all_shared_bp_dependencies_reach_evaluator :
    forall consumer : ReviewerSharedBPConsumer,
      consumer.Checked ∧
        Exists fun instr : WholeQueryInstr =>
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
          instr.reviewerReadLeaf? = some consumer.leaf ∧
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty consumer.leaf instr
  canonical_manifest_nodup :
    List.Nodup concreteBPNativeSuccinctRMQReviewerPhysicalSources
  canonical_regions_exclusive :
    forall {source other : ReviewerSource},
      source.region = other.region -> source = other
  canonical_segments_complete :
    forall segment : Nat,
      (Exists fun source =>
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
          some source) <-> segment < 21
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
  every_emitted_read_has_operational_source :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        Exists fun source : ReviewerSource =>
        Exists fun leaf : ReviewerReadLeaf =>
        Exists fun instr : WholeQueryInstr =>
          concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
              some source /\
          concreteBPNativeSuccinctRMQReviewerSegmentLeaf? segment =
              some leaf /\
          source.Counted /\ source.Live /\
          source.OperationallyOwnedBy leaf /\
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram /\
          instr.reviewerReadLeaf? = some leaf /\
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty leaf instr
  operational_consumer_labels_are_derived :
    forall {source : ReviewerSource} {leaf : ReviewerReadLeaf},
      source ≠ .sharedBPCode -> source.OperationallyOwnedBy leaf ->
        source.consumer? = some leaf.consumer
  canonical_manifest_excludes_legacy_close :
    forall (source : ReviewerSource),
      source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources ->
      forall legacy : ConcreteBPNativeSuccinctRMQFlatPayloadSource,
        source.legacyOuterSource? = some legacy ->
          Not legacy.LegacyCloseOrInterior
  compatibility_tail_unreachable :
    forall segment index, 21 <= segment ->
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
    ⟨hcost, hrefine, hclass, hstore, hnoSynthetic,
      hreadBits, hprimitiveBits⟩
  exact
    { toCosted_eq := hcost
      refines_canonical_interpreted := hrefine
      cost_le :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
          shape left right
      event_read_or_primitive := hclass
      matches_global_read_store := hstore
      event_bounds := fun event hmem =>
        ⟨hreadBits event hmem, hprimitiveBits event hmem⟩
      no_synthetic := hnoSynthetic
      successful_reads_backed_by_canonical_reviewer_payload := by
        intro segment index word hmem
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
            shape left right hmem
      canonical_manifest_counted_iff_live :=
        concreteBPNativeSuccinctRMQReviewerSource_counted_iff_live
      canonical_counted_sources_have_operational_connection :=
        concreteBPNativeSuccinctRMQReviewerSource_counted_operational_connection
      canonical_counted_sources_reach_evaluator := by
        intro source hcounted
        exact
          concreteBPNativeSuccinctRMQReviewerSource_counted_evaluator_connection
            shape left right WholeQueryState.empty source hcounted
      all_shared_bp_dependencies_reach_evaluator :=
        concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_evaluator_connection
          shape left right WholeQueryState.empty
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
      every_emitted_read_has_operational_source :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_operational_source
          shape left right
      operational_consumer_labels_are_derived :=
        concreteBPNativeSuccinctRMQReviewerSource_operational_owner_consumer
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
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
            shape hfoot left right
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
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint
            shape store hfoot left right
      supplied_costed_eq_global_of_footprint := by
        intro hfoot
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
            shape store hfoot left right }

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
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_exact_of_footprint_global
      hshape hfoot hlen hbound

theorem concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_canonicalTransitional
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_canonicalTransitional
      shape store hfoot left right

end SuccinctFinal

end RMQ

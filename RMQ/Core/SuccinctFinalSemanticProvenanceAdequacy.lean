import RMQ.Core.SuccinctFinal.RAM.ReviewerReachability

/-!
# W19 reviewer-manifest semantic adequacy

This proof-only packet keeps the symbolic source witnesses out of the native
validator link closure.  Its claims are deliberately not parameterized by a
current shape or query: each live manifest source has some successful closed
valid execution witness, while indexed forward provenance remains in the
query-specific final trace-model packet.
-/

namespace RMQ.SuccinctFinal

/-- Query-independent semantic adequacy of the canonical reviewer manifest.
The positive predicate is successful indexed occurrence in some actual closed
whole-query execution under a valid ordinary-list query.  The mutation
predicate is the same existential execution relation with arbitrary read
result, and the checked bridge below relates the two.  The B4 fields extend
the packet with the chunk-table provenance strength: per-leaf successful
occurrences for the shared fringe chunk table (segment `21`), one same-block
occurrence retaining the identical local position from its whole-query
producer through the exact invocation and charged component subtrace, and
positional repeated-equal-read witnesses with distinct global positions AND
distinct producing instruction positions for both chunk-table sources
(segments `21` and `22`). -/
structure ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy : Prop where
  canonical_counted_sources_have_successful_closed_valid_occurrence :
    forall source : ReviewerSource, source.Counted ->
      source.HasSuccessfulClosedValidOccurrence
  all_shared_bp_dependencies_have_successful_closed_valid_occurrence :
    forall consumer : ReviewerSharedBPConsumer,
      consumer.HasSuccessfulClosedValidOccurrence
  successful_closed_valid_occurrence_implies_operational_producer :
    forall claim : ReviewerProducerClaim,
      claim.HasSuccessfulClosedValidOccurrence -> claim.HasOperationalProducer
  fresh_unused_source_rejected_by_operational_producer :
    ¬ concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.HasOperationalProducer
  canonical_manifest_nodup :
    List.Nodup concreteBPNativeSuccinctRMQReviewerPhysicalSources
  canonical_segments_complete :
    forall segment : Nat,
      (Exists fun source =>
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source) <->
          segment < 23
  fringe_chunk_table_every_reader_leaf_has_successful_closed_valid_occurrence :
    forall leaf : ReviewerReadLeaf,
      (ReviewerProducerClaim.mk concreteBPNativeFringeChunkTraceSegment
        leaf).HasSuccessfulClosedValidOccurrence
  same_block_fringe_chunk_occurrence_retains_exact_identity :
    ∃ xs : List Int,
    ∃ globalPos localPos index : Nat,
    ∃ word : WordRAM.Word,
    ∃ preState : WholeQueryState,
      ValidRange xs 0 1 ∧
      preState =
        (WholeQueryProgram.evalGlobalWordTrace (Cartesian.shape xs) 0 1
          (concreteBPNativeSuccinctRMQWholeQueryProgram.take 2)
          WholeQueryState.empty).value ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) 0 1).trace[globalPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) 0 1 globalPos
        concreteBPNativeFringeChunkTraceSegment index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        0 1 globalPos 2 concreteBPNativeFringeChunkTraceSegment index
        (some word) ∧
      WholeQueryProgram.ProducesEventAt (Cartesian.shape xs) 0 1
        (.readWord concreteBPNativeFringeChunkTraceSegment index (some word))
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        globalPos 2
        (WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose)
        preState localPos ∧
      globalPos =
        (WholeQueryProgram.evalGlobalWordTrace (Cartesian.shape xs) 0 1
          (concreteBPNativeSuccinctRMQWholeQueryProgram.take 2)
          WholeQueryState.empty).trace.length + localPos ∧
      WholeQueryInstr.InvokesReviewerRead 0 1 preState
        (WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose)
        (.canonicalClose 1 1) ∧
      ((.canonicalClose 1 1 : ReviewerReadInvocation).componentTrace
        (Cartesian.shape xs))[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        (Cartesian.shape xs) 1 1).trace[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
        (Cartesian.shape xs)
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          (Cartesian.shape xs) concreteBPNativeRankCloseTraceSegmentBase)
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
          (Cartesian.shape xs)) 1 1).trace[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word))
  fringe_chunk_repeated_equal_read_occurrences_have_distinct_receipts :
    ∃ xs : List Int,
    ∃ left right firstPos secondPos instrPos1 instrPos2 index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧
      firstPos ≠ secondPos ∧ instrPos1 ≠ instrPos2 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right firstPos instrPos1 concreteBPNativeFringeChunkTraceSegment
        index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right secondPos instrPos2 concreteBPNativeFringeChunkTraceSegment
        index (some word)
  select_chunk_repeated_equal_read_occurrences_have_distinct_receipts :
    ∃ xs : List Int,
    ∃ left right firstPos secondPos instrPos1 instrPos2 index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧
      firstPos ≠ secondPos ∧ instrPos1 ≠ instrPos2 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right firstPos instrPos1 concreteBPNativeSelectChunkTraceSegment
        index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right secondPos instrPos2 concreteBPNativeSelectChunkTraceSegment
        index (some word)

/-- The concrete manifest discharges the global W19 packet using the actual
small, symbolic long-super, and symbolic sparse-local witness families. -/
theorem concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy :
    ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy :=
  { canonical_counted_sources_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence
    all_shared_bp_dependencies_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence
    successful_closed_valid_occurrence_implies_operational_producer :=
      fun _ hclaim =>
        ReviewerProducerClaim.hasOperationalProducer_of_successful hclaim
    fresh_unused_source_rejected_by_operational_producer :=
      concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer
    canonical_manifest_nodup :=
      concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup
    canonical_segments_complete :=
      concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage
    fringe_chunk_table_every_reader_leaf_has_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQFringeChunkTable_every_reader_leaf_successful_occurrence
    same_block_fringe_chunk_occurrence_retains_exact_identity :=
      concreteBPNativeSuccinctRMQSingleton_sameBlockFringeChunk_indexed_occurrence_receipt
    fringe_chunk_repeated_equal_read_occurrences_have_distinct_receipts :=
      concreteBPNativeSuccinctRMQFringeChunk_repeated_equal_read_distinct_instruction_receipts
    select_chunk_repeated_equal_read_occurrences_have_distinct_receipts :=
      concreteBPNativeSuccinctRMQSelectChunk_repeated_equal_read_distinct_instruction_receipts }

end RMQ.SuccinctFinal

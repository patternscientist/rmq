import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall

/-!
# Whole-query charge-policy value dependency for the chunk tables (B4)

Matrix row REQ-B4-06 (charge-policy uniformity): the B2/B3 corruption
witnesses (`bpFringeChunkTable_corruption_changes_fringe_value`,
`bpChunkSelectTable_corruption_changes_select_value`) are component-level;
this module lifts store-parametric value dependency for the two chunk-table
sources to the ACCEPTED whole-query route.  Each theorem exhibits a concrete
valid query whose canonical execution consumes a successful chunk-table read
(the consumed-read fact is part of the statement) and concludes that EVERY
supplied store disagreeing with the returned word at exactly that address
changes the whole-query supplied-store execution
(`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore`),
via the engine
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_ne_of_consumed_read_disagreement`.

Projection level (recorded honestly): the conclusion is full-`TraceResult`
inequality of the accepted supplied-store executions with the disagreeing
CONSUMED read as the exhibited cause; answer-projection (`.value`)
dependency for the chunk decodes is carried by the checked component-level
corruption witnesses above, and the flat-physical/list-facing transfer of
value inequalities follows
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne`'s
pattern.
-/

namespace RMQ

namespace SuccinctFinal

/-- A disagreement on a CONSUMED fringe-chunk-table (segment 21) address
changes the accepted whole-query execution. -/
theorem concreteBPNativeSuccinctRMQFringeChunkConsumedDisagreement_changes_wholeQuery :
    ∃ (xs : List Int) (left right index : Nat) (word : WordRAM.Word),
      ValidRange xs left right ∧
      WordRAM.TraceEvent.readWord concreteBPNativeFringeChunkTraceSegment
          index (some word) ∈
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          (Cartesian.shape xs) left right).trace ∧
      ∀ storeB : WordRAM.ReadStore,
        storeB.readWord? concreteBPNativeFringeChunkTraceSegment index ≠
          some word ->
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (Cartesian.shape xs)
            (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
            left right ≠
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (Cartesian.shape xs) storeB left right := by
  obtain ⟨xs, left, right, firstPos, secondPos, index, word, hvalid, _hne,
      hfirst, _hsecond, _hr1, _hr2⟩ :=
    concreteBPNativeSuccinctRMQFringeChunk_repeated_equal_read_distinct_receipts
  have hmem := List.mem_of_getElem? hfirst
  exact ⟨xs, left, right, index, word, hvalid, hmem, fun storeB hdis =>
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_ne_of_consumed_read_disagreement
      (Cartesian.shape xs) left right storeB hmem hdis⟩

/-- A disagreement on a CONSUMED select-chunk-table (segment 22) address
changes the accepted whole-query execution. -/
theorem concreteBPNativeSuccinctRMQSelectChunkConsumedDisagreement_changes_wholeQuery :
    ∃ (xs : List Int) (left right index : Nat) (word : WordRAM.Word),
      ValidRange xs left right ∧
      WordRAM.TraceEvent.readWord concreteBPNativeSelectChunkTraceSegment
          index (some word) ∈
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          (Cartesian.shape xs) left right).trace ∧
      ∀ storeB : WordRAM.ReadStore,
        storeB.readWord? concreteBPNativeSelectChunkTraceSegment index ≠
          some word ->
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (Cartesian.shape xs)
            (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
            left right ≠
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (Cartesian.shape xs) storeB left right := by
  obtain ⟨xs, left, right, firstPos, secondPos, index, word, hvalid, _hne,
      hfirst, _hsecond, _hr1, _hr2⟩ :=
    concreteBPNativeSuccinctRMQSelectChunk_repeated_equal_read_distinct_receipts
  have hmem := List.mem_of_getElem? hfirst
  exact ⟨xs, left, right, index, word, hvalid, hmem, fun storeB hdis =>
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_ne_of_consumed_read_disagreement
      (Cartesian.shape xs) left right storeB hmem hdis⟩

/-- Drop-store instantiation for segment 21: the canonical store mutated
ONLY at the consumed fringe-chunk-table address changes the accepted
whole-query execution. -/
theorem concreteBPNativeSuccinctRMQFringeChunkDrop_changes_wholeQuery :
    ∃ (xs : List Int) (left right index : Nat),
      ValidRange xs left right ∧
      (∃ word : WordRAM.Word,
        WordRAM.TraceEvent.readWord concreteBPNativeFringeChunkTraceSegment
            index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            (Cartesian.shape xs) left right).trace) ∧
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          (Cartesian.shape xs)
          (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
          left right ≠
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          (Cartesian.shape xs)
          (concreteBPNativeSuccinctRMQDropLogicalAddressStore
            (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
            concreteBPNativeFringeChunkTraceSegment index)
          left right := by
  obtain ⟨xs, left, right, index, word, hvalid, hmem, hall⟩ :=
    concreteBPNativeSuccinctRMQFringeChunkConsumedDisagreement_changes_wholeQuery
  refine ⟨xs, left, right, index, hvalid, ⟨word, hmem⟩, hall _ ?_⟩
  rw [concreteBPNativeSuccinctRMQDropLogicalAddressStore_dropped]
  exact fun h => Option.noConfusion h

/-- Drop-store instantiation for segment 22: the canonical store mutated
ONLY at the consumed select-chunk-table address changes the accepted
whole-query execution. -/
theorem concreteBPNativeSuccinctRMQSelectChunkDrop_changes_wholeQuery :
    ∃ (xs : List Int) (left right index : Nat),
      ValidRange xs left right ∧
      (∃ word : WordRAM.Word,
        WordRAM.TraceEvent.readWord concreteBPNativeSelectChunkTraceSegment
            index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            (Cartesian.shape xs) left right).trace) ∧
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          (Cartesian.shape xs)
          (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
          left right ≠
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          (Cartesian.shape xs)
          (concreteBPNativeSuccinctRMQDropLogicalAddressStore
            (concreteBPNativeSuccinctRMQGlobalReadStore (Cartesian.shape xs))
            concreteBPNativeSelectChunkTraceSegment index)
          left right := by
  obtain ⟨xs, left, right, index, word, hvalid, hmem, hall⟩ :=
    concreteBPNativeSuccinctRMQSelectChunkConsumedDisagreement_changes_wholeQuery
  refine ⟨xs, left, right, index, hvalid, ⟨word, hmem⟩, hall _ ?_⟩
  rw [concreteBPNativeSuccinctRMQDropLogicalAddressStore_dropped]
  exact fun h => Option.noConfusion h

end SuccinctFinal

end RMQ

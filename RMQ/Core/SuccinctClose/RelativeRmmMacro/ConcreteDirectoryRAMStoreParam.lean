import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM
import RMQ.Core.WordRAM.ReadStoreEval

/-!
# Store-parametric compact LCA-close evaluators

Store-parameterized (`WithStore`) twins of the structural trace evaluators
behind the all-size compact LCA-close leg.  Every BP-code payload read takes
both its value and its trace-event word from a supplied `WordRAM.ReadStore` at
segment `0`, mirroring the zero-block store-parametric leaf already present in
`ConcreteDirectoryRAM.lean`.  The rank seed stays an abstract
`Nat -> WordRAM.TraceResult Nat` parameter, so callers can supply the
store-parametric final false-rank leaf.
-/

namespace RMQ

namespace SuccinctClose

namespace ConcreteCompactBPCloseLCADirectory

/-- Store-parameterized relabeled fixed-width natural table read. -/
def fixedWidthNatTableReadTraceResultAtSegmentWithStore
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (i : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap segmentBase deadSegment)
    (WordRAM.TraceResult.ofResult
      ((table.readProgram i).evalR
        (store.pullback
          (WordRAM.singletonSegmentMap segmentBase deadSegment))))

theorem fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment : Nat) {store : WordRAM.ReadStore}
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          table.wordRAMStore.readWord? segment index)
    (i : Nat) :
    fixedWidthNatTableReadTraceResultAtSegmentWithStore
        table segmentBase deadSegment store i =
      table.readTraceResultAtSegment segmentBase deadSegment i := by
  unfold fixedWidthNatTableReadTraceResultAtSegmentWithStore
  unfold SuccinctSpace.FixedWidthNatTable.readTraceResultAtSegment
  unfold SuccinctSpace.FixedWidthNatTable.readTraceResult
  rw [WordRAM.ReadStore.pullback_eq_ofStore_of_agree
    (WordRAM.singletonSegmentMap segmentBase deadSegment)
    store table.wordRAMStore hread, WordRAM.Program.evalR_ofStore]

theorem fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment : Nat)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index)
    (i : Nat) :
    fixedWidthNatTableReadTraceResultAtSegmentWithStore
        table segmentBase deadSegment storeA i =
      fixedWidthNatTableReadTraceResultAtSegmentWithStore
        table segmentBase deadSegment storeB i := by
  unfold fixedWidthNatTableReadTraceResultAtSegmentWithStore
  rw [WordRAM.ReadStore.pullback_eq_of_agree_on_map
    (WordRAM.singletonSegmentMap segmentBase deadSegment) hread]

theorem fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (i : Nat) :
    forall event,
      event ∈
          (fixedWidthNatTableReadTraceResultAtSegmentWithStore
            table segmentBase deadSegment store i).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp only [fixedWidthNatTableReadTraceResultAtSegmentWithStore,
    WordRAM.TraceResult.relabelReadSegmentsWith,
    WordRAM.TraceResult.ofResult] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  exact
    WordRAM.TraceEvent.relabelReadSegmentWith_matchesReadStore_of_pullback
      (WordRAM.singletonSegmentMap segmentBase deadSegment) store
      (WordRAM.Program.evalR_matchesReadStore (table.readProgram i)
        (store.pullback
          (WordRAM.singletonSegmentMap segmentBase deadSegment))
        inner hinner)

theorem fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (i : Nat) :
    forall event,
      event ∈
          (fixedWidthNatTableReadTraceResultAtSegmentWithStore
            table segmentBase deadSegment store i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold fixedWidthNatTableReadTraceResultAtSegmentWithStore
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.readProgram i).evalR
          (store.pullback
            (WordRAM.singletonSegmentMap segmentBase deadSegment))))
      (by
        intro event hmem
        simpa only [WordRAM.TraceResult.ofResult_trace] using
          WordRAM.Program.evalR_no_syntheticCostOnlyPrimitive
            (table.readProgram i)
            (store.pullback
              (WordRAM.singletonSegmentMap segmentBase deadSegment))
            event hmem)

def summaryTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat × Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (fixedWidthNatTableReadTraceResultAtSegmentWithStore
      table.baselineTable segments.baseline segments.deadSegment store
      (block / blocksPerSuper))
    fun baseline? =>
      WordRAM.TraceResult.bind
        (fixedWidthNatTableReadTraceResultAtSegmentWithStore
          table.minRelTable segments.minRel segments.deadSegment store block)
        fun minRel? =>
          WordRAM.TraceResult.bind
            (fixedWidthNatTableReadTraceResultAtSegmentWithStore
              table.maxRelTable segments.maxRel segments.deadSegment store
              block)
            fun maxRel? =>
              WordRAM.TraceResult.map
                (fun argOffset? =>
                  match baseline?, minRel?, maxRel?, argOffset? with
                  | some baseline, some minRel, some maxRel, some argOffset =>
                      some (baseline, minRel, maxRel, argOffset)
                  | _, _, _, _ => none)
                (fixedWidthNatTableReadTraceResultAtSegmentWithStore
                  table.argOffsetTable segments.argOffset
                  segments.deadSegment store block)

theorem summaryTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {store : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          table.argOffsetTable.wordRAMStore.readWord? segment index)
    (block : Nat) :
    summaryTraceResultAtSegmentsWithStore table segments store block =
      table.summaryTraceResultAtSegments segments block := by
  unfold summaryTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments
  simp only [
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      table.baselineTable segments.baseline segments.deadSegment
      hbaseline (block / blocksPerSuper),
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      table.minRelTable segments.minRel segments.deadSegment hminRel block,
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      table.maxRelTable segments.maxRel segments.deadSegment hmaxRel block,
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      table.argOffsetTable segments.argOffset segments.deadSegment
      hargOffset block]
  rfl

theorem summaryTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index)
    (block : Nat) :
    summaryTraceResultAtSegmentsWithStore table segments storeA block =
      summaryTraceResultAtSegmentsWithStore table segments storeB block := by
  unfold summaryTraceResultAtSegmentsWithStore
  simp only [
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      table.baselineTable segments.baseline segments.deadSegment
      hbaseline (block / blocksPerSuper),
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      table.minRelTable segments.minRel segments.deadSegment hminRel block,
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      table.maxRelTable segments.maxRel segments.deadSegment hmaxRel block,
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      table.argOffsetTable segments.argOffset segments.deadSegment
      hargOffset block]

theorem summaryTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) :
    forall event,
      event ∈
          (summaryTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        event.matchesReadStore store := by
  unfold summaryTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
        table.baselineTable segments.baseline segments.deadSegment store
        (block / blocksPerSuper)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
          table.minRelTable segments.minRel segments.deadSegment store block
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
            table.maxRelTable segments.maxRel segments.deadSegment store block
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
            table.argOffsetTable segments.argOffset segments.deadSegment
            store block

theorem summaryTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) :
    forall event,
      event ∈
          (summaryTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold summaryTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        table.baselineTable segments.baseline segments.deadSegment store
        (block / blocksPerSuper)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
          table.minRelTable segments.minRel segments.deadSegment store block
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
            table.maxRelTable segments.maxRel segments.deadSegment store block
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
            table.argOffsetTable segments.argOffset segments.deadSegment
            store block

def minCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (summaryTraceResultAtSegmentsWithStore table segments store block)

theorem minCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {store : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          table.argOffsetTable.wordRAMStore.readWord? segment index)
    (block : Nat) :
    minCandidateTraceResultAtSegmentsWithStore table segments store block =
      table.minCandidateTraceResultAtSegments segments block := by
  unfold minCandidateTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments
  rw [summaryTraceResultAtSegmentsWithStore_eq_of_agree
    table segments hbaseline hminRel hmaxRel hargOffset block]

theorem minCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index)
    (block : Nat) :
    minCandidateTraceResultAtSegmentsWithStore table segments storeA block =
      minCandidateTraceResultAtSegmentsWithStore
        table segments storeB block := by
  unfold minCandidateTraceResultAtSegmentsWithStore
  rw [summaryTraceResultAtSegmentsWithStore_store_parametric
    table segments hbaseline hminRel hmaxRel hargOffset block]

theorem minCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) :
    forall event,
      event ∈
          (minCandidateTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        event.matchesReadStore store := by
  unfold minCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact summaryTraceResultAtSegmentsWithStore_matchesReadStore
    table segments store block

theorem minCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block : Nat) :
    forall event,
      event ∈
          (minCandidateTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold minCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    summaryTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
      table segments store block

def summaryRangeScanFromTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  match steps with
  | 0 => WordRAM.TraceResult.pure best?
  | steps + 1 =>
      WordRAM.TraceResult.bind
        (minCandidateTraceResultAtSegmentsWithStore
          table segments store block)
        fun candidate? =>
          summaryRangeScanFromTraceResultAtSegmentsWithStore
            table segments store (block + 1) steps
            (bpCandidateMerge? best? candidate?)

def summaryRangeScanTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  match count with
  | 0 => WordRAM.TraceResult.pure none
  | steps + 1 =>
      WordRAM.TraceResult.bind
        (minCandidateTraceResultAtSegmentsWithStore
          table segments store startBlock)
        fun first? =>
          summaryRangeScanFromTraceResultAtSegmentsWithStore
            table segments store (startBlock + 1) steps first?

def boundedSummaryRangeScanTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    summaryRangeScanTraceResultAtSegmentsWithStore
      table segments store startBlock count
  else
    WordRAM.TraceResult.pure none

theorem summaryRangeScanFromTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {store : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          table.argOffsetTable.wordRAMStore.readWord? segment index)
    (best? : Option (Nat × Nat)) :
    summaryRangeScanFromTraceResultAtSegmentsWithStore
        table segments store block steps best? =
      summaryRangeScanFromTraceResultAtSegments
        table segments block steps best? := by
  induction steps generalizing block best? with
  | zero =>
      simp [summaryRangeScanFromTraceResultAtSegmentsWithStore,
        summaryRangeScanFromTraceResultAtSegments]
  | succ steps ih =>
      simp [summaryRangeScanFromTraceResultAtSegmentsWithStore,
        summaryRangeScanFromTraceResultAtSegments,
        minCandidateTraceResultAtSegmentsWithStore_eq_of_agree
          table segments hbaseline hminRel hmaxRel hargOffset block,
        ih]

theorem summaryRangeScanTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {store : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          table.argOffsetTable.wordRAMStore.readWord? segment index) :
    summaryRangeScanTraceResultAtSegmentsWithStore
        table segments store startBlock count =
      summaryRangeScanTraceResultAtSegments
        table segments startBlock count := by
  cases count with
  | zero =>
      simp [summaryRangeScanTraceResultAtSegmentsWithStore,
        summaryRangeScanTraceResultAtSegments]
  | succ steps =>
      simp [summaryRangeScanTraceResultAtSegmentsWithStore,
        summaryRangeScanTraceResultAtSegments,
        minCandidateTraceResultAtSegmentsWithStore_eq_of_agree
          table segments hbaseline hminRel hmaxRel hargOffset startBlock,
        summaryRangeScanFromTraceResultAtSegmentsWithStore_eq_of_agree
          table segments hbaseline hminRel hmaxRel hargOffset]

theorem boundedSummaryRangeScanTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {store : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          table.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          table.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          table.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          table.argOffsetTable.wordRAMStore.readWord? segment index) :
    boundedSummaryRangeScanTraceResultAtSegmentsWithStore
        table segments store startBlock count =
      boundedSummaryRangeScanTraceResultAtSegments
        table segments startBlock count := by
  unfold boundedSummaryRangeScanTraceResultAtSegmentsWithStore
  unfold boundedSummaryRangeScanTraceResultAtSegments
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound,
      summaryRangeScanTraceResultAtSegmentsWithStore_eq_of_agree
        table segments hbaseline hminRel hmaxRel hargOffset]
  · simp [hbound]

theorem summaryRangeScanFromTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index)
    (best? : Option (Nat × Nat)) :
    summaryRangeScanFromTraceResultAtSegmentsWithStore
        table segments storeA block steps best? =
      summaryRangeScanFromTraceResultAtSegmentsWithStore
        table segments storeB block steps best? := by
  induction steps generalizing block best? with
  | zero =>
      simp [summaryRangeScanFromTraceResultAtSegmentsWithStore]
  | succ steps ih =>
      simp [summaryRangeScanFromTraceResultAtSegmentsWithStore,
        minCandidateTraceResultAtSegmentsWithStore_store_parametric
          table segments hbaseline hminRel hmaxRel hargOffset block,
        ih]

theorem summaryRangeScanTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index) :
    summaryRangeScanTraceResultAtSegmentsWithStore
        table segments storeA startBlock count =
      summaryRangeScanTraceResultAtSegmentsWithStore
        table segments storeB startBlock count := by
  cases count with
  | zero =>
      simp [summaryRangeScanTraceResultAtSegmentsWithStore]
  | succ steps =>
      simp [summaryRangeScanTraceResultAtSegmentsWithStore,
        minCandidateTraceResultAtSegmentsWithStore_store_parametric
          table segments hbaseline hminRel hmaxRel hargOffset startBlock,
        summaryRangeScanFromTraceResultAtSegmentsWithStore_store_parametric
          table segments hbaseline hminRel hmaxRel hargOffset]

theorem boundedSummaryRangeScanTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.baseline segments.deadSegment segment) index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.minRel segments.deadSegment segment) index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.maxRel segments.deadSegment segment) index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.argOffset segments.deadSegment segment) index) :
    boundedSummaryRangeScanTraceResultAtSegmentsWithStore
        table segments storeA startBlock count =
      boundedSummaryRangeScanTraceResultAtSegmentsWithStore
        table segments storeB startBlock count := by
  unfold boundedSummaryRangeScanTraceResultAtSegmentsWithStore
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound,
      summaryRangeScanTraceResultAtSegmentsWithStore_store_parametric
        table segments hbaseline hminRel hmaxRel hargOffset]
  · simp [hbound]

theorem summaryRangeScanFromTraceResultAtSegmentsWithStore_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (best? : Option (Nat × Nat))
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (minCandidateTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        P event) :
    forall event,
      List.Mem event
          (summaryRangeScanFromTraceResultAtSegmentsWithStore
            table segments store block steps best?).trace -> P event := by
  induction steps generalizing block best? with
  | zero =>
      simp [summaryRangeScanFromTraceResultAtSegmentsWithStore]
      exact WordRAM.TraceResult.pure_trace_forall P best?
  | succ steps ih =>
      unfold summaryRangeScanFromTraceResultAtSegmentsWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact hsummary block
      · exact ih (block := block + 1)
          (best? :=
            bpCandidateMerge? best?
              (minCandidateTraceResultAtSegmentsWithStore
                table segments store block).value)

theorem summaryRangeScanTraceResultAtSegmentsWithStore_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (minCandidateTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        P event) :
    forall event,
      List.Mem event
          (summaryRangeScanTraceResultAtSegmentsWithStore
            table segments store startBlock count).trace -> P event := by
  cases count with
  | zero =>
      simp [summaryRangeScanTraceResultAtSegmentsWithStore]
      exact WordRAM.TraceResult.pure_trace_forall P
        (none : Option (Nat × Nat))
  | succ steps =>
      unfold summaryRangeScanTraceResultAtSegmentsWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact hsummary startBlock
      · exact
          summaryRangeScanFromTraceResultAtSegmentsWithStore_trace_forall
            table segments store
            (minCandidateTraceResultAtSegmentsWithStore
              table segments store startBlock).value P hsummary

theorem boundedSummaryRangeScanTraceResultAtSegmentsWithStore_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall block event,
        List.Mem event
          (minCandidateTraceResultAtSegmentsWithStore
            table segments store block).trace ->
        P event) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegmentsWithStore
            table segments store startBlock count).trace -> P event := by
  unfold boundedSummaryRangeScanTraceResultAtSegmentsWithStore
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    exact
      summaryRangeScanTraceResultAtSegmentsWithStore_trace_forall
        table segments store P hsummary
  · simp [hbound]
    exact WordRAM.TraceResult.pure_trace_forall P
      (none : Option (Nat × Nat))

theorem boundedSummaryRangeScanTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegmentsWithStore
            table segments store startBlock count).trace ->
        event.matchesReadStore store := by
  exact
    boundedSummaryRangeScanTraceResultAtSegmentsWithStore_trace_forall
      table segments store (fun event => event.matchesReadStore store)
      (fun block event hmem =>
        minCandidateTraceResultAtSegmentsWithStore_matchesReadStore
          table segments store block event hmem)

theorem boundedSummaryRangeScanTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore) :
    forall event,
      List.Mem event
          (boundedSummaryRangeScanTraceResultAtSegmentsWithStore
            table segments store startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    boundedSummaryRangeScanTraceResultAtSegmentsWithStore_trace_forall
      table segments store
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (fun block event hmem =>
        minCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          table segments store block event hmem)

/-- Store-parameterized local sparse-offset read at a relabeled segment. -/
def bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) : WordRAM.TraceResult (Option Nat) :=
  fixedWidthNatTableReadTraceResultAtSegmentWithStore
    offsetTable.table segmentBase deadSegment store
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat) {store : WordRAM.ReadStore}
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          offsetTable.table.wordRAMStore.readWord? segment index)
    (macroIdx localStart level : Nat) :
    bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segmentBase deadSegment store macroIdx localStart level =
      offsetTable.readOffsetTraceResultAtSegment
        segmentBase deadSegment macroIdx localStart level := by
  unfold bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
  unfold PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      offsetTable.table segmentBase deadSegment hread
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index)
    (macroIdx localStart level : Nat) :
    bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segmentBase deadSegment storeA macroIdx localStart level =
      bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segmentBase deadSegment storeB macroIdx localStart
        level := by
  unfold bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      offsetTable.table segmentBase deadSegment hread
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) :
    forall event,
      event ∈
          (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
            offsetTable segmentBase deadSegment store macroIdx localStart
            level).trace ->
        event.matchesReadStore store := by
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
      offsetTable.table segmentBase deadSegment store
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) :
    forall event,
      event ∈
          (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
            offsetTable segmentBase deadSegment store macroIdx localStart
            level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
      offsetTable.table segmentBase deadSegment store
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

/-- Store-parameterized local sparse span candidate. -/
def bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
      offsetTable segments.localOffset segments.deadSegment store
      macroIdx localStart level)
    fun offset? =>
      match offset? with
      | some offset =>
          minCandidateTraceResultAtSegmentsWithStore
            summary segments.summary store (macroIdx * macroSize + offset)
      | none => WordRAM.TraceResult.pure none

theorem bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          offsetTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroIdx localStart level : Nat) :
    bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments store macroIdx localStart level =
      offsetTable.spanCandidateTraceResultAtSegments
        summary segments macroIdx localStart level := by
  unfold bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments
  simp only [
    bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_eq_of_agree
      offsetTable segments.localOffset segments.deadSegment hlocal
      macroIdx localStart level]
  cases hoff :
      (offsetTable.readOffsetTraceResultAtSegment segments.localOffset
        segments.deadSegment macroIdx localStart level).value with
  | none => simp [WordRAM.TraceResult.bind, hoff]
  | some offset =>
      simp [WordRAM.TraceResult.bind, hoff,
        minCandidateTraceResultAtSegmentsWithStore_eq_of_agree
          summary segments.summary hbaseline hminRel hmaxRel hargOffset
          (macroIdx * macroSize + offset)]

theorem bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroIdx localStart level : Nat) :
    bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments storeA macroIdx localStart level =
      bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments storeB macroIdx localStart level := by
  unfold bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_store_parametric
      offsetTable segments.localOffset segments.deadSegment hlocal
      macroIdx localStart level]
  cases hoff :
      (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segments.localOffset segments.deadSegment storeB
        macroIdx localStart level).value with
  | none => simp [WordRAM.TraceResult.bind, hoff]
  | some offset =>
      simp [WordRAM.TraceResult.bind, hoff,
        minCandidateTraceResultAtSegmentsWithStore_store_parametric
          summary segments.summary hbaseline hminRel hmaxRel hargOffset
          (macroIdx * macroSize + offset)]

theorem bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) :
    forall event,
      event ∈
          (bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
            offsetTable summary segments store macroIdx localStart
            level).trace ->
        event.matchesReadStore store := by
  unfold bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_matchesReadStore
        offsetTable segments.localOffset segments.deadSegment store
        macroIdx localStart level
  · cases hoff :
      (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segments.localOffset segments.deadSegment store
        macroIdx localStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall
          (fun event => event.matchesReadStore store)
          (none : Option (Nat × Nat))
    | some offset =>
        exact
          minCandidateTraceResultAtSegmentsWithStore_matchesReadStore
            summary segments.summary store
            (macroIdx * macroSize + offset)

theorem bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart level : Nat) :
    forall event,
      event ∈
          (bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
            offsetTable summary segments store macroIdx localStart
            level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseOffsetReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        offsetTable segments.localOffset segments.deadSegment store
        macroIdx localStart level
  · cases hoff :
      (bpLocalSparseOffsetReadTraceResultAtSegmentWithStore
        offsetTable segments.localOffset segments.deadSegment store
        macroIdx localStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall
          (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
          (none : Option (Nat × Nat))
    | some offset =>
        exact
          minCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
            summary segments.summary store
            (macroIdx * macroSize + offset)

/-- Store-parameterized local two-span candidate. -/
def bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart count : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  let rightLocalStart := localStart + count - span
  WordRAM.TraceResult.bind
    (bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
      offsetTable summary segments store macroIdx localStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore
          offsetTable summary segments store macroIdx rightLocalStart level)

theorem bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          offsetTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroIdx localStart count : Nat) :
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments store macroIdx localStart count =
      offsetTable.twoSpanCandidateTraceResultAtSegments
        summary segments macroIdx localStart count := by
  unfold bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments
  simp only [
    bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      offsetTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroIdx localStart count : Nat) :
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments storeA macroIdx localStart count =
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        offsetTable summary segments storeB macroIdx localStart count := by
  unfold bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      offsetTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart count : Nat) :
    forall event,
      event ∈
          (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
            offsetTable summary segments store macroIdx localStart
            count).trace ->
        event.matchesReadStore store := by
  unfold bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        offsetTable summary segments store macroIdx localStart (Nat.log2 count)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        offsetTable summary segments store macroIdx
        (localStart + count - bpSparseLogSpan count) (Nat.log2 count)

theorem bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroIdx localStart count : Nat) :
    forall event,
      event ∈
          (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
            offsetTable summary segments store macroIdx localStart
            count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        offsetTable summary segments store macroIdx localStart (Nat.log2 count)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpLocalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        offsetTable summary segments store macroIdx
        (localStart + count - bpSparseLogSpan count) (Nat.log2 count)

/-- Store-parameterized global sparse-block read at a relabeled segment. -/
def bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroStart level : Nat) : WordRAM.TraceResult (Option Nat) :=
  fixedWidthNatTableReadTraceResultAtSegmentWithStore
    globalTable.table segmentBase deadSegment store
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat) {store : WordRAM.ReadStore}
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (macroStart level : Nat) :
    bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segmentBase deadSegment store macroStart level =
      globalTable.readBlockTraceResultAtSegment
        segmentBase deadSegment macroStart level := by
  unfold bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
  unfold PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_eq_of_agree
      globalTable.table segmentBase deadSegment hread
      (bpGlobalSparseCellSlot macroCount macroStart level)

theorem bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index)
    (macroStart level : Nat) :
    bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segmentBase deadSegment storeA macroStart level =
      bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segmentBase deadSegment storeB macroStart level := by
  unfold bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_store_parametric
      globalTable.table segmentBase deadSegment hread
      (bpGlobalSparseCellSlot macroCount macroStart level)

theorem bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroStart level : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
            globalTable segmentBase deadSegment store macroStart
            level).trace ->
        event.matchesReadStore store := by
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_matchesReadStore
      globalTable.table segmentBase deadSegment store
      (bpGlobalSparseCellSlot macroCount macroStart level)

theorem bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (macroStart level : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
            globalTable segmentBase deadSegment store macroStart
            level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    fixedWidthNatTableReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
      globalTable.table segmentBase deadSegment store
      (bpGlobalSparseCellSlot macroCount macroStart level)
/-- Store-parameterized global sparse span candidate. -/
def bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart level : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
      globalTable segments.globalBlock segments.deadSegment store
      macroStart level)
    fun block? =>
      match block? with
      | some block =>
          minCandidateTraceResultAtSegmentsWithStore
            summary segments.summary store block
      | none => WordRAM.TraceResult.pure none

theorem bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart level : Nat) :
    bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments store macroStart level =
      globalTable.spanCandidateTraceResultAtSegments
        summary segments macroStart level := by
  unfold bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments
  simp only [
    bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_eq_of_agree
      globalTable segments.globalBlock segments.deadSegment hglobal
      macroStart level]
  cases hblock :
      (globalTable.readBlockTraceResultAtSegment segments.globalBlock
        segments.deadSegment macroStart level).value with
  | none => simp [WordRAM.TraceResult.bind, hblock]
  | some block =>
      simp [WordRAM.TraceResult.bind, hblock,
        minCandidateTraceResultAtSegmentsWithStore_eq_of_agree
          summary segments.summary hbaseline hminRel hmaxRel hargOffset
          block]

theorem bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroStart level : Nat) :
    bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments storeA macroStart level =
      bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments storeB macroStart level := by
  unfold bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_store_parametric
      globalTable segments.globalBlock segments.deadSegment hglobal
      macroStart level]
  cases hblock :
      (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segments.globalBlock segments.deadSegment storeB
        macroStart level).value with
  | none => simp [WordRAM.TraceResult.bind, hblock]
  | some block =>
      simp [WordRAM.TraceResult.bind, hblock,
        minCandidateTraceResultAtSegmentsWithStore_store_parametric
          summary segments.summary hbaseline hminRel hmaxRel hargOffset
          block]

theorem bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart level : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
            globalTable summary segments store macroStart level).trace ->
        event.matchesReadStore store := by
  unfold bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_matchesReadStore
        globalTable segments.globalBlock segments.deadSegment store
        macroStart level
  · cases hblock :
      (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segments.globalBlock segments.deadSegment store
        macroStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall
          (fun event => event.matchesReadStore store)
          (none : Option (Nat × Nat))
    | some block =>
        exact
          minCandidateTraceResultAtSegmentsWithStore_matchesReadStore
            summary segments.summary store block

theorem bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart level : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
            globalTable summary segments store macroStart level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpGlobalSparseBlockReadTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        globalTable segments.globalBlock segments.deadSegment store
        macroStart level
  · cases hblock :
      (bpGlobalSparseBlockReadTraceResultAtSegmentWithStore
        globalTable segments.globalBlock segments.deadSegment store
        macroStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall
          (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
          (none : Option (Nat × Nat))
    | some block =>
        exact
          minCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
            summary segments.summary store block

/-- Store-parameterized global two-span candidate. -/
def bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart macroSpanCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  WordRAM.TraceResult.bind
    (bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
      globalTable summary segments store macroStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore
          globalTable summary segments store rightMacroStart level)

theorem bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart macroSpanCount : Nat) :
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments store macroStart macroSpanCount =
      globalTable.twoSpanCandidateTraceResultAtSegments
        summary segments macroStart macroSpanCount := by
  unfold bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  unfold PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments
  simp only [
    bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroStart macroSpanCount : Nat) :
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments storeA macroStart macroSpanCount =
      bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
        globalTable summary segments storeB macroStart macroSpanCount := by
  unfold bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart macroSpanCount : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
            globalTable summary segments store macroStart
            macroSpanCount).trace ->
        event.matchesReadStore store := by
  unfold bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        globalTable summary segments store macroStart
        (Nat.log2 macroSpanCount)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        globalTable summary segments store
        (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
        (Nat.log2 macroSpanCount)

theorem bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart macroSpanCount : Nat) :
    forall event,
      event ∈
          (bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
            globalTable summary segments store macroStart
            macroSpanCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        globalTable summary segments store macroStart
        (Nat.log2 macroSpanCount)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpGlobalSparseSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        globalTable summary segments store
        (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
        (Nat.log2 macroSpanCount)

/-- Store-parameterized adjacent-macro two-level interior candidate case. -/
def bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
      localTable summary segments store macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
          localTable summary segments store (macroStart + 1) 0 rightCount)

/-- Store-parameterized left-plus-middle two-level interior candidate case. -/
def bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
      localTable summary segments store macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun middle? => bpCandidateMerge? left? middle?)
        (bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
          globalTable summary segments store (macroStart + 1)
          middleMacroCount)

/-- Store-parameterized left-middle-right two-level interior candidate case. -/
def bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  WordRAM.TraceResult.bind
    (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
      localTable summary segments store macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.bind
        (bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
          globalTable summary segments store (macroStart + 1)
          middleMacroCount)
        fun middle? =>
          WordRAM.TraceResult.map
            (fun right? => bpCandidateMerge3? left? middle? right?)
            (bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
              localTable summary segments store rightMacroStart 0 rightCount)

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          localTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart localStart rightCount : Nat) :
    bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
        localTable summary segments store macroStart localStart rightCount =
      bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
        localTable summary segments macroStart localStart rightCount := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          localTable.table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart localStart middleMacroCount : Nat) :
    bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments store macroStart localStart
        middleMacroCount =
      bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
        localTable globalTable summary segments macroStart localStart
        middleMacroCount := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset,
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          localTable.table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments store macroStart localStart
        middleMacroCount rightCount =
      bpTwoLevelCrossMacroCandidateTraceResultAtSegments
        localTable globalTable summary segments macroStart localStart
        middleMacroCount rightCount := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegments
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset,
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroStart localStart rightCount : Nat) :
    bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
        localTable summary segments storeA macroStart localStart rightCount =
      bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
        localTable summary segments storeB macroStart localStart
        rightCount := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroStart localStart middleMacroCount : Nat) :
    bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeA macroStart localStart
        middleMacroCount =
      bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeB macroStart localStart
        middleMacroCount := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset,
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeA macroStart localStart
        middleMacroCount rightCount =
      bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeB macroStart localStart
        middleMacroCount rightCount := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
  simp only [
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      localTable summary segments hlocal hbaseline hminRel hmaxRel
      hargOffset,
    bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
      globalTable summary segments hglobal hbaseline hminRel hmaxRel
      hargOffset]

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart rightCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
            localTable summary segments store macroStart localStart
            rightCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        localTable summary segments store (macroStart + 1) 0 rightCount

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart rightCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
            localTable summary segments store macroStart localStart
            rightCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        localTable summary segments store (macroStart + 1) 0 rightCount

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store macroStart
            localStart middleMacroCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        globalTable summary segments store (macroStart + 1)
        middleMacroCount

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store macroStart
            localStart middleMacroCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        globalTable summary segments store (macroStart + 1)
        middleMacroCount

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store macroStart
            localStart middleMacroCount rightCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
          globalTable summary segments store (macroStart + 1)
          middleMacroCount
    · apply WordRAM.TraceResult.map_trace_forall
      exact
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
          localTable summary segments store
          (macroStart + 1 + middleMacroCount) 0 rightCount

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    forall event,
      event ∈
          (bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store macroStart
            localStart middleMacroCount rightCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
        localTable summary segments store macroStart localStart
        (macroSize - localStart)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        bpGlobalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          globalTable summary segments store (macroStart + 1)
          middleMacroCount
    · apply WordRAM.TraceResult.map_trace_forall
      exact
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          localTable summary segments store
          (macroStart + 1 + middleMacroCount) 0 rightCount

/-- Store-parameterized two-level interior candidate. -/
def bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    WordRAM.TraceResult.pure none
  else if count <= macroSize - localStart then
    bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore
      localTable summary segments store macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore
        localTable summary segments store macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments store macroStart localStart
        middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments store macroStart localStart
        middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          localTable.table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          summary.baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          summary.minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          summary.maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments store startBlock count =
      bpTwoLevelInteriorCandidateTraceResultAtSegments
        localTable globalTable summary segments startBlock count := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegments
  by_cases hcount : count = 0
  · simp [hcount]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin,
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_eq_of_agree
          localTable summary segments hlocal hbaseline hminRel hmaxRel
          hargOffset]
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle,
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
            localTable summary segments hlocal hbaseline hminRel hmaxRel
            hargOffset]
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp [hright,
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
              localTable globalTable summary segments hlocal hglobal hbaseline
              hminRel hmaxRel hargOffset]
        · simp [hright,
            bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_eq_of_agree
              localTable globalTable summary segments hlocal hglobal hbaseline
              hminRel hmaxRel hargOffset]

theorem bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_store_parametric
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (startBlock count : Nat) :
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeA startBlock count =
      bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
        localTable globalTable summary segments storeB startBlock count := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
  by_cases hcount : count = 0
  · simp [hcount]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin,
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_store_parametric
          localTable summary segments hlocal hbaseline hminRel hmaxRel
          hargOffset]
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle,
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
            localTable summary segments hlocal hbaseline hminRel hmaxRel
            hargOffset]
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp [hright,
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
              localTable globalTable summary segments hlocal hglobal hbaseline
              hminRel hmaxRel hargOffset]
        · simp [hright,
            bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_store_parametric
              localTable globalTable summary segments hlocal hglobal hbaseline
              hminRel hmaxRel hargOffset]

theorem bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store startBlock
            count).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
  by_cases hcount : count = 0
  · simp [hcount]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      exact
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_matchesReadStore
          localTable summary segments store (startBlock / macroSize)
          (startBlock % macroSize) count
    · simp [hwithin]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        exact
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
            localTable summary segments store (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0
        · simp [hright]
          exact
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
              localTable globalTable summary segments store
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
        · simp [hright]
          exact
            bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_matchesReadStore
              localTable globalTable summary segments store
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) % macroSize)

theorem bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
            localTable globalTable summary segments store startBlock
            count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
  by_cases hcount : count = 0
  · simp [hcount]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      exact
        bpLocalSparseTwoSpanCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          localTable summary segments store (startBlock / macroSize)
          (startBlock % macroSize) count
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        exact
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
            localTable summary segments store (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0
        · simp [hright]
          exact
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
              localTable globalTable summary segments store
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
        · simp [hright]
          exact
            bpTwoLevelCrossMacroCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
              localTable globalTable summary segments store
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) % macroSize)

/--
Ready two-level relative-rmM interior replay whose table reads come from a
caller-supplied global read store.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
    (shape : Cartesian.CartesianShape)
    (_hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let summary := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore
    localTable globalTable summary segments store startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
        shape hready segments store startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
        shape hready segments startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_eq_of_agree
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments hlocal hglobal hbaseline hminRel hmaxRel hargOffset
      startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
      shape hready segments store startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  rw [
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_eq_of_agree
      shape hready segments hlocal hglobal hbaseline hminRel hmaxRel
      hargOffset startBlock count]
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReady_refines
      shape hready segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
        shape hready segments storeA startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
        shape hready segments storeB startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_store_parametric
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments hlocal hglobal hbaseline hminRel hmaxRel hargOffset
      startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
            shape hready segments store startBlock count).trace ->
        event.matchesReadStore store := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_matchesReadStore
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments store startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (hready : concreteBPRelativeRmmInteriorReady shape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
            shape hready segments store startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
  exact
    bpTwoLevelInteriorCandidateTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
      (concreteBPRelativeRmmInteriorLocalTable shape)
      (concreteBPRelativeRmmInteriorGlobalTable shape)
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments store startBlock count

/--
All-size structural interior replay whose table reads come from a supplied
global read store.
-/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStoreLegacy
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  if hready : concreteBPRelativeRmmInteriorReady shape then
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore
      shape hready segments store startBlock count
  else if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    boundedSummaryRangeScanTraceResultAtSegmentsWithStore
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      segments.summary store startBlock count
  else
    WordRAM.TraceResult.pure none
/-- Canonical supplied-store execution on the one component segment. -/
def concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Prod Nat Nat)) :=
  flatStoreExecutionTraceResultAtSegment segments.canonicalComponent
    ((canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count).run
      (flatWordStoreOfReadStore store segments.canonicalComponent))

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments store startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape segments startBlock count := by
  have hstore :
      flatWordStoreOfReadStore store segments.canonicalComponent =
        SuccinctSpace.FlatWordStore.ofArray
          (canonicalRelativeRmmInteriorComponentStore shape).store.words := by
    funext address
    exact hcomponent address
  simp [concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore,
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural,
    canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment,
    canonicalRelativeRmmInteriorRangeMinExecutionWithStore,
    canonicalRelativeRmmInteriorRangeMinExecutionWithRead, hstore]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
      shape segments store startBlock count).toCosted =
      (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  rw [concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
    shape segments hcomponent startBlock count]
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines
      shape segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hcomponent :
      forall address,
        storeA.readWord? segments.canonicalComponent address =
          storeB.readWord? segments.canonicalComponent address)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments storeA startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments storeB startBlock count := by
  have hstore :
      flatWordStoreOfReadStore storeA segments.canonicalComponent =
        flatWordStoreOfReadStore storeB segments.canonicalComponent := by
    funext address
    exact hcomponent address
  simp [concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore,
    hstore]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace ->
        event.matchesReadStore store := by
  exact
    flatStoreComputationTraceResultAtSegment_matchesReadStore
      (canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count)
      store segments.canonicalComponent

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  exact
    flatStoreExecutionTraceResultAtSegment_no_syntheticCostOnlyPrimitive
      segments.canonicalComponent
      ((canonicalRelativeRmmInteriorRangeMinComputation
        shape startBlock count).run
          (flatWordStoreOfReadStore store segments.canonicalComponent))

/-
Legacy Ready/Active/inactive proof archive. The executable legacy definition
above remains only for compatibility and is not used by the canonical route.


theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments store startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape segments startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_eq_of_agree
        shape hready segments hlocal hglobal hbaseline hminRel hmaxRel
        hargOffset startBlock count]
  · by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive,
        boundedSummaryRangeScanTraceResultAtSegmentsWithStore_eq_of_agree
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary hbaseline hminRel hmaxRel hargOffset]
    · simp [hready, hactive]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (startBlock count : Nat) :
    (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
      shape segments store startBlock count).toCosted =
      (concreteBPRelativeRmmInteriorDirectory shape).rangeMinCosted
        startBlock count := by
  rw [
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
      shape segments hlocal hglobal hbaseline hminRel hmaxRel hargOffset
      startBlock count]
  exact
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines
      shape segments startBlock count

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments storeA startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments storeB startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_store_parametric
        shape hready segments hlocal hglobal hbaseline hminRel hmaxRel
        hargOffset startBlock count]
  · by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive,
        boundedSummaryRangeScanTraceResultAtSegmentsWithStore_store_parametric
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary hbaseline hminRel hmaxRel hargOffset]
    · simp [hready, hactive]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace ->
        event.matchesReadStore store := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready]
    exact
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_matchesReadStore
        shape hready segments store startBlock count
  · by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive]
      exact
        boundedSummaryRangeScanTraceResultAtSegmentsWithStore_matchesReadStore
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary store
    · simp [hready, hactive]

theorem concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (startBlock count : Nat) :
    forall event,
      event ∈
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  by_cases hready : concreteBPRelativeRmmInteriorReady shape
  · simp [hready]
    exact
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsOfReadyWithStore_no_syntheticCostOnlyPrimitive
        shape hready segments store startBlock count
  · by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
    · simp [hready, hactive]
      exact
        boundedSummaryRangeScanTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
          segments.summary store
    · simp [hready, hactive]
-/

/-- Store-parameterized BP-code payload word read at global segment `0`. -/
def bpCodeWordReadTraceResultWithStore
    (store : WordRAM.ReadStore) (index : Nat) :
    WordRAM.TraceResult (List (List Bool)) where
  value := readStorePayloadWordValue store 0 index
  trace := [WordRAM.TraceEvent.readWord 0 index (store.readWord? 0 index)]

theorem bpCodeWordReadTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (index : Nat) :
    bpCodeWordReadTraceResultWithStore store index =
      bpCodeWordReadTraceResult shape index := by
  cases harr :
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? <;>
    simp [bpCodeWordReadTraceResultWithStore, bpCodeWordReadTraceResult,
      bpCodeReadWordTraceEvent, readStorePayloadWordValue,
      payloadWordReadOfGet?, hbpCode index, harr]

theorem bpCodeWordReadTraceResultWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (index : Nat) :
    bpCodeWordReadTraceResultWithStore storeA index =
      bpCodeWordReadTraceResultWithStore storeB index := by
  unfold bpCodeWordReadTraceResultWithStore readStorePayloadWordValue
  rw [hread index]

theorem bpCodeWordReadTraceResultWithStore_matchesReadStore
    (store : WordRAM.ReadStore) (index : Nat) :
    forall event,
      event ∈ (bpCodeWordReadTraceResultWithStore store index).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp [bpCodeWordReadTraceResultWithStore] at hmem
  subst event
  rfl

theorem bpCodeWordReadTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (index : Nat) :
    forall event,
      event ∈ (bpCodeWordReadTraceResultWithStore store index).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simp [bpCodeWordReadTraceResultWithStore] at hmem
  subst event
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

/-- Store-parameterized four-word local BP block read. -/
def localBPBlockWordsTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) : WordRAM.TraceResult (List (List Bool)) :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  WordRAM.TraceResult.bind (bpCodeWordReadTraceResultWithStore store firstWord)
    fun w0 =>
      WordRAM.TraceResult.bind
        (bpCodeWordReadTraceResultWithStore store (firstWord + 1))
        fun w1 =>
          WordRAM.TraceResult.bind
            (bpCodeWordReadTraceResultWithStore store (firstWord + 2))
            fun w2 =>
              WordRAM.TraceResult.map
                (fun w3 => w0 ++ w1 ++ w2 ++ w3)
                (bpCodeWordReadTraceResultWithStore store (firstWord + 3))

theorem localBPBlockWordsTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore shape store blockSize close =
      localBPBlockWordsTraceResult shape blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore localBPBlockWordsTraceResult
  simp only [bpCodeWordReadTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPBlockWordsTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore shape storeA blockSize close =
      localBPBlockWordsTraceResultWithStore shape storeB blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore
  simp only [bpCodeWordReadTraceResultWithStore_store_parametric hread]

theorem localBPBlockWordsTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPBlockWordsTraceResultWithStore
            shape store blockSize close).trace ->
        event.matchesReadStore store := by
  unfold localBPBlockWordsTraceResultWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _
      · apply WordRAM.TraceResult.map_trace_forall
        exact bpCodeWordReadTraceResultWithStore_matchesReadStore store _

theorem localBPBlockWordsTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPBlockWordsTraceResultWithStore
            shape store blockSize close).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPBlockWordsTraceResultWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact bpCodeWordReadTraceResultWithStore_no_syntheticCostOnlyPrimitive store _
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact bpCodeWordReadTraceResultWithStore_no_syntheticCostOnlyPrimitive store _
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact bpCodeWordReadTraceResultWithStore_no_syntheticCostOnlyPrimitive store _
      · apply WordRAM.TraceResult.map_trace_forall
        exact bpCodeWordReadTraceResultWithStore_no_syntheticCostOnlyPrimitive store _

/-- Store-parameterized local BP window bits. -/
def localBPWindowBitsTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) : WordRAM.TraceResult (List Bool) :=
  WordRAM.TraceResult.map SuccinctSpace.flattenPayloadWords
    (localBPBlockWordsTraceResultWithStore shape store blockSize close)

theorem localBPWindowBitsTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore shape store blockSize close =
      localBPWindowBitsTraceResult shape blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore localBPWindowBitsTraceResult
  rw [localBPBlockWordsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPWindowBitsTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore shape storeA blockSize close =
      localBPWindowBitsTraceResultWithStore shape storeB blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore
  rw [localBPBlockWordsTraceResultWithStore_store_parametric shape hread]

theorem localBPWindowBitsTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize close).trace ->
        event.matchesReadStore store := by
  unfold localBPWindowBitsTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPBlockWordsTraceResultWithStore_matchesReadStore
      shape store blockSize close

theorem localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize close : Nat) :
    forall event,
      event ∈
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize close).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPWindowBitsTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPBlockWordsTraceResultWithStore_no_syntheticCostOnlyPrimitive
      shape store blockSize close

/-- Store-parameterized seeded same-block local BP decoder. -/
def localBPSameBlockCloseSeededTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose seed : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  WordRAM.TraceResult.map
    (fun window =>
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed base start count,
            localBPSeededPrefixRangeArgMinPrefixPos window seed base
              start count)))
    (localBPWindowBitsTraceResultWithStore shape store blockSize leftClose)

theorem localBPSameBlockCloseSeededTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize leftClose rightClose seed : Nat) :
    localBPSameBlockCloseSeededTraceResultWithStore
        shape store blockSize leftClose rightClose seed =
      localBPSameBlockCloseSeededTraceResult
        shape blockSize leftClose rightClose seed := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
    localBPSameBlockCloseSeededTraceResult
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPSameBlockCloseSeededTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize leftClose rightClose seed : Nat) :
    localBPSameBlockCloseSeededTraceResultWithStore
        shape storeA blockSize leftClose rightClose seed =
      localBPSameBlockCloseSeededTraceResultWithStore
        shape storeB blockSize leftClose rightClose seed := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hread]

theorem localBPSameBlockCloseSeededTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose seed : Nat) :
    forall event,
      event ∈
          (localBPSameBlockCloseSeededTraceResultWithStore
            shape store blockSize leftClose rightClose seed).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPWindowBitsTraceResultWithStore_matchesReadStore
      shape store blockSize leftClose

theorem localBPSameBlockCloseSeededTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose seed : Nat) :
    forall event,
      event ∈
          (localBPSameBlockCloseSeededTraceResultWithStore
            shape store blockSize leftClose rightClose seed).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPSameBlockCloseSeededTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
      shape store blockSize leftClose

/-- Store-parameterized same-block close decoder with an abstract rank seed. -/
def localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededTraceResultWithStore
        shape store blockSize leftClose rightClose seed

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape}
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace store blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithRankSeed
        shape rankCloseTrace blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
    localBPSameBlockCloseDecodedTraceResultWithRankSeed
  simp only [localBPSameBlockCloseSeededTraceResultWithStore_eq_of_agree
    hbpCode]

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace storeA blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape rankCloseTrace storeB blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  simp only [localBPSameBlockCloseSeededTraceResultWithStore_store_parametric
    shape hread]

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      event ∈
          (localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
            shape rankCloseTrace store blockSize leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose
        (fun event => event.matchesReadStore store) hrank
  · exact
      localBPSameBlockCloseSeededTraceResultWithStore_matchesReadStore
        shape store blockSize leftClose rightClose _

theorem localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) :
    forall event,
      event ∈
          (localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
            shape rankCloseTrace store blockSize leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose
        (fun event => ¬ event.isSyntheticCostOnlyPrimitive) hrank
  · exact
      localBPSameBlockCloseSeededTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize leftClose rightClose _

/-- Store-parameterized seeded left endpoint-fringe decoder. -/
def localBPLeftFringeCandidateSeededTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize leftClose
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base
          (leftClose + 1) count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            (leftClose + 1) count))
    (localBPWindowBitsTraceResultWithStore shape store blockSize leftClose)

theorem localBPLeftFringeCandidateSeededTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize leftClose seed : Nat) :
    localBPLeftFringeCandidateSeededTraceResultWithStore
        shape store blockSize leftClose seed =
      localBPLeftFringeCandidateSeededTraceResult
        shape blockSize leftClose seed := by
  unfold localBPLeftFringeCandidateSeededTraceResultWithStore
    localBPLeftFringeCandidateSeededTraceResult
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPLeftFringeCandidateSeededTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize leftClose seed : Nat) :
    localBPLeftFringeCandidateSeededTraceResultWithStore
        shape storeA blockSize leftClose seed =
      localBPLeftFringeCandidateSeededTraceResultWithStore
        shape storeB blockSize leftClose seed := by
  unfold localBPLeftFringeCandidateSeededTraceResultWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hread]

theorem localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize leftClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPLeftFringeCandidateSeededTraceResultWithStore
            shape store blockSize leftClose seed).trace ->
        P event := by
  unfold localBPLeftFringeCandidateSeededTraceResultWithStore
  exact WordRAM.TraceResult.map_trace_forall P _ _ hbp

theorem localBPLeftFringeCandidateSeededTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose seed : Nat) :
    forall event,
      event ∈
          (localBPLeftFringeCandidateSeededTraceResultWithStore
            shape store blockSize leftClose seed).trace ->
        event.matchesReadStore store := by
  exact
    localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
      shape store blockSize leftClose seed
      (fun event => event.matchesReadStore store)
      (localBPWindowBitsTraceResultWithStore_matchesReadStore
        shape store blockSize leftClose)

theorem localBPLeftFringeCandidateSeededTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose seed : Nat) :
    forall event,
      event ∈
          (localBPLeftFringeCandidateSeededTraceResultWithStore
            shape store blockSize leftClose seed).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
      shape store blockSize leftClose seed
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize leftClose)

/-- Store-parameterized seeded right endpoint-fringe decoder. -/
def localBPRightFringeCandidateSeededTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize rightClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  WordRAM.TraceResult.map
    (fun window =>
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base start count))
    (localBPWindowBitsTraceResultWithStore shape store blockSize rightClose)

theorem localBPRightFringeCandidateSeededTraceResultWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize rightClose seed : Nat) :
    localBPRightFringeCandidateSeededTraceResultWithStore
        shape store blockSize rightClose seed =
      localBPRightFringeCandidateSeededTraceResult
        shape blockSize rightClose seed := by
  unfold localBPRightFringeCandidateSeededTraceResultWithStore
    localBPRightFringeCandidateSeededTraceResult
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]

theorem localBPRightFringeCandidateSeededTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (blockSize rightClose seed : Nat) :
    localBPRightFringeCandidateSeededTraceResultWithStore
        shape storeA blockSize rightClose seed =
      localBPRightFringeCandidateSeededTraceResultWithStore
        shape storeB blockSize rightClose seed := by
  unfold localBPRightFringeCandidateSeededTraceResultWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hread]

theorem localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize rightClose).trace ->
          P event) :
    forall event,
      List.Mem event
          (localBPRightFringeCandidateSeededTraceResultWithStore
            shape store blockSize rightClose seed).trace ->
        P event := by
  unfold localBPRightFringeCandidateSeededTraceResultWithStore
  exact WordRAM.TraceResult.map_trace_forall P _ _ hbp

theorem localBPRightFringeCandidateSeededTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize rightClose seed : Nat) :
    forall event,
      event ∈
          (localBPRightFringeCandidateSeededTraceResultWithStore
            shape store blockSize rightClose seed).trace ->
        event.matchesReadStore store := by
  exact
    localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
      shape store blockSize rightClose seed
      (fun event => event.matchesReadStore store)
      (localBPWindowBitsTraceResultWithStore_matchesReadStore
        shape store blockSize rightClose)

theorem localBPRightFringeCandidateSeededTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize rightClose seed : Nat) :
    forall event,
      event ∈
          (localBPRightFringeCandidateSeededTraceResultWithStore
            shape store blockSize rightClose seed).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
      shape store blockSize rightClose seed
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      (localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize rightClose)

/-- Store-parameterized all-size structural cross-block close decoder. -/
def crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStoreLegacy
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResultWithStore
          shape store blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
                shape segments store (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResultWithStore
                      shape store blockSize rightClose rightSeed)
/-- Canonical cross-block supplied-store consumer. -/
def crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (localBPLeftFringeCandidateSeededTraceResultWithStore
          shape store blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
                shape segments store (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResultWithStore
                      shape store blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (leftClose rightClose : Nat) :
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments store leftClose rightClose =
      crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
        shape segments hcomponent]
  case neg =>
    simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode]

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore shape).store.words[address]?)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
      shape rankCloseTrace segments store leftClose rightClose).toCosted =
      canonicalCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose := by
  rw [crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
    shape rankCloseTrace segments hbpCode hcomponent leftClose rightClose]
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
      shape rankCloseTrace rankCloseCosted segments leftClose rightClose hrank

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbpCode :
      forall index, storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hcomponent :
      forall address,
        storeA.readWord? segments.canonicalComponent address =
          storeB.readWord? segments.canonicalComponent address)
    (leftClose rightClose : Nat) :
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments storeA leftClose rightClose =
      crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments storeB leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_store_parametric
        shape segments hcomponent]
  case neg =>
    simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode]

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event, List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize close).trace -> P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace -> P event) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        P event := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  apply WordRAM.TraceResult.bind_trace_forall
  case hresult =>
    exact localBPSeedFromRankCloseTraceResult_trace_forall
      shape rankCloseTrace blockSize leftClose P hrank
  case hnext =>
    apply WordRAM.TraceResult.bind_trace_forall
    case hresult =>
      exact localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
        shape store blockSize leftClose _ P (hbp blockSize leftClose)
    case hnext =>
      apply WordRAM.TraceResult.bind_trace_forall
      case hresult =>
        by_cases hmiddle :
            blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose
        case pos =>
          simpa [blockSize, hmiddle] using
            hinterior (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)
        case neg =>
          simp [blockSize, hmiddle]
      case hnext =>
        apply WordRAM.TraceResult.bind_trace_forall
        case hresult =>
          exact localBPSeedFromRankCloseTraceResult_trace_forall
            shape rankCloseTrace blockSize rightClose P hrank
        case hnext =>
          exact WordRAM.TraceResult.map_trace_forall P _ _
            (localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
              shape store blockSize rightClose _ P (hbp blockSize rightClose))

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments store leftClose rightClose
      (fun event => event.matchesReadStore store) hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResultWithStore_matchesReadStore
          shape store blockSize close)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_matchesReadStore
          shape segments store startBlock count)

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          Not event.isSyntheticCostOnlyPrimitive) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments store leftClose rightClose
      (fun event => Not event.isSyntheticCostOnlyPrimitive) hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store blockSize close)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
          shape segments store startBlock count)

/-
Legacy segmented-table cross-block proof archive.

              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (localBPRightFringeCandidateSeededTraceResultWithStore
                      shape store blockSize rightClose rightSeed)

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (leftClose rightClose : Nat) :
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments store leftClose rightClose =
      crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
        shape segments hlocal hglobal hbaseline hminRel hmaxRel hargOffset]
  · simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_eq_of_agree
        hbpCode]

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
      shape rankCloseTrace segments store leftClose rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  rw [
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
      shape rankCloseTrace segments hbpCode hlocal hglobal hbaseline
      hminRel hmaxRel hargOffset leftClose rightClose]
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
      shape rankCloseTrace rankCloseCosted segments leftClose rightClose
      hrank

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index)
    (leftClose rightClose : Nat) :
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments storeA leftClose rightClose =
      crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments storeB leftClose rightClose := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_store_parametric
        shape segments hlocal hglobal hbaseline hminRel hmaxRel hargOffset]
  · simp [blockSize, hmiddle,
      localBPLeftFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode,
      localBPRightFringeCandidateSeededTraceResultWithStore_store_parametric
        shape hbpCode]

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hbp :
      forall blockSize close event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize close).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        P event := by
  unfold crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  intro event hmem
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, blockSize, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event hmem
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
        shape store blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event hmem
    rcases List.mem_append.mp htail with hmem | htail
    · exact hinterior
        (blockOfClose blockSize leftClose + 1)
        (blockOfClose blockSize rightClose -
          blockOfClose blockSize leftClose - 1)
        event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event hmem
    · exact localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
        shape store blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event hmem
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, blockSize, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event hmem
    rcases List.mem_append.mp htail with hmem | htail
    · exact localBPLeftFringeCandidateSeededTraceResultWithStore_trace_forall
        shape store blockSize leftClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize leftClose).value P
        (hbp blockSize leftClose) event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event hmem
    · exact localBPRightFringeCandidateSeededTraceResultWithStore_trace_forall
        shape store blockSize rightClose
        (localBPSeedFromRankCloseTraceResult
          shape rankCloseTrace blockSize rightClose).value P
        (hbp blockSize rightClose) event hmem

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      event ∈
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        event.matchesReadStore store := by
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments store leftClose rightClose
      (fun event => event.matchesReadStore store)
      hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResultWithStore_matchesReadStore
          shape store blockSize close)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_matchesReadStore
          shape segments store startBlock count)

theorem crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) :
    forall event,
      event ∈
          (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments store leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  exact
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments store leftClose rightClose
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
      hrank
      (fun blockSize close =>
        localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store blockSize close)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
          shape segments store startBlock count)
-/

theorem zeroBlockSameBlockCloseStructuralTraceResultWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?) :
    zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape store leftClose rightClose =
      zeroBlockSameBlockCloseStructuralTraceResult
        shape leftClose rightClose := by
  have h :=
    zeroBlockSameBlockCloseStructuralTraceResult_evalWithStore
      shape store leftClose rightClose hbpCode
  cases hstore :
      zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape store leftClose rightClose
  cases hcanonical :
      zeroBlockSameBlockCloseStructuralTraceResult
        shape leftClose rightClose
  simp [hstore, hcanonical] at h ⊢
  exact h

theorem zeroBlockSameBlockCloseStructuralTraceResultWithStore_store_parametric_eq
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (leftClose rightClose : Nat)
    (hread :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index) :
    zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape storeA leftClose rightClose =
      zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape storeB leftClose rightClose := by
  have h :=
    zeroBlockSameBlockCloseStructuralTraceResult_store_parametric
      shape storeA storeB leftClose rightClose hread
  cases hstoreA :
      zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape storeA leftClose rightClose
  cases hstoreB :
      zeroBlockSameBlockCloseStructuralTraceResultWithStore
        shape storeB leftClose rightClose
  simp [hstoreA, hstoreB] at h ⊢
  exact h

/-- Store-parameterized all-size structural compact close/LCA query trace. -/
def lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStoreLegacy
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (_sameBlockSegment : Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  if blockSize = 0 then
    zeroBlockSameBlockCloseStructuralTraceResultWithStore
      shape store leftClose rightClose
  else if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
      shape rankCloseTrace store blockSize leftClose rightClose
  else
    crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
      shape rankCloseTrace segments store leftClose rightClose
/-
Legacy zero-block and segmented-table LCA proof archive.


theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments store sameBlockSegment leftClose
        rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructural
        shape rankCloseTrace segments sameBlockSegment leftClose
        rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructural
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hzero : blockSize = 0
  · simp [blockSize, hzero,
      zeroBlockSameBlockCloseStructuralTraceResultWithStore_eq_of_agree
        shape store leftClose rightClose hbpCode]
  · by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
    · simp [blockSize, hzero, hsame,
        localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
          rankCloseTrace hbpCode]
    · simp [blockSize, hzero, hsame,
        crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
          shape rankCloseTrace segments hbpCode hlocal hglobal hbaseline
          hminRel hmaxRel hargOffset]

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {store : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hlocal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorLocalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hglobal :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          (concreteBPRelativeRmmInteriorGlobalTable
            shape).table.wordRAMStore.readWord? segment index)
    (hbaseline :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).baselineTable.wordRAMStore.readWord? segment index)
    (hminRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).minRelTable.wordRAMStore.readWord? segment index)
    (hmaxRel :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).maxRelTable.wordRAMStore.readWord? segment index)
    (hargOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          (concreteBPRelativeMinMaxArgSummaryTable_canonical
            shape).argOffsetTable.wordRAMStore.readWord? segment index)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
      shape rankCloseTrace segments store sameBlockSegment leftClose
      rightClose).toCosted =
      ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
        (concreteCompactBPCloseLCADirectory shape)
        rankCloseCosted leftClose rightClose := by
  rw [
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
      shape rankCloseTrace segments sameBlockSegment leftClose rightClose
      hbpCode hlocal hglobal hbaseline hminRel hmaxRel hargOffset]
  exact
    lcaCloseTraceResultWithRankSeedAllSizeStructural_refines
      shape rankCloseTrace rankCloseCosted segments sameBlockSegment
      leftClose rightClose hrank

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {storeA storeB : WordRAM.ReadStore}
    (sameBlockSegment leftClose rightClose : Nat)
    (hbpCode :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hlocal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.localOffset segments.deadSegment segment) index)
    (hglobal :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.globalBlock segments.deadSegment segment) index)
    (hbaseline :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.baseline segments.summary.deadSegment segment)
            index)
    (hminRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.minRel segments.summary.deadSegment segment)
            index)
    (hmaxRel :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.maxRel segments.summary.deadSegment segment)
            index)
    (hargOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap
              segments.summary.argOffset segments.summary.deadSegment segment)
            index) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments storeA sameBlockSegment leftClose
        rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        shape rankCloseTrace segments storeB sameBlockSegment leftClose
        rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hzero : blockSize = 0
  · simp [blockSize, hzero,
      zeroBlockSameBlockCloseStructuralTraceResultWithStore_store_parametric_eq
        shape leftClose rightClose hbpCode]
  · by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
    · simp [blockSize, hzero, hsame,
        localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
          shape rankCloseTrace hbpCode]
    · simp [blockSize, hzero, hsame,
        crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_store_parametric
          shape rankCloseTrace segments hbpCode hlocal hglobal hbaseline
          hminRel hmaxRel hargOffset]

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      event ∈
          (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
            shape rankCloseTrace segments store sameBlockSegment leftClose
            rightClose).trace ->
        event.matchesReadStore store := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hzero : blockSize = 0
  · simp [blockSize, hzero]
    exact
      zeroBlockSameBlockCloseStructuralTraceResultWithStore_matchesReadStore
        shape store leftClose rightClose
  · by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
    · simp [blockSize, hzero, hsame]
      exact
        localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
          shape rankCloseTrace store blockSize leftClose rightClose hrank
    · simp [blockSize, hzero, hsame]
      exact
        crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_matchesReadStore
          shape rankCloseTrace segments store leftClose rightClose hrank

theorem lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) :
    forall event,
      event ∈
          (lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
            shape rankCloseTrace segments store sameBlockSegment leftClose
            rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSize shape
  by_cases hzero : blockSize = 0
  · simp [blockSize, hzero]
    exact
      zeroBlockSameBlockCloseStructuralTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store leftClose rightClose
  · by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
    · simp [blockSize, hzero, hsame]
      exact
        localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_no_syntheticCostOnlyPrimitive
          shape rankCloseTrace store blockSize leftClose rightClose hrank
    · simp [blockSize, hzero, hsame]
      exact
        crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
          shape rankCloseTrace segments store leftClose rightClose hrank
-/

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ

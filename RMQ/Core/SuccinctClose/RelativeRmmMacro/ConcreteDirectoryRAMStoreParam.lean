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

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ

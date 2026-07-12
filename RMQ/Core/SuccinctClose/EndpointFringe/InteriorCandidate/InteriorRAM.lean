import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory
import RMQ.Core.SuccinctSpace.TablesRAM

/-!
# Word-RAM traces for endpoint-fringe interior candidates

This module mirrors the concrete two-level relative-rmM interior candidate path
with `WordRAM.TraceResult`s. The point is to replace black-box `ofCosted` wrapping
at the final close/LCA bridge with the same table-read control structure used by
the executable candidate code.
-/

namespace RMQ
namespace SuccinctSpace

namespace FixedWidthNatTable

/-- Polymorphic trace wrapper for an interpreted fixed-width natural table read. -/
def readTraceResult
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.ofResult ((table.readProgram i).eval table.wordRAMStore)

theorem readTraceResult_refines_readCosted
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readTraceResult i).toCosted = table.readCosted i := by
  exact FixedWidthNatTable.readProgram_refines_readCosted table i

/--
Read a fixed-width table while shifting its local segment numbering into a
caller-supplied global segment.  The erased value and modeled cost are exactly
the original interpreted table read.
-/
def readTraceResultAtSegment
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap segmentBase deadSegment)
    (table.readTraceResult i)

theorem readTraceResultAtSegment_refines_readCosted
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    (table.readTraceResultAtSegment segmentBase deadSegment i).toCosted =
      table.readCosted i := by
  simp [readTraceResultAtSegment, readTraceResult_refines_readCosted]

theorem readTraceResult_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    forall event,
      List.Mem event (table.readTraceResult i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simpa [readTraceResult, WordRAM.TraceResult.ofResult_trace] using
    WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
      (table.readProgram i) table.wordRAMStore event hmem

theorem readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment segmentBase deadSegment i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold readTraceResultAtSegment
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i)
      (table.readTraceResult_no_syntheticCostOnlyPrimitive i)

end FixedWidthNatTable

namespace FixedWidthOptionNatTable

/-- Polymorphic trace wrapper for an interpreted fixed-width optional-natural read. -/
def readTraceResult
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    WordRAM.TraceResult (Option (Option Nat)) :=
  WordRAM.TraceResult.ofResult ((table.readProgram i).eval table.wordRAMStore)

theorem readTraceResult_refines_readCosted
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readTraceResult i).toCosted = table.readCosted i := by
  exact FixedWidthOptionNatTable.readProgram_refines_readCosted table i

/--
Read a fixed-width optional table while shifting its local segment numbering
into a caller-supplied global segment.
-/
def readTraceResultAtSegment
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    WordRAM.TraceResult (Option (Option Nat)) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap segmentBase deadSegment)
    (table.readTraceResult i)

theorem readTraceResultAtSegment_refines_readCosted
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    (table.readTraceResultAtSegment segmentBase deadSegment i).toCosted =
      table.readCosted i := by
  simp [readTraceResultAtSegment, readTraceResult_refines_readCosted]

theorem readTraceResult_no_syntheticCostOnlyPrimitive
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    forall event,
      List.Mem event (table.readTraceResult i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simpa [readTraceResult, WordRAM.TraceResult.ofResult_trace] using
    WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
      (table.readProgram i) table.wordRAMStore event hmem

theorem readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment segmentBase deadSegment i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold readTraceResultAtSegment
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (table.readTraceResult i)
      (table.readTraceResult_no_syntheticCostOnlyPrimitive i)

end FixedWidthOptionNatTable

end SuccinctSpace

namespace SuccinctClose

open SuccinctSpace

/-- Global segment bases for the four tables in one relative summary row. -/
structure BPRelativeSummaryTraceSegments where
  baseline : Nat
  minRel : Nat
  maxRel : Nat
  argOffset : Nat
  deadSegment : Nat

/-- Global segment bases for the concrete relative-rmM interior candidate. -/
structure BPRelativeRmmInteriorTraceSegments where
  canonicalComponent : Nat
  summary : BPRelativeSummaryTraceSegments
  localOffset : Nat
  globalBlock : Nat
  finiteSmallMin : Nat
  finiteSmallArg : Nat
  deadSegment : Nat

/-- Interpret one flat read interface as one segment of a WordRAM store. -/
def flatWordStoreOfReadStore
    (store : WordRAM.ReadStore) (segment : Nat) : FlatWordStore :=
  fun address => store.readWord? segment address

/-- Convert an operational flat-store execution into its exact read trace. -/
def flatStoreExecutionTraceResultAtSegment
    (segment : Nat) (execution : FlatStoreExecution alpha) :
    WordRAM.TraceResult alpha where
  value := execution.value
  trace := execution.reads.map fun read =>
    WordRAM.TraceEvent.readWord segment read.1 read.2

@[simp] theorem flatStoreExecutionTraceResultAtSegment_toCosted
    (segment : Nat) (execution : FlatStoreExecution alpha) :
    (flatStoreExecutionTraceResultAtSegment segment execution).toCosted =
      execution.toCosted := by
  apply Costed.ext
  case hvalue => rfl
  case hcost =>
    simp [flatStoreExecutionTraceResultAtSegment,
      FlatStoreExecution.toCosted]

theorem flatStoreComputationTraceResultAtSegment_matchesReadStore
    (computation : FlatStoreComputation alpha)
    (store : WordRAM.ReadStore) (segment : Nat) :
    forall event,
      List.Mem event
        (flatStoreExecutionTraceResultAtSegment segment
          (computation.run
            (flatWordStoreOfReadStore store segment))).trace ->
        event.matchesReadStore store := by
  intro event hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro hread hevent =>
          subst event
          have hmatch :=
            computation.reads_match_store
              (flatWordStoreOfReadStore store segment)
              read.1 read.2 hread
          simpa [flatWordStoreOfReadStore,
            WordRAM.TraceEvent.matchesReadStore] using hmatch

theorem flatStoreExecutionTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (segment : Nat) (execution : FlatStoreExecution alpha) :
    forall event,
      List.Mem event
        (flatStoreExecutionTraceResultAtSegment segment execution).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  cases List.mem_map.mp hmem with
  | intro read hrest =>
      cases hrest with
      | intro hread hevent =>
          subst event
          simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

/-- Structural trace for one relative min/max/arg summary read. -/
def summaryTraceResult
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat × Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (table.baselineTable.readTraceResult (block / blocksPerSuper))
    fun baseline? =>
      WordRAM.TraceResult.bind (table.minRelTable.readTraceResult block)
        fun minRel? =>
          WordRAM.TraceResult.bind (table.maxRelTable.readTraceResult block)
            fun maxRel? =>
              WordRAM.TraceResult.map
                (fun argOffset? =>
                  match baseline?, minRel?, maxRel?, argOffset? with
                  | some baseline, some minRel, some maxRel, some argOffset =>
                      some (baseline, minRel, maxRel, argOffset)
                  | _, _, _, _ => none)
                (table.argOffsetTable.readTraceResult block)

theorem summaryTraceResult_refines_summaryCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryTraceResult block).toCosted =
      table.summaryCosted block := by
  apply Costed.ext
  · simp [summaryTraceResult, summaryCosted,
      FixedWidthNatTable.readTraceResult_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]
    cases (table.baselineTable.readCosted (block / blocksPerSuper)).value <;>
      cases (table.minRelTable.readCosted block).value <;>
      cases (table.maxRelTable.readCosted block).value <;>
      cases (table.argOffsetTable.readCosted block).value <;> rfl
  · simp [summaryTraceResult, summaryCosted,
      FixedWidthNatTable.readTraceResult_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]

/-- Segment-relabeled structural trace for one relative summary read. -/
def summaryTraceResultAtSegments
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat × Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (table.baselineTable.readTraceResultAtSegment
      segments.baseline segments.deadSegment (block / blocksPerSuper))
    fun baseline? =>
      WordRAM.TraceResult.bind
        (table.minRelTable.readTraceResultAtSegment
          segments.minRel segments.deadSegment block)
        fun minRel? =>
          WordRAM.TraceResult.bind
            (table.maxRelTable.readTraceResultAtSegment
              segments.maxRel segments.deadSegment block)
            fun maxRel? =>
              WordRAM.TraceResult.map
                (fun argOffset? =>
                  match baseline?, minRel?, maxRel?, argOffset? with
                  | some baseline, some minRel, some maxRel, some argOffset =>
                      some (baseline, minRel, maxRel, argOffset)
                  | _, _, _, _ => none)
                (table.argOffsetTable.readTraceResultAtSegment
                  segments.argOffset segments.deadSegment block)

theorem summaryTraceResultAtSegments_refines_summaryCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) :
    (table.summaryTraceResultAtSegments segments block).toCosted =
      table.summaryCosted block := by
  apply Costed.ext
  · simp [summaryTraceResultAtSegments, summaryCosted,
      FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]
    cases (table.baselineTable.readCosted (block / blocksPerSuper)).value <;>
      cases (table.minRelTable.readCosted block).value <;>
      cases (table.maxRelTable.readCosted block).value <;>
      cases (table.argOffsetTable.readCosted block).value <;> rfl
  · simp [summaryTraceResultAtSegments, summaryCosted,
      FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted,
      WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
      Costed.bind, Costed.map]

/-- Structural trace for the minimum candidate represented by one summary row. -/
def minCandidateTraceResult
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (table.summaryTraceResult block)

theorem minCandidateTraceResult_refines_minCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateTraceResult block).toCosted =
      table.minCandidateCosted block := by
  simp [minCandidateTraceResult, minCandidateCosted,
    summaryTraceResult_refines_summaryCosted,
    WordRAM.TraceResult.map_toCosted, Costed.map]

/-- Segment-relabeled structural trace for one summary-row minimum candidate. -/
def minCandidateTraceResultAtSegments
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (table.summaryTraceResultAtSegments segments block)

theorem minCandidateTraceResultAtSegments_refines_minCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) :
    (table.minCandidateTraceResultAtSegments segments block).toCosted =
      table.minCandidateCosted block := by
  simp [minCandidateTraceResultAtSegments, minCandidateCosted,
    summaryTraceResultAtSegments_refines_summaryCosted,
    WordRAM.TraceResult.map_toCosted, Costed.map]

end PayloadLiveBPRelativeMinMaxArgSummaryTable

namespace PayloadLiveBPLocalSparseOffsetTable

/-- Structural trace for one local sparse-offset table read. -/
def readOffsetTraceResult
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : WordRAM.TraceResult (Option Nat) :=
  offsetTable.table.readTraceResult
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetTraceResult_refines_readOffsetCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) :
    (offsetTable.readOffsetTraceResult macroIdx localStart level).toCosted =
      offsetTable.readOffsetCosted macroIdx localStart level := by
  simp [readOffsetTraceResult, readOffsetCosted,
    FixedWidthNatTable.readTraceResult_refines_readCosted]

/-- Segment-relabeled structural trace for one local sparse-offset table read. -/
def readOffsetTraceResultAtSegment
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment macroIdx localStart level : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  offsetTable.table.readTraceResultAtSegment segmentBase deadSegment
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetTraceResultAtSegment_refines_readOffsetCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment macroIdx localStart level : Nat) :
    (offsetTable.readOffsetTraceResultAtSegment segmentBase deadSegment macroIdx
        localStart level).toCosted =
      offsetTable.readOffsetCosted macroIdx localStart level := by
  simp [readOffsetTraceResultAtSegment, readOffsetCosted,
    FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted]

/-- Structural trace for one local sparse span candidate. -/
def spanCandidateTraceResult
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
    (macroIdx localStart level : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (offsetTable.readOffsetTraceResult macroIdx localStart level)
    fun offset? =>
      match offset? with
      | some offset =>
          summary.minCandidateTraceResult (macroIdx * macroSize + offset)
      | none => WordRAM.TraceResult.pure none

theorem spanCandidateTraceResult_refines_spanCandidateCosted
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
    (macroIdx localStart level : Nat) :
    (offsetTable.spanCandidateTraceResult summary macroIdx localStart
        level).toCosted =
      offsetTable.spanCandidateCosted summary macroIdx localStart level := by
  unfold spanCandidateTraceResult spanCandidateCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [readOffsetTraceResult_refines_readOffsetCosted]
  cases hoff :
      (offsetTable.readOffsetCosted macroIdx localStart level).value
  <;> simp [hoff,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResult_refines_minCandidateCosted,
    Costed.bind, Costed.pure]

/-- Segment-relabeled structural trace for one local sparse span candidate. -/
def spanCandidateTraceResultAtSegments
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
    (macroIdx localStart level : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (offsetTable.readOffsetTraceResultAtSegment segments.localOffset
      segments.deadSegment macroIdx localStart level)
    fun offset? =>
      match offset? with
      | some offset =>
          summary.minCandidateTraceResultAtSegments segments.summary
            (macroIdx * macroSize + offset)
      | none => WordRAM.TraceResult.pure none

theorem spanCandidateTraceResultAtSegments_refines_spanCandidateCosted
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
    (macroIdx localStart level : Nat) :
    (offsetTable.spanCandidateTraceResultAtSegments summary segments macroIdx
        localStart level).toCosted =
      offsetTable.spanCandidateCosted summary macroIdx localStart level := by
  unfold spanCandidateTraceResultAtSegments spanCandidateCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [readOffsetTraceResultAtSegment_refines_readOffsetCosted]
  cases hoff :
      (offsetTable.readOffsetCosted macroIdx localStart level).value
  <;> simp [hoff,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_refines_minCandidateCosted,
    Costed.bind, Costed.pure]

/-- Structural trace for the two local sparse spans covering a local range. -/
def twoSpanCandidateTraceResult
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
    (macroIdx localStart count : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  let rightLocalStart := localStart + count - span
  WordRAM.TraceResult.bind
    (offsetTable.spanCandidateTraceResult summary macroIdx localStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (offsetTable.spanCandidateTraceResult summary macroIdx
          rightLocalStart level)

theorem twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted
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
    (macroIdx localStart count : Nat) :
    (offsetTable.twoSpanCandidateTraceResult summary macroIdx localStart
        count).toCosted =
      offsetTable.twoSpanCandidateCosted summary macroIdx localStart count := by
  simp [twoSpanCandidateTraceResult, twoSpanCandidateCosted,
    spanCandidateTraceResult_refines_spanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Segment-relabeled structural trace for the two local sparse spans. -/
def twoSpanCandidateTraceResultAtSegments
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
    (macroIdx localStart count : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  let rightLocalStart := localStart + count - span
  WordRAM.TraceResult.bind
    (offsetTable.spanCandidateTraceResultAtSegments summary segments
      macroIdx localStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (offsetTable.spanCandidateTraceResultAtSegments summary segments
          macroIdx rightLocalStart level)

theorem twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted
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
    (macroIdx localStart count : Nat) :
    (offsetTable.twoSpanCandidateTraceResultAtSegments summary segments
        macroIdx localStart count).toCosted =
      offsetTable.twoSpanCandidateCosted summary macroIdx localStart count := by
  simp [twoSpanCandidateTraceResultAtSegments, twoSpanCandidateCosted,
    spanCandidateTraceResultAtSegments_refines_spanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

end PayloadLiveBPLocalSparseOffsetTable

namespace PayloadLiveBPGlobalSparseBlockTable

/-- Structural trace for one global sparse-block table read. -/
def readBlockTraceResult
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : WordRAM.TraceResult (Option Nat) :=
  globalTable.table.readTraceResult
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockTraceResult_refines_readBlockCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) :
    (globalTable.readBlockTraceResult macroStart level).toCosted =
      globalTable.readBlockCosted macroStart level := by
  simp [readBlockTraceResult, readBlockCosted,
    FixedWidthNatTable.readTraceResult_refines_readCosted]

/-- Segment-relabeled structural trace for one global sparse-block table read. -/
def readBlockTraceResultAtSegment
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment macroStart level : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  globalTable.table.readTraceResultAtSegment segmentBase deadSegment
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockTraceResultAtSegment_refines_readBlockCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment macroStart level : Nat) :
    (globalTable.readBlockTraceResultAtSegment segmentBase deadSegment macroStart
        level).toCosted =
      globalTable.readBlockCosted macroStart level := by
  simp [readBlockTraceResultAtSegment, readBlockCosted,
    FixedWidthNatTable.readTraceResultAtSegment_refines_readCosted]

/-- Structural trace for one global sparse span candidate. -/
def spanCandidateTraceResult
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
    (macroStart level : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (globalTable.readBlockTraceResult macroStart level) fun block? =>
      match block? with
      | some block => summary.minCandidateTraceResult block
      | none => WordRAM.TraceResult.pure none

theorem spanCandidateTraceResult_refines_spanCandidateCosted
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
    (macroStart level : Nat) :
    (globalTable.spanCandidateTraceResult summary macroStart level).toCosted =
      globalTable.spanCandidateCosted summary macroStart level := by
  unfold spanCandidateTraceResult spanCandidateCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [readBlockTraceResult_refines_readBlockCosted]
  cases hblock :
      (globalTable.readBlockCosted macroStart level).value
  <;> simp [hblock,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResult_refines_minCandidateCosted,
    Costed.bind, Costed.pure]

/-- Segment-relabeled structural trace for one global sparse span candidate. -/
def spanCandidateTraceResultAtSegments
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
    (macroStart level : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  WordRAM.TraceResult.bind
    (globalTable.readBlockTraceResultAtSegment segments.globalBlock
      segments.deadSegment macroStart level) fun block? =>
      match block? with
      | some block =>
          summary.minCandidateTraceResultAtSegments segments.summary block
      | none => WordRAM.TraceResult.pure none

theorem spanCandidateTraceResultAtSegments_refines_spanCandidateCosted
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
    (macroStart level : Nat) :
    (globalTable.spanCandidateTraceResultAtSegments summary segments
        macroStart level).toCosted =
      globalTable.spanCandidateCosted summary macroStart level := by
  unfold spanCandidateTraceResultAtSegments spanCandidateCosted
  rw [WordRAM.TraceResult.bind_toCosted]
  rw [readBlockTraceResultAtSegment_refines_readBlockCosted]
  cases hblock :
      (globalTable.readBlockCosted macroStart level).value
  <;> simp [hblock,
    PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_refines_minCandidateCosted,
    Costed.bind, Costed.pure]

/-- Structural trace for the two global sparse spans covering a macro range. -/
def twoSpanCandidateTraceResult
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
    (macroStart macroSpanCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  WordRAM.TraceResult.bind
    (globalTable.spanCandidateTraceResult summary macroStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (globalTable.spanCandidateTraceResult summary rightMacroStart level)

theorem twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted
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
    (macroStart macroSpanCount : Nat) :
    (globalTable.twoSpanCandidateTraceResult summary macroStart
        macroSpanCount).toCosted =
      globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount := by
  simp [twoSpanCandidateTraceResult, twoSpanCandidateCosted,
    spanCandidateTraceResult_refines_spanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Segment-relabeled structural trace for the two global sparse spans. -/
def twoSpanCandidateTraceResultAtSegments
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
    (macroStart macroSpanCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  WordRAM.TraceResult.bind
    (globalTable.spanCandidateTraceResultAtSegments summary segments
      macroStart level)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (globalTable.spanCandidateTraceResultAtSegments summary segments
          rightMacroStart level)

theorem twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted
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
    (macroStart macroSpanCount : Nat) :
    (globalTable.twoSpanCandidateTraceResultAtSegments summary segments
        macroStart macroSpanCount).toCosted =
      globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount := by
  simp [twoSpanCandidateTraceResultAtSegments, twoSpanCandidateCosted,
    spanCandidateTraceResultAtSegments_refines_spanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

end PayloadLiveBPGlobalSparseBlockTable

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbaseline :
      forall event,
        List.Mem event
          (table.baselineTable.readTraceResultAtSegment
            segments.baseline segments.deadSegment
            (block / blocksPerSuper)).trace -> P event)
    (hminRel :
      forall event,
        List.Mem event
          (table.minRelTable.readTraceResultAtSegment
            segments.minRel segments.deadSegment block).trace -> P event)
    (hmaxRel :
      forall event,
        List.Mem event
          (table.maxRelTable.readTraceResultAtSegment
            segments.maxRel segments.deadSegment block).trace -> P event)
    (hargOffset :
      forall event,
        List.Mem event
          (table.argOffsetTable.readTraceResultAtSegment
            segments.argOffset segments.deadSegment block).trace -> P event) :
    forall event,
      List.Mem event
          (table.summaryTraceResultAtSegments segments block).trace ->
        P event := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbaseline
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact hminRel
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact hmaxRel
      · apply WordRAM.TraceResult.map_trace_forall
        exact hargOffset

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_trace_forall
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsummary :
      forall event,
        List.Mem event
          (table.summaryTraceResultAtSegments segments block).trace ->
        P event) :
    forall event,
      List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        P event := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments
  exact WordRAM.TraceResult.map_trace_forall P _ _ hsummary

theorem PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments_trace_forall
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
    (macroIdx localStart level : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall event,
        List.Mem event
          (offsetTable.readOffsetTraceResultAtSegment
            segments.localOffset segments.deadSegment macroIdx localStart
            level).trace -> P event)
    (hsummary :
      forall block event,
        List.Mem event
          (summary.minCandidateTraceResultAtSegments
            segments.summary block).trace -> P event) :
    forall event,
      List.Mem event
          (offsetTable.spanCandidateTraceResultAtSegments summary segments
            macroIdx localStart level).trace -> P event := by
  unfold PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hread
  · cases hoff :
      (offsetTable.readOffsetTraceResultAtSegment segments.localOffset
        segments.deadSegment macroIdx localStart level).value with
    | none =>
        exact
          WordRAM.TraceResult.pure_trace_forall P
            (none : Option (Nat × Nat))
    | some offset =>
        exact hsummary (macroIdx * macroSize + offset)

theorem PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_trace_forall
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
    (macroIdx localStart count : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall macroIdx localStart level event,
        List.Mem event
          (offsetTable.readOffsetTraceResultAtSegment
            segments.localOffset segments.deadSegment macroIdx localStart
            level).trace -> P event)
    (hsummary :
      forall block event,
        List.Mem event
          (summary.minCandidateTraceResultAtSegments
            segments.summary block).trace -> P event) :
    forall event,
      List.Mem event
          (offsetTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace -> P event := by
  unfold PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      offsetTable.spanCandidateTraceResultAtSegments_trace_forall
        summary segments macroIdx localStart (Nat.log2 count) P
        (hread macroIdx localStart (Nat.log2 count)) hsummary
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      offsetTable.spanCandidateTraceResultAtSegments_trace_forall
        summary segments macroIdx (localStart + count - bpSparseLogSpan count)
        (Nat.log2 count) P
        (hread macroIdx (localStart + count - bpSparseLogSpan count)
          (Nat.log2 count)) hsummary

theorem PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments_trace_forall
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
    (macroStart level : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall event,
        List.Mem event
          (globalTable.readBlockTraceResultAtSegment
            segments.globalBlock segments.deadSegment macroStart level).trace ->
        P event)
    (hsummary :
      forall block event,
        List.Mem event
          (summary.minCandidateTraceResultAtSegments
            segments.summary block).trace -> P event) :
    forall event,
      List.Mem event
          (globalTable.spanCandidateTraceResultAtSegments summary segments
            macroStart level).trace -> P event := by
  unfold PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hread
  · cases hblock :
      (globalTable.readBlockTraceResultAtSegment segments.globalBlock
        segments.deadSegment macroStart level).value with
    | none =>
        exact
          WordRAM.TraceResult.pure_trace_forall P
            (none : Option (Nat × Nat))
    | some block =>
        exact hsummary block

theorem PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_trace_forall
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
    (macroStart macroSpanCount : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall macroStart level event,
        List.Mem event
          (globalTable.readBlockTraceResultAtSegment
            segments.globalBlock segments.deadSegment macroStart level).trace ->
        P event)
    (hsummary :
      forall block event,
        List.Mem event
          (summary.minCandidateTraceResultAtSegments
            segments.summary block).trace -> P event) :
    forall event,
      List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace -> P event := by
  unfold PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      globalTable.spanCandidateTraceResultAtSegments_trace_forall
        summary segments macroStart (Nat.log2 macroSpanCount) P
        (hread macroStart (Nat.log2 macroSpanCount)) hsummary
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      globalTable.spanCandidateTraceResultAtSegments_trace_forall
        summary segments
        (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
        (Nat.log2 macroSpanCount) P
        (hread
          (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
          (Nat.log2 macroSpanCount)) hsummary

/-- Structural trace for the adjacent-macro interior candidate case. -/
def bpTwoLevelAdjacentMacroCandidateTraceResult
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
    (macroStart localStart rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResult summary macroStart localStart
      leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (localTable.twoSpanCandidateTraceResult summary (macroStart + 1) 0
          rightCount)

theorem bpTwoLevelAdjacentMacroCandidateTraceResult_refines
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
    (macroStart localStart rightCount : Nat) :
    (bpTwoLevelAdjacentMacroCandidateTraceResult
      localTable summary macroStart localStart rightCount).toCosted =
      bpTwoLevelAdjacentMacroCandidateCosted
        localTable summary macroStart localStart rightCount := by
  simp [bpTwoLevelAdjacentMacroCandidateTraceResult,
    bpTwoLevelAdjacentMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Structural trace for the left-plus-middle macro interior candidate case. -/
def bpTwoLevelLeftMiddleMacroCandidateTraceResult
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
    (macroStart localStart middleMacroCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResult summary macroStart localStart
      leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun middle? => bpCandidateMerge? left? middle?)
        (globalTable.twoSpanCandidateTraceResult summary (macroStart + 1)
          middleMacroCount)

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResult_refines
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
    (macroStart localStart middleMacroCount : Nat) :
    (bpTwoLevelLeftMiddleMacroCandidateTraceResult
      localTable globalTable summary macroStart localStart
        middleMacroCount).toCosted =
      bpTwoLevelLeftMiddleMacroCandidateCosted
        localTable globalTable summary macroStart localStart
        middleMacroCount := by
  simp [bpTwoLevelLeftMiddleMacroCandidateTraceResult,
    bpTwoLevelLeftMiddleMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted,
    PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Structural trace for the left-middle-right macro interior candidate case. -/
def bpTwoLevelCrossMacroCandidateTraceResult
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
    (macroStart localStart middleMacroCount rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResult summary macroStart localStart
      leftCount)
    fun left? =>
      WordRAM.TraceResult.bind
        (globalTable.twoSpanCandidateTraceResult summary (macroStart + 1)
          middleMacroCount)
        fun middle? =>
          WordRAM.TraceResult.map
            (fun right? => bpCandidateMerge3? left? middle? right?)
            (localTable.twoSpanCandidateTraceResult summary rightMacroStart 0
              rightCount)

theorem bpTwoLevelCrossMacroCandidateTraceResult_refines
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
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (bpTwoLevelCrossMacroCandidateTraceResult
      localTable globalTable summary macroStart localStart middleMacroCount
        rightCount).toCosted =
      bpTwoLevelCrossMacroCandidateCosted
        localTable globalTable summary macroStart localStart middleMacroCount
        rightCount := by
  simp [bpTwoLevelCrossMacroCandidateTraceResult,
    bpTwoLevelCrossMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted,
    PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Segment-relabeled trace for the adjacent-macro interior candidate case. -/
def bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
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
    (macroStart localStart rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResultAtSegments summary segments
      macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun right? => bpCandidateMerge? left? right?)
        (localTable.twoSpanCandidateTraceResultAtSegments summary segments
          (macroStart + 1) 0 rightCount)

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_refines
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
    (macroStart localStart rightCount : Nat) :
    (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
      localTable summary segments macroStart localStart rightCount).toCosted =
      bpTwoLevelAdjacentMacroCandidateCosted
        localTable summary macroStart localStart rightCount := by
  simp [bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments,
    bpTwoLevelAdjacentMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Segment-relabeled trace for the left-plus-middle macro candidate case. -/
def bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
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
    (macroStart localStart middleMacroCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResultAtSegments summary segments
      macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.map
        (fun middle? => bpCandidateMerge? left? middle?)
        (globalTable.twoSpanCandidateTraceResultAtSegments summary segments
          (macroStart + 1) middleMacroCount)

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_refines
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
    (macroStart localStart middleMacroCount : Nat) :
    (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
      localTable globalTable summary segments macroStart localStart
        middleMacroCount).toCosted =
      bpTwoLevelLeftMiddleMacroCandidateCosted
        localTable globalTable summary macroStart localStart
        middleMacroCount := by
  simp [bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments,
    bpTwoLevelLeftMiddleMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted,
    PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Segment-relabeled trace for the left-middle-right macro candidate case. -/
def bpTwoLevelCrossMacroCandidateTraceResultAtSegments
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
    (macroStart localStart middleMacroCount rightCount : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  WordRAM.TraceResult.bind
    (localTable.twoSpanCandidateTraceResultAtSegments summary segments
      macroStart localStart leftCount)
    fun left? =>
      WordRAM.TraceResult.bind
        (globalTable.twoSpanCandidateTraceResultAtSegments summary segments
          (macroStart + 1) middleMacroCount)
        fun middle? =>
          WordRAM.TraceResult.map
            (fun right? => bpCandidateMerge3? left? middle? right?)
            (localTable.twoSpanCandidateTraceResultAtSegments summary
              segments rightMacroStart 0 rightCount)

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegments_refines
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
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (bpTwoLevelCrossMacroCandidateTraceResultAtSegments
      localTable globalTable summary segments macroStart localStart
        middleMacroCount rightCount).toCosted =
      bpTwoLevelCrossMacroCandidateCosted
        localTable globalTable summary macroStart localStart middleMacroCount
        rightCount := by
  simp [bpTwoLevelCrossMacroCandidateTraceResultAtSegments,
    bpTwoLevelCrossMacroCandidateCosted,
    PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted,
    PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    Costed.bind, Costed.map]

/-- Structural trace mirror for the concrete two-level interior candidate. -/
def bpTwoLevelInteriorCandidateTraceResult
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
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    WordRAM.TraceResult.pure none
  else if count <= macroSize - localStart then
    localTable.twoSpanCandidateTraceResult summary macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateTraceResult localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateTraceResult localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateTraceResult localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateTraceResult_refines
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
    (startBlock count : Nat) :
    (bpTwoLevelInteriorCandidateTraceResult
      localTable globalTable summary startBlock count).toCosted =
      bpTwoLevelInteriorCandidateCosted
        localTable globalTable summary startBlock count := by
  unfold bpTwoLevelInteriorCandidateTraceResult
    bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, WordRAM.TraceResult.pure_toCosted, Costed.pure]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin,
        PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult_refines_twoSpanCandidateCosted]
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle, bpTwoLevelAdjacentMacroCandidateTraceResult_refines]
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp [hright,
            bpTwoLevelLeftMiddleMacroCandidateTraceResult_refines]
        · simp [hright,
            bpTwoLevelCrossMacroCandidateTraceResult_refines]

/-- Segment-relabeled structural mirror for the two-level interior candidate. -/
def bpTwoLevelInteriorCandidateTraceResultAtSegments
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
    (startBlock count : Nat) : WordRAM.TraceResult (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    WordRAM.TraceResult.pure none
  else if count <= macroSize - localStart then
    localTable.twoSpanCandidateTraceResultAtSegments summary segments
      macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments localTable
        summary segments macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments localTable
        globalTable summary segments macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateTraceResultAtSegments localTable globalTable
        summary segments macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateTraceResultAtSegments_refines
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
    (startBlock count : Nat) :
    (bpTwoLevelInteriorCandidateTraceResultAtSegments
      localTable globalTable summary segments startBlock count).toCosted =
      bpTwoLevelInteriorCandidateCosted
        localTable globalTable summary startBlock count := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegments
    bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, WordRAM.TraceResult.pure_toCosted, Costed.pure]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin,
        PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_refines_twoSpanCandidateCosted]
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle,
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_refines]
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp [hright,
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_refines]
        · simp [hright,
            bpTwoLevelCrossMacroCandidateTraceResultAtSegments_refines]

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_trace_forall
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
    (macroStart localStart rightCount : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace -> P event) :
    forall event,
      List.Mem event
          (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
            localTable summary segments macroStart localStart rightCount).trace ->
        P event := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hlocalSpan (macroStart + 1) 0 rightCount

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_trace_forall
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
    (macroStart localStart middleMacroCount : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace -> P event)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace -> P event) :
    forall event,
      List.Mem event
          (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount).trace -> P event := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hglobalSpan (macroStart + 1) middleMacroCount

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegments_trace_forall
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
    (macroStart localStart middleMacroCount rightCount : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace -> P event)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace -> P event) :
    forall event,
      List.Mem event
          (bpTwoLevelCrossMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount rightCount).trace -> P event := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact hglobalSpan (macroStart + 1) middleMacroCount
    · apply WordRAM.TraceResult.map_trace_forall
      exact hlocalSpan (macroStart + 1 + middleMacroCount) 0 rightCount

theorem bpTwoLevelInteriorCandidateTraceResultAtSegments_trace_forall
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
    (startBlock count : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace -> P event)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace -> P event) :
    forall event,
      List.Mem event
          (bpTwoLevelInteriorCandidateTraceResultAtSegments
            localTable globalTable summary segments startBlock count).trace ->
        P event := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegments
  by_cases hcount : count = 0
  · simp [hcount]
    exact
      WordRAM.TraceResult.pure_trace_forall P
        (none : Option (Nat × Nat))
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      exact hlocalSpan (startBlock / macroSize)
        (startBlock % macroSize) count
    · simp [hwithin]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        exact
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_trace_forall
            localTable summary segments
            (startBlock / macroSize) (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
            P hlocalSpan
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0
        · simp [hright]
          exact
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_trace_forall
              localTable globalTable summary segments
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              P hlocalSpan hglobalSpan
        · simp [hright]
          exact
            bpTwoLevelCrossMacroCandidateTraceResultAtSegments_trace_forall
              localTable globalTable summary segments
              (startBlock / macroSize) (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) % macroSize)
              P hlocalSpan hglobalSpan

theorem fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          table.wordRAMStore.readWord? segment index) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment segmentBase deadSegment i).trace ->
        event.matchesReadStore store := by
  unfold FixedWidthNatTable.readTraceResultAtSegment
    FixedWidthNatTable.readTraceResult
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (WordRAM.TraceResult.ofResult
        ((table.readProgram i).eval table.wordRAMStore))
      (WordRAM.ReadStore.ofStore table.wordRAMStore)
      store
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      hread
      (by
        intro event hmem
        simpa [WordRAM.TraceResult.ofResult_trace,
          WordRAM.TraceEvent.matchesReadStore_ofStore] using
          WordRAM.Program.eval_reads_subset_payload
            (table.readProgram i) table.wordRAMStore event hmem)

theorem fixedWidthOptionNatTable_readTraceResultAtSegment_matchesReadStore
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width)
    (segmentBase deadSegment i : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          table.wordRAMStore.readWord? segment index) :
    forall event,
      List.Mem event
          (table.readTraceResultAtSegment segmentBase deadSegment i).trace ->
        event.matchesReadStore store := by
  unfold FixedWidthOptionNatTable.readTraceResultAtSegment
    FixedWidthOptionNatTable.readTraceResult
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (WordRAM.TraceResult.ofResult
        ((table.readProgram i).eval table.wordRAMStore))
      (WordRAM.ReadStore.ofStore table.wordRAMStore)
      store
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      hread
      (by
        intro event hmem
        simpa [WordRAM.TraceResult.ofResult_trace,
          WordRAM.TraceEvent.matchesReadStore_ofStore] using
          WordRAM.Program.eval_reads_subset_payload
            (table.readProgram i) table.wordRAMStore event hmem)

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
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
    forall event,
      List.Mem event
          (table.summaryTraceResultAtSegments segments block).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
        table.baselineTable segments.baseline segments.deadSegment
        (block / blocksPerSuper) store hbaseline
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
          table.minRelTable segments.minRel segments.deadSegment block
          store hminRel
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
            table.maxRelTable segments.maxRel segments.deadSegment block
            store hmaxRel
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
            table.argOffsetTable segments.argOffset segments.deadSegment
            block store hargOffset

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (store : WordRAM.ReadStore)
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
    forall event,
      List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.map_trace_forall
  exact
    table.summaryTraceResultAtSegments_matchesReadStore segments store
      hbaseline hminRel hmaxRel hargOffset block

theorem PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          offsetTable.table.wordRAMStore.readWord? segment index)
    (macroIdx localStart level : Nat) :
    forall event,
      List.Mem event
          (offsetTable.readOffsetTraceResultAtSegment segmentBase deadSegment
            macroIdx localStart level).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment
  exact
    fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
      offsetTable.table segmentBase deadSegment
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)
      store hread

theorem PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments_matchesReadStore
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
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroIdx localStart level : Nat) :
    forall event,
      List.Mem event
          (offsetTable.spanCandidateTraceResultAtSegments summary segments
            macroIdx localStart level).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      offsetTable.readOffsetTraceResultAtSegment_matchesReadStore
        segments.localOffset segments.deadSegment store hlocal
        macroIdx localStart level
  · cases hoff :
      (offsetTable.readOffsetTraceResultAtSegment segments.localOffset
        segments.deadSegment macroIdx localStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some offset =>
        exact
          summary.minCandidateTraceResultAtSegments_matchesReadStore
            segments.summary store hbaseline hminRel hmaxRel hargOffset
            (macroIdx * macroSize + offset)

theorem PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_matchesReadStore
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
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroIdx localStart count : Nat) :
    forall event,
      List.Mem event
          (offsetTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      offsetTable.spanCandidateTraceResultAtSegments_matchesReadStore
        summary segments store hlocal hbaseline hminRel hmaxRel hargOffset
        macroIdx localStart (Nat.log2 count)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      offsetTable.spanCandidateTraceResultAtSegments_matchesReadStore
        summary segments store hlocal hbaseline hminRel hmaxRel hargOffset
        macroIdx (localStart + count - bpSparseLogSpan count)
        (Nat.log2 count)

theorem PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          globalTable.table.wordRAMStore.readWord? segment index)
    (macroStart level : Nat) :
    forall event,
      List.Mem event
          (globalTable.readBlockTraceResultAtSegment segmentBase deadSegment
            macroStart level).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment
  exact
    fixedWidthNatTable_readTraceResultAtSegment_matchesReadStore
      globalTable.table segmentBase deadSegment
      (bpGlobalSparseCellSlot macroCount macroStart level) store hread

theorem PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments_matchesReadStore
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
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart level : Nat) :
    forall event,
      List.Mem event
          (globalTable.spanCandidateTraceResultAtSegments summary segments
            macroStart level).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      globalTable.readBlockTraceResultAtSegment_matchesReadStore
        segments.globalBlock segments.deadSegment store hglobal
        macroStart level
  · cases hblock :
      (globalTable.readBlockTraceResultAtSegment segments.globalBlock
        segments.deadSegment macroStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some block =>
        exact
          summary.minCandidateTraceResultAtSegments_matchesReadStore
            segments.summary store hbaseline hminRel hmaxRel hargOffset
            block

theorem PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_matchesReadStore
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
              segments.summary.argOffset segments.summary.deadSegment
              segment) index =
          summary.argOffsetTable.wordRAMStore.readWord? segment index)
    (macroStart macroSpanCount : Nat) :
    forall event,
      List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
        event.matchesReadStore store := by
  unfold PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      globalTable.spanCandidateTraceResultAtSegments_matchesReadStore
        summary segments store hglobal hbaseline hminRel hmaxRel hargOffset
        macroStart (Nat.log2 macroSpanCount)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      globalTable.spanCandidateTraceResultAtSegments_matchesReadStore
        summary segments store hglobal hbaseline hminRel hmaxRel hargOffset
        (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
        (Nat.log2 macroSpanCount)

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_matchesReadStore
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          event.matchesReadStore store)
    (macroStart localStart rightCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
            localTable summary segments macroStart localStart rightCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hlocalSpan (macroStart + 1) 0 rightCount

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_matchesReadStore
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          event.matchesReadStore store)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          event.matchesReadStore store)
    (macroStart localStart middleMacroCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hglobalSpan (macroStart + 1) middleMacroCount

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegments_matchesReadStore
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          event.matchesReadStore store)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          event.matchesReadStore store)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelCrossMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount rightCount).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact hglobalSpan (macroStart + 1) middleMacroCount
    · apply WordRAM.TraceResult.map_trace_forall
      exact hlocalSpan (macroStart + 1 + middleMacroCount) 0 rightCount

theorem bpTwoLevelInteriorCandidateTraceResultAtSegments_matchesReadStore
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          event.matchesReadStore store)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          event.matchesReadStore store)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelInteriorCandidateTraceResultAtSegments localTable
            globalTable summary segments startBlock count).trace ->
        event.matchesReadStore store := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegments
  by_cases hcount : count = 0
  · simp [hcount]
    exact
      WordRAM.TraceResult.pure_trace_forall
        (fun event => event.matchesReadStore store)
        (none : Option (Nat × Nat))
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      exact hlocalSpan (startBlock / macroSize)
        (startBlock % macroSize) count
    · simp [hwithin]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        exact
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_matchesReadStore
            localTable summary segments store hlocalSpan
            (startBlock / macroSize) (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0
        · simp [hright]
          exact
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_matchesReadStore
              localTable globalTable summary segments store
              hlocalSpan hglobalSpan (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
        · simp [hright]
          exact
            bpTwoLevelCrossMacroCandidateTraceResultAtSegments_matchesReadStore
            localTable globalTable summary segments store
            hlocalSpan hglobalSpan (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) / macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) :
    forall event,
      List.Mem event
          (table.summaryTraceResultAtSegments segments block).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.summaryTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      table.baselineTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segments.baseline segments.deadSegment (block / blocksPerSuper)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        table.minRelTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
          segments.minRel segments.deadSegment block
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          table.maxRelTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
            segments.maxRel segments.deadSegment block
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          table.argOffsetTable.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
            segments.argOffset segments.deadSegment block

theorem PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (segments : BPRelativeSummaryTraceSegments)
    (block : Nat) :
    forall event,
      List.Mem event
          (table.minCandidateTraceResultAtSegments segments block).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPRelativeMinMaxArgSummaryTable.minCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.map_trace_forall
  exact
    table.summaryTraceResultAtSegments_no_syntheticCostOnlyPrimitive
      segments block

theorem PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (segmentBase deadSegment : Nat)
    (macroIdx localStart level : Nat) :
    forall event,
      List.Mem event
          (offsetTable.readOffsetTraceResultAtSegment segmentBase deadSegment
            macroIdx localStart level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPLocalSparseOffsetTable.readOffsetTraceResultAtSegment
  exact
    offsetTable.table.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
      segmentBase deadSegment
      (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (macroIdx localStart level : Nat) :
    forall event,
      List.Mem event
          (offsetTable.spanCandidateTraceResultAtSegments summary segments
            macroIdx localStart level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPLocalSparseOffsetTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      offsetTable.readOffsetTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segments.localOffset segments.deadSegment macroIdx localStart level
  · cases hoff :
      (offsetTable.readOffsetTraceResultAtSegment segments.localOffset
        segments.deadSegment macroIdx localStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some offset =>
        exact
          summary.minCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
            segments.summary (macroIdx * macroSize + offset)

theorem PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (macroIdx localStart count : Nat) :
    forall event,
      List.Mem event
          (offsetTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      offsetTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
        summary segments macroIdx localStart (Nat.log2 count)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      offsetTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
        summary segments macroIdx (localStart + count - bpSparseLogSpan count)
        (Nat.log2 count)

theorem PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (segmentBase deadSegment : Nat)
    (macroStart level : Nat) :
    forall event,
      List.Mem event
          (globalTable.readBlockTraceResultAtSegment segmentBase deadSegment
            macroStart level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPGlobalSparseBlockTable.readBlockTraceResultAtSegment
  exact
    globalTable.table.readTraceResultAtSegment_no_syntheticCostOnlyPrimitive
      segmentBase deadSegment
      (bpGlobalSparseCellSlot macroCount macroStart level)

theorem PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (macroStart level : Nat) :
    forall event,
      List.Mem event
          (globalTable.spanCandidateTraceResultAtSegments summary segments
            macroStart level).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPGlobalSparseBlockTable.spanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      globalTable.readBlockTraceResultAtSegment_no_syntheticCostOnlyPrimitive
        segments.globalBlock segments.deadSegment macroStart level
  · cases hblock :
      (globalTable.readBlockTraceResultAtSegment segments.globalBlock
        segments.deadSegment macroStart level).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some block =>
        exact
          summary.minCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
            segments.summary block

theorem PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (macroStart macroSpanCount : Nat) :
    forall event,
      List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      globalTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
        summary segments macroStart (Nat.log2 macroSpanCount)
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      globalTable.spanCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
        summary segments
        (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
        (Nat.log2 macroSpanCount)

theorem bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (macroStart localStart rightCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
            localTable summary segments macroStart localStart rightCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hlocalSpan (macroStart + 1) 0 rightCount

theorem bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (macroStart localStart middleMacroCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.map_trace_forall
    exact hglobalSpan (macroStart + 1) middleMacroCount

theorem bpTwoLevelCrossMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelCrossMacroCandidateTraceResultAtSegments
            localTable globalTable summary segments macroStart localStart
            middleMacroCount rightCount).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelCrossMacroCandidateTraceResultAtSegments
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hlocalSpan macroStart localStart (macroSize - localStart)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact hglobalSpan (macroStart + 1) middleMacroCount
    · apply WordRAM.TraceResult.map_trace_forall
      exact hlocalSpan (macroStart + 1 + middleMacroCount) 0 rightCount

theorem bpTwoLevelInteriorCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
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
    (hlocalSpan :
      forall macroIdx localStart count event,
        List.Mem event
          (localTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroIdx localStart count).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (hglobalSpan :
      forall macroStart macroSpanCount event,
        List.Mem event
          (globalTable.twoSpanCandidateTraceResultAtSegments summary
            segments macroStart macroSpanCount).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (bpTwoLevelInteriorCandidateTraceResultAtSegments localTable
            globalTable summary segments startBlock count).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold bpTwoLevelInteriorCandidateTraceResultAtSegments
  by_cases hcount : count = 0
  · simp [hcount]
    exact
      WordRAM.TraceResult.pure_trace_forall
        (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
        (none : Option (Nat × Nat))
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      exact hlocalSpan (startBlock / macroSize)
        (startBlock % macroSize) count
    · simp [hwithin]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        exact
          bpTwoLevelAdjacentMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
            localTable summary segments hlocalSpan
            (startBlock / macroSize) (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0
        · simp [hright]
          exact
            bpTwoLevelLeftMiddleMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
              localTable globalTable summary segments
              hlocalSpan hglobalSpan (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
        · simp [hright]
          exact
            bpTwoLevelCrossMacroCandidateTraceResultAtSegments_no_syntheticCostOnlyPrimitive
              localTable globalTable summary segments
              hlocalSpan hglobalSpan (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) % macroSize)

end SuccinctClose
end RMQ

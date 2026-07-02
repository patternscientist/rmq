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

end FixedWidthNatTable

end SuccinctSpace

namespace SuccinctClose

open SuccinctSpace

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
    rfl
  · simp [summaryTraceResult, summaryCosted,
      FixedWidthNatTable.readTraceResult_refines_readCosted,
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

end PayloadLiveBPGlobalSparseBlockTable

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

end SuccinctClose
end RMQ

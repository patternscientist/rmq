import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.Candidate

/-!
# Endpoint-fringe local/global sparse candidate tables

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

namespace PayloadLiveBPLocalSparseOffsetTable

def twoSpanCandidateCosted
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
    (macroIdx localStart count : Nat) : Costed (Option (Nat × Nat)) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  let rightLocalStart := localStart + count - span
  Costed.bind
    (offsetTable.spanCandidateCosted summary macroIdx localStart level)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (offsetTable.spanCandidateCosted summary macroIdx rightLocalStart
          level)

theorem twoSpanCandidateCosted_cost_le_ten
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
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).cost <=
      10 := by
  unfold twoSpanCandidateCosted
  have hleft :=
    offsetTable.spanCandidateCosted_cost_le_five summary macroIdx localStart
      (Nat.log2 count)
  have hright :=
    offsetTable.spanCandidateCosted_cost_le_five summary macroIdx
      (localStart + count - bpSparseLogSpan count) (Nat.log2 count)
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem twoSpanCandidateCosted_erase_sparseLog_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < count)
    (hmacro : macroIdx < macroCount)
    (hlevel : Nat.log2 count < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalCount : localStart + count <= macroSize)
    (hblockCount :
      macroIdx * macroSize + localStart + count <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).erase =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize
              (macroIdx * macroSize + localStart) count)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize
              (macroIdx * macroSize + localStart) count)) := by
  let span := bpSparseLogSpan count
  let level := Nat.log2 count
  let startBlock := macroIdx * macroSize + localStart
  let rightLocalStart := localStart + count - span
  have hspanEq : span = 2 ^ level := by
    simp [span, level, bpSparseLogSpan]
  have hspanPos : 0 < span := by
    simpa [span] using bpSparseLogSpan_pos count
  have hspanLe : span <= count := by
    simpa [span] using bpSparseLogSpan_le_self hcount
  have hleftSpan : localStart + 2 ^ level <= macroSize := by
    omega
  have hleftBlock : macroIdx * macroSize + localStart + 2 ^ level <= blockCount := by
    omega
  have hrightLocal : rightLocalStart < macroSize := by
    have hrightSpan : rightLocalStart + span <= macroSize := by
      omega
    omega
  have hrightSpan : rightLocalStart + 2 ^ level <= macroSize := by
    omega
  have hrightBlock :
      macroIdx * macroSize + rightLocalStart + 2 ^ level <= blockCount := by
    omega
  have hrightStart :
      macroIdx * macroSize + rightLocalStart =
        startBlock + count - span := by
    omega
  have hleftExact :=
    offsetTable.spanCandidateCosted_erase_exact
      summary hmacro hlevel hlocal hleftSpan hleftBlock hblocks hcover
      hsuperCount
  have hrightExact :=
    offsetTable.spanCandidateCosted_erase_exact
      summary hmacro hlevel hrightLocal hrightSpan hrightBlock hblocks
      hcover hsuperCount
  have hrightErase :
      (offsetTable.spanCandidateCosted summary macroIdx
          (localStart + count - bpSparseLogSpan count)
          (Nat.log2 count)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroIdx * macroSize +
              (localStart + count - bpSparseLogSpan count))
            (2 ^ Nat.log2 count),
            bpRangeArgMinPrefixPos shape blockSize
              (macroIdx * macroSize +
                (localStart + count - bpSparseLogSpan count))
              (2 ^ Nat.log2 count)) := by
    simpa [span, level, rightLocalStart] using hrightExact
  have hmerge :=
    bpCandidateMerge?_bpSparseLogSpanArgMinBlock
      shape blockSize startBlock count hcount
  unfold twoSpanCandidateCosted
  rw [Costed.erase_bind]
  simp [hleftExact]
  simp [Costed.map, hrightErase]
  simpa [span, level, startBlock, rightLocalStart, hrightStart] using hmerge

theorem twoSpanCandidateCosted_erase_rangeWitness_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < count)
    (hmacro : macroIdx < macroCount)
    (hlevel : Nat.log2 count < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalCount : localStart + count <= macroSize)
    (hblockCount :
      macroIdx * macroSize + localStart + count <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroIdx * macroSize + localStart) count,
          bpRangeArgMinPrefixPos shape blockSize
            (macroIdx * macroSize + localStart) count) := by
  have hselector :=
    offsetTable.twoSpanCandidateCosted_erase_sparseLog_exact
      summary hcount hmacro hlevel hlocal hlocalCount hblockCount
      hblocks hcover hsuperCount
  have hwitness :=
    bpRangeWitness_eq_of_bpSparseLogSpanArgMinBlock
      shape blockSize (macroIdx * macroSize + localStart) count hcount
  simpa [hwitness] using hselector

end PayloadLiveBPLocalSparseOffsetTable

def bpGlobalSparseCellSlot
    (macroCount macroStart level : Nat) : Nat :=
  level * macroCount + macroStart

def bpGlobalSparseCellBlock
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount macroStart level : Nat) :
    Nat :=
  let spanMacros := 2 ^ level
  let startBlock := macroStart * macroSize
  let spanBlocks := spanMacros * macroSize
  if macroStart + spanMacros <= macroCount ∧ startBlock + spanBlocks <= blockCount then
    bpRangeArgMinBlock shape blockSize startBlock spanBlocks
  else
    0

def bpGlobalSparseBlockEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    List Nat :=
  (List.range (levelCount * macroCount)).map fun slot =>
    let level := slot / macroCount
    let macroStart := slot % macroCount
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level

theorem bpGlobalSparseCellSlot_lt
    {macroCount levelCount macroStart level : Nat}
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level <
      levelCount * macroCount := by
  unfold bpGlobalSparseCellSlot
  have hstep :
      level * macroCount + macroStart <
        level * macroCount + macroCount :=
    Nat.add_lt_add_left hmacro (level * macroCount)
  have hsucc :
      level * macroCount + macroCount =
        (level + 1) * macroCount := by
    simpa using (Nat.succ_mul level macroCount).symm
  have hmul :
      (level + 1) * macroCount <= levelCount * macroCount :=
    Nat.mul_le_mul_right macroCount (Nat.succ_le_of_lt hlevel)
  exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul

theorem bpGlobalSparseCellSlot_div
    {macroCount levelCount macroStart level : Nat}
    (_hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level / macroCount =
      level := by
  have hpos : 0 < macroCount := by omega
  unfold bpGlobalSparseCellSlot
  rw [Nat.mul_comm level macroCount]
  rw [Nat.mul_add_div hpos]
  rw [Nat.div_eq_of_lt hmacro]
  omega

theorem bpGlobalSparseCellSlot_mod
    {macroCount levelCount macroStart level : Nat}
    (_hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level % macroCount =
      macroStart := by
  unfold bpGlobalSparseCellSlot
  rw [Nat.mul_comm level macroCount]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hmacro

theorem bpGlobalSparseBlockEntries_get?_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      macroStart level : Nat}
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount)[
          bpGlobalSparseCellSlot macroCount macroStart level]? =
      some
        (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
          macroCount macroStart level) := by
  have hslot :
      bpGlobalSparseCellSlot macroCount macroStart level <
        levelCount * macroCount :=
    bpGlobalSparseCellSlot_lt hlevel hmacro
  have hget :
      (List.range (levelCount * macroCount))[
          bpGlobalSparseCellSlot macroCount macroStart level]? =
        some (bpGlobalSparseCellSlot macroCount macroStart level) :=
    List.getElem?_range hslot
  have hdiv :=
    bpGlobalSparseCellSlot_div
      (levelCount := levelCount) hlevel hmacro
  have hmod :=
    bpGlobalSparseCellSlot_mod
      (levelCount := levelCount) hlevel hmacro
  let slot := bpGlobalSparseCellSlot macroCount macroStart level
  have hgetSlot :
      (List.range (levelCount * macroCount))[slot]? = some slot := by
    simpa [slot] using hget
  have hmap :
      ((List.range (levelCount * macroCount)).map
          (fun slot =>
            bpGlobalSparseCellBlock shape blockSize blockCount macroSize
              macroCount (slot % macroCount) (slot / macroCount)))[slot]? =
        some
          (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
            macroCount (slot % macroCount) (slot / macroCount)) := by
    rw [List.getElem?_map]
    simp [hgetSlot]
  simpa [bpGlobalSparseBlockEntries, slot, hdiv, hmod] using hmap

theorem bpGlobalSparseCellBlock_valid_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount macroStart level : Nat}
    (hmacroSpan : macroStart + 2 ^ level <= macroCount)
    (hblockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount) :
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
        macroStart level =
      bpRangeArgMinBlock shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) := by
  simp [bpGlobalSparseCellBlock, hmacroSpan, hblockSpan]

theorem bpGlobalSparseCellBlock_lt_width
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount macroStart level
      blockWidth : Nat}
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth) :
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
        macroStart level <
      2 ^ blockWidth := by
  unfold bpGlobalSparseCellBlock
  by_cases hvalid :
      macroStart + 2 ^ level <= macroCount /\
        macroStart * macroSize + 2 ^ level * macroSize <= blockCount
  · simp [hvalid]
    have hspan : 0 < 2 ^ level * macroSize := by
      exact Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) hmacroSize
    have hmem :=
      bpRangeArgMinBlock_mem shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) hspan
    exact Nat.lt_trans (by omega : bpRangeArgMinBlock shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) < blockCount)
      hwidth
  · have hpow : 0 < 2 ^ blockWidth := by
      exact Nat.pow_pos (by omega : 0 < 2)
    simp [hvalid, hpow]

theorem bpGlobalSparseBlockEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth entry : Nat}
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth)
    (hmem :
      entry ∈
        bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount) :
    entry < 2 ^ blockWidth := by
  unfold bpGlobalSparseBlockEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, hentry⟩
  rw [← hentry]
  exact
    bpGlobalSparseCellBlock_lt_width
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (macroStart := slot % macroCount)
      (level := slot / macroCount) (blockWidth := blockWidth)
      hmacroSize hwidth

structure PayloadLiveBPGlobalSparseBlockTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat) where
  table :
    FixedWidthNatTable
      (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount) blockWidth
  payload_length_eq : table.payload.length = overhead

namespace PayloadLiveBPGlobalSparseBlockTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead) :
    List Bool :=
  globalTable.table.payload

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead) :
    globalTable.payload.length = overhead := by
  exact globalTable.payload_length_eq

def readBlockCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : Costed (Option Nat) :=
  globalTable.table.readCosted
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) :
    (globalTable.readBlockCosted macroStart level).cost <= 1 := by
  unfold readBlockCosted
  exact globalTable.table.readCosted_cost_le_one
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockCosted_erase_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    (globalTable.readBlockCosted macroStart level).erase =
      some
        (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
          macroCount macroStart level) := by
  have hentry :=
    bpGlobalSparseBlockEntries_get?_of_valid
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (levelCount := levelCount)
      (macroStart := macroStart) (level := level) hlevel hmacro
  unfold readBlockCosted
  simpa using
    (show
      (globalTable.table.readCosted
          (bpGlobalSparseCellSlot macroCount macroStart level)).erase =
        (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount)[
            bpGlobalSparseCellSlot macroCount macroStart level]? from
      globalTable.table.readCosted_erase
        (bpGlobalSparseCellSlot macroCount macroStart level)).trans hentry

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead index : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hmachine :
      blockWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hword : globalTable.table.store.words[index]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlen := globalTable.table.read_word_length_of_some hword
  omega

def spanCandidateCosted
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
    (macroStart level : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (globalTable.readBlockCosted macroStart level) fun block? =>
    match block? with
    | some block => summary.minCandidateCosted block
    | none => Costed.pure none

theorem spanCandidateCosted_cost_le_five
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
    (globalTable.spanCandidateCosted summary macroStart level).cost <= 5 := by
  unfold spanCandidateCosted
  cases hblock :
      (globalTable.readBlockCosted macroStart level).value with
  | none =>
      have hread :=
        globalTable.readBlockCosted_cost_le_one macroStart level
      simp [Costed.bind, Costed.pure, hblock] at hread ⊢
      omega
  | some block =>
      have hread :=
        globalTable.readBlockCosted_cost_le_one macroStart level
      have hsummary := summary.minCandidateCosted_cost_le_four block
      simp [Costed.bind, hblock] at hread hsummary ⊢
      omega

theorem spanCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroSize : 0 < macroSize)
    (hmacroSpan : macroStart + 2 ^ level <= macroCount)
    (hblockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.spanCandidateCosted summary macroStart level).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize) (2 ^ level * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize) (2 ^ level * macroSize)) := by
  let block :=
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level
  have hblockRead :
      (globalTable.readBlockCosted macroStart level).erase =
        some block := by
    simpa [block] using
      globalTable.readBlockCosted_erase_of_valid hlevel hmacro
  have hblockEq :
      block =
        bpRangeArgMinBlock shape blockSize
          (macroStart * macroSize) (2 ^ level * macroSize) := by
    simpa [block] using
      bpGlobalSparseCellBlock_valid_eq
        (shape := shape) (blockSize := blockSize)
        (blockCount := blockCount) (macroSize := macroSize)
        (macroCount := macroCount) (macroStart := macroStart)
        (level := level) hmacroSpan hblockSpan
  have hspan : 0 < 2 ^ level * macroSize := by
    exact Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) hmacroSize
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroStart * macroSize) (2 ^ level * macroSize) hspan
  have hblockLt : block < blockCount := by
    rw [hblockEq]
    omega
  have hsummary :=
    summary.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblockLt hcover (hsuperCount hblockLt)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize (macroStart * macroSize)
      (2 ^ level * macroSize) hspan
  unfold spanCandidateCosted
  rw [Costed.erase_bind]
  simp [hblockRead]
  simpa [hblockEq, hwitness] using hsummary

def twoSpanCandidateCosted
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
    (macroStart macroSpanCount : Nat) : Costed (Option (Nat × Nat)) :=
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  Costed.bind
    (globalTable.spanCandidateCosted summary macroStart level)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (globalTable.spanCandidateCosted summary rightMacroStart level)

theorem twoSpanCandidateCosted_cost_le_ten
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
    (globalTable.twoSpanCandidateCosted summary macroStart
      macroSpanCount).cost <= 10 := by
  unfold twoSpanCandidateCosted
  have hleft :=
    globalTable.spanCandidateCosted_cost_le_five summary macroStart
      (Nat.log2 macroSpanCount)
  have hright :=
    globalTable.spanCandidateCosted_cost_le_five summary
      (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
      (Nat.log2 macroSpanCount)
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem twoSpanCandidateCosted_erase_sparse_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < macroSpanCount)
    (hmacroSize : 0 < macroSize)
    (hlevel : Nat.log2 macroSpanCount < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroCount : macroStart + macroSpanCount <= macroCount)
    (hblockCount : macroStart * macroSize + macroSpanCount * macroSize <=
      blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount).erase =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize
              (macroStart * macroSize) (macroSpanCount * macroSize)
              (bpSparseLogSpan macroSpanCount * macroSize))),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize
              (macroStart * macroSize) (macroSpanCount * macroSize)
              (bpSparseLogSpan macroSpanCount * macroSize))) := by
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  have hspanMacrosPos : 0 < spanMacros := by
    simpa [spanMacros] using bpSparseLogSpan_pos macroSpanCount
  have hspanMacrosLe : spanMacros <= macroSpanCount := by
    simpa [spanMacros] using bpSparseLogSpan_le_self hcount
  have hspanBlocksPos : 0 < spanMacros * macroSize := by
    exact Nat.mul_pos hspanMacrosPos hmacroSize
  have hspanEq : spanMacros = 2 ^ level := by
    simp [spanMacros, level, bpSparseLogSpan]
  have hleftMacroSpan : macroStart + 2 ^ level <= macroCount := by
    rw [← hspanEq]
    omega
  have hleftBlockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount := by
    rw [← hspanEq]
    have hspanBlocksLe :
        spanMacros * macroSize <= macroSpanCount * macroSize :=
      Nat.mul_le_mul_right macroSize hspanMacrosLe
    omega
  have hrightMacro : rightMacroStart < macroCount := by
    have hrightSpan : rightMacroStart + spanMacros <= macroCount := by
      omega
    omega
  have hrightMacroSpan :
      rightMacroStart + 2 ^ level <= macroCount := by
    rw [← hspanEq]
    omega
  have hrightBlockSpan :
      rightMacroStart * macroSize + 2 ^ level * macroSize <=
        blockCount := by
    rw [← hspanEq]
    have hrightEnd :
        rightMacroStart * macroSize + spanMacros * macroSize =
          macroStart * macroSize + macroSpanCount * macroSize := by
      have hrightAdd : rightMacroStart + spanMacros =
          macroStart + macroSpanCount := by
        omega
      calc
        rightMacroStart * macroSize + spanMacros * macroSize =
            (rightMacroStart + spanMacros) * macroSize := by
          rw [Nat.add_mul]
        _ = (macroStart + macroSpanCount) * macroSize := by
          rw [hrightAdd]
        _ = macroStart * macroSize + macroSpanCount * macroSize := by
          rw [Nat.add_mul]
    simpa [hrightEnd] using hblockCount
  have hrightStart :
      rightMacroStart * macroSize =
        macroStart * macroSize + macroSpanCount * macroSize -
          spanMacros * macroSize := by
    have hrightEnd :
        rightMacroStart * macroSize + spanMacros * macroSize =
          macroStart * macroSize + macroSpanCount * macroSize := by
      have hrightAdd : rightMacroStart + spanMacros =
          macroStart + macroSpanCount := by
        omega
      calc
        rightMacroStart * macroSize + spanMacros * macroSize =
            (rightMacroStart + spanMacros) * macroSize := by
          rw [Nat.add_mul]
        _ = (macroStart + macroSpanCount) * macroSize := by
          rw [hrightAdd]
        _ = macroStart * macroSize + macroSpanCount * macroSize := by
          rw [Nat.add_mul]
    omega
  have hleftExact :=
    globalTable.spanCandidateCosted_erase_exact
      summary hlevel hmacro hmacroSize hleftMacroSpan hleftBlockSpan
      hblocks hcover hsuperCount
  have hrightExact :=
    globalTable.spanCandidateCosted_erase_exact
      summary hlevel hrightMacro hmacroSize hrightMacroSpan
      hrightBlockSpan hblocks hcover hsuperCount
  have hrightErase :
      (globalTable.spanCandidateCosted summary
          (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
          (Nat.log2 macroSpanCount)).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + macroSpanCount -
              bpSparseLogSpan macroSpanCount) * macroSize)
            (2 ^ Nat.log2 macroSpanCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + macroSpanCount -
                bpSparseLogSpan macroSpanCount) * macroSize)
              (2 ^ Nat.log2 macroSpanCount * macroSize)) := by
    simpa [rightMacroStart, spanMacros, level] using hrightExact
  have hmerge :=
    bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
      shape blockSize (macroStart * macroSize)
      (macroSpanCount * macroSize) (spanMacros * macroSize)
      hspanBlocksPos
  unfold twoSpanCandidateCosted
  rw [Costed.erase_bind]
  simp [hleftExact]
  simp [Costed.map, hrightErase]
  simpa [spanMacros, level, rightMacroStart, hrightStart,
    Nat.mul_assoc] using hmerge

theorem twoSpanCandidateCosted_erase_rangeWitness_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < macroSpanCount)
    (hmacroSize : 0 < macroSize)
    (hlevel : Nat.log2 macroSpanCount < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroCount : macroStart + macroSpanCount <= macroCount)
    (hblockCount : macroStart * macroSize + macroSpanCount * macroSize <=
      blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize) (macroSpanCount * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize) (macroSpanCount * macroSize)) := by
  let spanMacros := bpSparseLogSpan macroSpanCount
  have hselector :=
    globalTable.twoSpanCandidateCosted_erase_sparse_exact
      summary hcount hmacroSize hlevel hmacro hmacroCount hblockCount
      hblocks hcover hsuperCount
  have hspanPos : 0 < spanMacros * macroSize := by
    exact Nat.mul_pos
      (by simpa [spanMacros] using bpSparseLogSpan_pos macroSpanCount)
      hmacroSize
  have hspanLe : spanMacros * macroSize <= macroSpanCount * macroSize :=
    Nat.mul_le_mul_right macroSize
      (by simpa [spanMacros] using bpSparseLogSpan_le_self hcount)
  have hcoverSpan :
      macroSpanCount * macroSize <= 2 * (spanMacros * macroSize) := by
    have hmacroCover :
        macroSpanCount <= 2 * spanMacros := by
      simpa [spanMacros] using self_le_two_mul_bpSparseLogSpan hcount
    have hmul :=
      Nat.mul_le_mul_right macroSize hmacroCover
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hwitness :=
    bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
      shape blockSize (macroStart * macroSize)
      (macroSpanCount * macroSize) (spanMacros * macroSize)
      hspanPos hspanLe hcoverSpan
  simpa [spanMacros, hwitness] using hselector

end PayloadLiveBPGlobalSparseBlockTable

theorem bpLocalSparseOffsetEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
      macroCount levelCount).length =
      macroCount * (levelCount * macroSize) := by
  simp [bpLocalSparseOffsetEntries]

def concreteBPLocalSparseOffsetTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      offsetWidth : Nat)
    (hwidth : macroSize < 2 ^ offsetWidth) :
    PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
      macroSize macroCount levelCount offsetWidth
      ((macroCount * (levelCount * macroSize)) * offsetWidth) where
  table :=
    FixedWidthNatTable.ofEntries
      (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount) offsetWidth
      (bpLocalSparseOffsetEntries_mem_bound hwidth)
  payload_length_eq := by
    simpa [bpLocalSparseOffsetEntries_length] using
      (FixedWidthNatTable.ofEntries
        (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount) offsetWidth
        (bpLocalSparseOffsetEntries_mem_bound hwidth)).payload_length

theorem bpGlobalSparseBlockEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
      macroCount levelCount).length =
      levelCount * macroCount := by
  simp [bpGlobalSparseBlockEntries]

def concreteBPGlobalSparseBlockTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      blockWidth : Nat)
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth) :
    PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
      macroSize macroCount levelCount blockWidth
      ((levelCount * macroCount) * blockWidth) where
  table :=
    FixedWidthNatTable.ofEntries
      (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount) blockWidth
      (bpGlobalSparseBlockEntries_mem_bound hmacroSize hwidth)
  payload_length_eq := by
    simpa [bpGlobalSparseBlockEntries_length] using
      (FixedWidthNatTable.ofEntries
        (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount) blockWidth
        (bpGlobalSparseBlockEntries_mem_bound hmacroSize hwidth)).payload_length

def bpTwoLevelCrossMacroCandidateCosted
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
    Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.bind
        (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount)
        fun middle? =>
          Costed.map
            (fun right? => bpCandidateMerge3? left? middle? right?)
            (localTable.twoSpanCandidateCosted summary rightMacroStart 0
              rightCount)

def bpTwoLevelAdjacentMacroCandidateCosted
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
    (macroStart localStart rightCount : Nat) : Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (localTable.twoSpanCandidateCosted summary (macroStart + 1) 0
          rightCount)

theorem bpTwoLevelAdjacentMacroCandidateCosted_cost_le_twenty
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
    (bpTwoLevelAdjacentMacroCandidateCosted localTable summary macroStart
      localStart rightCount).cost <= 20 := by
  unfold bpTwoLevelAdjacentMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hright :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      0 rightCount
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem bpTwoLevelAdjacentMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead macroStart localStart
      rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hrightCount : 0 < rightCount)
    (hrightLe : rightCount <= macroSize)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hrightLevel : Nat.log2 rightCount < localLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hrightMacro : macroStart + 1 < macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          rightCount <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelAdjacentMacroCandidateCosted localTable summary macroStart
        localStart rightCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) + rightCount),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) + rightCount)) := by
  let leftCount := macroSize - localStart
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hrightBlockCount :
      (macroStart + 1) * macroSize + rightCount <= blockCount := by
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hrightExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hrightCount hrightMacro hrightLevel
      (by omega : 0 < macroSize)
      (by simpa using hrightLe)
      hrightBlockCount hblocks hcover hsuperCount
  have hrightErase :
      (localTable.twoSpanCandidateCosted summary (macroStart + 1) 0
          rightCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize) rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize) rightCount) := by
    simpa using hrightExact
  have hmerge :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount rightCount
      hleftCount hrightCount
  unfold bpTwoLevelAdjacentMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hrightErase]
  simpa [startBlock, leftCount, hleftEnd, Nat.add_assoc] using hmerge

def bpTwoLevelLeftMiddleMacroCandidateCosted
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
    Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.map
        (fun middle? => bpCandidateMerge? left? middle?)
        (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount)

theorem bpTwoLevelLeftMiddleMacroCandidateCosted_cost_le_twenty
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
    (bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
      summary macroStart localStart middleMacroCount).cost <= 20 := by
  unfold bpTwoLevelLeftMiddleMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hmiddle :=
    globalTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      middleMacroCount
  simp [Costed.bind, Costed.map] at hleft hmiddle ⊢
  omega

theorem bpTwoLevelLeftMiddleMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount : Nat}
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
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hmiddleCount : 0 < middleMacroCount)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hmiddleLevel : Nat.log2 middleMacroCount < globalLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hmiddleEnd : macroStart + 1 + middleMacroCount <= macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          middleMacroCount * macroSize <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
        summary macroStart localStart middleMacroCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) + middleMacroCount * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) + middleMacroCount * macroSize)) := by
  let leftCount := macroSize - localStart
  let middleCount := middleMacroCount * macroSize
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hmiddleBlocks : 0 < middleCount := by
    exact Nat.mul_pos hmiddleCount hmacroSize
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hmiddleBlockCount :
      (macroStart + 1) * macroSize + middleMacroCount * macroSize <=
        blockCount := by
    have hmidEnd :
        (macroStart + 1) * macroSize + middleMacroCount * macroSize =
          macroStart * macroSize + (macroSize - localStart) +
              middleMacroCount * macroSize + localStart := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      omega
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hmiddleExact :=
    globalTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hmiddleCount hmacroSize hmiddleLevel
      (by omega : macroStart + 1 < macroCount)
      hmiddleEnd hmiddleBlockCount hblocks hcover hsuperCount
  have hmiddleErase :
      (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize)
            (middleMacroCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize)
              (middleMacroCount * macroSize)) := by
    simpa [middleCount] using hmiddleExact
  have hmerge :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount middleCount
      hleftCount hmiddleBlocks
  unfold bpTwoLevelLeftMiddleMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hmiddleErase]
  simpa [startBlock, leftCount, middleCount, hleftEnd, Nat.add_assoc] using
    hmerge

theorem bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
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
    (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
      macroStart localStart middleMacroCount rightCount).cost <= 30 := by
  unfold bpTwoLevelCrossMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hmiddle :=
    globalTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      middleMacroCount
  have hright :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary
      (macroStart + 1 + middleMacroCount) 0 rightCount
  simp [Costed.bind, Costed.map] at hleft hmiddle hright ⊢
  omega

theorem bpTwoLevelCrossMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount
      rightCount : Nat}
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
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hmiddleCount : 0 < middleMacroCount)
    (hrightCount : 0 < rightCount)
    (hrightLe : rightCount <= macroSize)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hmiddleLevel : Nat.log2 middleMacroCount < globalLevelCount)
    (hrightLevel : Nat.log2 rightCount < localLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hrightMacro : macroStart + 1 + middleMacroCount < macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          middleMacroCount * macroSize + rightCount <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
        macroStart localStart middleMacroCount rightCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) +
            middleMacroCount * macroSize + rightCount),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) +
              middleMacroCount * macroSize + rightCount)) := by
  let leftCount := macroSize - localStart
  let middleCount := middleMacroCount * macroSize
  let rightMacroStart := macroStart + 1 + middleMacroCount
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hmiddleBlocks : 0 < middleCount := by
    exact Nat.mul_pos hmiddleCount hmacroSize
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hrightStartEq :
      (macroStart + 1) * macroSize + middleCount =
        rightMacroStart * macroSize := by
    unfold middleCount rightMacroStart
    rw [← Nat.add_mul]
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hmiddleBlockCount :
      (macroStart + 1) * macroSize + middleMacroCount * macroSize <=
        blockCount := by
    have hmidEnd :
        (macroStart + 1) * macroSize + middleMacroCount * macroSize =
          macroStart * macroSize + (macroSize - localStart) +
              middleMacroCount * macroSize + localStart := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      omega
    omega
  have hrightBlockCount :
      rightMacroStart * macroSize + rightCount <= blockCount := by
    have hrightStart' :
        rightMacroStart * macroSize =
          (macroStart + 1) * macroSize + middleMacroCount * macroSize := by
      simpa [rightMacroStart] using hrightStartEq.symm
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hmiddleExact :=
    globalTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hmiddleCount hmacroSize hmiddleLevel
      (by omega : macroStart + 1 < macroCount)
      (by omega : macroStart + 1 + middleMacroCount <= macroCount)
      hmiddleBlockCount hblocks hcover hsuperCount
  have hmiddleErase :
      (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize)
            (middleMacroCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize)
              (middleMacroCount * macroSize)) := by
    simpa using hmiddleExact
  have hrightExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hrightCount
      (by simpa [rightMacroStart] using hrightMacro)
      hrightLevel
      (by omega : 0 < macroSize)
      (by simpa using hrightLe)
      (by
        simpa [rightMacroStart] using hrightBlockCount)
      hblocks hcover hsuperCount
  have hrightErase :
      (localTable.twoSpanCandidateCosted summary
          (macroStart + 1 + middleMacroCount) 0 rightCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1 + middleMacroCount) * macroSize)
            rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1 + middleMacroCount) * macroSize)
              rightCount) := by
    simpa [rightMacroStart] using hrightExact
  have hmerge :=
    bpCandidateMerge3?_threeAdjacentRangeWitness
      shape blockSize startBlock leftCount middleCount rightCount
      hleftCount hmiddleBlocks hrightCount
  unfold bpTwoLevelCrossMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hmiddleErase,
    hrightErase]
  simpa [startBlock, leftCount, middleCount, rightMacroStart, hleftEnd,
    hrightStartEq, Nat.add_assoc] using hmerge

end SuccinctCloseProposal
end RMQ

import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseArgMin

/-!
# Local sparse offset table

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def bpLocalSparseCellSlot
    (macroSize levelCount macroIdx localStart level : Nat) : Nat :=
  macroIdx * (levelCount * macroSize) + level * macroSize + localStart

def bpLocalSparseCellOffset
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroIdx localStart level : Nat) :
    Nat :=
  let span := 2 ^ level
  let macroStart := macroIdx * macroSize
  let startBlock := macroStart + localStart
  if localStart + span <= macroSize ∧ startBlock + span <= blockCount then
    bpRangeArgMinBlock shape blockSize startBlock span - macroStart
  else
    0

def bpLocalSparseOffsetEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    List Nat :=
  (List.range (macroCount * (levelCount * macroSize))).map fun slot =>
    let perMacro := levelCount * macroSize
    let macroIdx := slot / perMacro
    let rem := slot % perMacro
    let level := rem / macroSize
    let localStart := rem % macroSize
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level

theorem bpLocalSparseCellSlot_lt
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level <
      macroCount * (levelCount * macroSize) := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  have hslot :
      macroIdx * (levelCount * macroSize) +
          (level * macroSize + localStart) <
        macroIdx * (levelCount * macroSize) +
          (levelCount * macroSize) :=
    Nat.add_lt_add_left hcell (macroIdx * (levelCount * macroSize))
  have hsucc :
      macroIdx * (levelCount * macroSize) +
          levelCount * macroSize =
        (macroIdx + 1) * (levelCount * macroSize) := by
    simpa using
      (Nat.succ_mul macroIdx (levelCount * macroSize)).symm
  have hmul :
      (macroIdx + 1) * (levelCount * macroSize) <=
        macroCount * (levelCount * macroSize) :=
    Nat.mul_le_mul_right (levelCount * macroSize)
      (Nat.succ_le_of_lt hmacro)
  exact Nat.lt_of_lt_of_le (by simpa [Nat.add_assoc, hsucc] using hslot) hmul

theorem bpLocalSparseCellSlot_div_perMacro
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (_hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level /
        (levelCount * macroSize) =
      macroIdx := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  have hpos : 0 < levelCount * macroSize := by omega
  rw [Nat.mul_comm macroIdx (levelCount * macroSize)]
  rw [Nat.add_assoc]
  rw [Nat.mul_add_div hpos]
  rw [Nat.div_eq_of_lt hcell]
  omega

theorem bpLocalSparseCellSlot_mod_perMacro
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (_hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize) =
      level * macroSize + localStart := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  rw [Nat.mul_comm macroIdx (levelCount * macroSize)]
  rw [Nat.add_assoc]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hcell

theorem bpLocalSparseCellSlot_rem_div
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize)) / macroSize =
      level := by
  have hrem :=
    bpLocalSparseCellSlot_mod_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hdiv :
      (level * macroSize + localStart) / macroSize = level := by
    have hpos : 0 < macroSize := by omega
    rw [Nat.mul_comm level macroSize]
    rw [Nat.mul_add_div hpos]
    rw [Nat.div_eq_of_lt hlocal]
    omega
  simpa [hrem] using hdiv

theorem bpLocalSparseCellSlot_rem_mod
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize)) % macroSize =
      localStart := by
  have hrem :=
    bpLocalSparseCellSlot_mod_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hmod :
      (level * macroSize + localStart) % macroSize = localStart := by
    rw [Nat.mul_comm level macroSize]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlocal
  simpa [hrem] using hmod

theorem bpLocalSparseOffsetEntries_get?_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount)[
          bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]? =
      some
        (bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level) := by
  have hslot :
      bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level <
        macroCount * (levelCount * macroSize) :=
    bpLocalSparseCellSlot_lt hmacro hlevel hlocal
  have hget :
      (List.range (macroCount * (levelCount * macroSize)))[
          bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]? =
        some
          (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level) :=
    List.getElem?_range hslot
  have hdiv :=
    bpLocalSparseCellSlot_div_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hremDiv :=
    bpLocalSparseCellSlot_rem_div
      (macroCount := macroCount) hmacro hlevel hlocal
  have hremMod :=
    bpLocalSparseCellSlot_rem_mod
      (macroCount := macroCount) hmacro hlevel hlocal
  let slot :=
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level
  have hgetSlot :
      (List.range (macroCount * (levelCount * macroSize)))[slot]? =
        some slot := by
    simpa [slot] using hget
  have hmap :
      ((List.range (macroCount * (levelCount * macroSize))).map
          (fun slot =>
            bpLocalSparseCellOffset shape blockSize blockCount macroSize
              (slot / (levelCount * macroSize))
              (slot % (levelCount * macroSize) % macroSize)
              (slot % (levelCount * macroSize) / macroSize)))[slot]? =
        some
          (bpLocalSparseCellOffset shape blockSize blockCount macroSize
            (slot / (levelCount * macroSize))
            (slot % (levelCount * macroSize) % macroSize)
            (slot % (levelCount * macroSize) / macroSize)) := by
    rw [List.getElem?_map]
    simp [hgetSlot]
  simpa [bpLocalSparseOffsetEntries, slot, hdiv, hremDiv, hremMod] using hmap

theorem bpLocalSparseCellOffset_valid_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level : Nat}
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount) :
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
        localStart level =
      bpRangeArgMinBlock shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level) -
        macroIdx * macroSize := by
  simp [bpLocalSparseCellOffset, hlocalSpan, hblockSpan]

theorem bpLocalSparseCellOffset_valid_add
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level : Nat}
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount) :
    macroIdx * macroSize +
        bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level =
      bpRangeArgMinBlock shape blockSize
        (macroIdx * macroSize + localStart) (2 ^ level) := by
  have hoffset :=
    bpLocalSparseCellOffset_valid_eq
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroIdx := macroIdx) (localStart := localStart) (level := level)
      hlocalSpan hblockSpan
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroIdx * macroSize + localStart) (2 ^ level)
      (Nat.pow_pos (by omega : 0 < 2))
  rw [hoffset]
  omega

theorem bpLocalSparseCellOffset_lt_width
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level
      offsetWidth : Nat}
    (hwidth : macroSize < 2 ^ offsetWidth) :
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
        localStart level <
      2 ^ offsetWidth := by
  unfold bpLocalSparseCellOffset
  by_cases hvalid :
      localStart + 2 ^ level <= macroSize /\
        macroIdx * macroSize + localStart + 2 ^ level <= blockCount
  · simp [hvalid]
    let startBlock := macroIdx * macroSize + localStart
    let span := 2 ^ level
    have hspan : 0 < span := by
      exact Nat.pow_pos (by omega : 0 < 2)
    have hmem :=
      bpRangeArgMinBlock_mem shape blockSize startBlock span hspan
    have hoff :
        bpRangeArgMinBlock shape blockSize startBlock span -
            macroIdx * macroSize <
          macroSize := by
      omega
    exact Nat.lt_trans hoff hwidth
  · have hpow : 0 < 2 ^ offsetWidth := by
      exact Nat.pow_pos (by omega : 0 < 2)
    simp [hvalid, hpow]

theorem bpLocalSparseOffsetEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth entry : Nat}
    (hwidth : macroSize < 2 ^ offsetWidth)
    (hmem :
      entry ∈
        bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount) :
    entry < 2 ^ offsetWidth := by
  unfold bpLocalSparseOffsetEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, hentry⟩
  rw [← hentry]
  exact
    bpLocalSparseCellOffset_lt_width
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroIdx := slot / (levelCount * macroSize))
      (localStart := slot % (levelCount * macroSize) % macroSize)
      (level := slot % (levelCount * macroSize) / macroSize)
      (offsetWidth := offsetWidth) hwidth

structure PayloadLiveBPLocalSparseOffsetTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat) where
  table :
    FixedWidthNatTable
      (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount) offsetWidth
  payload_length_eq : table.payload.length = overhead

namespace PayloadLiveBPLocalSparseOffsetTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead) :
    List Bool :=
  offsetTable.table.payload

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead) :
    offsetTable.payload.length = overhead := by
  exact offsetTable.payload_length_eq

def readOffsetCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : Costed (Option Nat) :=
  offsetTable.table.readCosted
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) :
    (offsetTable.readOffsetCosted macroIdx localStart level).cost <= 1 := by
  unfold readOffsetCosted
  exact offsetTable.table.readCosted_cost_le_one
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetCosted_erase_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (offsetTable.readOffsetCosted macroIdx localStart level).erase =
      some
        (bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level) := by
  have hentry :=
    bpLocalSparseOffsetEntries_get?_of_valid
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (levelCount := levelCount)
      (macroIdx := macroIdx) (localStart := localStart)
      (level := level) hmacro hlevel hlocal
  unfold readOffsetCosted
  simpa using
    (show
      (offsetTable.table.readCosted
          (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
            level)).erase =
        (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount)[
            bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
              level]? from
      offsetTable.table.readCosted_erase
        (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
          level)).trans hentry

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead index : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmachine :
      offsetWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hword : offsetTable.table.store.words[index]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlen := offsetTable.table.read_word_length_of_some hword
  omega

def spanCandidateCosted
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
    (macroIdx localStart level : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (offsetTable.readOffsetCosted macroIdx localStart level) fun offset? =>
    match offset? with
    | some offset =>
        summary.minCandidateCosted (macroIdx * macroSize + offset)
    | none => Costed.pure none

theorem spanCandidateCosted_cost_le_five
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
    (offsetTable.spanCandidateCosted summary macroIdx localStart level).cost <=
      5 := by
  unfold spanCandidateCosted
  cases hoff :
      (offsetTable.readOffsetCosted macroIdx localStart level).value with
  | none =>
      have hread :=
        offsetTable.readOffsetCosted_cost_le_one macroIdx localStart level
      simp [Costed.bind, Costed.pure, hoff] at hread ⊢
      omega
  | some offset =>
      have hread :=
        offsetTable.readOffsetCosted_cost_le_one macroIdx localStart level
      have hsummary :=
        summary.minCandidateCosted_cost_le_four
          (macroIdx * macroSize + offset)
      simp [Costed.bind, hoff] at hread hsummary ⊢
      omega

end PayloadLiveBPLocalSparseOffsetTable

theorem bpRangeWitness_eq_of_bpRangeArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpRangeArgMinBlock shape blockSize startBlock blockCount)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpRangeArgMinBlock shape blockSize startBlock blockCount)) := by
  have hprefix :=
    bpBlockArgMinPrefixPos_bpRangeArgMinBlock_of_pos
      shape blockSize startBlock blockCount hcount
  simp [bpRangeMinExcess, hprefix]

namespace PayloadLiveBPLocalSparseOffsetTable

theorem spanCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.spanCandidateCosted summary macroIdx localStart level).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level),
          bpRangeArgMinPrefixPos shape blockSize
            (macroIdx * macroSize + localStart) (2 ^ level)) := by
  let offset :=
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level
  have hoffRead :
      (offsetTable.readOffsetCosted macroIdx localStart level).erase =
        some offset := by
    simpa [offset] using
      offsetTable.readOffsetCosted_erase_of_valid hmacro hlevel hlocal
  have hoffAdd :
      macroIdx * macroSize + offset =
        bpRangeArgMinBlock shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level) := by
    simpa [offset] using
      bpLocalSparseCellOffset_valid_add
        (shape := shape) (blockSize := blockSize)
        (blockCount := blockCount) (macroSize := macroSize)
        (macroIdx := macroIdx) (localStart := localStart)
        (level := level) hlocalSpan hblockSpan
  have hspan : 0 < 2 ^ level := by
    exact Nat.pow_pos (by omega : 0 < 2)
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroIdx * macroSize + localStart) (2 ^ level) hspan
  have hblock : macroIdx * macroSize + offset < blockCount := by
    rw [hoffAdd]
    omega
  have hsummary :=
    summary.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblock hcover (hsuperCount hblock)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize (macroIdx * macroSize + localStart) (2 ^ level)
      hspan
  unfold spanCandidateCosted
  rw [Costed.erase_bind]
  simp [hoffRead]
  simpa [hoffAdd, hwitness] using hsummary

end PayloadLiveBPLocalSparseOffsetTable

end SuccinctCloseProposal
end RMQ

import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.LocalGlobalSparse

/-!
# Endpoint-fringe relative summary scan candidates

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def rangeScanFromCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    Nat -> Nat -> Option (Nat × Nat) -> Costed (Option (Nat × Nat))
  | _block, 0, best? => Costed.pure best?
  | block, steps + 1, best? =>
      Costed.bind (table.minCandidateCosted block) fun candidate? =>
        table.rangeScanFromCosted (block + 1) steps
          (bpCandidateMerge? best? candidate?)

def rangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  match count with
  | 0 => Costed.pure none
  | steps + 1 =>
      Costed.bind (table.minCandidateCosted startBlock) fun first? =>
        table.rangeScanFromCosted (startBlock + 1) steps first?

theorem rangeScanFromCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost <= 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have hhead := table.minCandidateCosted_cost_le_four block
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind]
      omega

theorem rangeScanFromCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost = 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind,
        table.minCandidateCosted_cost_eq_four block, htail,
        Nat.succ_mul]
      omega

theorem rangeScanCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost <= 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have hhead := table.minCandidateCosted_cost_le_four startBlock
      have htail :=
        table.rangeScanFromCosted_cost_le (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind]
      omega

theorem rangeScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost = 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have htail :=
        table.rangeScanFromCosted_cost_eq (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind, table.minCandidateCosted_cost_eq_four startBlock,
        htail, Nat.succ_mul]
      omega

theorem rangeScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock : Nat) :
    ¬ exists queryCost : Nat,
      forall count : Nat,
        (table.rangeScanCosted startBlock count).cost <= queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  have hbad := hqueryCost (queryCost + 1)
  rw [table.rangeScanCosted_cost_eq] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

def interiorScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  table.rangeScanCosted (blockOfClose blockSize leftClose + 1)
    (blockOfClose blockSize rightClose -
      blockOfClose blockSize leftClose - 1)

theorem interiorScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) :
    (table.interiorScanCosted leftClose rightClose).cost =
      4 * (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1) := by
  simp [interiorScanCosted, table.rangeScanCosted_cost_eq]

theorem interiorScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblockSize : 0 < blockSize) :
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  let rightClose := (queryCost + 2) * blockSize
  have hleftBlock : blockOfClose blockSize 0 = 0 := by
    simp [blockOfClose]
  have hrightBlock :
      blockOfClose blockSize rightClose = queryCost + 2 := by
    unfold rightClose blockOfClose
    simpa [Nat.mul_comm] using
      Nat.mul_div_right (queryCost + 2) hblockSize
  have hbad := hqueryCost 0 rightClose
  rw [table.interiorScanCosted_cost_eq] at hbad
  simp [hleftBlock, hrightBlock] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

theorem rangeScanFromCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps best : Nat}
    {best? : Option (Nat × Nat)}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hblockRange :
      forall {offset : Nat}, offset < steps ->
        block + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < steps ->
        (block + offset) / blocksPerSuper < superCount)
    (hbest :
      best? = some (bpExcessAt shape best, best)) :
    (table.rangeScanFromCosted block steps best?).erase =
      some
        (bpExcessAt shape
          (bpRangeArgMinPrefixPosFrom shape blockSize block steps best),
          bpRangeArgMinPrefixPosFrom shape blockSize block steps best) := by
  induction steps generalizing block best best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure, hbest,
        bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      have hblock : block < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : block / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block),
                bpBlockArgMinPrefixPos shape blockSize block) := by
        simpa [Costed.erase] using hread
      have hmerge :
          bpCandidateMerge? best?
              (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        rw [hbest, hvalue]
        exact bpCandidateMerge?_argmin_pair shape best
          (bpBlockArgMinPrefixPos shape blockSize block)
      have hmergeValue :
          bpCandidateMerge? best?
              (some
                (bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block),
                  bpBlockArgMinPrefixPos shape blockSize block)) =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        simpa [hvalue] using hmerge
      have htail :=
        ih (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          (best? :=
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)))
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                block + 1 + offset = block + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanFromCosted, Costed.bind, Costed.erase, hvalue,
        hmergeValue,
        bpRangeArgMinPrefixPosFrom] using htail

theorem rangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hcount : 0 < count)
    (hblockRange :
      forall {offset : Nat}, offset < count ->
        startBlock + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < count ->
        (startBlock + offset) / blocksPerSuper < superCount) :
    (table.rangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hblock : startBlock < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : startBlock / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted startBlock).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock) := by
        simpa [Costed.erase] using hread
      have htail :=
        table.rangeScanFromCosted_erase_exact
          (block := startBlock + 1)
          (steps := steps)
          (best := bpBlockArgMinPrefixPos shape blockSize startBlock)
          (best? :=
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock))
          hblocks hcover
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                startBlock + 1 + offset =
                  startBlock + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanCosted, Costed.bind, hvalue,
        bpRangeArgMinPrefixPos, bpRangeMinExcess] using htail

def rangeArgMinBlockCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  table.minCandidateCosted
    (bpRangeArgMinBlock shape blockSize startBlock count)

theorem rangeArgMinBlockCandidateCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeArgMinBlockCandidateCosted startBlock count).cost <= 4 := by
  exact table.minCandidateCosted_cost_le_four
    (bpRangeArgMinBlock shape blockSize startBlock count)

theorem rangeArgMinBlockCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (table.rangeArgMinBlockCandidateCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize startBlock count hcount
  have hblock :
      bpRangeArgMinBlock shape blockSize startBlock count < blockCount := by
    omega
  have hread :=
    table.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblock hcover (hsuperCount hblock)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock count hcount
  simpa [rangeArgMinBlockCandidateCosted, hwitness] using hread

def optionWordList (word? : Option (List Bool)) : List (List Bool) :=
  match word? with
  | some word => [word]
  | none => []

theorem mem_optionWordList
    {word? : Option (List Bool)} {word : List Bool}
    (hmem : word ∈ optionWordList word?) :
    word? = some word := by
  cases word? <;> simp [optionWordList] at hmem ⊢
  exact hmem.symm

def summaryCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : List (List Bool) :=
  optionWordList (table.baselineTable.store.words[block / blocksPerSuper]?) ++
    optionWordList (table.minRelTable.store.words[block]?) ++
    optionWordList (table.maxRelTable.store.words[block]?) ++
    optionWordList (table.argOffsetTable.store.words[block]?)

theorem summaryCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem : word ∈ table.summaryCandidateWordsRead block) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hwords :=
    table.read_words_length_le_machine hsuperMachine hrelativeMachine
  simp [summaryCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hbaseline | hmin | hmax | harg
  · exact hwords.1 (mem_optionWordList hbaseline)
  · exact hwords.2.1 (mem_optionWordList hmin)
  · exact hwords.2.2.1 (mem_optionWordList hmax)
  · exact hwords.2.2.2 (mem_optionWordList harg)

end PayloadLiveBPRelativeMinMaxArgSummaryTable

end SuccinctCloseProposal
end RMQ

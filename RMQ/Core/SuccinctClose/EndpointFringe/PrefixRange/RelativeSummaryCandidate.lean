import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.PrefixArgMin

/-!
# Relative summary prefix-range candidates

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def bpRelativeSummaryMinCandidate
    (blockSize blocksPerSuper block : Nat)
    (summary : Nat × Nat × Nat × Nat) : Nat × Nat :=
  let baseline := summary.1
  let minRel := summary.2.1
  let argOffset := summary.2.2.2
  (baseline + minRel - bpSuperblockSpan blockSize blocksPerSuper,
    blockStartOf blockSize block + argOffset)

theorem bpRelativeExcessEntry_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper block value : Nat}
    (hlower :
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) <=
        value + bpSuperblockSpan blockSize blocksPerSuper) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpRelativeExcessEntry shape blockSize blocksPerSuper block value -
      bpSuperblockSpan blockSize blocksPerSuper =
        value := by
  unfold bpRelativeExcessEntry
  omega

theorem bpBlockRelativeMinExcess_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
      bpSuperblockSpan blockSize blocksPerSuper =
        bpBlockMinExcess shape blockSize block := by
  exact bpRelativeExcessEntry_decode shape
    (bpBlockMinExcess_baseline_le_add_span
      shape hblocks hblock hcover)

theorem bpBlockArgMinLocalOffset_decode
    {shape : Cartesian.CartesianShape}
    {blockSize block : Nat}
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize block +
        bpBlockArgMinLocalOffset shape blockSize block =
      bpBlockArgMinPrefixPos shape blockSize block := by
  have hmem :=
    bpBlockArgMinPrefixPos_mem_range
      (shape := shape) (blockSize := blockSize) (block := block) hbound
  unfold bpBlockArgMinLocalOffset
  omega

theorem bpBlockArgMinPrefixPos_excess_le_offset
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block offset : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
      bpExcessAt shape (blockStartOf blockSize block + offset) := by
  have hsampleLe :
      blockStartOf blockSize block + offset <= shape.bpCode.length := by
    have hblockLe :
        blockStartOf blockSize block + offset <= blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := offset) hblock hoffset
    exact Nat.le_trans hblockLe hcover
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  have hle :=
    bpPrefixRangeArgMinPrefixPos_excess_le_offset
      shape (blockStartOf blockSize block) (blockSize + 1) offset
      (by omega)
  simpa [Nat.min_eq_left hsampleLe] using hle

theorem bpBlockMinExcess_eq_excess_argMin
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMinExcess shape blockSize block =
      bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) := by
  apply Nat.le_antisymm
  · have hbound :
        blockStartOf blockSize block + (blockSize + 1) <=
          shape.bpCode.length + 1 := by
      have hend :
          blockStartOf blockSize block + blockSize <=
            shape.bpCode.length := by
        have hblockEnd :
            blockStartOf blockSize block + blockSize <=
              blockCount * blockSize :=
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := blockSize) hblock (by omega)
        exact Nat.le_trans hblockEnd hcover
      omega
    have hmem :=
      bpBlockArgMinPrefixPos_mem_range
        (shape := shape) (blockSize := blockSize) (block := block)
        hbound
    let offset := bpBlockArgMinPrefixPos shape blockSize block -
      blockStartOf blockSize block
    have hoffset : offset <= blockSize := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      have hlt :
          bpBlockArgMinPrefixPos shape blockSize block <
            blockStartOf blockSize block + (blockSize + 1) := hmem.2
      omega
    have hsample :
        blockStartOf blockSize block + offset =
          bpBlockArgMinPrefixPos shape blockSize block := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      omega
    have hvalueMem :
        List.Mem
          (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize block))
          (bpBlockExcessSamples shape blockSize block) := by
      have hmemOffset :=
        bpBlockExcessSamples_offset_mem
          shape (blockSize := blockSize) (block := block)
          (offset := offset) hoffset
      simpa [hsample] using hmemOffset
    exact
      natListMinFrom_le_of_mem
        (seed := shape.bpCode.length) hvalueMem
  · unfold bpBlockMinExcess
    have hle :
        bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
          natListMinFrom shape.bpCode.length
            (bpBlockExcessSamples shape blockSize block) + 0 :=
      le_natListMinFrom_add_of_forall_mem
        (span := 0)
        (by
          exact bpExcessAt_le_length shape
            (bpBlockArgMinPrefixPos shape blockSize block))
        (by
          intro value hmem
          unfold bpBlockExcessSamples at hmem
          rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
          have hoffset : offset <= blockSize := by
            simp at hoffsetMem
            omega
          have harg :=
            bpBlockArgMinPrefixPos_excess_le_offset
              shape hblock hcover hoffset
          rw [← hvalue]
          omega)
    omega

theorem bpSuperblockBaselineEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper superCount super : Nat}
    (hsuper : super < superCount) :
    (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount)[super]? =
      some
        (bpExcessAt shape
          (blockStartOf blockSize (super * blocksPerSuper))) := by
  have hget :
      (List.range superCount)[super]? = some super :=
    List.getElem?_range hsuper
  simp [bpSuperblockBaselineEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMinExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMinExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMinExcessEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMaxExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMaxExcessEntries, List.getElem?_map, hget]

theorem bpBlockArgMinLocalOffsetEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]? =
      some (bpBlockArgMinLocalOffset shape blockSize block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockArgMinLocalOffsetEntries, List.getElem?_map, hget]

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def minCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (table.summaryCosted block)

theorem minCandidateCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost <= 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_le_four block

theorem summaryCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).cost = 4 := by
  unfold summaryCosted
  cases (table.baselineTable.readCosted (block / blocksPerSuper)).value
  <;> cases (table.minRelTable.readCosted block).value
  <;> cases (table.maxRelTable.readCosted block).value
  <;> simp [Costed.bind, Costed.map]

theorem minCandidateCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost = 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_eq_four block

theorem summaryCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblock : block < blockCount)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.summaryCosted block).erase =
      some
        (bpExcessAt shape
            (blockStartOf blockSize
              ((block / blocksPerSuper) * blocksPerSuper)),
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block,
          bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block,
          bpBlockArgMinLocalOffset shape blockSize block) := by
  rw [table.summaryCosted_erase]
  simp [bpSuperblockBaselineEntries_get?_of_lt hsuper,
    bpBlockRelativeMinExcessEntries_get?_of_lt hblock,
    bpBlockRelativeMaxExcessEntries_get?_of_lt hblock,
    bpBlockArgMinLocalOffsetEntries_get?_of_lt hblock]

theorem minCandidateCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpBlockMinExcess shape blockSize block,
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hsummary :=
    table.summaryCosted_erase_of_bounds hblock hsuper
  have hmin :=
    bpBlockRelativeMinExcess_decode
      shape hblocks hblock hcover
  have hmin' :
      bpExcessAt shape
          (blockStartOf blockSize
            (block / blocksPerSuper * blocksPerSuper)) +
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
        bpSuperblockSpan blockSize blocksPerSuper =
          bpBlockMinExcess shape blockSize block := by
    simpa [bpSuperblockStartPos, bpSuperblockStartBlock] using hmin
  have hblockEnd :
      blockStartOf blockSize block + blockSize <=
        shape.bpCode.length := by
    have hend :
        blockStartOf blockSize block + blockSize <=
          blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := blockSize) hblock (by omega)
    exact Nat.le_trans hend hcover
  have harg :=
    bpBlockArgMinLocalOffset_decode
      (shape := shape) (blockSize := blockSize) (block := block)
      (by omega)
  unfold minCandidateCosted
  simp [Costed.erase_map, hsummary, bpRelativeSummaryMinCandidate,
    hmin', harg]

theorem minCandidateCosted_erase_arg_excess_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block),
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hread :=
    table.minCandidateCosted_erase_of_bounds
      hblocks hblock hcover hsuper
  have hmin :=
    bpBlockMinExcess_eq_excess_argMin
      shape hblock hcover
  simpa [hmin] using hread

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best : Nat)
    (hall :
      forall {offset : Nat},
        offset < steps ->
          bpExcessAt shape best <=
            bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize
                (block + offset))) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best = best := by
  induction steps generalizing block best with
  | zero =>
      simp [bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      have hhead :
          bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block) = best := by
        exact bpBetterArgMinPrefixPos_eq_left_of_excess_le
          shape (hall (offset := 0) (by omega))
      simp [hhead]
      apply ih
      intro offset hoffset
      have htail := hall (offset := offset + 1) (by omega)
      have hblock :
          block + (offset + 1) = block + 1 + offset := by
        omega
      simpa [hblock] using htail

theorem bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
    (shape : Cartesian.CartesianShape)
    {blockSize block steps best targetBlock target : Nat}
    (hbest :
      bpExcessAt shape target < bpExcessAt shape best)
    (hlo : block <= targetBlock)
    (hhi : targetBlock < block + steps)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < block + steps ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best =
      target := by
  induction steps generalizing block best with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      by_cases hblockEq : block = targetBlock
      · subst targetBlock
        have hchoose :
            bpBetterArgMinPrefixPos shape best
                (bpBlockArgMinPrefixPos shape blockSize block) =
              target := by
          rw [htarget]
          exact bpBetterArgMinPrefixPos_eq_right_of_excess_lt
            shape hbest
        simp [hchoose]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (block + 1) steps target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hblockLt : block < targetBlock := by
          omega
        have hcandidateGt :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block) :=
          hleft (by omega) hblockLt
        have hnextBest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
          by_cases hlt :
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block) <
                bpExcessAt shape best
          · rw [bpBetterArgMinPrefixPos_eq_right_of_excess_lt
              shape hlt]
            exact hcandidateGt
          · have hle :
                bpExcessAt shape best <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize block) :=
              Nat.le_of_not_gt hlt
            rw [bpBetterArgMinPrefixPos_eq_left_of_excess_le
              shape hle]
            exact hbest
        exact ih
          (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          hnextBest
          (by omega)
          (by omega)
          (by
            intro candidateBlock hlo' hhi'
            exact hmin (by omega) (by omega))
          (by
            intro candidateBlock hlo' hlt'
            exact hleft (by omega) hlt')

theorem bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPos shape blockSize startBlock blockCount =
      target := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      by_cases htargetStart : targetBlock = startBlock
      · subst targetBlock
        rw [htarget]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (startBlock + 1) count target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hstartLt : startBlock < targetBlock := by
          omega
        have hbest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock) :=
          hleft (by omega) hstartLt
        exact
          bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
            shape hbest
            (by omega)
            (by omega)
            htarget
            (by
              intro candidateBlock hlo hhi
              exact hmin (by omega) (by omega))
            (by
              intro candidateBlock hlo hlt
              exact hleft (by omega) hlt)

theorem bpRangeMinExcess_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeMinExcess shape blockSize startBlock blockCount =
      bpExcessAt shape target := by
  unfold bpRangeMinExcess
  rw [bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    hblock htarget hmin hleft]

theorem bpRangeWitness_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape target, target) := by
  apply Prod.ext
  · exact
      bpRangeMinExcess_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft
  · exact
      bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft

end SuccinctCloseProposal
end RMQ

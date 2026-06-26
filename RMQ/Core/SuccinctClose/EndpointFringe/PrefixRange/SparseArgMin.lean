import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.RelativeSummaryCandidate

/-!
# Sparse block argmin witnesses

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

/--
Choose the better block-minimum candidate by comparing the excess attained at
each block's stored argmin prefix.  Ties keep the left block, matching the
leftmost policy used by `bpBetterArgMinPrefixPos`.
-/
def bpBetterArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) : Nat :=
  if bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock) then
    rightBlock
  else
    leftBlock

theorem bpBetterArgMinBlock_eq_left_of_excess_le
    (shape : Cartesian.CartesianShape)
    {blockSize leftBlock rightBlock : Nat}
    (hle :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock)) :
    bpBetterArgMinBlock shape blockSize leftBlock rightBlock = leftBlock := by
  unfold bpBetterArgMinBlock
  have hnot :
      ¬ bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
    omega
  simp [hnot]

theorem bpBetterArgMinBlock_eq_right_of_excess_lt
    (shape : Cartesian.CartesianShape)
    {blockSize leftBlock rightBlock : Nat}
    (hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)) :
    bpBetterArgMinBlock shape blockSize leftBlock rightBlock = rightBlock := by
  simp [bpBetterArgMinBlock, hlt]

theorem bpExcessAt_bpBetterArgMinBlock_le_left
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize
          (bpBetterArgMinBlock shape blockSize leftBlock rightBlock)) <=
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
  unfold bpBetterArgMinBlock
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt, Nat.le_of_lt hlt]
  · simp [hlt]

theorem bpExcessAt_bpBetterArgMinBlock_le_right
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize
          (bpBetterArgMinBlock shape blockSize leftBlock rightBlock)) <=
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
  unfold bpBetterArgMinBlock
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt]
  · have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt hlt
    simp [hlt, hle]

def bpRangeArgMinBlockFrom
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock : Nat) : Nat :=
  match steps with
  | 0 => bestBlock
  | steps + 1 =>
      let best' :=
        bpBetterArgMinBlock shape blockSize bestBlock block
      bpRangeArgMinBlockFrom shape blockSize (block + 1) steps best'

def bpRangeArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  match blockCount with
  | 0 => startBlock
  | count + 1 =>
      bpRangeArgMinBlockFrom shape blockSize (startBlock + 1) count
        startBlock

theorem bpBlockArgMinPrefixPos_bpBetterArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpBetterArgMinBlock shape blockSize leftBlock rightBlock) =
      bpBetterArgMinPrefixPos shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock)
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
  unfold bpBetterArgMinBlock bpBetterArgMinPrefixPos
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt]
  · simp [hlt]

theorem bpBlockArgMinPrefixPos_bpRangeArgMinBlockFrom
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock : Nat) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpRangeArgMinBlockFrom shape blockSize block steps bestBlock) =
      bpRangeArgMinPrefixPosFrom shape blockSize block steps
        (bpBlockArgMinPrefixPos shape blockSize bestBlock) := by
  induction steps generalizing block bestBlock with
  | zero =>
      simp [bpRangeArgMinBlockFrom, bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom bpRangeArgMinPrefixPosFrom
      simpa [bpBlockArgMinPrefixPos_bpBetterArgMinBlock] using
        ih (block + 1)
          (bpBetterArgMinBlock shape blockSize bestBlock block)

theorem bpBlockArgMinPrefixPos_bpRangeArgMinBlock_of_pos
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpRangeArgMinBlock shape blockSize startBlock blockCount) =
      bpRangeArgMinPrefixPos shape blockSize startBlock blockCount := by
  unfold bpRangeArgMinBlock bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      exact
        bpBlockArgMinPrefixPos_bpRangeArgMinBlockFrom
          shape blockSize (startBlock + 1) count startBlock

theorem bpRangeArgMinBlockFrom_mem
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock lo hi : Nat)
    (hbest : lo <= bestBlock /\ bestBlock < hi)
    (hcandidate :
      forall {offset : Nat}, offset < steps ->
        lo <= block + offset /\ block + offset < hi) :
    lo <= bpRangeArgMinBlockFrom shape blockSize block steps bestBlock /\
      bpRangeArgMinBlockFrom shape blockSize block steps bestBlock < hi := by
  induction steps generalizing block bestBlock with
  | zero =>
      simpa [bpRangeArgMinBlockFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom
      let next := bpBetterArgMinBlock shape blockSize bestBlock block
      have hcandidate0 : lo <= block /\ block < hi := by
        simpa using hcandidate (offset := 0) (by omega)
      have hnext : lo <= next /\ next < hi := by
        unfold next bpBetterArgMinBlock
        by_cases hlt :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [hlt, hcandidate0]
        · simp [hlt, hbest]
      exact
        ih (block := block + 1)
          (bestBlock := next)
          hnext
          (by
            intro offset hoffset
            have htail := hcandidate (offset := offset + 1) (by omega)
            have hblock :
                block + (offset + 1) = block + 1 + offset := by
              omega
            simpa [hblock] using htail)

theorem bpRangeArgMinBlock_mem
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    startBlock <=
        bpRangeArgMinBlock shape blockSize startBlock blockCount /\
      bpRangeArgMinBlock shape blockSize startBlock blockCount <
        startBlock + blockCount := by
  unfold bpRangeArgMinBlock
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      exact
        bpRangeArgMinBlockFrom_mem shape blockSize (startBlock + 1)
          count startBlock startBlock (startBlock + (count + 1))
          (by omega)
          (by
            intro offset hoffset
            omega)

theorem bpRangeArgMinBlockFrom_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock lo hi : Nat)
    (hbestMem : lo <= bestBlock /\ bestBlock < hi)
    (hbestBefore : bestBlock < block)
    (hbestLe :
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < block ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock))
    (hbestLeft :
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < bestBlock ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock))
    (hcandidate :
      forall {offset : Nat},
        offset < steps -> lo <= block + offset /\ block + offset < hi) :
    let target :=
      bpRangeArgMinBlockFrom shape blockSize block steps bestBlock
    lo <= target /\ target < hi /\ target < block + steps /\
      (forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < block + steps ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  induction steps generalizing block bestBlock with
  | zero =>
      simp [bpRangeArgMinBlockFrom]
      exact
        ⟨hbestMem.1, hbestMem.2, hbestBefore,
          (by
            intro candidateBlock hlo hlt
            exact hbestLe hlo hlt),
          hbestLeft⟩
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom
      let current := block
      let best' := bpBetterArgMinBlock shape blockSize bestBlock current
      have hcurrentMem : lo <= current /\ current < hi := by
        simpa [current] using hcandidate (offset := 0) (by omega)
      have htailCandidate :
          forall {offset : Nat},
            offset < steps ->
              lo <= block + 1 + offset /\
                block + 1 + offset < hi := by
        intro offset hoffset
        have htail := hcandidate (offset := offset + 1) (by omega)
        have hpos : block + (offset + 1) = block + 1 + offset := by
          omega
        simpa [hpos] using htail
      have hbest'Mem : lo <= best' /\ best' < hi := by
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake, hcurrentMem]
        · simp [htake, hbestMem]
      have hbest'Before : best' < block + 1 := by
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake, current]
        · simp [htake]
          omega
      have hbest'Le :
          forall {candidateBlock : Nat},
            lo <= candidateBlock ->
              candidateBlock < block + 1 ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize best') <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
        intro candidateBlock hlo hltBlock
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake]
          by_cases hcandidateCurrent : candidateBlock = current
          · subst candidateBlock
            exact Nat.le_refl _
          · have hcandidateBefore : candidateBlock < block := by
              omega
            exact Nat.le_trans (Nat.le_of_lt htake)
              (hbestLe hlo hcandidateBefore)
        · simp [htake]
          by_cases hcandidateCurrent : candidateBlock = current
          · subst candidateBlock
            exact Nat.le_of_not_gt htake
          · have hcandidateBefore : candidateBlock < block := by
              omega
            exact hbestLe hlo hcandidateBefore
      have hbest'Left :
          forall {candidateBlock : Nat},
            lo <= candidateBlock ->
              candidateBlock < best' ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize best') <
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
        intro candidateBlock hlo hltBest
        unfold best' bpBetterArgMinBlock at hltBest ⊢
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake] at hltBest ⊢
          have hcandidateBefore : candidateBlock < block := by
            omega
          exact Nat.lt_of_lt_of_le htake
            (hbestLe hlo hcandidateBefore)
        · simp [htake] at hltBest ⊢
          exact hbestLeft hlo hltBest
      have hrec :=
        ih (block := block + 1) (bestBlock := best')
          hbest'Mem hbest'Before hbest'Le hbest'Left htailCandidate
      have hsteps : 1 + steps = steps + 1 := by omega
      simpa [best', current, hsteps, Nat.add_assoc] using hrec

theorem bpRangeArgMinBlock_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    let target := bpRangeArgMinBlock shape blockSize startBlock blockCount
    startBlock <= target /\ target < startBlock + blockCount /\
      (forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  unfold bpRangeArgMinBlock
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      have hfrom :=
        bpRangeArgMinBlockFrom_leftmost
          shape blockSize (startBlock + 1) count startBlock
          startBlock (startBlock + (count + 1))
          (by omega)
          (by omega)
          (by
            intro candidateBlock hlo hlt
            have hcandidate : candidateBlock = startBlock := by omega
            subst candidateBlock
            exact Nat.le_refl _)
          (by
            intro candidateBlock hlo hlt
            omega)
          (by
            intro offset hoffset
            omega)
      rcases hfrom with ⟨hlo, hhi, _htargetLt, hle, hleft⟩
      have hle' :
          forall {candidateBlock : Nat},
            startBlock <= candidateBlock ->
              candidateBlock < startBlock + (count + 1) ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize
                      (bpRangeArgMinBlockFrom shape blockSize
                        (startBlock + 1) count startBlock)) <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize
                      candidateBlock) := by
        intro candidateBlock hloCandidate hltCandidate
        exact hle hloCandidate (by omega)
      exact ⟨hlo, hhi, hle', hleft⟩

def bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat) : Nat :=
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightStart := startBlock + blockCount - span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  bpBetterArgMinBlock shape blockSize leftBlock rightBlock

theorem bpSparseTwoSpanArgMinBlock_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span)
    (hspanLe : span <= blockCount)
    (hcover : blockCount <= 2 * span) :
    let target :=
      bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span
    startBlock <= target /\ target < startBlock + blockCount /\
      (forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightStart := startBlock + blockCount - span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  have hleft :=
    bpRangeArgMinBlock_leftmost shape blockSize startBlock span hspan
  have hright :=
    bpRangeArgMinBlock_leftmost shape blockSize rightStart span hspan
  have hrightStart_ge : startBlock <= rightStart := by
    omega
  have hrightStart_le_leftEnd : rightStart <= startBlock + span := by
    omega
  have hrightEnd : rightStart + span = startBlock + blockCount := by
    omega
  by_cases htake :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          rightBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hmem :
        startBlock <= rightBlock /\ rightBlock < startBlock + blockCount := by
      constructor
      · exact Nat.le_trans hrightStart_ge hright.1
      · simpa [hrightEnd] using hright.2.1
    have hle :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < startBlock + blockCount ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize rightBlock) <=
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hhi
      by_cases hrightSide : rightStart <= candidateBlock
      · exact hright.2.2.1 hrightSide (by simpa [hrightEnd] using hhi)
      · have hcandidateLeft : candidateBlock < startBlock + span := by
          omega
        exact Nat.le_trans (Nat.le_of_lt htake)
          (hleft.2.2.1 hlo hcandidateLeft)
    have hleftmost :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < rightBlock ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hltTarget
      by_cases hrightSide : rightStart <= candidateBlock
      · exact hright.2.2.2 hrightSide hltTarget
      · have hcandidateLeft : candidateBlock < startBlock + span := by
          omega
        exact Nat.lt_of_lt_of_le htake
          (hleft.2.2.1 hlo hcandidateLeft)
    simpa [htarget] using ⟨hmem.1, hmem.2, hle, hleftmost⟩
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          leftBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hrightNotLt :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt htake
    have hmem :
        startBlock <= leftBlock /\ leftBlock < startBlock + blockCount := by
      constructor
      · exact hleft.1
      · have hleftHi := hleft.2.1
        omega
    have hle :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < startBlock + blockCount ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hhi
      by_cases hleftSide : candidateBlock < startBlock + span
      · exact hleft.2.2.1 hlo hleftSide
      · have hrightSide : rightStart <= candidateBlock := by omega
        exact Nat.le_trans hrightNotLt
          (hright.2.2.1 hrightSide (by simpa [hrightEnd] using hhi))
    have hleftmost :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < leftBlock ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize leftBlock) <
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hltTarget
      exact hleft.2.2.2 hlo hltTarget
    simpa [htarget] using ⟨hmem.1, hmem.2, hle, hleftmost⟩

theorem bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span)
    (hspanLe : span <= blockCount)
    (hcover : blockCount <= 2 * span) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
            blockCount span)) := by
  have hleftmost :=
    bpSparseTwoSpanArgMinBlock_leftmost
      shape blockSize startBlock blockCount span hspan hspanLe hcover
  exact
    bpRangeWitness_eq_of_leftmost_block_candidate
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      (targetBlock :=
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span)
      (target :=
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
            blockCount span))
      ⟨hleftmost.1, hleftmost.2.1⟩
      rfl
      hleftmost.2.2.1
      hleftmost.2.2.2

def bpSparseLogSpan (blockCount : Nat) : Nat :=
  2 ^ Nat.log2 blockCount

theorem bpSparseLogSpan_pos (blockCount : Nat) :
    0 < bpSparseLogSpan blockCount := by
  unfold bpSparseLogSpan
  exact Nat.pow_pos (by omega)

theorem bpSparseLogSpan_le_self
    {blockCount : Nat} (hcount : 0 < blockCount) :
    bpSparseLogSpan blockCount <= blockCount := by
  unfold bpSparseLogSpan
  exact Nat.log2_self_le (by omega)

theorem self_le_two_mul_bpSparseLogSpan
    {blockCount : Nat} (_hcount : 0 < blockCount) :
    blockCount <= 2 * bpSparseLogSpan blockCount := by
  unfold bpSparseLogSpan
  have hlt :
      blockCount < 2 ^ (Nat.log2 blockCount + 1) :=
    Nat.lt_log2_self (n := blockCount)
  have hpow :
      2 ^ (Nat.log2 blockCount + 1) =
        2 * 2 ^ Nat.log2 blockCount := by
    rw [Nat.pow_succ]
    omega
  omega

def bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount
    (bpSparseLogSpan blockCount)

theorem bpRangeWitness_eq_of_bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseLogSpanArgMinBlock shape blockSize startBlock
            blockCount)) := by
  unfold bpSparseLogSpanArgMinBlock
  exact
    bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
      shape blockSize startBlock blockCount
      (bpSparseLogSpan blockCount)
      (bpSparseLogSpan_pos blockCount)
      (bpSparseLogSpan_le_self hcount)
      (self_le_two_mul_bpSparseLogSpan hcount)


end SuccinctCloseProposal
end RMQ

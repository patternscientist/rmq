import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange

/-!
# Endpoint-fringe candidate merge basics

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

def bpCandidateBetter (left right : Nat × Nat) : Nat × Nat :=
  if right.1 < left.1 then right else left

def bpCandidateMerge? :
    Option (Nat × Nat) -> Option (Nat × Nat) -> Option (Nat × Nat)
  | none, candidate => candidate
  | candidate, none => candidate
  | some left, some right => some (bpCandidateBetter left right)

def bpCandidateMerge3?
    (left middle right : Option (Nat × Nat)) : Option (Nat × Nat) :=
  bpCandidateMerge? (bpCandidateMerge? left middle) right

def bpCandidateClose? (candidate? : Option (Nat × Nat)) : Option Nat :=
  candidate?.map fun candidate => candidate.2 - 1

theorem bpCandidateBetter_eq_left_of_fst_le
    {left right : Nat × Nat}
    (hle : left.1 <= right.1) :
    bpCandidateBetter left right = left := by
  unfold bpCandidateBetter
  have hnot : ¬ right.1 < left.1 := by
    omega
  simp [hnot]

theorem bpCandidateBetter_eq_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateBetter left right = right := by
  simp [bpCandidateBetter, hlt]

theorem bpCandidateMerge?_some_left_of_fst_le
    {left : Nat × Nat} {right? : Option (Nat × Nat)}
    (hright :
      forall {right : Nat × Nat}, right? = some right -> left.1 <= right.1) :
    bpCandidateMerge? (some left) right? = some left := by
  cases right? with
  | none =>
      simp [bpCandidateMerge?]
  | some right =>
      have hle : left.1 <= right.1 := hright rfl
      simp [bpCandidateMerge?, bpCandidateBetter_eq_left_of_fst_le hle]

theorem bpCandidateMerge?_some_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateMerge? (some left) (some right) = some right := by
  simp [bpCandidateMerge?, bpCandidateBetter_eq_right_of_fst_lt hlt]

theorem bpCandidateMerge3?_eq_some_left_of_fst_le
    {left : Nat × Nat}
    {middle? right? : Option (Nat × Nat)}
    (hmiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> left.1 <= middle.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> left.1 <= right.1) :
    bpCandidateMerge3? (some left) middle? right? = some left := by
  have hfirst :
      bpCandidateMerge? (some left) middle? = some left :=
    bpCandidateMerge?_some_left_of_fst_le hmiddle
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
    {left middle : Nat × Nat}
    {right? : Option (Nat × Nat)}
    (hmiddleLeft : middle.1 < left.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> middle.1 <= right.1) :
    bpCandidateMerge3? (some left) (some middle) right? =
      some middle := by
  have hfirst :
      bpCandidateMerge? (some left) (some middle) = some middle :=
    bpCandidateMerge?_some_right_of_fst_lt hmiddleLeft
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
    {left right : Nat × Nat}
    {middle? : Option (Nat × Nat)}
    (hrightLeft : right.1 < left.1)
    (hrightMiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> right.1 < middle.1) :
    bpCandidateMerge3? (some left) middle? (some right) =
      some right := by
  cases middle? with
  | none =>
      unfold bpCandidateMerge3?
      simp [bpCandidateMerge?,
        bpCandidateBetter_eq_right_of_fst_lt hrightLeft]
  | some middle =>
      have hmiddle : right.1 < middle.1 := hrightMiddle rfl
      have hfirst :
          bpCandidateMerge? (some left) (some middle) =
            some (bpCandidateBetter left middle) := by
        simp [bpCandidateMerge?]
      unfold bpCandidateMerge3?
      rw [hfirst]
      by_cases hmiddleLeft : middle.1 < left.1
      · have hbest :
            bpCandidateBetter left middle = middle :=
          bpCandidateBetter_eq_right_of_fst_lt hmiddleLeft
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hmiddle
      · have hle : left.1 <= middle.1 := Nat.le_of_not_gt hmiddleLeft
        have hbest :
            bpCandidateBetter left middle = left :=
          bpCandidateBetter_eq_left_of_fst_le hle
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hrightLeft

theorem bpCandidateMerge?_argmin_pair
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    bpCandidateMerge?
        (some (bpExcessAt shape left, left))
        (some (bpExcessAt shape right, right)) =
      some
        (bpExcessAt shape (bpBetterArgMinPrefixPos shape left right),
          bpBetterArgMinPrefixPos shape left right) := by
  unfold bpCandidateMerge? bpCandidateBetter bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt]
  · simp [hlt]

theorem bpCandidateMerge?_adjacentRangeWitness
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock leftCount rightCount : Nat)
    (hleftCount : 0 < leftCount)
    (hrightCount : 0 < rightCount) :
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock leftCount,
            bpRangeArgMinPrefixPos shape blockSize startBlock leftCount))
        (some
          (bpRangeMinExcess shape blockSize (startBlock + leftCount)
            rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount) rightCount)) =
      some
        (bpRangeMinExcess shape blockSize startBlock
          (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) := by
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock leftCount
  let rightStart := startBlock + leftCount
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart rightCount
  have hleft :=
    bpRangeArgMinBlock_leftmost shape blockSize startBlock leftCount
      hleftCount
  have hright :=
    bpRangeArgMinBlock_leftmost shape blockSize rightStart rightCount
      hrightCount
  have hleftWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock leftCount hleftCount
  have hrightWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize rightStart rightCount hrightCount
  by_cases htake :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize rightBlock),
              bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact bpCandidateMerge?_some_right_of_fst_lt htake
    have hglobal :
        (bpRangeMinExcess shape blockSize startBlock
            (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) =
        (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock),
          bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact
        bpRangeWitness_eq_of_leftmost_block_candidate
          (shape := shape) (blockSize := blockSize)
          (startBlock := startBlock)
          (blockCount := leftCount + rightCount)
          (targetBlock := rightBlock)
          (target :=
            bpBlockArgMinPrefixPos shape blockSize rightBlock)
          (by
            constructor
            · exact Nat.le_trans (by omega : startBlock <= rightStart)
                hright.1
            · have hhi := hright.2.1
              omega)
          rfl
          (by
            intro candidateBlock hlo hhi
            by_cases hrightSide : rightStart <= candidateBlock
            · exact hright.2.2.1 hrightSide (by omega)
            · have hleftSide : candidateBlock < startBlock + leftCount := by
                omega
              exact Nat.le_trans (Nat.le_of_lt htake)
                (hleft.2.2.1 hlo hleftSide))
          (by
            intro candidateBlock hlo hlt
            by_cases hrightSide : rightStart <= candidateBlock
            · exact hright.2.2.2 hrightSide hlt
            · have hleftSide : candidateBlock < startBlock + leftCount := by
                omega
              exact Nat.lt_of_lt_of_le htake
                (hleft.2.2.1 hlo hleftSide))
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, hglobal] using hmerge
  · have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) :=
      Nat.le_of_not_gt htake
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize leftBlock),
              bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpCandidateMerge?_some_left_of_fst_le
          (by
            intro right hrightSome
            cases hrightSome
            exact hle)
    have hglobal :
        (bpRangeMinExcess shape blockSize startBlock
            (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) =
        (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock),
          bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpRangeWitness_eq_of_leftmost_block_candidate
          (shape := shape) (blockSize := blockSize)
          (startBlock := startBlock)
          (blockCount := leftCount + rightCount)
          (targetBlock := leftBlock)
          (target :=
            bpBlockArgMinPrefixPos shape blockSize leftBlock)
          (by
            constructor
            · exact hleft.1
            · have hhi := hleft.2.1
              omega)
          rfl
          (by
            intro candidateBlock hlo hhi
            by_cases hleftSide : candidateBlock < startBlock + leftCount
            · exact hleft.2.2.1 hlo hleftSide
            · have hrightSide : rightStart <= candidateBlock := by
                omega
              exact Nat.le_trans hle (hright.2.2.1 hrightSide (by omega)))
          (by
            intro candidateBlock hlo hlt
            exact hleft.2.2.2 hlo hlt)
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, hglobal] using hmerge

theorem bpCandidateMerge3?_threeAdjacentRangeWitness
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock leftCount middleCount rightCount : Nat)
    (hleftCount : 0 < leftCount)
    (hmiddleCount : 0 < middleCount)
    (hrightCount : 0 < rightCount) :
    bpCandidateMerge3?
        (some
          (bpRangeMinExcess shape blockSize startBlock leftCount,
            bpRangeArgMinPrefixPos shape blockSize startBlock leftCount))
        (some
          (bpRangeMinExcess shape blockSize (startBlock + leftCount)
            middleCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount) middleCount))
        (some
          (bpRangeMinExcess shape blockSize
            (startBlock + leftCount + middleCount) rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount + middleCount) rightCount)) =
      some
        (bpRangeMinExcess shape blockSize startBlock
          (leftCount + middleCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + middleCount + rightCount)) := by
  have hfirst :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount middleCount
      hleftCount hmiddleCount
  have hsecond :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock (leftCount + middleCount) rightCount
      (by omega) hrightCount
  unfold bpCandidateMerge3?
  rw [hfirst]
  simpa [Nat.add_assoc] using hsecond

theorem bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span) :
    let rightStart := startBlock + blockCount - span
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock span,
            bpRangeArgMinPrefixPos shape blockSize startBlock span))
        (some
          (bpRangeMinExcess shape blockSize rightStart span,
            bpRangeArgMinPrefixPos shape blockSize rightStart span)) =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)) := by
  let rightStart := startBlock + blockCount - span
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  have hleftWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock span hspan
  have hrightWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize rightStart span hspan
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
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize rightBlock),
              bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact bpCandidateMerge?_some_right_of_fst_lt htake
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, htarget] using hmerge
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          leftBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt htake
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize leftBlock),
              bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpCandidateMerge?_some_left_of_fst_le
          (by
            intro right hright
            cases hright
            exact hle)
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, htarget] using hmerge

theorem bpCandidateMerge?_bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (_hcount : 0 < blockCount) :
    let span := bpSparseLogSpan blockCount
    let rightStart := startBlock + blockCount - span
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock span,
            bpRangeArgMinPrefixPos shape blockSize startBlock span))
        (some
          (bpRangeMinExcess shape blockSize rightStart span,
            bpRangeArgMinPrefixPos shape blockSize rightStart span)) =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)) := by
  unfold bpSparseLogSpanArgMinBlock
  exact
    bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
      shape blockSize startBlock blockCount
      (bpSparseLogSpan blockCount)
      (bpSparseLogSpan_pos blockCount)

end SuccinctClose
end RMQ

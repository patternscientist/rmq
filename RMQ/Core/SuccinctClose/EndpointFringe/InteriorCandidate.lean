import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange

/-!
# Endpoint-fringe interior candidate machinery

Candidate merging, sparse local/global interior tables, two-level interior
candidate reads, and compact relative-rmM interior directory setup. The
historical `RMQ.SuccinctCloseProposal` namespace is preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

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
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hword : globalTable.table.store.words[index]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem : word ∈ table.summaryCandidateWordsRead block) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hwords :=
    table.read_words_length_le_machine hsuperMachine hrelativeMachine
  simp [summaryCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hbaseline | hmin | hmax | harg
  · exact hwords.1 (mem_optionWordList hbaseline)
  · exact hwords.2.1 (mem_optionWordList hmin)
  · exact hwords.2.2.1 (mem_optionWordList hmax)
  · exact hwords.2.2.2 (mem_optionWordList harg)

end PayloadLiveBPRelativeMinMaxArgSummaryTable

def localSparseOffsetWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (offsetTable.table.store.words[
      bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]?)

theorem localSparseOffsetWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSparseOffsetWordRead offsetTable macroIdx localStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact offsetTable.read_word_length_le_machine hmachine hsome

def globalSparseBlockWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (globalTable.table.store.words[
      bpGlobalSparseCellSlot macroCount macroStart level]?)

theorem globalSparseBlockWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hmachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSparseBlockWordRead globalTable macroStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact globalTable.read_word_length_le_machine hmachine hsome

def localSpanCandidateWordsRead
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
    (macroIdx localStart level : Nat) : List (List Bool) :=
  let offset :=
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level
  localSparseOffsetWordRead offsetTable macroIdx localStart level ++
    summary.summaryCandidateWordsRead (macroIdx * macroSize + offset)

theorem localSpanCandidateWordsRead_length_le_machine
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
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSpanCandidateWordsRead offsetTable summary macroIdx localStart
          level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hlocal | hsummary
  · exact
      localSparseOffsetWordRead_length_le_machine
        offsetTable hoffsetMachine hlocal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def globalSpanCandidateWordsRead
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
    (macroStart level : Nat) : List (List Bool) :=
  let block :=
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level
  globalSparseBlockWordRead globalTable macroStart level ++
    summary.summaryCandidateWordsRead block

theorem globalSpanCandidateWordsRead_length_le_machine
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
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSpanCandidateWordsRead globalTable summary macroStart
        level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hglobal | hsummary
  · exact
      globalSparseBlockWordRead_length_le_machine
        globalTable hblockMachine hglobal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def localTwoSpanCandidateWordsRead
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
    (macroIdx localStart count : Nat) : List (List Bool) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  localSpanCandidateWordsRead offsetTable summary macroIdx localStart level ++
    localSpanCandidateWordsRead offsetTable summary macroIdx
      (localStart + count - span) level

theorem localTwoSpanCandidateWordsRead_length_le_machine
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
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localTwoSpanCandidateWordsRead offsetTable summary macroIdx
          localStart count) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def globalTwoSpanCandidateWordsRead
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
    (macroStart macroSpanCount : Nat) : List (List Bool) :=
  let level := Nat.log2 macroSpanCount
  let span := bpSparseLogSpan macroSpanCount
  globalSpanCandidateWordsRead globalTable summary macroStart level ++
    globalSpanCandidateWordsRead globalTable summary
      (macroStart + macroSpanCount - span) level

theorem globalTwoSpanCandidateWordsRead_length_le_machine
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
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        globalTwoSpanCandidateWordsRead globalTable summary macroStart
          macroSpanCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelAdjacentMacroCandidateWordsRead
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
    (macroStart localStart rightCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    localTwoSpanCandidateWordsRead localTable summary (macroStart + 1) 0
      rightCount

theorem bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead macroStart localStart rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
          macroStart localStart rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelAdjacentMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelLeftMiddleMacroCandidateWordsRead
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
    (macroStart localStart middleMacroCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount

theorem bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      macroStart localStart middleMacroCount : Nat}
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
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelLeftMiddleMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle

def bpTwoLevelCrossMacroCandidateWordsRead
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
    List (List Bool) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount ++
    localTwoSpanCandidateWordsRead localTable summary rightMacroStart 0
      rightCount

theorem bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
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
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelCrossMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelInteriorCandidateCosted
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
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    Costed.pure none
  else if count <= macroSize - localStart then
    localTable.twoSpanCandidateCosted summary macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateCosted localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateCosted_cost_le_thirty
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
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).cost <= 30 := by
  unfold bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      have hlocal :=
        localTable.twoSpanCandidateCosted_cost_le_ten summary
          (startBlock / macroSize) (startBlock % macroSize) count
      omega
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        have hadj :=
          bpTwoLevelAdjacentMacroCandidateCosted_cost_le_twenty
            localTable summary (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
        omega
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true]
          have hleftMiddle :=
            bpTwoLevelLeftMiddleMacroCandidateCosted_cost_le_twenty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
          omega
        · simp only [hright, if_false]
          exact
            bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) %
                macroSize)

def bpTwoLevelInteriorCandidateWordsRead
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
    (startBlock count : Nat) : List (List Bool) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    []
  else if count <= macroSize - localStart then
    localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      startBlock count : Nat}
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
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelInteriorCandidateWordsRead localTable globalTable summary
          startBlock count) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold bpTwoLevelInteriorCandidateWordsRead at hmem
  by_cases hcount : count = 0
  · simp [hcount] at hmem
  · simp only [hcount, if_false] at hmem
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin] at hmem
      exact
        localTwoSpanCandidateWordsRead_length_le_machine localTable summary
          hoffsetMachine hsuperMachine hrelativeMachine hmem
    · simp only [hwithin, if_false] at hmem
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle] at hmem
        exact
          bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
            localTable summary hoffsetMachine hsuperMachine
            hrelativeMachine hmem
      · simp [hmiddle] at hmem
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true] at hmem
          exact
            bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem
        · simp only [hright, if_false] at hmem
          exact
            bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem

theorem bpTwoLevelInteriorCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead startBlock count : Nat}
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
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount)
    (hmacroRange :
      forall {block : Nat}, block < blockCount ->
        block / macroSize < macroCount)
    (hmacroCover : blockCount <= macroCount * macroSize)
    (hlocalLevel :
      forall {localCount : Nat}, 0 < localCount ->
        localCount <= macroSize ->
          Nat.log2 localCount < localLevelCount)
    (hglobalLevel :
      forall {macroSpanCount : Nat}, 0 < macroSpanCount ->
        macroSpanCount <= macroCount ->
        Nat.log2 macroSpanCount < globalLevelCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  let leftCount := macroSize - localStart
  have hlocalStart : localStart < macroSize := by
    exact Nat.mod_lt startBlock hmacroSize
  have hstartEq : macroStart * macroSize + localStart = startBlock := by
    simpa [macroStart, localStart, Nat.mul_comm] using
      Nat.div_add_mod startBlock macroSize
  have hstartLt : startBlock < blockCount := by
    omega
  have hmacroStart : macroStart < macroCount := by
    simpa [macroStart] using hmacroRange hstartLt
  have hnotCount : ¬ count = 0 := by
    omega
  unfold bpTwoLevelInteriorCandidateCosted
  simp only [hnotCount, if_false]
  by_cases hwithin : count <= macroSize - startBlock % macroSize
  · have hlocalCount :
        startBlock % macroSize + count <= macroSize := by
      omega
    have hcountLeMacro : count <= macroSize := by
      omega
    have hlevel : Nat.log2 count < localLevelCount :=
      hlocalLevel hcount hcountLeMacro
    have hblockCount :
        (startBlock / macroSize) * macroSize +
            startBlock % macroSize + count <= blockCount := by
      simpa [macroStart, localStart, hstartEq] using hbound
    have hexact :=
      localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
        summary hcount hmacroStart hlevel hlocalStart hlocalCount
        hblockCount hblocks hcover hsuperCount
    simp only [hwithin, if_true]
    simpa [macroStart, localStart, hstartEq] using hexact
  · simp only [hwithin, if_false]
    have hleftCount : 0 < leftCount := by
      unfold leftCount localStart
      omega
    have hleftLt : leftCount < count := by
      unfold leftCount localStart
      omega
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    have hremainingPos : 0 < remaining := by
      unfold remaining
      omega
    have hcountEq : count = leftCount + remaining := by
      unfold remaining
      omega
    have hleftEnd :
        macroStart * macroSize + localStart + leftCount =
          (macroStart + 1) * macroSize := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      unfold leftCount
      omega
    have hstartCountEq :
        startBlock + count =
          macroStart * macroSize + localStart + leftCount + remaining := by
      omega
    have hremainingDivMod :
        remaining = middleMacroCount * macroSize + rightCount := by
      unfold middleMacroCount rightCount
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod remaining macroSize).symm
    by_cases hmiddleSmall : macroSize = 0 ∨ remaining < macroSize
    · have hremainingLt : remaining < macroSize := by
        rcases hmiddleSmall with hzero | hlt
        · omega
        · exact hlt
      have hmiddleZero : middleMacroCount = 0 := by
        unfold middleMacroCount
        exact Nat.div_eq_of_lt hremainingLt
      have hrightEq : rightCount = remaining := by
        unfold rightCount
        exact Nat.mod_eq_of_lt hremainingLt
      have hrightCount : 0 < rightCount := by
        simpa [hrightEq] using hremainingPos
      have hrightLe : rightCount <= macroSize := by
        omega
      have hrightLevel :
          Nat.log2 rightCount < localLevelCount :=
        hlocalLevel hrightCount hrightLe
      have hrightBlockCount :
          (macroStart + 1) * macroSize + rightCount <= blockCount := by
        have hend :
            startBlock + count =
              (macroStart + 1) * macroSize + rightCount := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ = (macroStart + 1) * macroSize + rightCount := by
                simp [hrightEq]
        omega
      have hrightMacro : macroStart + 1 < macroCount := by
        have hrightStartLt :
            (macroStart + 1) * macroSize < blockCount := by
          omega
        have hidx := hmacroRange hrightStartLt
        have hdiv :
            ((macroStart + 1) * macroSize) / macroSize =
              macroStart + 1 := by
          simpa [Nat.mul_comm] using
            Nat.mul_div_right (macroStart + 1) hmacroSize
        simpa [hdiv] using hidx
      have htotalBlockCount :
          macroStart * macroSize + localStart + leftCount + rightCount <=
            blockCount := by
        have hend :
            macroStart * macroSize + localStart + leftCount + rightCount =
              startBlock + count := by
          omega
        omega
      have hexact :=
        bpTwoLevelAdjacentMacroCandidateCosted_erase_exact
          localTable summary hmacroSize hlocalStart hrightCount hrightLe
          (hlocalLevel hleftCount (by omega)) hrightLevel hmacroStart
          hrightMacro htotalBlockCount hblocks hcover hsuperCount
      have hmiddleSmall' :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      have hcountAdjacent :
          (macroSize - localStart) + rightCount = count := by
        omega
      simpa [hmiddleSmall', macroStart, localStart, rightCount,
        remaining, leftCount, hstartEq, hcountAdjacent] using hexact
    · have hnotRemainingLt : ¬ remaining < macroSize := by
        intro hlt
        exact hmiddleSmall (Or.inr hlt)
      have hmacroLeRemaining : macroSize <= remaining := by
        exact Nat.le_of_not_gt hnotRemainingLt
      have hmiddleCount : 0 < middleMacroCount := by
        unfold middleMacroCount
        exact Nat.div_pos hmacroLeRemaining hmacroSize
      have hmiddleSmall' :
          ¬ (macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize) := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      by_cases hrightZero : rightCount = 0
      · have hremainingEq :
            remaining = middleMacroCount * macroSize := by
          simpa [hrightZero] using hremainingDivMod
        have hendMul :
            startBlock + count =
              (macroStart + 1 + middleMacroCount) * macroSize := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ =
                (macroStart + 1) * macroSize +
                  middleMacroCount * macroSize := by
                omega
            _ = (macroStart + 1 + middleMacroCount) * macroSize := by
                rw [← Nat.add_mul]
        have hmiddleEnd :
            macroStart + 1 + middleMacroCount <= macroCount := by
          have hmulLe :
              (macroStart + 1 + middleMacroCount) * macroSize <=
                macroCount * macroSize := by
            have hendBound :
                (macroStart + 1 + middleMacroCount) * macroSize <=
                  blockCount := by
              simpa [hendMul] using hbound
            exact Nat.le_trans hendBound hmacroCover
          have hmulLe' :
              macroSize * (macroStart + 1 + middleMacroCount) <=
                macroSize * macroCount := by
            simpa [Nat.mul_comm] using hmulLe
          exact Nat.le_of_mul_le_mul_left hmulLe' hmacroSize
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix hmiddleEnd)
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelLeftMiddleMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount (hlocalLevel hleftCount (by omega))
            hmiddleLevel hmacroStart hmiddleEnd htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          simpa [rightCount, remaining, leftCount, localStart] using
            hrightZero
        have hcountLeftMiddle :
            (macroSize - localStart) + middleMacroCount * macroSize =
              count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, remaining, leftCount, hstartEq,
          hcountLeftMiddle] using hexact
      · have hrightCountPos : 0 < rightCount := by
          cases hright : rightCount with
          | zero =>
              exact False.elim (hrightZero hright)
          | succ k =>
              omega
        have hrightLe : rightCount <= macroSize := by
          have hrightLt : rightCount < macroSize := by
            unfold rightCount
            exact Nat.mod_lt remaining hmacroSize
          omega
        have hrightLevel :
            Nat.log2 rightCount < localLevelCount :=
          hlocalLevel hrightCountPos hrightLe
        have hrightMacro :
            macroStart + 1 + middleMacroCount < macroCount := by
          have hrightStartLt :
              (macroStart + 1 + middleMacroCount) * macroSize <
                blockCount := by
            have hend :
                startBlock + count =
                  (macroStart + 1 + middleMacroCount) * macroSize +
                    rightCount := by
              calc
                startBlock + count =
                    macroStart * macroSize + localStart + leftCount +
                      remaining := hstartCountEq
                _ = (macroStart + 1) * macroSize + remaining := by
                    omega
                _ =
                    (macroStart + 1) * macroSize +
                      (middleMacroCount * macroSize + rightCount) := by
                    omega
                _ =
                    (macroStart + 1 + middleMacroCount) * macroSize +
                      rightCount := by
                    calc
                      (macroStart + 1) * macroSize +
                          (middleMacroCount * macroSize + rightCount) =
                        ((macroStart + 1) * macroSize +
                            middleMacroCount * macroSize) + rightCount := by
                          omega
                      _ =
                        (macroStart + 1 + middleMacroCount) * macroSize +
                          rightCount := by
                          rw [← Nat.add_mul]
            omega
          have hidx := hmacroRange hrightStartLt
          have hdiv :
              ((macroStart + 1 + middleMacroCount) * macroSize) /
                  macroSize =
                macroStart + 1 + middleMacroCount := by
            simpa [Nat.mul_comm] using
              Nat.mul_div_right
                (macroStart + 1 + middleMacroCount) hmacroSize
          simpa [hdiv] using hidx
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix (Nat.le_of_lt hrightMacro))
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize + rightCount <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize + rightCount =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelCrossMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount hrightCountPos hrightLe
            (hlocalLevel hleftCount (by omega)) hmiddleLevel
            hrightLevel hmacroStart hrightMacro htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            ¬ (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          intro hzero
          exact hrightZero
            (by
              simpa [rightCount, remaining, leftCount, localStart] using
                hzero)
        have hcountCross :
            (macroSize - localStart) +
                middleMacroCount * macroSize + rightCount = count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, rightCount, remaining, leftCount, hstartEq,
          hcountCross] using hexact

theorem concreteBPTwoLevelCrossMacroCandidate_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth globalLevelCount blockWidth blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetWidth : macroSize < 2 ^ offsetWidth)
    (hmacroSize : 0 < macroSize)
    (hblockWidth : blockCount < 2 ^ blockWidth)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let localTable :=
      concreteBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth hoffsetWidth
    let globalTable :=
      concreteBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth hmacroSize
        hblockWidth
    localTable.payload.length =
        (macroCount * (localLevelCount * macroSize)) * offsetWidth /\
      globalTable.payload.length =
        (globalLevelCount * macroCount) * blockWidth /\
      (forall macroStart localStart middleMacroCount rightCount,
        (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
          macroStart localStart middleMacroCount rightCount).cost <= 30) /\
      (forall {macroStart localStart middleMacroCount rightCount : Nat},
        localStart < macroSize ->
          0 < middleMacroCount ->
            0 < rightCount ->
              rightCount <= macroSize ->
                Nat.log2 (macroSize - localStart) < localLevelCount ->
                  Nat.log2 middleMacroCount < globalLevelCount ->
                    Nat.log2 rightCount < localLevelCount ->
                      macroStart < macroCount ->
                        macroStart + 1 + middleMacroCount < macroCount ->
                          macroStart * macroSize + localStart +
                              (macroSize - localStart) +
                              middleMacroCount * macroSize + rightCount <=
                            blockCount ->
                            (bpTwoLevelCrossMacroCandidateCosted
                              localTable globalTable summary macroStart
                              localStart middleMacroCount rightCount).erase =
                              some
                                (bpRangeMinExcess shape blockSize
                                  (macroStart * macroSize + localStart)
                                  ((macroSize - localStart) +
                                    middleMacroCount * macroSize +
                                      rightCount),
                                  bpRangeArgMinPrefixPos shape blockSize
                                    (macroStart * macroSize + localStart)
                                    ((macroSize - localStart) +
                                      middleMacroCount * macroSize +
                                        rightCount))) /\
      forall {macroStart localStart middleMacroCount rightCount : Nat}
          {word : List Bool},
        word ∈
          bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
            summary macroStart localStart middleMacroCount rightCount ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro localTable globalTable
  constructor
  · exact localTable.payload_length
  constructor
  · exact globalTable.payload_length
  constructor
  · intro macroStart localStart middleMacroCount rightCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
        localTable globalTable summary macroStart localStart
        middleMacroCount rightCount
  constructor
  · intro macroStart localStart middleMacroCount rightCount
      hlocalStart hmiddleCount hrightCount hrightLe hleftLevel
      hmiddleLevel hrightLevel hmacroStart hrightMacro hblockCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_erase_exact
        localTable globalTable summary hmacroSize hlocalStart
        hmiddleCount hrightCount hrightLe hleftLevel hmiddleLevel
        hrightLevel hmacroStart hrightMacro hblockCount hblocks hcover
        hsuperCount
  · intro macroStart localStart middleMacroCount rightCount word hmem
    exact
      bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
        localTable globalTable summary hoffsetMachine hblockMachine
        hsuperMachine hrelativeMachine hmem

/--
Interior full-block range-minimum directory for the relative-rmM close layer.

This interface is deliberately narrow: a concrete implementation has to expose
one charged `rangeMinCosted` path whose erasure is the leftmost block-minimum
candidate over the requested complete-block range.  The compact C2 target must
instantiate this with a constant `queryCost`; the scan instance below is kept
only as a diagnostic replacement target.
-/
structure PayloadLiveBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead queryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  payloadWordsRead : Nat -> Nat -> List (List Bool)
  rangeMinCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  rangeMin_cost_le :
    forall startBlock count,
      (rangeMinCosted startBlock count).cost <= queryCost
  rangeMin_exact :
    forall {startBlock count : Nat},
      0 < count ->
        startBlock + count <= blockCount ->
          (rangeMinCosted startBlock count).erase =
            some
              (bpRangeMinExcess shape blockSize startBlock count,
                bpRangeArgMinPrefixPos shape blockSize startBlock count)
  read_words_length_le_machine :
    forall {startBlock count : Nat} {word : List Bool},
      word ∈ payloadWordsRead startBlock count ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length

namespace PayloadLiveBPRelativeRmmInteriorDirectory

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead queryCost : Nat}
    (directory :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        overhead queryCost) :
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= queryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact ⟨directory.payload_length_eq, directory.rangeMin_cost_le,
    directory.rangeMin_exact, directory.read_words_length_le_machine⟩

end PayloadLiveBPRelativeRmmInteriorDirectory

/--
Proof-only range-min oracle used to document a target-shape obstruction.

This is intentionally *not* a compact C2 construction: it answers by directly
calling the semantic reference functions and charges a constant without reading
payload bits.  The theorem below records why `concreteBPRelativeRmmInteriorDirectory_profile`
cannot be closed merely by exposing the abstract `PayloadLiveBPRelativeRmmInteriorDirectory`
record and invoking its generic `.profile`.
-/
def proofOnlyBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      0 1 where
  payload := []
  payload_length_eq := rfl
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := fun startBlock count =>
    { value :=
        if 0 < count ∧ startBlock + count <= blockCount then
          some
            (bpRangeMinExcess shape blockSize startBlock count,
              bpRangeArgMinPrefixPos shape blockSize startBlock count)
        else
          none
      cost := 1 }
  rangeMin_cost_le := by
    intro startBlock count
    simp
  rangeMin_exact := by
    intro startBlock count hcount hbound
    have hcond : 0 < count ∧ startBlock + count <= blockCount :=
      ⟨hcount, hbound⟩
    simp [hcond]
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    let directory :=
      proofOnlyBPRelativeRmmInteriorDirectory shape blockSize blockCount
    directory.payload.length = 0 /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= 1) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    (proofOnlyBPRelativeRmmInteriorDirectory
      shape blockSize blockCount).profile

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def boundedRangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    table.rangeScanCosted startBlock count
  else
    Costed.pure none

theorem boundedRangeScanCosted_cost_le_blockCount
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.boundedRangeScanCosted startBlock count).cost <=
      4 * blockCount := by
  unfold boundedRangeScanCosted
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    have hcost := table.rangeScanCosted_cost_le startBlock count
    have hcount : count <= blockCount := by omega
    have hmul : 4 * count <= 4 * blockCount :=
      Nat.mul_le_mul_left 4 hcount
    exact Nat.le_trans hcost hmul
  · simp [hbound, Costed.pure]

theorem div_lt_succ_div_of_lt
    {block blocksPerSuper blockCount : Nat}
    (hblock : block < blockCount) :
    block / blocksPerSuper < blockCount / blocksPerSuper + 1 := by
  have hle : block / blocksPerSuper <= blockCount / blocksPerSuper := by
    exact Nat.div_le_div_right (Nat.le_of_lt hblock)
  omega

theorem boundedRangeScanCosted_erase_exact
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
    (table.boundedRangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  unfold boundedRangeScanCosted
  simp [hbound]
  exact
    table.rangeScanCosted_erase_exact hblocks hcover hcount
      (by
        intro offset hoffset
        omega)
      (by
        intro offset hoffset
        exact hsuperCount (by omega))

def scanInteriorDirectory
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      overhead (4 * blockCount) where
  payload := table.payload
  payload_length_eq := table.payload_length
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := table.boundedRangeScanCosted
  rangeMin_cost_le := table.boundedRangeScanCosted_cost_le_blockCount
  rangeMin_exact := by
    intro startBlock count hcount hbound
    exact table.boundedRangeScanCosted_erase_exact hblocks hcover
      hsuperCount hcount hbound
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem scanInteriorDirectory_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let directory :=
      table.scanInteriorDirectory hblocks hcover hsuperCount
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          4 * blockCount) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    (table.scanInteriorDirectory hblocks hcover hsuperCount).profile

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem canonicalBPRelativeSummary_block_div_lt_superCount
    {shape : Cartesian.CartesianShape} {block : Nat}
    (hblock : block < canonicalBPRelativeSummaryBlockCount shape) :
    block / canonicalBPRelativeSummaryBlocksPerSuper shape <
      canonicalBPRelativeSummarySuperCount shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hdiv :
        block / canonicalBPRelativeSummaryBlocksPerSuperRaw shape <
          canonicalBPRelativeSummaryBlockCountRaw shape /
              canonicalBPRelativeSummaryBlocksPerSuperRaw shape + 1 :=
      have hblockRaw :
          block < canonicalBPRelativeSummaryBlockCountRaw shape := by
        simpa [canonicalBPRelativeSummaryBlockCount, hactive] using hblock
      PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
        (blockCount := canonicalBPRelativeSummaryBlockCountRaw shape)
        hblockRaw
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummarySuperCount,
      canonicalBPRelativeSummarySuperCountRaw, hactive] using hdiv
  · simp [canonicalBPRelativeSummaryBlockCount, hactive] at hblock

def concreteBPRelativeRmmInteriorLocalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPLocalSparseOffsetTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorLevelCount shape)
      (concreteBPRelativeRmmInteriorOffsetWidth shape)
      (((concreteBPRelativeRmmInteriorMacroCount shape) *
          ((concreteBPRelativeRmmInteriorLevelCount shape) *
            (concreteBPRelativeRmmInteriorMacroSize shape))) *
        (concreteBPRelativeRmmInteriorOffsetWidth shape)) :=
  concreteBPLocalSparseOffsetTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorLevelCount shape)
    (concreteBPRelativeRmmInteriorOffsetWidth shape)
    (concreteBPRelativeRmmInteriorOffsetWidth_capacity shape)

def concreteBPRelativeRmmInteriorGlobalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPGlobalSparseBlockTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
      (concreteBPRelativeRmmInteriorBlockWidth shape)
      (((concreteBPRelativeRmmInteriorGlobalLevelCount shape) *
          (concreteBPRelativeRmmInteriorMacroCount shape)) *
        (concreteBPRelativeRmmInteriorBlockWidth shape)) :=
  concreteBPGlobalSparseBlockTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
    (concreteBPRelativeRmmInteriorBlockWidth shape)
    (concreteBPRelativeRmmInteriorMacroSize_pos shape)
    (concreteBPRelativeRmmInteriorBlockWidth_capacity shape)

theorem concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length <=
      logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorLevelCount shape
  let offsetWidth := concreteBPRelativeRmmInteriorOffsetWidth shape
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_size_ge
        shape hsize
  have hoffset :
      offsetWidth <= 5 * logBase := by
    simpa [offsetWidth, logBase] using
      concreteBPRelativeRmmInteriorOffsetWidth_le_five_logBase shape
  have hlevel :
      levelCount <= 5 * logBase := by
    simpa [levelCount, concreteBPRelativeRmmInteriorLevelCount,
      offsetWidth] using hoffset
  have hlevelOffset :
      levelCount * offsetWidth <=
        (5 * logBase) * (5 * logBase) :=
    Nat.mul_le_mul hlevel hoffset
  have hactual :
      (macroCount * (levelCount * macroSize)) * offsetWidth <=
        (2 * blockCount) * ((5 * logBase) * (5 * logBase)) := by
    have hmul := Nat.mul_le_mul hmacroCells hlevelOffset
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hbudgetNorm :
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) <=
        64 * (blockCount * (logBase * logBase)) := by
    let cell := logBase * (logBase * blockCount)
    have hle :
        50 * cell <= 64 * cell :=
      Nat.mul_le_mul_right cell
        (by decide : 50 <= 64)
    calc
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) =
          2 * (5 * (5 * cell)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 50 * cell := by
        omega
      _ <= 64 * cell := hle
      _ = 64 * (blockCount * (logBase * logBase)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_comm]
  have hpayload :=
    (concreteBPRelativeRmmInteriorLocalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSquaredSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorLocalOffsetSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

theorem concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length <=
      logLogSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorGlobalLevelCount shape
  let blockWidth := concreteBPRelativeRmmInteriorBlockWidth shape
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlogPos : 1 <= logBase := by
    simp [logBase]
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_size_ge
        shape hsize
  have hmacroCellsBase :
      macroCount * (base * base) <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount,
      concreteBPRelativeRmmInteriorMacroSize, base,
      canonicalBPRelativeSummaryBase, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hmacroCells
  have hlevel :
      levelCount <= base + 1 := by
    simpa [levelCount, base] using
      concreteBPRelativeRmmInteriorGlobalLevelCount_le_base_succ_of_size_ge
        shape hsize
  have hwidth :
      blockWidth <= base := by
    simpa [blockWidth, base] using
      concreteBPRelativeRmmInteriorBlockWidth_le_base_of_size_ge shape hsize
  have hlevelWidth :
      levelCount * blockWidth <= (base + 1) * base :=
    Nat.mul_le_mul hlevel hwidth
  have hbasePair :
      (base + 1) * base <= 2 * (base * base) := by
    have hbaseLeSquare : base <= base * base := by
      calc
        base = 1 * base := by simp
        _ <= base * base :=
          Nat.mul_le_mul_right base (by exact hbasePos)
    calc
      (base + 1) * base = base * base + base := by
        rw [Nat.mul_comm, Nat.mul_add, Nat.mul_one]
      _ <= base * base + base * base :=
        Nat.add_le_add_left hbaseLeSquare (base * base)
      _ = 2 * (base * base) := by
        omega
  have hmacroPair :
      macroCount * ((base + 1) * base) <= 4 * blockCount := by
    have hleft :=
      Nat.mul_le_mul_left macroCount hbasePair
    have hright :=
      Nat.mul_le_mul_left 2 hmacroCellsBase
    exact Nat.le_trans hleft
      (by
        calc
          macroCount * (2 * (base * base)) =
              2 * (macroCount * (base * base)) := by
            simp [Nat.mul_assoc, Nat.mul_comm]
          _ <= 2 * (2 * blockCount) := hright
          _ = 4 * blockCount := by
            omega)
  have hactual :
      (levelCount * macroCount) * blockWidth <=
        4 * blockCount := by
    have hmul :=
      Nat.mul_le_mul_left macroCount hlevelWidth
    exact Nat.le_trans
      (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          hmul)
      hmacroPair
  have hbudgetNorm :
      4 * blockCount <= 32 * (blockCount * logBase) := by
    have hblockLog : blockCount <= blockCount * logBase := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left blockCount hlogPos
    have hfourLog : 4 * blockCount <= 4 * (blockCount * logBase) :=
      Nat.mul_le_mul_left 4 hblockLog
    have hfourLe :
        4 * (blockCount * logBase) <=
          32 * (blockCount * logBase) :=
      Nat.mul_le_mul_right (blockCount * logBase)
        (by decide : 4 <= 32)
    exact Nat.le_trans hfourLog hfourLe
  have hpayload :=
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorGlobalMacroSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

def concreteBPRelativeRmmInteriorDirectoryPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length +
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length +
      (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length

/--
Canonical payload-live relative interior directory backed by B's charged
relative min/max/arg summary table plus the two-level local/global sparse
navigator.
-/
def concreteBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  by_cases hlarge : 2 ^ 128 <= shape.size
  · exact
      { payload := table.payload ++ localTable.payload ++ globalTable.payload
        payload_length_eq := by
          simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
            localTable, globalTable, table, Nat.add_assoc]
        payloadWordsRead := fun startBlock count =>
          bpTwoLevelInteriorCandidateWordsRead localTable globalTable table
            startBlock count
        rangeMinCosted := fun startBlock count =>
          bpTwoLevelInteriorCandidateCosted localTable globalTable table
            startBlock count
        rangeMin_cost_le := by
          intro startBlock count
          have hcost :=
            bpTwoLevelInteriorCandidateCosted_cost_le_thirty
              localTable globalTable table startBlock count
          unfold concreteBPRelativeRmmInteriorQueryCost
          simpa using hcost
        rangeMin_exact := by
          intro startBlock count hcount hbound
          exact
            bpTwoLevelInteriorCandidateCosted_erase_exact
              localTable globalTable table
              (concreteBPRelativeRmmInteriorMacroSize_pos shape)
              hcount hbound
              (by
                intro block hblock
                exact
                  PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
                    (blockCount := canonicalBPRelativeSummaryBlockCount shape)
                    hblock)
              (by
                have hmacroSize :=
                  concreteBPRelativeRmmInteriorMacroSize_pos shape
                have hlt :=
                  Nat.lt_div_mul_add hmacroSize
                    (a := canonicalBPRelativeSummaryBlockCount shape)
                have hlt' : canonicalBPRelativeSummaryBlockCount shape <
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape := by
                  simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using hlt
                have hle : canonicalBPRelativeSummaryBlockCount shape <=
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape :=
                  Nat.le_of_lt hlt'
                simpa [concreteBPRelativeRmmInteriorMacroCount] using hle)
              (by
                intro localCount hlocalPos hlocalLe
                have hcap :
                    localCount <
                      2 ^ concreteBPRelativeRmmInteriorLevelCount shape := by
                  have hmacroCap :=
                    concreteBPRelativeRmmInteriorOffsetWidth_capacity shape
                  unfold concreteBPRelativeRmmInteriorLevelCount
                  exact Nat.lt_of_le_of_lt hlocalLe hmacroCap
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hlocalPos hcap
                omega)
              (by
                intro macroSpanCount hspanPos hspanLe
                have hcap :
                    macroSpanCount <
                      2 ^
                        concreteBPRelativeRmmInteriorGlobalLevelCount shape := by
                  exact
                    Nat.lt_of_le_of_lt hspanLe
                      (concreteBPRelativeRmmInteriorGlobalLevelCount_capacity
                        shape)
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hspanPos hcap
                omega)
              (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
              (canonicalBPRelativeSummary_cover shape)
              (by
                intro block hblock
                exact
                  canonicalBPRelativeSummary_block_div_lt_superCount
                    (shape := shape) hblock)
        read_words_length_le_machine := by
          intro startBlock count word hmem
          have hbudget :=
            concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge
              shape hlarge
          rcases hbudget with
            ⟨_hlittle, _hbudgetEq, _hpayloadBudget, _hactive,
              _hoffsetCapacity, hrelativeMachine, hblockCapacity,
              _hsummaryExact, _hbaselineRead, _hminRead, _hmaxRead,
              _hargRead⟩
          have hoffsetMachine :
              concreteBPRelativeRmmInteriorOffsetWidth shape <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
            have hlargeRegime :=
              canonicalBPRelativeSummaryLargeRegime_of_size_ge
                (shape := shape) hlarge
            rcases canonicalBPRelativeSummary_large_parts
                (shape := shape) hlargeRegime with
              ⟨_hbaseLe, _hsuperWidth, hspan, _hblockWidth,
                _hrelativeLeSuper⟩
            let base := canonicalBPRelativeSummaryBase shape
            have hbasePos : 0 < base := by
              simp [base, canonicalBPRelativeSummaryBase]
            have hbaseSqPos : 0 < base * base :=
              Nat.mul_pos hbasePos hbasePos
            have hmacroLtSpan :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 * bpSuperblockSpan
                    (canonicalBPRelativeSummaryBlockSizeRaw shape)
                    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) := by
              have hlt4 :
                  1 * (base * base) < 4 * (base * base) := by
                exact Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4)
                  hbaseSqPos
              have htwoTwo :
                  2 * (2 * (base * base)) = 4 * (base * base) := by
                omega
              rw [← htwoTwo] at hlt4
              simpa [base, concreteBPRelativeRmmInteriorMacroSize,
                canonicalBPRelativeSummaryBlockSizeRaw,
                canonicalBPRelativeSummaryBlocksPerSuperRaw,
                bpSuperblockSpan, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hlt4
            have hmacroRel :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape :=
              Nat.lt_trans hmacroLtSpan hspan
            have hoffsetRel :
                concreteBPRelativeRmmInteriorOffsetWidth shape <=
                  canonicalBPRelativeSummaryRelativeWidthRaw shape := by
              unfold concreteBPRelativeRmmInteriorOffsetWidth
              unfold SuccinctRankProposal.machineWordBits
              exact
                natLog2_succ_le_of_pos_lt_pow
                  (concreteBPRelativeRmmInteriorMacroSize_pos shape)
                  hmacroRel
            exact Nat.le_trans hoffsetRel hrelativeMachine
          have hblockMachine :
              concreteBPRelativeRmmInteriorBlockWidth shape <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
            unfold concreteBPRelativeRmmInteriorBlockWidth
            unfold SuccinctRankProposal.machineWordBits
            exact
              natLog2_succ_le_of_pos_lt_pow
                (by
                  have hcountPos :
                      0 < canonicalBPRelativeSummaryBlockCount shape := by
                    have hparams :=
                      concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge
                        shape hlarge
                    rcases hparams with
                      ⟨_hb, _hps, _hc, _hs, _hr, _hl, _ha, _hbs,
                        _hbps, hcountPos, _hcover, _hcountLe,
                        _hmachine, _hp, _he, _hr1, _hr2, _hr3, _hr4⟩
                    simpa [canonicalBPRelativeSummaryBlockCount, _ha] using
                      hcountPos
                  exact hcountPos)
                (by
                  simpa [concreteBPRelativeRmmInteriorBlockWidth,
                    SuccinctRankProposal.machineWordBits,
                    canonicalBPRelativeSummaryBlockCount, _hactive] using
                    hblockCapacity)
          exact
            bpTwoLevelInteriorCandidateWordsRead_length_le_machine
              localTable globalTable table hoffsetMachine hblockMachine
              (canonicalBPRelativeSummary_superWidth_machine shape)
              (canonicalBPRelativeSummary_relativeWidth_machine shape)
              hmem }
  · exact
      { payload := table.payload ++ localTable.payload ++ globalTable.payload
        payload_length_eq := by
          simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
            localTable, globalTable, table, Nat.add_assoc]
        payloadWordsRead := fun _ _ => []
        rangeMinCosted := fun startBlock count =>
          { value :=
              if 0 < count ∧
                  startBlock + count <=
                    canonicalBPRelativeSummaryBlockCount shape then
                some
                  (bpRangeMinExcess shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count,
                    bpRangeArgMinPrefixPos shape
                      (canonicalBPRelativeSummaryBlockSize shape)
                      startBlock count)
              else
                none
            cost := 1 }
        rangeMin_cost_le := by
          intro startBlock count
          unfold concreteBPRelativeRmmInteriorQueryCost
          simp
        rangeMin_exact := by
          intro startBlock count hcount hbound
          have hcond :
              0 < count ∧
                startBlock + count <=
                  canonicalBPRelativeSummaryBlockCount shape :=
            ⟨hcount, hbound⟩
          simp [hcond]
        read_words_length_le_machine := by
          intro startBlock count word hmem
          cases hmem }

theorem concreteBPRelativeRmmInteriorDirectory_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let directory := concreteBPRelativeRmmInteriorDirectory shape
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  let localOffsetBudget :=
    logLogSquaredSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size
  let globalMacroBudget :=
    logLogSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size
  let topRoutingBudget :=
    sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots shape.size
  have hbudget :=
    concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge
      shape hsize
  rcases hbudget with
    ⟨hlittle, _hbudgetEq, hpayloadReserve, _hactive, _hoffsetCapacity,
      _hrelativeMachine, _hblockCapacity, _hsummaryExact, _hbaselineRead,
      _hminRead, _hmaxRead, _hargRead⟩
  have hlocalPayload :
      localTable.payload.length <= localOffsetBudget := by
    simpa [localTable, localOffsetBudget] using
      concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge
        shape hsize
  have hglobalPayload :
      globalTable.payload.length <= globalMacroBudget := by
    simpa [globalTable, globalMacroBudget] using
      concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge
        shape hsize
  have hpayload :
      concreteBPRelativeRmmInteriorDirectoryPayloadLength shape <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    have hsum :
        table.payload.length + localTable.payload.length +
            globalTable.payload.length <=
          table.payload.length + localOffsetBudget +
            globalMacroBudget + topRoutingBudget := by
      omega
    exact Nat.le_trans
      (by
        simpa [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
          table, localTable, globalTable, Nat.add_assoc] using hsum)
      hpayloadReserve
  have hdir := directory.profile
  exact
    ⟨hlittle,
      by
        rw [hdir.1]
        exact hpayload,
      hdir.2.1, hdir.2.2.1, hdir.2.2.2⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_interior_scan_not_constant
    (shape : Cartesian.CartesianShape)
    (hblockSize : 0 < canonicalBPRelativeSummaryBlockSize shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.interiorScanCosted_no_uniform_constant
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      hblockSize


end SuccinctCloseProposal
end RMQ

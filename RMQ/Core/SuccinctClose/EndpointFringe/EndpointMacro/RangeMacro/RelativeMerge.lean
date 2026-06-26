import RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro.PayloadMacro

/-!
# Endpoint-fringe relative-rmM merge exactness

Split from `RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

theorem bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        shape.bpCode.length + 1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        shape.bpCode.length + 1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hleftPair :
      (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
        bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerLeft hleftBound
        (by
          intro pos hlo hhi
          exact hmin hlo (hleftInside hlo hhi))
        (by
          intro pos hlo hhi
          exact hleftmost hlo hhi)
  have hrightCount :
      0 <
        rightClose -
            blockStartOf blockSize
              (blockOfClose blockSize rightClose) +
          2 := by
    omega
  have hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) := by
    exact
      bpPrefixRangeMinExcess_ge_of_all_prefix_ge
        hrightCount hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hmin hinside.1 hinside.2)
  have hmiddleLe :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) <= middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_ge_of_all_prefix_ge
          (shape := shape) (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower := bpExcessAt shape (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hinside :=
              hmiddleInside (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hmin hinside.1 hinside.2)
    · simp [hblocks] at hmiddle
  simpa [hleftPair] using
    bpCandidateMerge3?_eq_some_left_of_fst_le
      (left := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      (by
        intro middle hmiddle
        exact hmiddleLe middle hmiddle)
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hrightPair :
      (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hleftGt :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) < middle.1) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hrightPair] using
    bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (right := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      hleftGt
      (by
        intro middle hmiddle
        exact hmiddleGt middle hmiddle)

theorem bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose)
    (hmiddlePair :
      (bpRangeMinExcess shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1),
        bpRangeArgMinPrefixPos shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hmiddleLeft :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hblocks, hmiddlePair] using
    bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (middle := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      hmiddleLeft
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_query_semantics
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (_hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (_hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let answerPrefix := answerClose + 1
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hanswerCloseBound := bpCloseOfInorder?_bounds shape hanswer
  have hrightStartLe :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hleftNextStart :
      leftClose < blockStartOf blockSize (leftBlock + 1) := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    simpa [leftBlock, blockStartOf_succ] using hend
  have hleftLimitEq :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) =
        blockStartOf blockSize (leftBlock + 1) + 1 := by
    have hstart :
        blockStartOf blockSize leftBlock <= leftClose := by
      simpa [leftBlock] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := leftClose))
    have hsucc :
        blockStartOf blockSize leftBlock + blockSize =
          blockStartOf blockSize (leftBlock + 1) :=
      blockStartOf_succ blockSize leftBlock
    omega
  have hrightLimitEq :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) =
        rightClose + 2 := by
    omega
  have hleftToRightStart :
      blockStartOf blockSize (leftBlock + 1) <=
        blockStartOf blockSize rightBlock := by
    exact blockStartOf_mono (blockSize := blockSize) (by
      simpa [leftBlock, rightBlock] using hcross)
  have hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) <=
        shape.bpCode.length + 1 := by
    rw [hleftLimitEq]
    omega
  have hrightBound :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) <=
        shape.bpCode.length + 1 := by
    rw [hrightLimitEq]
    omega
  have hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1 := by
    intro _hgap
    have hstart :
        blockStartOf blockSize
            (blockOfClose blockSize rightClose) <= rightClose :=
      blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose)
    omega
  have hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2 := by
    intro pos _hlo hhi
    have hhi' :
        pos < blockStartOf blockSize (leftBlock + 1) + 1 := by
      simpa [leftBlock, hleftLimitEq] using hhi
    have hleRight :
        blockStartOf blockSize (leftBlock + 1) + 1 <= rightClose + 1 := by
      omega
    omega
  have hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) := by
      have hlt := hleftNextStart
      have hmono :
          blockStartOf blockSize (leftBlock + 1) <=
            blockStartOf blockSize rightBlock :=
        hleftToRightStart
      simpa [rightBlock] using (by omega : leftClose + 1 <=
        blockStartOf blockSize rightBlock)
    constructor
    · exact Nat.le_trans hleftLe hlo
    · simpa [rightBlock, hrightLimitEq] using hhi
  have hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos _hgap hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize leftClose + 1) := by
      simpa [leftBlock] using (by omega :
        leftClose + 1 <= blockStartOf blockSize (leftBlock + 1))
    constructor
    · exact Nat.le_trans hleftLe hlo
    · have hrightLeClose :
          blockStartOf blockSize
              (blockOfClose blockSize rightClose) <= rightClose :=
        blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose)
      omega
  have hanswerMem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hanswerUpper : answerPrefix < rightClose + 2 := by
    simpa [answerPrefix] using (by omega :
      answerClose + 1 < rightClose + 2)
  by_cases hanswerLeft :
      answerPrefix <
        leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)
  · exact
      bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
        leftClose rightClose
        (by
          constructor
          · simpa [answerPrefix] using hanswerMem.1
          · exact hanswerLeft)
        (by simpa [leftBlock] using hleftBound)
        hleftInside
        (by simpa [rightBlock] using hrightBound)
        hrightInside
        hmiddleBound
        hmiddleInside
        hmin hleftmost
  · by_cases hanswerRight :
        blockStartOf blockSize rightBlock + 1 <= answerPrefix
    · have hrightAnswer :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
            answerClose + 1 /\
          answerClose + 1 <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        constructor
        · simpa [rightBlock, answerPrefix] using
            (Nat.le_trans (Nat.le_of_lt (by omega :
              blockStartOf blockSize rightBlock <
                blockStartOf blockSize rightBlock + 1)) hanswerRight)
        · simpa [rightBlock, hrightLimitEq, answerPrefix] using hanswerUpper
      have hleftBefore :
          forall {pos : Nat},
            leftClose + 1 <= pos ->
              pos <
                leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) ->
                pos < answerClose + 1 := by
        intro pos _hlo hhi
        have hlimit :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix := by
          omega
        simpa [answerPrefix] using (by omega : pos < answerPrefix)
      have hmiddleBefore :
          forall {pos : Nat},
            blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose ->
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose + 1) <= pos ->
                pos <
                  blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                    1 ->
                  leftClose + 1 <= pos /\ pos < answerClose + 1 := by
        intro pos hgap hlo hhi
        have hinside := hmiddleInside (pos := pos) hgap hlo hhi
        constructor
        · exact hinside.1
        · have hhi' : pos < blockStartOf blockSize rightBlock + 1 := by
            simpa [rightBlock] using hhi
          simpa [answerPrefix] using
            (by omega : pos < answerPrefix)
      exact
        bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
          leftClose rightClose
          (by
            exact
              bpPrefixRangeWitness_eq_of_leftmost_min_excess
                hrightAnswer
                (by simpa [rightBlock] using hrightBound)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo hhi
                  exact hmin hinside.1 hinside.2)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo (by omega)
                  exact hleftmost hinside.1 hhi))
          (by
            have hleftCount :
                0 <
                  blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose := by
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := leftClose)
                  hblockSize
              omega
            exact
              bpPrefixRangeMinExcess_gt_of_all_prefix_gt
                hleftCount
                (by simpa [leftBlock] using hleftBound)
                (by
                  intro pos hlo hhi
                  exact hleftmost hlo (hleftBefore hlo hhi)))
          (by
            intro middle hmiddle
            by_cases hgap :
                blockOfClose blockSize leftClose + 1 <
                  blockOfClose blockSize rightClose
            · simp [hgap] at hmiddle
              subst middle
              have hcount :
                  0 <
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1 := by
                omega
              exact
                bpRangeMinExcess_gt_of_all_prefix_gt
                  (shape := shape) (blockSize := blockSize)
                  (startBlock :=
                    blockOfClose blockSize leftClose + 1)
                  (blockCount :=
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1)
                  (lower := bpExcessAt shape (answerClose + 1))
                  hcount
                  (by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    simpa [hend] using hmiddleBound hgap)
                  (by
                    intro pos hlo hhi
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    have hbefore :=
                      hmiddleBefore (pos := pos) hgap hlo
                        (by simpa [hend] using hhi)
                    exact hleftmost hbefore.1 hbefore.2)
            · simp [hgap] at hmiddle)
    · have hmiddleGap :
          blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose := by
        by_cases heq : rightBlock = leftBlock + 1
        · have hlimitEq :
              leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) =
                blockStartOf blockSize rightBlock + 1 := by
            simpa [leftBlock, rightBlock, heq] using hleftLimitEq
          have hlimitLe :
              blockStartOf blockSize rightBlock + 1 <= answerPrefix := by
            simpa [hlimitEq] using (Nat.le_of_not_gt hanswerLeft)
          exact False.elim (hanswerRight hlimitLe)
        · have hcross' : leftBlock < rightBlock := by
            simpa [leftBlock, rightBlock] using hcross
          have hgap' : leftBlock + 1 < rightBlock := by
            omega
          simpa [leftBlock, rightBlock] using hgap'
      have hrangeEndEq :
          blockOfClose blockSize leftClose + 1 +
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1) =
            blockOfClose blockSize rightClose := by
        omega
      let answerBlock := blockOfClose blockSize answerClose
      have hanswerBlockMem :
          blockOfClose blockSize leftClose + 1 <= answerBlock /\
            answerBlock <
              blockOfClose blockSize leftClose + 1 +
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1) := by
        have hnotLeftLe :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix :=
          Nat.le_of_not_gt hanswerLeft
        have hanswerBeforeRight :
            answerPrefix < blockStartOf blockSize rightBlock + 1 :=
          Nat.lt_of_not_ge hanswerRight
        have hanswerCloseGeNext :
            blockStartOf blockSize (leftBlock + 1) <= answerClose := by
          have hlimit :
              blockStartOf blockSize (leftBlock + 1) + 1 <=
                answerPrefix := by
            simpa [leftBlock, hleftLimitEq] using hnotLeftLe
          omega
        have hanswerCloseLtRight :
            answerClose < blockStartOf blockSize rightBlock := by
          omega
        constructor
        · have hanswerBlockGeLeftNext : leftBlock + 1 <= answerBlock := by
            by_cases hge : leftBlock + 1 <= answerBlock
            · exact hge
            · have hltBlock : answerBlock < leftBlock + 1 :=
                Nat.lt_of_not_ge hge
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := answerClose)
                  hblockSize
              have hend' :
                  answerClose <
                    blockStartOf blockSize answerBlock + blockSize := by
                simpa [answerBlock] using hend
              have hsucc :
                  blockStartOf blockSize answerBlock + blockSize =
                    blockStartOf blockSize (answerBlock + 1) :=
                blockStartOf_succ blockSize answerBlock
              have hmono :
                  blockStartOf blockSize (answerBlock + 1) <=
                    blockStartOf blockSize (leftBlock + 1) :=
                blockStartOf_mono (blockSize := blockSize) (by omega)
              have hnext :
                  answerClose < blockStartOf blockSize (leftBlock + 1) := by
                omega
              omega
          simpa [answerBlock, leftBlock] using hanswerBlockGeLeftNext
        · have hanswerBlockLtRight : answerBlock < rightBlock := by
            by_cases hlt : answerBlock < rightBlock
            · exact hlt
            · have hge : rightBlock <= answerBlock := Nat.le_of_not_gt hlt
              have hstartAns :=
                blockStartOf_blockOfClose_le
                  (blockSize := blockSize) (close := answerClose)
              have hstartAns' :
                  blockStartOf blockSize answerBlock <= answerClose := by
                simpa [answerBlock] using hstartAns
              have hmono :
                  blockStartOf blockSize rightBlock <=
                    blockStartOf blockSize answerBlock :=
                blockStartOf_mono (blockSize := blockSize) hge
              omega
          simpa [answerBlock, rightBlock, hrangeEndEq] using
            hanswerBlockLtRight
      have hanswerBlockLtRight : answerBlock < rightBlock := by
        have h := hanswerBlockMem.2
        simpa [answerBlock, rightBlock, hrangeEndEq] using h
      have hanswerBlockTarget :
          bpBlockArgMinPrefixPos shape blockSize answerBlock =
            answerPrefix := by
        have hlocalMem :
            blockStartOf blockSize answerBlock <= answerPrefix /\
              answerPrefix <
                blockStartOf blockSize answerBlock + (blockSize + 1) := by
          have hstart :=
            blockStartOf_blockOfClose_le
              (blockSize := blockSize) (close := answerClose)
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := answerClose)
              hblockSize
          constructor
          · simpa [answerBlock, answerPrefix] using
              (by omega : blockStartOf blockSize
                  (blockOfClose blockSize answerClose) <=
                answerClose + 1)
          · simpa [answerBlock, answerPrefix] using
              (by omega : answerClose + 1 <
                blockStartOf blockSize
                    (blockOfClose blockSize answerClose) +
                  (blockSize + 1))
        have hlocalBound :
            blockStartOf blockSize answerBlock + (blockSize + 1) <=
              shape.bpCode.length + 1 := by
          have hmono :
              blockStartOf blockSize (answerBlock + 1) <=
                blockStartOf blockSize rightBlock :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          have hsucc :
              blockStartOf blockSize answerBlock + blockSize =
                blockStartOf blockSize (answerBlock + 1) :=
            blockStartOf_succ blockSize answerBlock
          omega
        exact
          bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
            hlocalMem hlocalBound
            (by
              intro pos hlo hhi
              have hinside :
                  leftClose + 1 <= pos /\ pos < rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize answerBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize answerBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        have h := hanswerBlockMem.1
                        simpa [answerBlock, leftBlock] using h)
                  omega
                have hupper :
                    pos < blockStartOf blockSize rightBlock + 1 := by
                  have hanswerBlockLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  have hmono :
                      blockStartOf blockSize (answerBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize answerBlock + blockSize =
                        blockStartOf blockSize (answerBlock + 1) :=
                    blockStartOf_succ blockSize answerBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hlo
                · have hrightStartLe' :
                    blockStartOf blockSize rightBlock <= rightClose :=
                    hrightStartLe
                  omega
              exact hmin hinside.1 hinside.2)
            (by
              intro pos hlo hhi
              have hstartLower :
                  leftClose + 1 <= blockStartOf blockSize answerBlock := by
                have hleftLeBlock :
                    blockStartOf blockSize (leftBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize)
                    (by
                      have h := hanswerBlockMem.1
                      simpa [answerBlock, leftBlock] using h)
                omega
              exact hleftmost (Nat.le_trans hstartLower hlo) hhi)
      have hmiddlePair :
          (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
            bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) =
            (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
        exact
          bpRangeWitness_eq_of_leftmost_block_candidate
            hanswerBlockMem
            hanswerBlockTarget
            (by
              intro candidateBlock hcLo hcHi
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hend :
                      blockOfClose blockSize leftClose + 1 +
                          (blockOfClose blockSize rightClose -
                            blockOfClose blockSize leftClose - 1) =
                        blockOfClose blockSize rightClose := by
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hinside :
                  leftClose + 1 <=
                      bpBlockArgMinPrefixPos shape blockSize candidateBlock /\
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        simpa [leftBlock] using hcLo)
                  omega
                have hupper :
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      blockStartOf blockSize rightBlock + 1 := by
                  have hcandidateLtRight : candidateBlock < rightBlock := by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    omega
                  have hmono :
                      blockStartOf blockSize (candidateBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize candidateBlock + blockSize =
                        blockStartOf blockSize (candidateBlock + 1) :=
                    blockStartOf_succ blockSize candidateBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hcandMem.1
                · omega
              exact hmin hinside.1 hinside.2)
            (by
              intro candidateBlock hcLo hcLt
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hABLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hlower :
                  leftClose + 1 <=
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by simpa [leftBlock] using hcLo)
                  omega
                exact Nat.le_trans hstartLower hcandMem.1
              have hbefore :
                  bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                    answerPrefix := by
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                have hanswerLower :
                    blockStartOf blockSize answerBlock + 1 <= answerPrefix := by
                  have hstart :=
                    blockStartOf_blockOfClose_le
                      (blockSize := blockSize) (close := answerClose)
                  simpa [answerBlock, answerPrefix] using
                    (by omega : blockStartOf blockSize
                        (blockOfClose blockSize answerClose) + 1 <=
                      answerClose + 1)
                omega
              exact hleftmost hlower (by simpa [answerPrefix] using hbefore))
      have hleftGt :
          bpExcessAt shape (answerClose + 1) <
            bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) := by
        have hleftCount :
            0 <
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose := by
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := leftClose)
              hblockSize
          omega
        exact
          bpPrefixRangeMinExcess_gt_of_all_prefix_gt
            hleftCount
            (by simpa [leftBlock] using hleftBound)
            (by
              intro pos hlo hhi
              have hlimit :
                  leftClose + 1 +
                      (blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize - leftClose) <= answerPrefix :=
                Nat.le_of_not_gt hanswerLeft
              exact hleftmost hlo (by simpa [answerPrefix] using
                (by omega : pos < answerPrefix)))
      have hrightLe :
          bpExcessAt shape (answerClose + 1) <=
            bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        have hrightCount :
            0 <
              rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2 := by
          omega
        exact
          bpPrefixRangeMinExcess_ge_of_all_prefix_ge
            hrightCount
            (by simpa [rightBlock] using hrightBound)
            (by
              intro pos hlo hhi
              have hinside := hrightInside hlo hhi
              exact hmin hinside.1 hinside.2)
      exact
        bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
          leftClose rightClose hmiddleGap hmiddlePair hleftGt hrightLe

theorem bpRelativeRmmCandidateMerge_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross hsemantic.1 hsemantic.2

end SuccinctCloseProposal
end RMQ

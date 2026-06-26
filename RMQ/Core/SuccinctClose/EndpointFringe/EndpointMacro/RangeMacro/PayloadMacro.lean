import RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro.RangeTables

/-!
# Payload-live endpoint-fringe range macro

Split from `RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

structure PayloadLiveBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  leftFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth leftOverhead
      (endpointLeftFringeRanges blockSize blockCount)
  interior :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
      interiorOverhead (interiorBlockPairRanges blockCount)
  rightFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth rightOverhead
      (endpointRightFringeRanges blockSize blockCount)

namespace PayloadLiveBPEndpointFringeRangeMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    List Bool :=
  component.leftFringe.payload ++ component.interior.payload ++
    component.rightFringe.payload

def interiorIndex
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (_component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Nat :=
  blockPairRangeSlot blockCount
    (blockOfClose blockSize leftClose)
    (blockOfClose blockSize rightClose)

def interiorWitnessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interior.rangeWitnessCosted
      (component.interiorIndex leftClose rightClose)
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (component.leftFringe.rangeWitnessCosted
      (endpointFringeSlot blockSize leftClose)) fun left? =>
    Costed.bind
      (component.interiorWitnessCosted leftClose rightClose) fun middle? =>
      Costed.map
        (fun right? =>
          bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
        (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose))

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
      leftOverhead + interiorOverhead + rightOverhead := by
  simp [payload, component.leftFringe.payload_length,
    component.interior.payload_length, component.rightFringe.payload_length]
  omega

theorem interiorWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.interiorWitnessCosted leftClose rightClose).cost <= 2 := by
  unfold interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hblocks]
    exact component.interior.rangeWitnessCosted_cost_le_two
      (component.interiorIndex leftClose rightClose)
  · simp [hblocks, Costed.pure]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  have hleft :=
    component.leftFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize leftClose)
  have hmiddle :=
    component.interiorWitnessCosted_cost_le_two leftClose rightClose
  have hright :=
    component.rightFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize rightClose)
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)) := by
  have hleft :
      (component.leftFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize leftClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.leftFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize leftClose)
  have hright :
      (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.rightFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize rightClose)
  have hmiddle :
      (component.interior.rangeWitnessCosted
          (component.interiorIndex leftClose rightClose)).value =
        match
          (bpRangeMinExcessEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]?,
          (bpRangeArgMinPrefixPosEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.interior.rangeWitnessCosted_erase
        (component.interiorIndex leftClose rightClose)
  unfold lcaCloseCosted interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [Costed.bind, Costed.map, Costed.erase,
      hleft, hmiddle, hright, hblocks]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hblocks]

theorem lcaCloseCosted_exact_of_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hmerge :
      bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  simp [component.lcaCloseCosted_erase, hmerge, bpCandidateClose?]

theorem lcaCloseCosted_exact_of_decoded_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hmerge :
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
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
  have hleftMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hleftArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeArgMinEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hrightMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hrightBlock
  have hrightArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeArgMinEntries_get?_of_close_bounds
      hblockSize hrightBlock
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddleMin :
        (bpRangeMinExcessEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    have hmiddleArg :
        (bpRangeArgMinPrefixPosEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    simpa [hleftMin, hleftArg, hmiddleMin, hmiddleArg,
      hrightMin, hrightArg, hblocks] using hmerge
  · simpa [hleftMin, hleftArg, hrightMin, hrightArg, hblocks]
      using hmerge

theorem lcaCloseCosted_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
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
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
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
  have hmerge :
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
  exact hmerge

theorem lcaCloseCosted_exact_of_decoded_right_fringe_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
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
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
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

theorem lcaCloseCosted_exact_of_decoded_middle_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
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
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
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

theorem lcaCloseCosted_exact_of_spanning_root_left_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
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
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
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
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
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
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_left_fringe_leftmost
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hanswerLeft hleftBound hleftInside
      hrightBound hrightInside hmiddleBound hmiddleInside
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_right_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerRight :
      blockStartOf blockSize (blockOfClose blockSize rightClose) <=
          answerClose + 1 /\
        answerClose + 1 <
          blockStartOf blockSize (blockOfClose blockSize rightClose) +
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hleftBefore :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < answerClose + 1)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
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
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleBefore :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < answerClose + 1) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  have hrightPair :
      (bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt
            (Cartesian.CartesianShape.node leftShape rightShape)
            (answerClose + 1),
          answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerRight hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hsemantic.1 hinside.1 hinside.2)
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo (by omega)
          exact hsemantic.2 hinside.1 hhi)
  have hleftCount :
      0 <
        blockStartOf blockSize
            (blockOfClose blockSize leftClose) +
          blockSize - leftClose := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    omega
  have hleftGt :
      bpExcessAt
          (Cartesian.CartesianShape.node leftShape rightShape)
          (answerClose + 1) <
        bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) := by
    exact
      bpPrefixRangeMinExcess_gt_of_all_prefix_gt
        hleftCount hleftBound
        (by
          intro pos hlo hhi
          exact hsemantic.2 hlo (hleftBefore hlo hhi))
  have hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess
                (Cartesian.CartesianShape.node leftShape rightShape)
                blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos
                  (Cartesian.CartesianShape.node leftShape rightShape)
                  blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1) < middle.1 := by
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
        bpRangeMinExcess_gt_of_all_prefix_gt
          (shape := Cartesian.CartesianShape.node leftShape rightShape)
          (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower :=
            bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1))
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
            have hbefore :=
              hmiddleBefore (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hsemantic.2 hbefore.1 hbefore.2)
    · simp [hblocks] at hmiddle
  exact
    component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hrightPair hleftGt hmiddleGt

theorem lcaCloseCosted_exact_of_query_semantics_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
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
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
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
      component.lcaCloseCosted_exact_of_left_fringe_leftmost
        leftClose rightClose hblockSize hleftBlock hrightBlock
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
        component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
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
        component.lcaCloseCosted_exact_of_decoded_middle_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
          hmiddleGap hmiddlePair hleftGt hrightLe

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
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
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_cross_block
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  have hleft := component.leftFringe.read_words_length_le_machine hmachine
  have hmid := component.interior.read_words_length_le_machine hmachine
  have hright := component.rightFringe.read_words_length_le_machine hmachine
  exact ⟨hleft.1, hleft.2, hmid.1, hmid.2, hright.1, hright.2⟩

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  constructor
  · exact component.payload_length
  intro leftClose rightClose
  exact ⟨component.lcaCloseCosted_cost_le_six leftClose rightClose,
    component.lcaCloseCosted_erase leftClose rightClose⟩

theorem profile_cross_block_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  constructor
  · exact component.payload_length
  constructor
  · intro leftClose rightClose
    exact component.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hleftBlock hrightBlock hcross
  exact
    component.lcaCloseCosted_exact_of_query_cross_block
      hlen hbound hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross

end PayloadLiveBPEndpointFringeRangeMacro

end SuccinctCloseProposal
end RMQ

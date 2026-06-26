import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate

/-!
# Endpoint-fringe BP macro directory

Endpoint-fringe range tables and the payload-live endpoint-fringe macro
component used by the relative-rmM close-navigation path. The historical
`RMQ.SuccinctCloseProposal` namespace is preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace
def endpointFringeSlot (blockSize close : Nat) : Nat :=
  let block := blockOfClose blockSize close
  block * blockSize + (close - blockStartOf blockSize block)

def endpointLeftFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block + offset + 1, blockSize - offset)

def endpointRightFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block, offset + 2)

def endpointLeftFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointLeftFringeRangeOfSlot blockSize)

theorem endpointLeftFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointLeftFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointLeftFringeRanges]

theorem endpointFringeSlot_lt
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    endpointFringeSlot blockSize close < blockCount * blockSize := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  unfold endpointFringeSlot
  have hltStep :
      blockOfClose blockSize close * blockSize +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) <
        blockOfClose blockSize close * blockSize + blockSize :=
    Nat.add_lt_add_left hoffset
      (blockOfClose blockSize close * blockSize)
  have hstepEq :
      blockOfClose blockSize close * blockSize + blockSize =
        (blockOfClose blockSize close + 1) * blockSize := by
    simpa using
      (Nat.succ_mul (blockOfClose blockSize close) blockSize).symm
  have hmul :
      (blockOfClose blockSize close + 1) * blockSize <=
        blockCount * blockSize :=
    Nat.mul_le_mul_right blockSize (Nat.succ_le_of_lt hblock)
  exact Nat.lt_of_lt_of_le (by simpa [hstepEq] using hltStep) hmul

theorem endpointFringeSlot_div
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close / blockSize =
      blockOfClose blockSize close := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_div
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

theorem endpointFringeSlot_mod
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close % blockSize =
      close - blockStartOf blockSize (blockOfClose blockSize close) := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_mod
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

def endpointRightFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointRightFringeRangeOfSlot blockSize)

theorem endpointRightFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointRightFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointRightFringeRanges]

theorem endpointLeftFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointLeftFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (close + 1,
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  have hstart :
      blockStartOf blockSize (blockOfClose blockSize close) <= close :=
    blockStartOf_blockOfClose_le
  have hend :
      close <
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add hblockSize
  have hfirst :
      blockStartOf blockSize (blockOfClose blockSize close) +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) +
          1 =
        close + 1 := by
    omega
  have hcount :
      blockSize -
          (close - blockStartOf blockSize (blockOfClose blockSize close)) =
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize - close := by
    omega
  simp [endpointLeftFringeRanges, List.getElem?_map, hslotGet,
    endpointLeftFringeRangeOfSlot, hdiv, hmod, hfirst, hcount]

theorem endpointRightFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointRightFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (blockStartOf blockSize (blockOfClose blockSize close),
          close - blockStartOf blockSize (blockOfClose blockSize close) +
            2) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  simp [endpointRightFringeRanges, List.getElem?_map, hslotGet,
    endpointRightFringeRangeOfSlot, hdiv, hmod]

theorem endpointLeftFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointLeftFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

def interiorBlockPairRangeOfSlot
    (blockCount slot : Nat) : Nat × Nat :=
  let leftBlock := slot / blockCount
  let rightBlock := slot % blockCount
  if leftBlock + 1 < rightBlock then
    (leftBlock + 1, rightBlock - leftBlock - 1)
  else
    (leftBlock + 1, 0)

def interiorBlockPairRanges (blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockCount)).map
    (interiorBlockPairRangeOfSlot blockCount)

theorem interiorBlockPairRanges_length (blockCount : Nat) :
    (interiorBlockPairRanges blockCount).length =
      blockCount * blockCount := by
  simp [interiorBlockPairRanges]

theorem interiorBlockPairRanges_get?_of_gap_bounds
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (interiorBlockPairRanges blockCount)[
        blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some (leftBlock + 1, rightBlock - leftBlock - 1) := by
  have hslot :
      blockPairRangeSlot blockCount leftBlock rightBlock <
        blockCount * blockCount :=
    blockPairRangeSlot_lt hleft hright
  have hslotGet :
      (List.range (blockCount * blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
        some (blockPairRangeSlot blockCount leftBlock rightBlock) := by
    exact List.getElem?_range hslot
  have hdiv :
      blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
        leftBlock :=
    blockPairRangeSlot_div hright
  have hmod :
      blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
        rightBlock :=
    blockPairRangeSlot_mod hright
  simp [interiorBlockPairRanges, List.getElem?_map, hslotGet,
    interiorBlockPairRangeOfSlot, hdiv, hmod, hgap]

theorem interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeMinExcessEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeMinExcess shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeMinExcessEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

theorem interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeArgMinPrefixPosEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeArgMinPrefixPos shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

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
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
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

def concreteBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges blockSize blockCount) hwidth
  interior :=
    concreteBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (interiorBlockPairRanges blockCount) hwidth
  rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges blockSize blockCount) hwidth

theorem concreteBPEndpointFringeRangeMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) /\
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
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile := component.profile
  constructor
  · simpa [component, concreteBPEndpointFringeRangeMacro,
      endpointLeftFringeRanges_length, endpointRightFringeRanges_length,
      interiorBlockPairRanges_length] using hprofile.1
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
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
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hprofile.1]
    exact hbudget
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_query_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
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
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    (component.profile_cross_block_exact)
  have hpayload :=
    (concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth).1
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hpayload]
    exact hbudget
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

theorem concreteBPEndpointFringeRangeMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPEndpointFringeRangeMacro.read_words_length_le_machine
      (concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth) hmachine

/--
The right-spine shape of size four is the smallest useful witness that a macro
entry keyed only by the pair of endpoint close blocks cannot be exact.
-/
def blockPairMacroBlockerShape : Cartesian.CartesianShape :=
  Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
    (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
      (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
          Cartesian.CartesianShape.empty)))

/--
A concrete blocker for the tempting compact macro layout keyed only by
`(blockOfClose leftClose, blockOfClose rightClose)`.

For `blockSize = 3`, the two valid queries `[1, 4)` and `[2, 4)` in the
right-spine shape have endpoint closes in the same pair of close blocks, but
their BP-LCA close answers are different (`3` and `5`).  Therefore a macro
directory whose inter-block entry is only a function of the endpoint block pair
cannot satisfy the close-LCA exactness contract.
-/
theorem blockPairMacroDirectory_not_sufficient
    (blockAnswer : Nat -> Nat -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                blockAnswer (blockOfClose 3 leftClose)
                    (blockOfClose 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      blockAnswer (blockOfClose 3 3) (blockOfClose 3 7) = some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 3 := by
    simpa [blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Endpoint summary key for the tempting "read the endpoint block summaries, then
answer by key" macro shortcut.

This records exactly the information returned by the existing min/max summary
layer for one endpoint block: the block id plus that block's sampled minimum
and maximum BP excess.
-/
def endpointSummaryBlockKey
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    Nat × (Nat × Nat) :=
  let block := blockOfClose blockSize close
  (block,
    (bpBlockMinExcess shape blockSize block,
      bpBlockMaxExcess shape blockSize block))

/--
Reading only the two endpoint block min/max summaries still cannot be a global
macro answer.

On the same four-node right spine as `blockPairMacroDirectory_not_sufficient`,
the queries `[1, 4)` and `[2, 4)` have the same endpoint summary keys at
`blockSize = 3`, because their endpoints fall in the same two BP blocks.  Their
correct close answers are nevertheless different.  A concrete macro therefore
needs position-bearing endpoint/fringe or range-min witnesses; the existing
summary values alone are not enough to determine the answer close.
-/
theorem endpointSummaryBlockMacroDirectory_not_sufficient
    (summaryAnswer :
      (Nat × (Nat × Nat)) -> (Nat × (Nat × Nat)) -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                summaryAnswer
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 leftClose)
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 3)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    simpa [endpointSummaryBlockKey, blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Payload-live table of per-block close/LCA micro-codes.

The old `BlockMicroCodebook` stores only the finite codebook payload and takes
`codeOfBlock` as proof-side data.  This table is the missing charged classifier:
one fixed-width payload word per block is read to recover the code used for the
local close/LCA table.
-/
structure BlockCodeTable
    (blockCount codeCount codeWidth overhead : Nat) where
  codes : List Nat
  table : FixedWidthNatTable codes codeWidth
  codes_length_eq : codes.length = blockCount
  payload_length_eq : table.payload.length = overhead
  code_lt :
    forall {block code : Nat}, codes[block]? = some code -> code < codeCount

namespace BlockCodeTable

def payload
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) : List Bool :=
  classifier.table.payload

def codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Option Nat :=
  classifier.codes[block]?

def codeCosted
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  classifier.table.readCosted block

theorem payload_length
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead := by
  exact classifier.payload_length_eq

theorem codeCosted_cost
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost = 1 := by
  simp [codeCosted]

theorem codeCosted_cost_le_one
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost <= 1 := by
  simp [classifier.codeCosted_cost block]

theorem codeCosted_erase
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).erase = classifier.codeAt block := by
  simp [codeCosted, codeAt]

theorem codeCosted_exact_of_codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    (classifier.codeCosted block).erase = some code := by
  simpa [hcode] using classifier.codeCosted_erase block

theorem codeAt_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    code < codeCount := by
  exact classifier.code_lt (by simpa [codeAt] using hcode)

private theorem list_get?_exists_of_lt
    {α : Type} (xs : List α) {idx : Nat}
    (hidx : idx < xs.length) :
    exists value, xs[idx]? = some value := by
  induction xs generalizing idx with
  | nil =>
      simp at hidx
  | cons head tail ih =>
      cases idx with
      | zero =>
          exact ⟨head, by simp⟩
      | succ idx =>
          have htail : idx < tail.length := by
            simp at hidx
            exact hidx
          rcases ih htail with ⟨value, hvalue⟩
          exact ⟨value, by simpa using hvalue⟩

theorem codeAt_exists_of_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block : Nat}
    (hblock : block < blockCount) :
    exists code, classifier.codeAt block = some code := by
  have hidx : block < classifier.codes.length := by
    rw [classifier.codes_length_eq]
    exact hblock
  simpa [codeAt] using list_get?_exists_of_lt classifier.codes hidx

theorem profile
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead /\
      classifier.codes.length = blockCount /\
      forall block : Nat,
        (classifier.codeCosted block).cost <= 1 /\
          (classifier.codeCosted block).erase =
            classifier.codeAt block /\
          forall {code : Nat},
            classifier.codeAt block = some code -> code < codeCount := by
  constructor
  · exact classifier.payload_length
  constructor
  · exact classifier.codes_length_eq
  intro block
  constructor
  · exact classifier.codeCosted_cost_le_one block
  constructor
  · exact classifier.codeCosted_erase block
  intro code hcode
  exact classifier.codeAt_lt hcode

def ofEntries
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    BlockCodeTable blockCount codeCount codeWidth overhead where
  codes := codes
  table := FixedWidthNatTable.ofEntries codes codeWidth hwidth
  codes_length_eq := hlength
  payload_length_eq := by
    simpa [hoverhead] using
      (FixedWidthNatTable.ofEntries codes codeWidth hwidth).payload_length
  code_lt := hcode

theorem ofEntries_profile
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).payload.length = overhead /\
      (ofEntries blockCount codeCount codeWidth overhead codes hwidth
        hlength hoverhead hcode).codes.length = blockCount /\
      forall block : Nat,
        ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
          hlength hoverhead hcode).codeCosted block).cost <= 1 /\
          ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
            hlength hoverhead hcode).codeCosted block).erase =
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block /\
          forall {code : Nat},
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block = some code ->
              code < codeCount := by
  exact
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).profile

end BlockCodeTable

/--
Reusable micro-codebook for block-local BP close/LCA tables.

The dense table from `BlockLocalBPCloseLCATable.concrete` is no longer charged
once per block here.  Each block carries a small code into a finite codebook,
and the counted micro payload is the concatenation of the table payloads for
those codes.  This is the micro half that a real macro/micro BP navigation
scheme can consume.

This compatibility skeleton still takes `codeOfBlock` as a supplied classifier.
`PayloadLiveBlockMicroCodebook` below is the counted successor that stores and
reads that classifier from payload bits.
-/
structure BlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount tableOverhead : Nat) where
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  codeOfBlock : Nat -> Nat
  codeOfBlock_lt : forall block, codeOfBlock block < codeCount
  payload : List Bool
  payload_eq_tables :
    payload =
      (List.range codeCount).flatMap fun code => (table code).payload
  payload_length_eq : payload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall block : Nat,
      BlockLocalBPCloseLCASpec shape
        (blockStartOf blockSize block) blockSize
        (entriesByCode (codeOfBlock block)) slotIndex

namespace BlockMicroCodebook

def tableForBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block : Nat) :
    FixedWidthOptionNatTable
      (micro.entriesByCode (micro.codeOfBlock block)) micro.fieldWidth :=
  micro.table (micro.codeOfBlock block)

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((micro.tableForBlock block).readCosted
      (micro.slotIndex
        (leftClose - blockStartOf blockSize block)
        (rightClose - blockStartOf blockSize block)))

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead := by
  exact micro.payload_length_eq

theorem lcaCloseCostedAtBlock_cost
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost = 1 := by
  simp [lcaCloseCostedAtBlock, Costed.map_cost]

theorem lcaCloseCostedAtBlock_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 1 := by
  simp [micro.lcaCloseCostedAtBlock_cost block leftClose rightClose]

theorem lcaCloseCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 1 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_one
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    {block left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  exact
    blockLocalBPCloseLCA_read_exact
      (micro.tableForBlock block) (micro.block_spec block)
      hlen hbound hleft hright hanswer hleftLo hleftHi
      hrightLo hrightHi hanswerLo hanswerHi

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (hblockSize : 0 < blockSize)
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
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hlen hbound hleft hright hanswer
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 1) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      rightClose ->
                    rightClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      answerClose ->
                    answerClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                      (micro.lcaCloseCosted
                        leftClose rightClose).erase =
                        some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_one leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hlen hbound hleft
      hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end BlockMicroCodebook

/--
Payload-live micro-codebook for BP close/LCA.

The query first performs a counted read from `classifier` to recover the
per-block code, then performs a counted read from the corresponding finite
codebook table.  The charged payload is exactly the classifier payload followed
by the finite codebook payload; no dense per-block close/LCA table is charged.
-/
structure PayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat) where
  classifier :
    BlockCodeTable blockCount codeCount codeWidth codeOverhead
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  tablePayload : List Bool
  tablePayload_eq_tables :
    tablePayload =
      (List.range codeCount).flatMap fun code => (table code).payload
  tablePayload_length_eq : tablePayload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall {block code : Nat},
      classifier.codeAt block = some code ->
        BlockLocalBPCloseLCASpec shape
          (blockStartOf blockSize block) blockSize
          (entriesByCode code) slotIndex

namespace PayloadLiveBlockMicroCodebook

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) : List Bool :=
  micro.classifier.payload ++ micro.tablePayload

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (micro.classifier.codeCosted block) fun code? =>
    match code? with
    | none => Costed.pure none
    | some code =>
        if _hcode : code < codeCount then
          Costed.map (fun entry? => entry?.join)
            ((micro.table code).readCosted
              (micro.slotIndex
                (leftClose - blockStartOf blockSize block)
                (rightClose - blockStartOf blockSize block)))
        else
          Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
      codeOverhead + codeCount * tableOverhead := by
  simp [payload, micro.classifier.payload_length,
    micro.tablePayload_length_eq]

theorem lcaCloseCostedAtBlock_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCostedAtBlock
  have hclassifier :=
    micro.classifier.codeCosted_cost_le_one block
  cases hread : (micro.classifier.codeCosted block).value with
  | none =>
      simp [Costed.bind, hread]
      omega
  | some code =>
      by_cases hcode : code < codeCount
      · simp [Costed.bind, hread, hcode, Costed.map_cost]
        omega
      · simp [Costed.bind, hread, hcode, Costed.pure]
        omega

theorem lcaCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_two
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    {block code left len leftClose rightClose answerClose : Nat}
    (hcodeAt : micro.classifier.codeAt block = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  have hread :
      (micro.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      micro.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    micro.classifier.codeAt_lt hcodeAt
  have hlocal :
      (Costed.map (fun entry? => entry?.join)
        ((micro.table code).readCosted
          (micro.slotIndex
            (leftClose - blockStartOf blockSize block)
            (rightClose - blockStartOf blockSize block)))).erase =
        some answerClose := by
    exact
      blockLocalBPCloseLCA_read_exact
        (micro.table code) (micro.block_spec hcodeAt)
        hlen hbound hleft hright hanswer hleftLo hleftHi
        hrightLo hrightHi hanswerLo hanswerHi
  simpa [lcaCloseCostedAtBlock, Costed.erase, Costed.bind,
    hread, hcodeLt] using hlocal

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (hblockSize : 0 < blockSize)
    {code left len leftClose rightClose answerClose : Nat}
    (hcodeAt :
      micro.classifier.codeAt
          (blockOfClose blockSize leftClose) = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hcodeAt hlen hbound hleft hright
      hanswer blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
        codeOverhead + codeCount * tableOverhead /\
      (forall block : Nat,
        (micro.classifier.codeCosted block).cost <= 1 /\
          (micro.classifier.codeCosted block).erase =
            micro.classifier.codeAt block /\
          forall {code : Nat},
            micro.classifier.codeAt block = some code ->
              code < codeCount) /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 2) /\
      (forall {code left len leftClose rightClose answerClose : Nat},
        micro.classifier.codeAt
            (blockOfClose blockSize leftClose) = some code ->
          0 < len ->
            left + len <= shape.size ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  bpCloseOfInorder? shape
                      (scanWindow shape.representative left len) =
                    some answerClose ->
                    0 < blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        rightClose ->
                      rightClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        answerClose ->
                      answerClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                        (micro.lcaCloseCosted
                          leftClose rightClose).erase =
                          some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro block
    have hprofile := micro.classifier.profile
    exact hprofile.2.2 block
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_two leftClose rightClose
  intro code left len leftClose rightClose answerClose hcodeAt hlen hbound
    hleft hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hcodeAt hlen hbound
      hleft hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end PayloadLiveBlockMicroCodebook

/-- Empty fixed-width Nat classifier used by the dense fallback construction. -/
def emptyBlockCodeTable : BlockCodeTable 0 1 0 0 :=
  BlockCodeTable.ofEntries 0 1 0 0 ([] : List Nat)
    (by intro code hmem; cases hmem)
    rfl
    rfl
    (by intro block code hget; cases hget)

/-- Empty optional-Nat table used by the dense fallback construction. -/
def emptyOptionNatTable
    (fieldWidth : Nat) :
    FixedWidthOptionNatTable ([] : List (Option Nat)) fieldWidth :=
  FixedWidthOptionNatTable.ofEntries
    ([] : List (Option Nat)) fieldWidth
    (by intro entry value hmem _hentry; cases hmem)

/--
Payload-live micro phase that always misses.

It still performs the charged classifier read before returning `none`; the
point is to make the dense fallback macro leg below a concrete consumer of the
existing payload-live macro/micro directory surface.
-/
def emptyPayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat) :
    PayloadLiveBlockMicroCodebook shape blockSize 0 1 0 0 0 where
  classifier := emptyBlockCodeTable
  fieldWidth := fieldWidth
  entriesByCode := fun _ => []
  table := fun _ => emptyOptionNatTable fieldWidth
  slotIndex := densePairSlot blockSize
  tablePayload := []
  tablePayload_eq_tables := by
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  tablePayload_length_eq := by
    simp
  table_payload_length_eq := by
    intro code _hcode
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  block_spec := by
    intro block code hcodeAt
    have hnone : (emptyBlockCodeTable.codeAt block) = none := by
      simp [emptyBlockCodeTable, BlockCodeTable.codeAt,
        BlockCodeTable.ofEntries]
    rw [hnone] at hcodeAt
    cases hcodeAt

theorem emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth leftClose rightClose : Nat) :
    ((emptyPayloadLiveBlockMicroCodebook
      shape blockSize fieldWidth).lcaCloseCosted
        leftClose rightClose).erase = none := by
  have hcode :
      (emptyBlockCodeTable.codeCosted
        (blockOfClose blockSize leftClose)).value = none := by
    have h :=
      emptyBlockCodeTable.codeCosted_erase
        (blockOfClose blockSize leftClose)
    simpa [Costed.erase, emptyBlockCodeTable, BlockCodeTable.codeAt,
      BlockCodeTable.ofEntries] using h
  unfold PayloadLiveBlockMicroCodebook.lcaCloseCosted
    PayloadLiveBlockMicroCodebook.lcaCloseCostedAtBlock
  simp [emptyPayloadLiveBlockMicroCodebook, hcode, Costed.bind,
    Costed.pure]

/--
Macro/micro BP close/LCA query skeleton.

The micro codebook gets the first constant-time attempt.  If it misses, the
query falls back to an explicit macro component.  The exactness field matches
this control flow instead of pretending that a real macro/micro navigation
structure is still a single fixed-width table read.
-/
structure MacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount microTableOverhead macroOverhead macroCost : Nat)
    where
  micro :
    BlockMicroCodebook shape blockSize codeCount microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace MacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
      codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      1 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_one leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
        codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          1 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end MacroMicroBPCloseLCADirectory

/--
Payload-live macro/micro BP close/LCA directory.

This is the counted successor to `MacroMicroBPCloseLCADirectory`: the micro
phase reads a stored per-block code before reading the codebook table.  The
macro component remains an explicit interface, but its payload length, query
cost, and fallback exactness are all exposed here.
-/
structure PayloadLiveMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace PayloadLiveMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      2 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          2 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveMacroMicroBPCloseLCADirectory

/--
Guarded payload-live macro/micro BP close/LCA directory.

Unlike the compatibility `PayloadLiveMacroMicroBPCloseLCADirectory`, this query
does not ask the micro table about cross-block endpoints.  Same-block queries
use the charged micro-codebook path; cross-block queries use the charged
endpoint-fringe/range macro path.
-/
structure PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroComponent :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth leftOverhead interiorOverhead rightOverhead
  blockSize_pos : 0 < blockSize
  close_block_lt :
    forall {close : Nat},
      close < shape.bpCode.length ->
        blockOfClose blockSize close < blockCount

namespace PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) : List Bool :=
  directory.micro.payload ++ directory.macroComponent.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    directory.micro.lcaCloseCosted leftClose rightClose
  else
    directory.macroComponent.lcaCloseCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead +
        (leftOverhead + interiorOverhead + rightOverhead) := by
  simp [payload, directory.micro.payload_length,
    directory.macroComponent.payload_length]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    have hmicro :=
      directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
    omega
  · simp [hsame]
    exact directory.macroComponent.lcaCloseCosted_cost_le_six
      leftClose rightClose

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount :=
    directory.close_block_lt hleftCloseBound
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount :=
    directory.close_block_lt hrightCloseBound
  have hbetween :=
    answerClose_between_endpoint_closes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    rcases directory.micro.classifier.codeAt_exists_of_lt hleftBlock with
      ⟨code, hcodeAt⟩
    have hrightLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          rightClose := by
      simpa [hsame] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose))
    have hrightHi :
        rightClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      simpa [hsame] using
        (close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          directory.blockSize_pos)
    have hanswerLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          answerClose := by
      exact Nat.le_trans blockStartOf_blockOfClose_le hbetween.1
    have hanswerHi :
        answerClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact Nat.lt_of_le_of_lt hbetween.2 hrightHi
    exact
      directory.micro.lcaCloseCosted_exact_of_left_block
        directory.blockSize_pos hcodeAt hlen hbound hleft hright hanswer
        hrightLo hrightHi hanswerLo hanswerHi
  · simp [hsame]
    have hleftRight : leftClose <= rightClose := by
      omega
    have hblockLe :
        blockOfClose blockSize leftClose <=
          blockOfClose blockSize rightClose := by
      unfold blockOfClose
      exact Nat.div_le_div_right hleftRight
    have hcross :
        blockOfClose blockSize leftClose <
          blockOfClose blockSize rightClose := by
      omega
    exact
      directory.macroComponent.lcaCloseCosted_exact_of_query_cross_block
        hlen hbound hleft hright hanswer directory.blockSize_pos
        hleftBlock hrightBlock hcross

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (leftOverhead + interiorOverhead + rightOverhead) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  micro := micro
  macroComponent :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  blockSize_pos := hblockSize
  close_block_lt := hcover

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
              fieldWidth) +
            2 * ((interiorBlockPairRanges blockCount).length *
              fieldWidth) +
            2 * ((endpointRightFringeRanges blockSize blockCount).length *
              fieldWidth)) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  simpa [directory] using directory.profile

theorem guardedEndpointFringeMacroMicroOverhead_littleO
    (microOverhead : Nat -> Nat) (slots : Nat)
    (hmicro : LittleOLinear microOverhead) :
    LittleOLinear
      (fun n => microOverhead n + sampledDirectoryOverhead slots n) := by
  exact LittleOLinear.add hmicro (sampledDirectoryOverhead_littleO slots)

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth slots n : Nat)
    (microOverhead : Nat -> Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount)
    (hmicroLittle : LittleOLinear microOverhead)
    (hmicroBudget :
      codeOverhead + codeCount * microTableOverhead <= microOverhead n)
    (hmacroBudget :
      2 * ((endpointLeftFringeRanges blockSize blockCount).length *
          fieldWidth) +
        2 * ((interiorBlockPairRanges blockCount).length * fieldWidth) +
        2 * ((endpointRightFringeRanges blockSize blockCount).length *
          fieldWidth) <= sampledDirectoryOverhead slots n) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    LittleOLinear
        (fun n => microOverhead n + sampledDirectoryOverhead slots n) /\
      directory.payload.length <=
        microOverhead n + sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  have hprofile :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  constructor
  · exact guardedEndpointFringeMacroMicroOverhead_littleO
      microOverhead slots hmicroLittle
  constructor
  · rw [hprofile.1]
    omega
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2


end SuccinctCloseProposal
end RMQ

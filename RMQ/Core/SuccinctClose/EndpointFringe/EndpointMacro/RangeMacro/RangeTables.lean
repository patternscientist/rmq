import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate

/-!
# Endpoint-fringe range macro tables

Split from `RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
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

end SuccinctCloseProposal
end RMQ

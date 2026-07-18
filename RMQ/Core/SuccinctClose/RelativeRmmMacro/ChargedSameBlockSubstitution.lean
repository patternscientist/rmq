import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedSameBlockTrace

/-!
# Same-block exact-value substitution at the accepted call site (B6)

`bpChunkedSameBlockCloseSeededCosted_value_eq` takes three geometry
hypotheses (`hvalid`, `hstart`, `hcov`).  This module discharges them from
the accepted route's own query-side facts, exactly as
`ChargedFringeSubstitution.lean` does for the cross-block arm.

The same-block discharge is markedly shorter than the cross-block one
because the same-block leaf shares its window base and its range start with
the LEFT fringe leaf (`base = localBPWindowBase shape blockSize leftClose`,
`start = leftClose + 1`); only the range length differs.  So `hvalid` and
`hstart` are the left-fringe facts verbatim, and `hcov` follows from
same-block containment: `rightClose` lies in the same block as `leftClose`,
that block ends inside the four-word window, hence the same-block range is
covered.
-/

namespace RMQ

namespace SuccinctClose

namespace ConcreteCompactBPCloseLCADirectory

open SuccinctSpace

/--
Exact-value substitution at the accepted same-block call site: under the
accepted route's own query-side facts, the charged chunked same-block close
returns exactly the value of the accepted event-silent same-block close.
-/
theorem bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq_of_query
    {shape : Cartesian.CartesianShape}
    (rankCloseCosted : Nat -> Costed Nat)
    {left len leftClose rightClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hlen : 0 < len) (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright : bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    (bpChunkedSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
        rightClose).value =
      (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
        rightClose).value := by
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hsizePos : 0 < shape.size := by omega
  have hblockSizePos := canonicalBPRelativeSummaryBlockSizeRaw_pos shape
  have hblockSizeLeTwo :
      canonicalBPRelativeSummaryBlockSizeRaw shape <=
        2 * SuccinctRank.machineWordBits shape.bpCode.length :=
    canonicalBPRelativeSummaryBlockSizeRaw_le_two_machine_of_size_pos
      (shape := shape) hsizePos
  have hblockSizeLeThree :
      canonicalBPRelativeSummaryBlockSizeRaw shape <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  have hblockCountLen :
      canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length :=
    canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
      shape
  have hleftBlockLe :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose <=
        canonicalBPRelativeSummaryBlockCountRaw shape :=
    canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
      (shape := shape) hleftCloseBound
  -- Window base geometry (shared verbatim with the left fringe leaf).
  have hleftBaseBlock :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <=
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose) :=
    localBPWindowBase_le_blockStart shape
      (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
  have hleftBaseClose :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <=
        leftClose :=
    Nat.le_trans hleftBaseBlock blockStartOf_blockOfClose_le
  have hleftBaseLen :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <=
        shape.bpCode.length := by
    omega
  -- The block containing both closes ends inside the four-word window.
  have hleftEndWidth :
      blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape
      (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
      hblockSizeLeThree
  -- `rightClose` lies in the SAME block, hence inside the same window.
  have hrightInside :
      rightClose <
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              rightClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := rightClose) hblockSizePos
  have hleftInside :
      leftClose <
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := leftClose) hblockSizePos
  have hrightInsideLeft :
      rightClose <
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape := by
    rw [hsame]
    exact hrightInside
  have hrightBaseClose :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <=
        rightClose := by
    refine Nat.le_trans hleftBaseBlock ?_
    rw [hsame]
    exact blockStartOf_blockOfClose_le
  -- Cover each close separately: the whole block need not lie inside the
  -- BP code (the same-block case admits the final block), but each close
  -- position does, and that is all the range needs.
  have hcoverLeft :
      leftClose + 1 <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose +
          (localBPWindowBits shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape)
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := leftClose) (pos := leftClose + 1)
      (by omega) (by omega) (by omega)
  have hcoverRight :
      rightClose + 1 <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose +
          (localBPWindowBits shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape)
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := leftClose) (pos := rightClose + 1)
      (by omega) (by omega) (by omega)
  -- The seed is the accepted directory seed excess.
  have hleftSeedVal :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose).value =
        localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
        hrankExact hleftBaseLen
  have hvalid :
      BPFringeWindowValid
        (localBPWindowBits shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
        (localBPSeedFromRankCloseCosted shape rankCloseCosted
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose).value := by
    rw [hleftSeedVal]
    exact
      bpFringeWindowValid_localBPSeedExcess shape
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose hleftBaseLen
  exact
    bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq shape
      rankCloseCosted (canonicalBPRelativeSummaryBlockSizeRaw shape)
      leftClose rightClose hvalid (by omega) (by omega)

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ

import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAM
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks

/-!
# Charged chunked fringe substitution at the accepted cross-block call sites

This module pins the Option B wiring: the accepted cross-block close consumer
(`canonicalCrossBlockCloseCostedWithRankSeed`) with its two event-silent
fringe leaves replaced by the charged chunked fringe leaves returns exactly
the same value for every invocation produced by a valid RMQ query, and its
cost is bounded by the new all-size literal.  The wiring rung (replacing the
leaves inside the accepted whole-query route and re-deriving the trace-cost
chain) consumes these theorems as its immediate successor.
-/

namespace RMQ

namespace SuccinctClose

namespace ConcreteCompactBPCloseLCADirectory

open SuccinctSpace

/-- Charged chunked endpoint-fringe literal: 4 window words + 33 chunk reads. -/
def bpChunkedEndpointFringeChargedTraceCost : Nat := 37

/-- Principled close/LCA algebra with the chunked fringe literal. -/
def bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed
    (rankCost : Nat) : Nat :=
  2 * rankCost + 2 * bpChunkedEndpointFringeChargedTraceCost +
    canonicalRelativeRmmPrincipledInteriorChargedTraceCost

/--
The accepted canonical cross-block close consumer with the two event-silent
fringe leaves replaced by the charged chunked fringe leaves.  Everything
else — seed threading, interior directory, merge — is byte-identical to
`canonicalCrossBlockCloseCostedWithRankSeed`.
-/
def bpChunkedCrossBlockCloseCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  Costed.bind
    (localBPSeedFromRankCloseCosted
      shape rankCloseCosted blockSize leftClose)
    fun leftSeed =>
      Costed.bind
        (bpChunkedLeftFringeCandidateSeededCosted
          shape blockSize leftClose leftSeed)
        fun left? =>
          Costed.bind
            (if leftBlock + 1 < rightBlock then
              (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
                (leftBlock + 1) (rightBlock - leftBlock - 1)
            else
              Costed.pure none)
            fun middle? =>
              Costed.bind
                (localBPSeedFromRankCloseCosted
                  shape rankCloseCosted blockSize rightClose)
                fun rightSeed =>
                  Costed.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (bpChunkedRightFringeCandidateSeededCosted
                      shape blockSize rightClose rightSeed)

/--
Exact-value substitution at the accepted fringe call sites: for every
invocation reachable from a valid RMQ query (the same query-side facts under
which the accepted route proves its own exactness), replacing the accepted
fringe leaves by the charged chunked leaves preserves the cross-block close
value exactly.
-/
theorem bpChunkedCrossBlockCloseCostedWithRankSeed_value_eq
    {shape : Cartesian.CartesianShape}
    (rankCloseCosted : Nat -> Costed Nat)
    {left len leftClose rightClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    (bpChunkedCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose).value =
      (canonicalCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose).value := by
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hrightBlockLe :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose <=
        canonicalBPRelativeSummaryBlockCountRaw shape :=
    canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
      (shape := shape) hrightCloseBound
  have hsizePos : 0 < shape.size := by omega
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
  -- Left fringe geometry.
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
  have hleftInside :
      leftClose <
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := leftClose)
      (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
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
  have hleftSuccLeCount :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose + 1 <=
        canonicalBPRelativeSummaryBlockCountRaw shape := by
    omega
  have hleftEndLen :
      blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length := by
    have hmul :=
      Nat.mul_le_mul_right (canonicalBPRelativeSummaryBlockSizeRaw shape)
        hleftSuccLeCount
    have hmulLen :
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose + 1) *
            canonicalBPRelativeSummaryBlockSizeRaw shape <=
          shape.bpCode.length :=
      Nat.le_trans hmul hblockCountLen
    have hexpand :
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose + 1) *
            canonicalBPRelativeSummaryBlockSizeRaw shape =
          blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose *
              canonicalBPRelativeSummaryBlockSizeRaw shape +
            canonicalBPRelativeSummaryBlockSizeRaw shape :=
      Nat.succ_mul _ _
    have hstartEq :
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose) =
          blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose *
            canonicalBPRelativeSummaryBlockSizeRaw shape := by
      simp [blockStartOf]
    omega
  have hleftEndCovered :
      blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose +
          (localBPWindowBits shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape)
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := leftClose)
      (pos :=
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape)
      (by omega) hleftEndLen hleftEndWidth
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
  have hLval :
      (bpChunkedLeftFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose).value).value =
        (localBPLeftFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            leftClose).value).value := by
    rw [hleftSeedVal]
    exact
      bpChunkedLeftFringeCandidateSeededCosted_value_eq shape
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
        (localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
        (bpFringeWindowValid_localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
          hleftBaseLen)
        (by omega) (by omega) (by omega)
  -- Right fringe geometry.
  have hrightBaseBlock :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose <=
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose) :=
    localBPWindowBase_le_blockStart shape
      (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
  have hrightInside :
      blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose) <=
        rightClose :=
    blockStartOf_blockOfClose_le
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := rightClose)
  have hrightBaseLen :
      localBPWindowBase shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose <=
        shape.bpCode.length := by
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightInsideStrict :
      rightClose <
        blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              rightClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := rightClose)
      (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
  have hrightBlockEndWidth :
      blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose) +
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape
      (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
      hblockSizeLeThree
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  have hrightEndCovered :
      rightClose + 1 <=
        localBPWindowBase shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose +
          (localBPWindowBits shape
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape)
      (blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape)
      (close := rightClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  have hrightSeedVal :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose).value =
        localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted
        (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
        hrankExact hrightBaseLen
  have hRval :
      (bpChunkedRightFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose).value).value =
        (localBPRightFringeCandidateSeededCosted shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
          (localBPSeedFromRankCloseCosted shape rankCloseCosted
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            rightClose).value).value := by
    rw [hrightSeedVal]
    exact
      bpChunkedRightFringeCandidateSeededCosted_value_eq shape
        (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
        (localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
        (bpFringeWindowValid_localBPSeedExcess shape
          (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
          hrightBaseLen)
        (by omega) (by omega)
  unfold bpChunkedCrossBlockCloseCostedWithRankSeed
    canonicalCrossBlockCloseCostedWithRankSeed
  simp only [Costed.bind, Costed.map, Costed.pure]
  rw [hLval, hRval]

/--
Literal cost bound for the chunked cross-block consumer: two rank seeds,
two 37-read chunked fringes, one bounded interior replay.
-/
theorem bpChunkedCrossBlockCloseCostedWithRankSeed_cost_le_principled
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose rankCost : Nat)
    (_hleftCloseBound : leftClose < shape.bpCode.length)
    (hrightCloseBound : rightClose < shape.bpCode.length)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (bpChunkedCrossBlockCloseCostedWithRankSeed
      shape rankCloseCosted leftClose rightClose).cost <=
        bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost := by
  unfold bpChunkedCrossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  have hleftSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize leftClose rankCost hrankCost
  have hleft :=
    bpChunkedLeftFringeCandidateSeededCosted_cost_le shape blockSize
      leftClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize leftClose).value
  have hmiddle :
      (if leftBlock + 1 < rightBlock then
          (canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted
            (leftBlock + 1) (rightBlock - leftBlock - 1)
        else
          Costed.pure none).cost <=
        canonicalRelativeRmmPrincipledInteriorChargedTraceCost := by
    by_cases hgap : leftBlock + 1 < rightBlock
    case pos =>
      rw [if_pos hgap]
      have hrightBlockLe :
          rightBlock <= canonicalBPRelativeSummaryBlockCountRaw shape := by
        exact canonicalBPRelativeSummary_blockOfClose_le_blockCountRaw
          (shape := shape) hrightCloseBound
      have hbound :
          (leftBlock + 1) + (rightBlock - leftBlock - 1) <=
            (RelativeRmm.canonicalLayout shape).blockCount := by
        simpa [RelativeRmm.canonicalLayout] using (show
          (leftBlock + 1) + (rightBlock - leftBlock - 1) <=
            canonicalBPRelativeSummaryBlockCountRaw shape by omega)
      let base := canonicalBPRelativeSummaryBase shape
      have hbasePos : 0 < base := by
        simp [base, canonicalBPRelativeSummaryBase]
      have htwoBlocks :
          2 <= canonicalBPRelativeSummaryBlockCountRaw shape := by omega
      have htwoDiv : 2 <= shape.size / base := by
        simpa [canonicalBPRelativeSummaryBlockCountRaw, base] using htwoBlocks
      have hmul : 2 * base <= shape.size :=
        (Nat.le_div_iff_mul_le hbasePos).mp htwoDiv
      have hsizeTwo : 2 <= shape.size := by omega
      have hlog : 1 <= Nat.log2 shape.size :=
        natLog2_ge_of_pow_le (by simpa using hsizeTwo)
      have hbaseTwo : 2 <= base := by
        simp only [base, canonicalBPRelativeSummaryBase]
        omega
      have hsize : 4 <= shape.size := by omega
      simpa [canonicalRelativeRmmInteriorDirectory] using
        canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le_thirty_of_size_ge_four_of_bounded
          shape hsize (leftBlock + 1) (rightBlock - leftBlock - 1) hbound
    case neg =>
      rw [if_neg hgap]
      simp [Costed.pure]
  have hrightSeed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted
      blockSize rightClose rankCost hrankCost
  have hright :=
    bpChunkedRightFringeCandidateSeededCosted_cost_le shape blockSize
      rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted
        blockSize rightClose).value
  dsimp [blockSize, leftBlock, rightBlock] at hleftSeed hleft hmiddle hrightSeed hright
  simp [Costed.bind, Costed.map, Costed.pure]
  simp [Costed.pure] at hmiddle
  unfold bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed
  unfold bpChunkedEndpointFringeChargedTraceCost
  omega

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ

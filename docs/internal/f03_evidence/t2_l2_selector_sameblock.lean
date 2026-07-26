import RMQ.Core.SuccinctFinalStoreParam

/-!
# T2/L2 -- the LCA-close leaf: route selector and same-block arm are size-only

Deliverable for the EG-CP-F03 process gap recorded at
`docs/internal/E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md:216-222`
("controller leaf L2 was never classified ... the entire same-block arm is
absent from the campaign").

Everything below is quantified over ALL pairs of shapes of equal size, ALL
stores, ALL segment records and ALL endpoint pairs.  No size threshold, no
regime restriction, no representative rows.
-/

namespace T2L2

open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## 0. Size-only geometry -/

/-- Closed form of the route selector's block size: `2·(⌊log₂ n⌋ + 1)`.
Kernel-definitional (`RelativeSummary.lean:1236-1242`). -/
theorem blockSizeRaw_closed (shape : RMQ.Cartesian.CartesianShape) :
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
      = 2 * (Nat.log2 shape.size + 1) := rfl

/-- The route selector's block size is size-only. -/
theorem blockSizeRaw_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size) :
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a
      = RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b := by
  simp only [blockSizeRaw_closed, h]

/-- `bpCode.length = 2n` (`Shape.lean:51`), hence size-only. -/
theorem bpLen_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size) :
    a.bpCode.length = b.bpCode.length := by
  rw [RMQ.Cartesian.CartesianShape.bpCode_length,
    RMQ.Cartesian.CartesianShape.bpCode_length, h]

/-! ## 1. THE ROUTE SELECTOR

`ChargedFringeWiring.lean:496-497`:
`if blockOfClose blockSize leftClose = blockOfClose blockSize rightClose`.
This is F03's "branch and table selector". -/

/-- Closed form of the selector's block index: `⌊close / (2·(⌊log₂ n⌋+1))⌋`. -/
theorem L2_selector_closed
    (shape : RMQ.Cartesian.CartesianShape) (close : Nat) :
    RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape) close
      = close / (2 * (Nat.log2 shape.size + 1)) := rfl

/-- **The L2 route selector is size-only.**  The literal `if` condition of the
dispatcher is the SAME proposition for any two shapes of equal size, at every
pair of close positions. -/
theorem L2_selector_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (leftClose rightClose : Nat) :
    (RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) leftClose =
      RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) rightClose)
    <->
    (RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) leftClose =
      RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) rightClose) := by
  rw [blockSizeRaw_size_only h]

/-! ## 2. The same-block arm, bottom up -/

/-- `localBPWindowBase` (`LocalBPDecoder.lean:205-211`) consumes the shape only
through `bpCode.length`. -/
theorem windowBase_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (blockSize close : Nat) :
    RMQ.SuccinctClose.localBPWindowBase a blockSize close
      = RMQ.SuccinctClose.localBPWindowBase b blockSize close := by
  unfold RMQ.SuccinctClose.localBPWindowBase
  rw [hlen]

/-- The four charged window-word reads
(`ConcreteDirectoryRAMStoreParam.lean:4071-4087`): the addresses are
`firstWord + 0..3` with `firstWord` computed from `bpCode.length`, and the
replies come from the shared store. -/
theorem localBPBlockWords_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore) (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore a store blockSize close
      = localBPBlockWordsTraceResultWithStore b store blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore
  rw [hlen]

/-- `localBPWindowBitsTraceResultWithStore`
(`ConcreteDirectoryRAMStoreParam.lean:4152-4156`). -/
theorem localBPWindowBits_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore) (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore a store blockSize close
      = localBPWindowBitsTraceResultWithStore b store blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore
  rw [localBPBlockWords_congr hlen]

/-- **The seeded same-block arm** (`ChargedSameBlockTrace.lean:55-73`).
`base = localBPWindowBase`, `c = bpFringeChunkBits bpCode.length`, the fold
bounds `relLo`/`relHi` and the arity cap `Nat.min (relHi / c + 1) 33` all agree,
and `bpFringeChunkFoldTraceResultAtSegmentWithStore` takes its `window` from the
shared store rather than from the shape. -/
theorem sameBlockSeeded_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose rightClose seed
      = bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  rw [hlen, localBPWindowBits_congr hlen, windowBase_congr hlen]

/-- `localBPSeedFromRankCloseTraceResult` (`ConcreteDirectoryRAM.lean:1530-1537`):
the rank probe position is `localBPWindowBase`, size-only. -/
theorem localBPSeed_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (blockSize close : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
        a rankA blockSize close
      = RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
        b rankB blockSize close := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
  rw [windowBase_congr hlen]
  simp only [hrank]

/-- **The decoded same-block arm** -- the branch the L2 dispatcher actually
calls at `ChargedFringeWiring.lean:498-499`. -/
theorem sameBlockDecoded_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose : Nat) :
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        a rankA fringeSegment store blockSize leftClose rightClose
      = bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        b rankB fringeSegment store blockSize leftClose rightClose := by
  unfold bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
  rw [localBPSeed_congr hlen hrank]
  simp only [sameBlockSeeded_congr hlen]

/-! ## 3. The cross-block arm's fringe components

Not required by the task, but they cost nothing and they isolate the ONLY
residual in the cross-block arm (the interior cone, obligation T3). -/

theorem leftFringeSeeded_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose seed
      = bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [hlen, localBPWindowBits_congr hlen, windowBase_congr hlen]

theorem rightFringeSeeded_congr
    {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize rightClose seed
      = bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize rightClose seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [hlen, localBPWindowBits_congr hlen, windowBase_congr hlen]

/-- **The cross-block arm, modulo the interior cone.**  Every shape-dependent
quantity in `ChargedFringeTrace.lean:1144-1180` other than the interior
range-min call is discharged; `hinterior` is exactly obligation T3. -/
theorem crossBlock_congr_of_interior
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (hinterior :
      forall startBlock count,
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            a segments store startBlock count
          = concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            b segments store startBlock count)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        a rankA segments fringeSegment store leftClose rightClose
      = bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        b rankB segments fringeSegment store leftClose rightClose := by
  have hlen : a.bpCode.length = b.bpCode.length := bpLen_size_only h
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  simp only [blockSizeRaw_size_only h, localBPSeed_congr hlen hrank,
    leftFringeSeeded_congr hlen, rightFringeSeeded_congr hlen, hinterior]

/-- Down payment on T3: the interior cone's whole `Layout` record
(`RelativeSummary.lean:1276-1281`) is size-only, in closed form.  What remains
for T3 is `canonicalRelativeRmmInteriorComponentOffsets` and the interior table
entry-list LENGTHS -- `machineReadComputationAt` binds `_table` unused but does
branch on `i < entries.length` (`MachineChunkedTableProgram.lean:349`). -/
theorem canonicalLayout_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size) :
    RMQ.SuccinctClose.RelativeRmm.canonicalLayout a
      = RMQ.SuccinctClose.RelativeRmm.canonicalLayout b := by
  unfold RMQ.SuccinctClose.RelativeRmm.canonicalLayout
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw
    RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidthRaw
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBase
  rw [h]

/-! ## 4. Leaf L3 (the rank-close leaf) is size-only

Needed to discharge the `rankCloseTrace` argument at the concrete controller
leaf, which is handed
`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store _`
(`SuccinctFinalStoreParam.lean:1580-1581`). -/

theorem rankData_wordSize (shape : RMQ.Cartesian.CartesianShape) :
    (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData shape).wordSize
      = RMQ.SuccinctRank.machineWordBits shape.bpCode.length := rfl

theorem rankData_blocksPerSuper (shape : RMQ.Cartesian.CartesianShape) :
    (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData shape).blocksPerSuper
      = RMQ.SuccinctRank.machineWordBits shape.bpCode.length := rfl

/-- T1's obligation O3 (`f03_evidence/t1map_obligations.lean:61`), restated here
so this file is self-contained. -/
theorem chunkedRank_geometry_only
    {b1 b2 : List Bool} {s1 k1 q1 s2 k2 q2 : Nat}
    (d1 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b1 s1 k1 q1)
    (d2 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b2 s2 k2 q2)
    (hlen : b1.length = b2.length)
    (hword : d1.wordSize = d2.wordSize)
    (hblocks : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : RMQ.WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos =
      d2.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hword, hblocks]

/-- **Controller leaf L3 is size-only** (`SuccinctFinalStoreParam.lean:442-448`). -/
theorem L3_rankClose_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store rankSegmentBase pos
      = RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store rankSegmentBase pos := by
  have hlen : a.bpCode.length = b.bpCode.length := bpLen_size_only h
  unfold RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [hlen]
  exact
    chunkedRank_geometry_only
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData a)
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData b)
      hlen
      (by rw [rankData_wordSize, rankData_wordSize, hlen])
      (by rw [rankData_blocksPerSuper, rankData_blocksPerSuper, hlen])
      store _ _ _ _ _ false pos

/-! ## 5. Assembly at the L2 dispatcher -/

/-- **MAIN RESULT (same-block).**  For every pair of shapes of equal size, every
`rankCloseTrace` pair that agrees pointwise, every store, every interior segment
record, every fringe segment and every close pair that lands in ONE block, the
L2 dispatcher (`ChargedFringeWiring.lean:487-503`) produces the identical
`WordRAM.TraceResult` -- identical event list AND identical value. -/
theorem L2_dispatcher_sameBlock_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat)
    (hsame :
      RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) leftClose =
        RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) rightClose) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankA segments fringeSegment store sameBlockSegment leftClose rightClose
      = lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankB segments fringeSegment store sameBlockSegment leftClose rightClose := by
  have hbs :
      RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a
        = RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b :=
    blockSizeRaw_size_only h
  have hsameB :
      RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) leftClose =
        RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) rightClose := by
    rw [← hbs]; exact hsame
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [hbs, hsameB, if_pos]
  exact sameBlockDecoded_congr (bpLen_size_only h) hrank store _ _ _ _

/-- **MAIN RESULT (whole dispatcher, modulo T3).**  Both arms, no branch
hypothesis: the L2 dispatcher is size-only as soon as the interior cone is. -/
theorem L2_dispatcher_size_only_of_interior
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (hinterior :
      forall startBlock count,
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            a segments store startBlock count
          = concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            b segments store startBlock count)
    (sameBlockSegment leftClose rightClose : Nat) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankA segments fringeSegment store sameBlockSegment leftClose rightClose
      = lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankB segments fringeSegment store sameBlockSegment leftClose rightClose := by
  have hbs :
      RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a
        = RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b :=
    blockSizeRaw_size_only h
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [hbs]
  by_cases hsame :
      RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) leftClose =
        RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b) rightClose
  · simp only [hsame, if_pos]
    exact sameBlockDecoded_congr (bpLen_size_only h) hrank store _ _ _ _
  · simp only [hsame, if_false]
    exact
      crossBlock_congr_of_interior h hrank segments fringeSegment store hinterior
        leftClose rightClose

/-! ## 6. The concrete controller leaf

`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore`
(`SuccinctFinalStoreParam.lean:1575-1585`) is controller leaf L2 as the
5-instruction controller dispatches it.  `rankCloseTrace` is discharged by
`L3_rankClose_size_only`, so nothing is left quantified but the shapes, the
store and the endpoints. -/

/-- **CONTROLLER LEAF L2, same-block route: size-only.** -/
theorem L2_leaf_sameBlock_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (leftClose rightClose : Nat)
    (hsame :
      RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) leftClose =
        RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) rightClose) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store leftClose rightClose
      = RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store leftClose rightClose := by
  unfold RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    L2_dispatcher_sameBlock_size_only h
      (fun pos => L3_rankClose_size_only h store _ pos) _ _ store _ _ _ hsame

/-- **CONTROLLER LEAF L2, both routes, modulo T3.** -/
theorem L2_leaf_size_only_of_interior
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore)
    (hinterior :
      forall startBlock count,
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            a RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments store
            startBlock count
          = concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            b RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments store
            startBlock count)
    (leftClose rightClose : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store leftClose rightClose
      = RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store leftClose rightClose := by
  unfold RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    L2_dispatcher_size_only_of_interior h
      (fun pos => L3_rankClose_size_only h store _ pos) _ _ store hinterior _ _ _

end T2L2

/-! ## 7. Anti-vacuity and expected-type pins -/

namespace T2L2Check

/-- Two shapes of size 2 with provably DIFFERENT `bpCode`. -/
def shapeL : RMQ.Cartesian.CartesianShape :=
  RMQ.Cartesian.CartesianShape.node
    (RMQ.Cartesian.CartesianShape.node
      RMQ.Cartesian.CartesianShape.empty RMQ.Cartesian.CartesianShape.empty)
    RMQ.Cartesian.CartesianShape.empty

def shapeR : RMQ.Cartesian.CartesianShape :=
  RMQ.Cartesian.CartesianShape.node
    RMQ.Cartesian.CartesianShape.empty
    (RMQ.Cartesian.CartesianShape.node
      RMQ.Cartesian.CartesianShape.empty RMQ.Cartesian.CartesianShape.empty)

theorem sizes_agree : shapeL.size = shapeR.size := by decide

theorem codes_differ : shapeL.bpCode ≠ shapeR.bpCode := by decide

theorem shapes_differ : shapeL ≠ shapeR := by decide

/-- The same-block branch is reachable at EVERY shape: `blockSize ≥ 2`, so
closes 0 and 1 always share block 0.  The conditional main theorem therefore has
a satisfiable hypothesis. -/
theorem sameBlock_reachable (shape : RMQ.Cartesian.CartesianShape) :
    RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape) 0 =
      RMQ.SuccinctClose.blockOfClose
        (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape) 1 := by
  have h1 : (1 : Nat) < 2 * (Nat.log2 shape.size + 1) := by omega
  rw [T2L2.L2_selector_closed, T2L2.L2_selector_closed, Nat.zero_div,
    Nat.div_eq_of_lt h1]

/-- The conditional main theorem, instantiated at two genuinely different
shapes and a live same-block branch. -/
theorem instantiated (store : RMQ.WordRAM.ReadStore) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shapeL store 0 1
      = RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shapeR store 0 1 :=
  T2L2.L2_leaf_sameBlock_size_only sizes_agree store 0 1 (sameBlock_reachable shapeL)

/-- Expected-type pin: written independently of the theorem's declaration and
inhabited by the theorem VALUE alone.  It takes only `a.size = b.size`, never
`a = b`, so the statement really is the equal-size congruence. -/
def ExpectedSameBlockLeafType : Prop :=
  forall (a b : RMQ.Cartesian.CartesianShape),
    a.size = b.size ->
    forall (store : RMQ.WordRAM.ReadStore) (l r : Nat),
      RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) l =
        RMQ.SuccinctClose.blockOfClose
          (RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a) r ->
      RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          a store l r
        = RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          b store l r

theorem expected_inhabited : ExpectedSameBlockLeafType :=
  fun _ _ h store l r hsame =>
    T2L2.L2_leaf_sameBlock_size_only h store l r hsame

end T2L2Check

#check @T2L2.L2_selector_size_only
#check @T2L2.L2_dispatcher_sameBlock_size_only
#check @T2L2.L2_leaf_sameBlock_size_only
#check @T2L2.L2_leaf_size_only_of_interior

#print axioms T2L2.L2_selector_size_only
#print axioms T2L2.L2_dispatcher_sameBlock_size_only
#print axioms T2L2.L2_leaf_sameBlock_size_only
#print axioms T2L2.L2_dispatcher_size_only_of_interior
#print axioms T2L2.L2_leaf_size_only_of_interior
#print axioms T2L2.L3_rankClose_size_only
#print axioms T2L2.canonicalLayout_size_only
#print axioms T2L2Check.instantiated
#print axioms T2L2Check.expected_inhabited

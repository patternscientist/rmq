import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

/-!
T1 OBLIGATION MAP -- Layer 2: the concrete-instantiation side conditions.
-/

namespace T1Map2

/-! ### Layer-1 lemmas (re-stated here so this file is self-contained). -/

theorem entryRead_table_irrelevant
    {e1 e2 : List RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry}
    {w1 w2 : Nat}
    (t1 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e1 w1)
    (t2 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e2 w2)
    (layout : RMQ.GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : RMQ.WordRAM.ReadStore) (i : Nat) :
    t1.readTraceResultRelabeledWithStore layout store i =
      t2.readTraceResultRelabeledWithStore layout store i := rfl

theorem denseLeaf_bitWords_irrelevant'
    {b1 b2 : List Bool} {w1 w2 : Nat}
    (bw1 : RMQ.SuccinctSpace.BoundedPayloadWordStore b1 w1)
    (bw2 : RMQ.SuccinctSpace.BoundedPayloadWordStore b2 w2)
    (hw : w1 = w2)
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) (store : RMQ.WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw1 store
        basePosition baseOccurrence q =
      RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw2 store
        basePosition baseOccurrence q := by
  subst hw; rfl

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

theorem sparseDirRead_geometry_only
    {b1 b2 : List Bool} {tg : Bool} {s1 k1 s2 k2 : Nat}
    (d1 : RMQ.GenericSelect.SparseExceptionDirectory b1 tg s1 k1)
    (d2 : RMQ.GenericSelect.SparseExceptionDirectory b2 tg s2 k2)
    (hflag : d1.flagBits.length = d2.flagBits.length)
    (hword : d1.rankData.wordSize = d2.rankData.wordSize)
    (hblocks : d1.rankData.blocksPerSuper = d2.rankData.blocksPerSuper)
    (hstride : d1.localStride = d2.localStride)
    (layout : RMQ.GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : RMQ.WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat) :
    d1.bpChunkedReadTraceResultWithStore layout chunkSegment store c base
        localSlot localOccurrence =
      d2.bpChunkedReadTraceResultWithStore layout chunkSegment store c base
        localSlot localOccurrence := by
  unfold RMQ.GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore
  rw [chunkedRank_geometry_only d1.rankData d2.rankData hflag hword hblocks,
    hstride]

theorem L1_generic_congr
    {b1 b2 : List Bool} {tg : Bool} {s1 k1 s2 k2 : Nat}
    (D1 : RMQ.GenericSelect.SparseExceptionSelectData b1 tg s1 k1)
    (D2 : RMQ.GenericSelect.SparseExceptionSelectData b2 tg s2 k2)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg)
    (hwordSize : D1.wordSize = D2.wordSize)
    (hsuperStride : D1.superStride = D2.superStride)
    (hlocalStride : D1.localStride = D2.localStride)
    (hlocalSlots : D1.localSlotsPerSuper = D2.localSlotsPerSuper)
    (hlongFlagLen : D1.longFlagBits.length = D2.longFlagBits.length)
    (hlongRankWord : D1.longFlagRankData.wordSize = D2.longFlagRankData.wordSize)
    (hlongRankBlocks :
      D1.longFlagRankData.blocksPerSuper = D2.longFlagRankData.blocksPerSuper)
    (hsparseFlagLen :
      D1.sparseDirectory.flagBits.length = D2.sparseDirectory.flagBits.length)
    (hsparseRankWord :
      D1.sparseDirectory.rankData.wordSize =
        D2.sparseDirectory.rankData.wordSize)
    (hsparseRankBlocks :
      D1.sparseDirectory.rankData.blocksPerSuper =
        D2.sparseDirectory.rankData.blocksPerSuper)
    (hsparseStride :
      D1.sparseDirectory.localStride = D2.sparseDirectory.localStride)
    (layout : RMQ.GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : RMQ.WordRAM.ReadStore) (c idx : Nat) :
    D1.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx =
      D2.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx := by
  unfold RMQ.GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [RMQ.GenericSelect.SparseExceptionSelectData.queryOccurrence,
    entryRead_table_irrelevant D1.superTable D2.superTable,
    entryRead_table_irrelevant D1.localTable D2.localTable,
    chunkedRank_geometry_only D1.longFlagRankData D2.longFlagRankData
      hlongFlagLen hlongRankWord hlongRankBlocks,
    sparseDirRead_geometry_only D1.sparseDirectory D2.sparseDirectory
      hsparseFlagLen hsparseRankWord hsparseRankBlocks hsparseStride,
    denseLeaf_bitWords_irrelevant' D1.bitWords D2.bitWords hwordSize]
  simp only [hcount, hwordSize, hsuperStride, hlocalStride, hlocalSlots]

/-! ### Layer 2: the flag-vector length obligations. -/

theorem longFlagLen_congr
    {b1 b2 : List Bool} {tg : Bool}
    (hlen : b1.length = b2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg) :
    (RMQ.GenericSelect.longSuperFlagBits b1 tg).length =
      (RMQ.GenericSelect.longSuperFlagBits b2 tg).length := by
  rw [RMQ.GenericSelect.longSuperFlagBits_length,
    RMQ.GenericSelect.longSuperFlagBits_length,
    RMQ.GenericSelect.superSlotCount, RMQ.GenericSelect.superSlotCount,
    hlen, hcount]

theorem sparseFlagLen_congr
    {b1 b2 : List Bool} {tg : Bool}
    (hlen : b1.length = b2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg) :
    (RMQ.GenericSelect.sparseExceptionEffectiveFlagBits b1 tg).length =
      (RMQ.GenericSelect.sparseExceptionEffectiveFlagBits b2 tg).length := by
  rw [RMQ.GenericSelect.sparseExceptionEffectiveFlagBits_length,
    RMQ.GenericSelect.sparseExceptionEffectiveFlagBits_length,
    RMQ.GenericSelect.sparseExceptionEffectiveLocalSlotCount,
    RMQ.GenericSelect.sparseExceptionEffectiveLocalSlotCount,
    RMQ.GenericSelect.localSlotCount, RMQ.GenericSelect.localSlotCount,
    RMQ.GenericSelect.superSlotCount, RMQ.GenericSelect.superSlotCount,
    hlen, hcount]

/-! ### T1 proper, at the concrete `sparseExceptionSelectData`. -/

theorem T1_L1_size_only
    (bits1 bits2 : List Bool) (target : Bool)
    (store : RMQ.WordRAM.ReadStore)
    (layout : RMQ.GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSeg selSeg c idx : Nat)
    (hlen : bits1.length = bits2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount bits1 target =
        RMQ.GenericSelect.occurrenceCount bits2 target) :
    (RMQ.GenericSelect.sparseExceptionSelectData bits1
          target).bpChunkedSelectTraceResultWithStore
        layout chunkSeg selSeg store c idx =
      (RMQ.GenericSelect.sparseExceptionSelectData bits2
          target).bpChunkedSelectTraceResultWithStore
        layout chunkSeg selSeg store c idx := by
  have hflagLong := longFlagLen_congr (b1 := bits1) (b2 := bits2) (tg := target)
    hlen hcount
  have hflagSparse := sparseFlagLen_congr (b1 := bits1) (b2 := bits2)
    (tg := target) hlen hcount
  refine L1_generic_congr _ _ hcount ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    layout chunkSeg selSeg store c idx
  · show RMQ.GenericSelect.wordBits bits1.length
      = RMQ.GenericSelect.wordBits bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.superStride bits1.length
      = RMQ.GenericSelect.superStride bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.localStride bits1.length
      = RMQ.GenericSelect.localStride bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.localSlotsPerSuper bits1.length
      = RMQ.GenericSelect.localSlotsPerSuper bits2.length
    rw [hlen]
  · exact hflagLong
  · show RMQ.GenericSelect.longFlagRankWordSize bits1 target
      = RMQ.GenericSelect.longFlagRankWordSize bits2 target
    unfold RMQ.GenericSelect.longFlagRankWordSize
    rw [hflagLong]
  · rfl
  · exact hflagSparse
  · show RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize bits1 target
      = RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize bits2 target
    unfold RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize
    rw [hflagSparse]
  · rfl
  · show RMQ.GenericSelect.localStride bits1.length
      = RMQ.GenericSelect.localStride bits2.length
    rw [hlen]

/-! ### Route corollary: leaf L1 at equal-size Cartesian shapes. -/

theorem L1_route_shape_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (idx : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        a store idx =
      RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        b store idx := by
  unfold
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  have hlen : a.bpCode.length = b.bpCode.length := by
    rw [RMQ.Cartesian.CartesianShape.bpCode_length,
      RMQ.Cartesian.CartesianShape.bpCode_length, h]
  have hcount :
      RMQ.GenericSelect.occurrenceCount a.bpCode false =
        RMQ.GenericSelect.occurrenceCount b.bpCode false := by
    unfold RMQ.GenericSelect.occurrenceCount
    rw [RMQ.SuccinctSpace.bpCode_rankFalse_full,
      RMQ.SuccinctSpace.bpCode_rankFalse_full, h]
  rw [T1_L1_size_only a.bpCode b.bpCode false store _ _ _ _ _ hlen hcount,
    hlen]

end T1Map2

#print axioms T1Map2.L1_route_shape_size_only
#print axioms T1Map2.longFlagLen_congr

/-! ## C06 independent verification -- appended to the lane's own proof.

These checks do not re-prove T1. They test that T1 SAYS something: that its
hypotheses are satisfiable by genuinely different inputs, that the route
corollary applies to genuinely different shapes, and that the statement is the
intended one rather than a sibling that unification collapsed. -/

section C06Verify

open RMQ

/-- Two DISTINCT bitvectors of equal length and equal occurrence count, so the
    hypotheses of `T1_L1_size_only` are satisfiable off the diagonal. -/
def bvA : List Bool := [true, false, true, false]
def bvB : List Bool := [false, true, false, true]

example : bvA ≠ bvB := by decide
example : bvA.length = bvB.length := by decide
example :
    RMQ.GenericSelect.occurrenceCount bvA true =
      RMQ.GenericSelect.occurrenceCount bvB true := by
  decide

/-- Two shapes of equal size whose balanced-parenthesis codes genuinely differ,
    so `L1_route_shape_size_only` is not vacuous on the route. -/
def shapeL : Cartesian.CartesianShape :=
  .node (.node .empty .empty) .empty
def shapeR : Cartesian.CartesianShape :=
  .node .empty (.node .empty .empty)

example : shapeL.size = shapeR.size := by decide
example : shapeL.bpCode ≠ shapeR.bpCode := by decide

/-- The route corollary instantiated at those two shapes: a real, non-vacuous
    consequence about the actual route function. -/
example (store : WordRAM.ReadStore) (idx : Nat) :
    SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shapeL store idx =
      SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shapeR store idx :=
  T1Map2.L1_route_shape_size_only (by decide) store idx

/-- Expected-type pin. This proposition is written independently of the
    theorem's declaration and is inhabited by the theorem VALUE alone -- no
    reconstruction from neighbouring lemmas. A sibling statement cannot
    inhabit it. -/
def C06ExpectedT1RouteType : Prop :=
  ∀ (a b : Cartesian.CartesianShape),
    a.size = b.size →
      ∀ (store : WordRAM.ReadStore) (idx : Nat),
        SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            a store idx =
          SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            b store idx

example : C06ExpectedT1RouteType :=
  fun _ _ h store idx => T1Map2.L1_route_shape_size_only h store idx

/-- Anti-bypass: equal SIZE is the hypothesis, not equal shape. If the theorem
    had secretly required `a = b`, this weaker-hypothesis consumer would fail. -/
example (a b : Cartesian.CartesianShape) (h : a.size = b.size)
    (store : WordRAM.ReadStore) (idx : Nat) :
    SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        a store idx =
      SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        b store idx :=
  T1Map2.L1_route_shape_size_only h store idx

#print axioms T1Map2.T1_L1_size_only
#print axioms T1Map2.L1_route_shape_size_only

end C06Verify

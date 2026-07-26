import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

/-!
T1 OBLIGATION MAP -- mechanical verification of the load-bearing claims.
Fully qualified names everywhere; no `open` of RMQ namespaces.
-/

namespace T1Map

/-! ## O1. Entry-table reader is table-argument irrelevant (content AND length). -/

theorem entryRead_table_irrelevant
    {e1 e2 : List RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry}
    {w1 w2 : Nat}
    (t1 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e1 w1)
    (t2 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e2 w2)
    (layout : RMQ.GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : RMQ.WordRAM.ReadStore) (i : Nat) :
    t1.readTraceResultRelabeledWithStore layout store i =
      t2.readTraceResultRelabeledWithStore layout store i := rfl

/-! ## O2. The dense two-word select leaf ignores its `bitWords` argument
     (only the implicit `wordSize` matters). -/

theorem denseLeaf_bitWords_irrelevant
    {b1 b2 : List Bool} {wordSize : Nat}
    (bw1 : RMQ.SuccinctSpace.BoundedPayloadWordStore b1 wordSize)
    (bw2 : RMQ.SuccinctSpace.BoundedPayloadWordStore b2 wordSize)
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) (store : RMQ.WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw1 store
        basePosition baseOccurrence q =
      RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw2 store
        basePosition baseOccurrence q := rfl

/-- Variant of O2 with the two word sizes supplied separately. -/
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

/-! ## O3. The chunked rank seed depends on its data only through
     `bits.length`, `wordSize`, `blocksPerSuper`. -/

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

/-! ## O4. The sparse-exception directory chunked read is geometry-only. -/

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

/-! ## O5. THE GENERIC L1 CONGRUENCE.  Everything above assembled. -/

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
    (hsparseStride : D1.sparseDirectory.localStride = D2.sparseDirectory.localStride)
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

end T1Map

#print axioms T1Map.entryRead_table_irrelevant
#print axioms T1Map.denseLeaf_bitWords_irrelevant
#print axioms T1Map.chunkedRank_geometry_only
#print axioms T1Map.sparseDirRead_geometry_only
#print axioms T1Map.L1_generic_congr

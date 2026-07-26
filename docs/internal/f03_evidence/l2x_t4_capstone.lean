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



open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

set_option autoImplicit false

namespace L2X

theorem bpLen_congr {a b : CartesianShape} (h : a.size = b.size) :
    a.bpCode.length = b.bpCode.length := by
  rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, h]

theorem layout_congr {a b : CartesianShape} (h : a.size = b.size) :
    RelativeRmm.canonicalLayout a = RelativeRmm.canonicalLayout b := by
  unfold RelativeRmm.canonicalLayout
  unfold canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummaryRelativeWidthRaw
    canonicalBPRelativeSummaryBase
  rw [h]

theorem blockSizeRaw_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBlockSizeRaw a =
      canonicalBPRelativeSummaryBlockSizeRaw b := by
  unfold canonicalBPRelativeSummaryBlockSizeRaw canonicalBPRelativeSummaryBase
  rw [h]

theorem windowBase_congr {a b : CartesianShape} (h : a.size = b.size)
    (blockSize close : Nat) :
    localBPWindowBase a blockSize close = localBPWindowBase b blockSize close := by
  unfold localBPWindowBase
  rw [bpLen_congr h]

theorem localBPBlockWords_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore a store blockSize close =
      localBPBlockWordsTraceResultWithStore b store blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore
  rw [bpLen_congr h]

theorem localBPWindowBits_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore a store blockSize close =
      localBPWindowBitsTraceResultWithStore b store blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore
  rw [localBPBlockWords_congr h]

theorem seed_congr {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat) (blockSize close : Nat) :
    localBPSeedFromRankCloseTraceResult a rankCloseTrace blockSize close =
      localBPSeedFromRankCloseTraceResult b rankCloseTrace blockSize close := by
  unfold localBPSeedFromRankCloseTraceResult
  rw [windowBase_congr h]

theorem leftFringe_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (fringeSegment blockSize leftClose seed : Nat) :
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose seed =
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]

theorem rightFringe_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (fringeSegment blockSize rightClose seed : Nat) :
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize rightClose seed =
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize rightClose seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]



/-! ### Generalised qz_mech core: word count of a fixed-width table's machine store. -/

theorem chunkFuel_length_congr (wordSize : Nat) :
    forall (fuel : Nat) (p q : List Bool), p.length = q.length ->
      (chunkPayloadWordsFuel wordSize fuel p).length =
        (chunkPayloadWordsFuel wordSize fuel q).length := by
  intro fuel
  induction fuel with
  | zero => intro p q _; simp [chunkPayloadWordsFuel]
  | succ fuel ih =>
      intro p q hpq
      cases p with
      | nil =>
          cases q with
          | nil => simp [chunkPayloadWordsFuel]
          | cons b r => simp at hpq
      | cons b r =>
          cases q with
          | nil => simp at hpq
          | cons c s =>
              have hdrop :
                  ((b :: r).drop wordSize).length =
                    ((c :: s).drop wordSize).length := by
                simp [List.length_drop, hpq]
              simp only [chunkPayloadWordsFuel, List.length_cons]
              rw [ih _ _ hdrop]

theorem chunkPayloadWords_length_congr
    (wordSize : Nat) (p q : List Bool) (h : p.length = q.length) :
    (chunkPayloadWords wordSize p).length =
      (chunkPayloadWords wordSize q).length := by
  unfold chunkPayloadWords
  rw [h]
  exact chunkFuel_length_congr wordSize (q.length + 1) p q h

theorem flatMap_chunk_length_of_uniform
    (wordSize width : Nat) :
    forall ws : List (List Bool),
      (forall w, List.Mem w ws -> w.length = width) ->
        (ws.flatMap (chunkPayloadWords wordSize)).length =
          ws.length *
            (chunkPayloadWords wordSize (List.replicate width false)).length := by
  intro ws
  induction ws with
  | nil => intro _; simp
  | cons head tail ih =>
      intro huniform
      have hhead : head.length = width := huniform head (List.Mem.head _)
      have htail : forall w, List.Mem w tail -> w.length = width := by
        intro w hw; exact huniform w (List.Mem.tail _ hw)
      have hrep : (List.replicate width false).length = width := by simp
      have hheadlen :
          (chunkPayloadWords wordSize head).length =
            (chunkPayloadWords wordSize (List.replicate width false)).length :=
        chunkPayloadWords_length_congr wordSize head _ (by rw [hhead, hrep])
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih htail, hheadlen, Nat.succ_mul]
      omega

theorem store_words_size_eq_entries_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.store.words.size = entries.length := by
  have key :
      forall i : Nat,
        ((table.store.words.toList)[i]?).isSome = (entries[i]?).isSome := by
    intro i
    have h : ((table.store.words.toList)[i]?).map bitsToNatLE = entries[i]? := by
      simpa using table.read_exact i
    rw [← h]
    cases (table.store.words.toList)[i]? <;> simp
  have hlen : table.store.words.toList.length = table.store.words.size :=
    Array.length_toList
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : ((table.store.words.toList)[entries.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : (entries[table.store.words.toList.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [← key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2

theorem store_word_mem_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {bits : List Bool} (hmem : List.Mem bits table.store.words.toList) :
    bits.length = width := by
  rcases List.getElem?_of_mem hmem with ⟨i, hi⟩
  exact table.word_length_of_get? (by simpa using hi)

/-- **Closed form**: a fixed-width table's machine-store word count is
`entries.length` times a function of `wordSize` and `width` only. -/
theorem machineStore_words_size_closed
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (h : 0 < wordSize) :
    (table.machineStore (wordSize := wordSize) h).store.words.size =
      entries.length *
        (chunkPayloadWords wordSize (List.replicate width false)).length := by
  show (fixedWidthNatTableMachineWords table wordSize).toArray.size = _
  rw [Array.size_toArray]
  unfold fixedWidthNatTableMachineWords
  rw [flatMap_chunk_length_of_uniform wordSize width table.store.words.toList
    (fun w hw => store_word_mem_length table hw)]
  rw [Array.length_toList, store_words_size_eq_entries_length table]

/-- **Generalised read-computation congruence**: differing widths allowed. -/
theorem machineReadComputationAt_geometry_only
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1)
    (t2 : FixedWidthNatTable e2 w2)
    (hlen : e1.length = e2.length) (hw : w1 = w2)
    (wordSize base deadAddress i : Nat) :
    t1.machineReadComputationAt wordSize base deadAddress i =
      t2.machineReadComputationAt wordSize base deadAddress i := by
  unfold FixedWidthNatTable.machineReadComputationAt
  rw [hlen, hw]


/-! ### Interior directory: the eight table geometries -/

theorem localMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmLocalMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl

theorem globalMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmGlobalMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl

theorem localLevelMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmLocalLevelMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl


/-! ### Per-table machine word-count congruences. -/

theorem baselineWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSuperblockBaselineEntries_length, bpSuperblockBaselineEntries_length]
  simp only [RelativeRmm.Layout.superWidth]
  rw [layout_congr h, bpLen_congr h]

theorem minRelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockRelativeMinExcessEntries_length, bpBlockRelativeMinExcessEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem maxRelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockRelativeMaxExcessEntries_length, bpBlockRelativeMaxExcessEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem argOffsetWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockArgMinLocalOffsetEntries_length, bpBlockArgMinLocalOffsetEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem localTableWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpLocalSparseOffsetEntries_length, bpLocalSparseOffsetEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem globalTableWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpGlobalSparseBlockEntries_length, bpGlobalSparseBlockEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem localLevelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSparseLevelEntries_length, bpSparseLevelEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem globalLevelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSparseLevelEntries_length, bpSparseLevelEntries_length]
  rw [layout_congr h, bpLen_congr h]

theorem componentStoreWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    (canonicalRelativeRmmInteriorComponentStore a).store.words.size =
      (canonicalRelativeRmmInteriorComponentStore b).store.words.size := by
  rw [canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq]
  simp only []
  rw [baselineWords_congr h, minRelWords_congr h, maxRelWords_congr h,
    argOffsetWords_congr h, localTableWords_congr h, globalTableWords_congr h,
    localLevelWords_congr h, globalLevelWords_congr h]

theorem offsets_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalRelativeRmmInteriorComponentOffsets a =
      canonicalRelativeRmmInteriorComponentOffsets b := by
  unfold canonicalRelativeRmmInteriorComponentOffsets
  simp only [localMachineStore_words_size, globalMachineStore_words_size,
    localLevelMachineStore_words_size]
  rw [baselineWords_congr h, minRelWords_congr h, maxRelWords_congr h,
    argOffsetWords_congr h, localTableWords_congr h, globalTableWords_congr h,
    localLevelWords_congr h, componentStoreWords_congr h]


/-! ### The interior read primitive is geometry-only. -/

theorem readNat_congr {a b : CartesianShape} (h : a.size = b.size)
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (hlen : e1.length = e2.length) (hw : w1 = w2) (base i : Nat) :
    canonicalRelativeRmmMachineReadNatComputation a t1 base i =
      canonicalRelativeRmmMachineReadNatComputation b t2 base i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  rw [bpLen_congr h, offsets_congr h]
  exact machineReadComputationAt_geometry_only t1 t2 hlen hw _ _ _ _


/-! ### Site-specific read congruences (index-parameterised). -/

theorem readNat_baseline_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).baselineTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).baselineTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSuperblockBaselineEntries_length, bpSuperblockBaselineEntries_length,
      layout_congr h]
  · simp only [RelativeRmm.Layout.superWidth]; rw [bpLen_congr h]

theorem readNat_minRel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).minRelTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).minRelTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockRelativeMinExcessEntries_length,
      bpBlockRelativeMinExcessEntries_length, layout_congr h]
  · rw [layout_congr h]

theorem readNat_maxRel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).maxRelTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).maxRelTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockRelativeMaxExcessEntries_length,
      bpBlockRelativeMaxExcessEntries_length, layout_congr h]
  · rw [layout_congr h]

theorem readNat_argOffset_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).argOffsetTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).argOffsetTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockArgMinLocalOffsetEntries_length,
      bpBlockArgMinLocalOffsetEntries_length, layout_congr h]
  · rw [layout_congr h]

theorem readNat_localTable_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorLocalTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorLocalTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpLocalSparseOffsetEntries_length, bpLocalSparseOffsetEntries_length,
      layout_congr h]
  · rw [layout_congr h]

theorem readNat_globalTable_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorGlobalTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorGlobalTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpGlobalSparseBlockEntries_length, bpGlobalSparseBlockEntries_length,
      layout_congr h]
  · rw [layout_congr h]

theorem readNat_localLevel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorLocalLevelTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorLocalLevelTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]
  · rw [layout_congr h]

theorem readNat_globalLevel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorGlobalLevelTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorGlobalLevelTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]
  · rw [layout_congr h]

/-! ### The interior candidate machinery. -/

theorem summaryComputation_congr {a b : CartesianShape} (h : a.size = b.size)
    (block : Nat) :
    canonicalRelativeRmmMachineSummaryComputation a block =
      canonicalRelativeRmmMachineSummaryComputation b block := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb1 : (canonicalRelativeRmmInteriorComponentOffsets a).baseline =
      (canonicalRelativeRmmInteriorComponentOffsets b).baseline := by rw [hO]
  have hb2 : (canonicalRelativeRmmInteriorComponentOffsets a).minRel =
      (canonicalRelativeRmmInteriorComponentOffsets b).minRel := by rw [hO]
  have hb3 : (canonicalRelativeRmmInteriorComponentOffsets a).maxRel =
      (canonicalRelativeRmmInteriorComponentOffsets b).maxRel := by rw [hO]
  have hb4 : (canonicalRelativeRmmInteriorComponentOffsets a).argOffset =
      (canonicalRelativeRmmInteriorComponentOffsets b).argOffset := by rw [hO]
  have hi1 : block / (RelativeRmm.canonicalLayout a).blocksPerSuper =
      block / (RelativeRmm.canonicalLayout b).blocksPerSuper := by rw [hL]
  unfold canonicalRelativeRmmMachineSummaryComputation
  simp only []
  rw [readNat_baseline_congr h hb1 hi1, readNat_minRel_congr h hb2 rfl,
    readNat_maxRel_congr h hb3 rfl, readNat_argOffset_congr h hb4 rfl]

theorem minCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineMinCandidateComputation a block =
      canonicalRelativeRmmMachineMinCandidateComputation b block := by
  unfold canonicalRelativeRmmMachineMinCandidateComputation
  simp only []
  rw [summaryComputation_congr h, layout_congr h]

theorem localSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroIdx localStart level : Nat) :
    canonicalRelativeRmmMachineLocalSpanCandidateComputation a
        macroIdx localStart level =
      canonicalRelativeRmmMachineLocalSpanCandidateComputation b
        macroIdx localStart level := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).localOffset =
      (canonicalRelativeRmmInteriorComponentOffsets b).localOffset := by rw [hO]
  have hi :
      bpLocalSparseCellSlot (RelativeRmm.canonicalLayout a).macroSize
          (RelativeRmm.canonicalLayout a).levelCount macroIdx localStart level =
        bpLocalSparseCellSlot (RelativeRmm.canonicalLayout b).macroSize
          (RelativeRmm.canonicalLayout b).levelCount macroIdx localStart
          level := by rw [hL]
  unfold canonicalRelativeRmmMachineLocalSpanCandidateComputation
  simp only []
  rw [readNat_localTable_congr h hb hi, hL]
  apply congrArg
  funext offset
  cases offset with
  | none => rfl
  | some value => exact minCandidateComputation_congr h _

theorem globalSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart level : Nat) :
    canonicalRelativeRmmMachineGlobalSpanCandidateComputation a
        macroStart level =
      canonicalRelativeRmmMachineGlobalSpanCandidateComputation b
        macroStart level := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).globalBlock =
      (canonicalRelativeRmmInteriorComponentOffsets b).globalBlock := by rw [hO]
  have hi :
      bpGlobalSparseCellSlot (RelativeRmm.canonicalLayout a).macroSampleCount
          macroStart level =
        bpGlobalSparseCellSlot (RelativeRmm.canonicalLayout b).macroSampleCount
          macroStart level := by rw [hL]
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  simp only []
  rw [readNat_globalTable_congr h hb hi]
  apply congrArg
  funext block
  cases block with
  | none => rfl
  | some value => exact minCandidateComputation_congr h _

theorem localTwoSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroIdx localStart count : Nat) :
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation a
        macroIdx localStart count =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation b
        macroIdx localStart count := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).localLevel =
      (canonicalRelativeRmmInteriorComponentOffsets b).localLevel := by rw [hO]
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  simp only []
  rw [readNat_localLevel_congr h hb rfl, hL]
  apply congrArg
  funext cell
  cases cell with
  | none => rfl
  | some value =>
      simp only []
      rw [localSpanCandidateComputation_congr h,
        localSpanCandidateComputation_congr h]

theorem globalTwoSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart macroSpanCount : Nat) :
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation a
        macroStart macroSpanCount =
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation b
        macroStart macroSpanCount := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).globalLevel =
      (canonicalRelativeRmmInteriorComponentOffsets b).globalLevel := by rw [hO]
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  simp only []
  rw [readNat_globalLevel_congr h hb rfl, hL]
  apply congrArg
  funext cell
  cases cell with
  | none => rfl
  | some value =>
      simp only []
      rw [globalSpanCandidateComputation_congr h,
        globalSpanCandidateComputation_congr h]

theorem adjacentMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart localStart rightCount : Nat) :
    canonicalRelativeRmmMachineAdjacentMacroCandidateComputation a
        macroStart localStart rightCount =
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation b
        macroStart localStart rightCount := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    localTwoSpanCandidateComputation_congr h]

theorem leftMiddleMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart localStart middleMacroCount : Nat) :
    canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation a
        macroStart localStart middleMacroCount =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation b
        macroStart localStart middleMacroCount := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    globalTwoSpanCandidateComputation_congr h]

theorem crossMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    canonicalRelativeRmmMachineCrossMacroCandidateComputation a
        macroStart localStart middleMacroCount rightCount =
      canonicalRelativeRmmMachineCrossMacroCandidateComputation b
        macroStart localStart middleMacroCount rightCount := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    globalTwoSpanCandidateComputation_congr h,
    localTwoSpanCandidateComputation_congr h]

/-- The whole interior range-min computation is size-only. -/
theorem interiorRangeMinComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeMinComputation a startBlock count =
      canonicalRelativeRmmInteriorRangeMinComputation b startBlock count := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    adjacentMacroCandidateComputation_congr h,
    leftMiddleMacroCandidateComputation_congr h,
    crossMacroCandidateComputation_congr h]

theorem interiorRangeMinWithStore_congr {a b : CartesianShape}
    (h : a.size = b.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore) (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a segments store startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b segments store startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  rw [interiorRangeMinComputation_congr h]


/-! ### The L2 cross-block arm. -/

/--
**L2 cross-block arm is size-only.**

For any two Cartesian shapes of equal `size`, the supplied-store cross-block
LCA-close consumer — the `else` branch of the L2 dispatcher
(`ChargedFringeWiring.lean:501-503`) — produces the *identical*
`WordRAM.TraceResult`: same ordered trace of read events and same value.

Universally quantified over both shapes, the rank-close sub-trace, the
interior trace segments, the fringe segment, the read store and both close
positions.  No size threshold, no regime restriction.
-/
theorem L2_crossBlock_size_only {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        a rankCloseTrace segments fringeSegment store leftClose rightClose =
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        b rankCloseTrace segments fringeSegment store leftClose rightClose := by
  unfold
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  simp only [blockSizeRaw_congr h, seed_congr h, leftFringe_congr h,
    interiorRangeMinWithStore_congr h, rightFringe_congr h]


/-! ### The L2 same-block arm and the L2 dispatcher. -/

theorem sameBlockSeeded_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose rightClose seed =
      bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]

theorem sameBlockDecoded_congr {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        a rankCloseTrace fringeSegment store blockSize leftClose rightClose =
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        b rankCloseTrace fringeSegment store blockSize leftClose rightClose := by
  unfold bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
  simp only [seed_congr h, sameBlockSeeded_congr h]

/--
**Controller leaf L2 is size-only.**

The whole supplied-store LCA-close dispatcher
(`ChargedFringeWiring.lean:487-503`) — its route selector, its same-block arm
and its cross-block arm — returns the identical `WordRAM.TraceResult` for any
two shapes of equal `size`.
-/
theorem L2_lcaClose_size_only {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [blockSizeRaw_congr h]
  by_cases hs :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw b) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw b) rightClose
  · simp only [hs, if_pos]
    exact sameBlockDecoded_congr h _ _ _ _ _ _
  · simp only [hs, if_false, if_neg]
    exact L2_crossBlock_size_only h _ _ _ _ _ _


/-! ### Bonus: the rank-close leaf L3, and the L2 leaf at the controller route. -/

/-- The campaign's O3 obligation, re-proved here (`t1map_obligations.lean:61`). -/
theorem chunkedRank_geometry_only
    {b1 b2 : List Bool} {s1 k1 q1 s2 k2 q2 : Nat}
    (d1 : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b1 s1 k1 q1)
    (d2 : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b2 s2 k2 q2)
    (hlen : b1.length = b2.length)
    (hword : d1.wordSize = d2.wordSize)
    (hblocks : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos =
      d2.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hword, hblocks]

theorem rankWordSize_congr {a b : CartesianShape} (h : a.size = b.size) :
    (SuccinctFinal.builtRelativeSplitBPCloseRankData a).wordSize =
      (SuccinctFinal.builtRelativeSplitBPCloseRankData b).wordSize := by
  show SuccinctRank.machineWordBits a.bpCode.length =
    SuccinctRank.machineWordBits b.bpCode.length
  rw [bpLen_congr h]

theorem rankBlocksPerSuper_congr {a b : CartesianShape} (h : a.size = b.size) :
    (SuccinctFinal.builtRelativeSplitBPCloseRankData a).blocksPerSuper =
      (SuccinctFinal.builtRelativeSplitBPCloseRankData b).blocksPerSuper := by
  show SuccinctRank.machineWordBits a.bpCode.length =
    SuccinctRank.machineWordBits b.bpCode.length
  rw [bpLen_congr h]

/-- **Controller leaf L3 (rank-close) is size-only.** -/
theorem L3_rankClose_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store rankSegmentBase pos =
      SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store rankSegmentBase pos := by
  unfold SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [bpLen_congr h]
  exact chunkedRank_geometry_only _ _ (bpLen_congr h) (rankWordSize_congr h)
    (rankBlocksPerSuper_congr h) _ _ _ _ _ _ _ _

/-- **Controller leaf L2 at the controller route is size-only.** -/
theorem L2_route_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (leftClose rightClose : Nat) :
    SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store leftClose rightClose =
      SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store leftClose rightClose := by
  have hrank :
      SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          a store SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase =
        SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          b store SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact L3_rankClose_size_only h store _ pos
  unfold
    SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  rw [hrank]
  exact L2_lcaClose_size_only h _ _ _ _ _ _ _


/-! ### Bonus: the whole-query capstone (campaign T4). -/

open RMQ.SuccinctFinal in
theorem wholeQueryInstr_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore a store left right state =
      instr.evalGlobalWordTraceWithStore b store left right state := by
  cases instr with
  | selectClose dst idx =>
      simp only [WholeQueryInstr.evalGlobalWordTraceWithStore]
      rw [T1Map2.L1_route_shape_size_only h]
  | lcaClose dst leftReg rightReg =>
      cases hl : state.opt leftReg with
      | none =>
          cases hr : state.opt rightReg <;>
            simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
      | some lc =>
          cases hr : state.opt rightReg with
          | none =>
              simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
          | some rc =>
              simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
              rw [L2_route_size_only h]
  | rankCloseIfSome dst guard pos =>
      cases hg : state.opt guard with
      | none => simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]
      | some v =>
          simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]
          rw [L3_rankClose_size_only h]
  | outputPredIfSome dst guard src =>
      cases hg : state.opt guard <;>
        simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]

open RMQ.SuccinctFinal in
theorem wholeQueryProgram_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat) :
    forall (program : WholeQueryProgram) (state : WholeQueryState),
      WholeQueryProgram.evalGlobalWordTraceWithStore a store left right
          program state =
        WholeQueryProgram.evalGlobalWordTraceWithStore b store left right
          program state := by
  intro program
  induction program with
  | nil => intro state; rfl
  | cons instr rest ih =>
      intro state
      unfold WholeQueryProgram.evalGlobalWordTraceWithStore
      rw [wholeQueryInstr_congr h]
      apply congrArg
      funext state'
      exact ih state'

/--
**T4 — the literal `EG-CP-F03` geometry-closure statement.**

For all Cartesian shapes `a b` with `a.size = b.size`, all read stores and all
endpoints, the whole-query controller's *ordered logical read footprint* and its
*output value* coincide.  No size threshold, no regime restriction.
-/
theorem T4_wholeQuery_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        a store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        b store l r
    /\ (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          a store l r).value =
        (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          b store l r).value := by
  have hres :
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          a store l r =
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          b store l r := by
    unfold
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    rw [wholeQueryProgram_congr h]
  refine ⟨?_, ?_⟩
  · unfold
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    rw [hres]
  · rw [hres]

/-- The strictly stronger form actually proved: the entire trace agrees, not
just its read projection and the value. -/
theorem T4_wholeQuery_trace_size_only {a b : CartesianShape}
    (h : a.size = b.size) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        a store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        b store l r := by
  unfold
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  rw [wholeQueryProgram_congr h]


end L2X

/-! ============================================================
    VERIFICATION SECTION — anti-vacuity, quantifier and axiom checks.
    ============================================================ -/

namespace L2XVerify

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ### 1. The two sides really are about two DIFFERENT shapes. -/

def shapeL : CartesianShape :=
  CartesianShape.node (CartesianShape.node CartesianShape.empty
    CartesianShape.empty) CartesianShape.empty

def shapeR : CartesianShape :=
  CartesianShape.node CartesianShape.empty
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)

theorem witness_sizes_eq : shapeL.size = shapeR.size := by decide

theorem witness_shapes_ne : shapeL ≠ shapeR := by
  intro hcontra
  have : shapeL.bpCode = shapeR.bpCode := by rw [hcontra]
  revert this
  decide

theorem witness_codes_ne : shapeL.bpCode ≠ shapeR.bpCode := by decide

/-- The cross-block arm instantiated at two provably distinct shapes. -/
theorem crossBlock_at_distinct_shapes
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shapeL rankCloseTrace segments fringeSegment store leftClose
        rightClose =
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shapeR rankCloseTrace segments fringeSegment store leftClose
        rightClose :=
  L2X.L2_crossBlock_size_only witness_sizes_eq rankCloseTrace segments
    fringeSegment store leftClose rightClose

/-- T4 instantiated at the same distinct pair. -/
theorem T4_at_distinct_shapes (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        shapeL store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        shapeR store l r
    /\ (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shapeL store l r).value =
        (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shapeR store l r).value :=
  L2X.T4_wholeQuery_size_only witness_sizes_eq store l r

/-! ### 2. Expected-type pins, written independently of the declarations. -/

def ExpectedCrossBlockType : Prop :=
  forall (a b : CartesianShape), a.size = b.size ->
    forall (rct : Nat -> WordRAM.TraceResult Nat)
      (segs : BPRelativeRmmInteriorTraceSegments)
      (fs : Nat) (st : WordRAM.ReadStore) (lc rc : Nat),
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
          a rct segs fs st lc rc =
        bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
          b rct segs fs st lc rc

theorem expected_crossBlock : ExpectedCrossBlockType :=
  fun _a _b h => L2X.L2_crossBlock_size_only h

def ExpectedT4Type : Prop :=
  forall (a b : CartesianShape), a.size = b.size ->
    forall (st : WordRAM.ReadStore) (l r : Nat),
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
          a st l r =
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
          b st l r
      /\ (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            a st l r).value =
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            b st l r).value

theorem expected_T4 : ExpectedT4Type :=
  fun _a _b h => L2X.T4_wholeQuery_size_only h

def ExpectedOffsetsType : Prop :=
  forall (a b : CartesianShape), a.size = b.size ->
    canonicalRelativeRmmInteriorComponentOffsets a =
      canonicalRelativeRmmInteriorComponentOffsets b

theorem expected_offsets : ExpectedOffsetsType := fun _a _b h => L2X.offsets_congr h

/-! ### 3. Anti-bypass: a consumer holding ONLY `a.size = b.size`. -/

theorem antibypass_consumer
    (a b : CartesianShape) (hsize : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
    (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        a store l r).value =
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        b store l r).value :=
  (L2X.T4_wholeQuery_size_only hsize store l r).2

/-! ### 4. Quantifier display. -/

#check @L2X.L2_crossBlock_size_only
#check @L2X.L2_lcaClose_size_only
#check @L2X.L2_route_size_only
#check @L2X.L3_rankClose_size_only
#check @L2X.offsets_congr
#check @L2X.interiorRangeMinComputation_congr
#check @L2X.T4_wholeQuery_size_only

/-! ### 5. Non-vacuity by execution: the objects under the congruence are
     non-trivial — they issue reads, and both the value and the footprint
     move with the endpoints and with the store. -/

def realStore (s : CartesianShape) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore s

def deadStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

#eval show IO Unit from do
  let s := shapeL
  IO.println s!"ANTIVAC shapeL.size={s.size} shapeR.size={shapeR.size} \
bpCodeL={s.bpCode} bpCodeR={shapeR.bpCode}"
  for (l, r) in [(0, 0), (0, 1), (0, 2), (1, 2)] do
    let res :=
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        s (realStore s) l r
    let fp :=
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        s (realStore s) l r
    IO.println s!"ANTIVAC wholeQuery l={l} r={r} value={res.value} \
traceLen={res.trace.length} footprintLen={fp.length}"
  let dead :=
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      s deadStore 0 2
  IO.println s!"ANTIVAC wholeQuery deadStore value={dead.value} \
traceLen={dead.trace.length}"

/-! The cross-block arm forced onto its middle (interior) branch. -/
#eval show IO Unit from do
  let s := shapeL
  let store := realStore s
  let rct :=
    SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
      s store SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
  let segs := SuccinctFinal.concreteBPNativeInteriorTraceSegments
  let fs := SuccinctFinal.concreteBPNativeFringeChunkTraceSegment
  let bs := canonicalBPRelativeSummaryBlockSizeRaw s
  IO.println s!"ANTIVAC blockSizeRaw={bs} \
leftBlock(0)={blockOfClose bs 0} rightBlock(20)={blockOfClose bs 20}"
  for (lc, rc) in [(0, 5), (0, 20), (1, 30)] do
    let res :=
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        s rct segs fs store lc rc
    let resDead :=
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        s rct segs fs deadStore lc rc
    IO.println s!"ANTIVAC crossBlock lc={lc} rc={rc} \
value={res.value} traceLen={res.trace.length} \
deadValue={resDead.value} deadTraceLen={resDead.trace.length}"

/-! The interior range-min computation itself issues reads. -/
#eval show IO Unit from do
  let s := shapeL
  let store := realStore s
  let segs := SuccinctFinal.concreteBPNativeInteriorTraceSegments
  for (sb, cnt) in [(0, 1), (1, 4), (2, 7)] do
    let res :=
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        s segs store sb cnt
    IO.println s!"ANTIVAC interior startBlock={sb} count={cnt} \
value={res.value} traceLen={res.trace.length}"
  IO.println s!"ANTIVAC offsets={repr (canonicalRelativeRmmInteriorComponentOffsets s)}"
  IO.println s!"ANTIVAC offsetsR={repr (canonicalRelativeRmmInteriorComponentOffsets shapeR)}"


/-! Control: the executed objects DO vary with size, so the equal-size
    congruence is not a trivial 'everything is equal' statement. -/
def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

#eval show IO Unit from do
  IO.println "CONTROL n | offsets.deadAddress | wholeQuery footprintLen (l=0,r=1)"
  for n in [2, 4, 8, 16, 24, 40] do
    let s := leftSpine n
    let o := canonicalRelativeRmmInteriorComponentOffsets s
    let fp :=
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        s (realStore s) 0 1
    IO.println s!"CONTROL n={s.size} dead={o.deadAddress} fpLen={fp.length}"

/-! Executable confirmation of the theorem at equal size but different shape,
    across several sizes (leftSpine vs rightSpine). -/
#eval show IO Unit from do
  for n in [4, 8, 16, 24, 40] do
    let a := leftSpine n
    let b := rightSpine n
    let sameCode := a.bpCode == b.bpCode
    let fa :=
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        a (realStore a) 0 (n - 1)
    let fb :=
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        b (realStore a) 0 (n - 1)
    IO.println s!"GRID n={a.size} bpCodeEqual={sameCode} footprintsEqual={fa == fb} len={fa.length}"

end L2XVerify

/-! ### 6. Axioms of the FINAL theorems. -/

#print axioms L2X.L2_crossBlock_size_only
#print axioms L2X.L2_lcaClose_size_only
#print axioms L2X.L2_route_size_only
#print axioms L2X.L3_rankClose_size_only
#print axioms L2X.offsets_congr
#print axioms L2X.interiorRangeMinComputation_congr
#print axioms L2X.T4_wholeQuery_size_only
#print axioms L2X.T4_wholeQuery_trace_size_only
#print axioms L2XVerify.expected_crossBlock
#print axioms L2XVerify.expected_T4
#print axioms L2XVerify.expected_offsets
#print axioms L2XVerify.antibypass_consumer
#print axioms L2XVerify.crossBlock_at_distinct_shapes
#print axioms L2XVerify.T4_at_distinct_shapes
#print axioms L2XVerify.witness_codes_ne

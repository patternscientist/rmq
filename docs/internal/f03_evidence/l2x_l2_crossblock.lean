import RMQ.Core.SuccinctFinalStoreParam

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


end L2X

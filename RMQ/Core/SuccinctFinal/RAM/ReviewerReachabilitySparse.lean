import RMQ.Core.SuccinctFinalRAM

/-!
# Successful valid-query reachability for the sparse-select sources

This module supplies the sparse-local leaf of the occurrence-level reviewer
reachability proof.  The witness is symbolic: it uses the canonical
representative of a Cartesian shape of size `2^128`, rather than materializing
an enormous list.
-/

namespace RMQ
namespace SuccinctFinal

private def reviewerSparseLeftSpine : Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node (reviewerSparseLeftSpine n) .empty

private def reviewerSparseRightSpine : Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (reviewerSparseRightSpine n)

private theorem reviewerSparseLeftSpine_size (n : Nat) :
    (reviewerSparseLeftSpine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [reviewerSparseLeftSpine, Cartesian.CartesianShape.size, ih]

private theorem reviewerSparseRightSpine_size (n : Nat) :
    (reviewerSparseRightSpine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [reviewerSparseRightSpine, Cartesian.CartesianShape.size, ih]
      omega

private theorem reviewerSparseLeftSpine_close
    (n i : Nat) (hi : i < n) :
    SuccinctSpace.bpCloseOfInorder? (reviewerSparseLeftSpine n) i =
      some (n + i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hlt : i < n
      · simp [reviewerSparseLeftSpine, SuccinctSpace.bpCloseOfInorder?,
          reviewerSparseLeftSpine_size, hlt, ih i hlt]
        omega
      · have hieq : i = n := by omega
        subst i
        simp [reviewerSparseLeftSpine, SuccinctSpace.bpCloseOfInorder?,
          reviewerSparseLeftSpine_size,
          Cartesian.CartesianShape.bpCode_length]
        omega

private theorem reviewerSparseRightSpine_close
    (n i : Nat) (hi : i < n) :
    SuccinctSpace.bpCloseOfInorder? (reviewerSparseRightSpine n) i =
      some (2 * i + 1) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hzero : i = 0
      · subst i
        simp [reviewerSparseRightSpine, SuccinctSpace.bpCloseOfInorder?,
          Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode]
      · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
        have htail : i - 1 < n := by omega
        have ih' := ih (i - 1) htail
        simp [reviewerSparseRightSpine, SuccinctSpace.bpCloseOfInorder?,
          Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode,
          hzero, ih']
        omega

private def reviewerSparseN : Nat := 2 ^ 128

@[irreducible] private def reviewerSparseShape : Cartesian.CartesianShape :=
  .node .empty
    (.node (reviewerSparseLeftSpine 130)
      (reviewerSparseRightSpine (reviewerSparseN - 132)))

private theorem reviewerSparseN_pos : 0 < reviewerSparseN := by
  exact Nat.pow_pos (by omega)

private theorem reviewerSparseN_large : 17031 < reviewerSparseN := by
  have hsmall : 17031 < 2 ^ 15 := by decide
  have hmono : 2 ^ 15 <= 2 ^ 128 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.lt_of_lt_of_le hsmall hmono

private theorem node_empty_node_size
    (left right : Cartesian.CartesianShape) :
    (Cartesian.CartesianShape.node .empty
      (.node left right)).size = left.size + 2 + right.size := by
  simp [Cartesian.CartesianShape.size]
  omega

private theorem reviewerSparseShape_size :
    reviewerSparseShape.size = reviewerSparseN := by
  rw [reviewerSparseShape, node_empty_node_size,
    reviewerSparseLeftSpine_size, reviewerSparseRightSpine_size]
  have := reviewerSparseN_large
  omega

private theorem reviewerSparseShape_bpCode_length :
    reviewerSparseShape.bpCode.length = 2 ^ 129 := by
  rw [Cartesian.CartesianShape.bpCode_length, reviewerSparseShape_size]
  rw [show reviewerSparseN = 2 ^ 128 by rfl]

private theorem reviewerSparseShape_close_zero :
    Succinct.select false reviewerSparseShape.bpCode 0 = some 1 := by
  rw [SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?]
  simp [reviewerSparseShape, SuccinctSpace.bpCloseOfInorder?,
    Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode]

private theorem reviewerSparseShape_close_one :
    Succinct.select false reviewerSparseShape.bpCode 1 = some 133 := by
  rw [SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?]
  simp [reviewerSparseShape, SuccinctSpace.bpCloseOfInorder?,
    Cartesian.CartesianShape.size, reviewerSparseLeftSpine_size,
    reviewerSparseLeftSpine_close, Cartesian.CartesianShape.bpCode]

private theorem reviewerSparseShape_close_super_end :
    Succinct.select false reviewerSparseShape.bpCode 16899 = some 33799 := by
  rw [SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?]
  have htail : 16767 < reviewerSparseN - 132 := by
    have := reviewerSparseN_large
    omega
  simp [reviewerSparseShape, SuccinctSpace.bpCloseOfInorder?,
    Cartesian.CartesianShape.size, reviewerSparseLeftSpine_size,
    Cartesian.CartesianShape.bpCode_length, reviewerSparseRightSpine_close,
    htail, Cartesian.CartesianShape.bpCode]

private def reviewerSparseInput : List Int := reviewerSparseShape.representative

private theorem reviewerSparseInput_length :
    reviewerSparseInput.length = reviewerSparseN := by
  simp [reviewerSparseInput, Cartesian.CartesianShape.representative_length,
    reviewerSparseShape_size]

private theorem reviewerSparseInput_shape :
    Cartesian.shape reviewerSparseInput = reviewerSparseShape := by
  simp [reviewerSparseInput, Cartesian.CartesianShape.shape_representative]

private theorem reviewerSparseInput_valid :
    ValidRange reviewerSparseInput 0 1 := by
  change 0 < 1 ∧ 1 ≤ reviewerSparseInput.length
  rw [reviewerSparseInput_length]
  exact ⟨by omega, reviewerSparseN_pos⟩

private theorem reviewerSparse_occurrenceCount :
    GenericSelect.occurrenceCount reviewerSparseShape.bpCode false =
      reviewerSparseN := by
  unfold GenericSelect.occurrenceCount
  rw [SuccinctSpace.bpCode_rankFalse_full, reviewerSparseShape_size]

private theorem reviewerSparse_log2_le_of_lt_pow_succ {n k : Nat}
    (h : n < 2 ^ (k + 1)) : Nat.log2 n <= k := by
  by_cases hzero : n = 0
  · simp [hzero]
  · by_cases hle : Nat.log2 n <= k
    · exact hle
    have hk : k + 1 <= Nat.log2 n := by omega
    have hmono : 2 ^ (k + 1) <= 2 ^ Nat.log2 n :=
      Nat.pow_le_pow_right (by omega) hk
    have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hzero
    omega

private theorem reviewerSparse_log2_two_pow (k : Nat) :
    Nat.log2 (2 ^ k) = k := by
  apply Nat.le_antisymm
  · apply reviewerSparse_log2_le_of_lt_pow_succ
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    rw [Nat.pow_succ]
    omega
  · have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    exact (Nat.le_log2 (Nat.ne_of_gt hpos)).2 (Nat.le_refl _)

private theorem reviewerSparse_wordBits :
    GenericSelect.wordBits reviewerSparseShape.bpCode.length = 130 := by
  rw [reviewerSparseShape_bpCode_length]
  unfold GenericSelect.wordBits SuccinctRank.machineWordBits
  rw [reviewerSparse_log2_two_pow]

private theorem reviewerSparse_ell :
    GenericSelect.ell reviewerSparseShape.bpCode.length = 8 := by
  unfold GenericSelect.ell
  rw [reviewerSparse_wordBits]
  have hlower : 7 <= Nat.log2 130 :=
    (Nat.le_log2 (by omega)).2 (by decide)
  have hupper : Nat.log2 130 <= 7 :=
    reviewerSparse_log2_le_of_lt_pow_succ (by decide)
  omega

private theorem reviewerSparse_superStride :
    GenericSelect.superStride reviewerSparseShape.bpCode.length = 16900 := by
  simp [GenericSelect.superStride, reviewerSparse_wordBits]

private theorem reviewerSparse_localStride :
    GenericSelect.localStride reviewerSparseShape.bpCode.length = 2 := by
  simp [GenericSelect.localStride, reviewerSparse_wordBits,
    reviewerSparse_ell]

private theorem reviewerSparse_superLongSpan :
    GenericSelect.superLongSpan reviewerSparseShape.bpCode.length =
      17576000 := by
  simp [GenericSelect.superLongSpan, reviewerSparse_superStride,
    reviewerSparse_wordBits, reviewerSparse_ell]

private theorem reviewerSparse_position_zero :
    GenericSelect.position reviewerSparseShape.bpCode false 0 = 1 :=
  GenericSelect.position_eq_of_select _ _ reviewerSparseShape_close_zero

private theorem reviewerSparse_position_one :
    GenericSelect.position reviewerSparseShape.bpCode false 1 = 133 :=
  GenericSelect.position_eq_of_select _ _ reviewerSparseShape_close_one

private theorem reviewerSparse_position_super_end :
    GenericSelect.position reviewerSparseShape.bpCode false 16899 = 33799 :=
  GenericSelect.position_eq_of_select _ _ reviewerSparseShape_close_super_end

private theorem reviewerSparse_superEndOccurrence :
    GenericSelect.superEndOccurrence reviewerSparseShape.bpCode false 0 =
      16900 := by
  unfold GenericSelect.superEndOccurrence GenericSelect.superBaseOccurrence
  rw [reviewerSparse_superStride, reviewerSparse_occurrenceCount]
  change Nat.min 16900 reviewerSparseN = 16900
  apply Nat.min_eq_left
  have := reviewerSparseN_large
  omega

private theorem reviewerSparse_superSpan_of
    (bits : List Bool)
    (hend : GenericSelect.superEndOccurrence bits false 0 = 16900)
    (hposEnd : GenericSelect.position bits false 16899 = 33799)
    (hposZero : GenericSelect.position bits false 0 = 1) :
    GenericSelect.superSpan bits false 0 = 33799 := by
  have hbase : GenericSelect.superBaseOccurrence bits.length 0 = 0 := by
    simp [GenericSelect.superBaseOccurrence]
  have hsub : 16900 - 1 = 16899 := by omega
  simp only [GenericSelect.superSpan, hend, hbase, hsub, hposEnd, hposZero]

private theorem reviewerSparse_superSpan :
    GenericSelect.superSpan reviewerSparseShape.bpCode false 0 = 33799 :=
  reviewerSparse_superSpan_of reviewerSparseShape.bpCode
    reviewerSparse_superEndOccurrence reviewerSparse_position_super_end
    reviewerSparse_position_zero

private theorem reviewerSparse_super_short :
    GenericSelect.superIsLong reviewerSparseShape.bpCode false 0 = false := by
  unfold GenericSelect.superIsLong
  rw [reviewerSparse_superLongSpan, reviewerSparse_superSpan]
  decide

private theorem reviewerSparse_localBaseOccurrence :
    GenericSelect.localBaseOccurrence reviewerSparseShape.bpCode.length 0 = 0 := by
  simp [GenericSelect.localBaseOccurrence,
    GenericSelect.localSlotInSuperOfGlobal]

private theorem reviewerSparse_localSuperSlot :
    GenericSelect.localSuperSlot reviewerSparseShape.bpCode.length 0 = 0 := by
  simp [GenericSelect.localSuperSlot]

private theorem reviewerSparse_shortSuperLocalEndOccurrence :
    GenericSelect.shortSuperLocalEndOccurrence reviewerSparseShape.bpCode
        false 0 = 2 := by
  simp [GenericSelect.shortSuperLocalEndOccurrence,
    reviewerSparse_localBaseOccurrence, reviewerSparse_localStride,
    reviewerSparse_localSuperSlot, reviewerSparse_superEndOccurrence]

private theorem reviewerSparse_shortSuperLocalSpan :
    GenericSelect.shortSuperLocalSpan reviewerSparseShape.bpCode false 0 =
      133 := by
  simp [GenericSelect.shortSuperLocalSpan,
    reviewerSparse_localBaseOccurrence,
    reviewerSparse_shortSuperLocalEndOccurrence,
    reviewerSparse_position_zero, reviewerSparse_position_one]

private theorem reviewerSparse_local_sparse :
    GenericSelect.localIsSparseException reviewerSparseShape.bpCode false 0 =
      true := by
  simp [GenericSelect.localIsSparseException, reviewerSparse_localSuperSlot,
    reviewerSparse_super_short, reviewerSparse_wordBits,
    reviewerSparse_shortSuperLocalSpan]

private theorem reviewerSparse_superSlotCount_pos :
    0 < GenericSelect.superSlotCount reviewerSparseShape.bpCode false := by
  have hcover := GenericSelect.selectCeilDiv_mul_ge_of_pos
    (n := reviewerSparseN) (stride := 16900) (by omega)
  unfold GenericSelect.superSlotCount
  rw [reviewerSparse_occurrenceCount, reviewerSparse_superStride]
  by_cases hpos : 0 < GenericSelect.selectCeilDiv reviewerSparseN 16900
  · exact hpos
  · have hzero : GenericSelect.selectCeilDiv reviewerSparseN 16900 = 0 :=
      Nat.eq_zero_of_not_pos hpos
    rw [hzero] at hcover
    have hbad : reviewerSparseN <= 0 := by simpa using hcover
    exact False.elim
      ((Nat.ne_of_gt reviewerSparseN_pos) (Nat.eq_zero_of_le_zero hbad))

private theorem reviewerSparse_localSlotCount_pos :
    0 < GenericSelect.localSlotCount reviewerSparseShape.bpCode false := by
  rw [GenericSelect.localSlotCount]
  exact Nat.mul_pos reviewerSparse_superSlotCount_pos
    (GenericSelect.localSlotsPerSuper_pos reviewerSparseShape.bpCode.length)

private theorem reviewerSparse_effectiveLocalSlotCount_pos :
    0 < GenericSelect.sparseExceptionEffectiveLocalSlotCount
      reviewerSparseShape.bpCode false := by
  unfold GenericSelect.sparseExceptionEffectiveLocalSlotCount
  exact Nat.lt_min.mpr
    ⟨reviewerSparse_localSlotCount_pos, by
      rw [reviewerSparse_occurrenceCount]
      exact reviewerSparseN_pos⟩

private theorem reviewerSparse_local_live :
    GenericSelect.compactLocalEntryIsLive reviewerSparseShape.bpCode false 0 =
      true := by
  simp [GenericSelect.compactLocalEntryIsLive,
    reviewerSparse_localSuperSlot, reviewerSparse_super_short,
    reviewerSparse_localBaseOccurrence, reviewerSparse_occurrenceCount,
    reviewerSparseN_pos]

private theorem reviewerSparse_super_marked_false :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.superEntry reviewerSparseShape.bpCode false 0) = false := by
  rw [GenericSelect.superEntry_marked_eq_long]
  exact reviewerSparse_super_short

private theorem reviewerSparse_local_marked_true :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.localEntry reviewerSparseShape.bpCode false 0) = true := by
  rw [GenericSelect.localEntry_marked_eq_flag]
  simp [reviewerSparse_local_live, reviewerSparse_local_sparse]

private theorem fixedWidthNatTable_word_present_of_entry_present
    {entries : List Nat} {width i entry : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hentry : entries[i]? = some entry) :
    ∃ word, table.store.words[i]? = some word := by
  cases hword : table.store.words[i]? with
  | none =>
      have hexact := table.read_exact i
      rw [hword, hentry] at hexact
      simp at hexact
  | some word => exact ⟨word, rfl⟩

private theorem rankTraceResult_value_zero
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) :
    (data.rankTraceResult target 0).value = 0 := by
  have hrefine := data.rankTraceResult_refines_rankInterpretedCosted target 0
  have hexact := data.rankInterpretedCosted_exact target 0
  have hvalue :
      (data.rankTraceResult target 0).value =
        (data.rankInterpretedCosted target 0).value := by
    simpa [WordRAM.TraceResult.toCosted] using congrArg Costed.value hrefine
  have hexact' : (data.rankInterpretedCosted target 0).value = 0 := by
    simpa [Costed.erase, Succinct.rankPrefix] using hexact
  exact hvalue.trans hexact'

private theorem rankTraceResultRelabeled_successful_reads
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) (segmentBase deadSegment : Nat) :
    (∃ word, WordRAM.TraceEvent.readWord segmentBase 0 (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target 0)).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord (segmentBase + 1) 0 (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target 0)).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord (segmentBase + 2) 0 (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target 0)).trace) := by
  let store := data.rankRegisterWordRAMStore target
  have hsource (localSegment : Nat) (hlocal : localSegment < 3) :
      WordRAM.TraceEvent.readWord localSegment 0
          (store.readWord? localSegment 0) ∈
        (data.rankTraceResult target 0).trace := by
    have hcases : localSegment = 0 ∨ localSegment = 1 ∨ localSegment = 2 := by
      omega
    rcases hcases with rfl | rfl | rfl
    all_goals simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterProgram,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndexExpr,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndexExpr,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPosExpr,
      WordRAM.Register.NatExpr.eval,
      WordRAM.Register.RegFile.withNat1_nat_zero,
      WordRAM.Register.NatProgram.eval]
    all_goals split <;> simp [store]
  have hsuperEntry := data.super_present target 0 (by omega)
  rcases hsuperEntry with ⟨sample, hsample⟩
  have hsuperWord : ∃ word, (data.superSampleWords target)[0]? = some word := by
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using hsample
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using hsample
  have hblockEntry := data.block_present target 0 (by omega)
  rcases hblockEntry with ⟨delta, hdelta⟩
  have hblockWord : ∃ word, (data.blockSampleWords target)[0]? = some word := by
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using hdelta
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using hdelta
  rcases data.word_present 0 (by omega) with ⟨wordBits, hwordBits⟩
  rcases hsuperWord with ⟨superWord, hsuperWord⟩
  rcases hblockWord with ⟨blockWord, hblockWord⟩
  have hstoreSuper : store.readWord? 0 0 = some superWord := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hsuperWord
  have hstoreBlock : store.readWord? 1 0 = some blockWord := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hblockWord
  have hstoreBits : store.readWord? 2 0 = some wordBits := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hwordBits
  have hmapped (localSegment : Nat) (hlocal : localSegment < 3) :=
    List.mem_map_of_mem
      (f := WordRAM.TraceEvent.relabelReadSegmentWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment))
      (hsource localSegment hlocal)
  refine ⟨⟨superWord, ?_⟩, ⟨blockWord, ?_⟩, ⟨wordBits, ?_⟩⟩
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreSuper] using hmapped 0 (by omega)
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreBlock] using hmapped 1 (by omega)
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreBits] using hmapped 2 (by omega)

private theorem denseEntryTraceResultRelabeled_value
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table : GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
      entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    (table.readTraceResultRelabeled layout i).value = entries[i]? := by
  have hrefine := table.readTraceResultRelabeled_refines_interpretedCosted
    layout i
  have hexact := table.readInterpretedCosted_erase i
  have hvalue :
      (table.readTraceResultRelabeled layout i).value =
        (table.readInterpretedCosted i).value := by
    simpa [WordRAM.TraceResult.toCosted] using congrArg Costed.value hrefine
  exact hvalue.trans (by simpa [Costed.erase] using hexact)

private theorem relativeOffsetReadTraceResultRelabeled_successful
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (segmentBase deadSegment base slot : Nat)
    {word : WordRAM.Word}
    (hword : table.store.words[slot]? = some word) :
    WordRAM.TraceEvent.readWord segmentBase slot (some word) ∈
      (GenericSelect.relativeOffsetReadTraceResultRelabeled
        segmentBase deadSegment table base slot).trace := by
  simp [GenericSelect.relativeOffsetReadTraceResultRelabeled,
    SuccinctSpace.FixedWidthNatTable.readProgram,
    SuccinctSpace.PayloadWordStore.readProgram,
    WordRAM.Program.eval, WordRAM.TraceResult.map,
    WordRAM.TraceResult.relabelReadSegmentsWith,
    WordRAM.TraceResult.ofResult,
    WordRAM.TraceEvent.relabelReadSegmentWith,
    WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
    SuccinctSpace.FixedWidthNatTable.wordRAMStore,
    SuccinctSpace.PayloadWordStore.wordRAMStore_readWord?_zero, hword]

private theorem reviewerSparse_relativeEntry_zero :
    (GenericSelect.sparseExceptionRelativeEntries
      reviewerSparseShape.bpCode false)[0]? = some 0 := by
  have hlookup := GenericSelect.sparseExceptionRelativeEntries_lookup_exact
    reviewerSparseShape.bpCode false
    (globalLocalSlot := 0) (localOccurrence := 0) (pos := 1)
    reviewerSparse_localSlotCount_pos reviewerSparse_local_sparse
    (by rw [reviewerSparse_localStride]; omega)
    (by rw [reviewerSparse_localBaseOccurrence,
      reviewerSparse_localSuperSlot, reviewerSparse_superEndOccurrence]; omega)
    (by simpa [reviewerSparse_localBaseOccurrence] using
      reviewerSparseShape_close_zero)
  simpa [Succinct.rankPrefix, reviewerSparse_localStride,
    reviewerSparse_localBaseOccurrence, reviewerSparse_position_zero]
    using hlookup

private theorem canonicalSuperTableWithStore_eq_sparse
    (shape : Cartesian.CartesianShape) (slot : Nat) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).superTable.readTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot =
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).superTable.readTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable slot :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode
      false).superTable.readTraceResultRelabeledWithStore_eq_of_pullback
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superFirstOffset
      shape)
    slot

private theorem canonicalLocalTableWithStore_eq_sparse
    (shape : Cartesian.CartesianShape) (slot : Nat) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).localTable.readTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) slot =
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).localTable.readTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable slot :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode
      false).localTable.readTraceResultRelabeledWithStore_eq_of_pullback
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localFirstOffset
      shape)
    slot

private theorem chunkedRankTraceWithStore_successful_reads_sparse
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat)
    {superWord blockWord wordBitsWord : WordRAM.Word}
    (hsuper :
      store.readWord? superSegment (data.superIndex pos) = some superWord)
    (hblock :
      store.readWord? blockSegment (data.wordIndex pos) = some blockWord)
    (hword :
      store.readWord? wordSegment (data.wordIndex pos) =
        some wordBitsWord) :
    (.readWord superSegment (data.superIndex pos) (some superWord) ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target pos).trace) ∧
    (.readWord blockSegment (data.wordIndex pos) (some blockWord) ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target pos).trace) ∧
    (.readWord wordSegment (data.wordIndex pos) (some wordBitsWord) ∈
      (data.bpChunkedRankTraceResultWithStore store superSegment
        blockSegment wordSegment chunkSegment c target pos).trace) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore,
      WordRAM.TraceResult.bind_trace, List.mem_append,
      SuccinctClose.bpChunkReadTraceResult,
      SuccinctClose.bpWordReadTraceResult, hsuper, hblock, hword]

private theorem chunkedSparseDirectoryTrace_rank_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory : GenericSelect.SparseExceptionDirectory bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (directory.rankData.bpChunkedRankTraceResultWithStore store
        layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
        chunkSegment c true localSlot).trace) :
    event ∈
      (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
        store c base localSlot localOccurrence).trace := by
  unfold GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore
  rw [WordRAM.TraceResult.bind_trace]
  exact List.mem_append_left _ hmem

private theorem chunkedSparseDirectoryTrace_relative_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory : GenericSelect.SparseExceptionDirectory bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence exceptionRank : Nat)
    (hrankValue :
      (directory.rankData.bpChunkedRankTraceResultWithStore store
        layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
        chunkSegment c true localSlot).value = exceptionRank)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (GenericSelect.bpRelativeOffsetReadTraceResultWithStore store
        layout.relativeBase base
        (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
          localOccurrence directory.localStride)).trace) :
    event ∈
      (directory.bpChunkedReadTraceResultWithStore layout chunkSegment
        store c base localSlot localOccurrence).trace := by
  unfold GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hrankValue]
  exact hmem

private theorem chunkedSelectTrace_sparse_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value = some super)
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    (hlocal :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        store
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence idx) data.superStride
          data.localSlotsPerSuper data.localStride super)).value = some loc)
    (hlocalMarked :
      GenericSelect.relativeSplitSelectEntryIsMarked loc = true)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.sparseDirectory.bpChunkedReadTraceResultWithStore
        layout.sparseDirectory chunkSegment store c
        (GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence idx) data.superStride
          data.localSlotsPerSuper data.localStride super)
        ((data.queryOccurrence idx) -
          GenericSelect.relativeSplitSelectLocalBaseOccurrence super
            loc)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hshort]
  apply Or.inr
  simpa [hlocal, hlocalMarked] using hmem

private theorem twoLevelRankData_sample_words_present
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) (hpos : pos <= bits.length) :
    (∃ word,
      (data.superSampleWords
        target)[pos / data.wordSize / data.blocksPerSuper]? = some word) ∧
    (∃ word,
      (data.blockSampleWords target)[pos / data.wordSize]? = some word) ∧
    (∃ word,
      data.bitWords.store.words[pos / data.wordSize]? = some word) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases data.super_present target pos hpos with ⟨sample, hsample⟩
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hsample
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hsample
  · rcases data.block_present target pos hpos with ⟨delta, hdelta⟩
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hdelta
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hdelta
  · exact data.word_present pos hpos

private theorem chunkedRankTwinWithStore_value_zero
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    {store : WordRAM.ReadStore}
    {superSegment blockSegment wordSegment chunkSegment c : Nat}
    (hsuper :
      forall address,
        store.readWord? superSegment address =
          (data.superSampleWords true)[address]?)
    (hblock :
      forall address,
        store.readWord? blockSegment address =
          (data.blockSampleWords true)[address]?)
    (hword :
      forall address,
        store.readWord? wordSegment address =
          data.bitWords.store.words[address]?)
    (hchunk :
      forall address,
        store.readWord? chunkSegment address =
          (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (hc : 0 < c) (hlen : data.wordSize <= 8 * c) :
    (data.bpChunkedRankTraceResultWithStore store superSegment
      blockSegment wordSegment chunkSegment c true 0).value = 0 := by
  have h := data.bpChunkedRankTraceResultWithStore_toCosted_of_agree
    hsuper hblock hword hchunk 0
  have hv := congrArg Costed.value h
  rw [WordRAM.TraceResult.toCosted_value] at hv
  rw [hv, data.bpChunkedRankCosted_value_eq hc hlen true 0]
  have hexact := data.rankInterpretedCosted_exact true 0
  rw [Succinct.rankPrefix_zero] at hexact
  rw [data.rankInterpretedCosted_refines_rankCosted true 0] at hexact
  exact hexact

private theorem reviewerSparseDirectory_successful_reads :
    (∃ word, WordRAM.TraceEvent.readWord 13 0 (some word) ∈
      ((GenericSelect.sparseExceptionSelectData reviewerSparseShape.bpCode
        false).sparseDirectory.bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
        1 0 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 14 0 (some word) ∈
      ((GenericSelect.sparseExceptionSelectData reviewerSparseShape.bpCode
        false).sparseDirectory.bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
        1 0 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 15 0 (some word) ∈
      ((GenericSelect.sparseExceptionSelectData reviewerSparseShape.bpCode
        false).sparseDirectory.bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
        1 0 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 16 0 (some word) ∈
      ((GenericSelect.sparseExceptionSelectData reviewerSparseShape.bpCode
        false).sparseDirectory.bpChunkedReadTraceResultWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        concreteBPNativeFringeChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
        1 0 0).trace) := by
  let dataD := (GenericSelect.sparseExceptionSelectData
    reviewerSparseShape.bpCode false).sparseDirectory
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
  have hqp : dataD.rankData.queryPos 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos
    exact Nat.zero_min _
  have hwi : dataD.rankData.wordIndex 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex
    rw [hqp]
    exact Nat.zero_div _
  have hsi : dataD.rankData.superIndex 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex
    rw [hwi]
    exact Nat.zero_div _
  obtain ⟨⟨superWord, hsuperWord⟩, ⟨blockWord, hblockWord⟩,
      ⟨wordBits, hwordBits⟩⟩ :=
    twoLevelRankData_sample_words_present dataD.rankData true 0
      (Nat.zero_le _)
  rw [Nat.zero_div, Nat.zero_div] at hsuperWord
  rw [Nat.zero_div] at hblockWord
  rw [Nat.zero_div] at hwordBits
  have hsuperRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerSparseShape).readWord? layout.rankBase
          (dataD.rankData.superIndex 0) = some superWord := by
    rw [hsi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper]
    exact hsuperWord
  have hblockRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerSparseShape).readWord? (layout.rankBase + 1)
          (dataD.rankData.wordIndex 0) = some blockWord := by
    rw [hwi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock]
    exact hblockWord
  have hwordRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerSparseShape).readWord? (layout.rankBase + 2)
          (dataD.rankData.wordIndex 0) = some wordBits := by
    rw [hwi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankWord]
    exact hwordBits
  have hchunkReads := chunkedRankTraceWithStore_successful_reads_sparse
    dataD.rankData
    (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
    layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
    concreteBPNativeFringeChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
    true 0 hsuperRead hblockRead hwordRead
  have hagreeSuper := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper
      reviewerSparseShape address
  have hagreeBlock := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock
      reviewerSparseShape address
  have hagreeWord := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankWord
      reviewerSparseShape address
  have hagreeChunk := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable
      reviewerSparseShape address
  have hrankValueChunked :
      (dataD.rankData.bpChunkedRankTraceResultWithStore
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        layout.rankBase (layout.rankBase + 1) (layout.rankBase + 2)
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
        true 0).value = 0 := by
    exact chunkedRankTwinWithStore_value_zero dataD.rankData
      hagreeSuper hagreeBlock hagreeWord hagreeChunk
      (SuccinctClose.bpFringeChunkBits_pos reviewerSparseShape.bpCode.length)
      (concreteBPNativeSelectCloseSparseRank_wordSize_le_8_chunk
        reviewerSparseShape)
  have hdirectoryEntry : dataD.relativeEntries[0]? = some 0 := by
    simpa [dataD, GenericSelect.sparseExceptionSelectData,
      GenericSelect.sparseExceptionDirectory] using
      reviewerSparse_relativeEntry_zero
  rcases fixedWidthNatTable_word_present_of_entry_present
      dataD.relativeTable hdirectoryEntry with ⟨word16, hword16⟩
  have hrelRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerSparseShape).readWord? layout.relativeBase 0 =
        some word16 := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRelative]
    exact hword16
  have hslot :
      GenericSelect.relativeSplitSelectSparseCompactSlot 0 0
        dataD.localStride = 0 := by
    simp [GenericSelect.relativeSplitSelectSparseCompactSlot]
  have hrelMem :
      WordRAM.TraceEvent.readWord layout.relativeBase 0 (some word16) ∈
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
          layout.relativeBase 1
          (GenericSelect.relativeSplitSelectSparseCompactSlot 0 0
            dataD.localStride)).trace := by
    unfold GenericSelect.bpRelativeOffsetReadTraceResultWithStore
    rw [WordRAM.TraceResult.map_trace, hslot]
    simp [SuccinctClose.bpChunkReadTraceResult, hrelRead]
  rcases hchunkReads with ⟨h13c, h14c, h15c⟩
  refine ⟨⟨superWord, ?_⟩, ⟨blockWord, ?_⟩,
    ⟨wordBits, ?_⟩, ⟨word16, ?_⟩⟩
  · apply chunkedSparseDirectoryTrace_rank_mem dataD layout
      concreteBPNativeFringeChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
      (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
      1 0 0
    have h := h13c
    rw [hsi] at h
    exact h
  · apply chunkedSparseDirectoryTrace_rank_mem dataD layout
      concreteBPNativeFringeChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
      (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
      1 0 0
    have h := h14c
    rw [hwi] at h
    exact h
  · apply chunkedSparseDirectoryTrace_rank_mem dataD layout
      concreteBPNativeFringeChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
      (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
      1 0 0
    have h := h15c
    rw [hwi] at h
    exact h
  · apply chunkedSparseDirectoryTrace_relative_mem dataD layout
      concreteBPNativeFringeChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
      (SuccinctClose.bpFringeChunkBits reviewerSparseShape.bpCode.length)
      1 0 0 0 hrankValueChunked
    exact hrelMem

private theorem reviewerSparseSelect_successful_reads :
    (∃ word, WordRAM.TraceEvent.readWord 13 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerSparseShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 14 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerSparseShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 15 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerSparseShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 16 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerSparseShape 0).trace) := by
  let data := GenericSelect.sparseExceptionSelectData
    reviewerSparseShape.bpCode false
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  have hvalid : 0 < GenericSelect.occurrenceCount
      reviewerSparseShape.bpCode false := by
    rw [reviewerSparse_occurrenceCount]
    exact reviewerSparseN_pos
  have hsuperGet := GenericSelect.superEntries_get?
    reviewerSparseShape.bpCode false reviewerSparse_superSlotCount_pos
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape) 0 =
      data.superTable.readTraceResultRelabeled layout.superTable 0 :=
    canonicalSuperTableWithStore_eq_sparse reviewerSparseShape 0
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        0).value =
        some (GenericSelect.superEntry reviewerSparseShape.bpCode false 0) := by
    rw [hsuperWS]
    calc
      _ = data.superEntries[0]? :=
        denseEntryTraceResultRelabeled_value data.superTable
          layout.superTable 0
      _ = _ := by
        simpa [data, GenericSelect.sparseExceptionSelectData] using hsuperGet
  have hlocalSlot :
      GenericSelect.relativeSplitSelectLocalSlot
        0 data.superStride data.localSlotsPerSuper
        data.localStride
        (GenericSelect.superEntry reviewerSparseShape.bpCode false 0) = 0 := by
    simp [data, GenericSelect.sparseExceptionSelectData,
      GenericSelect.relativeSplitSelectLocalSlot,
      GenericSelect.relativeSplitSelectLocalSlotInSuper,
      GenericSelect.selectSuperSlot, GenericSelect.superEntry]
  have hlocalGet := GenericSelect.localEntries_get?
    reviewerSparseShape.bpCode false reviewerSparse_localSlotCount_pos
  have hlocalWS :
      data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape) 0 =
      data.localTable.readTraceResultRelabeled layout.localTable 0 :=
    canonicalLocalTableWithStore_eq_sparse reviewerSparseShape 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
        0).value =
        some (GenericSelect.localEntry reviewerSparseShape.bpCode false 0) := by
    rw [hlocalWS]
    calc
      _ = data.localEntries[0]? :=
        denseEntryTraceResultRelabeled_value data.localTable
          layout.localTable 0
      _ = _ := by
        simpa [data, GenericSelect.sparseExceptionSelectData] using hlocalGet
  have hbasePosition :
      GenericSelect.relativeSplitSelectLocalBasePosition data.wordSize
        (GenericSelect.superEntry reviewerSparseShape.bpCode false 0)
        (GenericSelect.localEntry reviewerSparseShape.bpCode false 0) = 1 := by
    have hexact := GenericSelect.localBasePosition_exact
      reviewerSparseShape.bpCode false 0 reviewerSparse_local_live
    simpa [data, GenericSelect.sparseExceptionSelectData,
      reviewerSparse_localBaseOccurrence, reviewerSparse_position_zero]
      using hexact
  have hsuperSlot' :
      GenericSelect.selectSuperSlot (data.queryOccurrence 0)
        data.superStride = 0 := by
    simp [GenericSelect.SparseExceptionSelectData.queryOccurrence,
      GenericSelect.selectSuperSlot]
  have liftSparse
      {event : WordRAM.TraceEvent}
      (hmem : event ∈
        (data.sparseDirectory.bpChunkedReadTraceResultWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
          (SuccinctClose.bpFringeChunkBits
            reviewerSparseShape.bpCode.length)
          1 0 0).trace) :
      event ∈
        (data.bpChunkedSelectTraceResultWithStore layout
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerSparseShape)
          (SuccinctClose.bpFringeChunkBits
            reviewerSparseShape.bpCode.length)
          0).trace := by
    apply chunkedSelectTrace_sparse_read_mem data layout _ _ _ _ 0 hvalid
      (GenericSelect.superEntry reviewerSparseShape.bpCode false 0)
      (GenericSelect.localEntry reviewerSparseShape.bpCode false 0)
      (by rw [show GenericSelect.selectSuperSlot (data.queryOccurrence 0)
            data.superStride = 0 from hsuperSlot']
          exact hsuperValue)
      reviewerSparse_super_marked_false
      (by rw [show GenericSelect.relativeSplitSelectLocalSlot
            (data.queryOccurrence 0) data.superStride
            data.localSlotsPerSuper data.localStride
            (GenericSelect.superEntry reviewerSparseShape.bpCode false 0) =
            0 from hlocalSlot]
          exact hlocalValue)
      reviewerSparse_local_marked_true
    rw [show GenericSelect.relativeSplitSelectLocalBasePosition
        data.wordSize
        (GenericSelect.superEntry reviewerSparseShape.bpCode false 0)
        (GenericSelect.localEntry reviewerSparseShape.bpCode false 0) =
        1 from hbasePosition]
    rw [show GenericSelect.relativeSplitSelectLocalSlot
        (data.queryOccurrence 0) data.superStride
        data.localSlotsPerSuper data.localStride
        (GenericSelect.superEntry reviewerSparseShape.bpCode false 0) =
        0 from hlocalSlot]
    rw [show (data.queryOccurrence 0) -
        GenericSelect.relativeSplitSelectLocalBaseOccurrence
          (GenericSelect.superEntry reviewerSparseShape.bpCode false 0)
          (GenericSelect.localEntry reviewerSparseShape.bpCode false 0) =
        0 from Nat.zero_sub _]
    exact hmem
  rcases reviewerSparseDirectory_successful_reads with
    ⟨⟨word13, h13⟩, ⟨word14, h14⟩, ⟨word15, h15⟩, ⟨word16, h16⟩⟩
  exact ⟨⟨word13, liftSparse h13⟩, ⟨word14, liftSparse h14⟩,
    ⟨word15, liftSparse h15⟩, ⟨word16, liftSparse h16⟩⟩

private theorem reviewerSource_successful_of_select_component_mem
    (shape : Cartesian.CartesianShape) (xs : List Int)
    (hshape : Cartesian.shape xs = shape)
    (hvalid : ValidRange xs 0 1)
    (source : ReviewerSource) (segment : Nat) (word : WordRAM.Word)
    (hsource :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source)
    (hmem : WordRAM.TraceEvent.readWord segment 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape 0).trace) :
    source.HasSuccessfulClosedValidOccurrence := by
  rcases List.mem_iff_getElem?.mp hmem with ⟨localPos, hlocalGet⟩
  have hlocalLt : localPos <
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape 0).trace.length :=
    (List.getElem?_eq_some_iff.mp hlocalGet).1
  have hinstrGet :
      ((WholeQueryInstr.selectClose .leftClose .inputLeft).evalGlobalWordTrace
        shape 0 1 WholeQueryState.empty).trace[localPos]? =
          some (.readWord segment 0 (some word)) := by
    simpa [WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
      WordRAM.TraceResult.map] using hlocalGet
  have hprogramGet :
      (WholeQueryProgram.evalGlobalWordTrace shape 0 1
        concreteBPNativeSuccinctRMQWholeQueryProgram
        WholeQueryState.empty).trace[localPos]? =
          some (.readWord segment 0 (some word)) := by
    simp only [concreteBPNativeSuccinctRMQWholeQueryProgram,
      WholeQueryProgram.evalGlobalWordTrace, WordRAM.TraceResult.bind_trace]
    rw [List.getElem?_append]
    have hlocalValue := (List.getElem?_eq_some_iff.mp hlocalGet).2
    simpa [hlocalLt, WholeQueryInstr.evalGlobalWordTrace,
      WholeQueryNatExpr.eval, WordRAM.TraceResult.map] using hlocalValue
  have hglobalGet :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) 0 1).trace[localPos]? =
          some (.readWord segment 0 (some word)) := by
    rw [hshape]
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult,
      WordRAM.TraceResult.map] using hprogramGet
  have hproducer : WholeQueryProgram.ProducesEventAt shape 0 1
      (.readWord segment 0 (some word))
      concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
      localPos 0 (.selectClose .leftClose .inputLeft)
      WholeQueryState.empty localPos := by
    refine ⟨[],
      [ WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1))
      , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
      , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
          (.add (.optNatD .answerClose 0) (.const 1))
      , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
      ], rfl, rfl, ?_, ?_, hinstrGet⟩
    · simp [WholeQueryProgram.evalGlobalWordTrace]
    · simp [WholeQueryProgram.evalGlobalWordTrace]
  refine ⟨⟨segment, .selectClose⟩, hsource, word,
    xs, 0, 1, localPos, 0, hvalid, hglobalGet,
    0, .selectClose .leftClose .inputLeft, WholeQueryState.empty,
    localPos, .selectClose 0, ?_, ?_, rfl, ?_⟩
  · simpa [hshape] using hproducer
  · exact WholeQueryInstr.InvokesReviewerRead.selectClose .leftClose .inputLeft
  · simpa [ReviewerReadInvocation.componentTrace, hshape] using hlocalGet

/-- The four sparse-directory reviewer sources have successful indexed
occurrences in one actual closed valid query. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_sparse_successful_closed_valid_occurrence
    (source : ReviewerSource)
    (hsource : source ∈
      [.selectSparseRankSuperTrue, .selectSparseRankBlockTrue,
        .selectSparseFlagBits, .selectSparseRelative]) :
    source.HasSuccessfulClosedValidOccurrence := by
  rcases reviewerSparseSelect_successful_reads with
    ⟨⟨word13, h13⟩, ⟨word14, h14⟩, ⟨word15, h15⟩, ⟨word16, h16⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with h | h | h | h
  all_goals subst source
  · exact reviewerSource_successful_of_select_component_mem
      reviewerSparseShape reviewerSparseInput reviewerSparseInput_shape
      reviewerSparseInput_valid .selectSparseRankSuperTrue 13 word13 rfl h13
  · exact reviewerSource_successful_of_select_component_mem
      reviewerSparseShape reviewerSparseInput reviewerSparseInput_shape
      reviewerSparseInput_valid .selectSparseRankBlockTrue 14 word14 rfl h14
  · exact reviewerSource_successful_of_select_component_mem
      reviewerSparseShape reviewerSparseInput reviewerSparseInput_shape
      reviewerSparseInput_valid .selectSparseFlagBits 15 word15 rfl h15
  · exact reviewerSource_successful_of_select_component_mem
      reviewerSparseShape reviewerSparseInput reviewerSparseInput_shape
      reviewerSparseInput_valid .selectSparseRelative 16 word16 rfl h16

end SuccinctFinal
end RMQ

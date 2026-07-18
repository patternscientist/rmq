import RMQ.Core.SuccinctFinalRAM

/-!
# Successful valid-query reachability for the long-select sources

This module supplies the long-super leaf of the occurrence-level reviewer
reachability proof.  The witness is symbolic: it uses the canonical
representative of a Cartesian shape of size `2^15`, rather than materializing
an enormous list.
-/

namespace RMQ

namespace SuccinctFinal

private def reviewerLongLeftSpine : Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node (reviewerLongLeftSpine n) .empty

private theorem reviewerLongLeftSpine_size (n : Nat) :
    (reviewerLongLeftSpine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [reviewerLongLeftSpine, Cartesian.CartesianShape.size, ih]

private theorem reviewerLongLeftSpine_close
    (n i : Nat) (hi : i < n) :
    SuccinctSpace.bpCloseOfInorder? (reviewerLongLeftSpine n) i =
      some (n + i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hlt : i < n
      · simp [reviewerLongLeftSpine, SuccinctSpace.bpCloseOfInorder?,
          reviewerLongLeftSpine_size, hlt, ih i hlt]
        omega
      · have hieq : i = n := by omega
        subst i
        simp [reviewerLongLeftSpine, SuccinctSpace.bpCloseOfInorder?,
          reviewerLongLeftSpine_size,
          Cartesian.CartesianShape.bpCode_length]
        omega

private theorem replicate_append_singleton (n : Nat) (value : Bool) :
    List.replicate n value ++ [value] = List.replicate (n + 1) value := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      congr 1

private theorem reviewerLongLeftSpine_bpCode (n : Nat) :
    (reviewerLongLeftSpine n).bpCode =
      List.replicate n true ++ List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [reviewerLongLeftSpine, Cartesian.CartesianShape.bpCode, ih,
        List.cons_append, List.replicate_succ]
      rw [List.append_assoc]
      rw [replicate_append_singleton]
      rw [List.replicate_succ]

private theorem reviewerLongNode_size (n : Nat) :
    (Cartesian.CartesianShape.node .empty (reviewerLongLeftSpine n)).size =
      n + 1 := by
  rw [Cartesian.CartesianShape.size, reviewerLongLeftSpine_size]
  simp only [Cartesian.CartesianShape.size]
  omega

private theorem reviewerLongNode_bpCode (n : Nat) :
    (Cartesian.CartesianShape.node .empty (reviewerLongLeftSpine n)).bpCode =
      [true, false] ++ List.replicate n true ++ List.replicate n false := by
  rw [Cartesian.CartesianShape.bpCode, reviewerLongLeftSpine_bpCode]
  rfl

private def reviewerLongN : Nat := 2 ^ 15

@[irreducible] private def reviewerLongSpine : Cartesian.CartesianShape :=
  reviewerLongLeftSpine (reviewerLongN - 1)

private theorem reviewerLongSpine_size :
    reviewerLongSpine.size = reviewerLongN - 1 := by
  rw [reviewerLongSpine, reviewerLongLeftSpine_size]

private theorem reviewerLongSpine_bpCode :
    reviewerLongSpine.bpCode =
      List.replicate (reviewerLongN - 1) true ++
        List.replicate (reviewerLongN - 1) false := by
  rw [reviewerLongSpine, reviewerLongLeftSpine_bpCode]

private def reviewerLongShape : Cartesian.CartesianShape :=
  .node .empty reviewerLongSpine

private theorem reviewerLongShape_eq :
    reviewerLongShape =
      .node .empty reviewerLongSpine := rfl

private theorem reviewerLongN_pos : 0 < reviewerLongN := by
  simp [reviewerLongN]

private theorem reviewerLongN_large : 24566 < reviewerLongN := by
  decide

private theorem reviewerLongShape_size : reviewerLongShape.size = reviewerLongN := by
  rw [reviewerLongShape_eq, Cartesian.CartesianShape.size,
    reviewerLongSpine_size]
  simp only [Cartesian.CartesianShape.size]
  have hpos := reviewerLongN_pos
  omega

private theorem reviewerLongShape_bpCode :
    reviewerLongShape.bpCode =
      [true, false] ++
        List.replicate (reviewerLongN - 1) true ++
        List.replicate (reviewerLongN - 1) false := by
  rw [reviewerLongShape_eq, Cartesian.CartesianShape.bpCode,
    reviewerLongSpine_bpCode]
  rfl

private theorem reviewerLongShape_bpCode_length :
    reviewerLongShape.bpCode.length = 2 ^ 16 := by
  rw [Cartesian.CartesianShape.bpCode_length, reviewerLongShape_size]
  rw [show reviewerLongN = 2 ^ 15 by rfl, Nat.pow_succ]

private theorem reviewerLong_occurrenceCount_false :
    GenericSelect.occurrenceCount reviewerLongShape.bpCode false =
      reviewerLongN := by
  unfold GenericSelect.occurrenceCount
  rw [SuccinctSpace.bpCode_rankFalse_full, reviewerLongShape_size]

private theorem reviewerLong_select_false_zero :
    Succinct.select false reviewerLongShape.bpCode 0 = some 1 := by
  rw [SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?]
  simp [reviewerLongShape, SuccinctSpace.bpCloseOfInorder?,
    Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode]

private theorem reviewerLongSpine_close_287 :
    SuccinctSpace.bpCloseOfInorder? reviewerLongSpine 287 =
      some (reviewerLongN - 1 + 287) := by
  rw [reviewerLongSpine]
  apply reviewerLongLeftSpine_close
  have := reviewerLongN_large
  omega

private theorem reviewerLong_log2_le_of_lt_pow_succ {n k : Nat}
    (h : n < 2 ^ (k + 1)) : Nat.log2 n ≤ k := by
  by_cases hzero : n = 0
  · simp [hzero]
  · by_cases hle : Nat.log2 n ≤ k
    · exact hle
    have hk : k + 1 ≤ Nat.log2 n := by omega
    have hmono : 2 ^ (k + 1) ≤ 2 ^ Nat.log2 n :=
      Nat.pow_le_pow_right (by omega) hk
    have hself : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hzero
    omega

private theorem reviewerLong_log2_two_pow (k : Nat) :
    Nat.log2 (2 ^ k) = k := by
  apply Nat.le_antisymm
  · apply reviewerLong_log2_le_of_lt_pow_succ
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    rw [Nat.pow_succ]
    omega
  · have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    exact (Nat.le_log2 (Nat.ne_of_gt hpos)).2 (Nat.le_refl _)

private theorem reviewerLong_wordBits :
    GenericSelect.wordBits reviewerLongShape.bpCode.length = 17 := by
  rw [reviewerLongShape_bpCode_length]
  unfold GenericSelect.wordBits SuccinctRank.machineWordBits
  rw [reviewerLong_log2_two_pow]

private theorem reviewerLong_ell :
    GenericSelect.ell reviewerLongShape.bpCode.length = 5 := by
  unfold GenericSelect.ell
  rw [reviewerLong_wordBits]
  have hlower : 4 ≤ Nat.log2 17 :=
    (Nat.le_log2 (by omega)).2 (by decide)
  have hupper : Nat.log2 17 ≤ 4 :=
    reviewerLong_log2_le_of_lt_pow_succ (by decide)
  omega

private theorem reviewerLong_superStride :
    GenericSelect.superStride reviewerLongShape.bpCode.length = 289 := by
  simp [GenericSelect.superStride, reviewerLong_wordBits]

private theorem reviewerLong_superLongSpan :
    GenericSelect.superLongSpan reviewerLongShape.bpCode.length = 24565 := by
  simp [GenericSelect.superLongSpan, reviewerLong_superStride,
    reviewerLong_wordBits, reviewerLong_ell]

private theorem reviewerLong_select_false_superEnd :
    Succinct.select false reviewerLongShape.bpCode 288 =
      some (reviewerLongN + 288) := by
  rw [SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?]
  change
    (SuccinctSpace.bpCloseOfInorder?
      reviewerLongSpine 287).map
        (fun pos => 2 + pos) = some (reviewerLongN + 288)
  rw [reviewerLongSpine_close_287]
  simp only [Option.map_some, Option.some.injEq]
  have hsub : reviewerLongN - 1 + 1 = reviewerLongN := by
    apply Nat.sub_add_cancel
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt reviewerLongN_pos)
  calc
    2 + (reviewerLongN - 1 + 287) =
        (reviewerLongN - 1 + 1) + 288 := by omega
    _ = reviewerLongN + 288 := by rw [hsub]

private theorem reviewerLong_position_false_zero :
    GenericSelect.position reviewerLongShape.bpCode false 0 = 1 := by
  exact GenericSelect.position_eq_of_select reviewerLongShape.bpCode false
    reviewerLong_select_false_zero

private theorem reviewerLong_position_false_superEnd :
    GenericSelect.position reviewerLongShape.bpCode false 288 =
      reviewerLongN + 288 := by
  exact GenericSelect.position_eq_of_select reviewerLongShape.bpCode false
    reviewerLong_select_false_superEnd

private theorem reviewerLong_superEndOccurrence_zero :
    GenericSelect.superEndOccurrence reviewerLongShape.bpCode false 0 = 289 := by
  unfold GenericSelect.superEndOccurrence GenericSelect.superBaseOccurrence
  rw [reviewerLong_superStride, reviewerLong_occurrenceCount_false]
  change Nat.min 289 reviewerLongN = 289
  apply Nat.min_eq_left
  have := reviewerLongN_large
  omega

private theorem superSpan_eq_of_values
    (bits : List Bool) (target : Bool) (slot baseOccurrence endOccurrence : Nat)
    (basePosition endPosition : Nat)
    (hbase : GenericSelect.superBaseOccurrence bits.length slot = baseOccurrence)
    (hend : GenericSelect.superEndOccurrence bits target slot = endOccurrence)
    (hbasePosition :
      GenericSelect.position bits target baseOccurrence = basePosition)
    (hendPosition :
      GenericSelect.position bits target (endOccurrence - 1) = endPosition) :
    GenericSelect.superSpan bits target slot =
      endPosition + 1 - basePosition := by
  unfold GenericSelect.superSpan
  rw [hbase, hend]
  simp only
  rw [hbasePosition, hendPosition]

private theorem reviewerLong_superSpan_zero :
    GenericSelect.superSpan reviewerLongShape.bpCode false 0 =
      reviewerLongN + 288 := by
  have hbase :
      GenericSelect.superBaseOccurrence reviewerLongShape.bpCode.length 0 = 0 := by
    simp [GenericSelect.superBaseOccurrence]
  have hendPosition :
      GenericSelect.position reviewerLongShape.bpCode false (289 - 1) =
        reviewerLongN + 288 := by
    simpa using reviewerLong_position_false_superEnd
  calc
    GenericSelect.superSpan reviewerLongShape.bpCode false 0 =
        (reviewerLongN + 288) + 1 - 1 := by
      exact superSpan_eq_of_values reviewerLongShape.bpCode false 0 0 289
        1 (reviewerLongN + 288) hbase
        reviewerLong_superEndOccurrence_zero reviewerLong_position_false_zero
        hendPosition
    _ = reviewerLongN + 288 := Nat.add_sub_cancel _ _

private theorem reviewerLong_superIsLong_zero :
    GenericSelect.superIsLong reviewerLongShape.bpCode false 0 = true := by
  unfold GenericSelect.superIsLong
  rw [reviewerLong_superLongSpan, reviewerLong_superSpan_zero]
  have := reviewerLongN_large
  simp only [decide_eq_true_eq]
  omega

private def reviewerLongInput : List Int := reviewerLongShape.representative

private theorem reviewerLongInput_length :
    reviewerLongInput.length = reviewerLongN := by
  simp [reviewerLongInput, Cartesian.CartesianShape.representative_length,
    reviewerLongShape_size]

private theorem reviewerLongInput_shape :
    Cartesian.shape reviewerLongInput = reviewerLongShape := by
  simp [reviewerLongInput, Cartesian.CartesianShape.shape_representative]

private theorem reviewerLongInput_valid : ValidRange reviewerLongInput 0 1 := by
  change 0 < 1 ∧ 1 ≤ reviewerLongInput.length
  rw [reviewerLongInput_length]
  constructor
  · omega
  · exact reviewerLongN_pos

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
  rcases data.super_present target 0 (by omega) with ⟨sample, hsample⟩
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
  rcases data.block_present target 0 (by omega) with ⟨delta, hdelta⟩
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

private theorem reviewerLong_superSlotCount_pos :
    0 < GenericSelect.superSlotCount reviewerLongShape.bpCode false := by
  have hcover := GenericSelect.selectCeilDiv_mul_ge_of_pos
    (n := reviewerLongN) (stride := 289) (by omega)
  unfold GenericSelect.superSlotCount
  rw [reviewerLong_occurrenceCount_false, reviewerLong_superStride]
  by_cases hpos : 0 < GenericSelect.selectCeilDiv reviewerLongN 289
  · exact hpos
  · have hzero : GenericSelect.selectCeilDiv reviewerLongN 289 = 0 :=
      Nat.eq_zero_of_not_pos hpos
    rw [hzero] at hcover
    have hbad : reviewerLongN ≤ 0 := by simpa using hcover
    exfalso
    exact (Nat.ne_of_gt reviewerLongN_pos) (Nat.eq_zero_of_le_zero hbad)

private theorem reviewerLong_super_marked_true :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.superEntry reviewerLongShape.bpCode false 0) = true := by
  rw [GenericSelect.superEntry_marked_eq_long]
  exact reviewerLong_superIsLong_zero

private theorem reviewerLong_relativeEntry_zero :
    (GenericSelect.longSuperRelativeEntries
      reviewerLongShape.bpCode false)[0]? = some 0 := by
  have hlookup := GenericSelect.longSuperRelativeEntries_lookup_exact
    reviewerLongShape.bpCode false
    (superSlot := 0) (localOccurrence := 0) (pos := 1)
    reviewerLong_superSlotCount_pos reviewerLong_superIsLong_zero
    (by rw [reviewerLong_superStride]; omega)
    (by
      rw [reviewerLong_superEndOccurrence_zero]
      simp [GenericSelect.superBaseOccurrence])
    (by
      simpa [GenericSelect.superBaseOccurrence] using
        reviewerLong_select_false_zero)
  simpa [Succinct.rankPrefix, GenericSelect.superBaseOccurrence,
    reviewerLong_superStride, reviewerLong_position_false_zero] using hlookup

private theorem canonicalSuperTableWithStore_eq_long
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

private theorem chunkedRankTraceWithStore_successful_reads_long
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

private theorem twoLevelRankData_sample_words_present_long
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

private theorem chunkedRankTwinWithStore_value_zero_long
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

private theorem chunkedSelectTrace_longRank_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value = some super)
    (hmarked :
      GenericSelect.relativeSplitSelectEntryIsMarked super = true)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.longFlagRankData.bpChunkedRankTraceResultWithStore store
        layout.longFlagRankBase (layout.longFlagRankBase + 1)
        (layout.longFlagRankBase + 2) chunkSegment c true
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hmarked]
  exact Or.inl hmem

private theorem chunkedSelectTrace_longRelative_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value = some super)
    (hmarked :
      GenericSelect.relativeSplitSelectEntryIsMarked super = true)
    (exceptionRank : Nat)
    (hrankValue :
      (data.longFlagRankData.bpChunkedRankTraceResultWithStore store
        layout.longFlagRankBase (layout.longFlagRankBase + 1)
        (layout.longFlagRankBase + 2) chunkSegment c true
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value =
        exceptionRank)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (GenericSelect.bpRelativeOffsetReadTraceResultWithStore store
        layout.longRelativeBase
        (GenericSelect.relativeSplitSelectEntryBasePosition
          data.wordSize super)
        (GenericSelect.relativeSplitSelectLongCompactSlot exceptionRank
          ((data.queryOccurrence idx) - super.baseOccurrence)
          data.superStride)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hmarked]
  apply Or.inr
  rw [hrankValue]
  exact hmem

private theorem reviewerLongSelect_successful_reads :
    (∃ word, WordRAM.TraceEvent.readWord 9 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerLongShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 10 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerLongShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 11 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerLongShape 0).trace) ∧
    (∃ word, WordRAM.TraceEvent.readWord 12 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        reviewerLongShape 0).trace) := by
  let data := GenericSelect.sparseExceptionSelectData
    reviewerLongShape.bpCode false
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  have hvalid : 0 < GenericSelect.occurrenceCount
      reviewerLongShape.bpCode false := by
    rw [reviewerLong_occurrenceCount_false]
    exact reviewerLongN_pos
  have hsuperGet := GenericSelect.superEntries_get?
    reviewerLongShape.bpCode false reviewerLong_superSlotCount_pos
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape) 0 =
      data.superTable.readTraceResultRelabeled layout.superTable 0 :=
    canonicalSuperTableWithStore_eq_long reviewerLongShape 0
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        0).value =
        some (GenericSelect.superEntry reviewerLongShape.bpCode false 0) := by
    rw [hsuperWS]
    calc
      _ = data.superEntries[0]? :=
        denseEntryTraceResultRelabeled_value data.superTable
          layout.superTable 0
      _ = _ := by
        simpa [data, GenericSelect.sparseExceptionSelectData] using hsuperGet
  have hsuperBaseOccurrence :
      (GenericSelect.superEntry reviewerLongShape.bpCode false 0).baseOccurrence =
        0 := by
    simp [GenericSelect.superEntry]
  have hbasePosition :
      GenericSelect.relativeSplitSelectEntryBasePosition data.wordSize
        (GenericSelect.superEntry reviewerLongShape.bpCode false 0) = 1 := by
    simp [data, GenericSelect.sparseExceptionSelectData,
      GenericSelect.relativeSplitSelectEntryBasePosition,
      GenericSelect.superEntry, reviewerLong_wordBits,
      reviewerLong_position_false_zero]
  have hsuperSlot : GenericSelect.selectSuperSlot 0 data.superStride = 0 := by
    simp [GenericSelect.selectSuperSlot]
  have hagreeSuper := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper
      reviewerLongShape address
  have hagreeBlock := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock
      reviewerLongShape address
  have hagreeWord := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagWord
      reviewerLongShape address
  have hagreeChunk := fun address =>
    concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable
      reviewerLongShape address
  have hrankValueChunked :
      (data.longFlagRankData.bpChunkedRankTraceResultWithStore
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        layout.longFlagRankBase (layout.longFlagRankBase + 1)
        (layout.longFlagRankBase + 2)
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
        true 0).value = 0 := by
    exact chunkedRankTwinWithStore_value_zero_long data.longFlagRankData
      hagreeSuper hagreeBlock hagreeWord hagreeChunk
      (SuccinctClose.bpFringeChunkBits_pos reviewerLongShape.bpCode.length)
      (concreteBPNativeSelectCloseLongFlagRank_wordSize_le_8_chunk
        reviewerLongShape)
  have hqp : data.longFlagRankData.queryPos 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos
    exact Nat.zero_min _
  have hwi : data.longFlagRankData.wordIndex 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex
    rw [hqp]
    exact Nat.zero_div _
  have hsi : data.longFlagRankData.superIndex 0 = 0 := by
    unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex
    rw [hwi]
    exact Nat.zero_div _
  obtain ⟨⟨superWord, hsuperWord⟩, ⟨blockWord, hblockWord⟩,
      ⟨wordBits, hwordBits⟩⟩ :=
    twoLevelRankData_sample_words_present_long data.longFlagRankData true 0
      (Nat.zero_le _)
  rw [Nat.zero_div, Nat.zero_div] at hsuperWord
  rw [Nat.zero_div] at hblockWord
  rw [Nat.zero_div] at hwordBits
  have hsuperRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerLongShape).readWord? layout.longFlagRankBase
          (data.longFlagRankData.superIndex 0) = some superWord := by
    rw [hsi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper]
    exact hsuperWord
  have hblockRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerLongShape).readWord? (layout.longFlagRankBase + 1)
          (data.longFlagRankData.wordIndex 0) = some blockWord := by
    rw [hwi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock]
    exact hblockWord
  have hwordRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerLongShape).readWord? (layout.longFlagRankBase + 2)
          (data.longFlagRankData.wordIndex 0) = some wordBits := by
    rw [hwi]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagWord]
    exact hwordBits
  have hchunkReads := chunkedRankTraceWithStore_successful_reads_long
    data.longFlagRankData
    (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
    layout.longFlagRankBase (layout.longFlagRankBase + 1)
    (layout.longFlagRankBase + 2)
    concreteBPNativeFringeChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
    true 0 hsuperRead hblockRead hwordRead
  have hrelativeEntry : data.longSuperRelativeEntries[0]? = some 0 := by
    simpa [data, GenericSelect.sparseExceptionSelectData] using
      reviewerLong_relativeEntry_zero
  rcases fixedWidthNatTable_word_present_of_entry_present
      data.longSuperRelativeTable hrelativeEntry with ⟨word12, hword12⟩
  have hrelRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        reviewerLongShape).readWord? layout.longRelativeBase 0 =
        some word12 := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectLongRelative]
    exact hword12
  have h12mem :
      WordRAM.TraceEvent.readWord layout.longRelativeBase 0 (some word12) ∈
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
          layout.longRelativeBase 1 0).trace := by
    unfold GenericSelect.bpRelativeOffsetReadTraceResultWithStore
    rw [WordRAM.TraceResult.map_trace]
    simp [SuccinctClose.bpChunkReadTraceResult, hrelRead]
  have liftRank
      {event : WordRAM.TraceEvent}
      (hmem : event ∈
        (data.longFlagRankData.bpChunkedRankTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
          layout.longFlagRankBase (layout.longFlagRankBase + 1)
          (layout.longFlagRankBase + 2)
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
          true 0).trace) :
      event ∈
        (data.bpChunkedSelectTraceResultWithStore layout
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
          (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
          0).trace := by
    apply chunkedSelectTrace_longRank_read_mem data layout _ _ _ _ 0 hvalid
      (GenericSelect.superEntry reviewerLongShape.bpCode false 0)
      (by
        rw [show GenericSelect.selectSuperSlot (data.queryOccurrence 0)
            data.superStride = 0 from hsuperSlot]
        exact hsuperValue)
      reviewerLong_super_marked_true
    rw [show GenericSelect.selectSuperSlot (data.queryOccurrence 0)
        data.superStride = 0 from hsuperSlot]
    exact hmem
  have liftRelative
      {event : WordRAM.TraceEvent}
      (hmem : event ∈
        (GenericSelect.bpRelativeOffsetReadTraceResultWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
          layout.longRelativeBase 1 0).trace) :
      event ∈
        (data.bpChunkedSelectTraceResultWithStore layout
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
          (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
          0).trace := by
    apply chunkedSelectTrace_longRelative_read_mem data layout _ _ _ _ 0
      hvalid (GenericSelect.superEntry reviewerLongShape.bpCode false 0)
      (by
        rw [show GenericSelect.selectSuperSlot (data.queryOccurrence 0)
            data.superStride = 0 from hsuperSlot]
        exact hsuperValue)
      reviewerLong_super_marked_true 0
      (by
        rw [show GenericSelect.selectSuperSlot (data.queryOccurrence 0)
            data.superStride = 0 from hsuperSlot]
        exact hrankValueChunked)
    rw [show GenericSelect.relativeSplitSelectEntryBasePosition
        data.wordSize
        (GenericSelect.superEntry reviewerLongShape.bpCode false 0) =
        1 from hbasePosition]
    rw [show GenericSelect.relativeSplitSelectLongCompactSlot 0
        ((data.queryOccurrence 0) -
          (GenericSelect.superEntry
            reviewerLongShape.bpCode false 0).baseOccurrence)
        data.superStride = 0 from by
      simp [GenericSelect.relativeSplitSelectLongCompactSlot,
        GenericSelect.SparseExceptionSelectData.queryOccurrence,
        hsuperBaseOccurrence]]
    exact hmem
  rcases hchunkReads with ⟨h9c, h10c, h11c⟩
  have h9 : WordRAM.TraceEvent.readWord 9 0 (some superWord) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
        0).trace := by
    apply liftRank
    have h := h9c
    rw [hsi] at h
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h
  have h10 : WordRAM.TraceEvent.readWord 10 0 (some blockWord) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
        0).trace := by
    apply liftRank
    have h := h10c
    rw [hwi] at h
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h
  have h11 : WordRAM.TraceEvent.readWord 11 0 (some wordBits) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
        0).trace := by
    apply liftRank
    have h := h11c
    rw [hwi] at h
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h
  have h12 : WordRAM.TraceEvent.readWord 12 0 (some word12) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore reviewerLongShape)
        (SuccinctClose.bpFringeChunkBits reviewerLongShape.bpCode.length)
        0).trace := by
    apply liftRelative
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h12mem
  exact ⟨⟨superWord, h9⟩, ⟨blockWord, h10⟩, ⟨wordBits, h11⟩,
    ⟨word12, h12⟩⟩

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

/- The closing theorem is proved below after the symbolic long-super route
lemmas. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_long_successful_closed_valid_occurrence
    (source : ReviewerSource)
    (hsource : source ∈
      [.selectLongFlagRankSuperTrue, .selectLongFlagRankBlockTrue,
        .selectLongFlagBits, .selectLongRelative]) :
    source.HasSuccessfulClosedValidOccurrence := by
  rcases reviewerLongSelect_successful_reads with
    ⟨⟨word9, h9⟩, ⟨word10, h10⟩, ⟨word11, h11⟩, ⟨word12, h12⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with h | h | h | h
  all_goals subst source
  · exact reviewerSource_successful_of_select_component_mem
      reviewerLongShape reviewerLongInput reviewerLongInput_shape
      reviewerLongInput_valid .selectLongFlagRankSuperTrue 9 word9 rfl h9
  · exact reviewerSource_successful_of_select_component_mem
      reviewerLongShape reviewerLongInput reviewerLongInput_shape
      reviewerLongInput_valid .selectLongFlagRankBlockTrue 10 word10 rfl h10
  · exact reviewerSource_successful_of_select_component_mem
      reviewerLongShape reviewerLongInput reviewerLongInput_shape
      reviewerLongInput_valid .selectLongFlagBits 11 word11 rfl h11
  · exact reviewerSource_successful_of_select_component_mem
      reviewerLongShape reviewerLongInput reviewerLongInput_shape
      reviewerLongInput_valid .selectLongRelative 12 word12 rfl h12

end SuccinctFinal

end RMQ

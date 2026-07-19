import RMQ.Core.SuccinctFinalStoreParam

/-!
# Whole-query answer dependency on a consumed charged read

This module gives the concrete answer-projection witness required by
`INV-B4-VALUE-DEPENDENCY`.  The ordinary query is the valid singleton range
`[7][0:1]`.  Its supplied store changes exactly logical cell `(21, 3)`, from
the canonical five-bit little-endian word for `1` to the word for `4`.
-/

namespace RMQ
namespace SuccinctFinal

private def singletonAnswerDependencyInput : List Int := [7]

private abbrev singletonAnswerDependencyShape : Cartesian.CartesianShape :=
  Cartesian.shape singletonAnswerDependencyInput

def concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore :
    WordRAM.ReadStore where
  readWord? segment index :=
    if segment = concreteBPNativeFringeChunkTraceSegment && index = 3 then
      some [false, false, true, false, false]
    else
      (concreteBPNativeSuccinctRMQGlobalReadStore
        singletonAnswerDependencyShape).readWord? segment index

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
    {segment index : Nat}
    (hne : segment ≠ concreteBPNativeFringeChunkTraceSegment ∨ index ≠ 3) :
    concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore.readWord?
        segment index =
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape ([7] : List Int))).readWord? segment index := by
  rcases hne with hne | hne <;>
    simp [concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore, hne,
      singletonAnswerDependencyShape, singletonAnswerDependencyInput]

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_changed :
    concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore.readWord?
        concreteBPNativeFringeChunkTraceSegment 3 =
      some [false, false, true, false, false] := by
  simp [concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore]

private theorem singletonAnswerDependencyShape_eq :
    singletonAnswerDependencyShape = .node .empty .empty := by
  simp [singletonAnswerDependencyShape, singletonAnswerDependencyInput,
    Cartesian.shape, Cartesian.shapeRange, scanWindow]

private abbrev candidateStore : WordRAM.ReadStore :=
  concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore

private theorem singletonAnswerDependency_bpCode :
    singletonAnswerDependencyShape.bpCode = [true, false] := by
  rw [singletonAnswerDependencyShape_eq]
  rfl

private theorem singletonAnswerDependency_log2_two : Nat.log2 2 = 1 := by
  apply Nat.le_antisymm
  · by_cases hle : Nat.log2 2 ≤ 1
    · exact hle
    have htwo : 2 ≤ Nat.log2 2 := by omega
    have hmono : 2 ^ 2 ≤ 2 ^ Nat.log2 2 :=
      Nat.pow_le_pow_right (by omega) htwo
    have hself : 2 ^ Nat.log2 2 ≤ 2 :=
      Nat.log2_self_le (by omega)
    omega
  · exact (Nat.le_log2 (n := 2) (by omega)).2 (by omega)

private theorem singletonAnswerDependency_chunkBits :
    SuccinctClose.bpFringeChunkBits
      singletonAnswerDependencyShape.bpCode.length = 1 := by
  rw [singletonAnswerDependency_bpCode]
  simp [SuccinctClose.bpFringeChunkBits,
    singletonAnswerDependency_log2_two]

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_canonical_cell :
    (concreteBPNativeSuccinctRMQGlobalReadStore
      (Cartesian.shape ([7] : List Int))).readWord?
        concreteBPNativeFringeChunkTraceSegment 3 =
      some [true, false, false, false, false] := by
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
  rw [show SuccinctClose.bpFringeChunkBits
      (Cartesian.shape ([7] : List Int)).bpCode.length = 1 by
    simpa [singletonAnswerDependencyShape, singletonAnswerDependencyInput] using
      singletonAnswerDependency_chunkBits]
  simp [SuccinctClose.bpFringeChunkTable,
    SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords,
    SuccinctClose.bpFringeChunkEntries,
    SuccinctClose.bpFringeChunkEntryWidth,
    SuccinctClose.bpFringeChunkEntryBound,
    SuccinctSpace.natToBitsLE]
  refine ⟨3, by decide, by decide, ?_⟩
  have hlog : Nat.log2 24 = 4 := by
    apply Nat.le_antisymm
    · by_cases hle : Nat.log2 24 ≤ 4
      · exact hle
      have hfive : 5 ≤ Nat.log2 24 := by omega
      have hmono : 2 ^ 5 ≤ 2 ^ Nat.log2 24 :=
        Nat.pow_le_pow_right (by omega) hfive
      have hself : 2 ^ Nat.log2 24 ≤ 24 :=
        Nat.log2_self_le (by omega)
      omega
    · exact (Nat.le_log2 (n := 24) (by omega)).2 (by omega)
  rw [hlog]
  decide

private theorem candidateStore_read_three :
    candidateStore.readWord? concreteBPNativeFringeChunkTraceSegment 3 =
      some [false, false, true, false, false] := by
  exact concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_changed

private theorem candidateStore_chunkRead_seven :
    (SuccinctClose.bpChunkReadTraceResult candidateStore
      concreteBPNativeFringeChunkTraceSegment 7).value = some 21 := by
  have hentry : (SuccinctClose.bpFringeChunkEntries 1)[7]? = some 21 := by
    decide
  have hread :=
    SuccinctSpace.FixedWidthNatTable.readCosted_erase
      (SuccinctClose.bpFringeChunkTable 1) 7
  rw [hentry] at hread
  have hdecoded :
      ((SuccinctClose.bpFringeChunkTable 1).store.words[7]?).map
          SuccinctSpace.bitsToNatLE = some 21 := by
    simpa [Costed.erase, SuccinctSpace.FixedWidthNatTable.readCosted] using hread
  unfold SuccinctClose.bpChunkReadTraceResult
  change (candidateStore.readWord?
      concreteBPNativeFringeChunkTraceSegment 7).map
        SuccinctSpace.bitsToNatLE = some 21
  rw [show candidateStore.readWord?
      concreteBPNativeFringeChunkTraceSegment 7 =
        (concreteBPNativeSuccinctRMQGlobalReadStore
          singletonAnswerDependencyShape).readWord?
            concreteBPNativeFringeChunkTraceSegment 7 by
      exact
        concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
          (Or.inr (by decide))]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
  rw [singletonAnswerDependency_chunkBits]
  exact hdecoded

private theorem candidateStore_chunkRead_three :
    (SuccinctClose.bpChunkReadTraceResult candidateStore
      concreteBPNativeFringeChunkTraceSegment 3).value = some 4 := by
  simp [SuccinctClose.bpChunkReadTraceResult, candidateStore_read_three,
    SuccinctSpace.bitsToNatLE, SuccinctSpace.bitToNat]

private theorem candidateStore_rank_before :
    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
      candidateStore concreteBPNativeFringeChunkTraceSegment 1 false
      [true, false] 1).value = 0 := by
  change (SuccinctClose.bpChunkedWordRankTraceFromWithStore candidateStore
    concreteBPNativeFringeChunkTraceSegment 1 false [true, false]
    1 0 1 0).value = 0
  unfold SuccinctClose.bpChunkedWordRankTraceFromWithStore
  rw [show SuccinctClose.bpFringeChunkSlot 1
      (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
      (SuccinctClose.bpWordChunkSliceLen 1 1 0)
      (SuccinctClose.bpWordChunkSliceLen 1 1 0) = 7 by decide]
  rw [WordRAM.TraceResult.bind_value]
  rw [candidateStore_chunkRead_seven]
  rfl

private theorem candidateStore_rank_upto :
    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
      candidateStore concreteBPNativeFringeChunkTraceSegment 1 false
      [true, false] 2).value = 0 := by
  change (SuccinctClose.bpChunkedWordRankTraceFromWithStore candidateStore
    concreteBPNativeFringeChunkTraceSegment 1 false [true, false]
    2 0 2 0).value = 0
  unfold SuccinctClose.bpChunkedWordRankTraceFromWithStore
  rw [show SuccinctClose.bpFringeChunkSlot 1
      (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
      (SuccinctClose.bpWordChunkSliceLen 1 2 0)
      (SuccinctClose.bpWordChunkSliceLen 1 2 0) = 7 by decide]
  rw [WordRAM.TraceResult.bind_value]
  rw [candidateStore_chunkRead_seven]
  change (SuccinctClose.bpChunkedWordRankTraceFromWithStore candidateStore
    concreteBPNativeFringeChunkTraceSegment 1 false [true, false]
    2 1 1 0).value = 0
  unfold SuccinctClose.bpChunkedWordRankTraceFromWithStore
  rw [show SuccinctClose.bpFringeChunkSlot 1
      (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
      (SuccinctClose.bpWordChunkSliceLen 1 2 1)
      (SuccinctClose.bpWordChunkSliceLen 1 2 1) = 3 by decide]
  rw [WordRAM.TraceResult.bind_value]
  rw [candidateStore_chunkRead_three]
  rfl

private theorem candidateStore_bpWord_zero :
    candidateStore.readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase 0 =
      some [true, false] := by
  change candidateStore.readWord? 0 0 = some [true, false]
  rw [show candidateStore.readWord? 0 0 =
      (concreteBPNativeSuccinctRMQGlobalReadStore
        singletonAnswerDependencyShape).readWord? 0 0 by
    exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
        (Or.inl (by decide))]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
  rw [singletonAnswerDependency_bpCode]
  simp [SuccinctSpace.chunkPayloadWords,
    SuccinctSpace.chunkPayloadWordsFuel,
    SuccinctRank.machineWordBits, singletonAnswerDependency_log2_two]

private theorem candidateStore_bpWord_one :
    candidateStore.readWord?
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase 1 = none := by
  change candidateStore.readWord? 0 1 = none
  rw [show candidateStore.readWord? 0 1 =
      (concreteBPNativeSuccinctRMQGlobalReadStore
        singletonAnswerDependencyShape).readWord? 0 1 by
    exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
        (Or.inl (by decide))]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
  rw [singletonAnswerDependency_bpCode]
  simp [SuccinctSpace.chunkPayloadWords,
    SuccinctSpace.chunkPayloadWordsFuel,
    SuccinctRank.machineWordBits, singletonAnswerDependency_log2_two]

private theorem singletonAnswerDependency_wordSize :
    (GenericSelect.sparseExceptionSelectData
      singletonAnswerDependencyShape.bpCode false).wordSize = 2 := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.sparseExceptionSelectData, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, singletonAnswerDependency_log2_two]

private theorem candidateStore_denseSelect_value :
    (GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment 1 false
      (GenericSelect.sparseExceptionSelectData
        singletonAnswerDependencyShape.bpCode false).bitWords
      candidateStore 1 0 0).value = none := by
  unfold GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
  rw [WordRAM.TraceResult.bind_value]
  simp only [singletonAnswerDependency_wordSize]
  rw [show (SuccinctClose.bpWordReadTraceResult candidateStore
      concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase 0).value =
        some [true, false] by
      simpa [SuccinctClose.bpWordReadTraceResult] using
        candidateStore_bpWord_zero]
  rw [WordRAM.TraceResult.bind_value]
  rw [candidateStore_rank_before]
  rw [WordRAM.TraceResult.bind_value]
  simp only [List.length_cons, List.length_nil]
  rw [candidateStore_rank_upto]
  rw [if_neg (by omega)]
  rw [WordRAM.TraceResult.bind_value]
  rw [show (SuccinctClose.bpWordReadTraceResult candidateStore
      concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase 1).value =
        none by
      simpa [SuccinctClose.bpWordReadTraceResult] using
        candidateStore_bpWord_one]
  rfl

private theorem denseEntryTable_trace_value
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    (table.readTraceResultRelabeled layout i).value = entries[i]? := by
  have hrefine := table.readTraceResultRelabeled_refines_interpretedCosted
    layout i
  calc
    (table.readTraceResultRelabeled layout i).value =
        (table.readInterpretedCosted i).value := by
      simpa [WordRAM.TraceResult.toCosted] using
        congrArg Costed.value hrefine
    _ = entries[i]? := by
      simpa [Costed.erase] using table.readInterpretedCosted_erase i

private theorem candidateStore_pullback_eq_global
    {base dead : Nat}
    (hbase : base ≠ concreteBPNativeFringeChunkTraceSegment)
    (hdead : dead ≠ concreteBPNativeFringeChunkTraceSegment) :
    candidateStore.pullback (WordRAM.singletonSegmentMap base dead) =
      (concreteBPNativeSuccinctRMQGlobalReadStore
        singletonAnswerDependencyShape).pullback
          (WordRAM.singletonSegmentMap base dead) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment
  · exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
        (Or.inl hbase)
  · exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
        (Or.inl hdead)

private theorem candidateSuperTableWithStore_eq (slot : Nat) :
    (GenericSelect.sparseExceptionSelectData
        singletonAnswerDependencyShape.bpCode false).superTable.readTraceResultRelabeledWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        candidateStore slot =
    (GenericSelect.sparseExceptionSelectData
        singletonAnswerDependencyShape.bpCode false).superTable.readTraceResultRelabeled
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable slot := by
  apply (GenericSelect.sparseExceptionSelectData
      singletonAnswerDependencyShape.bpCode false).superTable.readTraceResultRelabeledWithStore_eq_of_pullback
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseOccurrence
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseWordIndex
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superRankBefore
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superFirstOffset
        singletonAnswerDependencyShape)

private theorem candidateLocalTableWithStore_eq (slot : Nat) :
    (GenericSelect.sparseExceptionSelectData
        singletonAnswerDependencyShape.bpCode false).localTable.readTraceResultRelabeledWithStore
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        candidateStore slot =
    (GenericSelect.sparseExceptionSelectData
        singletonAnswerDependencyShape.bpCode false).localTable.readTraceResultRelabeled
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable slot := by
  apply (GenericSelect.sparseExceptionSelectData
      singletonAnswerDependencyShape.bpCode false).localTable.readTraceResultRelabeledWithStore_eq_of_pullback
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseOccurrence
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseWordIndex
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localRankBefore
        singletonAnswerDependencyShape)
  · exact (candidateStore_pullback_eq_global (by decide) (by decide)).trans
      (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localFirstOffset
        singletonAnswerDependencyShape)

private theorem singletonAnswerDependency_super_slot_exists :
    0 < GenericSelect.superSlotCount
      singletonAnswerDependencyShape.bpCode false := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.superSlotCount, GenericSelect.selectCeilDiv,
    GenericSelect.occurrenceCount, Succinct.rankPrefix,
    GenericSelect.superStride, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, singletonAnswerDependency_log2_two]

private theorem singletonAnswerDependency_local_slot_exists :
    0 < GenericSelect.localSlotCount
      singletonAnswerDependencyShape.bpCode false := by
  unfold GenericSelect.localSlotCount
  exact Nat.mul_pos singletonAnswerDependency_super_slot_exists
    (GenericSelect.localSlotsPerSuper_pos _)

private theorem singletonAnswerDependency_super_not_marked :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.superEntry
        singletonAnswerDependencyShape.bpCode false 0) = false := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.relativeSplitSelectEntryIsMarked,
    GenericSelect.superEntry, GenericSelect.superIsLong,
    GenericSelect.superLongSpan, GenericSelect.superSpan,
    GenericSelect.superEndOccurrence, GenericSelect.superBaseOccurrence,
    GenericSelect.position, GenericSelect.occurrenceCount,
    GenericSelect.superStride, GenericSelect.ell,
    GenericSelect.wordBits, SuccinctRank.machineWordBits,
    Succinct.rankPrefix, Succinct.select, Succinct.selectFrom,
    singletonAnswerDependency_log2_two]

private theorem singletonAnswerDependency_local_not_marked :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.localEntry
        singletonAnswerDependencyShape.bpCode false 0) = false := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.relativeSplitSelectEntryIsMarked,
    GenericSelect.localEntry, GenericSelect.compactLocalEntryIsLive,
    GenericSelect.localIsSparseException,
    GenericSelect.shortSuperLocalSpan,
    GenericSelect.shortSuperLocalEndOccurrence,
    GenericSelect.localBaseOccurrence,
    GenericSelect.localSlotInSuperOfGlobal,
    GenericSelect.localSuperSlot, GenericSelect.superEndOccurrence,
    GenericSelect.superBaseOccurrence, GenericSelect.superIsLong,
    GenericSelect.superSpan, GenericSelect.superLongSpan,
    GenericSelect.position, GenericSelect.occurrenceCount,
    GenericSelect.localSlotsPerSuper,
    GenericSelect.selectLocalSlotsPerSuper,
    GenericSelect.superStride, GenericSelect.localStride,
    GenericSelect.ell, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, Succinct.rankPrefix,
    Succinct.select, Succinct.selectFrom,
    singletonAnswerDependency_log2_two]

private theorem singletonAnswerDependency_dense_base_position :
    GenericSelect.relativeSplitSelectLocalBasePosition
        (GenericSelect.wordBits singletonAnswerDependencyShape.bpCode.length)
        (GenericSelect.superEntry
          singletonAnswerDependencyShape.bpCode false 0)
        (GenericSelect.localEntry
          singletonAnswerDependencyShape.bpCode false 0) = 1 := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.relativeSplitSelectLocalBasePosition,
    GenericSelect.superEntry, GenericSelect.localEntry,
    GenericSelect.compactLocalEntryIsLive,
    GenericSelect.localIsSparseException,
    GenericSelect.shortSuperLocalSpan,
    GenericSelect.shortSuperLocalEndOccurrence,
    GenericSelect.localBaseOccurrence,
    GenericSelect.localSlotInSuperOfGlobal,
    GenericSelect.localSuperSlot, GenericSelect.superEndOccurrence,
    GenericSelect.superBaseOccurrence, GenericSelect.superIsLong,
    GenericSelect.superSpan, GenericSelect.superLongSpan,
    GenericSelect.position, GenericSelect.occurrenceCount,
    GenericSelect.localSlotsPerSuper,
    GenericSelect.selectLocalSlotsPerSuper,
    GenericSelect.superStride, GenericSelect.localStride,
    GenericSelect.ell, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, Succinct.rankPrefix,
    Succinct.select, Succinct.selectFrom,
    singletonAnswerDependency_log2_two]

private theorem singletonAnswerDependency_dense_base_occurrence :
    GenericSelect.relativeSplitSelectLocalBaseOccurrence
        (GenericSelect.superEntry
          singletonAnswerDependencyShape.bpCode false 0)
        (GenericSelect.localEntry
          singletonAnswerDependencyShape.bpCode false 0) = 0 := by
  rw [singletonAnswerDependency_bpCode]
  simp [GenericSelect.relativeSplitSelectLocalBaseOccurrence,
    GenericSelect.superEntry, GenericSelect.localEntry,
    GenericSelect.compactLocalEntryIsLive,
    GenericSelect.localIsSparseException,
    GenericSelect.shortSuperLocalSpan,
    GenericSelect.shortSuperLocalEndOccurrence,
    GenericSelect.localBaseOccurrence,
    GenericSelect.localSlotInSuperOfGlobal,
    GenericSelect.localSuperSlot, GenericSelect.superEndOccurrence,
    GenericSelect.superBaseOccurrence, GenericSelect.superIsLong,
    GenericSelect.superSpan, GenericSelect.superLongSpan,
    GenericSelect.position, GenericSelect.occurrenceCount,
    GenericSelect.localSlotsPerSuper,
    GenericSelect.selectLocalSlotsPerSuper,
    GenericSelect.superStride, GenericSelect.localStride,
    GenericSelect.ell, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, Succinct.rankPrefix,
    Succinct.select, Succinct.selectFrom,
    singletonAnswerDependency_log2_two]

private theorem candidateStore_select_value :
    (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
      singletonAnswerDependencyShape candidateStore 0).value = none := by
  let data := GenericSelect.sparseExceptionSelectData
    singletonAnswerDependencyShape.bpCode false
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  let super := GenericSelect.superEntry
    singletonAnswerDependencyShape.bpCode false 0
  let loc := GenericSelect.localEntry
    singletonAnswerDependencyShape.bpCode false 0
  have hvalid :
      0 < GenericSelect.occurrenceCount
        singletonAnswerDependencyShape.bpCode false := by
    rw [singletonAnswerDependency_bpCode]
    simp [GenericSelect.occurrenceCount, Succinct.rankPrefix]
  have hsuperEntry : data.superEntries[0]? = some super := by
    change (GenericSelect.superEntries
      singletonAnswerDependencyShape.bpCode false)[0]? =
        some (GenericSelect.superEntry
          singletonAnswerDependencyShape.bpCode false 0)
    exact GenericSelect.superEntries_get?
      singletonAnswerDependencyShape.bpCode false
      singletonAnswerDependency_super_slot_exists
  have hlocalEntry : data.localEntries[0]? = some loc := by
    change (GenericSelect.localEntries
      singletonAnswerDependencyShape.bpCode false)[0]? =
        some (GenericSelect.localEntry
          singletonAnswerDependencyShape.bpCode false 0)
    exact GenericSelect.localEntries_get?
      singletonAnswerDependencyShape.bpCode false
      singletonAnswerDependency_local_slot_exists
  have hsuperSlot :
      GenericSelect.selectSuperSlot (data.queryOccurrence 0)
        data.superStride = 0 := by
    simp [data, GenericSelect.sparseExceptionSelectData,
      GenericSelect.SparseExceptionSelectData.queryOccurrence,
      GenericSelect.selectSuperSlot]
  have hlocalSlot :
      GenericSelect.relativeSplitSelectLocalSlot
        (data.queryOccurrence 0) data.superStride
        data.localSlotsPerSuper data.localStride super = 0 := by
    simp [data, super, GenericSelect.sparseExceptionSelectData,
      GenericSelect.SparseExceptionSelectData.queryOccurrence,
      GenericSelect.relativeSplitSelectLocalSlot,
      GenericSelect.relativeSplitSelectLocalSlotInSuper,
      GenericSelect.selectSuperSlot, GenericSelect.superEntry]
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        candidateStore
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [show data.superTable.readTraceResultRelabeledWithStore
        layout.superTable candidateStore
          (GenericSelect.selectSuperSlot
            (data.queryOccurrence 0) data.superStride) =
      data.superTable.readTraceResultRelabeled layout.superTable
          (GenericSelect.selectSuperSlot
            (data.queryOccurrence 0) data.superStride) by
        simpa [data, layout] using
          candidateSuperTableWithStore_eq
            (GenericSelect.selectSuperSlot
              (data.queryOccurrence 0) data.superStride)]
    rw [hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        candidateStore
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super)).value = some loc := by
    rw [show data.localTable.readTraceResultRelabeledWithStore
        layout.localTable candidateStore
          (GenericSelect.relativeSplitSelectLocalSlot
            (data.queryOccurrence 0) data.superStride
            data.localSlotsPerSuper data.localStride super) =
      data.localTable.readTraceResultRelabeled layout.localTable
          (GenericSelect.relativeSplitSelectLocalSlot
            (data.queryOccurrence 0) data.superStride
            data.localSlotsPerSuper data.localStride super) by
        simpa [data, layout] using
          candidateLocalTableWithStore_eq
            (GenericSelect.relativeSplitSelectLocalSlot
              (data.queryOccurrence 0) data.superStride
              data.localSlotsPerSuper data.localStride super)]
    rw [hlocalSlot]
    simpa [hlocalEntry] using
      denseEntryTable_trace_value data.localTable layout.localTable 0
  have hshort :
      GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
    simpa [super] using singletonAnswerDependency_super_not_marked
  have hdense :
      GenericSelect.relativeSplitSelectEntryIsMarked loc = false := by
    simpa [loc] using singletonAnswerDependency_local_not_marked
  have hbasePos :
      GenericSelect.relativeSplitSelectLocalBasePosition
        data.wordSize super loc = 1 := by
    simpa [data, super, loc, GenericSelect.sparseExceptionSelectData] using
      singletonAnswerDependency_dense_base_position
  have hbaseOcc :
      GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc = 0 := by
    simpa [super, loc] using
      singletonAnswerDependency_dense_base_occurrence
  have hq0 : data.queryOccurrence 0 = 0 := rfl
  have hcb : SuccinctClose.bpFringeChunkBits
      singletonAnswerDependencyShape.bpCode.length = 1 :=
    singletonAnswerDependency_chunkBits
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  change (data.bpChunkedSelectTraceResultWithStore layout
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment candidateStore
    (SuccinctClose.bpFringeChunkBits
      singletonAnswerDependencyShape.bpCode.length) 0).value = none
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  rw [if_pos hvalid, WordRAM.TraceResult.bind_value, hsuperValue]
  simp only [hshort, Bool.false_eq_true, ↓reduceIte]
  rw [WordRAM.TraceResult.bind_value, hlocalValue]
  simp only [hdense, Bool.false_eq_true, ↓reduceIte]
  rw [hbasePos, hbaseOcc, hq0, hcb]
  exact candidateStore_denseSelect_value

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependency_corrupt_value :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      (Cartesian.shape ([7] : List Int))
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore 0 1).value =
        none := by
  have hselect :
      (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        (Cartesian.shape ([7] : List Int))
        concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore 0).value =
          none := by
    simpa [candidateStore, singletonAnswerDependencyShape,
      singletonAnswerDependencyInput] using candidateStore_select_value
  simp [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore,
    concreteBPNativeSuccinctRMQWholeQueryProgram,
    WholeQueryProgram.evalGlobalWordTraceWithStore,
    WholeQueryInstr.evalGlobalWordTraceWithStore,
    WholeQueryNatExpr.eval, hselect,
    WholeQueryState.empty, WholeQueryState.setOpt, WholeQueryState.opt,
    WholeQueryState.setNat, WholeQueryState.nat]

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_value :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      (Cartesian.shape ([7] : List Int))
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape ([7] : List Int))) 0 1).value = some 0 := by
  have hshape :
      Cartesian.shape ([7] : List Int) ∈ Cartesian.shapesOfSize 1 := by
    rw [show Cartesian.shape ([7] : List Int) = .node .empty .empty by
      simpa [singletonAnswerDependencyShape,
        singletonAnswerDependencyInput] using singletonAnswerDependencyShape_eq]
    exact Cartesian.shapeOfSize_mem_shapesOfSize
      (.node .empty .empty)
  have hexact :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_exact
      hshape (left := 0) (len := 1) (by omega) (by omega)
  simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore,
    WordRAM.TraceResult.toCosted, Costed.erase,
    Cartesian.CartesianShape.representative, scanWindow, betterIndex] using
      hexact

theorem concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_consumed :
    ∃ globalPos : Nat,
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape ([7] : List Int))
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape ([7] : List Int))) 0 1).trace[globalPos]? =
        some (WordRAM.TraceEvent.readWord
          concreteBPNativeFringeChunkTraceSegment 3
          (some [true, false, false, false, false])) := by
  let shape := Cartesian.shape ([7] : List Int)
  let canonical := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let corrupt := concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore
  have hcanonical :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape canonical 0 1).value = some 0 := by
    simpa [shape, canonical] using
      concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_value
  have hcorrupt :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape corrupt 0 1).value = none := by
    simpa [shape, corrupt, singletonAnswerDependencyShape,
      singletonAnswerDependencyInput] using
      concreteBPNativeSuccinctRMQSingletonAnswerDependency_corrupt_value
  have hfoot :
      (concreteBPNativeFringeChunkTraceSegment, 3) ∈
        concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
          shape canonical 0 1 := by
    by_cases hpresent :
        (concreteBPNativeFringeChunkTraceSegment, 3) ∈
          concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
            shape canonical 0 1
    · exact hpresent
    · have hagree :
          concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
            shape canonical corrupt 0 1 := by
        intro segment index hmem
        by_cases hsegment : segment = concreteBPNativeFringeChunkTraceSegment
        · subst segment
          by_cases hindex : index = 3
          · subst index
            exact False.elim (hpresent hmem)
          · exact
              (concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
                (Or.inr hindex)).symm
        · exact
            (concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
              (Or.inl hsegment)).symm
      have heq :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
          shape canonical corrupt 0 1 hagree
      have hvalue := congrArg (fun result => result.value) heq
      change
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape canonical 0 1).value =
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape corrupt 0 1).value at hvalue
      rw [hcanonical, hcorrupt] at hvalue
      cases hvalue
  simp only [
    concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore,
    List.mem_filterMap] at hfoot
  rcases hfoot with ⟨event, hevent, hproject⟩
  cases event with
  | readWord segment index word? =>
      simp at hproject
      rcases hproject with ⟨rfl, rfl⟩
      have hmatches :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
          shape canonical 0 1
          (WordRAM.TraceEvent.readWord
            concreteBPNativeFringeChunkTraceSegment 3 word?) hevent
      have hword : word? = some [true, false, false, false, false] := by
        exact hmatches.symm.trans (by
          simpa [shape, canonical, singletonAnswerDependencyShape,
            singletonAnswerDependencyInput] using
            concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_canonical_cell)
      rw [hword] at hevent
      simpa [shape, canonical] using List.mem_iff_getElem?.mp hevent
  | wordRank target limit result => simp at hproject
  | wordSelect target occurrence result => simp at hproject
  | syntheticCostOnlyPrimitive => simp at hproject

/--
Answer-level charged-read dependency for one valid ordinary query.  The
canonical execution consumes the successful read of logical cell `(21,3)`;
changing only that cell from LE1 to LE4 changes the whole-query `Option Nat`
answer from `some 0` to `none`.
-/
theorem concreteBPNativeSuccinctRMQSingletonAnswerDependency_value_ne :
    ∃ (xs : List Int) (globalPos : Nat),
      xs = [7] ∧
      ValidRange xs 0 1 ∧
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape xs)).readWord?
          concreteBPNativeFringeChunkTraceSegment 3 =
        some [true, false, false, false, false] ∧
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore.readWord?
          concreteBPNativeFringeChunkTraceSegment 3 =
        some [false, false, true, false, false] ∧
      (∀ segment index,
        segment ≠ concreteBPNativeFringeChunkTraceSegment ∨ index ≠ 3 →
          concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore.readWord?
              segment index =
            (concreteBPNativeSuccinctRMQGlobalReadStore
              (Cartesian.shape xs)).readWord? segment index) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs)
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape xs)) 0 1).trace[globalPos]? =
        some (WordRAM.TraceEvent.readWord
          concreteBPNativeFringeChunkTraceSegment 3
          (some [true, false, false, false, false])) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs)
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape xs)) 0 1).value = some 0 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs)
        concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore 0 1).value =
          none ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs)
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape xs)) 0 1).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs)
        concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore 0 1).value := by
  rcases
      concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_consumed with
    ⟨globalPos, hconsumed⟩
  refine ⟨[7], globalPos, rfl, ?_, ?_, ?_, ?_, hconsumed, ?_, ?_, ?_⟩
  · simp [ValidRange]
  · exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_canonical_cell
  · exact concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_changed
  · intro segment index hne
    exact
      concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere
        hne
  · exact concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_value
  · exact concreteBPNativeSuccinctRMQSingletonAnswerDependency_corrupt_value
  · intro heq
    rw [concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_value,
      concreteBPNativeSuccinctRMQSingletonAnswerDependency_corrupt_value] at heq
    cases heq


end SuccinctFinal
end RMQ

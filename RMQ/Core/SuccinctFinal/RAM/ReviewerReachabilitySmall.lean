import RMQ.Core.SuccinctFinalRAM

/-!
# Small closed-valid reviewer-source reachability witnesses

This module records concrete successful top-level executions for the reviewer
sources exercised by the singleton query and by the canonical-close interior
query on an increasing list of length sixteen.  Every witness starts from a
global `getElem?` occurrence and is discharged through the indexed producer
receipt, so no component-only may-read path or arbitrary machine state is used.
-/

namespace RMQ
namespace SuccinctFinal

private theorem reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
    (source : ReviewerSource) (xs : List Int)
    (left right segment index : Nat) (word : WordRAM.Word)
    (hvalid : ValidRange xs left right)
    (hsource :
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source)
    (hmem :
      .readWord segment index (some word) ∈
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          (Cartesian.shape xs) left right).trace) :
    source.HasSuccessfulClosedValidOccurrence := by
  rcases List.mem_iff_getElem?.mp hmem with ⟨globalPos, hget⟩
  rcases
      concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
        (Cartesian.shape xs) left right hget with
    ⟨receiptSource, instrPos, instr, preState, localPos, invocation,
      hproducer, _hreceiptSource, _hregion, hinvocation, hcomponent,
      _hpath, _hcounted⟩
  refine ⟨⟨segment, invocation.leaf⟩, hsource, word, ?_⟩
  exact ⟨xs, left, right, globalPos, index, hvalid, hget,
    instrPos, instr, preState, localPos, invocation,
    hproducer, hinvocation, rfl, hcomponent⟩

private theorem evalGlobalWordTrace_append_trace
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (before after : WholeQueryProgram) (state : WholeQueryState) :
    (WholeQueryProgram.evalGlobalWordTrace shape left right
      (before ++ after) state).trace =
      (WholeQueryProgram.evalGlobalWordTrace shape left right before state).trace ++
        (WholeQueryProgram.evalGlobalWordTrace shape left right after
          (WholeQueryProgram.evalGlobalWordTrace
            shape left right before state).value).trace := by
  induction before generalizing state with
  | nil => simp [WholeQueryProgram.evalGlobalWordTrace]
  | cons first rest ih =>
      simp only [List.cons_append, WholeQueryProgram.evalGlobalWordTrace,
        WordRAM.TraceResult.bind_trace, WordRAM.TraceResult.bind_value]
      rw [ih]
      simp [List.append_assoc]

private theorem WholeQueryProgram.ProducesEventAt.global_getElem
    {shape : Cartesian.CartesianShape} {left right : Nat}
    {event : WordRAM.TraceEvent} {program : WholeQueryProgram}
    {state : WholeQueryState} {globalPos instrPos : Nat}
    {instr : WholeQueryInstr} {preState : WholeQueryState}
    {localPos : Nat}
    (hproducer : ProducesEventAt shape left right event program state globalPos
      instrPos instr preState localPos) :
    (evalGlobalWordTrace shape left right program state).trace[globalPos]? =
      some event := by
  rcases hproducer with
    ⟨before, after, hprogram, _hinstrPos, hpreState, hglobalPos,
      hlocal⟩
  have hlocalLt : localPos <
      (instr.evalGlobalWordTrace shape left right preState).trace.length :=
    (List.getElem?_eq_some_iff.mp hlocal).1
  rw [hprogram, evalGlobalWordTrace_append_trace]
  rw [hglobalPos]
  simp only [List.getElem?_append]
  simp
  rw [← hpreState]
  simp only [evalGlobalWordTrace, WordRAM.TraceResult.bind_trace]
  simpa [List.getElem?_append, hlocalLt] using hlocal

private theorem reviewerClaim_successful_of_local_get
    (xs : List Int) (left right segment index : Nat) (word : WordRAM.Word)
    (leaf : ReviewerReadLeaf)
    (before after : WholeQueryProgram) (instr : WholeQueryInstr)
    (preState : WholeQueryState) (localPos : Nat)
    (invocation : ReviewerReadInvocation)
    (hvalid : ValidRange xs left right)
    (hprogram : concreteBPNativeSuccinctRMQWholeQueryProgram =
      before ++ instr :: after)
    (hpreState : preState =
      (WholeQueryProgram.evalGlobalWordTrace
        (Cartesian.shape xs) left right before WholeQueryState.empty).value)
    (hlocal :
      (instr.evalGlobalWordTrace
        (Cartesian.shape xs) left right preState).trace[localPos]? =
          some (.readWord segment index (some word)))
    (hinvocation : instr.InvokesReviewerRead left right preState invocation)
    (hleaf : invocation.leaf = leaf)
    (hcomponent :
      (invocation.componentTrace (Cartesian.shape xs))[localPos]? =
        some (.readWord segment index (some word))) :
    (ReviewerProducerClaim.mk segment leaf).HasSuccessfulClosedValidOccurrence := by
  let globalPos :=
    (WholeQueryProgram.evalGlobalWordTrace
      (Cartesian.shape xs) left right before WholeQueryState.empty).trace.length +
      localPos
  have hproducer :
      WholeQueryProgram.ProducesEventAt
        (Cartesian.shape xs) left right
        (.readWord segment index (some word))
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        globalPos before.length instr preState localPos := by
    exact ⟨before, after, hprogram, rfl, hpreState, rfl, hlocal⟩
  have hprogramGet := hproducer.global_getElem
  have hglobalGet :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[globalPos]? =
          some (.readWord segment index (some word)) := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using
      hprogramGet
  refine ⟨word, xs, left, right, globalPos, index, hvalid, hglobalGet,
    before.length, instr, preState, localPos, invocation, hproducer,
    hinvocation, hleaf, hcomponent⟩

private def reviewerSingletonInput : List Int := [7]

private def reviewerIncreasingSixteenInput : List Int :=
  (List.range 16).map Int.ofNat

private def reviewerRightSpine : Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (reviewerRightSpine n)

private theorem reviewerIncreasingSixteenInput_shape :
    Cartesian.shape reviewerIncreasingSixteenInput = reviewerRightSpine 16 := by
  simp [reviewerIncreasingSixteenInput, reviewerRightSpine, Cartesian.shape,
    Cartesian.shapeRange, scanWindow, betterIndex]

private theorem fixedWidthNatTable_word_of_entry
    {entries : List Nat} {width entry : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (i : Nat) (hentry : entries[i]? = some entry) :
    ∃ word, table.store.words[i]? = some word := by
  have hread := table.read_exact i
  rw [hentry] at hread
  cases hword : table.store.words[i]? with
  | none => simp [hword] at hread
  | some word => exact ⟨word, rfl⟩

private theorem reviewerFixedWidthMachineChunkCount_pos
    {width wordSize : Nat} (hwidth : 0 < width) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize := by
  by_cases hmod : width % wordSize = 0
  · have hdecomp := Nat.mod_add_div width wordSize
    have hdiv : width / wordSize ≠ 0 := by
      intro hzero
      simp [hmod, hzero] at hdecomp
      omega
    simpa [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hmod] using
      Nat.pos_of_ne_zero hdiv
  · simp [SuccinctSpace.fixedWidthNatTableMachineChunkCount, hmod]

private theorem denseEntryTable_successful_field_reads
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    {entry : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (hentry : entries[0]? = some entry) :
    (∃ word, .readWord layout.baseOccurrence 0 (some word) ∈
      (table.readTraceResultRelabeled layout 0).trace) ∧
    (∃ word, .readWord layout.baseWordIndex 0 (some word) ∈
      (table.readTraceResultRelabeled layout 0).trace) ∧
    (∃ word, .readWord layout.rankBefore 0 (some word) ∈
      (table.readTraceResultRelabeled layout 0).trace) ∧
    (∃ word, .readWord layout.firstOffset 0 (some word) ∈
      (table.readTraceResultRelabeled layout 0).trace) := by
  have hbase :
      (GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences
        entries)[0]? = some entry.baseOccurrence := by
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
      List.getElem?_map] using
      congrArg (Option.map fun value :
        GenericSelect.SparseDenseSelectDenseLocalEntry =>
          value.baseOccurrence) hentry
  have hwordIndex :
      (GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices
        entries)[0]? = some entry.baseWordIndex := by
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices,
      List.getElem?_map] using
      congrArg (Option.map fun value :
        GenericSelect.SparseDenseSelectDenseLocalEntry =>
          value.baseWordIndex) hentry
  have hrank :
      (GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore
        entries)[0]? = some entry.rankBefore := by
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore,
      List.getElem?_map] using
      congrArg (Option.map fun value :
        GenericSelect.SparseDenseSelectDenseLocalEntry =>
          value.rankBefore) hentry
  have hoffset :
      (GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets
        entries)[0]? = some entry.firstOffset := by
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
      List.getElem?_map] using
      congrArg (Option.map fun value :
        GenericSelect.SparseDenseSelectDenseLocalEntry =>
          value.firstOffset) hentry
  rcases fixedWidthNatTable_word_of_entry
      table.baseOccurrenceTable 0 hbase with ⟨word1, hword1⟩
  rcases fixedWidthNatTable_word_of_entry
      table.baseWordIndexTable 0 hwordIndex with ⟨word2, hword2⟩
  rcases fixedWidthNatTable_word_of_entry
      table.rankBeforeTable 0 hrank with ⟨word3, hword3⟩
  rcases fixedWidthNatTable_word_of_entry
      table.firstOffsetTable 0 hoffset with ⟨word4, hword4⟩
  refine ⟨⟨word1, ?_⟩, ⟨word2, ?_⟩, ⟨word3, ?_⟩,
    ⟨word4, ?_⟩⟩
  all_goals
    simp [GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeled,
      SuccinctSpace.FixedWidthNatTable.readProgram,
      SuccinctSpace.PayloadWordStore.readProgram,
      WordRAM.Program.eval, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.map, WordRAM.TraceResult.pure,
      WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore_readWord?_zero,
      hword1, hword2, hword3, hword4]

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

private theorem reviewerSingletonInput_shape :
    Cartesian.shape reviewerSingletonInput = .node .empty .empty := by
  simp [reviewerSingletonInput, Cartesian.shape,
    Cartesian.shapeRange, scanWindow]

private theorem reviewerSingletonInput_bpCode :
    (Cartesian.shape reviewerSingletonInput).bpCode = [true, false] := by
  rw [reviewerSingletonInput_shape]
  rfl

private theorem reviewerSingleton_super_slot_exists :
    0 < GenericSelect.superSlotCount
      (Cartesian.shape reviewerSingletonInput).bpCode false := by
  rw [reviewerSingletonInput_bpCode]
  simp [GenericSelect.superSlotCount, GenericSelect.selectCeilDiv,
    GenericSelect.occurrenceCount, Succinct.rankPrefix,
    GenericSelect.superStride, GenericSelect.wordBits,
    SuccinctRank.machineWordBits]

private theorem reviewerSingleton_local_slot_exists :
    0 < GenericSelect.localSlotCount
      (Cartesian.shape reviewerSingletonInput).bpCode false := by
  unfold GenericSelect.localSlotCount
  exact Nat.mul_pos reviewerSingleton_super_slot_exists
    (GenericSelect.localSlotsPerSuper_pos _)

private theorem selectTrace_super_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).trace) :
    event ∈ (data.selectTraceResultRelabeled layout idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  exact Or.inl hmem

private theorem selectTrace_local_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value = some super)
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence idx) data.superStride
          data.localSlotsPerSuper data.localStride super)).trace) :
    event ∈ (data.selectTraceResultRelabeled layout idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hshort]
  exact Or.inl hmem

private theorem selectTrace_dense_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hsuper :
      (data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).value = some super)
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    (hlocal :
      (data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence idx) data.superStride
          data.localSlotsPerSuper data.localStride super)).value = some loc)
    (hdense : GenericSelect.relativeSplitSelectEntryIsMarked loc = false)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (GenericSelect.denseTwoWordSelectTraceResultRelabeled
        layout.bitWordBase layout.deadSegment target data.bitWords
        (GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc)
        (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
        (data.queryOccurrence idx)).trace) :
    event ∈ (data.selectTraceResultRelabeled layout idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeled
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hshort]
  apply Or.inr
  simpa [hlocal, hdense] using hmem

private theorem reviewerSingleton_log2_two : Nat.log2 2 = 1 := by
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

private theorem reviewer_log2_sixteen : Nat.log2 16 = 4 := by
  apply Nat.le_antisymm
  · by_cases hle : Nat.log2 16 ≤ 4
    · exact hle
    have hfive : 5 ≤ Nat.log2 16 := by omega
    have hmono : 2 ^ 5 ≤ 2 ^ Nat.log2 16 :=
      Nat.pow_le_pow_right (by omega) hfive
    have hself : 2 ^ Nat.log2 16 ≤ 16 :=
      Nat.log2_self_le (by omega)
    omega
  · exact (Nat.le_log2 (n := 16) (by omega)).2 (by omega)

private theorem reviewer_log2_twentyFive : Nat.log2 25 = 4 := by
  apply Nat.le_antisymm
  · by_cases hle : Nat.log2 25 ≤ 4
    · exact hle
    have hfive : 5 ≤ Nat.log2 25 := by omega
    have hmono : 2 ^ 5 ≤ 2 ^ Nat.log2 25 :=
      Nat.pow_le_pow_right (by omega) hfive
    have hself : 2 ^ Nat.log2 25 ≤ 25 :=
      Nat.log2_self_le (by omega)
    omega
  · exact (Nat.le_log2 (n := 25) (by omega)).2 (by omega)

private theorem reviewerSingleton_super_not_marked :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.superEntry
        (Cartesian.shape reviewerSingletonInput).bpCode false 0) = false := by
  rw [reviewerSingletonInput_bpCode]
  simp [GenericSelect.relativeSplitSelectEntryIsMarked,
    GenericSelect.superEntry, GenericSelect.superIsLong,
    GenericSelect.superLongSpan, GenericSelect.superSpan,
    GenericSelect.superEndOccurrence, GenericSelect.superBaseOccurrence,
    GenericSelect.position, GenericSelect.occurrenceCount,
    GenericSelect.superStride, GenericSelect.ell,
    GenericSelect.wordBits, SuccinctRank.machineWordBits,
    Succinct.rankPrefix, Succinct.select, Succinct.selectFrom,
    reviewerSingleton_log2_two]

private theorem reviewerSingleton_local_not_marked :
    GenericSelect.relativeSplitSelectEntryIsMarked
      (GenericSelect.localEntry
        (Cartesian.shape reviewerSingletonInput).bpCode false 0) = false := by
  rw [reviewerSingletonInput_bpCode]
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
    GenericSelect.position,
    GenericSelect.occurrenceCount,
    GenericSelect.localSlotsPerSuper,
    GenericSelect.selectLocalSlotsPerSuper,
    GenericSelect.superStride, GenericSelect.localStride,
    GenericSelect.ell, GenericSelect.wordBits,
    SuccinctRank.machineWordBits, Succinct.rankPrefix,
    Succinct.select, Succinct.selectFrom, reviewerSingleton_log2_two]

private theorem reviewerSingleton_dense_first_word_index :
    GenericSelect.relativeSplitSelectLocalBasePosition
        (GenericSelect.wordBits
          (Cartesian.shape reviewerSingletonInput).bpCode.length)
        (GenericSelect.superEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0)
        (GenericSelect.localEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0) /
      GenericSelect.wordBits
        (Cartesian.shape reviewerSingletonInput).bpCode.length = 0 := by
  rw [reviewerSingletonInput_bpCode]
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
    Succinct.select, Succinct.selectFrom, reviewerSingleton_log2_two]

private theorem reviewerSingleton_select_table_successful_reads :
    (∃ word, .readWord 1 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 2 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 3 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 4 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 5 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 6 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 7 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) ∧
    (∃ word, .readWord 8 0 (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) := by
  let shape := Cartesian.shape reviewerSingletonInput
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  let super := GenericSelect.superEntry shape.bpCode false 0
  let loc := GenericSelect.localEntry shape.bpCode false 0
  have hvalid : 0 < GenericSelect.occurrenceCount shape.bpCode false := by
    dsimp [shape]
    rw [reviewerSingletonInput_bpCode]
    simp [GenericSelect.occurrenceCount, Succinct.rankPrefix]
  have hsuperEntry : data.superEntries[0]? = some super := by
    change (GenericSelect.superEntries shape.bpCode false)[0]? =
      some (GenericSelect.superEntry shape.bpCode false 0)
    exact GenericSelect.superEntries_get? shape.bpCode false
      reviewerSingleton_super_slot_exists
  have hlocalEntry : data.localEntries[0]? = some loc := by
    change (GenericSelect.localEntries shape.bpCode false)[0]? =
      some (GenericSelect.localEntry shape.bpCode false 0)
    exact GenericSelect.localEntries_get? shape.bpCode false
      reviewerSingleton_local_slot_exists
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
      (data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hshort :
      GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
    simpa [super, shape] using reviewerSingleton_super_not_marked
  rcases denseEntryTable_successful_field_reads
      data.superTable layout.superTable hsuperEntry with
    ⟨⟨word1, h1⟩, ⟨word2, h2⟩, ⟨word3, h3⟩, ⟨word4, h4⟩⟩
  rcases denseEntryTable_successful_field_reads
      data.localTable layout.localTable hlocalEntry with
    ⟨⟨word5, h5⟩, ⟨word6, h6⟩, ⟨word7, h7⟩, ⟨word8, h8⟩⟩
  refine ⟨⟨word1, ?_⟩, ⟨word2, ?_⟩, ⟨word3, ?_⟩,
    ⟨word4, ?_⟩, ⟨word5, ?_⟩, ⟨word6, ?_⟩,
    ⟨word7, ?_⟩, ⟨word8, ?_⟩⟩
  · change .readWord 1 0 (some word1) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    apply selectTrace_super_read_mem data layout 0 hvalid
    rw [hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h1
  · change .readWord 2 0 (some word2) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    apply selectTrace_super_read_mem data layout 0 hvalid
    rw [hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h2
  · change .readWord 3 0 (some word3) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    apply selectTrace_super_read_mem data layout 0 hvalid
    rw [hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h3
  · change .readWord 4 0 (some word4) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    apply selectTrace_super_read_mem data layout 0 hvalid
    rw [hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h4
  · change .readWord 5 0 (some word5) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    exact selectTrace_local_read_mem data layout 0 hvalid super
      hsuperValue hshort (by
        rw [hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h5)
  · change .readWord 6 0 (some word6) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    exact selectTrace_local_read_mem data layout 0 hvalid super
      hsuperValue hshort (by
        rw [hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h6)
  · change .readWord 7 0 (some word7) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    exact selectTrace_local_read_mem data layout 0 hvalid super
      hsuperValue hshort (by
        rw [hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h7)
  · change .readWord 8 0 (some word8) ∈
      (data.selectTraceResultRelabeled layout 0).trace
    exact selectTrace_local_read_mem data layout 0 hvalid super
      hsuperValue hshort (by
        rw [hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h8)

private theorem firstSelectClose_read_mem_wholeQuery
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) :
    event ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0 1).trace := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  simp only [WordRAM.TraceResult.map_trace]
  change event ∈
    (WholeQueryProgram.evalGlobalWordTrace
      (Cartesian.shape reviewerSingletonInput) 0 1
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty).trace
  rw [show concreteBPNativeSuccinctRMQWholeQueryProgram =
    .selectClose .leftClose .inputLeft ::
      [ .selectClose .rightClose (.sub .inputRight (.const 1))
      , .lcaClose .answerClose .leftClose .rightClose
      , .rankCloseIfSome .closeRank .answerClose
          (.add (.optNatD .answerClose 0) (.const 1))
      , .outputPredIfSome .output .answerClose .closeRank ] by rfl]
  simp only [WholeQueryProgram.evalGlobalWordTrace,
    WordRAM.TraceResult.bind_trace, List.mem_append]
  apply Or.inl
  simpa [WholeQueryInstr.evalGlobalWordTrace,
    WholeQueryNatExpr.eval] using hmem

private theorem denseTwoWordSelect_first_successful_read
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) (word : WordRAM.Word)
    (hword : bitWords.store.words[basePosition / wordSize]? = some word) :
    .readWord bitWordSegmentBase (basePosition / wordSize) (some word) ∈
      (GenericSelect.denseTwoWordSelectTraceResultRelabeled
        bitWordSegmentBase deadSegment target bitWords
        basePosition baseOccurrence q).trace := by
  unfold GenericSelect.denseTwoWordSelectTraceResultRelabeled
    GenericSelect.denseTwoWordSelectTraceResult
  simp [WordRAM.TraceResult.relabelReadSegmentsWith,
    WordRAM.TraceEvent.relabelReadSegmentWith,
    WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
    SuccinctSpace.PayloadWordStore.readProgram,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Program.eval, WordRAM.Store.readWord?, hword]

private theorem reviewerSingleton_bitWord_zero :
    (GenericSelect.sparseExceptionSelectData
      (Cartesian.shape reviewerSingletonInput).bpCode false).bitWords.store.words[0]? =
        some [true, false] := by
  rw [reviewerSingletonInput_bpCode]
  simp [GenericSelect.sparseExceptionSelectData,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks,
    SuccinctSpace.chunkPayloadWords,
    SuccinctSpace.chunkPayloadWordsFuel,
    GenericSelect.wordBits, SuccinctRank.machineWordBits,
    reviewerSingleton_log2_two]

private theorem reviewerSingleton_sharedBP_select_successful_read :
    .readWord 0 0 (some [true, false]) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace := by
  let shape := Cartesian.shape reviewerSingletonInput
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  let super := GenericSelect.superEntry shape.bpCode false 0
  let loc := GenericSelect.localEntry shape.bpCode false 0
  have hvalid : 0 < GenericSelect.occurrenceCount shape.bpCode false := by
    dsimp [shape]
    rw [reviewerSingletonInput_bpCode]
    simp [GenericSelect.occurrenceCount, Succinct.rankPrefix]
  have hsuperEntry : data.superEntries[0]? = some super := by
    change (GenericSelect.superEntries shape.bpCode false)[0]? =
      some (GenericSelect.superEntry shape.bpCode false 0)
    exact GenericSelect.superEntries_get? shape.bpCode false
      reviewerSingleton_super_slot_exists
  have hlocalEntry : data.localEntries[0]? = some loc := by
    change (GenericSelect.localEntries shape.bpCode false)[0]? =
      some (GenericSelect.localEntry shape.bpCode false 0)
    exact GenericSelect.localEntries_get? shape.bpCode false
      reviewerSingleton_local_slot_exists
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
      (data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super)).value = some loc := by
    rw [hlocalSlot]
    simpa [hlocalEntry] using
      denseEntryTable_trace_value data.localTable layout.localTable 0
  have hshort :
      GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
    simpa [super, shape] using reviewerSingleton_super_not_marked
  have hdense :
      GenericSelect.relativeSplitSelectEntryIsMarked loc = false := by
    simpa [loc, shape] using reviewerSingleton_local_not_marked
  have hfirstIndex :
      GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc / data.wordSize = 0 := by
    simpa [data, super, loc, shape,
      GenericSelect.sparseExceptionSelectData] using
      reviewerSingleton_dense_first_word_index
  change .readWord 0 0 (some [true, false]) ∈
    (data.selectTraceResultRelabeled layout 0).trace
  apply selectTrace_dense_read_mem data layout 0 hvalid super loc
    hsuperValue hshort hlocalValue hdense
  have hword :
      data.bitWords.store.words[
        GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc / data.wordSize]? =
        some [true, false] := by
    rw [hfirstIndex]
    simpa [data, shape] using reviewerSingleton_bitWord_zero
  have hdenseMem := denseTwoWordSelect_first_successful_read
    layout.bitWordBase layout.deadSegment false data.bitWords
    (GenericSelect.relativeSplitSelectLocalBasePosition
      data.wordSize super loc)
    (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
    (data.queryOccurrence 0) [true, false] hword
  simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout,
    hfirstIndex] using hdenseMem

private theorem reviewerSingleton_select_value :
    (concreteBPNativeSelectCloseGlobalWordTraceResult
      (Cartesian.shape reviewerSingletonInput) 0).value = some 1 := by
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      (Cartesian.shape reviewerSingletonInput) 0
  have hexact :=
    concreteBPNativeSelectCloseCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      (Cartesian.shape reviewerSingletonInput) 0
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerSingletonInput) 0).value = some 1 := by
    rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
    rw [reviewerSingletonInput_shape] at hexact
    rw [reviewerSingletonInput_shape]
    simpa [Costed.erase, SuccinctSpace.bpCloseOfInorder?] using hexact
  have hvalue := congrArg Costed.value href
  exact hvalue.trans hinterpreted

private theorem reviewerSingleton_lca_value :
    (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
      (Cartesian.shape reviewerSingletonInput) 1 1).value = some 1 := by
  let shape := Cartesian.shape reviewerSingletonInput
  have hrankExact : forall pos,
      (concreteBPNativeRankCloseInterpretedCosted shape pos).erase =
        Succinct.rankPrefix false shape.bpCode pos := by
    intro pos
    rw [concreteBPNativeRankCloseInterpretedCosted_refines_rankCloseCosted]
    exact concreteBPNativeRankCloseCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily shape pos
  have hcanonical :=
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_exact_of_query
      (concreteBPNativeRankCloseInterpretedCosted shape)
      hrankExact (left := 0) (len := 1) (leftClose := 1)
      (rightClose := 1) (answerClose := 1)
      (by omega) (by
        dsimp [shape]
        rw [reviewerSingletonInput_shape]
        simp [Cartesian.CartesianShape.size])
      (by
        dsimp [shape]
        rw [reviewerSingletonInput_shape]
        simp [SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode])
      (by
        dsimp [shape]
        rw [reviewerSingletonInput_shape]
        simp [SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode])
      (by
        dsimp [shape]
        rw [reviewerSingletonInput_shape]
        simp [
          SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode, scanWindow])
  have hinterpreted :
      (concreteBPNativeLCACloseCanonicalInterpretedCosted shape 1 1).value =
        some 1 := by
    simpa [Costed.erase,
      concreteBPNativeLCACloseCanonicalInterpretedCosted] using hcanonical
  have href :=
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted
      shape 1 1
  have hvalue := congrArg Costed.value href
  exact hvalue.trans hinterpreted

private def reviewerSingletonBeforeRank : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
  ]

private def reviewerSingletonBeforeRankState : WholeQueryState :=
  (WholeQueryProgram.evalGlobalWordTrace
    (Cartesian.shape reviewerSingletonInput) 0 1 reviewerSingletonBeforeRank
    WholeQueryState.empty).value

private theorem reviewerSingletonBeforeRankState_answerClose :
    reviewerSingletonBeforeRankState.opt .answerClose = some 1 := by
  simp [reviewerSingletonBeforeRankState, reviewerSingletonBeforeRank,
    WholeQueryProgram.evalGlobalWordTrace,
    WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
    reviewerSingleton_select_value, reviewerSingleton_lca_value,
    WholeQueryState.empty, WholeQueryState.setOpt, WholeQueryState.opt]

private theorem rankTraceResultRelabeled_successful_reads_at
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) (segmentBase deadSegment pos : Nat) :
    (exists index word, WordRAM.TraceEvent.readWord segmentBase index
        (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target pos)).trace) /\
    (exists index word, WordRAM.TraceEvent.readWord (segmentBase + 1) index
        (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target pos)).trace) /\
    (exists index word, WordRAM.TraceEvent.readWord (segmentBase + 2) index
        (some word) ∈
      (WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment)
        (data.rankTraceResult target pos)).trace) := by
  let store := data.rankRegisterWordRAMStore target
  have hsource (localSegment index : Nat)
      (hsegment : localSegment < 3)
      (hindex : index = if localSegment = 0 then data.superIndex pos
        else data.wordIndex pos) :
      WordRAM.TraceEvent.readWord localSegment index
          (store.readWord? localSegment index) ∈
        (data.rankTraceResult target pos).trace := by
    have hcases :
        localSegment = 0 \/ localSegment = 1 \/ localSegment = 2 := by
      omega
    rcases hcases with rfl | rfl | rfl
    all_goals subst index
    all_goals simp [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterProgram,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndexExpr,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndexExpr,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPosExpr,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
      WordRAM.Register.NatExpr.eval,
      WordRAM.Register.RegFile.withNat1_nat_zero,
      WordRAM.Register.NatProgram.eval]
    all_goals split <;> simp [store]
  have hq : data.queryPos pos <= bits.length := Nat.min_le_right _ _
  rcases data.super_present target (data.queryPos pos) hq with
    ⟨sample, hsample⟩
  have hsuperWord :
      exists word, (data.superSampleWords target)[data.superIndex pos]? =
        some word := by
    cases target with
    | false =>
        apply fixedWidthNatTable_word_of_entry data.superTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex] using
          hsample
    | true =>
        apply fixedWidthNatTable_word_of_entry data.superTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex] using
          hsample
  rcases data.block_present target (data.queryPos pos) hq with
    ⟨delta, hdelta⟩
  have hblockWord :
      exists word, (data.blockSampleWords target)[data.wordIndex pos]? =
        some word := by
    cases target with
    | false =>
        apply fixedWidthNatTable_word_of_entry data.blockTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex] using
          hdelta
    | true =>
        apply fixedWidthNatTable_word_of_entry data.blockTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
          SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex] using
          hdelta
  rcases data.word_present (data.queryPos pos) hq with ⟨wordBits, hwordBits⟩
  rcases hsuperWord with ⟨superWord, hsuperWord⟩
  rcases hblockWord with ⟨blockWord, hblockWord⟩
  have hstoreSuper :
      store.readWord? 0 (data.superIndex pos) = some superWord := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hsuperWord
  have hstoreBlock :
      store.readWord? 1 (data.wordIndex pos) = some blockWord := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hblockWord
  have hstoreBits :
      store.readWord? 2 (data.wordIndex pos) = some wordBits := by
    simpa [store,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?] using hwordBits
  have hmapped (localSegment index : Nat) (hlocal : localSegment < 3)
      (hindex : index = if localSegment = 0 then data.superIndex pos
        else data.wordIndex pos) :=
    List.mem_map_of_mem
      (f := WordRAM.TraceEvent.relabelReadSegmentWith
        (WordRAM.tripleSegmentMap segmentBase deadSegment))
      (hsource localSegment index hlocal hindex)
  refine ⟨⟨data.superIndex pos, superWord, ?_⟩,
    ⟨data.wordIndex pos, blockWord, ?_⟩,
    ⟨data.wordIndex pos, wordBits, ?_⟩⟩
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreSuper] using
        hmapped 0 (data.superIndex pos) (by omega) rfl
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreBlock] using
        hmapped 1 (data.wordIndex pos) (by omega) rfl
  · simpa [WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceEvent.relabelReadSegmentWith,
      WordRAM.tripleSegmentMap, hstoreBits] using
        hmapped 2 (data.wordIndex pos) (by omega) rfl

private theorem reviewerSingleton_rank_successful_claims :
    (ReviewerProducerClaim.mk 17 .rankClose).HasSuccessfulClosedValidOccurrence /\
    (ReviewerProducerClaim.mk 18 .rankClose).HasSuccessfulClosedValidOccurrence /\
    (ReviewerProducerClaim.mk 19 .rankClose).HasSuccessfulClosedValidOccurrence := by
  let shape := Cartesian.shape reviewerSingletonInput
  let data := builtRelativeSplitBPCloseRankData shape
  have hreads := rankTraceResultRelabeled_successful_reads_at data false
    concreteBPNativeRankCloseTraceSegmentBase
    concreteBPNativeDeadTraceSegment 2
  change
    (exists index word, .readWord 17 index (some word) ∈
      (concreteBPNativeRankCloseWordTraceResultAtSegment shape 17 2).trace) /\
    (exists index word, .readWord 18 index (some word) ∈
      (concreteBPNativeRankCloseWordTraceResultAtSegment shape 17 2).trace) /\
    (exists index word, .readWord 19 index (some word) ∈
      (concreteBPNativeRankCloseWordTraceResultAtSegment shape 17 2).trace)
      at hreads
  have closeOne {segment index : Nat} {word : WordRAM.Word}
      (hmem : .readWord segment index (some word) ∈
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape 17 2).trace) :
      (ReviewerProducerClaim.mk segment .rankClose)
        |>.HasSuccessfulClosedValidOccurrence := by
    rcases List.mem_iff_getElem?.mp hmem with ⟨localPos, hget⟩
    apply reviewerClaim_successful_of_local_get reviewerSingletonInput
      0 1 segment index word .rankClose reviewerSingletonBeforeRank
      [WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank]
      (WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
        (.add (.optNatD .answerClose 0) (.const 1)))
      reviewerSingletonBeforeRankState localPos (.rankClose 2)
    · simp [ValidRange, reviewerSingletonInput]
    · rfl
    · rfl
    · simpa [shape, WholeQueryInstr.evalGlobalWordTrace,
        reviewerSingletonBeforeRankState_answerClose,
        WholeQueryNatExpr.eval] using hget
    · simpa [WholeQueryNatExpr.eval,
        reviewerSingletonBeforeRankState_answerClose] using
        (WholeQueryInstr.InvokesReviewerRead.rankClose
          (left := 0) (right := 1) .closeRank .answerClose
          (.add (.optNatD .answerClose 0) (.const 1)) 1
          reviewerSingletonBeforeRankState_answerClose)
    · rfl
    · simpa [shape, ReviewerReadInvocation.componentTrace] using hget
  rcases hreads with
    ⟨⟨index17, word17, h17⟩, ⟨index18, word18, h18⟩,
      ⟨index19, word19, h19⟩⟩
  exact ⟨closeOne h17, closeOne h18, closeOne h19⟩

private theorem reviewerSingleton_select_shared_claim :
    (ReviewerProducerClaim.mk 0 .selectClose)
      |>.HasSuccessfulClosedValidOccurrence := by
  rcases List.mem_iff_getElem?.mp
      reviewerSingleton_sharedBP_select_successful_read with
    ⟨localPos, hget⟩
  apply reviewerClaim_successful_of_local_get reviewerSingletonInput
    0 1 0 0 [true, false] .selectClose []
    [ WholeQueryInstr.selectClose .rightClose
        (.sub .inputRight (.const 1))
    , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
    , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
        (.add (.optNatD .answerClose 0) (.const 1))
    , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
    ]
    (WholeQueryInstr.selectClose .leftClose .inputLeft)
    WholeQueryState.empty localPos (.selectClose 0)
  · simp [ValidRange, reviewerSingletonInput]
  · rfl
  · rfl
  · simpa [WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval] using
      hget
  · exact WholeQueryInstr.InvokesReviewerRead.selectClose
      .leftClose .inputLeft
  · rfl
  · simpa [ReviewerReadInvocation.componentTrace] using hget

private theorem reviewerIncreasingSixteen_select_left_value :
    (concreteBPNativeSelectCloseGlobalWordTraceResult
      (Cartesian.shape reviewerIncreasingSixteenInput) 0).value = some 1 := by
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      (Cartesian.shape reviewerIncreasingSixteenInput) 0
  have hexact :=
    concreteBPNativeSelectCloseCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      (Cartesian.shape reviewerIncreasingSixteenInput) 0
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerIncreasingSixteenInput) 0).value = some 1 := by
    rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
    rw [reviewerIncreasingSixteenInput_shape] at hexact
    rw [reviewerIncreasingSixteenInput_shape]
    simpa [Costed.erase, reviewerRightSpine,
      SuccinctSpace.bpCloseOfInorder?,
      Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode] using
      hexact
  exact (congrArg Costed.value href).trans hinterpreted

private theorem reviewerIncreasingSixteen_select_right_value :
    (concreteBPNativeSelectCloseGlobalWordTraceResult
      (Cartesian.shape reviewerIncreasingSixteenInput) 15).value = some 31 := by
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      (Cartesian.shape reviewerIncreasingSixteenInput) 15
  have hexact :=
    concreteBPNativeSelectCloseCosted_exact
      builtGenericSparseExceptionSelectBPCloseAccessFamily
      (Cartesian.shape reviewerIncreasingSixteenInput) 15
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerIncreasingSixteenInput) 15).value =
          some 31 := by
    rw [concreteBPNativeSelectCloseInterpretedCosted_refines_selectCloseCosted]
    rw [reviewerIncreasingSixteenInput_shape] at hexact
    rw [reviewerIncreasingSixteenInput_shape]
    simpa [Costed.erase, reviewerRightSpine,
      SuccinctSpace.bpCloseOfInorder?,
      Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode] using
      hexact
  exact (congrArg Costed.value href).trans hinterpreted

private def reviewerIncreasingSixteenBeforeLCA : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  ]

private def reviewerIncreasingSixteenBeforeLCAState : WholeQueryState :=
  (WholeQueryProgram.evalGlobalWordTrace
    (Cartesian.shape reviewerIncreasingSixteenInput) 0 16
    reviewerIncreasingSixteenBeforeLCA WholeQueryState.empty).value

private theorem reviewerIncreasingSixteenBeforeLCAState_closes :
    reviewerIncreasingSixteenBeforeLCAState.opt .leftClose = some 1 /\
    reviewerIncreasingSixteenBeforeLCAState.opt .rightClose = some 31 := by
  simp [reviewerIncreasingSixteenBeforeLCAState,
    reviewerIncreasingSixteenBeforeLCA,
    WholeQueryProgram.evalGlobalWordTrace,
    WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
    reviewerIncreasingSixteen_select_left_value,
    reviewerIncreasingSixteen_select_right_value,
    WholeQueryState.empty, WholeQueryState.setOpt, WholeQueryState.opt]

private theorem reviewerCanonicalComponent_local_get
    (shape : Cartesian.CartesianShape) (localAddress : Nat)
    (hlocal :
      localAddress <
        (SuccinctClose.canonicalRelativeRmmLocalMachineStore
          shape).store.words.size) :
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
      shape).store.words[
        (SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets
          shape).localOffset + localAddress]? =
      (SuccinctClose.canonicalRelativeRmmLocalMachineStore
        shape).store.words[localAddress]? := by
  have hlist :
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words.toList[
          (SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets
            shape).localOffset + localAddress]? =
        (SuccinctClose.canonicalRelativeRmmLocalMachineStore
          shape).store.words.toList[localAddress]? := by
    let hword := SuccinctRank.machineWordBits_pos shape.bpCode.length
    let summary := SuccinctClose.canonicalRelativeRmmSummaryTable shape
    let baselineWords :=
      (summary.baselineTable.machineStore hword).store.words.toList
    let minRelWords :=
      (summary.minRelTable.machineStore hword).store.words.toList
    let maxRelWords :=
      (summary.maxRelTable.machineStore hword).store.words.toList
    let argWords :=
      (summary.argOffsetTable.machineStore hword).store.words.toList
    let localWords :=
      ((SuccinctClose.canonicalRelativeRmmInteriorLocalTable
        shape).table.machineStore hword).store.words.toList
    let globalWords :=
      ((SuccinctClose.canonicalRelativeRmmInteriorGlobalTable
        shape).table.machineStore hword).store.words.toList
    have hlocalWords : localAddress < localWords.length := by
      simpa [localWords,
        SuccinctClose.canonicalRelativeRmmLocalMachineStore] using hlocal
    have hmiddle :
        ((((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords) ++
          localWords ++ globalWords)[
            (((baselineWords ++ minRelWords) ++ maxRelWords) ++
              argWords).length + localAddress]? =
          localWords[localAddress]? :=
      SuccinctSpace.List.getElem?_append_middle_of_lt
        (((baselineWords ++ minRelWords) ++ maxRelWords) ++ argWords)
        localWords globalWords localAddress hlocalWords
    rw [SuccinctClose.canonicalRelativeRmmInteriorComponentStore_words_toList]
    simpa [hword, summary, baselineWords, minRelWords, maxRelWords,
      argWords, localWords, globalWords,
      SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets,
      SuccinctClose.canonicalRelativeRmmLocalMachineStore,
      List.length_append, List.append_assoc, Nat.add_assoc] using hmiddle
  simpa [Array.getElem?_toList] using hlist

private theorem reviewerIncreasingCanonicalInterior_successfulRead :
    exists index word, .readWord 20 index (some word) ∈
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        (Cartesian.shape reviewerIncreasingSixteenInput)
        concreteBPNativeInteriorTraceSegments 1 2).trace := by
  let shape := Cartesian.shape reviewerIncreasingSixteenInput
  let layout := SuccinctClose.RelativeRmm.canonicalLayout shape
  let table := SuccinctClose.canonicalRelativeRmmInteriorLocalTable shape
  let offsets :=
    SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets shape
  let array :=
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore shape).store.words
  let store := SuccinctSpace.FlatWordStore.ofArray array
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let slot := SuccinctClose.bpLocalSparseCellSlot layout.macroSize
    layout.levelCount 0 1 (Nat.log2 2)
  have hlogSixteen := reviewer_log2_sixteen
  have hlogTwentyFive := reviewer_log2_twentyFive
  have hlogTwo := reviewerSingleton_log2_two
  have hmacroSize : layout.macroSize = 25 := by
    dsimp [layout, shape]
    rw [reviewerIncreasingSixteenInput_shape]
    simp [
      SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw,
      SuccinctClose.canonicalBPRelativeSummaryBase, reviewerRightSpine,
      Cartesian.CartesianShape.size, hlogSixteen]
  have hlevelCount : layout.levelCount = 5 := by
    dsimp [layout, shape]
    rw [reviewerIncreasingSixteenInput_shape]
    simp [SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw,
      SuccinctClose.canonicalBPRelativeSummaryBase, reviewerRightSpine,
      Cartesian.CartesianShape.size, SuccinctRank.machineWordBits,
      hlogSixteen, hlogTwentyFive]
  have hstart : 1 < layout.macroSize := by omega
  have hfits : 2 <= layout.macroSize - 1 := by omega
  have hqueryLevel : Nat.log2 2 < layout.levelCount := by
    rw [hlevelCount, hlogTwo]
    omega
  have hmacroShape :
      (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize = 25 := by
    simpa [layout] using hmacroSize
  have hmacro : 0 < layout.macroSampleCount := by
    simp [layout, SuccinctClose.RelativeRmm.Layout.macroSampleCount]
  have hlayoutLevelPos : 0 < layout.levelCount := by
    simpa [layout, SuccinctClose.RelativeRmm.Layout.levelCount,
      SuccinctClose.RelativeRmm.Layout.offsetWidth] using
      SuccinctRank.machineWordBits_pos layout.macroSize
  have hlocal : 0 < layout.macroSize := by
    have hraw :=
      SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw_pos shape
    simpa [layout, SuccinctClose.RelativeRmm.Layout.macroSize,
      SuccinctClose.RelativeRmm.canonicalLayout] using Nat.mul_pos hraw hraw
  have hslot :
      slot <
        (SuccinctClose.bpLocalSparseOffsetEntries shape layout.blockSize
          layout.blockCount layout.macroSize layout.macroSampleCount
          layout.levelCount).length := by
    have hentry :=
      SuccinctClose.bpLocalSparseOffsetEntries_get?_of_valid
        (shape := shape) (blockSize := layout.blockSize)
        (blockCount := layout.blockCount) (macroSize := layout.macroSize)
        (macroCount := layout.macroSampleCount)
        (levelCount := layout.levelCount) (macroIdx := 0)
        (localStart := 1) (level := Nat.log2 2)
        (by omega) (by simpa [layout] using hqueryLevel)
        (by simpa [layout] using hstart)
    exact (List.getElem?_eq_some_iff.mp hentry).1
  have hslotCanonical := hslot
  dsimp [layout] at hslotCanonical
  let count :=
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
      layout.offsetWidth wordSize
  let localAddress := slot * count
  have hfootprint :
      localAddress ∈
        SuccinctSpace.fixedWidthNatTableMachineFootprint
          layout.offsetWidth wordSize slot := by
    have hcount : 0 < count := by
      apply reviewerFixedWidthMachineChunkCount_pos
      simpa [layout, SuccinctClose.RelativeRmm.Layout.offsetWidth] using
        SuccinctRank.machineWordBits_pos layout.macroSize
    obtain ⟨tail, hcountEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hcount)
    simp [SuccinctSpace.fixedWidthNatTableMachineFootprint, localAddress,
      count, hcountEq, SuccinctSpace.consecutiveWordIndices]
  have hwordSize : 0 < wordSize := by
    simpa [wordSize] using SuccinctRank.machineWordBits_pos shape.bpCode.length
  rcases table.table.machineFootprint_successful_read_backed
      hwordSize hslot hfootprint with
    ⟨word, hwordRead, _hwordMem, _herases⟩
  have hlocalGet :
      (SuccinctClose.canonicalRelativeRmmLocalMachineStore
        shape).store.words[localAddress]? = some word := by
    simpa [table, wordSize,
      SuccinctClose.canonicalRelativeRmmLocalMachineStore,
      Costed.erase] using hwordRead
  have hlocalLt :
      localAddress <
        (SuccinctClose.canonicalRelativeRmmLocalMachineStore
          shape).store.words.size :=
    (Array.getElem?_eq_some_iff.mp hlocalGet).1
  have hcomponentGet :
      array[offsets.localOffset + localAddress]? = some word := by
    have hslice :=
      reviewerCanonicalComponent_local_get shape localAddress hlocalLt
    rw [hslice]
    exact hlocalGet
  have hfirst :
      (offsets.localOffset + localAddress, some word) ∈
        ((table.table.machineReadComputationAt wordSize offsets.localOffset
          offsets.deadAddress slot).run store).reads := by
    unfold SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
    rw [if_pos (by simpa [slot, layout] using hslot)]
    simp only [
      SuccinctSpace.FlatStoreComputation.map_run_reads,
      SuccinctSpace.FlatStoreComputation.readMany_run_reads, List.mem_map]
    refine ⟨offsets.localOffset + localAddress, ?_, ?_⟩
    · exact List.mem_map_of_mem
        (f := fun address => offsets.localOffset + address) hfootprint
    · simp [store, SuccinctSpace.FlatWordStore.ofArray, hcomponentGet]
  have hlocalSpan :
      (offsets.localOffset + localAddress, some word) ∈
        ((SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
          shape 0 1 (Nat.log2 2)).run store).reads := by
    unfold SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
    simp only [SuccinctSpace.FlatStoreComputation.bind_run,
      SuccinctSpace.FlatStoreExecution.append]
    apply List.mem_append_left
    change
      (offsets.localOffset + localAddress, some word) ∈
        ((table.table.machineReadComputationAt wordSize offsets.localOffset
          offsets.deadAddress slot).run store).reads
    exact hfirst
  have htwo :
      (offsets.localOffset + localAddress, some word) ∈
        ((SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
          shape 0 1 2).run store).reads := by
    unfold
      SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    simp only [SuccinctSpace.FlatStoreComputation.bind_run,
      SuccinctSpace.FlatStoreExecution.append]
    exact List.mem_append_left _ hlocalSpan
  have hexec :
      (offsets.localOffset + localAddress, some word) ∈
        (SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithStore
          shape array 1 2).reads := by
    unfold
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithStore
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithRead
      SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation
    dsimp only
    rw [if_neg (by omega)]
    rw [if_pos (by
      rw [hmacroShape]
      omega)]
    rw [hmacroShape]
    rw [show 1 / 25 = 0 by omega, show 1 % 25 = 1 by omega]
    unfold
      SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
    simp only [SuccinctSpace.FlatStoreComputation.bind_run,
      SuccinctSpace.FlatStoreExecution.append]
    exact List.mem_append_left _ hlocalSpan
  refine ⟨offsets.localOffset + localAddress, word, ?_⟩
  unfold
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
  unfold
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment
  unfold SuccinctClose.flatStoreExecutionTraceResultAtSegment
  apply List.mem_map.mpr
  exact ⟨(offsets.localOffset + localAddress, some word), hexec, by
    simp [concreteBPNativeInteriorTraceSegments]⟩

private theorem reviewerIncreasing_lca_interior_mem
    {event : WordRAM.TraceEvent}
    (hmem : List.Mem event
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        (Cartesian.shape reviewerIncreasingSixteenInput)
        concreteBPNativeInteriorTraceSegments 1 2).trace) :
    List.Mem event
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        (Cartesian.shape reviewerIncreasingSixteenInput) 1 31).trace := by
  have hblock : SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
      (Cartesian.shape reviewerIncreasingSixteenInput) = 10 := by
    rw [reviewerIncreasingSixteenInput_shape]
    simp [SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw,
      SuccinctClose.canonicalBPRelativeSummaryBase, reviewerRightSpine,
      Cartesian.CartesianShape.size, Nat.log2]
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_append_left _ hmem

private theorem reviewerIncreasing_lca_sharedBP_mem :
    List.Mem (.readWord 0 0
      (some [true, false, true, false, true, false]))
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        (Cartesian.shape reviewerIncreasingSixteenInput) 1 31).trace := by
  have hword0 :
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits
          (Cartesian.shape reviewerIncreasingSixteenInput).bpCode.length)
        (Cartesian.shape reviewerIncreasingSixteenInput).bpCode).toArray[0]? =
          some [true, false, true, false, true, false] := by
    rw [reviewerIncreasingSixteenInput_shape]
    simp [reviewerRightSpine, Cartesian.CartesianShape.bpCode,
      SuccinctRank.machineWordBits, SuccinctSpace.chunkPayloadWords,
      SuccinctSpace.chunkPayloadWordsFuel, Nat.log2]
  have hwindow :
      List.Mem (.readWord 0 0
        (some [true, false, true, false, true, false]))
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult
          (Cartesian.shape reviewerIncreasingSixteenInput) 10 1).trace := by
    simp only [
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResult,
      WordRAM.TraceResult.map_trace,
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResult,
      WordRAM.TraceResult.bind_trace,
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResult,
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeReadWordTraceEvent,
      SuccinctClose.blockOfClose, SuccinctClose.blockStartOf]
    simp only [Nat.reduceDiv, Nat.zero_mul, Nat.zero_div, hword0]
    exact List.mem_append_left _ List.mem_cons_self
  have hblock : SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
      (Cartesian.shape reviewerIncreasingSixteenInput) = 10 := by
    rw [reviewerIncreasingSixteenInput_shape]
    simp [SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw,
      SuccinctClose.canonicalBPRelativeSummaryBase, reviewerRightSpine,
      Cartesian.CartesianShape.size, Nat.log2]
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  apply List.mem_append_right
  apply List.mem_append_left
  simpa [
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPLeftFringeCandidateSeededTraceResult,
    WordRAM.TraceResult.map_trace] using hwindow

private theorem reviewerIncreasing_canonical_successful_claim_of_mem
    {segment index : Nat} {word : WordRAM.Word}
    (hmem : List.Mem (.readWord segment index (some word))
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        (Cartesian.shape reviewerIncreasingSixteenInput) 1 31).trace) :
    (ReviewerProducerClaim.mk segment .canonicalClose)
      |>.HasSuccessfulClosedValidOccurrence := by
  rcases List.mem_iff_getElem?.mp hmem with ⟨localPos, hget⟩
  have hcloses := reviewerIncreasingSixteenBeforeLCAState_closes
  apply reviewerClaim_successful_of_local_get reviewerIncreasingSixteenInput
    0 16 segment index word .canonicalClose
    reviewerIncreasingSixteenBeforeLCA
    [ WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
        (.add (.optNatD .answerClose 0) (.const 1))
    , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
    ]
    (WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose)
    reviewerIncreasingSixteenBeforeLCAState localPos
    (.canonicalClose 1 31)
  · simp [ValidRange, reviewerIncreasingSixteenInput]
  · rfl
  · rfl
  · simpa [WholeQueryInstr.evalGlobalWordTrace,
      hcloses.1, hcloses.2] using hget
  · exact WholeQueryInstr.InvokesReviewerRead.canonicalClose
      .answerClose .leftClose .rightClose 1 31 hcloses.1 hcloses.2
  · rfl
  · simpa [ReviewerReadInvocation.componentTrace] using hget

private theorem reviewerIncreasing_canonical_successful_claims :
    (ReviewerProducerClaim.mk 20 .canonicalClose).HasSuccessfulClosedValidOccurrence ∧
    (ReviewerProducerClaim.mk 0 .canonicalClose).HasSuccessfulClosedValidOccurrence := by
  rcases reviewerIncreasingCanonicalInterior_successfulRead with
    ⟨index, word, hread⟩
  exact ⟨
    reviewerIncreasing_canonical_successful_claim_of_mem
      (reviewerIncreasing_lca_interior_mem hread),
    reviewerIncreasing_canonical_successful_claim_of_mem
      reviewerIncreasing_lca_sharedBP_mem⟩

/--
The twelve always-small reviewer sources have successful occurrences in real
closed valid queries. Source ordinals `1` through `11` are witnessed by the
singleton execution, whose successful reads include segments `0` through `8`
and `17` through `19`; canonical source ordinal `20` is witnessed by the
increasing-length-sixteen cross-block execution.
-/
theorem concreteBPNativeSuccinctRMQReviewerSource_small_successful_closed_valid_occurrence
    (source : ReviewerSource)
    (hsource : source ∈
      [ .sharedBPCode
      , .finalRankSuperFalse
      , .finalRankBlockFalse
      , .selectSuperBaseOccurrence
      , .selectSuperBaseWordIndex
      , .selectSuperRankBefore
      , .selectSuperFirstOffset
      , .selectLocalBaseOccurrence
      , .selectLocalBaseWordIndex
      , .selectLocalRankBefore
      , .selectLocalFirstOffset
      , .canonicalClose ]) :
    source.HasSuccessfulClosedValidOccurrence := by
  rcases reviewerSingleton_select_table_successful_reads with
    ⟨⟨word1, hread1⟩, ⟨word2, hread2⟩, ⟨word3, hread3⟩,
      ⟨word4, hread4⟩, ⟨word5, hread5⟩, ⟨word6, hread6⟩,
      ⟨word7, hread7⟩, ⟨word8, hread8⟩⟩
  have h1 : ReviewerSource.selectSuperBaseOccurrence
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectSuperBaseOccurrence reviewerSingletonInput 0 1 1 0 word1
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread1)
  have h2 : ReviewerSource.selectSuperBaseWordIndex
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectSuperBaseWordIndex reviewerSingletonInput 0 1 2 0 word2
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread2)
  have h3 : ReviewerSource.selectSuperRankBefore
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectSuperRankBefore reviewerSingletonInput 0 1 3 0 word3
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread3)
  have h4 : ReviewerSource.selectSuperFirstOffset
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectSuperFirstOffset reviewerSingletonInput 0 1 4 0 word4
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread4)
  have h5 : ReviewerSource.selectLocalBaseOccurrence
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectLocalBaseOccurrence reviewerSingletonInput 0 1 5 0 word5
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread5)
  have h6 : ReviewerSource.selectLocalBaseWordIndex
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectLocalBaseWordIndex reviewerSingletonInput 0 1 6 0 word6
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread6)
  have h7 : ReviewerSource.selectLocalRankBefore
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectLocalRankBefore reviewerSingletonInput 0 1 7 0 word7
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread7)
  have h8 : ReviewerSource.selectLocalFirstOffset
      |>.HasSuccessfulClosedValidOccurrence :=
    reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
      .selectLocalFirstOffset reviewerSingletonInput 0 1 8 0 word8
      (by simp [ValidRange, reviewerSingletonInput]) rfl
      (firstSelectClose_read_mem_wholeQuery hread8)
  have hshared : ReviewerSource.sharedBPCode
      |>.HasSuccessfulClosedValidOccurrence :=
    ⟨ReviewerProducerClaim.mk 0 .selectClose, rfl,
      reviewerSingleton_select_shared_claim⟩
  rcases reviewerSingleton_rank_successful_claims with
    ⟨hrank17, hrank18, _hrank19⟩
  have h17 : ReviewerSource.finalRankSuperFalse
      |>.HasSuccessfulClosedValidOccurrence :=
    ⟨ReviewerProducerClaim.mk 17 .rankClose, rfl, hrank17⟩
  have h18 : ReviewerSource.finalRankBlockFalse
      |>.HasSuccessfulClosedValidOccurrence :=
    ⟨ReviewerProducerClaim.mk 18 .rankClose, rfl, hrank18⟩
  have h20 : ReviewerSource.canonicalClose
      |>.HasSuccessfulClosedValidOccurrence :=
    ⟨ReviewerProducerClaim.mk 20 .canonicalClose, rfl,
      reviewerIncreasing_canonical_successful_claims.1⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact hshared
  · exact h17
  · exact h18
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h20

/-- Every deliberate consumer of the shared BP payload has its own successful
indexed occurrence in an actual closed valid query. -/
theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence
    (consumer : ReviewerSharedBPConsumer) :
    consumer.HasSuccessfulClosedValidOccurrence := by
  cases consumer with
  | selectClose =>
      simpa [ReviewerSharedBPConsumer.HasSuccessfulClosedValidOccurrence,
        ReviewerSharedBPConsumer.producerClaim,
        ReviewerSharedBPConsumer.segment, ReviewerSharedBPConsumer.leaf] using
        reviewerSingleton_select_shared_claim
  | rankClose =>
      simpa [ReviewerSharedBPConsumer.HasSuccessfulClosedValidOccurrence,
        ReviewerSharedBPConsumer.producerClaim,
        ReviewerSharedBPConsumer.segment, ReviewerSharedBPConsumer.leaf] using
        reviewerSingleton_rank_successful_claims.2.2
  | canonicalClose =>
      simpa [ReviewerSharedBPConsumer.HasSuccessfulClosedValidOccurrence,
        ReviewerSharedBPConsumer.producerClaim,
        ReviewerSharedBPConsumer.segment, ReviewerSharedBPConsumer.leaf] using
        reviewerIncreasing_canonical_successful_claims.2

end SuccinctFinal
end RMQ

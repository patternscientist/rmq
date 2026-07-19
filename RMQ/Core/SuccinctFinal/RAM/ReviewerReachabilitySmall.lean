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

private theorem canonicalSuperTableWithStore_eq
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

private theorem canonicalLocalTableWithStore_eq
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

private theorem chunkedSelectTrace_super_read_mem
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData bits target
      rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : WordRAM.ReadStore) (c idx : Nat)
    (hvalid : idx < GenericSelect.occurrenceCount bits target)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        store
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence idx) data.superStride)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  exact Or.inl hmem

private theorem chunkedSelectTrace_local_read_mem
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
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        store
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence idx) data.superStride
          data.localSlotsPerSuper data.localStride super)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hshort]
  exact Or.inl hmem

private theorem chunkedSelectTrace_dense_read_mem
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
    (hdense : GenericSelect.relativeSplitSelectEntryIsMarked loc = false)
    {event : WordRAM.TraceEvent}
    (hmem : event ∈
      (GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        layout.bitWordBase chunkSegment selectTableSegment c target
        data.bitWords store
        (GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc)
        (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
        (data.queryOccurrence idx)).trace) :
    event ∈
      (data.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx).trace := by
  unfold GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [if_pos hvalid, WordRAM.TraceResult.bind_trace,
    List.mem_append]
  apply Or.inr
  simp [hsuper, hshort]
  apply Or.inr
  simpa [hlocal, hdense] using hmem

private theorem chunkedDenseTwoWordSelect_first_successful_read
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) (word : WordRAM.Word)
    (hword :
      store.readWord? bitWordSegment (basePosition / wordSize) =
        some word) :
    .readWord bitWordSegment (basePosition / wordSize) (some word) ∈
      (GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target
        bitWords store basePosition baseOccurrence q).trace := by
  simp [GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore,
    WordRAM.TraceResult.bind_trace, SuccinctClose.bpWordReadTraceResult,
    List.mem_append, hword]

private theorem chunkedRankTraceWithStore_successful_reads
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

/-- The head event of any non-empty charged in-word rank fold is the chunk
read of the first visited slot, recording the supplied store's answer. -/
private theorem chunkedWordRankTraceFromWithStore_head_read_mem
    (store : WordRAM.ReadStore) (segment c : Nat) (target : Bool)
    (word : List Bool) (e j count acc : Nat) :
    .readWord segment
        (SuccinctClose.bpFringeChunkSlot c
          (SuccinctClose.bpFringeWindowChunkValue c word j)
          (SuccinctClose.bpWordChunkSliceLen c e j)
          (SuccinctClose.bpWordChunkSliceLen c e j))
        (store.readWord? segment
          (SuccinctClose.bpFringeChunkSlot c
            (SuccinctClose.bpFringeWindowChunkValue c word j)
            (SuccinctClose.bpWordChunkSliceLen c e j)
            (SuccinctClose.bpWordChunkSliceLen c e j))) ∈
      (SuccinctClose.bpChunkedWordRankTraceFromWithStore store segment c
        target word e j (count + 1) acc).trace := by
  show _ ∈ (WordRAM.TraceResult.bind
      (SuccinctClose.bpChunkReadTraceResult store segment
        (SuccinctClose.bpFringeChunkSlot c
          (SuccinctClose.bpFringeWindowChunkValue c word j)
          (SuccinctClose.bpWordChunkSliceLen c e j)
          (SuccinctClose.bpWordChunkSliceLen c e j))) _).trace
  rw [WordRAM.TraceResult.bind_trace]
  exact List.mem_append_left _ (List.Mem.head _)

/--
Under store agreement with the honest fringe chunk table, the charged
in-word rank fold ALWAYS issues at least one SUCCESSFUL chunk-table read:
the chunk count is at least one even at limit zero, the first visited slot
is row-count-bounded, and every counted slot is backed by a stored word.
Existence-level only; table widths are never kernel-reduced.
-/
private theorem reviewerFringeChunk_rankFold_first_successful_read
    {store : WordRAM.ReadStore} {segment c : Nat}
    (hagree : forall address,
      store.readWord? segment address =
        (SuccinctClose.bpFringeChunkTable c).store.words[address]?)
    (target : Bool) (word : List Bool) (limit : Nat) :
    ∃ index w,
      .readWord segment index (some w) ∈
        (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
          store segment c target word limit).trace := by
  have hv : SuccinctClose.bpFringeWindowChunkValue c word 0 < 2 ^ c :=
    SuccinctClose.bpFringeWindowChunkValue_lt c word 0
  have ha : SuccinctClose.bpWordChunkSliceLen c
      (SuccinctClose.bpWordRankEffLimit word limit) 0 <= c :=
    SuccinctClose.bpWordChunkSliceLen_le c _ 0
  have hentry :
      (SuccinctClose.bpFringeChunkEntries c)[
        SuccinctClose.bpFringeChunkSlot c
          (SuccinctClose.bpFringeWindowChunkValue c word 0)
          (SuccinctClose.bpWordChunkSliceLen c
            (SuccinctClose.bpWordRankEffLimit word limit) 0)
          (SuccinctClose.bpWordChunkSliceLen c
            (SuccinctClose.bpWordRankEffLimit word limit) 0)]? =
        some (SuccinctClose.bpFringeChunkPacked c
          (SuccinctClose.bpFringeWindowChunkValue c word 0)
          (SuccinctClose.bpWordChunkSliceLen c
            (SuccinctClose.bpWordRankEffLimit word limit) 0)
          (SuccinctClose.bpWordChunkSliceLen c
            (SuccinctClose.bpWordRankEffLimit word limit) 0)) :=
    SuccinctClose.bpFringeChunkEntries_getElem hv ha ha
  obtain ⟨w, hw⟩ := fixedWidthNatTable_word_of_entry
    (SuccinctClose.bpFringeChunkTable c) _ hentry
  have hread : store.readWord? segment
      (SuccinctClose.bpFringeChunkSlot c
        (SuccinctClose.bpFringeWindowChunkValue c word 0)
        (SuccinctClose.bpWordChunkSliceLen c
          (SuccinctClose.bpWordRankEffLimit word limit) 0)
        (SuccinctClose.bpWordChunkSliceLen c
          (SuccinctClose.bpWordRankEffLimit word limit) 0)) = some w := by
    rw [hagree]
    exact hw
  have hpos : 0 < SuccinctClose.bpWordChunkCount c
      (SuccinctClose.bpWordRankEffLimit word limit) :=
    Nat.le_min.mpr ⟨Nat.le_add_left 1 _, by omega⟩
  obtain ⟨count, hcount⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hmem := chunkedWordRankTraceFromWithStore_head_read_mem store segment
    c target word (SuccinctClose.bpWordRankEffLimit word limit) 0 count 0
  rw [hread] at hmem
  refine ⟨SuccinctClose.bpFringeChunkSlot c
      (SuccinctClose.bpFringeWindowChunkValue c word 0)
      (SuccinctClose.bpWordChunkSliceLen c
        (SuccinctClose.bpWordRankEffLimit word limit) 0)
      (SuccinctClose.bpWordChunkSliceLen c
        (SuccinctClose.bpWordRankEffLimit word limit) 0), w, ?_⟩
  unfold SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
  rw [hcount]
  exact hmem

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

private theorem reviewerSingleton_dense_base_position :
    GenericSelect.relativeSplitSelectLocalBasePosition
        (GenericSelect.wordBits
          (Cartesian.shape reviewerSingletonInput).bpCode.length)
        (GenericSelect.superEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0)
        (GenericSelect.localEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0) = 1 := by
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

private theorem reviewerSingleton_dense_base_occurrence :
    GenericSelect.relativeSplitSelectLocalBaseOccurrence
        (GenericSelect.superEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0)
        (GenericSelect.localEntry
          (Cartesian.shape reviewerSingletonInput).bpCode false 0) = 0 := by
  rw [reviewerSingletonInput_bpCode]
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
    Succinct.select, Succinct.selectFrom, reviewerSingleton_log2_two]

private theorem reviewerSingleton_chunkBits :
    SuccinctClose.bpFringeChunkBits
      (Cartesian.shape reviewerSingletonInput).bpCode.length = 1 := by
  rw [reviewerSingletonInput_bpCode]
  simp [SuccinctClose.bpFringeChunkBits, reviewerSingleton_log2_two]

/--
The singleton close-select execution's in-word select fold on the shared
word `[true, false]` (target `false`, occurrence `0`) issues a genuine
SUCCESSFUL read of the counted select chunk-table segment: chunk `0`
(the `true` bit) contributes no `false`, so the fold routes to chunk `1`
whose decoded count `1 > 0` fires the found branch's segment-`22` read,
and the read succeeds because the slot is inside the counted table.
-/
private theorem reviewerSingleton_inWordSelect_selectTable_read :
    ∃ index word,
      .readWord concreteBPNativeSelectChunkTraceSegment index (some word) ∈
        (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
          (concreteBPNativeSuccinctRMQGlobalReadStore
            (Cartesian.shape reviewerSingletonInput))
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment
          1 false [true, false] 0).trace := by
  have hfringe : forall address,
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
          concreteBPNativeFringeChunkTraceSegment address =
        (SuccinctClose.bpFringeChunkTable 1).store.words[address]? := by
    intro address
    have h := concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable
      (Cartesian.shape reviewerSingletonInput) address
    rwa [reviewerSingleton_chunkBits] at h
  have hselect : forall address,
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
          concreteBPNativeSelectChunkTraceSegment address =
        (SuccinctClose.bpChunkSelectTable 1 false).store.words[address]? := by
    intro address
    have h := concreteBPNativeSuccinctRMQGlobalReadStore_selectChunkTable
      (Cartesian.shape reviewerSingletonInput) address
    rwa [reviewerSingleton_chunkBits] at h
  have hv0 :
      SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0 < 2 ^ 1 :=
    SuccinctClose.bpFringeWindowChunkValue_lt 1 [true, false] 0
  have hv1 :
      SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1 < 2 ^ 1 :=
    SuccinctClose.bpFringeWindowChunkValue_lt 1 [true, false] 1
  have ht0 :
      SuccinctClose.bpWordChunkSliceLen 1
        ([true, false] : List Bool).length 0 = 1 := by
    decide
  have ht1 :
      SuccinctClose.bpWordChunkSliceLen 1
        ([true, false] : List Bool).length 1 = 1 := by
    decide
  have hle0 :
      SuccinctClose.bpWordChunkSliceLen 1
          ([true, false] : List Bool).length 0 <= 1 :=
    SuccinctClose.bpWordChunkSliceLen_le 1 _ 0
  have hle1 :
      SuccinctClose.bpWordChunkSliceLen 1
          ([true, false] : List Bool).length 1 <= 1 :=
    SuccinctClose.bpWordChunkSliceLen_le 1 _ 1
  have hreadVal0 :
      (SuccinctClose.bpChunkReadTraceResult
          (concreteBPNativeSuccinctRMQGlobalReadStore
            (Cartesian.shape reviewerSingletonInput))
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot 1
            (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 0)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 0))).value =
        some
          (SuccinctClose.bpFringeChunkPacked 1
            (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 0)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 0)) := by
    show ((concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot _ _ _ _)).map
        SuccinctSpace.bitsToNatLE = _
    rw [hfringe]
    rw [(SuccinctClose.bpFringeChunkTable 1).read_exact]
    exact SuccinctClose.bpFringeChunkEntries_getElem hv0 hle0 hle0
  have hreadVal1 :
      (SuccinctClose.bpChunkReadTraceResult
          (concreteBPNativeSuccinctRMQGlobalReadStore
            (Cartesian.shape reviewerSingletonInput))
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot 1
            (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 1)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 1))).value =
        some
          (SuccinctClose.bpFringeChunkPacked 1
            (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 1)
            (SuccinctClose.bpWordChunkSliceLen 1
              ([true, false] : List Bool).length 1)) := by
    show ((concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
          concreteBPNativeFringeChunkTraceSegment
          (SuccinctClose.bpFringeChunkSlot _ _ _ _)).map
        SuccinctSpace.bitsToNatLE = _
    rw [hfringe]
    rw [(SuccinctClose.bpFringeChunkTable 1).read_exact]
    exact SuccinctClose.bpFringeChunkEntries_getElem hv1 hle1 hle1
  have hdec0 :
      SuccinctClose.bpChunkRankOfEntry 1 false 1
        (SuccinctClose.bpFringeChunkPacked 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
          1 1) = 0 := by
    rw [SuccinctClose.bpChunkRankOfEntry_packed 1 false hv0
      (Nat.le_refl 1)]
    decide
  have hdec1 :
      SuccinctClose.bpChunkRankOfEntry 1 false 1
        (SuccinctClose.bpFringeChunkPacked 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
          1 1) = 1 := by
    rw [SuccinctClose.bpChunkRankOfEntry_packed 1 false hv1
      (Nat.le_refl 1)]
    decide
  have hselEntry :
      (SuccinctClose.bpChunkSelectEntries 1 false)[
        SuccinctClose.bpChunkSelectSlot 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1) 0]? =
        some (SuccinctClose.bpChunkSelectPos 1 false
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1) 0) :=
    SuccinctClose.bpChunkSelectEntries_getElem false hv1 (by omega)
  rcases fixedWidthNatTable_word_of_entry
      (SuccinctClose.bpChunkSelectTable 1 false) _ hselEntry with
    ⟨word22, hword22⟩
  have hsel22 :
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
          concreteBPNativeSelectChunkTraceSegment
          (SuccinctClose.bpChunkSelectSlot 1
            (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
            0) = some word22 := by
    rw [hselect]
    exact hword22
  refine ⟨SuccinctClose.bpChunkSelectSlot 1
      (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1) 0,
    word22, ?_⟩
  unfold SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
  have hcount :
      SuccinctClose.bpWordChunkCount 1
        ([true, false] : List Bool).length = 2 := by
    decide
  rw [hcount]
  show WordRAM.TraceEvent.readWord _ _ _ ∈
    (WordRAM.TraceResult.bind
      (SuccinctClose.bpChunkReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape reviewerSingletonInput))
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.bpFringeChunkSlot 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 0)
          (SuccinctClose.bpWordChunkSliceLen 1
            ([true, false] : List Bool).length 0)
          (SuccinctClose.bpWordChunkSliceLen 1
            ([true, false] : List Bool).length 0)))
      _).trace
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hreadVal0]
  dsimp only
  rw [if_neg (by
    simp only [Option.getD_some]
    rw [ht0, hdec0]
    omega)]
  simp only [Option.getD_some, ht0, hdec0, Nat.sub_zero]
  show WordRAM.TraceEvent.readWord _ _ _ ∈
    (WordRAM.TraceResult.bind
      (SuccinctClose.bpChunkReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore
          (Cartesian.shape reviewerSingletonInput))
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.bpFringeChunkSlot 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
          (SuccinctClose.bpWordChunkSliceLen 1
            ([true, false] : List Bool).length 1)
          (SuccinctClose.bpWordChunkSliceLen 1
            ([true, false] : List Bool).length 1)))
      _).trace
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hreadVal1]
  dsimp only
  rw [if_pos (by
    simp only [Option.getD_some]
    rw [ht1, hdec1]
    omega)]
  rw [WordRAM.TraceResult.map_trace]
  rw [show (SuccinctClose.bpChunkReadTraceResult
      (concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput))
      concreteBPNativeSelectChunkTraceSegment
      (SuccinctClose.bpChunkSelectSlot 1
        (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
        0)).trace =
    [WordRAM.TraceEvent.readWord concreteBPNativeSelectChunkTraceSegment
      (SuccinctClose.bpChunkSelectSlot 1
        (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1) 0)
      (some word22)] from by
    show [WordRAM.TraceEvent.readWord _ _
      ((concreteBPNativeSuccinctRMQGlobalReadStore
        (Cartesian.shape reviewerSingletonInput)).readWord?
        concreteBPNativeSelectChunkTraceSegment
        (SuccinctClose.bpChunkSelectSlot 1
          (SuccinctClose.bpFringeWindowChunkValue 1 [true, false] 1)
          0))] = _
    rw [hsel22]]
  exact List.Mem.head _

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
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) =
      data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) :=
    canonicalSuperTableWithStore_eq shape _
  have hlocalWS :
      data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) =
      data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) :=
    canonicalLocalTableWithStore_eq shape _
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperWS, hsuperSlot]
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
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    apply chunkedSelectTrace_super_read_mem data layout _ _ _ _ 0 hvalid
    rw [hsuperWS, hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h1
  · change .readWord 2 0 (some word2) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    apply chunkedSelectTrace_super_read_mem data layout _ _ _ _ 0 hvalid
    rw [hsuperWS, hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h2
  · change .readWord 3 0 (some word3) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    apply chunkedSelectTrace_super_read_mem data layout _ _ _ _ 0 hvalid
    rw [hsuperWS, hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h3
  · change .readWord 4 0 (some word4) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    apply chunkedSelectTrace_super_read_mem data layout _ _ _ _ 0 hvalid
    rw [hsuperWS, hsuperSlot]
    simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h4
  · change .readWord 5 0 (some word5) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    exact chunkedSelectTrace_local_read_mem data layout _ _ _ _ 0 hvalid
      super hsuperValue hshort (by
        rw [hlocalWS, hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h5)
  · change .readWord 6 0 (some word6) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    exact chunkedSelectTrace_local_read_mem data layout _ _ _ _ 0 hvalid
      super hsuperValue hshort (by
        rw [hlocalWS, hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h6)
  · change .readWord 7 0 (some word7) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    exact chunkedSelectTrace_local_read_mem data layout _ _ _ _ 0 hvalid
      super hsuperValue hshort (by
        rw [hlocalWS, hlocalSlot]
        simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout] using h7)
  · change .readWord 8 0 (some word8) ∈
      (data.bpChunkedSelectTraceResultWithStore layout
        concreteBPNativeFringeChunkTraceSegment
        concreteBPNativeSelectChunkTraceSegment
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
    exact chunkedSelectTrace_local_read_mem data layout _ _ _ _ 0 hvalid
      super hsuperValue hshort (by
        rw [hlocalWS, hlocalSlot]
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
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) =
      data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) :=
    canonicalSuperTableWithStore_eq shape _
  have hlocalWS :
      data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) =
      data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) :=
    canonicalLocalTableWithStore_eq shape _
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperWS, hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
        some loc := by
    rw [hlocalWS, hlocalSlot]
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
  have hstoreWord :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        layout.bitWordBase
        (GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc / data.wordSize) = some [true, false] := by
    rw [hfirstIndex]
    show (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 0 =
      some [true, false]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
    dsimp only [shape]
    rw [reviewerSingletonInput_bpCode]
    simp [SuccinctSpace.chunkPayloadWords,
      SuccinctSpace.chunkPayloadWordsFuel,
      SuccinctRank.machineWordBits, reviewerSingleton_log2_two]
  change .readWord 0 0 (some [true, false]) ∈
    (data.bpChunkedSelectTraceResultWithStore layout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
  apply chunkedSelectTrace_dense_read_mem data layout _ _ _ _ 0 hvalid
    super loc hsuperValue hshort hlocalValue hdense
  have hdenseMem := chunkedDenseTwoWordSelect_first_successful_read
    layout.bitWordBase concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false
    data.bitWords
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (GenericSelect.relativeSplitSelectLocalBasePosition
      data.wordSize super loc)
    (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
    (data.queryOccurrence 0) [true, false] hstoreWord
  simpa [layout, concreteBPNativeSelectCloseTraceSegmentLayout,
    hfirstIndex] using hdenseMem

/--
W19 for the select chunk table: the singleton whole-query select leg's
dense route actually issues a SUCCESSFUL segment-`22` read (the found
branch of the chunked in-word select on the shared word `[true, false]`).
-/
private theorem reviewerSingleton_selectChunkTable_successful_read :
    ∃ index word,
      .readWord concreteBPNativeSelectChunkTraceSegment index (some word) ∈
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
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) =
      data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) :=
    canonicalSuperTableWithStore_eq shape _
  have hlocalWS :
      data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) =
      data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) :=
    canonicalLocalTableWithStore_eq shape _
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperWS, hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
        some loc := by
    rw [hlocalWS, hlocalSlot]
    simpa [hlocalEntry] using
      denseEntryTable_trace_value data.localTable layout.localTable 0
  have hshort :
      GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
    simpa [super, shape] using reviewerSingleton_super_not_marked
  have hdense :
      GenericSelect.relativeSplitSelectEntryIsMarked loc = false := by
    simpa [loc, shape] using reviewerSingleton_local_not_marked
  have hbasePos :
      GenericSelect.relativeSplitSelectLocalBasePosition
        data.wordSize super loc = 1 := by
    simpa [data, super, loc, shape,
      GenericSelect.sparseExceptionSelectData] using
      reviewerSingleton_dense_base_position
  have hbaseOcc :
      GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc = 0 := by
    simpa [super, loc, shape] using
      reviewerSingleton_dense_base_occurrence
  have hfirstIndex :
      GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc / data.wordSize = 0 := by
    simpa [data, super, loc, shape,
      GenericSelect.sparseExceptionSelectData] using
      reviewerSingleton_dense_first_word_index
  rw [hbasePos] at hfirstIndex
  have hq0 : data.queryOccurrence 0 = 0 := rfl
  have hcb : SuccinctClose.bpFringeChunkBits shape.bpCode.length = 1 :=
    reviewerSingleton_chunkBits
  have hfringe : forall address,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeFringeChunkTraceSegment address =
        (SuccinctClose.bpFringeChunkTable 1).store.words[address]? := by
    intro address
    have h := concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable
      shape address
    rwa [hcb] at h
  have hword0 :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        layout.bitWordBase 0 = some [true, false] := by
    show (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 0 =
      some [true, false]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
    dsimp only [shape]
    rw [reviewerSingletonInput_bpCode]
    simp [SuccinctSpace.chunkPayloadWords,
      SuccinctSpace.chunkPayloadWordsFuel,
      SuccinctRank.machineWordBits, reviewerSingleton_log2_two]
  have hbefore :
      (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeFringeChunkTraceSegment 1 false
        [true, false] 1).value = 0 := by
    have h :=
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
        (SuccinctClose.bpFringeChunkTable 1) hfringe 1 false
        [true, false] 1
    have hv := congrArg Costed.value h
    rw [WordRAM.TraceResult.toCosted_value] at hv
    rw [hv, SuccinctClose.bpChunkedWordRankCosted_value 1 (by omega) false
      [true, false] 1 (by simp)]
    decide
  have hupto :
      (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeFringeChunkTraceSegment 1 false
        [true, false] ([true, false] : List Bool).length).value = 1 := by
    have h :=
      SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
        (SuccinctClose.bpFringeChunkTable 1) hfringe 1 false
        [true, false] ([true, false] : List Bool).length
    have hv := congrArg Costed.value h
    rw [WordRAM.TraceResult.toCosted_value] at hv
    rw [hv, SuccinctClose.bpChunkedWordRankCosted_value 1 (by omega) false
      [true, false] ([true, false] : List Bool).length (by simp)]
    decide
  obtain ⟨index22, word22, hfold⟩ :=
    reviewerSingleton_inWordSelect_selectTable_read
  refine ⟨index22, word22, ?_⟩
  change .readWord concreteBPNativeSelectChunkTraceSegment index22
      (some word22) ∈
    (data.bpChunkedSelectTraceResultWithStore layout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
  apply chunkedSelectTrace_dense_read_mem data layout _ _ _ _ 0 hvalid
    super loc hsuperValue hshort hlocalValue hdense
  rw [hbasePos, hbaseOcc, hq0, hcb]
  unfold GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
  simp only [hfirstIndex, Nat.zero_mul, Nat.sub_zero, Nat.zero_sub,
    Nat.add_zero, Nat.zero_add]
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [show (SuccinctClose.bpWordReadTraceResult
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      layout.bitWordBase 0).value =
    some [true, false] from hword0]
  dsimp only
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hbefore]
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hupto]
  simp only [Nat.sub_zero, Nat.add_zero, Nat.zero_add]
  rw [if_pos (show (0 : Nat) < 1 by decide)]
  rw [WordRAM.TraceResult.map_trace]
  simpa using hfold

/--
W19 for the fringe chunk table on the SELECT leg: the singleton whole-query
select leg's dense route actually issues a SUCCESSFUL segment-`21` read.
The dense two-word component's before-rank chunk fold on the shared word
`[true, false]` reads the fringe chunk table at a row-count-bounded slot,
and the read succeeds because the slot is inside the counted table.
-/
private theorem reviewerSingleton_selectClose_fringeChunk_successful_read :
    ∃ index word,
      .readWord concreteBPNativeFringeChunkTraceSegment index (some word) ∈
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
  have hsuperWS :
      data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) =
      data.superTable.readTraceResultRelabeled layout.superTable
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride) :=
    canonicalSuperTableWithStore_eq shape _
  have hlocalWS :
      data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) =
      data.localTable.readTraceResultRelabeled layout.localTable
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super) :=
    canonicalLocalTableWithStore_eq shape _
  have hsuperValue :
      (data.superTable.readTraceResultRelabeledWithStore layout.superTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.selectSuperSlot
          (data.queryOccurrence 0) data.superStride)).value = some super := by
    rw [hsuperWS, hsuperSlot]
    simpa [hsuperEntry] using
      denseEntryTable_trace_value data.superTable layout.superTable 0
  have hlocalValue :
      (data.localTable.readTraceResultRelabeledWithStore layout.localTable
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.relativeSplitSelectLocalSlot
          (data.queryOccurrence 0) data.superStride
          data.localSlotsPerSuper data.localStride super)).value =
        some loc := by
    rw [hlocalWS, hlocalSlot]
    simpa [hlocalEntry] using
      denseEntryTable_trace_value data.localTable layout.localTable 0
  have hshort :
      GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
    simpa [super, shape] using reviewerSingleton_super_not_marked
  have hdense :
      GenericSelect.relativeSplitSelectEntryIsMarked loc = false := by
    simpa [loc, shape] using reviewerSingleton_local_not_marked
  have hbasePos :
      GenericSelect.relativeSplitSelectLocalBasePosition
        data.wordSize super loc = 1 := by
    simpa [data, super, loc, shape,
      GenericSelect.sparseExceptionSelectData] using
      reviewerSingleton_dense_base_position
  have hbaseOcc :
      GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc = 0 := by
    simpa [super, loc, shape] using
      reviewerSingleton_dense_base_occurrence
  have hfirstIndex :
      GenericSelect.relativeSplitSelectLocalBasePosition
          data.wordSize super loc / data.wordSize = 0 := by
    simpa [data, super, loc, shape,
      GenericSelect.sparseExceptionSelectData] using
      reviewerSingleton_dense_first_word_index
  rw [hbasePos] at hfirstIndex
  have hq0 : data.queryOccurrence 0 = 0 := rfl
  have hcb : SuccinctClose.bpFringeChunkBits shape.bpCode.length = 1 :=
    reviewerSingleton_chunkBits
  have hfringe : forall address,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeFringeChunkTraceSegment address =
        (SuccinctClose.bpFringeChunkTable 1).store.words[address]? := by
    intro address
    have h := concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable
      shape address
    rwa [hcb] at h
  have hword0 :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        layout.bitWordBase 0 = some [true, false] := by
    show (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 0 =
      some [true, false]
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_bpCode]
    dsimp only [shape]
    rw [reviewerSingletonInput_bpCode]
    simp [SuccinctSpace.chunkPayloadWords,
      SuccinctSpace.chunkPayloadWordsFuel,
      SuccinctRank.machineWordBits, reviewerSingleton_log2_two]
  obtain ⟨index21, word21, hfold⟩ :=
    reviewerFringeChunk_rankFold_first_successful_read hfringe false
      [true, false] 1
  refine ⟨index21, word21, ?_⟩
  change .readWord concreteBPNativeFringeChunkTraceSegment index21
      (some word21) ∈
    (data.bpChunkedSelectTraceResultWithStore layout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) 0).trace
  apply chunkedSelectTrace_dense_read_mem data layout _ _ _ _ 0 hvalid
    super loc hsuperValue hshort hlocalValue hdense
  rw [hbasePos, hbaseOcc, hq0, hcb]
  unfold GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
  simp only [hfirstIndex, Nat.zero_mul, Nat.sub_zero, Nat.zero_sub,
    Nat.add_zero, Nat.zero_add]
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [show (SuccinctClose.bpWordReadTraceResult
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      layout.bitWordBase 0).value =
    some [true, false] from hword0]
  dsimp only
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_left
  exact hfold

private theorem reviewerSingleton_select_value :
    (concreteBPNativeSelectCloseGlobalWordTraceResult
      (Cartesian.shape reviewerSingletonInput) 0).value = some 1 := by
  have href :=
    concreteBPNativeSelectCloseGlobalWordTraceResult_refines_interpretedCosted
      (Cartesian.shape reviewerSingletonInput) 0
  have hexact :=
    concreteBPNativeSelectCloseInterpretedCosted_exact
      (Cartesian.shape reviewerSingletonInput) 0
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerSingletonInput) 0).value = some 1 := by
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
        Succinct.rankPrefix false shape.bpCode pos :=
    fun pos => concreteBPNativeRankCloseInterpretedCosted_exact shape pos
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

private def reviewerSingletonBeforeLCA : WholeQueryProgram :=
  [ WholeQueryInstr.selectClose .leftClose .inputLeft
  , WholeQueryInstr.selectClose .rightClose
      (.sub .inputRight (.const 1))
  ]

private def reviewerSingletonBeforeLCAState : WholeQueryState :=
  (WholeQueryProgram.evalGlobalWordTrace
    (Cartesian.shape reviewerSingletonInput) 0 1 reviewerSingletonBeforeLCA
    WholeQueryState.empty).value

private theorem reviewerSingletonBeforeLCAState_closes :
    reviewerSingletonBeforeLCAState.opt .leftClose = some 1 ∧
      reviewerSingletonBeforeLCAState.opt .rightClose = some 1 := by
  simp [reviewerSingletonBeforeLCAState, reviewerSingletonBeforeLCA,
    WholeQueryProgram.evalGlobalWordTrace,
    WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
    reviewerSingleton_select_value, WholeQueryState.empty,
    WholeQueryState.setOpt, WholeQueryState.opt]

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

private theorem reviewerSingleton_rank_successful_claims :
    (ReviewerProducerClaim.mk 17 .rankClose).HasSuccessfulClosedValidOccurrence /\
    (ReviewerProducerClaim.mk 18 .rankClose).HasSuccessfulClosedValidOccurrence /\
    (ReviewerProducerClaim.mk 19 .rankClose).HasSuccessfulClosedValidOccurrence := by
  let shape := Cartesian.shape reviewerSingletonInput
  let data := builtRelativeSplitBPCloseRankData shape
  have hq : data.queryPos 2 <= shape.bpCode.length := Nat.min_le_right _ _
  rcases data.super_present false (data.queryPos 2) hq with ⟨sample, hsample⟩
  have hsuperWordEx :
      exists word,
        ((data.superSampleWords false)[data.superIndex 2]?) = some word := by
    apply fixedWidthNatTable_word_of_entry data.superTables.falseTable
    simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex] using
      hsample
  rcases data.block_present false (data.queryPos 2) hq with ⟨delta, hdelta⟩
  have hblockWordEx :
      exists word,
        ((data.blockSampleWords false)[data.wordIndex 2]?) = some word := by
    apply fixedWidthNatTable_word_of_entry data.blockTables.falseTable
    simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex] using
      hdelta
  rcases data.word_present (data.queryPos 2) hq with ⟨wordBits, hwordBits⟩
  rcases hsuperWordEx with ⟨superWord, hsuperWord⟩
  rcases hblockWordEx with ⟨blockWord, hblockWord⟩
  have hsuperRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeRankCloseTraceSegmentBase (data.superIndex 2) =
        some superWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper]
    exact hsuperWord
  have hblockRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 1)
          (data.wordIndex 2) =
        some blockWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock]
    exact hblockWord
  have hwordRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 2)
          (data.wordIndex 2) =
        some wordBits := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord]
    exact hwordBits
  have hchunkReads := chunkedRankTraceWithStore_successful_reads data
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    concreteBPNativeRankCloseTraceSegmentBase
    (concreteBPNativeRankCloseTraceSegmentBase + 1)
    (concreteBPNativeRankCloseTraceSegmentBase + 2)
    concreteBPNativeFringeChunkTraceSegment
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false 2
    hsuperRead hblockRead hwordRead
  have hcanon :=
    concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq shape 2
  have hreads :
      (exists index word,
        .readWord concreteBPNativeRankCloseTraceSegmentBase index
            (some word) ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase 2).trace) /\
      (exists index word,
        .readWord (concreteBPNativeRankCloseTraceSegmentBase + 1) index
            (some word) ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase 2).trace) /\
      (exists index word,
        .readWord (concreteBPNativeRankCloseTraceSegmentBase + 2) index
            (some word) ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegment shape
            concreteBPNativeRankCloseTraceSegmentBase 2).trace) := by
    rcases hchunkReads with ⟨h17, h18, h19⟩
    refine ⟨⟨data.superIndex 2, superWord, ?_⟩,
      ⟨data.wordIndex 2, blockWord, ?_⟩,
      ⟨data.wordIndex 2, wordBits, ?_⟩⟩
    · rw [hcanon]
      exact h17
    · rw [hcanon]
      exact h18
    · rw [hcanon]
      exact h19
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

/--
W19 for the fringe chunk table on the RANK leg: the singleton whole-query
final-rank component at position `2` reaches the charged in-word chunk fold
after its three successful seed reads (segments `17`/`18`/`19`), and the
fold's first segment-`21` chunk read succeeds because the visited slot is
inside the counted fringe chunk table.
-/
private theorem reviewerSingleton_rankClose_fringeChunk_successful_read :
    ∃ index word,
      .readWord concreteBPNativeFringeChunkTraceSegment index (some word) ∈
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          (Cartesian.shape reviewerSingletonInput)
          concreteBPNativeRankCloseTraceSegmentBase 2).trace := by
  let shape := Cartesian.shape reviewerSingletonInput
  let data := builtRelativeSplitBPCloseRankData shape
  have hq : data.queryPos 2 <= shape.bpCode.length := Nat.min_le_right _ _
  rcases data.super_present false (data.queryPos 2) hq with ⟨sample, hsample⟩
  have hsuperWordEx :
      exists word,
        ((data.superSampleWords false)[data.superIndex 2]?) = some word := by
    apply fixedWidthNatTable_word_of_entry data.superTables.falseTable
    simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex] using
      hsample
  rcases data.block_present false (data.queryPos 2) hq with ⟨delta, hdelta⟩
  have hblockWordEx :
      exists word,
        ((data.blockSampleWords false)[data.wordIndex 2]?) = some word := by
    apply fixedWidthNatTable_word_of_entry data.blockTables.falseTable
    simpa [SuccinctSpace.FixedWidthRankSampleTables.entries,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex] using
      hdelta
  rcases data.word_present (data.queryPos 2) hq with ⟨wordBits, hwordBits⟩
  rcases hsuperWordEx with ⟨superWord, hsuperWord⟩
  rcases hblockWordEx with ⟨blockWord, hblockWord⟩
  have hsuperRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeRankCloseTraceSegmentBase (data.superIndex 2) =
        some superWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper]
    exact hsuperWord
  have hblockRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 1)
          (data.wordIndex 2) =
        some blockWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock]
    exact hblockWord
  have hwordRead :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 2)
          (data.wordIndex 2) =
        some wordBits := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord]
    exact hwordBits
  have hsuperVal :
      (SuccinctClose.bpChunkReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase (data.superIndex 2)).value =
      some (SuccinctSpace.bitsToNatLE superWord) :=
    congrArg (Option.map SuccinctSpace.bitsToNatLE) hsuperRead
  have hblockVal :
      (SuccinctClose.bpChunkReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (concreteBPNativeRankCloseTraceSegmentBase + 1)
        (data.wordIndex 2)).value =
      some (SuccinctSpace.bitsToNatLE blockWord) :=
    congrArg (Option.map SuccinctSpace.bitsToNatLE) hblockRead
  have hwordVal :
      (SuccinctClose.bpWordReadTraceResult
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (concreteBPNativeRankCloseTraceSegmentBase + 2)
        (data.wordIndex 2)).value = some wordBits :=
    hwordRead
  obtain ⟨index21, word21, hfold⟩ :=
    reviewerFringeChunk_rankFold_first_successful_read
      (concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable shape)
      false wordBits (data.wordOffset 2)
  refine ⟨index21, word21, ?_⟩
  show .readWord concreteBPNativeFringeChunkTraceSegment index21
      (some word21) ∈
    (concreteBPNativeRankCloseWordTraceResultAtSegment shape
      concreteBPNativeRankCloseTraceSegmentBase 2).trace
  rw [concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq shape 2]
  show .readWord concreteBPNativeFringeChunkTraceSegment index21
      (some word21) ∈
    (data.bpChunkedRankTraceResultWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeRankCloseTraceSegmentBase
      (concreteBPNativeRankCloseTraceSegmentBase + 1)
      (concreteBPNativeRankCloseTraceSegmentBase + 2)
      concreteBPNativeFringeChunkTraceSegment
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false 2).trace
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hsuperVal]
  try dsimp only
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hblockVal]
  try dsimp only
  rw [WordRAM.TraceResult.bind_trace]
  apply List.mem_append_right
  rw [hwordVal]
  try dsimp only
  rw [WordRAM.TraceResult.map_trace]
  exact hfold

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
    concreteBPNativeSelectCloseInterpretedCosted_exact
      (Cartesian.shape reviewerIncreasingSixteenInput) 0
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerIncreasingSixteenInput) 0).value = some 1 := by
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
    concreteBPNativeSelectCloseInterpretedCosted_exact
      (Cartesian.shape reviewerIncreasingSixteenInput) 15
  have hinterpreted :
      (concreteBPNativeSelectCloseInterpretedCosted
        (Cartesian.shape reviewerIncreasingSixteenInput) 15).value =
          some 31 := by
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
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
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
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  apply List.mem_append_right
  apply List.mem_append_left
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_window_mem
      (Cartesian.shape reviewerIncreasingSixteenInput)
      concreteBPNativeFringeChunkTraceSegment 10 1 _ hwindow

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

private theorem reviewerIncreasing_lca_fringe_successful_mem :
    ∃ index word,
      List.Mem
        (.readWord concreteBPNativeFringeChunkTraceSegment index (some word))
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          (Cartesian.shape reviewerIncreasingSixteenInput) 1 31).trace := by
  rcases
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_fringe_successful_mayRead
        (Cartesian.shape reviewerIncreasingSixteenInput)
        concreteBPNativeFringeChunkTraceSegment 10 1
        ((SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
          (Cartesian.shape reviewerIncreasingSixteenInput)
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            (Cartesian.shape reviewerIncreasingSixteenInput)
            concreteBPNativeRankCloseTraceSegmentBase) 10 1).value) with
    ⟨index, word, hmem⟩
  refine ⟨index, word, ?_⟩
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
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  rw [hblock]
  simp only [SuccinctClose.blockOfClose]
  simp
  apply List.mem_append_right
  apply List.mem_append_left
  exact hmem

private theorem reviewerIncreasing_fringe_successful_claim :
    (ReviewerProducerClaim.mk concreteBPNativeFringeChunkTraceSegment
      .canonicalClose).HasSuccessfulClosedValidOccurrence := by
  rcases reviewerIncreasing_lca_fringe_successful_mem with
    ⟨index, word, hmem⟩
  exact reviewerIncreasing_canonical_successful_claim_of_mem hmem

/--
W19 aggregate for the fringe chunk table (segment `21` =
`concreteBPNativeFringeChunkTraceSegment`): EVERY reader leaf — select,
rank, and LCA/canonical close — has a successful closed valid occurrence of
the `(21, leaf)` producer claim.  The shared table's multi-consumer story is
therefore fully witnessed operationally, not only through the compat
primary-consumer label `canonicalClose`.
-/
theorem concreteBPNativeSuccinctRMQFringeChunkTable_every_reader_leaf_successful_occurrence :
    ∀ leaf : ReviewerReadLeaf,
      (ReviewerProducerClaim.mk concreteBPNativeFringeChunkTraceSegment
        leaf).HasSuccessfulClosedValidOccurrence := by
  intro leaf
  cases leaf with
  | selectClose =>
      rcases reviewerSingleton_selectClose_fringeChunk_successful_read with
        ⟨index, word, hmem⟩
      rcases List.mem_iff_getElem?.mp hmem with ⟨localPos, hget⟩
      apply reviewerClaim_successful_of_local_get reviewerSingletonInput
        0 1 concreteBPNativeFringeChunkTraceSegment index word .selectClose []
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
      · simpa [WholeQueryInstr.evalGlobalWordTrace,
          WholeQueryNatExpr.eval] using hget
      · exact WholeQueryInstr.InvokesReviewerRead.selectClose
          .leftClose .inputLeft
      · rfl
      · simpa [ReviewerReadInvocation.componentTrace] using hget
  | rankClose =>
      rcases reviewerSingleton_rankClose_fringeChunk_successful_read with
        ⟨index, word, hmem⟩
      rcases List.mem_iff_getElem?.mp hmem with ⟨localPos, hget⟩
      apply reviewerClaim_successful_of_local_get reviewerSingletonInput
        0 1 concreteBPNativeFringeChunkTraceSegment index word .rankClose
        reviewerSingletonBeforeRank
        [WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank]
        (WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
          (.add (.optNatD .answerClose 0) (.const 1)))
        reviewerSingletonBeforeRankState localPos (.rankClose 2)
      · simp [ValidRange, reviewerSingletonInput]
      · rfl
      · rfl
      · simpa [WholeQueryInstr.evalGlobalWordTrace,
          reviewerSingletonBeforeRankState_answerClose,
          WholeQueryNatExpr.eval] using hget
      · simpa [WholeQueryNatExpr.eval,
          reviewerSingletonBeforeRankState_answerClose] using
          (WholeQueryInstr.InvokesReviewerRead.rankClose
            (left := 0) (right := 1) .closeRank .answerClose
            (.add (.optNatD .answerClose 0) (.const 1)) 1
            reviewerSingletonBeforeRankState_answerClose)
      · rfl
      · simpa [ReviewerReadInvocation.componentTrace] using hget
  | canonicalClose =>
      exact reviewerIncreasing_fringe_successful_claim

/-- A complete occurrence receipt whose producing instruction position is an
explicit parameter instead of an existential hidden inside the receipt. -/
def ReviewerReadOccurrenceReceiptAtInstruction
    (shape : Cartesian.CartesianShape)
    (left right globalPos instrPos segment index : Nat)
    (word? : Option WordRAM.Word) : Prop :=
  ∃ source : ReviewerSource,
  ∃ instr : WholeQueryInstr,
  ∃ preState : WholeQueryState,
  ∃ localPos : Nat,
  ∃ invocation : ReviewerReadInvocation,
    WholeQueryProgram.ProducesEventAt shape left right
      (.readWord segment index word?)
      concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
      globalPos instrPos instr preState localPos ∧
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
      some source ∧
    concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
      some source.region ∧
    instr.InvokesReviewerRead left right preState invocation ∧
    (invocation.componentTrace shape)[localPos]? =
      some (.readWord segment index word?) ∧
    ReviewerProducerReadPath shape invocation.leaf segment index word? ∧
    source.Counted

private theorem reviewerReadOccurrenceReceiptAtInstruction_of_producer
    {shape : Cartesian.CartesianShape}
    {left right globalPos instrPos segment index : Nat}
    {word? : Option WordRAM.Word}
    {instr : WholeQueryInstr} {preState : WholeQueryState} {localPos : Nat}
    (hproducer :
      WholeQueryProgram.ProducesEventAt shape left right
        (.readWord segment index word?)
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        globalPos instrPos instr preState localPos) :
    ReviewerReadOccurrenceReceiptAtInstruction shape left right globalPos
      instrPos segment index word? := by
  have hglobalGet := hproducer.global_getElem
  rcases hproducer with
    ⟨before, after, hprogram, hinstrPos, hpreState, hglobalPos, hlocalGet⟩
  rcases WholeQueryInstr.evalGlobalWordTrace_getElem?_read_invocation
      shape left right instr preState localPos segment index word? hlocalGet with
    ⟨invocation, hinvocation, hinvocationGet⟩
  have hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace := by
    apply List.mem_of_getElem?
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using
      hglobalGet
  have hsegment : segment < 23 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      shape left right hmem
  rcases (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2
      hsegment with ⟨source, hsource⟩
  have hregion :
      concreteBPNativeSuccinctRMQReviewerSegmentRegion? segment =
        some source.region := by
    simp [concreteBPNativeSuccinctRMQReviewerSegmentRegion?, hsource]
  rcases WholeQueryInstr.evalGlobalWordTrace_read_producer_path
      shape left right instr preState (List.mem_of_getElem? hlocalGet) with
    ⟨leaf, hleaf, hpath⟩
  have hinvocationLeaf := hinvocation.reviewerReadLeaf?_eq
  have hleafEq : leaf = invocation.leaf := by
    rw [hleaf] at hinvocationLeaf
    exact Option.some.inj hinvocationLeaf
  subst leaf
  refine ⟨source, instr, preState, localPos, invocation,
    ⟨before, after, hprogram, hinstrPos, hpreState, hglobalPos, hlocalGet⟩,
    hsource, hregion, hinvocation, hinvocationGet, hpath, ?_⟩
  exact concreteBPNativeSuccinctRMQReviewerSegmentSource_counted hsource

/-- A valid singleton whole query reaches the charged SAME-BLOCK LCA arm and
emits an indexed segment-21 read.  The same local position is exhibited both
in the LCA invocation trace and in the charged same-block decoded subtrace,
and global instruction position `2` carries the complete occurrence receipt. -/
theorem concreteBPNativeSuccinctRMQSingleton_sameBlockFringeChunk_indexed_occurrence_receipt :
    ∃ xs : List Int,
    ∃ globalPos localPos index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs 0 1 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) 0 1).trace[globalPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) 0 1 globalPos
        concreteBPNativeFringeChunkTraceSegment index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        0 1 globalPos 2 concreteBPNativeFringeChunkTraceSegment index
        (some word) ∧
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        (Cartesian.shape xs) 1 1).trace[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment
        (Cartesian.shape xs)
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          (Cartesian.shape xs) concreteBPNativeRankCloseTraceSegmentBase)
        concreteBPNativeFringeChunkTraceSegment
        (SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
          (Cartesian.shape xs)) 1 1).trace[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) := by
  let shape := Cartesian.shape reviewerSingletonInput
  let rankTrace := concreteBPNativeRankCloseWordTraceResultAtSegment
    shape concreteBPNativeRankCloseTraceSegmentBase
  let blockSize :=
    SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  rcases
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment_fringe_successful_mayRead
        shape rankTrace concreteBPNativeFringeChunkTraceSegment
        blockSize 1 1 with
    ⟨index, word, hsameMem⟩
  rcases List.mem_iff_getElem?.mp hsameMem with ⟨localPos, hsameGet⟩
  have hcomponentGet :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape 1 1).trace[localPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) := by
    have hsame :
        SuccinctClose.blockOfClose blockSize 1 =
          SuccinctClose.blockOfClose blockSize 1 := rfl
    unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
    unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural
    simp only [hsame, if_pos]
    simpa [rankTrace, blockSize] using hsameGet
  have hcloses := reviewerSingletonBeforeLCAState_closes
  have hlocal :
      ((WholeQueryInstr.lcaClose .answerClose .leftClose
        .rightClose).evalGlobalWordTrace shape 0 1
          reviewerSingletonBeforeLCAState).trace[localPos]? =
        some (.readWord concreteBPNativeFringeChunkTraceSegment index
          (some word)) := by
    simpa [WholeQueryInstr.evalGlobalWordTrace, hcloses.1, hcloses.2] using
      hcomponentGet
  let globalPos :=
    (WholeQueryProgram.evalGlobalWordTrace shape 0 1
      reviewerSingletonBeforeLCA WholeQueryState.empty).trace.length + localPos
  have hprogram : concreteBPNativeSuccinctRMQWholeQueryProgram =
      reviewerSingletonBeforeLCA ++
        WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose ::
          [ WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
              (.add (.optNatD .answerClose 0) (.const 1))
          , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
          ] := rfl
  have hproducer :
      WholeQueryProgram.ProducesEventAt shape 0 1
        (.readWord concreteBPNativeFringeChunkTraceSegment index (some word))
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        globalPos 2
        (WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose)
        reviewerSingletonBeforeLCAState localPos := by
    refine ⟨reviewerSingletonBeforeLCA,
      [ WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
          (.add (.optNatD .answerClose 0) (.const 1))
      , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
      ], hprogram, ?_, ?_, ?_, hlocal⟩
    · decide
    · rfl
    · rfl
  have hglobalGet :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape 0 1).trace[globalPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using
      hproducer.global_getElem
  refine ⟨reviewerSingletonInput, globalPos, localPos, index, word,
    by simp [ValidRange, reviewerSingletonInput], hglobalGet,
    concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
      shape 0 1 hglobalGet,
    reviewerReadOccurrenceReceiptAtInstruction_of_producer hproducer,
    hcomponentGet, ?_⟩
  simpa [shape, rankTrace, blockSize] using hsameGet

/--
The singleton query at `left = 0`, `right = 1` runs its two select-close
instructions at the SAME component index `0` (the second instruction's
expression `right - 1 = 0` reads no state registers), so any successful
component read appears at two distinct whole-trace positions, each with its
own complete occurrence receipt.
-/
private theorem reviewerSingleton_selectComponent_repeated_receipts
    {segment index : Nat} {word : WordRAM.Word}
    (hmem : .readWord segment index (some word) ∈
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace) :
    ∃ firstPos secondPos instrPos1 instrPos2 : Nat,
      instrPos1 ≠ instrPos2 ∧ firstPos ≠ secondPos ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0 1).trace[firstPos]? =
          some (.readWord segment index (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0 1).trace[secondPos]? =
          some (.readWord segment index (some word)) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape reviewerSingletonInput)
        0 1 firstPos segment index (some word) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape reviewerSingletonInput)
        0 1 secondPos segment index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction
        (Cartesian.shape reviewerSingletonInput) 0 1 firstPos instrPos1
        segment index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction
        (Cartesian.shape reviewerSingletonInput) 0 1 secondPos instrPos2
        segment index (some word) := by
  rcases List.mem_iff_getElem?.mp hmem with ⟨p, hcompGet⟩
  have hprogram1 : concreteBPNativeSuccinctRMQWholeQueryProgram =
      [] ++ WholeQueryInstr.selectClose .leftClose .inputLeft ::
        [ WholeQueryInstr.selectClose .rightClose
            (.sub .inputRight (.const 1))
        , WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
        , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
            (.add (.optNatD .answerClose 0) (.const 1))
        , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
        ] := rfl
  have hprogram2 : concreteBPNativeSuccinctRMQWholeQueryProgram =
      [WholeQueryInstr.selectClose .leftClose .inputLeft] ++
        WholeQueryInstr.selectClose .rightClose
            (.sub .inputRight (.const 1)) ::
          [ WholeQueryInstr.lcaClose .answerClose .leftClose .rightClose
          , WholeQueryInstr.rankCloseIfSome .closeRank .answerClose
              (.add (.optNatD .answerClose 0) (.const 1))
          , WholeQueryInstr.outputPredIfSome .output .answerClose .closeRank
          ] := rfl
  have hlocal1 :
      ((WholeQueryInstr.selectClose .leftClose
          .inputLeft).evalGlobalWordTrace
        (Cartesian.shape reviewerSingletonInput) 0 1
        WholeQueryState.empty).trace[p]? =
          some (.readWord segment index (some word)) := by
    simpa [WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
      WordRAM.TraceResult.map_trace] using hcompGet
  have htrace2 :
      ((WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1))).evalGlobalWordTrace
        (Cartesian.shape reviewerSingletonInput) 0 1
        (WholeQueryProgram.evalGlobalWordTrace
          (Cartesian.shape reviewerSingletonInput) 0 1
          [WholeQueryInstr.selectClose .leftClose .inputLeft]
          WholeQueryState.empty).value).trace =
        (concreteBPNativeSelectCloseGlobalWordTraceResult
          (Cartesian.shape reviewerSingletonInput) 0).trace := by
    simp [WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
      WordRAM.TraceResult.map_trace]
  have hlocal2 :
      ((WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1))).evalGlobalWordTrace
        (Cartesian.shape reviewerSingletonInput) 0 1
        (WholeQueryProgram.evalGlobalWordTrace
          (Cartesian.shape reviewerSingletonInput) 0 1
          [WholeQueryInstr.selectClose .leftClose .inputLeft]
          WholeQueryState.empty).value).trace[p]? =
          some (.readWord segment index (some word)) := by
    rw [htrace2]
    exact hcompGet
  have hL :
      (WholeQueryProgram.evalGlobalWordTrace
        (Cartesian.shape reviewerSingletonInput) 0 1
        [WholeQueryInstr.selectClose .leftClose .inputLeft]
        WholeQueryState.empty).trace =
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace := by
    simp [WholeQueryProgram.evalGlobalWordTrace,
      WholeQueryInstr.evalGlobalWordTrace, WholeQueryNatExpr.eval,
      WordRAM.TraceResult.bind_trace, WordRAM.TraceResult.map_trace,
      WordRAM.TraceResult.pure]
  have hp : p <
      (concreteBPNativeSelectCloseGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0).trace.length :=
    (List.getElem?_eq_some_iff.mp hcompGet).1
  have hne : p ≠
      (WholeQueryProgram.evalGlobalWordTrace
        (Cartesian.shape reviewerSingletonInput) 0 1
        [WholeQueryInstr.selectClose .leftClose .inputLeft]
        WholeQueryState.empty).trace.length + p := by
    have hlen := congrArg List.length hL
    omega
  have hproducer1 :
      WholeQueryProgram.ProducesEventAt
        (Cartesian.shape reviewerSingletonInput) 0 1
        (.readWord segment index (some word))
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        p 0 (WholeQueryInstr.selectClose .leftClose .inputLeft)
        WholeQueryState.empty p :=
    ⟨[], _, hprogram1, rfl, rfl,
      by simp [WholeQueryProgram.evalGlobalWordTrace,
        WordRAM.TraceResult.pure], hlocal1⟩
  have hproducer2 :
      WholeQueryProgram.ProducesEventAt
        (Cartesian.shape reviewerSingletonInput) 0 1
        (.readWord segment index (some word))
        concreteBPNativeSuccinctRMQWholeQueryProgram WholeQueryState.empty
        ((WholeQueryProgram.evalGlobalWordTrace
          (Cartesian.shape reviewerSingletonInput) 0 1
          [WholeQueryInstr.selectClose .leftClose .inputLeft]
          WholeQueryState.empty).trace.length + p)
        1
        (WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1)))
        (WholeQueryProgram.evalGlobalWordTrace
          (Cartesian.shape reviewerSingletonInput) 0 1
          [WholeQueryInstr.selectClose .leftClose .inputLeft]
          WholeQueryState.empty).value p :=
    ⟨[WholeQueryInstr.selectClose .leftClose .inputLeft], _, hprogram2,
      rfl, rfl, rfl, hlocal2⟩
  have hget1 :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0 1).trace[p]? =
          some (.readWord segment index (some word)) := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using
      hproducer1.global_getElem
  have hget2 :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape reviewerSingletonInput) 0 1).trace[
          (WholeQueryProgram.evalGlobalWordTrace
            (Cartesian.shape reviewerSingletonInput) 0 1
            [WholeQueryInstr.selectClose .leftClose .inputLeft]
            WholeQueryState.empty).trace.length + p]? =
          some (.readWord segment index (some word)) := by
    simpa [concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult] using
      hproducer2.global_getElem
  exact ⟨p,
    (WholeQueryProgram.evalGlobalWordTrace
      (Cartesian.shape reviewerSingletonInput) 0 1
      [WholeQueryInstr.selectClose .leftClose .inputLeft]
      WholeQueryState.empty).trace.length + p,
    0, 1, by omega, hne, hget1, hget2,
    concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
      (Cartesian.shape reviewerSingletonInput) 0 1 hget1,
    concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked
      (Cartesian.shape reviewerSingletonInput) 0 1 hget2,
    reviewerReadOccurrenceReceiptAtInstruction_of_producer hproducer1,
    reviewerReadOccurrenceReceiptAtInstruction_of_producer hproducer2⟩

/--
W19 positional repeated-equal-read witness for the select chunk table
(segment `22` = `concreteBPNativeSelectChunkTraceSegment`): one closed
valid query reads the same successful segment-`22` word at two DIFFERENT
global positions, and each position carries its own complete occurrence
receipt.
-/
theorem concreteBPNativeSuccinctRMQSelectChunk_repeated_equal_read_distinct_receipts :
    ∃ xs : List Int, ∃ left right firstPos secondPos index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧ firstPos ≠ secondPos ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) left right firstPos
        concreteBPNativeSelectChunkTraceSegment index (some word) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) left right secondPos
        concreteBPNativeSelectChunkTraceSegment index (some word) := by
  rcases reviewerSingleton_selectChunkTable_successful_read with
    ⟨index, word, hmem⟩
  rcases reviewerSingleton_selectComponent_repeated_receipts hmem with
    ⟨firstPos, secondPos, _instrPos1, _instrPos2, _hinstrNe, hne,
      hfirst, hsecond, hreceipt1, hreceipt2, _hat1, _hat2⟩
  exact ⟨reviewerSingletonInput, 0, 1, firstPos, secondPos, index, word,
    by simp [ValidRange, reviewerSingletonInput], hne, hfirst, hsecond,
    hreceipt1, hreceipt2⟩

/--
W19 positional repeated-equal-read witness for the fringe chunk table
(segment `21` = `concreteBPNativeFringeChunkTraceSegment`): one closed
valid query reads the same successful segment-`21` word at two DIFFERENT
global positions, and each position carries its own complete occurrence
receipt.
-/
theorem concreteBPNativeSuccinctRMQFringeChunk_repeated_equal_read_distinct_receipts :
    ∃ xs : List Int, ∃ left right firstPos secondPos index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧ firstPos ≠ secondPos ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) left right firstPos
        concreteBPNativeFringeChunkTraceSegment index (some word) ∧
      ReviewerReadOccurrenceReceipt (Cartesian.shape xs) left right secondPos
        concreteBPNativeFringeChunkTraceSegment index (some word) := by
  rcases reviewerSingleton_selectClose_fringeChunk_successful_read with
    ⟨index, word, hmem⟩
  rcases reviewerSingleton_selectComponent_repeated_receipts hmem with
    ⟨firstPos, secondPos, _instrPos1, _instrPos2, _hinstrNe, hne,
      hfirst, hsecond, hreceipt1, hreceipt2, _hat1, _hat2⟩
  exact ⟨reviewerSingletonInput, 0, 1, firstPos, secondPos, index, word,
    by simp [ValidRange, reviewerSingletonInput], hne, hfirst, hsecond,
    hreceipt1, hreceipt2⟩

/-- The repeated singleton select-table read is produced by two distinct
program-instruction positions, not merely emitted at two distinct trace
positions.  Each explicit instruction position carries a complete receipt. -/
theorem concreteBPNativeSuccinctRMQSelectChunk_repeated_equal_read_distinct_instruction_receipts :
    ∃ xs : List Int,
    ∃ left right firstPos secondPos instrPos1 instrPos2 index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧
      firstPos ≠ secondPos ∧ instrPos1 ≠ instrPos2 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeSelectChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right firstPos instrPos1 concreteBPNativeSelectChunkTraceSegment
        index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right secondPos instrPos2 concreteBPNativeSelectChunkTraceSegment
        index (some word) := by
  rcases reviewerSingleton_selectChunkTable_successful_read with
    ⟨index, word, hmem⟩
  rcases reviewerSingleton_selectComponent_repeated_receipts hmem with
    ⟨firstPos, secondPos, instrPos1, instrPos2, hinstrNe, hposNe,
      hfirst, hsecond, _hreceipt1, _hreceipt2, hat1, hat2⟩
  exact ⟨reviewerSingletonInput, 0, 1, firstPos, secondPos, instrPos1,
    instrPos2, index, word, by simp [ValidRange, reviewerSingletonInput],
    hposNe, hinstrNe, hfirst, hsecond, hat1, hat2⟩

/-- The repeated singleton fringe-table read is produced by two distinct
program-instruction positions, not merely emitted at two distinct trace
positions.  Each explicit instruction position carries a complete receipt. -/
theorem concreteBPNativeSuccinctRMQFringeChunk_repeated_equal_read_distinct_instruction_receipts :
    ∃ xs : List Int,
    ∃ left right firstPos secondPos instrPos1 instrPos2 index : Nat,
    ∃ word : WordRAM.Word,
      ValidRange xs left right ∧
      firstPos ≠ secondPos ∧ instrPos1 ≠ instrPos2 ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[firstPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (Cartesian.shape xs) left right).trace[secondPos]? =
          some (.readWord concreteBPNativeFringeChunkTraceSegment index
            (some word)) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right firstPos instrPos1 concreteBPNativeFringeChunkTraceSegment
        index (some word) ∧
      ReviewerReadOccurrenceReceiptAtInstruction (Cartesian.shape xs)
        left right secondPos instrPos2 concreteBPNativeFringeChunkTraceSegment
        index (some word) := by
  rcases reviewerSingleton_selectClose_fringeChunk_successful_read with
    ⟨index, word, hmem⟩
  rcases reviewerSingleton_selectComponent_repeated_receipts hmem with
    ⟨firstPos, secondPos, instrPos1, instrPos2, hinstrNe, hposNe,
      hfirst, hsecond, _hreceipt1, _hreceipt2, hat1, hat2⟩
  exact ⟨reviewerSingletonInput, 0, 1, firstPos, secondPos, instrPos1,
    instrPos2, index, word, by simp [ValidRange, reviewerSingletonInput],
    hposNe, hinstrNe, hfirst, hsecond, hat1, hat2⟩

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
The fourteen always-small reviewer sources have successful occurrences in
real closed valid queries. Source ordinals `1` through `11` and the select
chunk-table source are witnessed by the singleton execution, whose successful
reads include segments `0` through `8`, `17` through `19`, and `22`; the
canonical close source and the fringe chunk-table source are witnessed by
the increasing-length-sixteen cross-block execution (segments `20` and
`21`).
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
      , .canonicalClose
      , .fringeChunkTable
      , .selectChunkTable ]) :
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
  have h21 : ReviewerSource.fringeChunkTable
      |>.HasSuccessfulClosedValidOccurrence :=
    ⟨ReviewerProducerClaim.mk concreteBPNativeFringeChunkTraceSegment
        .canonicalClose, rfl,
      reviewerIncreasing_fringe_successful_claim⟩
  have h22 : ReviewerSource.selectChunkTable
      |>.HasSuccessfulClosedValidOccurrence := by
    obtain ⟨index22, word22, hread22⟩ :=
      reviewerSingleton_selectChunkTable_successful_read
    exact
      reviewerSource_hasSuccessfulClosedValidOccurrence_of_mem
        .selectChunkTable reviewerSingletonInput 0 1
        concreteBPNativeSelectChunkTraceSegment index22 word22
        (by simp [ValidRange, reviewerSingletonInput]) rfl
        (firstSelectClose_read_mem_wholeQuery hread22)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsource
  rcases hsource with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact h21
  · exact h22

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

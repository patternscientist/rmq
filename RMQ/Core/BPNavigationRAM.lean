import RMQ.Core.BPNavigationPublic
import RMQ.Core.SuccinctFinalRAM

/-!
# Word-RAM execution story for concrete BP close navigation

This module adds the RAM replay missing from the public BP close-navigation
profile.  The final RMQ WordRAM layer already supplies the rank-close and
compact close/LCA traces; the extra work here is the relative-split false-select
trace used by `RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile`.
-/

namespace RMQ

namespace SuccinctSelect

namespace FixedWidthSparseDenseFalseSelectDenseLocalEntryTable

/-- Trace-preserving read of a split false-select dense-local entry table. -/
def readTraceResultRelabeled
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    WordRAM.TraceResult (Option SparseDenseFalseSelectDenseLocalEntry) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.relabelReadSegmentsWith
      (WordRAM.singletonSegmentMap layout.baseOccurrence layout.deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.baseOccurrenceTable.readProgram i).eval
          table.baseOccurrenceTable.wordRAMStore)))
    fun baseOccurrence? =>
      WordRAM.TraceResult.bind
        (WordRAM.TraceResult.relabelReadSegmentsWith
          (WordRAM.singletonSegmentMap layout.baseWordIndex layout.deadSegment)
          (WordRAM.TraceResult.ofResult
            ((table.baseWordIndexTable.readProgram i).eval
              table.baseWordIndexTable.wordRAMStore)))
        fun baseWordIndex? =>
          WordRAM.TraceResult.bind
            (WordRAM.TraceResult.relabelReadSegmentsWith
              (WordRAM.singletonSegmentMap layout.rankBefore layout.deadSegment)
              (WordRAM.TraceResult.ofResult
                ((table.rankBeforeTable.readProgram i).eval
                  table.rankBeforeTable.wordRAMStore)))
            fun rankBefore? =>
              WordRAM.TraceResult.map
                (fun firstOffset? =>
                  entryOfFields baseOccurrence? baseWordIndex?
                    rankBefore? firstOffset?)
                (WordRAM.TraceResult.relabelReadSegmentsWith
                  (WordRAM.singletonSegmentMap
                    layout.firstOffset layout.deadSegment)
                  (WordRAM.TraceResult.ofResult
                    ((table.firstOffsetTable.readProgram i).eval
                      table.firstOffsetTable.wordRAMStore)))

theorem readTraceResultRelabeled_refines_readCosted
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    (table.readTraceResultRelabeled layout i).toCosted =
      table.readCosted i := by
  apply Costed.ext
  · have hfirstValue :
      Option.map WordRAM.bitsToNatLE table.firstOffsetTable.store.words[i]? =
        (table.firstOffsetTable.readCosted i).value := by
      have hv :=
        congrArg Costed.value
          (table.firstOffsetTable.readProgram_refines_readCosted i)
      simpa [WordRAM.Result.toCosted] using hv
    simp [readTraceResultRelabeled, readCosted,
      table.baseOccurrenceTable.readProgram_refines_readCosted i,
      table.baseWordIndexTable.readProgram_refines_readCosted i,
      table.rankBeforeTable.readProgram_refines_readCosted i,
      hfirstValue,
      Costed.bind, Costed.map]
  · have hfirstTrace :
      ((table.firstOffsetTable.readProgram i).eval
          table.firstOffsetTable.wordRAMStore).trace.length = 1 := by
      have hc :=
        congrArg Costed.cost
          (table.firstOffsetTable.readProgram_refines_readCosted i)
      simpa [WordRAM.Result.toCosted] using hc
    simp [readTraceResultRelabeled, readCosted,
      table.baseOccurrenceTable.readProgram_refines_readCosted i,
      table.baseWordIndexTable.readProgram_refines_readCosted i,
      table.rankBeforeTable.readProgram_refines_readCosted i,
      hfirstTrace,
      Costed.bind, Costed.map]

theorem readTraceResultRelabeled_matchesReadStore
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore)
    (hbaseOccurrence :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              layout.baseOccurrence layout.deadSegment segment) index =
          table.baseOccurrenceTable.wordRAMStore.readWord? segment index)
    (hbaseWordIndex :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              layout.baseWordIndex layout.deadSegment segment) index =
          table.baseWordIndexTable.wordRAMStore.readWord? segment index)
    (hrankBefore :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              layout.rankBefore layout.deadSegment segment) index =
          table.rankBeforeTable.wordRAMStore.readWord? segment index)
    (hfirstOffset :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              layout.firstOffset layout.deadSegment segment) index =
          table.firstOffsetTable.wordRAMStore.readWord? segment index)
    (i : Nat) :
    forall event,
      List.Mem event (table.readTraceResultRelabeled layout i).trace ->
        event.matchesReadStore store := by
  unfold readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
        (WordRAM.TraceResult.ofResult
          ((table.baseOccurrenceTable.readProgram i).eval
            table.baseOccurrenceTable.wordRAMStore))
        (WordRAM.ReadStore.ofStore
          table.baseOccurrenceTable.wordRAMStore)
        store
        (WordRAM.singletonSegmentMap
          layout.baseOccurrence layout.deadSegment)
        hbaseOccurrence
        (by
          intro event hmem
          simpa [WordRAM.TraceResult.ofResult_trace,
            WordRAM.TraceEvent.matchesReadStore_ofStore] using
            WordRAM.Program.eval_reads_subset_payload
              (table.baseOccurrenceTable.readProgram i)
              table.baseOccurrenceTable.wordRAMStore event hmem)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (WordRAM.TraceResult.ofResult
            ((table.baseWordIndexTable.readProgram i).eval
              table.baseWordIndexTable.wordRAMStore))
          (WordRAM.ReadStore.ofStore
            table.baseWordIndexTable.wordRAMStore)
          store
          (WordRAM.singletonSegmentMap
            layout.baseWordIndex layout.deadSegment)
          hbaseWordIndex
          (by
            intro event hmem
            simpa [WordRAM.TraceResult.ofResult_trace,
              WordRAM.TraceEvent.matchesReadStore_ofStore] using
              WordRAM.Program.eval_reads_subset_payload
                (table.baseWordIndexTable.readProgram i)
                table.baseWordIndexTable.wordRAMStore event hmem)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
            (WordRAM.TraceResult.ofResult
              ((table.rankBeforeTable.readProgram i).eval
                table.rankBeforeTable.wordRAMStore))
            (WordRAM.ReadStore.ofStore
              table.rankBeforeTable.wordRAMStore)
            store
            (WordRAM.singletonSegmentMap
              layout.rankBefore layout.deadSegment)
            hrankBefore
            (by
              intro event hmem
              simpa [WordRAM.TraceResult.ofResult_trace,
                WordRAM.TraceEvent.matchesReadStore_ofStore] using
                WordRAM.Program.eval_reads_subset_payload
                  (table.rankBeforeTable.readProgram i)
                  table.rankBeforeTable.wordRAMStore event hmem)
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
            (WordRAM.TraceResult.ofResult
              ((table.firstOffsetTable.readProgram i).eval
                table.firstOffsetTable.wordRAMStore))
            (WordRAM.ReadStore.ofStore
              table.firstOffsetTable.wordRAMStore)
            store
            (WordRAM.singletonSegmentMap
              layout.firstOffset layout.deadSegment)
            hfirstOffset
            (by
              intro event hmem
              simpa [WordRAM.TraceResult.ofResult_trace,
                WordRAM.TraceEvent.matchesReadStore_ofStore] using
                WordRAM.Program.eval_reads_subset_payload
                  (table.firstOffsetTable.readProgram i)
                  table.firstOffsetTable.wordRAMStore event hmem)

theorem readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    forall event,
      List.Mem event (table.readTraceResultRelabeled layout i).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
        (WordRAM.singletonSegmentMap
          layout.baseOccurrence layout.deadSegment)
        (WordRAM.TraceResult.ofResult
          ((table.baseOccurrenceTable.readProgram i).eval
            table.baseOccurrenceTable.wordRAMStore))
        (by
          intro event hmem
          simpa [WordRAM.TraceResult.ofResult_trace] using
            WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
              (table.baseOccurrenceTable.readProgram i)
              table.baseOccurrenceTable.wordRAMStore event hmem)
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
          (WordRAM.singletonSegmentMap
            layout.baseWordIndex layout.deadSegment)
          (WordRAM.TraceResult.ofResult
            ((table.baseWordIndexTable.readProgram i).eval
              table.baseWordIndexTable.wordRAMStore))
          (by
            intro event hmem
            simpa [WordRAM.TraceResult.ofResult_trace] using
              WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
                (table.baseWordIndexTable.readProgram i)
                table.baseWordIndexTable.wordRAMStore event hmem)
    · apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
            (WordRAM.singletonSegmentMap
              layout.rankBefore layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.rankBeforeTable.readProgram i).eval
                table.rankBeforeTable.wordRAMStore))
            (by
              intro event hmem
              simpa [WordRAM.TraceResult.ofResult_trace] using
                WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
                  (table.rankBeforeTable.readProgram i)
                  table.rankBeforeTable.wordRAMStore event hmem)
      · apply WordRAM.TraceResult.map_trace_forall
        exact
          WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
            (WordRAM.singletonSegmentMap
              layout.firstOffset layout.deadSegment)
            (WordRAM.TraceResult.ofResult
              ((table.firstOffsetTable.readProgram i).eval
                table.firstOffsetTable.wordRAMStore))
            (by
              intro event hmem
              simpa [WordRAM.TraceResult.ofResult_trace] using
                WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
                  (table.firstOffsetTable.readProgram i)
                  table.firstOffsetTable.wordRAMStore event hmem)

end FixedWidthSparseDenseFalseSelectDenseLocalEntryTable

/-- Trace-preserving relative-offset read for false-select tables. -/
def relativeSplitFalseOffsetReadTraceResultRelabeled
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun offset? => offset?.map (fun offset => base + offset))
    (WordRAM.TraceResult.relabelReadSegmentsWith
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.readProgram slot).eval table.wordRAMStore)))

theorem relativeSplitFalseOffsetReadTraceResultRelabeled_refines
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    (relativeSplitFalseOffsetReadTraceResultRelabeled
      segmentBase deadSegment table base slot).toCosted =
      relativeOffsetReadCosted table base slot := by
  apply Costed.ext <;>
    simp [relativeSplitFalseOffsetReadTraceResultRelabeled,
      relativeOffsetReadCosted, table.readProgram_refines_readCosted slot,
      Costed.map]

theorem relativeSplitFalseOffsetReadTraceResultRelabeled_matchesReadStore
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          table.wordRAMStore.readWord? segment index)
    (base slot : Nat) :
    forall event,
      List.Mem event
          (relativeSplitFalseOffsetReadTraceResultRelabeled
            segmentBase deadSegment table base slot).trace ->
        event.matchesReadStore store := by
  unfold relativeSplitFalseOffsetReadTraceResultRelabeled
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (WordRAM.TraceResult.ofResult
        ((table.readProgram slot).eval table.wordRAMStore))
      (WordRAM.ReadStore.ofStore table.wordRAMStore)
      store
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      hread
      (by
        intro event hmem
        simpa [WordRAM.TraceResult.ofResult_trace,
          WordRAM.TraceEvent.matchesReadStore_ofStore] using
          WordRAM.Program.eval_reads_subset_payload
            (table.readProgram slot) table.wordRAMStore event hmem)

theorem relativeSplitFalseOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    forall event,
      List.Mem event
          (relativeSplitFalseOffsetReadTraceResultRelabeled
            segmentBase deadSegment table base slot).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold relativeSplitFalseOffsetReadTraceResultRelabeled
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      (WordRAM.TraceResult.ofResult
        ((table.readProgram slot).eval table.wordRAMStore))
      (by
        intro event hmem
        simpa [WordRAM.TraceResult.ofResult_trace] using
          WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
            (table.readProgram slot) table.wordRAMStore event hmem)

namespace RelativeSplitSparseExceptionDirectory

/-- Trace-preserving sparse-exception read for the relative-split false-select directory. -/
def readTraceResultRelabeled
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.relabelReadSegmentsWith
      (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
      (directory.rankData.rankTraceResult true localSlot))
    fun exceptionRank =>
      relativeSplitFalseOffsetReadTraceResultRelabeled layout.relativeBase
        layout.deadSegment directory.relativeTable base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readTraceResultRelabeled_refines_readCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    (directory.readTraceResultRelabeled
      layout base localSlot localOccurrence).toCosted =
      directory.readCosted base localSlot localOccurrence := by
  simp [readTraceResultRelabeled, readCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
    directory.rankData.rankTraceResult_refines_rankInterpretedCosted,
    directory.rankData.rankInterpretedCosted_refines_rankCosted,
    relativeSplitFalseOffsetReadTraceResultRelabeled_refines]

theorem readTraceResultRelabeled_matchesReadStore
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (store : WordRAM.ReadStore)
    (hrank :
      forall segment index,
        store.readWord?
            (WordRAM.tripleSegmentMap layout.rankBase
              layout.deadSegment segment) index =
          (directory.rankData.rankRegisterWordRAMStore true).readWord?
            segment index)
    (hrelative :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              layout.relativeBase layout.deadSegment segment) index =
          directory.relativeTable.wordRAMStore.readWord? segment index)
    (base localSlot localOccurrence : Nat) :
    forall event,
      List.Mem event
          (directory.readTraceResultRelabeled
            layout base localSlot localOccurrence).trace ->
        event.matchesReadStore store := by
  unfold readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
        (directory.rankData.rankTraceResult true localSlot)
        (WordRAM.ReadStore.ofStore
          (directory.rankData.rankRegisterWordRAMStore true))
        store
        (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
        hrank
        (directory.rankData.rankTraceResult_matchesReadStore true localSlot)
  · exact
      relativeSplitFalseOffsetReadTraceResultRelabeled_matchesReadStore
        layout.relativeBase layout.deadSegment directory.relativeTable store
        hrelative base
        (relativeSplitFalseSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)

theorem readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    forall event,
      List.Mem event
          (directory.readTraceResultRelabeled
            layout base localSlot localOccurrence).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold readTraceResultRelabeled
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
        (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
        (directory.rankData.rankTraceResult true localSlot)
        (directory.rankData.rankTraceResult_no_syntheticCostOnlyPrimitive
          true localSlot)
  · exact
      relativeSplitFalseOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        layout.relativeBase layout.deadSegment directory.relativeTable base
        (relativeSplitFalseSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)

end RelativeSplitSparseExceptionDirectory

theorem denseTwoWordFalseSelectTraceResultRelabeled_refines
    {bits : List Bool} {wordSize : Nat}
    (segmentBase deadSegment : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (GenericSelect.denseTwoWordSelectTraceResultRelabeled
      segmentBase deadSegment false bitWords
      basePosition baseOccurrence q).toCosted =
      denseTwoWordFalseSelectCosted bitWords
        basePosition baseOccurrence q := by
  rw [GenericSelect.denseTwoWordSelectTraceResultRelabeled_refines_interpretedCosted]
  rw [GenericSelect.denseTwoWordSelectInterpretedCosted_refines]
  rfl

namespace RelativeSplitSparseExceptionFalseSelectCloseData

/-- Trace-preserving relative-split false-select close query with global segments. -/
def selectTraceResultRelabeled
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < shape.size then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeled layout.superTable
        (falseSelectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if relativeSplitFalseSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (WordRAM.TraceResult.relabelReadSegmentsWith
                (WordRAM.tripleSegmentMap
                  layout.longFlagRankBase layout.deadSegment)
                (data.longFlagRankData.rankTraceResult true
                  (falseSelectSuperSlot q data.superStride)))
              fun exceptionRank =>
                relativeSplitFalseOffsetReadTraceResultRelabeled
                  layout.longRelativeBase layout.deadSegment
                  data.longSuperRelativeTable
                  (relativeSplitFalseSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitFalseSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitFalseSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            WordRAM.TraceResult.bind
              (data.localTable.readTraceResultRelabeled
                layout.localTable localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if relativeSplitFalseSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResultRelabeled
                      layout.sparseDirectory
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitFalseSelectLocalBaseOccurrence
                          super loc)
                  else
                    GenericSelect.denseTwoWordSelectTraceResultRelabeled
                      layout.bitWordBase layout.deadSegment false
                      data.bitWords
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitFalseSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

set_option linter.unusedSimpArgs false in
theorem selectTraceResultRelabeled_refines_selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat) :
    (data.selectTraceResultRelabeled layout idx).toCosted =
      data.selectCloseCosted idx := by
  unfold selectTraceResultRelabeled selectCloseCosted
  by_cases hvalid : idx < shape.size
  · simp [hvalid, WordRAM.TraceResult.bind_toCosted,
      data.superTable.readTraceResultRelabeled_refines_readCosted
        layout.superTable
        (falseSelectSuperSlot (data.queryOccurrence idx)
          data.superStride)]
    cases hsuper :
        (data.superTable.readCosted
          (falseSelectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        · simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
            data.longFlagRankData.rankTraceResult_refines_rankInterpretedCosted,
            data.longFlagRankData.rankInterpretedCosted_refines_rankCosted,
            relativeSplitFalseOffsetReadTraceResultRelabeled_refines]
        · let localSlot :=
            relativeSplitFalseSelectLocalSlot (data.queryOccurrence idx)
              data.superStride data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            localSlot,
            data.localTable.readTraceResultRelabeled_refines_readCosted
              layout.localTable localSlot]
          cases hlocal :
              (data.localTable.readCosted localSlot).value with
          | none =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_readCosted
                  layout.localTable localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).value = none := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).trace.length =
                    (data.localTable.readCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              simp [Costed.pure]
          | some loc =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_readCosted
                  layout.localTable localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).value = some loc := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).trace.length =
                    (data.localTable.readCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  data.sparseDirectory.readTraceResultRelabeled_refines_readCosted
                    layout.sparseDirectory
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalSlot
                      (data.queryOccurrence idx) data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (data.queryOccurrence idx -
                      relativeSplitFalseSelectLocalBaseOccurrence super loc)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hdense :=
                  denseTwoWordFalseSelectTraceResultRelabeled_refines
                    layout.bitWordBase layout.deadSegment data.bitWords
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalBaseOccurrence super loc)
                    (data.queryOccurrence idx)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hdense
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hdense
  · simp [hvalid, Costed.pure]

theorem selectTraceResultRelabeled_trace_forall
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsuper :
      forall slot event,
        List.Mem event
          (data.superTable.readTraceResultRelabeled
            layout.superTable slot).trace ->
          P event)
    (hlongRank :
      forall slot event,
        List.Mem event
          (WordRAM.TraceResult.relabelReadSegmentsWith
            (WordRAM.tripleSegmentMap
              layout.longFlagRankBase layout.deadSegment)
            (data.longFlagRankData.rankTraceResult true slot)).trace ->
          P event)
    (hlongRelative :
      forall base slot event,
        List.Mem event
          (relativeSplitFalseOffsetReadTraceResultRelabeled
            layout.longRelativeBase layout.deadSegment
            data.longSuperRelativeTable base slot).trace ->
          P event)
    (hlocal :
      forall slot event,
        List.Mem event
          (data.localTable.readTraceResultRelabeled
            layout.localTable slot).trace ->
          P event)
    (hsparse :
      forall base localSlot localOccurrence event,
        List.Mem event
          (data.sparseDirectory.readTraceResultRelabeled
            layout.sparseDirectory base localSlot localOccurrence).trace ->
          P event)
    (hdense :
      forall basePosition baseOccurrence q event,
        List.Mem event
          (GenericSelect.denseTwoWordSelectTraceResultRelabeled
            layout.bitWordBase layout.deadSegment false
            data.bitWords basePosition baseOccurrence q).trace ->
          P event) :
    forall event,
      List.Mem event (data.selectTraceResultRelabeled layout idx).trace ->
        P event := by
  unfold selectTraceResultRelabeled
  by_cases hvalid : idx < shape.size
  · intro ev htrace
    simp [hvalid, WordRAM.TraceResult.bind] at htrace
    rcases List.mem_append.mp htrace with hsuperMem | htrace
    ·
        exact hsuper
          (falseSelectSuperSlot (data.queryOccurrence idx) data.superStride)
          ev hsuperMem
    · cases hsuperValue :
        (data.superTable.readTraceResultRelabeled layout.superTable
          (falseSelectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
      | none =>
          simp [hsuperValue] at htrace
      | some super =>
          by_cases hlong :
              relativeSplitFalseSelectEntryIsMarked super = true
          · simp [hsuperValue, hlong] at htrace
            rcases htrace with hlongMem | hlongRelativeMem
            · have hmemRelabeled :
                  List.Mem ev
                    (WordRAM.TraceResult.relabelReadSegmentsWith
                      (WordRAM.tripleSegmentMap
                        layout.longFlagRankBase layout.deadSegment)
                        (data.longFlagRankData.rankTraceResult true
                          (falseSelectSuperSlot (data.queryOccurrence idx)
                            data.superStride))).trace := by
                rw [WordRAM.TraceResult.relabelReadSegmentsWith_trace]
                exact List.mem_map.mpr hlongMem
              exact hlongRank
                (falseSelectSuperSlot (data.queryOccurrence idx)
                  data.superStride) ev hmemRelabeled
            · exact hlongRelative
                (relativeSplitFalseSelectEntryBasePosition
                  data.wordSize super)
                (relativeSplitFalseSelectLongCompactSlot
                  (data.longFlagRankData.rankTraceResult true
                    (falseSelectSuperSlot (data.queryOccurrence idx)
                      data.superStride)).value
                  (data.queryOccurrence idx - super.baseOccurrence)
                  data.superStride) ev hlongRelativeMem
          · simp [hsuperValue, hlong] at htrace
            let localSlot :=
              relativeSplitFalseSelectLocalSlot (data.queryOccurrence idx)
                data.superStride data.localSlotsPerSuper
                data.localStride super
            rcases htrace with hlocalMem | htrace
            · exact hlocal localSlot ev hlocalMem
            · cases hlocalValue :
                (data.localTable.readTraceResultRelabeled
                  layout.localTable localSlot).value with
              | none =>
                  simp [hlocalValue, localSlot] at htrace
              | some loc =>
                  by_cases hsparseBranch :
                      relativeSplitFalseSelectEntryIsMarked loc = true
                  · exact hsparse
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (data.queryOccurrence idx -
                        relativeSplitFalseSelectLocalBaseOccurrence
                          super loc) ev
                      (by
                        simpa [hlocalValue, hsparseBranch, localSlot] using
                          htrace)
                  · exact hdense
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitFalseSelectLocalBaseOccurrence
                        super loc)
                      (data.queryOccurrence idx) ev
                      (by
                        simpa [hlocalValue, hsparseBranch, localSlot] using
                          htrace)
  · intro ev htrace
    simp [hvalid] at htrace
    cases htrace

end RelativeSplitSparseExceptionFalseSelectCloseData

end SuccinctSelect

namespace BPNavigation

open SuccinctFinal

/-- Global read store for the concrete relative-split BP close-navigation trace. -/
def concreteBPCloseNavigationGlobalReadStore
    (shape : Cartesian.CartesianShape) : WordRAM.ReadStore where
  readWord? segment index :=
    let accessDirectory :=
      concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape
    let selectData := accessDirectory.selectData
    let rankStore :=
      (SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
        |>.rankRegisterWordRAMStore false
    let summary :=
      SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
    let globalTable := SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
    if segment = 0 then
      selectData.bitWords.store.wordRAMStore.readWord? 0 index
    else if segment = 1 then
      selectData.superTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    else if segment = 2 then
      selectData.superTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    else if segment = 3 then
      selectData.superTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    else if segment = 4 then
      selectData.superTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 5 then
      selectData.localTable.baseOccurrenceTable.wordRAMStore.readWord? 0 index
    else if segment = 6 then
      selectData.localTable.baseWordIndexTable.wordRAMStore.readWord? 0 index
    else if segment = 7 then
      selectData.localTable.rankBeforeTable.wordRAMStore.readWord? 0 index
    else if segment = 8 then
      selectData.localTable.firstOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 9 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 0 index
    else if segment = 10 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 1 index
    else if segment = 11 then
      (selectData.longFlagRankData.rankRegisterWordRAMStore true).readWord? 2 index
    else if segment = 12 then
      selectData.longSuperRelativeTable.wordRAMStore.readWord? 0 index
    else if segment = 13 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 0 index
    else if segment = 14 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 1 index
    else if segment = 15 then
      (selectData.sparseDirectory.rankData.rankRegisterWordRAMStore true).readWord? 2 index
    else if segment = 16 then
      selectData.sparseDirectory.relativeTable.wordRAMStore.readWord? 0 index
    else if segment = 17 then
      rankStore.readWord? 0 index
    else if segment = 18 then
      rankStore.readWord? 1 index
    else if segment = 19 then
      rankStore.readWord? 2 index
    else if segment = 20 then
      (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
        shape).store.words[index]?
    else if segment = 21 then
      summary.minRelTable.wordRAMStore.readWord? 0 index
    else if segment = 22 then
      summary.maxRelTable.wordRAMStore.readWord? 0 index
    else if segment = 23 then
      summary.argOffsetTable.wordRAMStore.readWord? 0 index
    else if segment = 24 then
      localTable.table.wordRAMStore.readWord? 0 index
    else if segment = 25 then
      globalTable.table.wordRAMStore.readWord? 0 index
    else
      none

theorem concreteBPCloseNavigationGlobalReadStore_retiredFiniteSmallInterior_none
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPCloseNavigationGlobalReadStore shape).readWord? 26 index =
        none /\
      (concreteBPCloseNavigationGlobalReadStore shape).readWord? 27 index =
        none := by
  simp [concreteBPCloseNavigationGlobalReadStore]

/-- Payload components used to back successful global reads. -/
structure ConcreteBPCloseNavigationPayloadLayout
    (shape : Cartesian.CartesianShape) where
  payload : List Bool
  bpCodePayload : List Bool
  accessRankPayload : List Bool
  selectPayload : List Bool
  accessPadding : List Bool
  closePayload : List Bool
  closePadding : List Bool

/-- Counted payload layout for the concrete BP close-navigation global store. -/
def concreteBPCloseNavigationPayloadLayout
    (shape : Cartesian.CartesianShape) :
    ConcreteBPCloseNavigationPayloadLayout shape :=
  let accessDirectory :=
    concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape
  let closeDirectory := concreteBPNativeCloseDirectory shape
  let accessPadding :=
    List.replicate
      (relativeSplitSparseExceptionBPCloseAccessOverhead shape.size -
        accessDirectory.payload.length) false
  let closePadding :=
    List.replicate
      (SuccinctClose.compactBPCloseOverhead shape.size -
        closeDirectory.payload.length) false
  { payload := shape.bpCode ++ accessDirectory.rankData.auxPayload ++
      accessDirectory.selectData.payload ++ accessPadding ++
        closeDirectory.payload ++ closePadding
    bpCodePayload := shape.bpCode
    accessRankPayload := accessDirectory.rankData.auxPayload
    selectPayload := accessDirectory.selectData.payload
    accessPadding := accessPadding
    closePayload := closeDirectory.payload
    closePadding := closePadding }

theorem concreteBPCloseNavigationPayloadLayout_payload_components
    (shape : Cartesian.CartesianShape) :
    let layout := concreteBPCloseNavigationPayloadLayout shape
    layout.payload =
      layout.bpCodePayload ++ layout.accessRankPayload ++
        layout.selectPayload ++ layout.accessPadding ++
          layout.closePayload ++ layout.closePadding := by
  simp [concreteBPCloseNavigationPayloadLayout,
    concreteBPCloseNavigationRelativeSplitAccessFamily,
    List.append_assoc]

abbrev ConcreteBPCloseNavigationPayloadSource :=
  SuccinctFinal.ConcreteBPNativeSuccinctRMQFlatPayloadSource

/-- Source words for one global read segment in the BP close-navigation store. -/
def concreteBPCloseNavigationPayloadSourceWords
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPCloseNavigationPayloadSource) :
    Array (List Bool) :=
  let accessDirectory :=
    concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape
  let selectData := accessDirectory.selectData
  let rankData := accessDirectory.rankData
  let summary :=
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
  match source with
  | .bpCode => selectData.bitWords.store.words
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.store.words
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.store.words
  | .selectSuperRankBefore =>
      selectData.superTable.rankBeforeTable.store.words
  | .selectSuperFirstOffset =>
      selectData.superTable.firstOffsetTable.store.words
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.store.words
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.store.words
  | .selectLocalRankBefore =>
      selectData.localTable.rankBeforeTable.store.words
  | .selectLocalFirstOffset =>
      selectData.localTable.firstOffsetTable.store.words
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.store.words
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.store.words
  | .selectLongFlagBits =>
      selectData.longFlagRankData.bitWords.store.words
  | .selectLongRelative =>
      selectData.longSuperRelativeTable.store.words
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.store.words
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.store.words
  | .selectSparseFlagBits =>
      selectData.sparseDirectory.rankData.bitWords.store.words
  | .selectSparseRelative =>
      selectData.sparseDirectory.relativeTable.store.words
  | .finalRankSuperFalse =>
      rankData.superTables.falseTable.store.words
  | .finalRankBlockFalse =>
      rankData.blockTables.falseTable.store.words
  | .finalRankBPCodeAlias =>
      rankData.bitWords.store.words
  | .closeSummaryBaseline =>
      summary.baselineTable.store.words
  | .closeSummaryMinRel =>
      summary.minRelTable.store.words
  | .closeSummaryMaxRel =>
      summary.maxRelTable.store.words
  | .closeSummaryArgOffset =>
      summary.argOffsetTable.store.words
  | .closeInteriorLocal =>
      localTable.table.store.words
  | .closeInteriorGlobal =>
      globalTable.table.store.words
  | .closeFiniteSmallInteriorMin =>
      #[]
  | .closeFiniteSmallInteriorArg =>
      #[]
  | .closeFiniteSmallSameBlock =>
      #[]

def concreteBPCloseNavigationPayloadSourcePayload
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPCloseNavigationPayloadSource) :
    List Bool :=
  let accessDirectory :=
    concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape
  let selectData := accessDirectory.selectData
  let rankData := accessDirectory.rankData
  let summary :=
    SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := SuccinctClose.concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable shape
  match source with
  | .bpCode => shape.bpCode
  | .selectSuperBaseOccurrence =>
      selectData.superTable.baseOccurrenceTable.payload
  | .selectSuperBaseWordIndex =>
      selectData.superTable.baseWordIndexTable.payload
  | .selectSuperRankBefore =>
      selectData.superTable.rankBeforeTable.payload
  | .selectSuperFirstOffset =>
      selectData.superTable.firstOffsetTable.payload
  | .selectLocalBaseOccurrence =>
      selectData.localTable.baseOccurrenceTable.payload
  | .selectLocalBaseWordIndex =>
      selectData.localTable.baseWordIndexTable.payload
  | .selectLocalRankBefore =>
      selectData.localTable.rankBeforeTable.payload
  | .selectLocalFirstOffset =>
      selectData.localTable.firstOffsetTable.payload
  | .selectLongFlagRankSuperTrue =>
      selectData.longFlagRankData.superTables.trueTable.payload
  | .selectLongFlagRankBlockTrue =>
      selectData.longFlagRankData.blockTables.trueTable.payload
  | .selectLongFlagBits =>
      selectData.longFlagBits
  | .selectLongRelative =>
      selectData.longSuperRelativeTable.payload
  | .selectSparseRankSuperTrue =>
      selectData.sparseDirectory.rankData.superTables.trueTable.payload
  | .selectSparseRankBlockTrue =>
      selectData.sparseDirectory.rankData.blockTables.trueTable.payload
  | .selectSparseFlagBits =>
      selectData.sparseDirectory.flagBits
  | .selectSparseRelative =>
      selectData.sparseDirectory.relativeTable.payload
  | .finalRankSuperFalse =>
      rankData.superTables.falseTable.payload
  | .finalRankBlockFalse =>
      rankData.blockTables.falseTable.payload
  | .finalRankBPCodeAlias =>
      shape.bpCode
  | .closeSummaryBaseline =>
      summary.baselineTable.payload
  | .closeSummaryMinRel =>
      summary.minRelTable.payload
  | .closeSummaryMaxRel =>
      summary.maxRelTable.payload
  | .closeSummaryArgOffset =>
      summary.argOffsetTable.payload
  | .closeInteriorLocal =>
      localTable.payload
  | .closeInteriorGlobal =>
      globalTable.payload
  | .closeFiniteSmallInteriorMin =>
      []
  | .closeFiniteSmallInteriorArg =>
      []
  | .closeFiniteSmallSameBlock =>
      []

theorem concreteBPCloseNavigationPayloadLegacyInteriorSegment_empty
    (shape : Cartesian.CartesianShape) :
    concreteBPCloseNavigationPayloadSourceWords
        shape .closeFiniteSmallInteriorMin = #[] /\
      concreteBPCloseNavigationPayloadSourceWords
        shape .closeFiniteSmallInteriorArg = #[] /\
      concreteBPCloseNavigationPayloadSourcePayload
        shape .closeFiniteSmallInteriorMin = [] /\
      concreteBPCloseNavigationPayloadSourcePayload
        shape .closeFiniteSmallInteriorArg = [] := by
  simp [concreteBPCloseNavigationPayloadSourceWords,
    concreteBPCloseNavigationPayloadSourcePayload]

def concreteBPCloseNavigationPayloadReadBacked
    (shape : Cartesian.CartesianShape)
    (segment index : Nat) (word : List Bool) : Prop :=
  (segment = 20 /\
    (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
      shape).store.words[index]? = some word /\
    SuccinctSpace.flattenPayloadWords
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words.toList =
      (SuccinctClose.canonicalRelativeRmmInteriorDirectory shape).payload) \/
  exists source,
    SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
        segment = some source /\
      (concreteBPCloseNavigationPayloadSourceWords shape source)[index]? =
        some word /\
      SuccinctSpace.flattenPayloadWords
          (concreteBPCloseNavigationPayloadSourceWords shape source).toList =
        concreteBPCloseNavigationPayloadSourcePayload shape source

theorem concreteBPCloseNavigationPayloadSourceWords_erases
    (shape : Cartesian.CartesianShape)
    (source : ConcreteBPCloseNavigationPayloadSource) :
    SuccinctSpace.flattenPayloadWords
        (concreteBPCloseNavigationPayloadSourceWords
          shape source).toList =
      concreteBPCloseNavigationPayloadSourcePayload shape source := by
  let accessDirectory :=
    concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape
  let selectData := accessDirectory.selectData
  let rankData := accessDirectory.rankData
  cases source with
  | bpCode =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using selectData.bitWords.erases
  | selectSuperBaseOccurrence =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.superTable.baseOccurrenceTable.store.erases
  | selectSuperBaseWordIndex =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.superTable.baseWordIndexTable.store.erases
  | selectSuperRankBefore =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.superTable.rankBeforeTable.store.erases
  | selectSuperFirstOffset =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.superTable.firstOffsetTable.store.erases
  | selectLocalBaseOccurrence =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.localTable.baseOccurrenceTable.store.erases
  | selectLocalBaseWordIndex =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.localTable.baseWordIndexTable.store.erases
  | selectLocalRankBefore =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.localTable.rankBeforeTable.store.erases
  | selectLocalFirstOffset =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.localTable.firstOffsetTable.store.erases
  | selectLongFlagRankSuperTrue =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.longFlagRankData.superTables.trueTable.store.erases
  | selectLongFlagRankBlockTrue =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.longFlagRankData.blockTables.trueTable.store.erases
  | selectLongFlagBits =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.longFlagRankData.bitWords.erases
  | selectLongRelative =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.longSuperRelativeTable.store.erases
  | selectSparseRankSuperTrue =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.sparseDirectory.rankData.superTables.trueTable.store.erases
  | selectSparseRankBlockTrue =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.sparseDirectory.rankData.blockTables.trueTable.store.erases
  | selectSparseFlagBits =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.sparseDirectory.rankData.bitWords.erases
  | selectSparseRelative =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, selectData] using
        selectData.sparseDirectory.relativeTable.store.erases
  | finalRankSuperFalse =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, rankData] using
        rankData.superTables.falseTable.store.erases
  | finalRankBlockFalse =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, rankData] using
        rankData.blockTables.falseTable.store.erases
  | finalRankBPCodeAlias =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        accessDirectory, rankData] using rankData.bitWords.erases
  | closeSummaryBaseline =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).baselineTable.store.erases
  | closeSummaryMinRel =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).minRelTable.store.erases
  | closeSummaryMaxRel =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).maxRelTable.store.erases
  | closeSummaryArgOffset =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload] using
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).argOffsetTable.store.erases
  | closeInteriorLocal =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload] using
        (SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
          shape).table.store.erases
  | closeInteriorGlobal =>
      simpa [concreteBPCloseNavigationPayloadSourceWords,
        concreteBPCloseNavigationPayloadSourcePayload,
        SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload] using
        (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
          shape).table.store.erases
  | closeFiniteSmallInteriorMin =>
      change SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
        ([] : List Bool)
      rfl
  | closeFiniteSmallInteriorArg =>
      change SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
        ([] : List Bool)
      rfl
  | closeFiniteSmallSameBlock =>
      change
        SuccinctSpace.flattenPayloadWords ([] : List (List Bool)) =
          ([] : List Bool)
      rfl

theorem concreteBPCloseNavigationGlobalReadStore_eq_sourceStore
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    (concreteBPCloseNavigationGlobalReadStore shape).readWord?
        segment index =
      if segment = 20 then
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words[index]?
      else
        match
          SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
            segment with
        | some source =>
            (concreteBPCloseNavigationPayloadSourceWords shape source)[index]?
        | none => none := by
  match segment with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | 17 => rfl
  | 18 => rfl
  | 19 => rfl
  | 20 => rfl
  | 21 => rfl
  | 22 => rfl
  | 23 => rfl
  | 24 => rfl
  | 25 => rfl
  | 26 => rfl
  | 27 => rfl
  | 28 => rfl
  | _ + 29 => rfl

theorem concreteBPCloseNavigationGlobalReadStore_successful_read_backed
    (shape : Cartesian.CartesianShape)
    {segment index : Nat} {word : List Bool}
    (hread :
      (concreteBPCloseNavigationGlobalReadStore shape).readWord?
          segment index = some word) :
    concreteBPCloseNavigationPayloadReadBacked
      shape segment index word := by
  rw [concreteBPCloseNavigationGlobalReadStore_eq_sourceStore] at hread
  by_cases hcomponent :
      segment = 20
  · left
    refine ⟨hcomponent, ?_, ?_⟩
    · simpa [hcomponent] using hread
    · simpa [SuccinctClose.canonicalRelativeRmmInteriorDirectory] using
        SuccinctClose.canonicalRelativeRmmInteriorComponentStore_flattens_payload
          shape
  · right
    simp [hcomponent] at hread
    cases hsource :
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
          segment with
    | none =>
        simp [hsource] at hread
    | some source =>
        exact ⟨source, rfl,
          by simpa [hsource] using hread,
          concreteBPCloseNavigationPayloadSourceWords_erases shape source⟩

theorem concreteBPCloseNavigationGlobalReadStore_bpCode
    (shape : Cartesian.CartesianShape) (index : Nat) :
    (concreteBPCloseNavigationGlobalReadStore shape).readWord? 0 index =
      (SuccinctSpace.chunkPayloadWords
        (SuccinctRank.machineWordBits shape.bpCode.length)
        shape.bpCode).toArray[index]? := by
  simp [concreteBPCloseNavigationGlobalReadStore,
    SuccinctFinal.builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily,
    SuccinctFinal.builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory,
    SuccinctSelect.builtRelativeSplitSparseExceptionFalseSelectCloseData,
    SuccinctSelect.sparseDenseFalseSelectWordBits,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks,
    SuccinctSpace.PayloadWordStore.wordRAMStore,
    WordRAM.Store.readWord?]

def concreteBPCloseNavigationSelectCloseGlobalTraceResult
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape).selectData
    |>.selectTraceResultRelabeled
      SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout idx

theorem concreteBPCloseNavigationSelectCloseGlobalTraceResult_refines
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPCloseNavigationSelectCloseGlobalTraceResult shape idx).toCosted =
      SuccinctFinal.concreteBPNativeSelectCloseCosted
        concreteBPCloseNavigationAccessFamily shape idx := by
  simp [concreteBPCloseNavigationSelectCloseGlobalTraceResult,
    concreteBPCloseNavigationAccessFamily,
    concreteBPCloseNavigationRelativeSplitAccessFamily,
    SuccinctFinal.RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.toWeakFamily,
    SuccinctFinal.RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory.toWeakDirectory,
    SuccinctFinal.RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory.selectCloseCosted,
    SuccinctSelect.RelativeSplitSparseExceptionFalseSelectCloseData.selectTraceResultRelabeled_refines_selectCloseCosted,
    SuccinctFinal.concreteBPNativeSelectCloseCosted]

set_option linter.unusedSimpArgs false in
theorem concreteBPCloseNavigationSelectCloseGlobalTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
          (concreteBPCloseNavigationSelectCloseGlobalTraceResult
            shape idx).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape) := by
  let data :=
    (concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape).selectData
  refine
    SuccinctSelect.RelativeSplitSparseExceptionFalseSelectCloseData.selectTraceResultRelabeled_trace_forall
      data SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout idx
      (fun event => event.matchesReadStore
        (concreteBPCloseNavigationGlobalReadStore shape)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro slot
    exact
      data.superTable.readTraceResultRelabeled_matchesReadStore
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        (concreteBPCloseNavigationGlobalReadStore shape)
        (by
          intro segment index
          rw [concreteBPCloseNavigationGlobalReadStore_eq_sourceStore]
          cases segment <;>
            simp [concreteBPCloseNavigationPayloadSourceWords,
              SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot
  · intro slot
    exact
      WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
        (data.longFlagRankData.rankTraceResult true slot)
        (WordRAM.ReadStore.ofStore
          (data.longFlagRankData.rankRegisterWordRAMStore true))
        (concreteBPCloseNavigationGlobalReadStore shape)
        (WordRAM.tripleSegmentMap
          SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (by
          intro segment index
          rw [concreteBPCloseNavigationGlobalReadStore_eq_sourceStore]
          cases segment with
          | zero =>
              simp [concreteBPCloseNavigationPayloadSourceWords,
                SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                data,
                SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                SuccinctFinal.concreteBPNativeDeadTraceSegment,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.ReadStore.ofStore,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                WordRAM.Store.readWord?]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [concreteBPCloseNavigationPayloadSourceWords,
                    SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                    data,
                    SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                    SuccinctFinal.concreteBPNativeDeadTraceSegment,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap,
                    WordRAM.ReadStore.ofStore,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                    WordRAM.Store.readWord?]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [concreteBPCloseNavigationPayloadSourceWords,
                        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                        data,
                        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                        SuccinctFinal.concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                        WordRAM.Store.readWord?]
                  | succ segment =>
                      simp [concreteBPCloseNavigationPayloadSourceWords,
                        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                        data,
                        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                        SuccinctFinal.concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                        WordRAM.Store.readWord?])
        (data.longFlagRankData.rankTraceResult_matchesReadStore true slot)
  · intro base slot
    exact
      SuccinctSelect.relativeSplitFalseOffsetReadTraceResultRelabeled_matchesReadStore
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable
        (concreteBPCloseNavigationGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base slot
  · intro slot
    exact
      data.localTable.readTraceResultRelabeled_matchesReadStore
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        (concreteBPCloseNavigationGlobalReadStore shape)
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        slot
  · intro base localSlot localOccurrence
    exact
      data.sparseDirectory.readTraceResultRelabeled_matchesReadStore
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        (concreteBPCloseNavigationGlobalReadStore shape)
        (by
          intro segment index
          rw [concreteBPCloseNavigationGlobalReadStore_eq_sourceStore]
          cases segment with
          | zero =>
              simp [concreteBPCloseNavigationPayloadSourceWords,
                SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                data,
                SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                SuccinctFinal.concreteBPNativeDeadTraceSegment,
                WordRAM.tripleSegmentMap,
                WordRAM.TraceEvent.tripleSegmentMap,
                WordRAM.ReadStore.ofStore,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                WordRAM.Store.readWord?]
          | succ segment =>
              cases segment with
              | zero =>
                  simp [concreteBPCloseNavigationPayloadSourceWords,
                    SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                    data,
                    SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                    SuccinctFinal.concreteBPNativeDeadTraceSegment,
                    WordRAM.tripleSegmentMap,
                    WordRAM.TraceEvent.tripleSegmentMap,
                    WordRAM.ReadStore.ofStore,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                    WordRAM.Store.readWord?]
              | succ segment =>
                  cases segment with
                  | zero =>
                      simp [concreteBPCloseNavigationPayloadSourceWords,
                        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                        data,
                        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                        SuccinctFinal.concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                        WordRAM.Store.readWord?]
                  | succ segment =>
                      simp [concreteBPCloseNavigationPayloadSourceWords,
                        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
                        data,
                        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
                        SuccinctFinal.concreteBPNativeDeadTraceSegment,
                        WordRAM.tripleSegmentMap,
                        WordRAM.TraceEvent.tripleSegmentMap,
                        WordRAM.ReadStore.ofStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords,
                        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords,
                        WordRAM.Store.readWord?])
        (by
          intro segment index
          cases segment <;>
            simp [concreteBPCloseNavigationGlobalReadStore,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.FixedWidthNatTable.wordRAMStore,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        base localSlot localOccurrence
  · intro basePosition baseOccurrence q
    exact
      GenericSelect.denseTwoWordSelectTraceResultRelabeled_matchesReadStore
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        false data.bitWords
        (concreteBPCloseNavigationGlobalReadStore shape)
        (by
          intro segment index
          rw [concreteBPCloseNavigationGlobalReadStore_eq_sourceStore]
          cases segment <;>
            simp [concreteBPCloseNavigationPayloadSourceWords,
              SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?,
              data,
              SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout,
              SuccinctFinal.concreteBPNativeDeadTraceSegment,
              WordRAM.singletonSegmentMap,
              WordRAM.TraceEvent.singletonSegmentMap,
              SuccinctSpace.PayloadWordStore.wordRAMStore,
              WordRAM.Store.readWord?])
        basePosition baseOccurrence q

theorem concreteBPCloseNavigationSelectCloseGlobalTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    forall event,
      List.Mem event
          (concreteBPCloseNavigationSelectCloseGlobalTraceResult
            shape idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  let data :=
    (concreteBPCloseNavigationRelativeSplitAccessFamily.directory shape).selectData
  refine
    SuccinctSelect.RelativeSplitSparseExceptionFalseSelectCloseData.selectTraceResultRelabeled_trace_forall
      data SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout idx
      (fun event => ¬ event.isSyntheticCostOnlyPrimitive) ?_ ?_ ?_ ?_ ?_ ?_
  · intro slot
    exact
      data.superTable.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.superTable
        slot
  · intro slot
    exact
      WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
        (WordRAM.tripleSegmentMap
          SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment)
        (data.longFlagRankData.rankTraceResult true slot)
        (data.longFlagRankData.rankTraceResult_no_syntheticCostOnlyPrimitive
          true slot)
  · intro base slot
    exact
      SuccinctSelect.relativeSplitFalseOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        data.longSuperRelativeTable base slot
  · intro slot
    exact
      data.localTable.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.localTable
        slot
  · intro base localSlot localOccurrence
    exact
      data.sparseDirectory.readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory
        base localSlot localOccurrence
  · intro basePosition baseOccurrence q
    exact
      GenericSelect.denseTwoWordSelectTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        SuccinctFinal.concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        false data.bitWords basePosition baseOccurrence q

theorem concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    SuccinctFinal.concreteBPNativeRankCloseInterpretedCosted shape pos =
      SuccinctFinal.concreteBPNativeRankCloseCosted
        concreteBPCloseNavigationAccessFamily shape pos := by
  unfold SuccinctFinal.concreteBPNativeRankCloseInterpretedCosted
    SuccinctFinal.concreteBPNativeRankCloseCosted
    concreteBPCloseNavigationAccessFamily
    concreteBPCloseNavigationRelativeSplitAccessFamily
  rw [
    (SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
      |>.rankRegisterInterpretedCosted_refines_rankInterpretedCosted false pos]
  exact
    (SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
      |>.rankInterpretedCosted_refines_rankCosted false pos

theorem concreteBPCloseNavigationRankCloseGlobalTraceResult_refines
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
      shape SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
      pos).toCosted =
      SuccinctFinal.concreteBPNativeRankCloseCosted
        concreteBPCloseNavigationAccessFamily shape pos := by
  rw [
    SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment_refines_interpretedCosted,
    concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted]

theorem concreteBPCloseNavigationLCACloseGlobalTraceResult_refines
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
      shape leftClose rightClose).toCosted =
      SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
        shape leftClose rightClose :=
  SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_refines_interpretedCosted
    shape leftClose rightClose

def concreteBPCloseNavigationGlobalTraceResult
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (concreteBPCloseNavigationSelectCloseGlobalTraceResult shape left)
    fun leftClose? =>
      WordRAM.TraceResult.bind
        (concreteBPCloseNavigationSelectCloseGlobalTraceResult
          shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              WordRAM.TraceResult.bind
                (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                  shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      WordRAM.TraceResult.map
                        (fun closeRank => some (closeRank - 1))
                        (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
                          shape
                          SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
                          (answerClose + 1))
                  | none => WordRAM.TraceResult.pure none
          | _, _ => WordRAM.TraceResult.pure none
/-- Canonical U2 cost semantics for the close-navigation trace. -/
def concreteBPCloseNavigationCanonicalCosted
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (SuccinctFinal.concreteBPNativeSelectCloseCosted
      concreteBPCloseNavigationAccessFamily shape left)
    fun leftClose? =>
      Costed.bind
        (SuccinctFinal.concreteBPNativeSelectCloseCosted
          concreteBPCloseNavigationAccessFamily shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
                  shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (SuccinctFinal.concreteBPNativeRankCloseCosted
                          concreteBPCloseNavigationAccessFamily
                          shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none


set_option linter.unusedSimpArgs false in

theorem concreteBPCloseNavigationCanonicalCosted_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPCloseNavigationCanonicalCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hboundShape : left + len <= shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hbound
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hleftLtShape with ⟨leftClose, hleftClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hrightLtShape with ⟨rightClose, hrightClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (SuccinctFinal.concreteBPNativeSelectCloseCosted
        concreteBPCloseNavigationAccessFamily shape left).value =
          some leftClose := by
    have h :=
      SuccinctFinal.concreteBPNativeSelectCloseCosted_exact
        concreteBPCloseNavigationAccessFamily shape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (SuccinctFinal.concreteBPNativeSelectCloseCosted
        concreteBPCloseNavigationAccessFamily shape (left + len - 1)).value =
          some rightClose := by
    have h :=
      SuccinctFinal.concreteBPNativeSelectCloseCosted_exact
        concreteBPCloseNavigationAccessFamily shape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hrankExact :
      ∀ pos,
        (SuccinctFinal.concreteBPNativeRankCloseInterpretedCosted
          shape pos).erase =
            Succinct.rankPrefix false shape.bpCode pos := by
    intro pos
    rw [concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted]
    exact
      SuccinctFinal.concreteBPNativeRankCloseCosted_exact
        concreteBPCloseNavigationAccessFamily shape pos
  have hlca :
      (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
        shape leftClose rightClose).value = some answerClose := by
    have h :=
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_exact_of_query
        (SuccinctFinal.concreteBPNativeRankCloseInterpretedCosted shape)
        hrankExact hlen hboundShape hleftClose hrightClose hanswerClose
    simpa [SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted,
      Costed.erase] using h
  have hrank :
      (SuccinctFinal.concreteBPNativeRankCloseCosted
        concreteBPCloseNavigationAccessFamily shape (answerClose + 1)).value =
          scanWindow shape.representative left len + 1 := by
    have hrankExact' :=
      SuccinctFinal.concreteBPNativeRankCloseCosted_exact
        concreteBPCloseNavigationAccessFamily shape (answerClose + 1)
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      _ = Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact'
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by omega
  unfold concreteBPCloseNavigationCanonicalCosted
  simp [Costed.erase, Costed.bind, Costed.map, Costed.pure,
    hselectLeft, hselectRight, hlca, hrank, hrankSub]
set_option linter.unusedSimpArgs false in
theorem concreteBPCloseNavigationCosted_eq_globalTraceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPCloseNavigationCanonicalCosted shape left right =
      (concreteBPCloseNavigationGlobalTraceResult
        shape left right).toCosted := by
  unfold concreteBPCloseNavigationCanonicalCosted
    concreteBPCloseNavigationGlobalTraceResult
  simp [WordRAM.TraceResult.bind_toCosted,
    concreteBPCloseNavigationSelectCloseGlobalTraceResult_refines,
    Costed.bind]
  cases hleft :
      (SuccinctFinal.concreteBPNativeSelectCloseCosted
        concreteBPCloseNavigationAccessFamily shape left).value with
  | none =>
      simp [hleft, Costed.pure]
  | some leftClose =>
      cases hright :
          (SuccinctFinal.concreteBPNativeSelectCloseCosted
            concreteBPCloseNavigationAccessFamily shape (right - 1)).value with
      | none =>
          simp [hleft, hright, Costed.pure]
      | some rightClose =>
          have hlca :=
            concreteBPCloseNavigationLCACloseGlobalTraceResult_refines
              shape leftClose rightClose
          cases hanswer :
              (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
                shape leftClose rightClose).value with
          | none =>
              have hlcaValue :
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).value = none := by
                have hv := congrArg Costed.value hlca
                simpa [WordRAM.TraceResult.toCosted, hanswer] using hv
              have hlcaCost :
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).trace.length =
                    (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
                      shape leftClose rightClose).cost := by
                have hc := congrArg Costed.cost hlca
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using hc
              simp [hleft, hright, hanswer, hlcaValue, hlcaCost,
                Costed.pure]
          | some answerClose =>
              have hlcaValue :
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).value = some answerClose := by
                have hv := congrArg Costed.value hlca
                simpa [WordRAM.TraceResult.toCosted, hanswer] using hv
              have hlcaCost :
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).trace.length =
                    (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
                      shape leftClose rightClose).cost := by
                have hc := congrArg Costed.cost hlca
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using hc
              have hrank :=
                concreteBPCloseNavigationRankCloseGlobalTraceResult_refines
                  shape (answerClose + 1)
              have hrankValue :
                  (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
                    shape SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
                    (answerClose + 1)).value =
                    (SuccinctFinal.concreteBPNativeRankCloseCosted
                      concreteBPCloseNavigationAccessFamily
                      shape (answerClose + 1)).value := by
                have hv := congrArg Costed.value hrank
                simpa [WordRAM.TraceResult.toCosted] using hv
              have hrankCost :
                  (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
                    shape SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
                    (answerClose + 1)).trace.length =
                    (SuccinctFinal.concreteBPNativeRankCloseCosted
                      concreteBPCloseNavigationAccessFamily
                      shape (answerClose + 1)).cost := by
                have hc := congrArg Costed.cost hrank
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using hc
              simp [hleft, hright, hanswer, hlcaValue, hlcaCost,
                hrankValue, hrankCost, WordRAM.TraceResult.map,
                WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
                Costed.map]

theorem concreteBPCloseNavigationRankCloseGlobalTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    forall event,
      List.Mem event
          (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
            shape SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
            pos).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape) := by
  apply
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (SuccinctFinal.concreteBPNativeRankCloseWordTraceResult shape pos)
      (WordRAM.ReadStore.ofStore
        ((SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false))
      (concreteBPCloseNavigationGlobalReadStore shape)
      (WordRAM.tripleSegmentMap
        SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase
        SuccinctFinal.concreteBPNativeDeadTraceSegment)
  · intro segment index
    cases segment with
    | zero =>
        simp [concreteBPCloseNavigationGlobalReadStore,
          SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase,
          WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
          WordRAM.ReadStore.ofStore]
    | succ segment =>
        cases segment with
        | zero =>
            simp [concreteBPCloseNavigationGlobalReadStore,
              SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase,
              WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
              WordRAM.ReadStore.ofStore]
        | succ segment =>
            cases segment with
            | zero =>
                simp [concreteBPCloseNavigationGlobalReadStore,
                  SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore]
            | succ segment =>
                simp [concreteBPCloseNavigationGlobalReadStore,
                  SuccinctFinal.concreteBPNativeDeadTraceSegment,
                  WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
                  WordRAM.ReadStore.ofStore,
                  SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
                  WordRAM.Store.readWord?]
  · intro event hmem
    simpa [SuccinctFinal.concreteBPNativeRankCloseWordTraceResult,
      WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Register.NatProgram.eval_reads_subset_payload
        ((SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterProgram false (WordRAM.Register.NatExpr.reg 0))
        ((SuccinctFinal.builtRelativeSplitBPCloseRankData shape)
          |>.rankRegisterWordRAMStore false)
        (WordRAM.Register.RegFile.withNat1 pos) event hmem

theorem concreteBPCloseNavigationInteriorGlobalTraceResultAllSizeStructural_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    forall event,
      List.Mem event
          (SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape SuccinctFinal.concreteBPNativeInteriorTraceSegments
            startBlock count).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_matchesReadStore
      shape SuccinctFinal.concreteBPNativeInteriorTraceSegments
      (concreteBPCloseNavigationGlobalReadStore shape)
      (by
        intro address
        simp [concreteBPCloseNavigationGlobalReadStore,
          SuccinctFinal.concreteBPNativeInteriorTraceSegments])
      startBlock count

theorem concreteBPCloseNavigationLCACloseGlobalTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    forall event,
      List.Mem event
          (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
            shape leftClose rightClose).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape) := by
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructural_matchesReadStore
      shape
      (SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegment
        shape SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase)
      SuccinctFinal.concreteBPNativeInteriorTraceSegments
      SuccinctFinal.concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPCloseNavigationGlobalReadStore shape)
      (fun pos =>
        concreteBPCloseNavigationRankCloseGlobalTraceResult_matchesReadStore
          shape pos)
      (concreteBPCloseNavigationGlobalReadStore_bpCode shape)
      (fun startBlock count =>
        concreteBPCloseNavigationInteriorGlobalTraceResultAllSizeStructural_matchesReadStore
          shape startBlock count)

theorem concreteBPCloseNavigationGlobalTraceResult_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
          (concreteBPCloseNavigationGlobalTraceResult shape left right).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape) := by
  unfold concreteBPCloseNavigationGlobalTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPCloseNavigationSelectCloseGlobalTraceResult_matchesReadStore
        shape left
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPCloseNavigationSelectCloseGlobalTraceResult_matchesReadStore
          shape (right - 1)
    · cases
        (concreteBPCloseNavigationSelectCloseGlobalTraceResult
          shape left).value with
      | none =>
          simp [WordRAM.TraceResult.pure]
      | some leftClose =>
          cases
              (concreteBPCloseNavigationSelectCloseGlobalTraceResult
                shape (right - 1)).value with
          | none =>
              simp [WordRAM.TraceResult.pure]
          | some rightClose =>
              apply WordRAM.TraceResult.bind_trace_forall
              · exact
                  concreteBPCloseNavigationLCACloseGlobalTraceResult_matchesReadStore
                    shape leftClose rightClose
              · cases
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).value with
                | none =>
                    simp [WordRAM.TraceResult.pure]
                | some answerClose =>
                    apply WordRAM.TraceResult.map_trace_forall
                    exact
                      concreteBPCloseNavigationRankCloseGlobalTraceResult_matchesReadStore
                        shape (answerClose + 1)

theorem concreteBPCloseNavigationGlobalTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
          (concreteBPCloseNavigationGlobalTraceResult shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPCloseNavigationGlobalTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      concreteBPCloseNavigationSelectCloseGlobalTraceResult_no_syntheticCostOnlyPrimitive
        shape left
  · apply WordRAM.TraceResult.bind_trace_forall
    · exact
        concreteBPCloseNavigationSelectCloseGlobalTraceResult_no_syntheticCostOnlyPrimitive
          shape (right - 1)
    · cases
        (concreteBPCloseNavigationSelectCloseGlobalTraceResult
          shape left).value with
      | none =>
          simp [WordRAM.TraceResult.pure]
      | some leftClose =>
          cases
              (concreteBPCloseNavigationSelectCloseGlobalTraceResult
                shape (right - 1)).value with
          | none =>
              simp [WordRAM.TraceResult.pure]
          | some rightClose =>
              apply WordRAM.TraceResult.bind_trace_forall
              · exact
                  SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural_no_syntheticCostOnlyPrimitive
                    shape leftClose rightClose
              · cases
                  (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
                    shape leftClose rightClose).value with
                | none =>
                    simp [WordRAM.TraceResult.pure]
                | some answerClose =>
                    apply WordRAM.TraceResult.map_trace_forall
                    exact
                      SuccinctFinal.concreteBPNativeRankCloseGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
                        shape (answerClose + 1)

theorem concreteBPCloseNavigationGlobalTraceResult_event_read_or_primitive
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
          (concreteBPCloseNavigationGlobalTraceResult shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive := by
  intro event _hmem
  exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event

def concreteBPCloseNavigationGlobalTraceEventBits
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Nat :=
  SuccinctFinal.concreteBPNativeTraceEventBitWidth
    (concreteBPCloseNavigationGlobalTraceResult shape left right).trace

theorem concreteBPCloseNavigationGlobalTraceResult_event_bounds
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult shape left right).trace ->
        SuccinctFinal.concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPCloseNavigationGlobalTraceEventBits shape left right)
          event /\
        SuccinctFinal.concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPCloseNavigationGlobalTraceEventBits shape left right)
          event := by
  intro event hmem
  constructor
  · exact
      SuccinctFinal.concreteBPNativeTraceEventReadAddressFitsInBits_of_mem
        (trace := (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace) (event := event) hmem
  · exact
      SuccinctFinal.concreteBPNativeTraceEventPrimitiveOperandsFitInBits_of_mem
        (trace := (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace) (event := event) hmem

/--
Public store-backed execution packet for concrete BP close navigation.

The trace is built from the relative-split false-select payload, the compact
close/LCA directory, and the final false-rank payload.  It is not a sampled
profile and does not use a synthetic cost-only adapter.
-/
theorem concreteBPCloseNavigationGlobalTrace_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPCloseNavigationCanonicalCosted shape left right =
      (concreteBPCloseNavigationGlobalTraceResult
        shape left right).toCosted /\
    (forall {n len : Nat},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        right = left + len ->
          0 < len ->
            left + len <= n ->
              (concreteBPCloseNavigationGlobalTraceResult
                shape left right).toCosted.erase =
                some (scanWindow shape.representative left len)) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape)) /\
    (forall {segment index : Nat} {word : List Bool},
      (concreteBPCloseNavigationGlobalReadStore shape).readWord?
          segment index = some word ->
        concreteBPCloseNavigationPayloadReadBacked
          shape segment index word) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive) := by
  have hcost :=
    concreteBPCloseNavigationCosted_eq_globalTraceResult_toCosted
      shape left right
  constructor
  · exact hcost
  constructor
  · intro n len hshape hright hlen hbound
    subst right
    rw [← concreteBPCloseNavigationCosted_eq_globalTraceResult_toCosted]
    exact
      concreteBPCloseNavigationCanonicalCosted_exact hshape hlen hbound
  constructor
  · exact
      concreteBPCloseNavigationGlobalTraceResult_event_read_or_primitive
        shape left right
  constructor
  · exact
      concreteBPCloseNavigationGlobalTraceResult_matchesReadStore
        shape left right
  constructor
  · intro segment index word hread
    exact
      concreteBPCloseNavigationGlobalReadStore_successful_read_backed
        shape hread
  · exact
      concreteBPCloseNavigationGlobalTraceResult_no_syntheticCostOnlyPrimitive
        shape left right

/--
Bounded store-backed execution packet for concrete BP close navigation.

In addition to the store-backed execution story, every read address and every
word-primitive operand/result fits the declared trace-local bit width
`concreteBPCloseNavigationGlobalTraceEventBits`.
-/
theorem concreteBPCloseNavigationGlobalTrace_bounded_execution_story
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPCloseNavigationCanonicalCosted shape left right =
      (concreteBPCloseNavigationGlobalTraceResult
        shape left right).toCosted /\
    (forall {n len : Nat},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        right = left + len ->
          0 < len ->
            left + len <= n ->
              (concreteBPCloseNavigationGlobalTraceResult
                shape left right).toCosted.erase =
                some (scanWindow shape.representative left len)) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        event.matchesReadStore
          (concreteBPCloseNavigationGlobalReadStore shape)) /\
    (forall {segment index : Nat} {word : List Bool},
      (concreteBPCloseNavigationGlobalReadStore shape).readWord?
          segment index = some word ->
        concreteBPCloseNavigationPayloadReadBacked
          shape segment index word) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        SuccinctFinal.concreteBPNativeTraceEventReadAddressFitsInBits
          (concreteBPCloseNavigationGlobalTraceEventBits shape left right)
          event) /\
    (forall event,
      List.Mem event
        (concreteBPCloseNavigationGlobalTraceResult
          shape left right).trace ->
        SuccinctFinal.concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPCloseNavigationGlobalTraceEventBits shape left right)
          event) := by
  rcases
    concreteBPCloseNavigationGlobalTrace_execution_story shape left right with
    ⟨hcost, hexact, hclass, hstore, hbacked, hnoSynthetic⟩
  exact
    ⟨hcost, hexact, hclass, hstore, hbacked, hnoSynthetic,
      (fun event hmem =>
        (concreteBPCloseNavigationGlobalTraceResult_event_bounds
          shape left right event hmem).1),
      (fun event hmem =>
        (concreteBPCloseNavigationGlobalTraceResult_event_bounds
          shape left right event hmem).2)⟩

/--
The tempting current-store adapter route for a succinct tree-navigation
capstone: try to obtain the matching-open leg by asking the concrete
close/LCA WordRAM trace for the singleton close/close query.

This is a necessary condition for reusing the existing concrete close/LCA
payload store as the whole matching-open component of public parent/enclose
tree navigation.
-/
def ConcreteSuccinctTreeNavigationFromCloseLCATraceTarget : Prop :=
  forall (shape : Cartesian.CartesianShape) (idx close : Nat),
    SuccinctSpace.bpCloseOfInorder? shape idx = some close ->
      (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape close close).toCosted.erase =
        matchingOpenOfClose? shape close

/--
Formal obstruction for the current close/LCA-store adapter route toward a
succinct BP tree-navigation capstone.

On the one-node Cartesian shape, the all-size structural close/LCA trace for a
singleton close/close query returns the closing position. Public matching-open
semantics return the opening position. Therefore the existing payload-backed
close/LCA WordRAM trace cannot be relabeled into the matching-open leg needed
by `encloseOpenOfInorderFastCosted`, `parentOfInorderFastCosted`, or the fast
subtree-interval operation.

This does not rule out a real succinct tree-navigation directory. It only rules
out this adapter path, so the next positive target is a dedicated succinct
matching-open/enclose/matching-close directory.
-/
theorem concreteSuccinctTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStore_obstruction :
    ¬ ConcreteSuccinctTreeNavigationFromCloseLCATraceTarget := by
  intro htarget
  let shape :=
    Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
      Cartesian.CartesianShape.empty
  have hclose :
      SuccinctSpace.bpCloseOfInorder? shape 0 = some 1 := by
    simp [shape, SuccinctSpace.bpCloseOfInorder?,
      Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode]
  have hanswer :
      SuccinctSpace.bpCloseOfInorder?
          shape (scanWindow shape.representative 0 1) =
        some 1 := by
    simp [shape, SuccinctSpace.bpCloseOfInorder?, scanWindow,
      Cartesian.CartesianShape.size, Cartesian.CartesianShape.bpCode]
  have hlcaCosted :
      (SuccinctFinal.concreteBPNativeLCACloseCanonicalInterpretedCosted
          shape 1 1).erase =
        some 1 := by
    exact
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalLcaCloseCostedWithRankSeed_exact_of_query
        (SuccinctFinal.concreteBPNativeRankCloseInterpretedCosted shape)
        (shape := shape) (left := 0) (len := 1)
        (leftClose := 1) (rightClose := 1) (answerClose := 1)
        (by
          intro pos
          rw [concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted]
          exact
            SuccinctFinal.concreteBPNativeRankCloseCosted_exact
              concreteBPCloseNavigationAccessFamily shape pos)
        (by omega)
        (by
          simp [shape, Cartesian.CartesianShape.size])
        hclose hclose hanswer
  have hlcaTrace :
      (SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape 1 1).toCosted.erase =
        some 1 := by
    rw [concreteBPCloseNavigationLCACloseGlobalTraceResult_refines]
    exact hlcaCosted
  have hclaimed := htarget shape 0 1 hclose
  rw [hlcaTrace] at hclaimed
  have hnotMatchingOpen :
      ¬ matchingOpenOfClose? shape 1 = some 1 := by
    simp [shape, matchingOpenOfClose?, matchingOpenSearchRef,
      bpPrefixExcess, Cartesian.CartesianShape.bpCode,
      Succinct.rankPrefix]
  exact hnotMatchingOpen hclaimed.symm

end BPNavigation

end RMQ

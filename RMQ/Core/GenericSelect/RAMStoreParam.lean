import RMQ.Core.GenericSelect.RAM
import RMQ.Core.WordRAM.ReadStoreEval

/-!
# Store-parametric select-tower evaluators

Store-parameterized (`WithStore`) twins of the relabeled select-tower trace
evaluators in `GenericSelect.RAM`.  Every payload read is performed against a
supplied `WordRAM.ReadStore` pulled back along the same segment maps used by
the canonical relabeled evaluators, so the value and trace are genuine
functions of the supplied store.  Each layer comes with:

* `_matchesReadStore` — for every store, emitted read events report exactly
  that store's words;
* `_eq_of_pullback` — under the pullback agreements with the component-local
  stores, the evaluator is literally the canonical relabeled trace; and
* `_store_parametric` — stores agreeing on the mapped segments produce the
  same value and trace.
-/

namespace RMQ

namespace WordRAM

namespace TraceResult

/-- Store-parametric relabeled first-order program atom: evaluate against the
supplied store pulled back along the segment map, then relabel the trace. -/
def ofProgramWithStore (segmentMap : Nat -> Nat) (store : ReadStore)
    {ty : Ty} (program : Program ty) : TraceResult ty.denote :=
  relabelReadSegmentsWith segmentMap
    (ofResult (program.evalR (store.pullback segmentMap)))

theorem ofProgramWithStore_eq_of_pullback
    {segmentMap : Nat -> Nat} {store : ReadStore} {localStore : Store}
    (hpull : store.pullback segmentMap = ReadStore.ofStore localStore)
    {ty : Ty} (program : Program ty) :
    ofProgramWithStore segmentMap store program =
      relabelReadSegmentsWith segmentMap
        (ofResult (program.eval localStore)) := by
  unfold ofProgramWithStore
  rw [hpull, Program.evalR_ofStore]

theorem ofProgramWithStore_store_parametric
    {segmentMap : Nat -> Nat} {storeA storeB : ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord? (segmentMap segment) index =
          storeB.readWord? (segmentMap segment) index)
    {ty : Ty} (program : Program ty) :
    ofProgramWithStore segmentMap storeA program =
      ofProgramWithStore segmentMap storeB program := by
  unfold ofProgramWithStore
  rw [ReadStore.pullback_eq_of_agree_on_map segmentMap hagree]

theorem ofProgramWithStore_matchesReadStore
    (segmentMap : Nat -> Nat) (store : ReadStore)
    {ty : Ty} (program : Program ty) :
    forall event,
      event ∈ (ofProgramWithStore segmentMap store program).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp only [ofProgramWithStore, relabelReadSegmentsWith_trace,
    ofResult_trace] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  exact
    TraceEvent.relabelReadSegmentWith_matchesReadStore_of_pullback
      segmentMap store
      (Program.evalR_matchesReadStore program
        (store.pullback segmentMap) inner hinner)

/-- Store-parametric relabeled register-program atom. -/
def ofNatProgramWithStore (segmentMap : Nat -> Nat) (store : ReadStore)
    (program : Register.NatProgram) (regs : Register.RegFile) :
    TraceResult Nat :=
  relabelReadSegmentsWith segmentMap
    (ofResult (program.evalR (store.pullback segmentMap) regs))

theorem ofNatProgramWithStore_eq_of_pullback
    {segmentMap : Nat -> Nat} {store : ReadStore} {localStore : Store}
    (hpull : store.pullback segmentMap = ReadStore.ofStore localStore)
    (program : Register.NatProgram) (regs : Register.RegFile) :
    ofNatProgramWithStore segmentMap store program regs =
      relabelReadSegmentsWith segmentMap
        (ofResult (program.eval localStore regs)) := by
  unfold ofNatProgramWithStore
  rw [hpull, Register.NatProgram.evalR_ofStore]

theorem ofNatProgramWithStore_store_parametric
    {segmentMap : Nat -> Nat} {storeA storeB : ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord? (segmentMap segment) index =
          storeB.readWord? (segmentMap segment) index)
    (program : Register.NatProgram) (regs : Register.RegFile) :
    ofNatProgramWithStore segmentMap storeA program regs =
      ofNatProgramWithStore segmentMap storeB program regs := by
  unfold ofNatProgramWithStore
  rw [ReadStore.pullback_eq_of_agree_on_map segmentMap hagree]

theorem ofNatProgramWithStore_matchesReadStore
    (segmentMap : Nat -> Nat) (store : ReadStore)
    (program : Register.NatProgram) (regs : Register.RegFile) :
    forall event,
      event ∈ (ofNatProgramWithStore segmentMap store program regs).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp only [ofNatProgramWithStore, relabelReadSegmentsWith_trace,
    ofResult_trace] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  exact
    TraceEvent.relabelReadSegmentWith_matchesReadStore_of_pullback
      segmentMap store
      (Register.NatProgram.evalR_matchesReadStore program
        (store.pullback segmentMap) regs inner hinner)

end TraceResult

end WordRAM

namespace SuccinctRank

namespace TwoLevelPayloadLiveStoredWordRankData

open WordRAM.Register

/-- Store-parametric relabeled two-level rank leaf. -/
def rankTraceResultRelabeledWithStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (rankBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (target : Bool) (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofNatProgramWithStore
    (WordRAM.tripleSegmentMap rankBase deadSegment) store
    (data.rankRegisterProgram target (NatExpr.reg 0))
    (RegFile.withNat1 pos)

theorem rankTraceResultRelabeledWithStore_eq_of_pullback
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {rankBase deadSegment : Nat} {store : WordRAM.ReadStore}
    {target : Bool}
    (hpull :
      store.pullback (WordRAM.tripleSegmentMap rankBase deadSegment) =
        WordRAM.ReadStore.ofStore (data.rankRegisterWordRAMStore target))
    (pos : Nat) :
    data.rankTraceResultRelabeledWithStore rankBase deadSegment store
        target pos =
      WordRAM.TraceResult.relabelReadSegmentsWith
        (WordRAM.tripleSegmentMap rankBase deadSegment)
        (data.rankTraceResult target pos) := by
  unfold rankTraceResultRelabeledWithStore rankTraceResult
  rw [WordRAM.TraceResult.ofNatProgramWithStore_eq_of_pullback hpull]

theorem rankTraceResultRelabeledWithStore_store_parametric
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {rankBase deadSegment : Nat} {storeA storeB : WordRAM.ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord?
            (WordRAM.tripleSegmentMap rankBase deadSegment segment) index =
          storeB.readWord?
            (WordRAM.tripleSegmentMap rankBase deadSegment segment) index)
    (target : Bool) (pos : Nat) :
    data.rankTraceResultRelabeledWithStore rankBase deadSegment storeA
        target pos =
      data.rankTraceResultRelabeledWithStore rankBase deadSegment storeB
        target pos := by
  unfold rankTraceResultRelabeledWithStore
  rw [WordRAM.TraceResult.ofNatProgramWithStore_store_parametric hagree]

theorem rankTraceResultRelabeledWithStore_matchesReadStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (rankBase deadSegment : Nat) (store : WordRAM.ReadStore)
    (target : Bool) (pos : Nat) :
    forall event,
      event ∈
          (data.rankTraceResultRelabeledWithStore rankBase deadSegment
            store target pos).trace ->
        event.matchesReadStore store := by
  exact
    WordRAM.TraceResult.ofNatProgramWithStore_matchesReadStore
      (WordRAM.tripleSegmentMap rankBase deadSegment) store
      (data.rankRegisterProgram target (NatExpr.reg 0))
      (RegFile.withNat1 pos)

end TwoLevelPayloadLiveStoredWordRankData

end SuccinctRank

namespace GenericSelect

namespace FixedWidthSparseDenseSelectDenseLocalEntryTable

/-- Store-parametric relabeled read of the four-field entry table. -/
def readTraceResultRelabeledWithStore
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (i : Nat) :
    WordRAM.TraceResult (Option SparseDenseSelectDenseLocalEntry) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.ofProgramWithStore
      (WordRAM.singletonSegmentMap layout.baseOccurrence layout.deadSegment)
      store (table.baseOccurrenceTable.readProgram i))
    fun baseOccurrence? =>
      WordRAM.TraceResult.bind
        (WordRAM.TraceResult.ofProgramWithStore
          (WordRAM.singletonSegmentMap layout.baseWordIndex
            layout.deadSegment)
          store (table.baseWordIndexTable.readProgram i))
        fun baseWordIndex? =>
          WordRAM.TraceResult.bind
            (WordRAM.TraceResult.ofProgramWithStore
              (WordRAM.singletonSegmentMap layout.rankBefore
                layout.deadSegment)
              store (table.rankBeforeTable.readProgram i))
            fun rankBefore? =>
              WordRAM.TraceResult.map
                (fun firstOffset? =>
                  entryOfFields baseOccurrence? baseWordIndex?
                    rankBefore? firstOffset?)
                (WordRAM.TraceResult.ofProgramWithStore
                  (WordRAM.singletonSegmentMap layout.firstOffset
                    layout.deadSegment)
                  store (table.firstOffsetTable.readProgram i))

theorem readTraceResultRelabeledWithStore_eq_of_pullback
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    {layout : SparseDenseEntryTableTraceSegmentBases}
    {store : WordRAM.ReadStore}
    (hbaseOccurrence :
      store.pullback
          (WordRAM.singletonSegmentMap layout.baseOccurrence
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore table.baseOccurrenceTable.wordRAMStore)
    (hbaseWordIndex :
      store.pullback
          (WordRAM.singletonSegmentMap layout.baseWordIndex
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore table.baseWordIndexTable.wordRAMStore)
    (hrankBefore :
      store.pullback
          (WordRAM.singletonSegmentMap layout.rankBefore
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore table.rankBeforeTable.wordRAMStore)
    (hfirstOffset :
      store.pullback
          (WordRAM.singletonSegmentMap layout.firstOffset
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore table.firstOffsetTable.wordRAMStore)
    (i : Nat) :
    table.readTraceResultRelabeledWithStore layout store i =
      table.readTraceResultRelabeled layout i := by
  unfold readTraceResultRelabeledWithStore readTraceResultRelabeled
  rw [WordRAM.TraceResult.ofProgramWithStore_eq_of_pullback hbaseOccurrence,
    WordRAM.TraceResult.ofProgramWithStore_eq_of_pullback hbaseWordIndex,
    WordRAM.TraceResult.ofProgramWithStore_eq_of_pullback hrankBefore,
    WordRAM.TraceResult.ofProgramWithStore_eq_of_pullback hfirstOffset]

theorem readTraceResultRelabeledWithStore_store_parametric
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    {layout : SparseDenseEntryTableTraceSegmentBases}
    {storeA storeB : WordRAM.ReadStore}
    (hbaseOccurrence :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.baseOccurrence
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.baseOccurrence
              layout.deadSegment segment) index)
    (hbaseWordIndex :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.baseWordIndex
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.baseWordIndex
              layout.deadSegment segment) index)
    (hrankBefore :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.rankBefore
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.rankBefore
              layout.deadSegment segment) index)
    (hfirstOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.firstOffset
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.firstOffset
              layout.deadSegment segment) index)
    (i : Nat) :
    table.readTraceResultRelabeledWithStore layout storeA i =
      table.readTraceResultRelabeledWithStore layout storeB i := by
  unfold readTraceResultRelabeledWithStore
  rw [WordRAM.TraceResult.ofProgramWithStore_store_parametric hbaseOccurrence,
    WordRAM.TraceResult.ofProgramWithStore_store_parametric hbaseWordIndex,
    WordRAM.TraceResult.ofProgramWithStore_store_parametric hrankBefore,
    WordRAM.TraceResult.ofProgramWithStore_store_parametric hfirstOffset]

theorem readTraceResultRelabeledWithStore_matchesReadStore
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (store : WordRAM.ReadStore) (i : Nat) :
    forall event,
      event ∈
          (table.readTraceResultRelabeledWithStore layout store i).trace ->
        event.matchesReadStore store := by
  unfold readTraceResultRelabeledWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      WordRAM.TraceResult.ofProgramWithStore_matchesReadStore _ store _
  · intro baseOccurrence?
    apply WordRAM.TraceResult.bind_trace_forall
    · exact
        WordRAM.TraceResult.ofProgramWithStore_matchesReadStore _ store _
    · intro baseWordIndex?
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WordRAM.TraceResult.ofProgramWithStore_matchesReadStore _ store _
      · intro rankBefore?
        apply WordRAM.TraceResult.map_trace_forall
        exact
          WordRAM.TraceResult.ofProgramWithStore_matchesReadStore _ store _

end FixedWidthSparseDenseSelectDenseLocalEntryTable

/-- Store-parametric relabeled relative-offset read. -/
def relativeOffsetReadTraceResultRelabeledWithStore
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (store : WordRAM.ReadStore)
    (base slot : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun offset? => offset?.map (fun offset => base + offset))
    (WordRAM.TraceResult.ofProgramWithStore
      (WordRAM.singletonSegmentMap segmentBase deadSegment)
      store (table.readProgram slot))

theorem relativeOffsetReadTraceResultRelabeledWithStore_eq_of_pullback
    {entries : List Nat} {width : Nat}
    {segmentBase deadSegment : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore}
    (hpull :
      store.pullback
          (WordRAM.singletonSegmentMap segmentBase deadSegment) =
        WordRAM.ReadStore.ofStore table.wordRAMStore)
    (base slot : Nat) :
    relativeOffsetReadTraceResultRelabeledWithStore
        segmentBase deadSegment table store base slot =
      relativeOffsetReadTraceResultRelabeled
        segmentBase deadSegment table base slot := by
  unfold relativeOffsetReadTraceResultRelabeledWithStore
    relativeOffsetReadTraceResultRelabeled
  rw [WordRAM.TraceResult.ofProgramWithStore_eq_of_pullback hpull]

theorem relativeOffsetReadTraceResultRelabeledWithStore_store_parametric
    {entries : List Nat} {width : Nat}
    {segmentBase deadSegment : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap segmentBase deadSegment segment)
            index)
    (base slot : Nat) :
    relativeOffsetReadTraceResultRelabeledWithStore
        segmentBase deadSegment table storeA base slot =
      relativeOffsetReadTraceResultRelabeledWithStore
        segmentBase deadSegment table storeB base slot := by
  unfold relativeOffsetReadTraceResultRelabeledWithStore
  rw [WordRAM.TraceResult.ofProgramWithStore_store_parametric hagree]

theorem relativeOffsetReadTraceResultRelabeledWithStore_matchesReadStore
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (store : WordRAM.ReadStore)
    (base slot : Nat) :
    forall event,
      event ∈
          (relativeOffsetReadTraceResultRelabeledWithStore
            segmentBase deadSegment table store base slot).trace ->
        event.matchesReadStore store := by
  unfold relativeOffsetReadTraceResultRelabeledWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact WordRAM.TraceResult.ofProgramWithStore_matchesReadStore _ store _

namespace SparseExceptionDirectory

/-- Store-parametric relabeled sparse-exception directory read. -/
def readTraceResultRelabeledWithStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (store : WordRAM.ReadStore)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (directory.rankData.rankTraceResultRelabeledWithStore
      layout.rankBase layout.deadSegment store true localSlot)
    fun exceptionRank =>
      relativeOffsetReadTraceResultRelabeledWithStore
        layout.relativeBase layout.deadSegment
        directory.relativeTable store base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readTraceResultRelabeledWithStore_eq_of_pullback
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionDirectoryTraceSegmentBases}
    {store : WordRAM.ReadStore}
    (hrank :
      store.pullback
          (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment) =
        WordRAM.ReadStore.ofStore
          (directory.rankData.rankRegisterWordRAMStore true))
    (hrelative :
      store.pullback
          (WordRAM.singletonSegmentMap layout.relativeBase
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore directory.relativeTable.wordRAMStore)
    (base localSlot localOccurrence : Nat) :
    directory.readTraceResultRelabeledWithStore
        layout store base localSlot localOccurrence =
      directory.readTraceResultRelabeled
        layout base localSlot localOccurrence := by
  unfold readTraceResultRelabeledWithStore readTraceResultRelabeled
  have hrel :=
    fun base slot =>
      relativeOffsetReadTraceResultRelabeledWithStore_eq_of_pullback
        directory.relativeTable hrelative base slot
  simp only [directory.rankData.rankTraceResultRelabeledWithStore_eq_of_pullback
    hrank, hrel]

theorem readTraceResultRelabeledWithStore_store_parametric
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionDirectoryTraceSegmentBases}
    {storeA storeB : WordRAM.ReadStore}
    (hrank :
      forall segment index,
        storeA.readWord?
            (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment
              segment) index =
          storeB.readWord?
            (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment
              segment) index)
    (hrelative :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.relativeBase
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.relativeBase
              layout.deadSegment segment) index)
    (base localSlot localOccurrence : Nat) :
    directory.readTraceResultRelabeledWithStore
        layout storeA base localSlot localOccurrence =
      directory.readTraceResultRelabeledWithStore
        layout storeB base localSlot localOccurrence := by
  unfold readTraceResultRelabeledWithStore
  have hrel :=
    fun base slot =>
      relativeOffsetReadTraceResultRelabeledWithStore_store_parametric
        directory.relativeTable hrelative base slot
  simp only [directory.rankData.rankTraceResultRelabeledWithStore_store_parametric
    hrank, hrel]

theorem readTraceResultRelabeledWithStore_matchesReadStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (store : WordRAM.ReadStore)
    (base localSlot localOccurrence : Nat) :
    forall event,
      event ∈
          (directory.readTraceResultRelabeledWithStore
            layout store base localSlot localOccurrence).trace ->
        event.matchesReadStore store := by
  unfold readTraceResultRelabeledWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      directory.rankData.rankTraceResultRelabeledWithStore_matchesReadStore
        layout.rankBase layout.deadSegment store true localSlot
  · exact
      relativeOffsetReadTraceResultRelabeledWithStore_matchesReadStore
        layout.relativeBase layout.deadSegment directory.relativeTable
        store base _

end SparseExceptionDirectory

/--
Store-parametric dense two-word select branch against a component-local read
store.  Structure mirrors `denseTwoWordSelectTraceResult`, with each packed
BP-code word read evaluated against the supplied local store.
-/
def denseTwoWordSelectTraceResultWithStoreLocal
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (localStore : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.ofResult
      ((bitWords.store.readProgram firstWordIndex).evalR localStore))
    fun firstWord? =>
      match firstWord? with
      | none => WordRAM.TraceResult.pure none
      | some firstWord =>
          WordRAM.TraceResult.bind
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
              target firstWord firstOffset)
            fun beforeFirst =>
              WordRAM.TraceResult.bind
                (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                  target firstWord firstWord.length)
                fun uptoFirst =>
                  let firstCount := uptoFirst - beforeFirst
                  if localOccurrence < firstCount then
                    WordRAM.TraceResult.map
                      (fun local? =>
                        local?.map fun offset => firstWordStart + offset)
                      (wordSelectTraceResult target firstWord
                        (beforeFirst + localOccurrence))
                  else
                    WordRAM.TraceResult.bind
                      (WordRAM.TraceResult.ofResult
                        ((bitWords.store.readProgram
                          (firstWordIndex + 1)).evalR localStore))
                      fun secondWord? =>
                        match secondWord? with
                        | none => WordRAM.TraceResult.pure none
                        | some secondWord =>
                            WordRAM.TraceResult.map
                              (fun local? =>
                                local?.map fun offset =>
                                  (firstWordIndex + 1) * wordSize + offset)
                              (wordSelectTraceResult target secondWord
                                (localOccurrence - firstCount))

theorem denseTwoWordSelectTraceResultWithStoreLocal_ofStore
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    denseTwoWordSelectTraceResultWithStoreLocal target bitWords
        (WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore)
        basePosition baseOccurrence q =
      denseTwoWordSelectTraceResult
        target bitWords basePosition baseOccurrence q := by
  unfold denseTwoWordSelectTraceResultWithStoreLocal
    denseTwoWordSelectTraceResult
  simp only [WordRAM.Program.evalR_ofStore]
  rfl

theorem denseTwoWordSelectTraceResultWithStoreLocal_matchesReadStore
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (localStore : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResultWithStoreLocal target bitWords
            localStore basePosition baseOccurrence q).trace ->
        event.matchesReadStore localStore := by
  unfold denseTwoWordSelectTraceResultWithStoreLocal
  apply WordRAM.TraceResult.bind_trace_forall
  · intro event hmem
    simp only [WordRAM.TraceResult.ofResult_trace] at hmem
    exact
      WordRAM.Program.evalR_matchesReadStore
        (bitWords.store.readProgram (basePosition / wordSize))
        localStore event hmem
  · cases hfirst :
        (WordRAM.TraceResult.ofResult
          ((bitWords.store.readProgram (basePosition / wordSize)).evalR
            localStore)).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ _
    | some firstWord =>
        apply WordRAM.TraceResult.bind_trace_forall
        · exact
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
              target firstWord _ localStore
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
                target firstWord _ localStore
          · dsimp only []
            split
            · apply WordRAM.TraceResult.map_trace_forall
              exact
                wordSelectTraceResult_matchesReadStore target firstWord _
                  localStore
            · apply WordRAM.TraceResult.bind_trace_forall
              · intro event hmem
                simp only [WordRAM.TraceResult.ofResult_trace] at hmem
                exact
                  WordRAM.Program.evalR_matchesReadStore
                    (bitWords.store.readProgram
                      (basePosition / wordSize + 1))
                    localStore event hmem
              · cases hsecond :
                    (WordRAM.TraceResult.ofResult
                      ((bitWords.store.readProgram
                        (basePosition / wordSize + 1)).evalR
                          localStore)).value with
                | none =>
                    exact WordRAM.TraceResult.pure_trace_forall _ _
                | some secondWord =>
                    apply WordRAM.TraceResult.map_trace_forall
                    exact
                      wordSelectTraceResult_matchesReadStore target
                        secondWord _ localStore

/-- Store-parametric relabeled dense two-word select branch. -/
def denseTwoWordSelectTraceResultRelabeledWithStore
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
    (denseTwoWordSelectTraceResultWithStoreLocal target bitWords
      (store.pullback
        (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment))
      basePosition baseOccurrence q)

theorem denseTwoWordSelectTraceResultRelabeledWithStore_eq_of_pullback
    {bitWordSegmentBase deadSegment : Nat}
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    {store : WordRAM.ReadStore}
    (hpull :
      store.pullback
          (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment) =
        WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore)
    (basePosition baseOccurrence q : Nat) :
    denseTwoWordSelectTraceResultRelabeledWithStore
        bitWordSegmentBase deadSegment target bitWords store
        basePosition baseOccurrence q =
      denseTwoWordSelectTraceResultRelabeled
        bitWordSegmentBase deadSegment target bitWords
        basePosition baseOccurrence q := by
  unfold denseTwoWordSelectTraceResultRelabeledWithStore
    denseTwoWordSelectTraceResultRelabeled
  rw [hpull, denseTwoWordSelectTraceResultWithStoreLocal_ofStore]

theorem denseTwoWordSelectTraceResultRelabeledWithStore_store_parametric
    {bitWordSegmentBase deadSegment : Nat}
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment
              segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment
              segment) index)
    (basePosition baseOccurrence q : Nat) :
    denseTwoWordSelectTraceResultRelabeledWithStore
        bitWordSegmentBase deadSegment target bitWords storeA
        basePosition baseOccurrence q =
      denseTwoWordSelectTraceResultRelabeledWithStore
        bitWordSegmentBase deadSegment target bitWords storeB
        basePosition baseOccurrence q := by
  unfold denseTwoWordSelectTraceResultRelabeledWithStore
  rw [WordRAM.ReadStore.pullback_eq_of_agree_on_map
    (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment) hagree]

theorem denseTwoWordSelectTraceResultRelabeledWithStore_matchesReadStore
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResultRelabeledWithStore
            bitWordSegmentBase deadSegment target bitWords store
            basePosition baseOccurrence q).trace ->
        event.matchesReadStore store := by
  unfold denseTwoWordSelectTraceResultRelabeledWithStore
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (denseTwoWordSelectTraceResultWithStoreLocal target bitWords
        (store.pullback
          (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment))
        basePosition baseOccurrence q)
      (store.pullback
        (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment))
      store
      (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
      (fun _segment _index => rfl)
      (denseTwoWordSelectTraceResultWithStoreLocal_matchesReadStore
        target bitWords _ basePosition baseOccurrence q)

namespace SparseExceptionSelectData

/--
Store-parametric relabeled sparse-exception select query.

Structure mirrors `selectTraceResultRelabeled`; every payload read is served by
the supplied read store pulled back along the same segment layout.
-/
def selectTraceResultRelabeledWithStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (store : WordRAM.ReadStore)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeledWithStore
        layout.superTable store
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (data.longFlagRankData.rankTraceResultRelabeledWithStore
                layout.longFlagRankBase layout.deadSegment store true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadTraceResultRelabeledWithStore
                  layout.longRelativeBase layout.deadSegment
                  data.longSuperRelativeTable store
                  (relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            WordRAM.TraceResult.bind
              (data.localTable.readTraceResultRelabeledWithStore
                layout.localTable store localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResultRelabeledWithStore
                      layout.sparseDirectory store
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectTraceResultRelabeledWithStore
                      layout.bitWordBase layout.deadSegment
                      target data.bitWords store
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

theorem selectTraceResultRelabeledWithStore_eq_of_pullback
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionSelectTraceSegmentLayout}
    {store : WordRAM.ReadStore}
    (hsuperBaseOccurrence :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.baseOccurrenceTable.wordRAMStore)
    (hsuperBaseWordIndex :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.baseWordIndexTable.wordRAMStore)
    (hsuperRankBefore :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.rankBefore
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.rankBeforeTable.wordRAMStore)
    (hsuperFirstOffset :
      store.pullback
          (WordRAM.singletonSegmentMap layout.superTable.firstOffset
            layout.superTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.superTable.firstOffsetTable.wordRAMStore)
    (hlongRank :
      store.pullback
          (WordRAM.tripleSegmentMap layout.longFlagRankBase
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore
          (data.longFlagRankData.rankRegisterWordRAMStore true))
    (hlongRelative :
      store.pullback
          (WordRAM.singletonSegmentMap layout.longRelativeBase
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.longSuperRelativeTable.wordRAMStore)
    (hlocalBaseOccurrence :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.baseOccurrenceTable.wordRAMStore)
    (hlocalBaseWordIndex :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.baseWordIndexTable.wordRAMStore)
    (hlocalRankBefore :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.rankBefore
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.rankBeforeTable.wordRAMStore)
    (hlocalFirstOffset :
      store.pullback
          (WordRAM.singletonSegmentMap layout.localTable.firstOffset
            layout.localTable.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.localTable.firstOffsetTable.wordRAMStore)
    (hsparseRank :
      store.pullback
          (WordRAM.tripleSegmentMap layout.sparseDirectory.rankBase
            layout.sparseDirectory.deadSegment) =
        WordRAM.ReadStore.ofStore
          (data.sparseDirectory.rankData.rankRegisterWordRAMStore true))
    (hsparseRelative :
      store.pullback
          (WordRAM.singletonSegmentMap layout.sparseDirectory.relativeBase
            layout.sparseDirectory.deadSegment) =
        WordRAM.ReadStore.ofStore
          data.sparseDirectory.relativeTable.wordRAMStore)
    (hbitWords :
      store.pullback
          (WordRAM.singletonSegmentMap layout.bitWordBase
            layout.deadSegment) =
        WordRAM.ReadStore.ofStore data.bitWords.store.wordRAMStore)
    (idx : Nat) :
    data.selectTraceResultRelabeledWithStore layout store idx =
      data.selectTraceResultRelabeled layout idx := by
  unfold selectTraceResultRelabeledWithStore selectTraceResultRelabeled
  have hsuperEq :=
    fun slot =>
      data.superTable.readTraceResultRelabeledWithStore_eq_of_pullback
        hsuperBaseOccurrence hsuperBaseWordIndex hsuperRankBefore
        hsuperFirstOffset slot
  have hlocalEq :=
    fun slot =>
      data.localTable.readTraceResultRelabeledWithStore_eq_of_pullback
        hlocalBaseOccurrence hlocalBaseWordIndex hlocalRankBefore
        hlocalFirstOffset slot
  have hrankEq :=
    fun pos =>
      data.longFlagRankData.rankTraceResultRelabeledWithStore_eq_of_pullback
        hlongRank pos
  have hrelEq :=
    fun base slot =>
      relativeOffsetReadTraceResultRelabeledWithStore_eq_of_pullback
        data.longSuperRelativeTable hlongRelative base slot
  have hsparseEq :=
    fun base localSlot localOccurrence =>
      data.sparseDirectory.readTraceResultRelabeledWithStore_eq_of_pullback
        hsparseRank hsparseRelative base localSlot localOccurrence
  have hdenseEq :=
    fun basePosition baseOccurrence q =>
      denseTwoWordSelectTraceResultRelabeledWithStore_eq_of_pullback
        target data.bitWords hbitWords basePosition baseOccurrence q
  simp only [hsuperEq, hlocalEq, hrankEq, hrelEq, hsparseEq, hdenseEq]
  rfl

theorem selectTraceResultRelabeledWithStore_store_parametric
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    {layout : SparseExceptionSelectTraceSegmentLayout}
    {storeA storeB : WordRAM.ReadStore}
    (hsuperBaseOccurrence :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseOccurrence
              layout.superTable.deadSegment segment) index)
    (hsuperBaseWordIndex :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.baseWordIndex
              layout.superTable.deadSegment segment) index)
    (hsuperRankBefore :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.rankBefore
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.rankBefore
              layout.superTable.deadSegment segment) index)
    (hsuperFirstOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.firstOffset
              layout.superTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.superTable.firstOffset
              layout.superTable.deadSegment segment) index)
    (hlongRank :
      forall segment index,
        storeA.readWord?
            (WordRAM.tripleSegmentMap layout.longFlagRankBase
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.tripleSegmentMap layout.longFlagRankBase
              layout.deadSegment segment) index)
    (hlongRelative :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.longRelativeBase
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.longRelativeBase
              layout.deadSegment segment) index)
    (hlocalBaseOccurrence :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseOccurrence
              layout.localTable.deadSegment segment) index)
    (hlocalBaseWordIndex :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.baseWordIndex
              layout.localTable.deadSegment segment) index)
    (hlocalRankBefore :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.rankBefore
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.rankBefore
              layout.localTable.deadSegment segment) index)
    (hlocalFirstOffset :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.firstOffset
              layout.localTable.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.localTable.firstOffset
              layout.localTable.deadSegment segment) index)
    (hsparseRank :
      forall segment index,
        storeA.readWord?
            (WordRAM.tripleSegmentMap layout.sparseDirectory.rankBase
              layout.sparseDirectory.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.tripleSegmentMap layout.sparseDirectory.rankBase
              layout.sparseDirectory.deadSegment segment) index)
    (hsparseRelative :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.sparseDirectory.relativeBase
              layout.sparseDirectory.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.sparseDirectory.relativeBase
              layout.sparseDirectory.deadSegment segment) index)
    (hbitWords :
      forall segment index,
        storeA.readWord?
            (WordRAM.singletonSegmentMap layout.bitWordBase
              layout.deadSegment segment) index =
          storeB.readWord?
            (WordRAM.singletonSegmentMap layout.bitWordBase
              layout.deadSegment segment) index)
    (idx : Nat) :
    data.selectTraceResultRelabeledWithStore layout storeA idx =
      data.selectTraceResultRelabeledWithStore layout storeB idx := by
  unfold selectTraceResultRelabeledWithStore
  have hsuperEq :=
    fun slot =>
      data.superTable.readTraceResultRelabeledWithStore_store_parametric
        hsuperBaseOccurrence hsuperBaseWordIndex hsuperRankBefore
        hsuperFirstOffset slot
  have hlocalEq :=
    fun slot =>
      data.localTable.readTraceResultRelabeledWithStore_store_parametric
        hlocalBaseOccurrence hlocalBaseWordIndex hlocalRankBefore
        hlocalFirstOffset slot
  have hrankEq :=
    fun pos =>
      data.longFlagRankData.rankTraceResultRelabeledWithStore_store_parametric
        hlongRank true pos
  have hrelEq :=
    fun base slot =>
      relativeOffsetReadTraceResultRelabeledWithStore_store_parametric
        data.longSuperRelativeTable hlongRelative base slot
  have hsparseEq :=
    fun base localSlot localOccurrence =>
      data.sparseDirectory.readTraceResultRelabeledWithStore_store_parametric
        hsparseRank hsparseRelative base localSlot localOccurrence
  have hdenseEq :=
    fun basePosition baseOccurrence q =>
      denseTwoWordSelectTraceResultRelabeledWithStore_store_parametric
        target data.bitWords hbitWords basePosition baseOccurrence q
  simp only [hsuperEq, hlocalEq, hrankEq, hrelEq, hsparseEq, hdenseEq]

theorem selectTraceResultRelabeledWithStore_matchesReadStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (store : WordRAM.ReadStore)
    (idx : Nat) :
    forall event,
      event ∈
          (data.selectTraceResultRelabeledWithStore layout store idx).trace ->
        event.matchesReadStore store := by
  unfold selectTraceResultRelabeledWithStore
  by_cases hvalid : idx < occurrenceCount bits target
  · intro event hmem
    simp [hvalid, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact
        data.superTable.readTraceResultRelabeledWithStore_matchesReadStore
          layout.superTable store
          (selectSuperSlot (data.queryOccurrence idx) data.superStride)
          event hmem
    · cases hsuperValue :
          (data.superTable.readTraceResultRelabeledWithStore
            layout.superTable store
            (selectSuperSlot (data.queryOccurrence idx)
              data.superStride)).value with
      | none =>
          simp [hsuperValue] at hmem
      | some super =>
          by_cases hlong :
              relativeSplitSelectEntryIsMarked super = true
          · simp [hsuperValue, hlong] at hmem
            rcases hmem with hmem | hmem
            · exact
                data.longFlagRankData.rankTraceResultRelabeledWithStore_matchesReadStore
                  layout.longFlagRankBase layout.deadSegment store true
                  (selectSuperSlot (data.queryOccurrence idx)
                    data.superStride)
                  event hmem
            · exact
                relativeOffsetReadTraceResultRelabeledWithStore_matchesReadStore
                  layout.longRelativeBase layout.deadSegment
                  data.longSuperRelativeTable store _ _ event hmem
          · simp [hsuperValue, hlong] at hmem
            rcases hmem with hmem | hmem
            · exact
                data.localTable.readTraceResultRelabeledWithStore_matchesReadStore
                  layout.localTable store _ event hmem
            · cases hlocalValue :
                  (data.localTable.readTraceResultRelabeledWithStore
                    layout.localTable store
                    (relativeSplitSelectLocalSlot
                      (data.queryOccurrence idx) data.superStride
                      data.localSlotsPerSuper data.localStride
                      super)).value with
              | none =>
                  simp [hlocalValue] at hmem
              | some loc =>
                  by_cases hsparseBranch :
                      relativeSplitSelectEntryIsMarked loc = true
                  · exact
                      data.sparseDirectory.readTraceResultRelabeledWithStore_matchesReadStore
                        layout.sparseDirectory store _ _ _ event
                        (by simpa [hlocalValue, hsparseBranch] using hmem)
                  · exact
                      denseTwoWordSelectTraceResultRelabeledWithStore_matchesReadStore
                        layout.bitWordBase layout.deadSegment target
                        data.bitWords store _ _ _ event
                        (by simpa [hlocalValue, hsparseBranch] using hmem)
  · intro event hmem
    simp [hvalid] at hmem

end SparseExceptionSelectData

end GenericSelect

end RMQ

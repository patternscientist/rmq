import RMQ.Core.GenericSelect.Source
import RMQ.Core.SuccinctSpace.RankSelectRAM

/-!
# Word-RAM bridges for generic sparse-exception select

This module keeps the generic sparse-exception select surface concrete: the
interpreted query consumes the `SparseExceptionSelectData` tables and word
stores directly, replacing each payload read by the existing first-order
`WordRAM` read interpretation and then proving that the result refines the
older `Costed` query.
-/

namespace RMQ

namespace SuccinctRank

namespace TwoLevelPayloadLiveStoredWordRankData

open RMQ.WordRAM.Register

/-- Word-RAM-backed word-rank primitive for a word already obtained by a read. -/
def wordRankInterpretedCosted
    (target : Bool) (word : List Bool) (limit : Nat) : Costed Nat :=
  ((WordRAM.Program.sampledRank target limit
      (WordRAM.Program.pure (some 0))
      (WordRAM.Program.pure (some word))).eval
    { wordSegments := #[] }).toCosted

/-- Trace-preserving version of `wordRankInterpretedCosted`. -/
def wordRankTraceResult
    (target : Bool) (word : List Bool) (limit : Nat) :
    WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    ((WordRAM.Program.sampledRank target limit
        (WordRAM.Program.pure (some 0))
        (WordRAM.Program.pure (some word))).eval
      { wordSegments := #[] })

theorem wordRankTraceResult_refines_interpretedCosted
    (target : Bool) (word : List Bool) (limit : Nat) :
    (wordRankTraceResult target word limit).toCosted =
      wordRankInterpretedCosted target word limit := by
  rfl

theorem wordRankTraceResult_matchesReadStore
    (target : Bool) (word : List Bool) (limit : Nat)
    (store : WordRAM.ReadStore) :
    forall event,
      event ∈ (wordRankTraceResult target word limit).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp [wordRankTraceResult, WordRAM.Program.eval] at hmem ⊢
  subst event
  simp [WordRAM.TraceEvent.matchesReadStore]

theorem wordRankTraceResult_no_syntheticCostOnlyPrimitive
    (target : Bool) (word : List Bool) (limit : Nat) :
    forall event,
      event ∈ (wordRankTraceResult target word limit).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simpa [wordRankTraceResult, WordRAM.TraceResult.ofResult_trace] using
    WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
      (WordRAM.Program.sampledRank target limit
        (WordRAM.Program.pure (some 0))
        (WordRAM.Program.pure (some word)))
      { wordSegments := #[] } event hmem

theorem wordRankInterpretedCosted_refines_rankBoolWordPrefix
    (target : Bool) (word : List Bool) (limit : Nat) :
    wordRankInterpretedCosted target word limit =
      (RAM.rankBoolWordPrefix target word limit).toCosted := by
  apply Costed.ext
  · simp [wordRankInterpretedCosted, WordRAM.Program.eval,
      WordRAM.Result.toCosted, WordRAM.Result.steps,
      RAM.Exec.toCosted, RAM.Exec.steps]
  · have hrun := RAM.rankBoolWordPrefix_run target word limit
    have hcost :
        (RAM.rankBoolWordPrefix target word limit).toCosted.cost = 1 := by
      exact congrArg Prod.snd hrun
    simpa [wordRankInterpretedCosted, WordRAM.Program.eval,
      WordRAM.Result.toCosted, WordRAM.Result.steps,
      RAM.Exec.toCosted, RAM.Exec.steps] using hcost.symm

/--
Interpreted two-level sampled-rank query.

The super sample, block sample, and packed bit word are all read through the
Word-RAM read bridges.  The final in-word rank is represented by the existing
Word-RAM `sampledRank` primitive specialized to already-read words.
-/
def rankInterpretedCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind
    ((data.superTables.sampleProgram target (data.superIndex pos)).eval
      (data.superTables.sampleWordRAMStore target)).toCosted
    fun super? =>
      Costed.bind
        ((data.blockTables.sampleProgram target (data.wordIndex pos)).eval
          (data.blockTables.sampleWordRAMStore target)).toCosted
        fun delta? =>
          Costed.bind
            ((data.bitWords.store.readProgram (data.wordIndex pos)).eval
              data.bitWords.store.wordRAMStore).toCosted
            fun word? =>
              match super?, delta?, word? with
              | some super, some delta, some word =>
                  Costed.map
                    (fun localRank => super + delta + localRank)
                    (wordRankInterpretedCosted target word
                      (data.wordOffset pos))
              | _, _, _ => Costed.pure 0

theorem rankInterpretedCosted_refines_rankCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    data.rankInterpretedCosted target pos =
      data.rankCosted target pos := by
  unfold rankInterpretedCosted rankCosted
  rw [data.superTables.sampleProgram_refines_sampleCosted target
    (data.superIndex pos)]
  rw [data.blockTables.sampleProgram_refines_sampleCosted target
    (data.wordIndex pos)]
  rw [data.bitWords.store.readProgram_refines_readWordCosted
    (data.wordIndex pos)]
  cases hsuper :
      (data.superTables.sampleCosted target (data.superIndex pos)).value <;>
    cases hblock :
      (data.blockTables.sampleCosted target (data.wordIndex pos)).value <;>
    cases hword :
      (data.bitWords.store.readWordCosted (data.wordIndex pos)).value <;>
    simp [Costed.bind, Costed.map, Costed.pure, hsuper, hblock, hword,
      wordRankInterpretedCosted_refines_rankBoolWordPrefix]

theorem rankInterpretedCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankInterpretedCosted target pos).cost <= queryCost := by
  rw [data.rankInterpretedCosted_refines_rankCosted target pos]
  exact data.rankCosted_cost_le target pos

theorem rankInterpretedCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankInterpretedCosted target pos).erase =
      RMQ.Succinct.rankPrefix target bits pos := by
  rw [data.rankInterpretedCosted_refines_rankCosted target pos]
  exact data.rankCosted_exact target pos

/-- Payload words for the selected super-level rank samples. -/
def superSampleWords
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) : Array (List Bool) :=
  match target with
  | true => data.superTables.trueTable.store.words
  | false => data.superTables.falseTable.store.words

/-- Payload words for the selected block-level rank samples. -/
def blockSampleWords
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) : Array (List Bool) :=
  match target with
  | true => data.blockTables.trueTable.store.words
  | false => data.blockTables.falseTable.store.words

/--
Combined payload store for the register-interpreted two-level rank query.

Segment `0` is the selected super-sample table, segment `1` is the selected
block-sample table, and segment `2` is the packed bit-word store.
-/
def rankRegisterWordRAMStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) : RMQ.WordRAM.Store where
  wordSegments :=
    #[data.superSampleWords target, data.blockSampleWords target,
      data.bitWords.store.words]

/-- Register expression for the clamped two-level rank position. -/
def queryPosExpr
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (_data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : NatExpr) : NatExpr :=
  NatExpr.min pos (NatExpr.const bits.length)

/-- Register expression for the packed word index. -/
def wordIndexExpr
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : NatExpr) : NatExpr :=
  NatExpr.div (data.queryPosExpr pos) (NatExpr.const data.wordSize)

/-- Register expression for the super-block sample index. -/
def superIndexExpr
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : NatExpr) : NatExpr :=
  NatExpr.div (data.wordIndexExpr pos) (NatExpr.const data.blocksPerSuper)

/-- Register expression for the in-word rank offset. -/
def wordOffsetExpr
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : NatExpr) : NatExpr :=
  let q := data.queryPosExpr pos
  let wi := data.wordIndexExpr pos
  NatExpr.sub q (NatExpr.mul wi (NatExpr.const data.wordSize))

/-- First-order register program for the two-level stored-word rank query. -/
def rankRegisterProgram
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : NatExpr) : NatProgram :=
  NatProgram.twoLevelSampledRank target
    (data.wordOffsetExpr pos)
    0 (data.superIndexExpr pos)
    1 (data.wordIndexExpr pos)
    2 (data.wordIndexExpr pos)

theorem rankRegisterProgram_refines_rankInterpretedCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : NatExpr) (regs : RegFile) :
    ((data.rankRegisterProgram target pos).eval
        (data.rankRegisterWordRAMStore target) regs).toCosted =
      data.rankInterpretedCosted target (pos.eval regs) := by
  unfold rankRegisterProgram rankRegisterWordRAMStore rankInterpretedCosted
    wordOffsetExpr superIndexExpr wordIndexExpr queryPosExpr wordOffset
    superIndex wordIndex queryPos
  cases target
  · simp [NatProgram.eval, NatExpr.eval,
      SuccinctSpace.FixedWidthRankSampleTables.sampleProgram,
      SuccinctSpace.FixedWidthRankSampleTables.sampleWordRAMStore,
      SuccinctSpace.FixedWidthNatTable.readProgram,
      SuccinctSpace.PayloadWordStore.readProgram,
      blockSampleWords, superSampleWords, wordRankInterpretedCosted,
      RMQ.WordRAM.Program.eval]
    cases hsuper :
        data.superTables.falseTable.store.words[((pos.eval regs).min bits.length /
          data.wordSize / data.blocksPerSuper)]? <;>
      cases hblock :
        data.blockTables.falseTable.store.words[((pos.eval regs).min bits.length /
          data.wordSize)]? <;>
      cases hword :
        data.bitWords.store.words[((pos.eval regs).min bits.length /
          data.wordSize)]? <;>
      simp [RMQ.WordRAM.Store.readWord?, hsuper, hblock, hword,
        SuccinctSpace.FixedWidthNatTable.wordRAMStore,
        SuccinctSpace.PayloadWordStore.wordRAMStore,
        Costed.bind, Costed.map, Costed.pure, RMQ.WordRAM.Result.toCosted,
        RMQ.WordRAM.Result.steps]
  · simp [NatProgram.eval, NatExpr.eval,
      SuccinctSpace.FixedWidthRankSampleTables.sampleProgram,
      SuccinctSpace.FixedWidthRankSampleTables.sampleWordRAMStore,
      SuccinctSpace.FixedWidthNatTable.readProgram,
      SuccinctSpace.PayloadWordStore.readProgram,
      blockSampleWords, superSampleWords, wordRankInterpretedCosted,
      RMQ.WordRAM.Program.eval]
    cases hsuper :
        data.superTables.trueTable.store.words[((pos.eval regs).min bits.length /
          data.wordSize / data.blocksPerSuper)]? <;>
      cases hblock :
        data.blockTables.trueTable.store.words[((pos.eval regs).min bits.length /
          data.wordSize)]? <;>
      cases hword :
        data.bitWords.store.words[((pos.eval regs).min bits.length /
          data.wordSize)]? <;>
      simp [RMQ.WordRAM.Store.readWord?, hsuper, hblock, hword,
        SuccinctSpace.FixedWidthNatTable.wordRAMStore,
        SuccinctSpace.PayloadWordStore.wordRAMStore,
        Costed.bind, Costed.map, Costed.pure, RMQ.WordRAM.Result.toCosted,
        RMQ.WordRAM.Result.steps]

/-- Two-level rank query whose position is supplied through a natural register. -/
def rankRegisterInterpretedCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  ((data.rankRegisterProgram target (NatExpr.reg 0)).eval
      (data.rankRegisterWordRAMStore target)
      (RegFile.withNat1 pos)).toCosted

theorem rankRegisterInterpretedCosted_refines_rankInterpretedCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    data.rankRegisterInterpretedCosted target pos =
      data.rankInterpretedCosted target pos := by
  simpa [rankRegisterInterpretedCosted] using
    data.rankRegisterProgram_refines_rankInterpretedCosted target
      (NatExpr.reg 0) (RegFile.withNat1 pos)

/-- Trace-preserving register-backed two-level rank query. -/
def rankTraceResult
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.ofResult
    ((data.rankRegisterProgram target (NatExpr.reg 0)).eval
      (data.rankRegisterWordRAMStore target)
      (RegFile.withNat1 pos))

theorem rankTraceResult_refines_rankInterpretedCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankTraceResult target pos).toCosted =
      data.rankInterpretedCosted target pos := by
  simpa [rankTraceResult, rankRegisterInterpretedCosted] using
    data.rankRegisterInterpretedCosted_refines_rankInterpretedCosted
      target pos

theorem rankTraceResult_matchesReadStore
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    forall event,
      event ∈ (data.rankTraceResult target pos).trace ->
        event.matchesReadStore
          (WordRAM.ReadStore.ofStore
            (data.rankRegisterWordRAMStore target)) := by
  intro event hmem
  simpa [rankTraceResult, WordRAM.TraceResult.ofResult_trace,
    WordRAM.TraceEvent.matchesReadStore_ofStore] using
    WordRAM.Register.NatProgram.eval_reads_subset_payload
      (data.rankRegisterProgram target (NatExpr.reg 0))
      (data.rankRegisterWordRAMStore target)
      (RegFile.withNat1 pos) event hmem

theorem rankTraceResult_no_syntheticCostOnlyPrimitive
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    forall event,
      event ∈ (data.rankTraceResult target pos).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simpa [rankTraceResult, WordRAM.TraceResult.ofResult_trace] using
    WordRAM.Register.NatProgram.eval_no_syntheticCostOnlyPrimitive
      (data.rankRegisterProgram target (NatExpr.reg 0))
      (data.rankRegisterWordRAMStore target)
      (RegFile.withNat1 pos) event hmem

theorem rankRegisterInterpretedCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankRegisterInterpretedCosted target pos).cost <= queryCost := by
  rw [data.rankRegisterInterpretedCosted_refines_rankInterpretedCosted
    target pos]
  exact data.rankInterpretedCosted_cost_le target pos

theorem rankRegisterInterpretedCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankRegisterInterpretedCosted target pos).erase =
      RMQ.Succinct.rankPrefix target bits pos := by
  rw [data.rankRegisterInterpretedCosted_refines_rankInterpretedCosted
    target pos]
  exact data.rankInterpretedCosted_exact target pos

end TwoLevelPayloadLiveStoredWordRankData

end SuccinctRank

namespace GenericSelect

open SuccinctSpace SuccinctRank

/-- Segment bases for the four one-word tables of a sparse/dense entry table. -/
structure SparseDenseEntryTableTraceSegmentBases where
  baseOccurrence : Nat
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat
  deadSegment : Nat
deriving Repr

/-- Segment bases for the compact sparse-exception directory trace. -/
structure SparseExceptionDirectoryTraceSegmentBases where
  rankBase : Nat
  relativeBase : Nat
  deadSegment : Nat
deriving Repr

/-- Segment bases for a full sparse-exception select trace. -/
structure SparseExceptionSelectTraceSegmentLayout where
  superTable : SparseDenseEntryTableTraceSegmentBases
  localTable : SparseDenseEntryTableTraceSegmentBases
  longFlagRankBase : Nat
  longRelativeBase : Nat
  sparseDirectory : SparseExceptionDirectoryTraceSegmentBases
  bitWordBase : Nat
  deadSegment : Nat
deriving Repr

namespace FixedWidthSparseDenseSelectDenseLocalEntryTable

/-- Interpreted read of the four-field dense-local entry table. -/
def readInterpretedCosted
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    Costed (Option SparseDenseSelectDenseLocalEntry) :=
  Costed.bind
    ((table.baseOccurrenceTable.readProgram i).eval
      table.baseOccurrenceTable.wordRAMStore).toCosted
    fun baseOccurrence? =>
      Costed.bind
        ((table.baseWordIndexTable.readProgram i).eval
          table.baseWordIndexTable.wordRAMStore).toCosted
        fun baseWordIndex? =>
          Costed.bind
            ((table.rankBeforeTable.readProgram i).eval
              table.rankBeforeTable.wordRAMStore).toCosted
            fun rankBefore? =>
              Costed.map
                (fun firstOffset? =>
                  entryOfFields baseOccurrence? baseWordIndex?
                    rankBefore? firstOffset?)
                ((table.firstOffsetTable.readProgram i).eval
                  table.firstOffsetTable.wordRAMStore).toCosted

/-- Trace-preserving read of the four-field dense-local entry table. -/
def readTraceResult
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    WordRAM.TraceResult (Option SparseDenseSelectDenseLocalEntry) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.ofResult
      ((table.baseOccurrenceTable.readProgram i).eval
        table.baseOccurrenceTable.wordRAMStore))
    fun baseOccurrence? =>
      WordRAM.TraceResult.bind
        (WordRAM.TraceResult.ofResult
          ((table.baseWordIndexTable.readProgram i).eval
            table.baseWordIndexTable.wordRAMStore))
        fun baseWordIndex? =>
          WordRAM.TraceResult.bind
            (WordRAM.TraceResult.ofResult
              ((table.rankBeforeTable.readProgram i).eval
                table.rankBeforeTable.wordRAMStore))
            fun rankBefore? =>
              WordRAM.TraceResult.map
                (fun firstOffset? =>
                  entryOfFields baseOccurrence? baseWordIndex?
                    rankBefore? firstOffset?)
                (WordRAM.TraceResult.ofResult
                  ((table.firstOffsetTable.readProgram i).eval
                    table.firstOffsetTable.wordRAMStore))

/--
Trace-preserving read of the four-field entry table with each field table
shifted into a caller-supplied global segment range.
-/
def readTraceResultRelabeled
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    WordRAM.TraceResult (Option SparseDenseSelectDenseLocalEntry) :=
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

theorem readTraceResult_refines_interpretedCosted
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readTraceResult i).toCosted =
      table.readInterpretedCosted i := by
  rfl

theorem readTraceResultRelabeled_refines_interpretedCosted
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    (table.readTraceResultRelabeled layout i).toCosted =
      table.readInterpretedCosted i := by
  simp [readTraceResultRelabeled, readInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted, WordRAM.TraceResult.map_toCosted,
    WordRAM.TraceResult.ofResult_toCosted,
    WordRAM.TraceResult.relabelReadSegmentsWith_toCosted, Costed.bind,
    Costed.map]

theorem readTraceResultRelabeled_matchesReadStore
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
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
      event ∈ (table.readTraceResultRelabeled layout i).trace ->
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    forall event,
      event ∈ (table.readTraceResultRelabeled layout i).trace ->
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

theorem readInterpretedCosted_refines_readCosted
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    table.readInterpretedCosted i = table.readCosted i := by
  unfold readInterpretedCosted readCosted
  rw [table.baseOccurrenceTable.readProgram_refines_readCosted i]
  rw [table.baseWordIndexTable.readProgram_refines_readCosted i]
  rw [table.rankBeforeTable.readProgram_refines_readCosted i]
  rw [table.firstOffsetTable.readProgram_refines_readCosted i]
  rfl

theorem readInterpretedCosted_cost_le_four
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readInterpretedCosted i).cost <= 4 := by
  rw [table.readInterpretedCosted_refines_readCosted i]
  exact table.readCosted_cost_le_four i

theorem readInterpretedCosted_erase
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readInterpretedCosted i).erase = entries[i]? := by
  rw [table.readInterpretedCosted_refines_readCosted i]
  exact table.readCosted_erase i

end FixedWidthSparseDenseSelectDenseLocalEntryTable

/-- Interpreted relative-offset read over a fixed-width Nat payload table. -/
def relativeOffsetReadInterpretedCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : Costed (Option Nat) :=
  Costed.map (fun offset? => offset?.map (fun offset => base + offset))
    ((table.readProgram slot).eval table.wordRAMStore).toCosted

/-- Trace-preserving relative-offset read over a fixed-width Nat payload table. -/
def relativeOffsetReadTraceResult
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map
    (fun offset? => offset?.map (fun offset => base + offset))
    (WordRAM.TraceResult.ofResult
      ((table.readProgram slot).eval table.wordRAMStore))

/-- Trace-preserving relative-offset read with payload reads shifted. -/
def relativeOffsetReadTraceResultRelabeled
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

theorem relativeOffsetReadTraceResult_refines_interpretedCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    (relativeOffsetReadTraceResult table base slot).toCosted =
      relativeOffsetReadInterpretedCosted table base slot := by
  rfl

theorem relativeOffsetReadTraceResultRelabeled_refines_interpretedCosted
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    (relativeOffsetReadTraceResultRelabeled
      segmentBase deadSegment table base slot).toCosted =
      relativeOffsetReadInterpretedCosted table base slot := by
  simp [relativeOffsetReadTraceResultRelabeled,
    relativeOffsetReadInterpretedCosted,
    WordRAM.TraceResult.map_toCosted,
    WordRAM.TraceResult.ofResult_toCosted,
    WordRAM.TraceResult.relabelReadSegmentsWith_toCosted]

theorem relativeOffsetReadTraceResultRelabeled_matchesReadStore
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
      event ∈
          (relativeOffsetReadTraceResultRelabeled
            segmentBase deadSegment table base slot).trace ->
        event.matchesReadStore store := by
  unfold relativeOffsetReadTraceResultRelabeled
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

theorem relativeOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    forall event,
      event ∈
          (relativeOffsetReadTraceResultRelabeled
            segmentBase deadSegment table base slot).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold relativeOffsetReadTraceResultRelabeled
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

theorem relativeOffsetReadInterpretedCosted_refines
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    relativeOffsetReadInterpretedCosted table base slot =
      relativeOffsetReadCosted table base slot := by
  unfold relativeOffsetReadInterpretedCosted relativeOffsetReadCosted
  rw [table.readProgram_refines_readCosted slot]
  rfl

/-- Word-RAM-backed word-select primitive for a word already obtained by a read. -/
def wordSelectInterpretedCosted
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  ((WordRAM.Program.wordSelectFromOpt target occurrence
      (WordRAM.Program.pure (some word))).eval
    { wordSegments := #[] }).toCosted

/-- Trace-preserving version of `wordSelectInterpretedCosted`. -/
def wordSelectTraceResult
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.ofResult
    ((WordRAM.Program.wordSelectFromOpt target occurrence
        (WordRAM.Program.pure (some word))).eval
      { wordSegments := #[] })

theorem wordSelectTraceResult_refines_interpretedCosted
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    (wordSelectTraceResult target word occurrence).toCosted =
      wordSelectInterpretedCosted target word occurrence := by
  rfl

theorem wordSelectTraceResult_matchesReadStore
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (store : WordRAM.ReadStore) :
    forall event,
      event ∈ (wordSelectTraceResult target word occurrence).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp [wordSelectTraceResult, WordRAM.Program.eval] at hmem ⊢
  subst event
  simp [WordRAM.TraceEvent.matchesReadStore]

theorem wordSelectTraceResult_no_syntheticCostOnlyPrimitive
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    forall event,
      event ∈ (wordSelectTraceResult target word occurrence).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  simpa [wordSelectTraceResult, WordRAM.TraceResult.ofResult_trace] using
    WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
      (WordRAM.Program.wordSelectFromOpt target occurrence
        (WordRAM.Program.pure (some word)))
      { wordSegments := #[] } event hmem

theorem wordSelectInterpretedCosted_refines_selectBoolWord
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    wordSelectInterpretedCosted target word occurrence =
      (RAM.selectBoolWord target word occurrence).toCosted := by
  apply Costed.ext
  · simp [wordSelectInterpretedCosted, WordRAM.Program.eval,
      WordRAM.Result.toCosted, WordRAM.Result.steps,
      RAM.Exec.toCosted, RAM.Exec.steps]
  · have hrun := RAM.selectBoolWord_run target word occurrence
    have hcost :
        (RAM.selectBoolWord target word occurrence).toCosted.cost = 1 := by
      exact congrArg Prod.snd hrun
    simpa [wordSelectInterpretedCosted, WordRAM.Program.eval,
      WordRAM.Result.toCosted, WordRAM.Result.steps,
      RAM.Exec.toCosted, RAM.Exec.steps] using hcost.symm

/--
Interpreted dense two-word select branch.

The payload word reads are interpreted reads from the concrete bounded word
store, and the word-local rank/select operations are first-order Word-RAM
primitive events specialized to the already-read words.
-/
def denseTwoWordSelectInterpretedCosted
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind
    ((bitWords.store.readProgram firstWordIndex).eval
      bitWords.store.wordRAMStore).toCosted
    fun firstWord? =>
      match firstWord? with
      | none => Costed.pure none
      | some firstWord =>
          Costed.bind
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
              target firstWord firstOffset)
            fun beforeFirst =>
              Costed.bind
                (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                  target firstWord firstWord.length)
                fun uptoFirst =>
                  let firstCount := uptoFirst - beforeFirst
                  if localOccurrence < firstCount then
                    Costed.map
                      (fun local? =>
                        local?.map fun offset => firstWordStart + offset)
                      (wordSelectInterpretedCosted target firstWord
                        (beforeFirst + localOccurrence))
                  else
                    Costed.bind
                      ((bitWords.store.readProgram (firstWordIndex + 1)).eval
                        bitWords.store.wordRAMStore).toCosted
                      fun secondWord? =>
                        match secondWord? with
                        | none => Costed.pure none
                        | some secondWord =>
                            Costed.map
                              (fun local? =>
                                local?.map fun offset =>
                                  (firstWordIndex + 1) * wordSize + offset)
                              (wordSelectInterpretedCosted target secondWord
                                (localOccurrence - firstCount))

/-- Trace-preserving dense two-word select branch. -/
def denseTwoWordSelectTraceResult
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.ofResult
      ((bitWords.store.readProgram firstWordIndex).eval
        bitWords.store.wordRAMStore))
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
                          (firstWordIndex + 1)).eval
                          bitWords.store.wordRAMStore))
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

/--
Trace-preserving dense two-word select branch with packed BP-code word reads
shifted into a caller-supplied segment range.
-/
def denseTwoWordSelectTraceResultRelabeled
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
    (denseTwoWordSelectTraceResult
      target bitWords basePosition baseOccurrence q)

theorem denseTwoWordSelectTraceResult_refines_interpretedCosted
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordSelectTraceResult
      target bitWords basePosition baseOccurrence q).toCosted =
      denseTwoWordSelectInterpretedCosted
        target bitWords basePosition baseOccurrence q := by
  unfold denseTwoWordSelectTraceResult denseTwoWordSelectInterpretedCosted
  simp only [WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.ofResult_toCosted]
  cases hfirst : bitWords.store.words[basePosition / wordSize]? with
  | none =>
      simp [SuccinctSpace.PayloadWordStore.readProgram,
        SuccinctSpace.PayloadWordStore.wordRAMStore, WordRAM.Program.eval,
        WordRAM.Store.readWord?, hfirst, Costed.bind, Costed.pure]
  | some firstWord =>
      have hbefore :=
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_refines_interpretedCosted
          target firstWord (basePosition - basePosition / wordSize * wordSize)
      have hupto :=
        SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_refines_interpretedCosted
          target firstWord firstWord.length
      simp [SuccinctSpace.PayloadWordStore.readProgram,
        SuccinctSpace.PayloadWordStore.wordRAMStore, WordRAM.Program.eval,
        WordRAM.Store.readWord?, hfirst, Costed.bind, hbefore, hupto]
      by_cases hlt :
          q - baseOccurrence <
            (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
              target firstWord firstWord.length).value -
              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                target firstWord
                (basePosition - basePosition / wordSize * wordSize)).value
      · simp [hlt]
        have hsel :=
          wordSelectTraceResult_refines_interpretedCosted target firstWord
            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                target firstWord
                (basePosition - basePosition / wordSize * wordSize)).value +
              (q - baseOccurrence))
        constructor
        · have hvalue :
              (wordSelectTraceResult target firstWord
                ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                    target firstWord
                    (basePosition - basePosition / wordSize * wordSize)).value +
                  (q - baseOccurrence))).value =
                (wordSelectInterpretedCosted target firstWord
                  ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                    (q - baseOccurrence))).value := by
              simpa [WordRAM.TraceResult.toCosted] using
                congrArg Costed.value hsel
          simp [hvalue]
        · simpa [WordRAM.TraceResult.toCosted, WordRAM.TraceResult.steps] using
            congrArg Costed.cost hsel
      · cases hsecond :
            bitWords.store.words[basePosition / wordSize + 1]? with
        | none =>
            simp [hlt]
        | some secondWord =>
            simp [hlt]
            have hsel :=
              wordSelectTraceResult_refines_interpretedCosted target secondWord
                (q - baseOccurrence -
                  ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                    target firstWord firstWord.length).value -
                    (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value))
            constructor
            · have hvalue :
                  (wordSelectTraceResult target secondWord
                    (q - baseOccurrence -
                      ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                        target firstWord firstWord.length).value -
                        (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                          target firstWord
                          (basePosition - basePosition / wordSize * wordSize)).value))).value =
                    (wordSelectInterpretedCosted target secondWord
                      (q - baseOccurrence -
                        ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                          target firstWord firstWord.length).value -
                          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                            target firstWord
                            (basePosition - basePosition / wordSize * wordSize)).value))).value := by
                  simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hsel
              simp [hvalue]
            · have hcost :
                  (wordSelectTraceResult target secondWord
                    (q - baseOccurrence -
                      ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                        target firstWord firstWord.length).value -
                        (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                          target firstWord
                          (basePosition - basePosition / wordSize * wordSize)).value))).trace.length =
                    (wordSelectInterpretedCosted target secondWord
                      (q - baseOccurrence -
                        ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                          target firstWord firstWord.length).value -
                          (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted
                            target firstWord
                            (basePosition - basePosition / wordSize * wordSize)).value))).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using congrArg Costed.cost hsel
              rw [hcost, Nat.add_comm]

theorem denseTwoWordSelectTraceResultRelabeled_refines_interpretedCosted
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordSelectTraceResultRelabeled bitWordSegmentBase deadSegment
      target bitWords basePosition baseOccurrence q).toCosted =
      denseTwoWordSelectInterpretedCosted
        target bitWords basePosition baseOccurrence q := by
  simp [denseTwoWordSelectTraceResultRelabeled,
    denseTwoWordSelectTraceResult_refines_interpretedCosted]

theorem denseTwoWordSelectTraceResult_matchesReadStore
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResult
            target bitWords basePosition baseOccurrence q).trace ->
        event.matchesReadStore
          (WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore) := by
  unfold denseTwoWordSelectTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · intro event hmem
    simpa [WordRAM.TraceResult.ofResult_trace,
      WordRAM.TraceEvent.matchesReadStore_ofStore] using
      WordRAM.Program.eval_reads_subset_payload
        (bitWords.store.readProgram (basePosition / wordSize))
        bitWords.store.wordRAMStore event hmem
  · cases hfirst :
      (WordRAM.TraceResult.ofResult
        ((bitWords.store.readProgram (basePosition / wordSize)).eval
          bitWords.store.wordRAMStore)).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some firstWord =>
        apply WordRAM.TraceResult.bind_trace_forall
        · exact
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
              target firstWord
              (basePosition - basePosition / wordSize * wordSize)
              (WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore)
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_matchesReadStore
                target firstWord firstWord.length
                (WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore)
          · by_cases hlt :
                q - baseOccurrence <
                  (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                    target firstWord firstWord.length).value -
                    (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value
            · intro event hmem
              simp [hlt] at hmem
              exact
                (WordRAM.TraceResult.map_trace_forall
                  (fun event =>
                    event.matchesReadStore
                      (WordRAM.ReadStore.ofStore
                        bitWords.store.wordRAMStore))
                  (fun local? =>
                    local?.map fun offset =>
                      basePosition / wordSize * wordSize + offset)
                  (wordSelectTraceResult target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                      (q - baseOccurrence)))
                  (wordSelectTraceResult_matchesReadStore target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                      (q - baseOccurrence))
                    (WordRAM.ReadStore.ofStore
                      bitWords.store.wordRAMStore))) event hmem
            · intro event hmem
              simp [hlt] at hmem
              rcases hmem with hmem | hmem
              · subst event
                simp [WordRAM.TraceEvent.matchesReadStore,
                  WordRAM.ReadStore.ofStore,
                  SuccinctSpace.PayloadWordStore.wordRAMStore,
                  WordRAM.Store.readWord?]
              · cases hsecond :
                    bitWords.store.words[basePosition / wordSize + 1]? with
                | none =>
                    simp [hsecond] at hmem
                | some secondWord =>
                    simp [hsecond] at hmem
                    exact
                      (WordRAM.TraceResult.map_trace_forall
                        (fun event =>
                          event.matchesReadStore
                            (WordRAM.ReadStore.ofStore
                              bitWords.store.wordRAMStore))
                        (fun local? =>
                          local?.map fun offset =>
                            (basePosition / wordSize + 1) *
                                wordSize + offset)
                        (wordSelectTraceResult target secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)).value)))
                        (wordSelectTraceResult_matchesReadStore target
                          secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)).value))
                          (WordRAM.ReadStore.ofStore
                            bitWords.store.wordRAMStore))) event hmem

theorem denseTwoWordSelectTraceResult_no_syntheticCostOnlyPrimitive
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResult
            target bitWords basePosition baseOccurrence q).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold denseTwoWordSelectTraceResult
  apply WordRAM.TraceResult.bind_trace_forall
  · intro event hmem
    simpa [WordRAM.TraceResult.ofResult_trace] using
      WordRAM.Program.eval_no_syntheticCostOnlyPrimitive
        (bitWords.store.readProgram (basePosition / wordSize))
        bitWords.store.wordRAMStore event hmem
  · cases hfirst :
      (WordRAM.TraceResult.ofResult
        ((bitWords.store.readProgram (basePosition / wordSize)).eval
          bitWords.store.wordRAMStore)).value with
    | none =>
        exact WordRAM.TraceResult.pure_trace_forall _ none
    | some firstWord =>
        apply WordRAM.TraceResult.bind_trace_forall
        · exact
            SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_no_syntheticCostOnlyPrimitive
              target firstWord
              (basePosition - basePosition / wordSize * wordSize)
        · apply WordRAM.TraceResult.bind_trace_forall
          · exact
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult_no_syntheticCostOnlyPrimitive
                target firstWord firstWord.length
          · by_cases hlt :
                q - baseOccurrence <
                  (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                    target firstWord firstWord.length).value -
                    (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value
            · intro event hmem
              simp [hlt] at hmem
              exact
                (WordRAM.TraceResult.map_trace_forall
                  (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
                  (fun local? =>
                    local?.map fun offset =>
                      basePosition / wordSize * wordSize + offset)
                  (wordSelectTraceResult target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                      (q - baseOccurrence)))
                  (wordSelectTraceResult_no_syntheticCostOnlyPrimitive
                    target firstWord
                    ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                      target firstWord
                      (basePosition - basePosition / wordSize * wordSize)).value +
                      (q - baseOccurrence)))) event hmem
            · intro event hmem
              simp [hlt] at hmem
              rcases hmem with hmem | hmem
              · subst event
                simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
              · cases hsecond :
                    bitWords.store.words[basePosition / wordSize + 1]? with
                | none =>
                    simp [hsecond] at hmem
                | some secondWord =>
                    simp [hsecond] at hmem
                    exact
                      (WordRAM.TraceResult.map_trace_forall
                        (fun event => ¬ event.isSyntheticCostOnlyPrimitive)
                        (fun local? =>
                          local?.map fun offset =>
                            (basePosition / wordSize + 1) *
                                wordSize + offset)
                        (wordSelectTraceResult target secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)).value)))
                        (wordSelectTraceResult_no_syntheticCostOnlyPrimitive
                          target secondWord
                          (q - baseOccurrence -
                            ((SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                              target firstWord firstWord.length).value -
                              (SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankTraceResult
                                target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)).value)))) event hmem

theorem denseTwoWordSelectTraceResultRelabeled_matchesReadStore
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (store : WordRAM.ReadStore)
    (hread :
      forall segment index,
        store.readWord?
            (WordRAM.singletonSegmentMap
              bitWordSegmentBase deadSegment segment) index =
          bitWords.store.wordRAMStore.readWord? segment index)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResultRelabeled
            bitWordSegmentBase deadSegment target bitWords
            basePosition baseOccurrence q).trace ->
        event.matchesReadStore store := by
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
      (denseTwoWordSelectTraceResult
        target bitWords basePosition baseOccurrence q)
      (WordRAM.ReadStore.ofStore bitWords.store.wordRAMStore)
      store
      (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
      hread
      (denseTwoWordSelectTraceResult_matchesReadStore
        target bitWords basePosition baseOccurrence q)

theorem denseTwoWordSelectTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    forall event,
      event ∈
          (denseTwoWordSelectTraceResultRelabeled
            bitWordSegmentBase deadSegment target bitWords
            basePosition baseOccurrence q).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold denseTwoWordSelectTraceResultRelabeled
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (WordRAM.singletonSegmentMap bitWordSegmentBase deadSegment)
      (denseTwoWordSelectTraceResult
        target bitWords basePosition baseOccurrence q)
      (denseTwoWordSelectTraceResult_no_syntheticCostOnlyPrimitive
        target bitWords basePosition baseOccurrence q)

theorem denseTwoWordSelectInterpretedCosted_refines
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    denseTwoWordSelectInterpretedCosted
        target bitWords basePosition baseOccurrence q =
      denseTwoWordSelectCosted
        target bitWords basePosition baseOccurrence q := by
  apply Costed.ext
  · unfold denseTwoWordSelectInterpretedCosted denseTwoWordSelectCosted
    simp [Costed.bind, Costed.map, Costed.pure,
      SuccinctSpace.PayloadWordStore.readProgram_refines_readWordCosted,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted_refines_rankBoolWordPrefix,
      wordSelectInterpretedCosted_refines_selectBoolWord]
    rfl
  · unfold denseTwoWordSelectInterpretedCosted denseTwoWordSelectCosted
    simp [Costed.bind, Costed.map, Costed.pure,
      SuccinctSpace.PayloadWordStore.readProgram_refines_readWordCosted,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordRankInterpretedCosted_refines_rankBoolWordPrefix,
      wordSelectInterpretedCosted_refines_selectBoolWord]
    rfl

theorem denseTwoWordSelectInterpretedCosted_cost_le_five
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordSelectInterpretedCosted
      target bitWords basePosition baseOccurrence q).cost <= 5 := by
  rw [denseTwoWordSelectInterpretedCosted_refines
    target bitWords basePosition baseOccurrence q]
  exact denseTwoWordSelectCosted_cost_le_five
    target bitWords basePosition baseOccurrence q

namespace SparseExceptionDirectory

/-- Interpreted read for the sparse-exception compact directory. -/
def readInterpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    (directory.rankData.rankInterpretedCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadInterpretedCosted directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

/-- Trace-preserving read for the sparse-exception compact directory. -/
def readTraceResult
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (directory.rankData.rankTraceResult true localSlot)
    fun exceptionRank =>
      relativeOffsetReadTraceResult directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

/-- Trace-preserving sparse-exception directory read with shifted rank/table reads. -/
def readTraceResultRelabeled
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.bind
    (WordRAM.TraceResult.relabelReadSegmentsWith
      (WordRAM.tripleSegmentMap layout.rankBase layout.deadSegment)
      (directory.rankData.rankTraceResult true localSlot))
    fun exceptionRank =>
      relativeOffsetReadTraceResultRelabeled layout.relativeBase
        layout.deadSegment
        directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readTraceResult_refines_interpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readTraceResult base localSlot localOccurrence).toCosted =
      directory.readInterpretedCosted base localSlot localOccurrence := by
  simp [readTraceResult, readInterpretedCosted,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult_refines_rankInterpretedCosted,
    relativeOffsetReadTraceResult_refines_interpretedCosted]

theorem readTraceResultRelabeled_refines_interpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    (directory.readTraceResultRelabeled
      layout base localSlot localOccurrence).toCosted =
      directory.readInterpretedCosted base localSlot localOccurrence := by
  simp [readTraceResultRelabeled, readInterpretedCosted,
    WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResult_refines_rankInterpretedCosted,
    relativeOffsetReadTraceResultRelabeled_refines_interpretedCosted]

theorem readTraceResultRelabeled_matchesReadStore
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
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
      event ∈
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
      relativeOffsetReadTraceResultRelabeled_matchesReadStore
        layout.relativeBase layout.deadSegment
        directory.relativeTable store hrelative base
        (relativeSplitSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)

theorem readTraceResultRelabeled_no_syntheticCostOnlyPrimitive
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    forall event,
      event ∈
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
      relativeOffsetReadTraceResultRelabeled_no_syntheticCostOnlyPrimitive
        layout.relativeBase layout.deadSegment
        directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          (directory.rankData.rankTraceResult true localSlot).value
          localOccurrence directory.localStride)

theorem readInterpretedCosted_refines_readCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    directory.readInterpretedCosted base localSlot localOccurrence =
      directory.readCosted base localSlot localOccurrence := by
  apply Costed.ext <;>
    unfold readInterpretedCosted readCosted <;>
    simp [Costed.bind,
      directory.rankData.rankInterpretedCosted_refines_rankCosted true
        localSlot,
      relativeOffsetReadInterpretedCosted_refines]

theorem readInterpretedCosted_cost_le_five
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readInterpretedCosted
      base localSlot localOccurrence).cost <= 5 := by
  rw [directory.readInterpretedCosted_refines_readCosted
    base localSlot localOccurrence]
  exact directory.readCosted_cost_le_five base localSlot localOccurrence

theorem readInterpretedCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readInterpretedCosted base localSlot localOccurrence).erase =
      (directory.relativeEntries[
          relativeSplitSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
            localOccurrence directory.localStride]?).map
        (fun offset => base + offset) := by
  rw [directory.readInterpretedCosted_refines_readCosted
    base localSlot localOccurrence]
  exact directory.readCosted_exact base localSlot localOccurrence

end SparseExceptionDirectory

namespace SparseExceptionSelectData

/-- Interpreted sparse-exception select query over the concrete data record. -/
def selectInterpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    Costed.bind
      (data.superTable.readInterpretedCosted
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankInterpretedCosted true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadInterpretedCosted data.longSuperRelativeTable
                  (relativeSplitSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind
              (data.localTable.readInterpretedCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readInterpretedCosted
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectInterpretedCosted target data.bitWords
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    Costed.pure none

/-- Trace-preserving sparse-exception select query over the concrete data record. -/
def selectTraceResult
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResult
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (data.longFlagRankData.rankTraceResult true
                (selectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadTraceResult data.longSuperRelativeTable
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
              (data.localTable.readTraceResult localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResult
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectTraceResult target data.bitWords
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

/--
Trace-preserving sparse-exception select query with payload reads shifted into a
caller-supplied global segment layout.
-/
def selectTraceResultRelabeled
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < occurrenceCount bits target then
    WordRAM.TraceResult.bind
      (data.superTable.readTraceResultRelabeled
        layout.superTable
        (selectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => WordRAM.TraceResult.pure none
      | some super =>
          if relativeSplitSelectEntryIsMarked super then
            WordRAM.TraceResult.bind
              (WordRAM.TraceResult.relabelReadSegmentsWith
                (WordRAM.tripleSegmentMap
                  layout.longFlagRankBase layout.deadSegment)
                (data.longFlagRankData.rankTraceResult true
                  (selectSuperSlot q data.superStride)))
              fun exceptionRank =>
                relativeOffsetReadTraceResultRelabeled
                  layout.longRelativeBase layout.deadSegment
                  data.longSuperRelativeTable
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
              (data.localTable.readTraceResultRelabeled
                layout.localTable localSlot) fun loc? =>
              match loc? with
              | none => WordRAM.TraceResult.pure none
              | some loc =>
                  if relativeSplitSelectEntryIsMarked loc then
                    data.sparseDirectory.readTraceResultRelabeled
                      layout.sparseDirectory
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordSelectTraceResultRelabeled
                      layout.bitWordBase layout.deadSegment
                      target data.bitWords
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc) q
  else
    WordRAM.TraceResult.pure none

theorem selectTraceResultRelabeled_trace_forall
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hsuper :
      forall slot event,
        event ∈
          (data.superTable.readTraceResultRelabeled
            layout.superTable slot).trace ->
          P event)
    (hlongRank :
      forall slot event,
        event ∈
          (WordRAM.TraceResult.relabelReadSegmentsWith
            (WordRAM.tripleSegmentMap
              layout.longFlagRankBase layout.deadSegment)
            (data.longFlagRankData.rankTraceResult true slot)).trace ->
          P event)
    (hlongRelative :
      forall base slot event,
        event ∈
          (relativeOffsetReadTraceResultRelabeled
            layout.longRelativeBase layout.deadSegment
            data.longSuperRelativeTable base slot).trace ->
          P event)
    (hlocal :
      forall slot event,
        event ∈
          (data.localTable.readTraceResultRelabeled
            layout.localTable slot).trace ->
          P event)
    (hsparse :
      forall base localSlot localOccurrence event,
        event ∈
          (data.sparseDirectory.readTraceResultRelabeled
            layout.sparseDirectory base localSlot localOccurrence).trace ->
          P event)
    (hdense :
      forall basePosition baseOccurrence q event,
        event ∈
          (denseTwoWordSelectTraceResultRelabeled
            layout.bitWordBase layout.deadSegment
            target data.bitWords basePosition baseOccurrence q).trace ->
          P event) :
    forall event,
      event ∈ (data.selectTraceResultRelabeled layout idx).trace ->
        P event := by
  unfold selectTraceResultRelabeled
  by_cases hvalid : idx < occurrenceCount bits target
  · intro event hmem
    simp [hvalid, WordRAM.TraceResult.bind] at hmem
    rcases hmem with hmem | hmem
    · exact hsuper
        (selectSuperSlot (data.queryOccurrence idx) data.superStride)
        event hmem
    · cases hsuperValue :
        (data.superTable.readTraceResultRelabeled layout.superTable
          (selectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
      | none =>
          simp [hsuperValue] at hmem
      | some super =>
          by_cases hlong :
              relativeSplitSelectEntryIsMarked super = true
          · simp [hsuperValue, hlong] at hmem
            rcases hmem with hmem | hmem
            · have hmemRelabeled :
                  event ∈
                    (WordRAM.TraceResult.relabelReadSegmentsWith
                      (WordRAM.tripleSegmentMap
                        layout.longFlagRankBase layout.deadSegment)
                      (data.longFlagRankData.rankTraceResult true
                        (selectSuperSlot (data.queryOccurrence idx)
                          data.superStride))).trace := by
                simpa [WordRAM.TraceResult.relabelReadSegmentsWith] using
                  (List.mem_map.mpr hmem)
              exact hlongRank
                (selectSuperSlot (data.queryOccurrence idx)
                  data.superStride)
                event hmemRelabeled
            · exact hlongRelative
                (relativeSplitSelectEntryBasePosition
                  data.wordSize super)
                (relativeSplitSelectLongCompactSlot
                  (data.longFlagRankData.rankTraceResult true
                    (selectSuperSlot (data.queryOccurrence idx)
                      data.superStride)).value
                  (data.queryOccurrence idx - super.baseOccurrence)
                  data.superStride)
                event hmem
          · simp [hsuperValue, hlong] at hmem
            let localSlot :=
              relativeSplitSelectLocalSlot (data.queryOccurrence idx)
                data.superStride data.localSlotsPerSuper
                data.localStride super
            rcases hmem with hmem | hmem
            · exact hlocal localSlot event hmem
            · cases hlocalValue :
                (data.localTable.readTraceResultRelabeled
                  layout.localTable localSlot).value with
              | none =>
                  simp [hlocalValue, localSlot] at hmem
              | some loc =>
                  by_cases hsparseBranch :
                      relativeSplitSelectEntryIsMarked loc = true
                  · exact hsparse
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (data.queryOccurrence idx -
                        relativeSplitSelectLocalBaseOccurrence
                          super loc)
                      event
                      (by
                        simpa [hlocalValue, hsparseBranch, localSlot] using
                          hmem)
                  · exact hdense
                      (relativeSplitSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitSelectLocalBaseOccurrence
                        super loc)
                      (data.queryOccurrence idx)
                      event
                      (by
                        simpa [hlocalValue, hsparseBranch, localSlot] using
                          hmem)
  · intro event hmem
    simp [hvalid] at hmem

set_option linter.unusedSimpArgs false in
theorem selectTraceResultRelabeled_refines_interpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat) :
    (data.selectTraceResultRelabeled layout idx).toCosted =
      data.selectInterpretedCosted idx := by
  unfold selectTraceResultRelabeled selectInterpretedCosted
  by_cases hvalid : idx < occurrenceCount bits target
  · simp [hvalid, WordRAM.TraceResult.bind_toCosted,
      data.superTable.readTraceResultRelabeled_refines_interpretedCosted
        layout.superTable
        (selectSuperSlot (data.queryOccurrence idx) data.superStride)]
    cases hsuper :
        (data.superTable.readInterpretedCosted
          (selectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            relativeSplitSelectEntryIsMarked super = true
        · simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            WordRAM.TraceResult.relabelReadSegmentsWith_toCosted,
            data.longFlagRankData.rankTraceResult_refines_rankInterpretedCosted,
            relativeOffsetReadTraceResultRelabeled_refines_interpretedCosted]
        · let localSlot :=
            relativeSplitSelectLocalSlot (data.queryOccurrence idx)
              data.superStride data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            localSlot,
            data.localTable.readTraceResultRelabeled_refines_interpretedCosted
              layout.localTable localSlot]
          cases hlocal :
              (data.localTable.readInterpretedCosted localSlot).value with
          | none =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  layout.localTable localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).value = none := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              simp [Costed.pure]
          | some loc =>
              have hlocalTrace :=
                data.localTable.readTraceResultRelabeled_refines_interpretedCosted
                  layout.localTable localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).value =
                    some loc := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResultRelabeled
                    layout.localTable localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  data.sparseDirectory.readTraceResultRelabeled_refines_interpretedCosted
                    layout.sparseDirectory
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalSlot (data.queryOccurrence idx)
                      data.superStride data.localSlotsPerSuper
                      data.localStride super)
                    (data.queryOccurrence idx -
                      relativeSplitSelectLocalBaseOccurrence super loc)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hchild
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hdense :=
                  denseTwoWordSelectTraceResultRelabeled_refines_interpretedCosted
                    layout.bitWordBase layout.deadSegment target data.bitWords
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalBaseOccurrence super loc)
                    (data.queryOccurrence idx)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hdense
                · simpa [WordRAM.TraceResult.toCosted,
                    WordRAM.TraceResult.steps] using
                    congrArg Costed.cost hdense
  · simp [hvalid, Costed.pure]

set_option linter.unusedSimpArgs false in
theorem selectTraceResult_refines_interpretedCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    (data.selectTraceResult idx).toCosted =
      data.selectInterpretedCosted idx := by
  unfold selectTraceResult selectInterpretedCosted
  by_cases hvalid : idx < occurrenceCount bits target
  · simp [hvalid, WordRAM.TraceResult.bind_toCosted,
      data.superTable.readTraceResult_refines_interpretedCosted
        (selectSuperSlot (data.queryOccurrence idx) data.superStride)]
    cases hsuper :
        (data.superTable.readInterpretedCosted
          (selectSuperSlot (data.queryOccurrence idx)
            data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            relativeSplitSelectEntryIsMarked super = true
        · simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            data.longFlagRankData.rankTraceResult_refines_rankInterpretedCosted,
            relativeOffsetReadTraceResult_refines_interpretedCosted]
        · let localSlot :=
            relativeSplitSelectLocalSlot (data.queryOccurrence idx)
              data.superStride data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong,
            WordRAM.TraceResult.bind_toCosted,
            localSlot,
            data.localTable.readTraceResult_refines_interpretedCosted
              localSlot]
          cases hlocal :
              (data.localTable.readInterpretedCosted localSlot).value with
          | none =>
              have hlocalTrace :=
                data.localTable.readTraceResult_refines_interpretedCosted
                  localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResult localSlot).value = none := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResult localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              simp [Costed.pure]
          | some loc =>
              have hlocalTrace :=
                data.localTable.readTraceResult_refines_interpretedCosted
                  localSlot
              have hlocalTraceValue :
                  (data.localTable.readTraceResult localSlot).value =
                    some loc := by
                have hv := congrArg Costed.value hlocalTrace
                simpa [WordRAM.TraceResult.toCosted, hlocal] using hv
              have hlocalTraceCost :
                  (data.localTable.readTraceResult localSlot).trace.length =
                    (data.localTable.readInterpretedCosted localSlot).cost := by
                simpa [WordRAM.TraceResult.toCosted,
                  WordRAM.TraceResult.steps] using
                  congrArg Costed.cost hlocalTrace
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  data.sparseDirectory.readTraceResult_refines_interpretedCosted
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalSlot (data.queryOccurrence idx)
                      data.superStride data.localSlotsPerSuper
                      data.localStride super)
                    (data.queryOccurrence idx -
                      relativeSplitSelectLocalBaseOccurrence super loc)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · have hchildCost :
                      (data.sparseDirectory.readTraceResult
                        (relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        (relativeSplitSelectLocalSlot
                          (data.queryOccurrence idx) data.superStride
                          data.localSlotsPerSuper data.localStride super)
                        (data.queryOccurrence idx -
                          relativeSplitSelectLocalBaseOccurrence
                            super loc)).trace.length =
                        (data.sparseDirectory.readInterpretedCosted
                          (relativeSplitSelectLocalBasePosition
                            data.wordSize super loc)
                          (relativeSplitSelectLocalSlot
                            (data.queryOccurrence idx) data.superStride
                            data.localSlotsPerSuper data.localStride super)
                          (data.queryOccurrence idx -
                            relativeSplitSelectLocalBaseOccurrence
                              super loc)).cost := by
                    simpa [WordRAM.TraceResult.toCosted,
                      WordRAM.TraceResult.steps] using
                      congrArg Costed.cost hchild
                  rw [hchildCost]
              · simp [Costed.bind, hlocal, hsparse, localSlot,
                  hlocalTraceValue, hlocalTraceCost]
                have hchild :=
                  denseTwoWordSelectTraceResult_refines_interpretedCosted
                    target data.bitWords
                    (relativeSplitSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitSelectLocalBaseOccurrence super loc)
                    (data.queryOccurrence idx)
                constructor
                · simpa [WordRAM.TraceResult.toCosted] using
                    congrArg Costed.value hchild
                · have hchildCost :
                      (denseTwoWordSelectTraceResult target data.bitWords
                        (relativeSplitSelectLocalBasePosition
                          data.wordSize super loc)
                        (relativeSplitSelectLocalBaseOccurrence super loc)
                        (data.queryOccurrence idx)).trace.length =
                        (denseTwoWordSelectInterpretedCosted target
                          data.bitWords
                          (relativeSplitSelectLocalBasePosition
                            data.wordSize super loc)
                          (relativeSplitSelectLocalBaseOccurrence super loc)
                          (data.queryOccurrence idx)).cost := by
                    simpa [WordRAM.TraceResult.toCosted,
                      WordRAM.TraceResult.steps] using
                      congrArg Costed.cost hchild
                  rw [hchildCost]
  · simp [hvalid, WordRAM.TraceResult.pure_toCosted, Costed.pure]

theorem selectInterpretedCosted_refines_selectCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    data.selectInterpretedCosted idx = data.selectCosted idx := by
  unfold selectInterpretedCosted selectCosted queryOccurrence
  by_cases hvalid : idx < occurrenceCount bits target
  · simp [hvalid]
    rw [data.superTable.readInterpretedCosted_refines_readCosted
      (selectSuperSlot idx data.superStride)]
    cases hsuper :
        (data.superTable.readCosted
          (selectSuperSlot idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hsuper]
    | some super =>
        by_cases hlong :
            relativeSplitSelectEntryIsMarked super = true
        · rw [data.longFlagRankData.rankInterpretedCosted_refines_rankCosted
            true (selectSuperSlot idx data.superStride)]
          simp [Costed.bind, hsuper, hlong]
          rw [relativeOffsetReadInterpretedCosted_refines]
          exact ⟨rfl, rfl⟩
        · let localSlot :=
            relativeSplitSelectLocalSlot idx data.superStride
              data.localSlotsPerSuper data.localStride super
          simp [Costed.bind, hsuper, hlong]
          rw [data.localTable.readInterpretedCosted_refines_readCosted
            localSlot]
          cases hlocal :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp
          | some loc =>
              by_cases hsparse :
                  relativeSplitSelectEntryIsMarked loc = true
              · simp [hsparse]
                rw [data.sparseDirectory.readInterpretedCosted_refines_readCosted]
                exact ⟨rfl, rfl⟩
              · simp [hsparse]
                rw [denseTwoWordSelectInterpretedCosted_refines]
                exact ⟨rfl, rfl⟩
  · simp [hvalid, Costed.pure]

theorem selectInterpretedCosted_cost_le
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectInterpretedCosted idx).cost <=
      sparseDenseSelectQueryCost := by
  rw [data.selectInterpretedCosted_refines_selectCosted idx]
  exact data.selectCosted_cost_le idx

theorem selectInterpretedCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectInterpretedCosted idx).erase =
      RMQ.Succinct.select target bits idx := by
  rw [data.selectInterpretedCosted_refines_selectCosted idx]
  exact data.selectCosted_exact idx

theorem interpreted_profile
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      SparseExceptionSelectData
        bits target rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectInterpretedCosted idx).cost <=
          sparseDenseSelectQueryCost) /\
      (forall idx,
        (data.selectInterpretedCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  exact
    ⟨data.payload_length_le_canonical,
      canonicalSparseExceptionSelectOverhead_littleO,
      data.selectInterpretedCosted_cost_le,
      data.selectInterpretedCosted_exact,
      fun {word} hmem => data.read_word_length_le_machine hmem⟩

end SparseExceptionSelectData

/--
Built sparse-exception source profile with the select leg routed through the
interpreted concrete data query.
-/
theorem sparseExceptionSelectSource_interpreted_profile
    (bits : List Bool) (target : Bool) :
    let data := sparseExceptionSelectData bits target
    let source := sparseExceptionSelectSource bits target
    data.payload.length <=
        canonicalSparseExceptionSelectOverhead source.domainSize /\
      SuccinctSpace.LittleOLinear canonicalSparseExceptionSelectOverhead /\
      (forall idx,
        (data.selectInterpretedCosted idx).cost <=
          sparseDenseSelectQueryCost) /\
      (forall idx,
        (data.selectInterpretedCosted idx).erase =
          RMQ.Succinct.select target bits idx) /\
      (forall idx,
        data.selectInterpretedCosted idx =
          source.selectPositionCosted idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  intro data source
  refine
    ⟨?_, canonicalSparseExceptionSelectOverhead_littleO,
      data.selectInterpretedCosted_cost_le,
      data.selectInterpretedCosted_exact,
      ?_, fun {word} hmem => data.read_word_length_le_machine hmem⟩
  · simpa [source, sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using
      data.payload_length_le_canonical
  · intro idx
    simpa [source, sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using
      data.selectInterpretedCosted_refines_selectCosted idx

end GenericSelect

end RMQ

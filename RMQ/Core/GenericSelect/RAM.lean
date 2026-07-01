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

theorem relativeOffsetReadTraceResult_refines_interpretedCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    (relativeOffsetReadTraceResult table base slot).toCosted =
      relativeOffsetReadInterpretedCosted table base slot := by
  rfl

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

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

/-- Word-RAM-backed word-rank primitive for a word already obtained by a read. -/
def wordRankInterpretedCosted
    (target : Bool) (word : List Bool) (limit : Nat) : Costed Nat :=
  ((WordRAM.Program.sampledRank target limit
      (WordRAM.Program.pure (some 0))
      (WordRAM.Program.pure (some word))).eval
    { wordSegments := #[] }).toCosted

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

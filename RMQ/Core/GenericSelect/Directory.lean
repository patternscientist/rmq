import RMQ.Core.GenericSelect.FlagRank
import RMQ.Core.GenericSelect.RelativeTables

/-!
# Generic select sparse-exception directory layer

This module contains the payload-live sparse-exception directory structure,
charged read path, concrete builder, and directory-level exactness/profile
lemmas.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

structure SparseExceptionDirectory
    (bits : List Bool) (target : Bool)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  localStride : Nat
  localStride_pos : 0 < localStride
  flagBits : List Bool
  rankData :
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      flagBits rankSuperOverhead rankBlockOverhead 4
  relativeEntries : List Nat
  relativeWidth : Nat
  relativeTable :
    SuccinctSpace.FixedWidthNatTable relativeEntries relativeWidth
  rank_wordSize_le_machine :
    rankData.wordSize <=
      SuccinctRank.machineWordBits bits.length
  rank_superWidth_le_machine :
    rankData.superWidth <=
      SuccinctRank.machineWordBits bits.length
  rank_blockWidth_le_machine :
    rankData.blockWidth <=
      SuccinctRank.machineWordBits bits.length
  relativeWidth_le_machine :
    relativeWidth <=
      SuccinctRank.machineWordBits bits.length
  payload_length_le_overhead :
    flagBits.length + rankData.auxPayload.length +
        relativeTable.payload.length <=
      canonicalSparseExceptionDirectoryOverhead bits.length

namespace SparseExceptionDirectory

def payload
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  directory.flagBits ++ directory.rankData.auxPayload ++
    directory.relativeTable.payload

theorem payload_length_le_canonical
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
      canonicalSparseExceptionDirectoryOverhead bits.length := by
  simpa [payload, Nat.add_assoc] using
    directory.payload_length_le_overhead

def readWords
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  directory.rankData.superTables.trueTable.store.words.toList ++
    directory.rankData.superTables.falseTable.store.words.toList ++
      directory.rankData.blockTables.trueTable.store.words.toList ++
        directory.rankData.blockTables.falseTable.store.words.toList ++
          directory.rankData.bitWords.store.words.toList ++
            directory.relativeTable.store.words.toList

def readCosted
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.rankData.rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted directory.relativeTable base
        (relativeSplitSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readCosted_cost_le_five
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).cost <= 5 := by
  unfold readCosted relativeOffsetReadCosted
  have hrank :=
    directory.rankData.rankCosted_cost_le_four true localSlot
  have hrelative :=
    directory.relativeTable.readCosted_cost_le_one
      (relativeSplitSelectSparseCompactSlot
        (directory.rankData.rankCosted true localSlot).value
        localOccurrence directory.localStride)
  simp [Costed.bind] at *
  omega

theorem readCosted_exact
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).erase =
      (directory.relativeEntries[
          relativeSplitSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
            localOccurrence directory.localStride]?).map
        (fun offset => base + offset) := by
  have hrank :=
    directory.rankData.rankCosted_exact true localSlot
  change (directory.rankData.rankCosted true localSlot).value =
      RMQ.Succinct.rankPrefix true directory.flagBits localSlot at hrank
  let slot :=
    relativeSplitSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
      localOccurrence directory.localStride
  have hread :
      (directory.relativeTable.readCosted slot).value =
        directory.relativeEntries[slot]? := by
    simpa [Costed.erase] using
      directory.relativeTable.readCosted_erase slot
  unfold readCosted relativeOffsetReadCosted
  simp [Costed.bind, Costed.erase, hrank, slot, hread]

theorem read_words_length_le_machine
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word directory.readWords) :
    word.length <=
      SuccinctRank.machineWordBits bits.length := by
  rw [readWords] at hmem
  rcases List.mem_append.mp hmem with hprefix0 | hrelative
  · rcases List.mem_append.mp hprefix0 with hprefix1 | hflagWord
    · rcases List.mem_append.mp hprefix1 with hprefix2 | hblockFalse
      · rcases List.mem_append.mp hprefix2 with hprefix3 | hblockTrue
        · rcases List.mem_append.mp hprefix3 with hsuperTrue | hsuperFalse
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.trueTable
                directory.rank_superWidth_le_machine hsuperTrue
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.falseTable
                directory.rank_superWidth_le_machine hsuperFalse
        · exact
            fixedWidthNatTable_word_length_le_of_mem
              directory.rankData.blockTables.trueTable
              directory.rank_blockWidth_le_machine hblockTrue
      · exact
          fixedWidthNatTable_word_length_le_of_mem
            directory.rankData.blockTables.falseTable
            directory.rank_blockWidth_le_machine hblockFalse
    · exact Nat.le_trans
        (directory.rankData.bitWords.word_length_le hflagWord)
        directory.rank_wordSize_le_machine
  · exact
      fixedWidthNatTable_word_length_le_of_mem
        directory.relativeTable
        directory.relativeWidth_le_machine hrelative

theorem profile
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      SparseExceptionDirectory
        bits target rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
        canonicalSparseExceptionDirectoryOverhead bits.length /\
      (forall base localSlot localOccurrence,
        (directory.readCosted
          base localSlot localOccurrence).cost <= 5) /\
      (forall base localSlot localOccurrence,
        (directory.readCosted base localSlot localOccurrence).erase =
          (directory.relativeEntries[
              relativeSplitSelectSparseCompactSlot
                (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
                localOccurrence directory.localStride]?).map
            (fun offset => base + offset)) /\
      forall {word : List Bool},
        List.Mem word directory.readWords ->
          word.length <=
            SuccinctRank.machineWordBits bits.length := by
  exact
    ⟨directory.payload_length_le_canonical,
      directory.readCosted_cost_le_five,
      directory.readCosted_exact,
      fun {word} hmem => directory.read_words_length_le_machine hmem⟩

end SparseExceptionDirectory

def sparseExceptionDirectory
    (bits : List Bool) (target : Bool) :
    SparseExceptionDirectory
      bits target
      (sparseExceptionEffectiveFlagRankSuperOverhead bits target)
      (sparseExceptionEffectiveFlagRankBlockOverhead bits target) where
  localStride := localStride bits.length
  localStride_pos := localStride_pos bits.length
  flagBits := sparseExceptionEffectiveFlagBits bits target
  rankData := sparseExceptionEffectiveFlagRankData bits target
  relativeEntries := sparseExceptionRelativeEntries bits target
  relativeWidth := sparseExceptionRelativeWidth bits
  relativeTable := sparseExceptionRelativeTable bits target
  rank_wordSize_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.1
  rank_superWidth_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.2.1
  rank_blockWidth_le_machine := by
    exact (sparseExceptionEffectiveFlagRankData_profile bits target).2.2.2.1
  relativeWidth_le_machine :=
    sparseExceptionRelativeWidth_le_machine bits
  payload_length_le_overhead := by
    have hflags :=
      sparseExceptionEffectiveFlagBits_length_le_overhead bits target
    have hrank :=
      sparseExceptionEffectiveFlagRankData_auxPayload_le_overhead bits target
    have hrelative :=
      sparseExceptionRelativeTable_payload_le_overhead bits target
    simp [canonicalSparseExceptionDirectoryOverhead] at hflags hrank hrelative ⊢
    omega

theorem sparseExceptionDirectory_readCosted_lookup_exact
    (bits : List Bool) (target : Bool)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < localSlotCount bits target)
    (heff :
      globalLocalSlot <
        sparseExceptionEffectiveLocalSlotCount bits target)
    (hflag :
      localIsSparseException bits target globalLocalSlot = true)
    (hocc :
      localOccurrence < localStride bits.length)
    (hend :
      localBaseOccurrence bits.length globalLocalSlot + localOccurrence <
        superEndOccurrence bits target
          (localSuperSlot bits.length globalLocalSlot))
    (hselect :
      RMQ.Succinct.select target bits
          (localBaseOccurrence bits.length globalLocalSlot + localOccurrence) =
        some pos) :
    ((sparseExceptionDirectory bits target).readCosted
      (position bits target
        (localBaseOccurrence bits.length globalLocalSlot))
      globalLocalSlot localOccurrence).erase =
      some
        (position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          (pos -
            position bits target
              (localBaseOccurrence bits.length globalLocalSlot))) := by
  have hread :=
    (sparseExceptionDirectory bits target).readCosted_exact
      (position bits target
        (localBaseOccurrence bits.length globalLocalSlot))
      globalLocalSlot localOccurrence
  rw [hread]
  change
    Option.map
      (fun offset =>
        position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          offset)
      ((sparseExceptionRelativeEntries bits target)[
          relativeSplitSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (sparseExceptionEffectiveFlagBits bits target)
              globalLocalSlot)
            localOccurrence
            (localStride bits.length)]?) =
      some
        (position bits target
            (localBaseOccurrence bits.length globalLocalSlot) +
          (pos -
            position bits target
              (localBaseOccurrence bits.length globalLocalSlot)))
  have hprefix :=
    sparseExceptionEffectiveFlagBits_prefix_eq
      bits target (globalLocalSlot := globalLocalSlot) (Nat.le_of_lt heff)
  rw [hprefix]
  have hlookup :=
    sparseExceptionRelativeEntries_lookup_exact
      bits target hslot hflag hocc hend hselect
  rw [relativeSplitSelectSparseCompactSlot]
  rw [hlookup]
  rfl


end RMQ.GenericSelect

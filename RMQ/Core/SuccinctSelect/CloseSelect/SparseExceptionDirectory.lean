import RMQ.Core.SuccinctSelect.CloseSelect.RelativeSplit

/-!
# Sparse-exception select directory

Split implementation layer for the select-side close-select proposal.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

structure RelativeSplitSparseExceptionDirectory
    (shape : Cartesian.CartesianShape)
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
      SuccinctRank.machineWordBits shape.bpCode.length
  rank_superWidth_le_machine :
    rankData.superWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length
  rank_blockWidth_le_machine :
    rankData.blockWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length
  relativeWidth_le_machine :
    relativeWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length
  payload_length_le_overhead :
    flagBits.length + rankData.auxPayload.length +
        relativeTable.payload.length <=
      canonicalSparseExceptionDirectoryOverhead shape.size

namespace RelativeSplitSparseExceptionDirectory

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  directory.flagBits ++ directory.rankData.auxPayload ++
    directory.relativeTable.payload

theorem payload_length_le_canonical
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
      canonicalSparseExceptionDirectoryOverhead shape.size := by
  simpa [payload, Nat.add_assoc] using
    directory.payload_length_le_overhead

def readWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  directory.rankData.superTables.trueTable.store.words.toList ++
    directory.rankData.superTables.falseTable.store.words.toList ++
      directory.rankData.blockTables.trueTable.store.words.toList ++
        directory.rankData.blockTables.falseTable.store.words.toList ++
          directory.rankData.bitWords.store.words.toList ++
            directory.relativeTable.store.words.toList

def readCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.rankData.rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted directory.relativeTable base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readCosted_cost_le_five
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).cost <= 5 := by
  unfold readCosted relativeOffsetReadCosted
  have hrank :=
    directory.rankData.rankCosted_cost_le_four true localSlot
  have hrelative :=
    directory.relativeTable.readCosted_cost_le_one
      (relativeSplitFalseSelectSparseCompactSlot
        (directory.rankData.rankCosted true localSlot).value
        localOccurrence directory.localStride)
  simp [Costed.bind, Costed.map] at *
  omega

theorem readCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).erase =
      (directory.relativeEntries[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
            localOccurrence directory.localStride]?).map
        (fun offset => base + offset) := by
  have hrank :=
    directory.rankData.rankCosted_exact true localSlot
  change (directory.rankData.rankCosted true localSlot).value =
      RMQ.Succinct.rankPrefix true directory.flagBits localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
      localOccurrence directory.localStride
  have hread :
      (directory.relativeTable.readCosted slot).value =
        directory.relativeEntries[slot]? := by
    simpa [Costed.erase] using
      directory.relativeTable.readCosted_erase slot
  unfold readCosted relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word directory.readWords) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
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
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
        canonicalSparseExceptionDirectoryOverhead shape.size /\
      (forall base localSlot localOccurrence,
        (directory.readCosted
          base localSlot localOccurrence).cost <= 5) /\
      (forall base localSlot localOccurrence,
        (directory.readCosted base localSlot localOccurrence).erase =
          (directory.relativeEntries[
              relativeSplitFalseSelectSparseCompactSlot
                (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
                localOccurrence directory.localStride]?).map
            (fun offset => base + offset)) /\
      forall {word : List Bool},
        List.Mem word directory.readWords ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length := by
  exact
    ⟨directory.payload_length_le_canonical,
      directory.readCosted_cost_le_five,
      directory.readCosted_exact,
      fun {word} hmem => directory.read_words_length_le_machine hmem⟩

end RelativeSplitSparseExceptionDirectory

def builtRelativeSplitSparseExceptionDirectory
    (shape : Cartesian.CartesianShape) :
    RelativeSplitSparseExceptionDirectory
      shape
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
        shape) where
  localStride := sparseDenseFalseSelectLocalStride shape
  localStride_pos := sparseDenseFalseSelectLocalStride_pos shape
  flagBits :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape
  rankData :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData shape
  relativeEntries :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape
  relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  relativeTable :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
  rank_wordSize_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.1
  rank_superWidth_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.2.1
  rank_blockWidth_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.2.2.1
  relativeWidth_le_machine :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine shape
  payload_length_le_overhead := by
    have hflags :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_overhead
        shape
    have hrank :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
        shape
    have hrelative :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
        shape
    have hbp : shape.bpCode.length = 2 * shape.size :=
      Cartesian.CartesianShape.bpCode_length shape
    simp [canonicalSparseExceptionDirectoryOverhead,
      hbp] at hflags hrank hrelative ⊢
    omega

def canonicalRelativeSplitSparseExceptionFalseSelectOverhead
    (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
    SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) + 16) +
        compactLongSuperRelativeTableOverhead n +
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 (2 * n) +
            canonicalSparseExceptionDirectoryOverhead n

theorem canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead := by
  unfold canonicalRelativeSplitSparseExceptionFalseSelectOverhead
  have hsuper :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hflags :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) +
            16) :=
    ((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192)
      |>.comp_two_mul_arg).add_const 16
  have hlocal :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 640)
      |>.comp_two_mul_arg
  exact
    (((((hsuper.add hflags).add hrank).add
      compactLongSuperRelativeTableOverhead_littleO).add hlocal).add
      canonicalSparseExceptionDirectoryOverhead_littleO)


end SuccinctSelectProposal
end RMQ

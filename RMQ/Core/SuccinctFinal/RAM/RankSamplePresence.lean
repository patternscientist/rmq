import RMQ.Core.GenericSelect.RAM

/-!
# Seed-word presence for two-level rank data (shared)

Two generic presence facts about
`SuccinctRank.TwoLevelPayloadLiveStoredWordRankData`, previously carried as
byte-identical `private` copies in
`RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilityLong.lean` and
`RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySparse.lean`.  They are
consumed by the reviewer-reachability witnesses and by the E1 amended
machine's canonical-store select form
(`RMQ/Core/WordRAM/E1SelectCanonical.lean`), which needs the three seed
reads of a select-side rank object to be PRESENT at the canonical global
store.  Single-sourcing them here removes the duplication instead of
adding a third copy.
-/

namespace RMQ
namespace SuccinctFinal

/--
A fixed-width table presents a stored word at every index whose logical
entry is present: the codec `read_exact` equation would otherwise read
`none` where the entry list reads `some`.
-/
theorem fixedWidthNatTable_word_present_of_entry_present
    {entries : List Nat} {width i entry : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hentry : entries[i]? = some entry) :
    ∃ word, table.store.words[i]? = some word := by
  cases hword : table.store.words[i]? with
  | none =>
      have hexact := table.read_exact i
      rw [hword, hentry] at hexact
      simp at hexact
  | some word => exact ⟨word, rfl⟩

/--
All three seed words of a two-level rank object — super sample, block
sample, and the packed payload word — are present at any position within
the payload.  Stated in the `superSampleWords`/`blockSampleWords`
vocabulary, so it composes with per-address store-agreement lemmas by
plain rewriting, with no `read_exact` codec detour at the call site.
-/
theorem twoLevelRankData_sample_words_present
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) (hpos : pos <= bits.length) :
    (∃ word,
      (data.superSampleWords
        target)[pos / data.wordSize / data.blocksPerSuper]? = some word) ∧
    (∃ word,
      (data.blockSampleWords target)[pos / data.wordSize]? = some word) ∧
    (∃ word,
      data.bitWords.store.words[pos / data.wordSize]? = some word) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases data.super_present target pos hpos with ⟨sample, hsample⟩
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hsample
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.superTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hsample
  · rcases data.block_present target pos hpos with ⟨delta, hdelta⟩
    cases target with
    | false =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.falseTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hdelta
    | true =>
        apply fixedWidthNatTable_word_present_of_entry_present
          data.blockTables.trueTable
        simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
          hdelta
  · exact data.word_present pos hpos

end SuccinctFinal
end RMQ

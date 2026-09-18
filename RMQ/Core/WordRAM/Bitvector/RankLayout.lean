import RMQ.Core.WordRAM.Bitvector.RegularLayout

/-! # Layout of the actual canonical Jacobson rank arrays

The overhead-index cast in jacobsonRankData preserves all runtime projections.
Every theorem below concerns that actual record and its actual arrays.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank

private theorem rank_cast_project
    {bits : List Bool} {s b s' b' q : Nat} {α : Type}
    (hs : s = s') (hb : b = b')
    (h : TwoLevelPayloadLiveStoredWordRankData bits s b q =
      TwoLevelPayloadLiveStoredWordRankData bits s' b' q)
    (d : TwoLevelPayloadLiveStoredWordRankData bits s b q)
    (f : ∀ s b, TwoLevelPayloadLiveStoredWordRankData bits s b q → α) :
    f s' b' (cast h d) = f s b d := by
  subst s'
  subst b'
  rfl

private abbrev jacobsonUncast (bits : List Bool) :=
  canonicalTwoLevelRankDataOfChunksExactLocalBlock bits
    (jacobsonRankBuilderSideConditions bits).1
    (jacobsonRankBuilderSideConditions bits).2.1
    (jacobsonRankBuilderSideConditions bits).2.2.1
    (jacobsonRankBuilderSideConditions bits).2.2.2.1
    (jacobsonRankBuilderSideConditions bits).2.2.2.2.1
    (jacobsonRankBuilderSideConditions bits).2.2.2.2.2

private theorem jacobson_project (bits : List Bool) {α : Type}
    (f : ∀ s b, TwoLevelPayloadLiveStoredWordRankData bits s b 4 → α) :
    f _ _ (jacobsonRankData bits) = f _ _ (jacobsonUncast bits) := by
  unfold jacobsonRankData
  exact rank_cast_project
    (canonicalSuperRankSampleTables_payload_length_jacobson bits)
    (canonicalBlockRankSampleTablesOfLocalSpan_payload_length_jacobson bits)
    _ _ f

theorem jacobson_wordSize_eq (bits : List Bool) :
    (jacobsonRankData bits).wordSize = machineWordBits bits.length :=
  jacobson_project bits (fun _ _ d => d.wordSize)

theorem jacobson_blocksPerSuper_eq (bits : List Bool) :
    (jacobsonRankData bits).blocksPerSuper = machineWordBits bits.length :=
  jacobson_project bits (fun _ _ d => d.blocksPerSuper)

theorem jacobson_superWidth_eq (bits : List Bool) :
    (jacobsonRankData bits).superWidth = machineWordBits bits.length :=
  jacobson_project bits (fun _ _ d => d.superWidth)

theorem jacobson_blockWidth_eq (bits : List Bool) :
    (jacobsonRankData bits).blockWidth =
      machineWordBits (machineWordBits bits.length * machineWordBits bits.length) :=
  jacobson_project bits (fun _ _ d => d.blockWidth)

theorem jacobson_raw_words_eq (bits : List Bool) :
    (jacobsonRankData bits).bitWords.store.words =
      (BoundedPayloadWordStore.ofChunksWithSentinel bits
        (machineWordBits_pos bits.length)).store.words :=
  jacobson_project bits (fun _ _ d => d.bitWords.store.words)

/-- The exact four arrays appended by the final allocation, in its order. -/
def jacobsonSampleArrays (bits : List Bool) : List (Array (List Bool)) :=
  let d := jacobsonRankData bits
  [d.superTables.falseTable.store.words, d.superTables.trueTable.store.words,
   d.blockTables.falseTable.store.words, d.blockTables.trueTable.store.words]

theorem jacobson_raw_regular (bits : List Bool) :
    RegularWords (jacobsonRankData bits).bitWords.store.words := by
  rw [jacobson_raw_words_eq]
  exact regularWords_ofChunksWithSentinel bits (machineWordBits_pos bits.length)

theorem jacobson_samples_regular (bits : List Bool) (words : Array (List Bool))
    (hwords : words ∈ jacobsonSampleArrays bits) : RegularWords words := by
  simp only [jacobsonSampleArrays, List.mem_cons, List.not_mem_nil, or_false] at hwords
  rcases hwords with rfl | rfl | rfl | rfl <;>
    exact regularWords_fixedWidthTable _

private theorem table_words_size {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) : table.store.words.size = entries.length := by
  have heq : table.store.words.toList.map bitsToNatLE = entries := by
    apply List.ext_getElem?
    intro i
    simpa only [List.getElem?_map, Array.getElem?_toList] using table.read_exact i
  have hlen := congrArg List.length heq
  simpa using hlen

private theorem jacobson_super_entries_length (bits : List Bool) :
    (jacobsonRankData bits).superFalseEntries.length =
      bits.length / machineWordBits bits.length / machineWordBits bits.length + 1 ∧
    (jacobsonRankData bits).superTrueEntries.length =
      bits.length / machineWordBits bits.length / machineWordBits bits.length + 1 := by
  have hf := jacobson_project bits (fun _ _ d => d.superFalseEntries)
  have ht := jacobson_project bits (fun _ _ d => d.superTrueEntries)
  change (jacobsonRankData bits).superFalseEntries =
    canonicalSuperRankEntries false bits (machineWordBits bits.length)
      (machineWordBits bits.length) at hf
  change (jacobsonRankData bits).superTrueEntries =
    canonicalSuperRankEntries true bits (machineWordBits bits.length)
      (machineWordBits bits.length) at ht
  rw [hf, ht, canonicalSuperRankEntries_length, canonicalSuperRankEntries_length]
  exact ⟨rfl, rfl⟩

private theorem jacobson_block_entries_length (bits : List Bool) :
    (jacobsonRankData bits).blockFalseEntries.length =
      bits.length / machineWordBits bits.length + 1 ∧
    (jacobsonRankData bits).blockTrueEntries.length =
      bits.length / machineWordBits bits.length + 1 := by
  have hf := jacobson_project bits (fun _ _ d => d.blockFalseEntries)
  have ht := jacobson_project bits (fun _ _ d => d.blockTrueEntries)
  change (jacobsonRankData bits).blockFalseEntries =
    canonicalBlockRankEntries false bits (machineWordBits bits.length)
      (machineWordBits bits.length) at hf
  change (jacobsonRankData bits).blockTrueEntries =
    canonicalBlockRankEntries true bits (machineWordBits bits.length)
      (machineWordBits bits.length) at ht
  rw [hf, ht, canonicalBlockRankEntries_length, canonicalBlockRankEntries_length]
  exact ⟨rfl, rfl⟩

theorem jacobson_samples_count_le (bits : List Bool) (words : Array (List Bool))
    (hwords : words ∈ jacobsonSampleArrays bits) : words.size ≤ bits.length + 1 := by
  have hs := jacobson_super_entries_length bits
  have hb := jacobson_block_entries_length bits
  have hd1 := Nat.div_le_self bits.length (machineWordBits bits.length)
  have hd2 := Nat.div_le_self (bits.length / machineWordBits bits.length)
    (machineWordBits bits.length)
  simp only [jacobsonSampleArrays, List.mem_cons, List.not_mem_nil, or_false] at hwords
  rcases hwords with rfl | rfl | rfl | rfl <;>
    rw [table_words_size] <;> omega

theorem jacobson_raw_count_le (bits : List Bool) :
    (jacobsonRankData bits).bitWords.store.words.size ≤ 2 * bits.length + 2 := by
  rw [jacobson_raw_words_eq]
  change (chunkPayloadWords (machineWordBits bits.length) bits ++
    List.replicate (bits.length + 1) []).toArray.size ≤ _
  simp only [List.size_toArray, List.length_append, List.length_replicate]
  have hchunks := chunkPayloadWords_length_le_div_add_one
    (machineWordBits_pos bits.length) bits
  have hdiv := Nat.div_le_self bits.length (machineWordBits bits.length)
  omega

private theorem jacobson_blockWidth_le (bits : List Bool) :
    (jacobsonRankData bits).blockWidth ≤ 2 * machineWordBits bits.length + 3 := by
  rw [jacobson_blockWidth_eq]
  have hm := machineWordBits_mul_self_log_bound (machineWordBits bits.length)
  have hn := nestedMachineWordBits_le_succ bits.length
  omega

private theorem table_word_length {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (word : List Bool)
    (hword : word ∈ table.store.words.toList) : word.length = width := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hword
  exact table.word_length_of_get? (by simpa using hi)

theorem jacobson_sample_word_length_le (bits : List Bool) (words : Array (List Bool))
    (hwords : words ∈ jacobsonSampleArrays bits) (word : List Bool)
    (hword : word ∈ words.toList) : word.length ≤ 2 * machineWordBits bits.length + 3 := by
  have hs := jacobson_superWidth_eq bits
  have hb := jacobson_blockWidth_le bits
  simp only [jacobsonSampleArrays, List.mem_cons, List.not_mem_nil, or_false] at hwords
  rcases hwords with rfl | rfl | rfl | rfl
  · have hlen := table_word_length (jacobsonRankData bits).superTables.falseTable word hword
    omega
  · have hlen := table_word_length (jacobsonRankData bits).superTables.trueTable word hword
    omega
  · have hlen := table_word_length (jacobsonRankData bits).blockTables.falseTable word hword
    omega
  · have hlen := table_word_length (jacobsonRankData bits).blockTables.trueTable word hword
    omega

theorem jacobson_raw_word_length_le (bits : List Bool) (word : List Bool)
    (hword : word ∈ (jacobsonRankData bits).bitWords.store.words.toList) :
    word.length ≤ machineWordBits bits.length := by
  exact Nat.le_trans ((jacobsonRankData bits).bitWords.word_length_le hword)
    (jacobsonRankData bits).wordSize_le_machine

/-- All fields concern the same actual Jacobson record, with no readiness
assumption. This is the direct input to final allocation geometry. -/
theorem jacobsonRankLayout (bits : List Bool) :
    let d := jacobsonRankData bits
    let n := bits.length
    let m := machineWordBits n
    d.wordSize = m ∧ d.blocksPerSuper = m ∧
      RegularWords d.bitWords.store.words ∧ d.bitWords.store.words.size ≤ 2*n+2 ∧
      (∀ word ∈ d.bitWords.store.words.toList, word.length ≤ m) ∧
      ∀ words ∈ jacobsonSampleArrays bits,
        RegularWords words ∧ words.size ≤ n+1 ∧
          ∀ word ∈ words.toList, word.length ≤ 2*m+3 := by
  exact ⟨jacobson_wordSize_eq bits, jacobson_blocksPerSuper_eq bits,
    jacobson_raw_regular bits, jacobson_raw_count_le bits,
    jacobson_raw_word_length_le bits,
    fun words hwords => ⟨jacobson_samples_regular bits words hwords,
      jacobson_samples_count_le bits words hwords,
      jacobson_sample_word_length_le bits words hwords⟩⟩

end RMQ.PackedBitvector

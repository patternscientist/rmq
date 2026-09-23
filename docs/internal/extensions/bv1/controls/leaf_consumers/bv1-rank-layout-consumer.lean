import RMQ.Core.WordRAM.Bitvector.RankLayout
open RMQ RMQ.PackedBitvector RMQ.SuccinctSpace RMQ.SuccinctRank
example (bits : List Bool) : (jacobsonRankData bits).wordSize = machineWordBits bits.length :=
  jacobson_wordSize_eq bits
example (bits : List Bool) : (jacobsonRankData bits).blocksPerSuper = machineWordBits bits.length :=
  jacobson_blocksPerSuper_eq bits
example (bits : List Bool) :
  (jacobsonRankData bits).bitWords.store.words =
    (BoundedPayloadWordStore.ofChunksWithSentinel bits (machineWordBits_pos bits.length)).store.words :=
  jacobson_raw_words_eq bits
example (bits : List Bool) :
  let d := jacobsonRankData bits
  let n := bits.length
  let m := machineWordBits n
  d.wordSize = m ∧ d.blocksPerSuper = m ∧
    RegularWords d.bitWords.store.words ∧ d.bitWords.store.words.size ≤ 2*n+2 ∧
    (∀ word ∈ d.bitWords.store.words.toList, word.length ≤ m) ∧
    ∀ words ∈ [d.superTables.falseTable.store.words, d.superTables.trueTable.store.words,
      d.blockTables.falseTable.store.words, d.blockTables.trueTable.store.words],
      RegularWords words ∧ words.size ≤ n+1 ∧
        ∀ word ∈ words.toList, word.length ≤ 2*m+3 := jacobsonRankLayout bits
example (bits : List Bool) :
  (jacobsonRankData bits).superWidth = machineWordBits bits.length := jacobson_superWidth_eq bits
example (bits : List Bool) :
  (jacobsonRankData bits).blockWidth =
    machineWordBits (machineWordBits bits.length * machineWordBits bits.length) := jacobson_blockWidth_eq bits
example : ¬RegularWords #[[], [true]] := irregular_empty_head_rejected
#print axioms jacobson_wordSize_eq
#print axioms jacobson_blocksPerSuper_eq
#print axioms jacobson_superWidth_eq
#print axioms jacobson_blockWidth_eq
#print axioms jacobson_raw_words_eq
#print axioms jacobson_raw_regular
#print axioms jacobson_samples_regular
#print axioms jacobson_samples_count_le
#print axioms jacobson_raw_count_le
#print axioms jacobson_sample_word_length_le
#print axioms jacobson_raw_word_length_le
#print axioms jacobsonRankLayout

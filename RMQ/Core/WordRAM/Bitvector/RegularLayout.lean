import RMQ.Core.WordRAM.Bitvector.AllocationFacts

/-!
# Regular layouts of the canonical logical-word arrays

Descriptors store the first word's length as their stride and keep the logical
word count separately. These proofs cover every array retained by the generic
select allocation, including short first words and empty sentinel tails.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment
open SuccinctFinal.PackedWordRAM

/-- Exactly the stride field installed by `Experiment.descriptor`. -/
def firstLength (words : Array (List Bool)) : Nat :=
  (words[0]?.getD []).length

/-- Every present logical word is its descriptor's slice of the flattened bits. -/
def RegularWords (words : Array (List Bool)) : Prop :=
  ∀ i (hi : i < words.size),
    words[i] = ((segmentBits words).drop
      (i * firstLength words)).take (firstLength words)

theorem RegularWords.getElem?_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) :
    words[i]? = if i < words.size then
      some (((segmentBits words).drop
        (i * firstLength words)).take (firstLength words)) else none := by
  by_cases hi : i < words.size
  · rw [if_pos hi, Array.getElem?_eq_getElem hi, h i hi]
  · rw [if_neg hi]
    exact Array.getElem?_eq_none (by omega)

theorem RegularWords.length_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) (hi : i < words.size) :
    words[i].length = min (firstLength words)
      ((segmentBits words).length - i * firstLength words) := by
  rw [h i hi, List.length_take, List.length_drop]

/-- Recovery with the actual span length selected by the numeric descriptor. -/
theorem RegularWords.min_slice_eq {words : Array (List Bool)}
    (h : RegularWords words) (i : Nat) (hi : i < words.size) :
    words[i] = ((segmentBits words).drop (i * firstLength words)).take
      (min (firstLength words) ((segmentBits words).length - i * firstLength words)) := by
  have hle : words[i].length ≤ firstLength words := by
    rw [h.length_eq i hi]
    exact Nat.min_le_left _ _
  calc
    words[i] = words[i].take words[i].length := List.take_length.symm
    _ = (((segmentBits words).drop (i * firstLength words)).take
        (firstLength words)).take words[i].length := by rw [← h i hi]
    _ = ((segmentBits words).drop (i * firstLength words)).take words[i].length := by
      rw [List.take_take, Nat.min_eq_left hle]
    _ = _ := by rw [h.length_eq i hi]

private theorem slice_at_min_width (payload : List Bool) (width i : Nat) :
    (payload.drop (i * width)).take width =
      (payload.drop (i * min width payload.length)).take
        (min width payload.length) := by
  by_cases hw : width ≤ payload.length
  · rw [Nat.min_eq_left hw]
  · have hn : payload.length ≤ width := by omega
    rw [Nat.min_eq_right hn]
    cases i with
    | zero => simp [List.take_of_length_le hn]
    | succ i =>
        have hwide : payload.length ≤ (i + 1) * width := by
          rw [Nat.succ_mul]
          omega
        have hshort : payload.length ≤ (i + 1) * payload.length := by
          rw [Nat.succ_mul]
          omega
        rw [List.drop_eq_nil_of_le hwide, List.drop_eq_nil_of_le hshort]
        simp

/-- Any exact chunk slicing can use the observed first-word length as stride. -/
theorem regularWords_of_slices (words : Array (List Bool)) (payload : List Bool)
    (width : Nat) (herase : segmentBits words = payload)
    (hslices : ∀ i (hi : i < words.size),
      words[i] = (payload.drop (i * width)).take width) :
    RegularWords words := by
  intro i hi
  have hzero : 0 < words.size := by omega
  have hfirst : firstLength words = min width payload.length := by
    simp only [firstLength, Array.getElem?_eq_getElem hzero, Option.getD_some]
    rw [hslices 0 hzero]
    simp
  rw [hslices i hi, herase, hfirst]
  exact slice_at_min_width payload width i

/-- Uniform tables also allow zero-width rows and an empty array. -/
theorem regularWords_of_uniform (words : Array (List Bool)) (width : Nat)
    (hwidth : ∀ word ∈ words.toList, word.length = width) : RegularWords words := by
  apply regularWords_of_slices words (segmentBits words) width rfl
  intro i hi
  have h := uniform_flatten_slice words.toList width hwidth i
  simpa only [segmentBits, Array.getElem?_toList,
    Array.getElem?_eq_getElem hi, Option.getD_some] using h.symm

theorem regularWords_fixedWidthTable {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) : RegularWords table.store.words := by
  apply regularWords_of_uniform table.store.words width
  intro word hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  exact table.word_length_of_get? (i := i) (by simpa using hi)

private theorem chunks_empty_tail_get?_slice
    (payload : List Bool) {width : Nat} (hw : 0 < width) (sentinels : Nat)
    {i : Nat} {word : List Bool}
    (hget : (chunkPayloadWords width payload ++
      List.replicate sentinels [])[i]? = some word) :
    word = (payload.drop (i * width)).take width := by
  by_cases hi : i < (chunkPayloadWords width payload).length
  · rw [List.getElem?_append_left hi] at hget
    exact chunkPayloadWords_get?_eq_take_drop hget
  · have hcovered : payload.length ≤ i * width := by
      by_cases hcov : payload.length ≤ i * width
      · exact hcov
      have hstart : i * width < payload.length := by omega
      obtain ⟨chunk, hchunk⟩ := chunkPayloadWords_get?_some_of_mul_lt hw hstart
      have hindex := (List.getElem?_eq_some_iff.mp hchunk).1
      omega
    rw [List.getElem?_append_right (by omega)] at hget
    have hempty : word = [] := (List.mem_replicate.mp (List.mem_of_getElem? hget)).2
    rw [hempty, List.drop_eq_nil_of_le hcovered]
    simp

private theorem flattenPayloadWords_eq_listFlatten (words : List (List Bool)) :
    flattenPayloadWords words = words.flatten := by
  induction words with
  | nil => rfl
  | cons word words ih => simp [flattenPayloadWords, ih]

/-- A chunk array remains regular after any number of trailing empty words. -/
theorem regularWords_chunks_with_empty_tail
    (payload : List Bool) {width : Nat} (hw : 0 < width) (sentinels : Nat) :
    RegularWords ((chunkPayloadWords width payload ++
      List.replicate sentinels []).toArray) := by
  apply regularWords_of_slices _ payload width
  · simp only [segmentBits]
    rw [← flattenPayloadWords_eq_listFlatten, flattenPayloadWords_append,
      flattenPayloadWords_chunkPayloadWords hw payload,
      flattenPayloadWords_replicate_nil]
    simp
  · intro i hi
    apply chunks_empty_tail_get?_slice payload hw sentinels
    rw [← List.getElem?_toArray]
    exact Array.getElem?_eq_getElem hi

theorem regularWords_ofChunks (payload : List Bool) {width : Nat} (hw : 0 < width) :
    RegularWords (BoundedPayloadWordStore.ofChunks payload hw).store.words := by
  simpa only [BoundedPayloadWordStore.ofChunks, List.replicate_zero,
    List.append_nil] using regularWords_chunks_with_empty_tail payload hw 0

theorem regularWords_ofChunksWithSentinel
    (payload : List Bool) {width : Nat} (hw : 0 < width) :
    RegularWords (BoundedPayloadWordStore.ofChunksWithSentinel payload hw).store.words :=
  regularWords_chunks_with_empty_tail payload hw (payload.length + 1)

/-- Fixed-width contracts discharge fourteen components; only the two flag
chunk layouts remain as premises of this generic directory lemma. -/
theorem directorySegments_regular
    {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb)
    (hlong : RegularWords d.longFlagRankData.bitWords.store.words)
    (hsparse : RegularWords d.sparseDirectory.rankData.bitWords.store.words) :
    ∀ words ∈ directorySegments d, RegularWords words := by
  intro words hmem
  simp only [directorySegments, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact regularWords_fixedWidthTable _
    | exact hlong
    | exact hsparse

theorem canonical_bitWords_regular (bits : List Bool) (target : Bool) :
    RegularWords (sparseExceptionSelectData bits target).bitWords.store.words := by
  change RegularWords (BoundedPayloadWordStore.ofChunks
    bits (wordBits_pos bits.length)).store.words
  exact regularWords_ofChunks bits (wordBits_pos bits.length)

/-- Both flag stores use the actual sentinel-bearing canonical rank builder. -/
theorem canonical_directorySegments_regular (bits : List Bool) (target : Bool) :
    ∀ words ∈ directorySegments (sparseExceptionSelectData bits target),
      RegularWords words := by
  apply directorySegments_regular
  · change RegularWords (BoundedPayloadWordStore.ofChunksWithSentinel
      (longSuperFlagBits bits target) (longFlagRankWordSize_pos bits target)).store.words
    exact regularWords_ofChunksWithSentinel _ _
  · change RegularWords (BoundedPayloadWordStore.ofChunksWithSentinel
      (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankWordSize_pos bits target)).store.words
    exact regularWords_ofChunksWithSentinel _ _

/-- Every actual body array in `Experiment.memory`, at every input size. -/
theorem canonical_allSegments_regular (bits : List Bool) :
    let df := sparseExceptionSelectData bits false
    let dt := sparseExceptionSelectData bits true
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    ∀ words ∈ [df.bitWords.store.words] ++
        directorySegments df ++ directorySegments dt ++
        [(SuccinctClose.bpFringeChunkTable c).store.words,
         (SuccinctClose.bpChunkSelectTable c false).store.words],
      RegularWords words := by
  dsimp only
  intro words hmem
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | hf | ht | rfl | rfl
  · exact canonical_bitWords_regular bits false
  · exact canonical_directorySegments_regular bits false words hf
  · exact canonical_directorySegments_regular bits true words ht
  · exact regularWords_fixedWidthTable _
  · exact regularWords_fixedWidthTable _

/-- An empty first word cannot describe a later nonempty logical word. -/
theorem irregular_empty_head_rejected : ¬ RegularWords #[[], [true]] := by
  intro h
  have bad := h 1 (by decide)
  simp [firstLength, segmentBits] at bad

-- Present empty words retain their count even with a zero-bit flattened body.
example : RegularWords #[[], [], []] :=
  regularWords_of_uniform _ 0 (by simp)

-- The configured width exceeds the first logical word's actual length.
example : RegularWords (BoundedPayloadWordStore.ofChunksWithSentinel
    [true] (by decide : 0 < 8)).store.words :=
  regularWords_ofChunksWithSentinel _ _

end RMQ.PackedBitvector

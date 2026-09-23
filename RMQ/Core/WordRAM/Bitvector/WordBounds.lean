import RMQ.Core.WordRAM.Bitvector.MemoryLayout
import RMQ.Core.WordRAM.Bitvector.RegularLayout
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTableFacts

/-! # Logical span widths for the generic allocation

The bounds concern the actual stored component words and the experiment's
single input-size-dependent physical width. Arithmetic and address safety of
the complete program remain separate obligations.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment
open SuccinctFinal.PackedWordRAM

theorem width_pos (n : Nat) : 0 < width n := by unfold width; omega

theorem machineWordBits_lt_width (n : Nat) : machineWordBits n < width n := by
  unfold width
  omega

theorem log2_double_le (n : Nat) : Nat.log2 (2 * n) ≤ Nat.log2 n + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hdouble : 2 ^ (Nat.log2 n + 2) = 2 * 2 ^ (Nat.log2 n + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  by_cases h : Nat.log2 (2 * n) ≤ Nat.log2 n + 1
  · exact h
  · have hp : 2 ^ (Nat.log2 n + 2) ≤ 2 ^ Nat.log2 (2 * n) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hself : 2 ^ Nat.log2 (2 * n) ≤ 2 * n := Nat.log2_self_le (by omega)
    omega

theorem chunkBits_le (n : Nat) :
    SuccinctClose.bpFringeChunkBits (2 * n) ≤ machineWordBits n + 1 := by
  have hl := log2_double_le n
  have hd := Nat.div_le_self (Nat.log2 (2 * n)) 8
  unfold SuccinctClose.bpFringeChunkBits machineWordBits
  omega

theorem directorySegments_word_length {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb)
    (words : Array (List Bool)) (hs : words ∈ directorySegments d)
    (word : List Bool) (hw : word ∈ words.toList) :
    word.length ≤ machineWordBits bits.length := by
  apply d.read_word_length_le_machine
  change word ∈ d.readWords
  simp only [directorySegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SparseExceptionSelectData.readWords, SparseExceptionSelectData.longFlagRankReadWords,
      FixedWidthSparseDenseSelectDenseLocalEntryTable.readWords,
      SparseExceptionDirectory.readWords, List.mem_append, hw]

theorem allSegments_word_length_lt (bits : List Bool)
    (words : Array (List Bool)) (hs : words ∈ allSegments bits)
    (word : List Bool) (hw : word ∈ words.toList) : word.length < width bits.length := by
  simp only [allSegments, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((rfl | hfalse) | htrue) | (rfl | rfl)
  · have h := (sparseExceptionSelectData bits false).bitWords.word_length_le hw
    have hb := (sparseExceptionSelectData bits false).wordSize_le_machine
    have hwidth := machineWordBits_lt_width bits.length
    omega
  · exact Nat.lt_of_le_of_lt (directorySegments_word_length _ _ hfalse _ hw)
      (machineWordBits_lt_width bits.length)
  · exact Nat.lt_of_le_of_lt (directorySegments_word_length _ _ htrue _ hw)
      (machineWordBits_lt_width bits.length)
  · obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hw
    have hl := (SuccinctClose.bpFringeChunkTable
      (SuccinctClose.bpFringeChunkBits (2 * bits.length))).word_length_of_get?
        (by simpa using hi)
    have hb := SuccinctClose.bpFringeChunkEntryWidth_le
      (SuccinctClose.bpFringeChunkBits (2 * bits.length))
    have hc := chunkBits_le bits.length
    unfold width
    omega
  · obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hw
    have hl := (SuccinctClose.bpChunkSelectTable
      (SuccinctClose.bpFringeChunkBits (2 * bits.length)) false).word_length_of_get?
        (by simpa using hi)
    have hb := SuccinctClose.bpChunkSelectEntryWidth_le
      (SuccinctClose.bpFringeChunkBits (2 * bits.length))
    have hc := chunkBits_le bits.length
    unfold width
    omega

theorem allSegments_regular (bits : List Bool) (words : Array (List Bool))
    (hs : words ∈ allSegments bits) : RegularWords words :=
  canonical_allSegments_regular bits words hs

theorem allSegments_firstLength_lt (bits : List Bool) (words : Array (List Bool))
    (hs : words ∈ allSegments bits) : firstLength words < width bits.length := by
  cases hg : words[0]? with
  | none => simpa [firstLength, hg] using width_pos bits.length
  | some word =>
    have hm : word ∈ words.toList := List.mem_of_getElem? (by simpa using hg)
    simpa [firstLength, hg] using allSegments_word_length_lt bits words hs word hm

end RMQ.PackedBitvector

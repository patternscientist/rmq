import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL F5 PROBE, PART 3.

The F5 defence conceded ONE non-theorem: "the component offsets are size-only,
but that factorisation is not yet a theorem" -- offsets are built from
`(...machineStore hword).store.words.size` (InteriorDirectory.lean:1614-1647),
i.e. from the actual constructed content.

This file tries to break that link, and instead CLOSES it: the machine-store
word count of ANY `FixedWidthNatTable` of positive width is
`entries.length * chunkCount(width, wordSize)` -- no dependence on entry VALUES.
-/

open RMQ RMQ.SuccinctSpace

namespace AdvQOff

private theorem flatMap_length_const
    {alpha beta : Type} (xs : List alpha) (f : alpha -> List beta) (c : Nat)
    (h : forall x, List.Mem x xs -> (f x).length = c) :
    (xs.flatMap f).length = xs.length * c := by
  induction xs with
  | nil => simp
  | cons a t ih =>
      have hhead : (f a).length = c := h a List.mem_cons_self
      have htail : forall y, List.Mem y t -> (f y).length = c := by
        intro y hy
        exact h y (List.mem_cons_of_mem a hy)
      rw [List.flatMap_cons, List.length_append, hhead, ih htail]
      simp [Nat.succ_mul]
      omega

/-- Every logical word of a fixed-width table really has length `width`. -/
private theorem word_length_of_mem
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {word : List Bool} (hmem : List.Mem word table.store.words.toList) :
    word.length = width := by
  rcases List.mem_iff_getElem?.mp hmem with ⟨j, hj⟩
  exact table.word_length_of_get? (by simpa [Array.getElem?_toList] using hj)

/-- **The logical word count of a fixed-width table is its entry count.**
No dependence on entry values. -/
theorem store_words_size_eq_entries_length
    {entries : List Nat} {width : Nat} (hwidth : 0 < width)
    (table : FixedWidthNatTable entries width) :
    table.store.words.size = entries.length := by
  have hflat :
      (flattenPayloadWords table.store.words.toList).length =
        table.store.words.toList.length * width :=
    flattenPayloadWords_length_of_forall_length
      (fun {w} hw => word_length_of_mem table hw)
  rw [table.store.erases, table.payload_length_eq] at hflat
  have hsize : table.store.words.toList.length = table.store.words.size := by
    simp
  rw [hsize] at hflat
  exact (Nat.eq_of_mul_eq_mul_right hwidth hflat.symm)

/-- **The MACHINE word count of a fixed-width table factors through
`entries.length` and `width` only.**  This is the missing link: every component
offset in `canonicalRelativeRmmInteriorComponentOffsets` is a partial sum of
these counts, so if entry lengths and widths are size-only, so are the offsets --
regardless of what the entries CONTAIN. -/
theorem machineStore_words_size_eq
    {entries : List Nat} {width wordSize : Nat}
    (hwidth : 0 < width) (hword : 0 < wordSize)
    (table : FixedWidthNatTable entries width) :
    ((table.machineStore hword).store.words.size) =
      entries.length * fixedWidthNatTableMachineChunkCount width wordSize := by
  have hconst :
      forall w, List.Mem w table.store.words.toList ->
        (chunkPayloadWords wordSize w).length =
          fixedWidthNatTableMachineChunkCount width wordSize := by
    intro w hw
    have hlen : w.length = width := word_length_of_mem table hw
    simpa [fixedWidthNatTableMachineChunkCount, hlen] using
      chunkPayloadWords_length_eq_div_add_indicator hword w
  have hflat :=
    flatMap_length_const table.store.words.toList
      (chunkPayloadWords wordSize)
      (fixedWidthNatTableMachineChunkCount width wordSize) hconst
  have hsize := store_words_size_eq_entries_length hwidth table
  simp only [FixedWidthNatTable.machineStore, fixedWidthNatTableMachineWords,
    Array.size_toArray]
  rw [hflat]
  simp only [Array.length_toList] at *
  rw [hsize]

/-- Corollary in the exact form the offsets need: two same-width tables whose
ENTRY LISTS MERELY HAVE EQUAL LENGTH occupy the same number of machine words. -/
theorem machineStore_words_size_congr
    {entriesA entriesB : List Nat} {width wordSize : Nat}
    (hwidth : 0 < width) (hword : 0 < wordSize)
    (tableA : FixedWidthNatTable entriesA width)
    (tableB : FixedWidthNatTable entriesB width)
    (hlen : entriesA.length = entriesB.length) :
    (tableA.machineStore hword).store.words.size =
      (tableB.machineStore hword).store.words.size := by
  rw [machineStore_words_size_eq hwidth hword tableA,
    machineStore_words_size_eq hwidth hword tableB, hlen]

end AdvQOff

#print axioms AdvQOff.store_words_size_eq_entries_length
#print axioms AdvQOff.machineStore_words_size_eq
#print axioms AdvQOff.machineStore_words_size_congr

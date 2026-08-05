import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerMachineWords

/-!
# Machine words of an entry-chunked table, with no width hypothesis

`ReviewerMachineWords.lean` handled the case where a logical entry fits one
machine word. Measurement says that case does not cover the interior.

On the right spine, comparing each interior column's entry width against
`machineWordBits (2 * n)`:

```
n      0  1  2  4   8  16  64  128  256  512  1024
W      1  2  3  4   5   6   8    9   10   11    12
super  1  2  3  4   5   6   8    9   10   11    12   -- equals W
offset 1  1  3  4   5   5   6    7    7    7     7   -- below W
addr   1  1  1  1   2   2   4    5    5    6     7   -- below W
rel    5  5  7  7   9   9   9   11   11   11    11   -- ABOVE W below ~512
```

So `minRel`, `maxRel` and `argOffset` -- three of the eight interior components --
carry entries **wider than a machine word** at every size below roughly `512`, and
their machine stores genuinely split each entry. The `width <= wordSize` route
covers the other five and cannot cover these.

`packedMachineStoreWords_getElem?_general` removes the hypothesis. Machine word
`i` is chunk `i % c` of logical entry `i / c`, where `c` is the number of machine
words one entry occupies. The `c = 1` case is exactly the earlier lemma.

The two-level index is the honest shape of this store: entries are chunked
individually, so the word grid is a grid of grids, and any single-level
`packedWordSlice` claim over the component payload would be false in precisely the
regime measured above.

## What this module does not establish

* No interior component is instantiated here; each still needs its width and
  positivity supplied.
* The composition to a payload-relative bit address -- entry `i / c` at
  `(i / c) * width`, chunk `i % c` at a further `(i % c) * wordSize` -- is
  mechanical from this plus `packedFixedWidthTable_getElem?`, and is not yet
  written.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/--
**Indexing a flatMap whose blocks all have the same length.** Word `i` is block
`i / c`, element `i % c`.
-/
theorem packedFlatMapUniform_getElem?
    {alpha beta : Type} (f : alpha -> List beta) {c : Nat} (hc : 0 < c)
    (l : List alpha)
    (huniform : forall {x : alpha}, List.Mem x l -> (f x).length = c) (i : Nat) :
    (l.flatMap f)[i]? = (l[i / c]?).bind (fun x => (f x)[i % c]?) := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
      have ha : (f a).length = c := huniform List.mem_cons_self
      have ht : forall {x : alpha}, List.Mem x t -> (f x).length = c := by
        intro x hx
        exact huniform (List.mem_cons_of_mem a hx)
      rw [List.flatMap_cons, List.getElem?_append]
      by_cases hlt : i < c
      · have hlt' : i < (f a).length := by omega
        rw [if_pos hlt']
        have hdiv : i / c = 0 := Nat.div_eq_of_lt hlt
        have hmod : i % c = i := Nat.mod_eq_of_lt hlt
        rw [hdiv, hmod]
        simp
      · have hge : c <= i := by omega
        obtain ⟨j, rfl⟩ : exists j, i = j + c := ⟨i - c, by omega⟩
        have hnot : ¬ j + c < (f a).length := by omega
        have hsub : j + c - c = j := by omega
        rw [if_neg hnot, ha, hsub, ih ht j, Nat.add_div_right j hc,
          Nat.add_mod_right j c]
        simp

/-- A positive-width entry always occupies at least one machine word. -/
theorem packedChunkCount_pos {width wordSize : Nat}
    (hword : 0 < wordSize) (hpos : 0 < width) :
    0 < packedChunkCount width wordSize := by
  unfold packedChunkCount
  by_cases h : width % wordSize = 0
  · rw [if_pos h]
    have hle : wordSize <= width := by
      by_cases hlt : width < wordSize
      · rw [Nat.mod_eq_of_lt hlt] at h
        omega
      · omega
    exact Nat.div_pos hle hword
  · rw [if_neg h]
    exact Nat.succ_pos _

/--
**The machine store's words, with no width hypothesis.** Machine word `i` is chunk
`i % c` of logical entry `i / c`, where `c` is the number of machine words one
entry occupies.

`packedMachineStoreWords_getElem?` is the `c = 1` special case. This form is what
the three over-wide interior columns need.
-/
theorem packedMachineStoreWords_getElem?_general
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hword : 0 < wordSize) (hpos : 0 < width) (i : Nat) :
    (table.machineStore hword).store.words[i]? =
      (table.store.words.toList[i / packedChunkCount width wordSize]?).bind
        (fun entryWord =>
          packedWordSlice entryWord
            (packedChunkCount entryWord.length wordSize) wordSize
            (i % packedChunkCount width wordSize)) := by
  have hc : 0 < packedChunkCount width wordSize := packedChunkCount_pos hword hpos
  have huniform :
      forall {w : List Bool}, List.Mem w table.store.words.toList ->
        (chunkPayloadWords wordSize w).length =
          packedChunkCount width wordSize := by
    intro w hmem
    rcases List.getElem?_of_mem hmem with ⟨j, hj⟩
    have hw : w.length = width :=
      table.word_length_of_get? (by simpa [Array.getElem?_toList] using hj)
    rw [chunkPayloadWords_length_eq_div_add_indicator hword w, hw]
    rfl
  rw [← Array.getElem?_toList]
  show (table.store.words.toList.flatMap (chunkPayloadWords wordSize))[i]? = _
  rw [packedFlatMapUniform_getElem? (chunkPayloadWords wordSize) hc _ huniform i]
  congr 1
  funext w
  exact packedChunkedWords_getElem? hword w (i % packedChunkCount width wordSize)

end PackedCellProbe
end SuccinctFinal
end RMQ

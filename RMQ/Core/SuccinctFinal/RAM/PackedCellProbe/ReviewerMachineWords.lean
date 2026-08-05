import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCloseGeometry

/-!
# When a machine store is the table's own store

`DD-20260804-049` recorded that `FixedWidthNatTable.machineStore` chunks each
logical entry **separately**, so its words are not in general the uniform grid the
table already has, and no `packedWordSlice` statement describes them.

This module gives the exact condition under which it is: `0 < width` and
`width <= wordSize`. An entry that fits one machine word is chunked into exactly
that one word, so the flatMap is the identity and the machine store's word list is
the table's own.

That is the hypothesis the eight interior components will each have to discharge.
It is an `n`-only condition -- both widths are functions of the input size -- so it
belongs with `PackedSourceCounted` and `PackedInteriorReady` as a guard the
controller can consult, rather than as a fact about a particular shape.

## Why state the negative case at all

The obvious route for the interior -- treat each component as `packedWordSlice` of
its own payload at the machine width -- is unconditionally wrong. It happens to
hold whenever the entry width fits the machine word, which is the regime one
samples, and fails otherwise. Stating the hypothesis explicitly is what keeps the
eventual interior geometry from being a theorem that is true only where it was
tested.

## What this module does not establish

* No interior component discharges the hypothesis here. Each of the eight needs
  its own width comparison.
* Nothing here concerns cell probes.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian
open RMQ.SuccinctSpace

/-- A payload that fits one machine word is chunked into exactly that one word. -/
theorem packedChunkPayloadWords_singleton
    {width : Nat} (hwidth : 0 < width) (p : List Bool)
    (hpos : 0 < p.length) (hle : p.length <= width) :
    chunkPayloadWords width p = [p] := by
  have hlen : (chunkPayloadWords width p).length = 1 := by
    rw [chunkPayloadWords_length_eq_div_add_indicator hwidth p]
    by_cases heq : p.length = width
    · rw [heq]
      rw [Nat.div_self hwidth, Nat.mod_self]
      simp
    · have hlt : p.length < width := by omega
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
      have : p.length ≠ 0 := by omega
      simp [this]
  have hflat := flattenPayloadWords_chunkPayloadWords hwidth p
  rcases List.length_eq_one_iff.mp hlen with ⟨a, ha⟩
  rw [ha] at hflat ⊢
  congr 1
  simpa [flattenPayloadWords] using hflat

/--
**When an entry fits a machine word, the machine store is the table's own store.**

`FixedWidthNatTable.machineStore` chunks each logical entry separately, so this is
the exact condition under which its words form the same uniform grid the table
already has. Off this condition the two differ and no `packedWordSlice` statement
describes the machine store.
-/
theorem packedMachineStoreWords_eq_of_width_le
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hword : 0 < wordSize) (hpos : 0 < width) (hle : width <= wordSize) :
    (table.machineStore hword).store.words.toList =
      table.store.words.toList := by
  have huniform :
      forall {word : List Bool},
        List.Mem word table.store.words.toList -> word.length = width := by
    intro word hmem
    rcases List.getElem?_of_mem hmem with ⟨j, hj⟩
    exact table.word_length_of_get? (by simpa [Array.getElem?_toList] using hj)
  have hgen :
      forall ws : List (List Bool),
        (forall {w : List Bool}, List.Mem w ws -> w.length = width) ->
          ws.flatMap (chunkPayloadWords wordSize) = ws := by
    intro ws
    induction ws with
    | nil => intro _; rfl
    | cons a t ih =>
        intro hall
        have ha : a.length = width := hall List.mem_cons_self
        have ht : forall {w : List Bool}, List.Mem w t -> w.length = width := by
          intro w hw
          exact hall (List.mem_cons_of_mem a hw)
        rw [List.flatMap_cons,
          packedChunkPayloadWords_singleton hword a (by omega) (by omega),
          ih ht]
        rfl
  show (fixedWidthNatTableMachineWords table wordSize) = _
  unfold fixedWidthNatTableMachineWords
  exact hgen table.store.words.toList huniform

/-- Consequently the packed word slice describes it, at the table's own width. -/
theorem packedMachineStoreWords_getElem?
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hword : 0 < wordSize) (hpos : 0 < width) (hle : width <= wordSize)
    (i : Nat) :
    (table.machineStore hword).store.words[i]? =
      packedWordSlice table.payload entries.length width i := by
  rw [← Array.getElem?_toList,
    packedMachineStoreWords_eq_of_width_le table hword hpos hle,
    Array.getElem?_toList]
  exact packedFixedWidthTable_getElem? table i

end PackedCellProbe
end SuccinctFinal
end RMQ

import RMQ.Core.WordRAM.Packed.DensePacking
import RMQ.Core.WordRAM.E1FringeBridge

/-!
# Numeric decoding of a repacked bit span

The executable definitions here accept only numeric memory and numeric scalar
parameters. They preserve absence with `Option`, so a full all-ones raw cell
requires no `+1` tag. Their one/two-cell read plan is a functional specification;
primitive execution and instruction accounting are separate downstream proofs.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open SuccinctSpace

/-- Ordered physical addresses needed by a span no longer than one word. -/
def spanPlan (width position len : Nat) : List Nat :=
  if len = 0 then []
  else if position % width + len ≤ width then [position / width]
  else [position / width, position / width + 1]

/-- Scalar decoding reads a second physical cell only on a crossing. Masking
the second fragment before shifting avoids constructing a double-width word. -/
def decodeSpanNat (width position len : Nat) (memory : List Nat) : Option Nat :=
  if len = 0 then some 0
  else do
    let first ← memory[position / width]?
    if position % width + len ≤ width then
      some (first / 2 ^ (position % width) % 2 ^ len)
    else do
      let second ← memory[position / width + 1]?
      some (first / 2 ^ (position % width) +
        second % 2 ^ (len - (width - position % width)) *
          2 ^ (width - position % width))

/-- Recover one old cell from the counted, header-prefixed repacking. -/
def loadOldCellNat (headerCount width oldWidth oldCount : Nat)
    (memory : List Nat) (index : Nat) : Option Nat :=
  if index < oldCount then
    decodeSpanNat width (headerCount * width + index * oldWidth) oldWidth memory
  else none

theorem spanPlan_length_le (width position len : Nat) :
    (spanPlan width position len).length ≤ 2 := by
  unfold spanPlan
  split
  · simp
  · split <;> simp

@[simp] theorem spanPlan_zero (width position : Nat) : spanPlan width position 0 = [] := by
  simp [spanPlan]

@[simp] theorem decodeSpanNat_zero (width position : Nat) (memory : List Nat) :
    decodeSpanNat width position 0 memory = some 0 := by
  simp [decodeSpanNat]

private theorem bitsToNatLE_pair_slice (first second : List Bool)
    (width offset len : Nat) (hfirst : first.length = width) (hoff : offset ≤ width) :
    bitsToNatLE (((first ++ second).drop offset).take len) =
      if offset + len ≤ width then
        bitsToNatLE first / 2 ^ offset % 2 ^ len
      else bitsToNatLE first / 2 ^ offset +
        bitsToNatLE second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) := by
  rw [List.drop_append_of_le_length (by omega)]
  by_cases h : offset + len ≤ width
  · rw [if_pos h, List.take_append_of_le_length (by simp; omega)]
    rw [SuccinctClose.bitsToNatLE_take, SuccinctClose.bitsToNatLE_drop]
  · rw [if_neg h, List.take_append]
    have htake : (first.drop offset).take len = first.drop offset :=
      List.take_of_length_le (by simp; omega)
    rw [htake, SuccinctClose.bitsToNatLE_append, SuccinctClose.bitsToNatLE_drop,
      SuccinctClose.bitsToNatLE_take]
    simp only [List.length_drop, hfirst]
    rw [Nat.mul_comm]

private theorem cellAt_uniform (cells : List (List Bool)) (width index : Nat)
    (hwidth : ∀ cell ∈ cells, cell.length = width) :
    cellAt cells.flatten width index = (cells[index]?).getD [] :=
  uniform_flatten_slice cells width hwidth index

/-- Universal numeric refinement for a valid span, including a zero-length
span at the end of memory. The cells in the premise are proof-side bit lists. -/
theorem decodeSpanNat_uniform (cells : List (List Bool)) (width position len : Nat)
    (hw : 0 < width) (hwidth : ∀ cell ∈ cells, cell.length = width)
    (hlen : len ≤ width) (hbound : position + len ≤ cells.length * width) :
    decodeSpanNat width position len (cells.map bitsToNatLE) =
      some (bitsToNatLE ((cells.flatten.drop position).take len)) := by
  by_cases hz : len = 0
  · simp [hz, decodeSpanNat, bitsToNatLE]
  have hmod := Nat.mod_lt position hw
  have hdiv : position / width * width + position % width = position := by
    have := Nat.mod_add_div position width
    rw [Nat.mul_comm width] at this
    omega
  have hfirstIndex : position / width < cells.length := by
    by_cases hi : position / width < cells.length
    · exact hi
    · have hm := Nat.mul_le_mul_right width (Nat.le_of_not_gt hi)
      omega
  let first := cells[position / width]
  have hfirst : cells[position / width]? = some first := by
    exact List.getElem?_eq_getElem hfirstIndex
  have hfirstWidth : first.length = width :=
    hwidth first (List.getElem_mem hfirstIndex)
  have hslice := span_from_two_cells cells.flatten width position len hw hlen
  rw [cellAt_uniform cells width _ hwidth, cellAt_uniform cells width _ hwidth,
    hfirst, Option.getD_some] at hslice
  rw [hslice, bitsToNatLE_pair_slice first _ width _ len hfirstWidth (by omega)]
  unfold decodeSpanNat
  rw [if_neg hz]
  simp only [List.getElem?_map, hfirst, Option.map_some, bind, Option.bind]
  by_cases hc : position % width + len ≤ width
  · rw [if_pos hc, if_pos hc]
  · have hsecondIndex : position / width + 1 < cells.length := by
      by_cases hi : position / width + 1 < cells.length
      · exact hi
      · have hm := Nat.mul_le_mul_right width (Nat.le_of_not_gt hi)
        rw [Nat.add_mul, Nat.one_mul] at hm
        omega
    have hsecond : cells[position / width + 1]? = some cells[position / width + 1] := by
      exact List.getElem?_eq_getElem hsecondIndex
    rw [if_neg hc, if_neg hc]
    simp only [hsecond, Option.map_some, Option.getD_some]

/-- Prefixing full numeric words shifts the physical addresses and preserves
the decoded result, including missing reads. No interpretation of headers is
needed: the span begins after them. -/
theorem decodeSpanNat_append_shift (headers memory : List Nat)
    (width position len : Nat) (hw : 0 < width) :
    decodeSpanNat width (headers.length * width + position) len (headers ++ memory) =
      decodeSpanNat width position len memory := by
  have hdiv : (headers.length * width + position) / width =
      headers.length + position / width := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.add_comm]
  have hmod : (headers.length * width + position) % width = position % width := by
    simp [Nat.add_mod]
  have hfirst : (headers ++ memory)[headers.length + position / width]? =
      memory[position / width]? := by
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp
  have hsecond : (headers ++ memory)[headers.length + position / width + 1]? =
      memory[position / width + 1]? := by
    rw [List.getElem?_append_right (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))]
    simp [Nat.add_assoc]
  simp only [decodeSpanNat, hdiv, hmod, hfirst, hsecond]

private theorem densePad_slice (bits : List Bool) (width position len : Nat)
    (hbound : position + len ≤ bits.length) :
    ((densePad width bits).drop position).take len = (bits.drop position).take len := by
  unfold densePad
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-- Exact old-cell recovery for the same allocation as
`repackWords_capacity_le`, at every valid and invalid old-cell index. The
statement is stronger than requiring bounded headers: their values are never
examined by this loader; their separate width theorem bounds the allocation. -/
theorem loadOldCellNat_repacked (headers : List Nat) (width oldWidth : Nat)
    (old : List (List Bool)) (hOld : ∀ cell ∈ old, cell.length = oldWidth)
    (hOldPos : 0 < oldWidth) (hOldLe : oldWidth ≤ width) (index : Nat) :
    loadOldCellNat headers.length width oldWidth old.length
      (repackWords headers width old) index = (old[index]?).map bitsToNatLE := by
  have hw : 0 < width := by omega
  unfold loadOldCellNat
  by_cases hi : index < old.length
  · rw [if_pos hi, repackWords, decodeSpanNat_append_shift _ _ _ _ _ hw]
    have hspan : index * oldWidth + oldWidth ≤ old.flatten.length := by
      rw [uniform_flatten_length old oldWidth hOld]
      have hm := Nat.mul_le_mul_right oldWidth (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at hm
    have hcover : old.flatten.length ≤ (denseCells width old.flatten).length * width := by
      rw [denseCells_length]
      exact GenericSelect.selectCeilDiv_mul_ge_of_pos hw
    have hdecode := decodeSpanNat_uniform (denseCells width old.flatten)
      width (index * oldWidth) oldWidth hw
      (fun cell hc => denseCells_cell_length width old.flatten hw hc)
      hOldLe (Nat.le_trans hspan hcover)
    change decodeSpanNat width (index * oldWidth) oldWidth
      ((denseCells width old.flatten).map bitsToNatLE) = _
    rw [hdecode, denseCells_flatten width old.flatten hw,
      densePad_slice _ _ _ _ hspan, uniform_flatten_slice old oldWidth hOld index]
    simp only [List.getElem?_eq_getElem, hi, Option.getD_some,
      Option.map_some]
  · rw [if_neg hi, List.getElem?_eq_none (Nat.le_of_not_gt hi)]
    rfl

/-- A successful decode requires exactly the physical cells named by the
geometric plan. This statement concerns the functional read layer, not a
primitive execution trace; a failed first read short-circuits evaluation. -/
theorem decodeSpanNat_isSome_iff (width position len : Nat) (memory : List Nat) :
    (decodeSpanNat width position len memory).isSome ↔
      ∀ address ∈ spanPlan width position len, (memory[address]?).isSome := by
  by_cases hz : len = 0
  · simp [decodeSpanNat, spanPlan, hz]
  by_cases hc : position % width + len ≤ width
  · simp only [decodeSpanNat, spanPlan, if_neg hz, if_pos hc,
      List.mem_singleton, forall_eq, bind, Option.bind]
    cases memory[position / width]? <;> simp
  · simp only [decodeSpanNat, spanPlan, if_neg hz, if_neg hc,
      List.mem_cons, forall_eq_or_imp, bind, Option.bind]
    cases memory[position / width]? <;> cases memory[position / width + 1]? <;> simp

/-- Successful read backing retains each occurrence's position, including
both consecutive cells of a crossing. -/
theorem decodeSpanNat_read_backing (width position len : Nat) (memory : List Nat)
    (hsuccess : (decodeSpanNat width position len memory).isSome)
    (occurrence : Nat) (hocc : occurrence < (spanPlan width position len).length) :
    ∃ word, memory[(spanPlan width position len)[occurrence]]? = some word := by
  apply Option.isSome_iff_exists.mp
  exact (decodeSpanNat_isSome_iff width position len memory).mp hsuccess
    _ (List.getElem_mem hocc)

/-- A missing required positional reply prevents successful decoding. -/
theorem decodeSpanNat_none_of_missing (width position len : Nat) (memory : List Nat)
    (occurrence : Nat) (hocc : occurrence < (spanPlan width position len).length)
    (hmissing : memory[(spanPlan width position len)[occurrence]]? = none) :
    decodeSpanNat width position len memory = none := by
  apply Option.not_isSome_iff_eq_none.mp
  intro hsuccess
  obtain ⟨word, hword⟩ := decodeSpanNat_read_backing width position len memory
    hsuccess occurrence hocc
  rw [hmissing] at hword
  cases hword

/-- Changing numeric memory outside the planned addresses cannot affect the
returned value or its absence. The premise compares replies positionally. -/
theorem decodeSpanNat_congr (width position len : Nat) (memory other : List Nat)
    (hagrees : ∀ occurrence (hocc : occurrence < (spanPlan width position len).length),
      memory[(spanPlan width position len)[occurrence]]? =
        other[(spanPlan width position len)[occurrence]]?) :
    decodeSpanNat width position len memory = decodeSpanNat width position len other := by
  by_cases hz : len = 0
  · simp [hz]
  by_cases hc : position % width + len ≤ width
  · have hf : memory[position / width]? = other[position / width]? := by
      have h := hagrees 0 (by simp [spanPlan, hz, hc])
      simpa [spanPlan, hz, hc] using h
    simp only [decodeSpanNat, if_neg hz, if_pos hc, hf]
  · have hf : memory[position / width]? = other[position / width]? := by
      have h := hagrees 0 (by simp [spanPlan, hz, hc])
      simpa [spanPlan, hz, hc] using h
    have hs : memory[position / width + 1]? = other[position / width + 1]? := by
      have h := hagrees 1 (by simp [spanPlan, hz, hc])
      simpa [spanPlan, hz, hc] using h
    simp only [decodeSpanNat, if_neg hz, if_neg hc, hf, hs]

@[simp] theorem loadOldCellNat_absent (headerCount width oldWidth oldCount : Nat)
    (memory : List Nat) (index : Nat) (hi : oldCount ≤ index) :
    loadOldCellNat headerCount width oldWidth oldCount memory index = none := by
  simp [loadOldCellNat, Nat.not_lt.mpr hi]

/-! ## Kernel-checked direct consumers

The expected numerals below are explicit bit-slice values, and every consumer
elaborates the new numeric decoder or the exact repacked allocation. These are
boundary witnesses, not a universal machine-instruction or mutation campaign.
-/

example : spanPlan 4 1 2 = [0] ∧ decodeSpanNat 4 1 2 [13] = some 2 := by decide

example : spanPlan 4 3 3 = [0, 1] ∧ decodeSpanNat 4 3 3 [13, 3] = some 7 := by decide

example : loadOldCellNat 2 4 3 3
    (repackWords [5, 2] 4
      [[true, false, true], [true, true, true], [false, true, true]]) 2 = some 6 := by
  decide

example : spanPlan 4 8 0 = [] ∧ decodeSpanNat 4 8 0 [1, 2] = some 0 := by decide

example : decodeSpanNat 4 3 3 [13] = none := by decide

example : decodeSpanNat 4 0 1 [] = none := by decide

example : loadOldCellNat 2 4 3 3 [5, 2, 13, 11, 1] 3 = none := by decide

example : decodeSpanNat 4 0 4 [15] = some 15 := by decide

example : decodeSpanNat 4 3 3 [5, 3] = some 6 ∧
    decodeSpanNat 4 3 3 [13, 2] = some 5 := by decide

/-- The returned numeral is sensitive to each physical reply in this
crossing. This pins value dependency rather than a surrounding trace record. -/
theorem crossing_value_dependency :
    decodeSpanNat 4 3 3 [13, 3] ≠ decodeSpanNat 4 3 3 [5, 3] ∧
    decodeSpanNat 4 3 3 [13, 3] ≠ decodeSpanNat 4 3 3 [13, 2] := by
  decide

/-- The zero-span result is independent even of absent physical memory. -/
example : decodeSpanNat 4 0 0 [] = some 0 := by decide

/-- An independently stated consumer pins the full original-cell option,
including the returned numeral, against the concrete repacking constructor. -/
theorem repackedLoader_expectedType (headers : List Nat) (width oldWidth : Nat)
    (old : List (List Bool)) (hOld : ∀ cell ∈ old, cell.length = oldWidth)
    (hOldPos : 0 < oldWidth) (hOldLe : oldWidth ≤ width) :
    ∀ index, loadOldCellNat headers.length width oldWidth old.length
      (headers ++ denseWords width old.flatten) index = (old[index]?).map bitsToNatLE := by
  intro index
  exact loadOldCellNat_repacked headers width oldWidth old hOld hOldPos hOldLe index

end RMQ.SuccinctFinal.PackedWordRAM

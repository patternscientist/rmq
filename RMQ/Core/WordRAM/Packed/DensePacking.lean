import RMQ.Core.GenericSelect.DenseEntryTable

/-!
# Dense packing at an independently chosen physical width

The number of cells is recomputed from the bit length. Consequently increasing
the physical width changes only final padding, not the leading payload term.
These are representation lemmas. Actual load execution is proved separately.

The chunk-flatten induction generalizes the private RC6 lemma in
PackedCellProbe.ReviewerCrossing; it is public here for arbitrary positive widths.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open SuccinctSpace

def denseCount (width : Nat) (bits : List Bool) : Nat :=
  GenericSelect.selectCeilDiv bits.length width

def densePad (width : Nat) (bits : List Bool) : List Bool :=
  bits ++ List.replicate (denseCount width bits * width - bits.length) false

def cellAt (bits : List Bool) (width index : Nat) : List Bool :=
  (bits.drop (index * width)).take width

def denseCells (width : Nat) (bits : List Bool) : List (List Bool) :=
  (List.range (denseCount width bits)).map (cellAt (densePad width bits) width)

def denseWords (width : Nat) (bits : List Bool) : List Nat :=
  (denseCells width bits).map bitsToNatLE

theorem densePad_length (width : Nat) (bits : List Bool) (hw : 0 < width) :
    (densePad width bits).length = denseCount width bits * width := by
  have hcover : bits.length ≤ denseCount width bits * width :=
    GenericSelect.selectCeilDiv_mul_ge_of_pos hw
  simp only [densePad, List.length_append, List.length_replicate]
  omega

@[simp] theorem denseCells_length (width : Nat) (bits : List Bool) :
    (denseCells width bits).length = denseCount width bits := by
  simp [denseCells]

@[simp] theorem denseWords_length (width : Nat) (bits : List Bool) :
    (denseWords width bits).length = denseCount width bits := by
  simp [denseWords]

theorem denseCells_cell_length (width : Nat) (bits : List Bool)
    (hw : 0 < width) {cell : List Bool} (hcell : cell ∈ denseCells width bits) :
    cell.length = width := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcell
  have hi' : i < denseCount width bits := List.mem_range.mp hi
  have hmul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi')
  have hpad := densePad_length width bits hw
  simp only [cellAt, List.length_take, List.length_drop, hpad]
  rw [Nat.succ_mul] at hmul
  omega

theorem chunks_flatten (width : Nat) :
    ∀ (count : Nat) (bits : List Bool), bits.length = count * width →
      ((List.range count).map (cellAt bits width)).flatten = bits := by
  intro count
  induction count with
  | zero =>
      intro bits hbits
      simp only [Nat.zero_mul] at hbits
      simp [List.eq_nil_of_length_eq_zero hbits]
  | succ count ih =>
      intro bits hbits
      have hdrop : (bits.drop width).length = count * width := by
        rw [List.length_drop, hbits, Nat.succ_mul]
        omega
      have htail :
          ((List.range count).map fun i => cellAt bits width (i + 1)) =
            ((List.range count).map (cellAt (bits.drop width) width)) := by
        apply List.map_congr_left
        intro i _
        simp only [cellAt, List.drop_drop, Nat.add_mul, Nat.one_mul]
        rw [Nat.add_comm]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.flatten_cons, Function.comp_def]
      rw [htail, ih (bits.drop width) hdrop]
      simp [cellAt]

theorem denseCells_flatten (width : Nat) (bits : List Bool) (hw : 0 < width) :
    (denseCells width bits).flatten = densePad width bits :=
  chunks_flatten width _ _ (densePad_length width bits hw)

theorem denseCells_recovers (width : Nat) (bits : List Bool) (hw : 0 < width) :
    (denseCells width bits).flatten.take bits.length = bits := by
  rw [denseCells_flatten width bits hw]
  simp [densePad]

theorem denseWords_capacity_le (width : Nat) (bits : List Bool) :
    (denseWords width bits).length * width ≤ bits.length + width := by
  rw [denseWords_length]
  exact GenericSelect.selectCeilDiv_mul_le_add _ _

theorem denseWords_word_lt (width : Nat) (bits : List Bool) (hw : 0 < width)
    {word : Nat} (hword : word ∈ denseWords width bits) : word < 2 ^ width := by
  obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hword
  have hlen := denseCells_cell_length width bits hw hcell
  simpa [hlen] using GenericSelect.bitsToNatLE_lt_two_pow_length cell

theorem uniform_flatten_length (cells : List (List Bool)) (width : Nat)
    (hwidth : ∀ cell ∈ cells, cell.length = width) :
    cells.flatten.length = cells.length * width := by
  induction cells with
  | nil => simp
  | cons head tail ih =>
      have hh := hwidth head (by simp)
      have ht : ∀ cell ∈ tail, cell.length = width := by
        intro cell hc
        exact hwidth cell (by simp [hc])
      simp [List.flatten_cons, hh, ih ht, Nat.succ_mul, Nat.add_comm]

theorem uniform_flatten_slice (cells : List (List Bool)) (width : Nat)
    (hwidth : ∀ cell ∈ cells, cell.length = width) (index : Nat) :
    (cells.flatten.drop (index * width)).take width = (cells[index]?).getD [] := by
  induction cells generalizing index with
  | nil => simp
  | cons head tail ih =>
      have hh := hwidth head (by simp)
      have ht : ∀ cell ∈ tail, cell.length = width := by
        intro cell hc
        exact hwidth cell (by simp [hc])
      cases index with
      | zero =>
          simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons,
            List.getElem?_cons_zero, Option.getD_some]
          rw [← hh, List.take_left]
      | succ index =>
          simp only [List.flatten_cons, List.getElem?_cons_succ]
          rw [Nat.succ_mul, Nat.add_comm (index * width) width,
            ← List.drop_drop, ← hh, List.drop_left, hh]
          exact ih ht index

theorem cellAt_pair (bits : List Bool) (width index : Nat) :
    cellAt bits width index ++ cellAt bits width (index + 1) =
      (bits.drop (index * width)).take (width + width) := by
  unfold cellAt
  rw [List.take_add]
  congr 1
  rw [List.drop_drop]
  congr 1
  rw [Nat.add_mul, Nat.one_mul]

theorem span_from_two_cells (bits : List Bool) (width position len : Nat)
    (hw : 0 < width) (hlen : len ≤ width) :
    (bits.drop position).take len =
      ((cellAt bits width (position / width) ++
        cellAt bits width (position / width + 1)).drop (position % width)).take len := by
  have hmod := Nat.mod_lt position hw
  have hidx : position / width * width + position % width = position := by
    have := Nat.mod_add_div position width
    rw [Nat.mul_comm width] at this
    omega
  have hmin : min len (width + width - position % width) = len := by omega
  rw [cellAt_pair, List.drop_take, List.take_take, List.drop_drop, hidx, hmin]

/-- Fixed metadata occupies full words. The serialized body is re-chunked,
including old headers and padding; both padding layers remain in the bound. -/
def repackWords (headers : List Nat) (width : Nat) (old : List (List Bool)) : List Nat :=
  headers ++ denseWords width old.flatten

theorem repackWords_capacity_le (headers : List Nat) (width oldWidth : Nat)
    (old : List (List Bool)) (hOld : ∀ cell ∈ old, cell.length = oldWidth) :
    (repackWords headers width old).length * width ≤
      old.length * oldWidth + (headers.length + 1) * width := by
  have hbody := denseWords_capacity_le width old.flatten
  rw [uniform_flatten_length old oldWidth hOld] at hbody
  simp only [repackWords, List.length_append, Nat.add_mul, Nat.one_mul]
  omega

theorem repackWords_word_lt (headers : List Nat) (width : Nat)
    (old : List (List Bool)) (hw : 0 < width)
    (hHeaders : ∀ word ∈ headers, word < 2 ^ width)
    {word : Nat} (hword : word ∈ repackWords headers width old) :
    word < 2 ^ width := by
  rcases List.mem_append.mp hword with h | h
  · exact hHeaders word h
  · exact denseWords_word_lt width old.flatten hw h

end RMQ.SuccinctFinal.PackedWordRAM

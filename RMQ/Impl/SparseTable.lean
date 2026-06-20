import RMQ.Core.Backend

/-!
# Sparse-table RMQ backend

Sparse-table cells store leftmost-argmin indices for power-of-two blocks. A
valid query combines the two overlapping blocks selected by `Nat.log2`.
-/

namespace RMQ.SparseTable

/-- Power-of-two block length for sparse-table level `k`. -/
def blockLen (k : Nat) : Nat :=
  2 ^ k

/-- Option-level argmin combination. `none` represents an out-of-bounds block. -/
abbrev combineIndex := RMQ.combineIndex

/--
The level-`k` sparse-table argmin cell starting at `start`.

Level zero is the singleton index. A successor level combines two adjacent
half-size cells, preserving leftmost ties through `betterIndex`.
-/
def blockArgMin (xs : List Int) : Nat -> Nat -> Option Nat
  | 0, start =>
      if _h : start < xs.length then some start else none
  | k + 1, start =>
      combineIndex xs (blockArgMin xs k start) (blockArgMin xs k (start + blockLen k))

/-- A materialized sparse-table row for one power-of-two level. -/
def sparseRow (xs : List Int) (k : Nat) : List (Option Nat) :=
  List.ofFn (fun i : Fin xs.length => blockArgMin xs k i.1)

/-- Flatten a materialized row lookup. Missing row entries and cells both give `none`. -/
def rowCell (row : List (Option Nat)) (i : Nat) : Option Nat :=
  match row[i]? with
  | some cell => cell
  | none => none

/--
Materialized sparse table.

The row count is deliberately `xs.length + 1`: this keeps the standalone
library independent of heavier logarithm monotonicity lemmas while still
covering every query level because `Nat.log2 len <= len <= xs.length`.
-/
def buildSparseTable (xs : List Int) : List (List (Option Nat)) :=
  List.ofFn (fun k : Fin (xs.length + 1) => sparseRow xs k.1)

/-- Fetch a materialized table row, returning an empty row if the level is absent. -/
def tableRow (table : List (List (Option Nat))) (k : Nat) : List (Option Nat) :=
  match table[k]? with
  | some row => row
  | none => []

/-- Query a supplied sparse table with the standard overlapping two-block schedule. -/
def queryFromTable
    (xs : List Int) (table : List (List (Option Nat))) (left right : Nat) :
    Option Nat :=
  if _h : RMQ.ValidRange xs left right then
    let len := right - left
    let k := Nat.log2 len
    let p := blockLen k
    let row := tableRow table k
    combineIndex xs (rowCell row left) (rowCell row (right - p))
  else
    none

/-- Sparse-table RMQ over a freshly built table. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  queryFromTable xs (buildSparseTable xs) left right

private theorem get?_some_of_lt (xs : List Int) {i : Nat} (h : i < xs.length) :
    xs[i]? = some (xs[i]'h) := by
  simp

private theorem betterIndex_self (xs : List Int) (i : Nat) :
    RMQ.betterIndex xs i i = i := by
  unfold RMQ.betterIndex
  cases xs[i]? <;> simp

private theorem leftmost_singleton (xs : List Int) {i : Nat} (h : i < xs.length) :
    RMQ.LeftmostArgMin xs i (i + 1) i := by
  refine ⟨by omega, by omega, by omega, by omega, xs[i]'h,
    get?_some_of_lt xs h, ?_, ?_⟩
  · intro j w hij hj hget
    have hji : j = i := by omega
    subst j
    have hw : w = xs[i]'h := by
      exact (Option.some.inj (by simpa [get?_some_of_lt xs h] using hget)).symm
    simp [hw]
  · intro j _ hij hj _
    omega

/-- Sparse-table cells are exact leftmost argmins for their power-of-two block. -/
theorem blockArgMin_leftmost_exists
    (xs : List Int) (k start : Nat)
    (hbound : start + blockLen k <= xs.length) :
    exists idx, blockArgMin xs k start = some idx /\
      RMQ.LeftmostArgMin xs start (start + blockLen k) idx := by
  induction k generalizing start with
  | zero =>
      have hlt : start < xs.length := by
        unfold blockLen at hbound
        omega
      refine ⟨start, ?_, leftmost_singleton xs hlt⟩
      simp [blockArgMin, hlt]
  | succ k ih =>
      have hsplit : blockLen (k + 1) = blockLen k + blockLen k := by
        unfold blockLen
        rw [Nat.pow_succ]
        omega
      have hleft : start + blockLen k <= xs.length := by
        omega
      have hright : start + blockLen k + blockLen k <= xs.length := by
        have hrewrite : start + blockLen k + blockLen k = start + blockLen (k + 1) := by
          rw [hsplit]
          omega
        rw [hrewrite]
        exact hbound
      rcases ih start hleft with ⟨li, hlcell, hlarg⟩
      rcases ih (start + blockLen k) hright with ⟨ri, hrcell, hrarg⟩
      refine ⟨RMQ.betterIndex xs li ri, ?_, ?_⟩
      · simp [blockArgMin, hlcell, hrcell, combineIndex, RMQ.combineIndex]
      · have hright_end : start + blockLen k + blockLen k = start + blockLen (k + 1) := by
          rw [hsplit]
          omega
        have hrarg' :
            RMQ.LeftmostArgMin xs (start + blockLen k) (start + blockLen (k + 1)) ri := by
          simpa [Nat.add_assoc, hright_end] using hrarg
        have hcover :
            forall t, start <= t -> t < start + blockLen (k + 1) ->
              t < start + blockLen k \/ start + blockLen k <= t := by
          intro t ht_left ht_right
          by_cases ht : t < start + blockLen k
          · exact Or.inl ht
          · exact Or.inr (by omega)
        exact RMQ.combineLeftmost hlarg hrarg' (by omega) (by omega) hcover

private theorem sparseRow_get?_eq_blockArgMin
    (xs : List Int) (k start : Nat) (h : start < xs.length) :
    (sparseRow xs k)[start]? = some (blockArgMin xs k start) := by
  have hrow : start < (sparseRow xs k).length := by
    simp [sparseRow, h]
  rw [List.getElem?_eq_getElem hrow]
  unfold sparseRow
  simp

theorem sparseRow_cell_eq_blockArgMin
    (xs : List Int) (k start : Nat) (h : start < xs.length) :
    rowCell (sparseRow xs k) start = blockArgMin xs k start := by
  unfold rowCell
  simp [sparseRow_get?_eq_blockArgMin xs k start h]

theorem tableRow_build_eq_sparseRow
    (xs : List Int) (k : Nat) (hk : k <= xs.length) :
    tableRow (buildSparseTable xs) k = sparseRow xs k := by
  have htab : k < (buildSparseTable xs).length := by
    simp [buildSparseTable]
    omega
  unfold tableRow
  rw [List.getElem?_eq_getElem htab]
  unfold buildSparseTable
  rw [List.getElem_ofFn]

private theorem log2_block_bounds {len : Nat} (hlen : 0 < len) :
    blockLen (Nat.log2 len) <= len /\
      len <= blockLen (Nat.log2 len) + blockLen (Nat.log2 len) := by
  have hne : Not (len = 0) := Nat.ne_of_gt hlen
  have hle : 2 ^ Nat.log2 len <= len := Nat.log2_self_le hne
  have hlt : len < 2 ^ (Nat.log2 len + 1) := Nat.lt_log2_self
  constructor
  · simpa [blockLen] using hle
  · unfold blockLen
    have hpow : 2 ^ (Nat.log2 len + 1) = 2 ^ Nat.log2 len + 2 ^ Nat.log2 len := by
      rw [Nat.pow_succ]
      omega
    omega

theorem query_valid_exact
    (xs : List Int) (left right : Nat) (hValid : RMQ.ValidRange xs left right) :
    exists idx, query xs left right = some idx /\
      RMQ.LeftmostArgMin xs left right idx := by
  unfold query queryFromTable
  have hif : left < right /\ right <= xs.length := hValid
  simp [RMQ.ValidRange, hif]
  let len := right - left
  let k := Nat.log2 len
  let p := blockLen k
  have hlen_pos : 0 < len := by
    unfold len
    omega
  have hp_bounds := log2_block_bounds hlen_pos
  have hp_le_len : p <= len := by
    simpa [p, k] using hp_bounds.1
  have hlen_le_twop : len <= p + p := by
    simpa [p, k] using hp_bounds.2
  have hk_le_len : k <= len := by
    unfold k
    exact Nat.log2_le_self len
  have hk_le_table : k <= xs.length := by
    unfold len at hk_le_len
    omega
  have hp_pos : 0 < p := by
    unfold p blockLen
    exact Nat.pow_pos (by omega)
  have hleft_bound : left + p <= xs.length := by
    unfold len at hp_le_len
    omega
  have hright_bound : right - p + p <= xs.length := by
    unfold len at hp_le_len
    omega
  rcases blockArgMin_leftmost_exists xs k left hleft_bound with ⟨li, hlcell, hlarg⟩
  rcases blockArgMin_leftmost_exists xs k (right - p) hright_bound with ⟨ri, hrcell, hrarg⟩
  refine ⟨RMQ.betterIndex xs li ri, ?_, ?_⟩
  · have hleft_idx : left < xs.length := by omega
    have hright_idx : right - p < xs.length := by omega
    have hlrow := sparseRow_cell_eq_blockArgMin xs k left hleft_idx
    have hrrow := sparseRow_cell_eq_blockArgMin xs k (right - p) hright_idx
    have htable := tableRow_build_eq_sparseRow xs k hk_le_table
    change combineIndex xs (rowCell (tableRow (buildSparseTable xs) k) left)
        (rowCell (tableRow (buildSparseTable xs) k) (right - p)) =
      some (RMQ.betterIndex xs li ri)
    simp [htable, hlrow, hrrow, hlcell, hrcell, combineIndex, RMQ.combineIndex]
  · have hA_sub : left + p <= right := by
      unfold len at hp_le_len
      omega
    have hB_sub : left <= right - p := by
      unfold len at hp_le_len
      omega
    have hcover : forall t, left <= t -> t < right -> t < left + p \/ right - p <= t := by
      intro t hleft_t hright_t
      by_cases ht : t < left + p
      · exact Or.inl ht
      · have hge : left + p <= t := by omega
        have hright_le : right <= t + p := by
          unfold len at hlen_le_twop
          omega
        exact Or.inr (by omega)
    have hright_end : right - p + p = right := by
      unfold len at hp_le_len
      omega
    have hrarg' : RMQ.LeftmostArgMin xs (right - p) right ri := by
      simpa [p, hright_end] using hrarg
    exact RMQ.combineLeftmost hlarg hrarg' hA_sub hB_sub hcover

theorem query_sound {xs : List Int} {left right idx : Nat}
    (hres : query xs left right = some idx) :
    RMQ.LeftmostArgMin xs left right idx := by
  by_cases hValid : RMQ.ValidRange xs left right
  · rcases query_valid_exact xs left right hValid with ⟨idx', hres', harg'⟩
    have hidx : idx = idx' := by
      have hsome : some idx = some idx' := by
        rw [<- hres, hres']
      exact Option.some.inj hsome
    simpa [hidx] using harg'
  · unfold query queryFromTable at hres
    simp [hValid] at hres

theorem query_complete {xs : List Int} {left right idx : Nat}
    (harg : RMQ.LeftmostArgMin xs left right idx) :
    query xs left right = some idx := by
  have hValid : RMQ.ValidRange xs left right := RMQ.LeftmostArgMin.valid harg
  rcases query_valid_exact xs left right hValid with ⟨idx', hres', harg'⟩
  have hidx : idx' = idx :=
    RMQ.leftmostArgMin_unique xs left right idx' idx harg' harg
  simpa [hidx] using hres'

theorem invalid_none {xs : List Int} {left right : Nat}
    (hbad : Not (RMQ.ValidRange xs left right)) :
    query xs left right = none := by
  unfold query queryFromTable
  simp [hbad]

/-- Sparse table as an explicit `RMQBackend`. -/
def backend (xs : List Int) : RMQ.RMQBackend xs where
  State := List (List (Option Nat))
  build := buildSparseTable xs
  query := fun table => queryFromTable xs table
  sound := by
    intro left right idx hres
    have hquery : query xs left right = some idx := hres
    exact query_sound hquery
  complete := by
    intro left right idx harg
    have hquery := query_complete harg
    exact hquery
  invalid_none := by
    intro left right hbad
    exact invalid_none hbad

end RMQ.SparseTable

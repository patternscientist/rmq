import RMQ.Core.Cost
import RMQ.Impl.SparseTable

/-!
# Costed sparse-table RMQ

This module instruments the existing sparse-table implementation with the
lightweight `Costed` carrier. The cost model is deliberately simple and local:

* `blockArgMinCost k` charges one unit for a level-zero cell, and one unit for
  each combine at successor levels.
* building a row charges the cost of materializing each cell in that row.
* querying a supplied table charges one row lookup, two cell lookups, and one
  combine for valid ranges, or one failed validity check for invalid ranges.

The erasure theorems connect these costed kernels back to the existing
value-correct sparse-table functions.
-/

namespace RMQ.SparseTable

/-- Cost of computing one sparse-table cell at level `k`. -/
def blockArgMinCost : Nat -> Nat
  | 0 => 1
  | k + 1 => blockArgMinCost k + blockArgMinCost k + 1

/-- Costed version of `blockArgMin`. -/
def blockArgMinCosted
    (xs : List Int) : Nat -> Nat -> Costed (Option Nat)
  | 0, start => Costed.tickValue 1 (blockArgMin xs 0 start)
  | k + 1, start =>
      Costed.bind (blockArgMinCosted xs k start) fun leftCell =>
        Costed.bind (blockArgMinCosted xs k (start + blockLen k))
          fun rightCell =>
            Costed.tickValue 1 (combineIndex xs leftCell rightCell)

@[simp] theorem blockArgMinCosted_value
    (xs : List Int) (k start : Nat) :
    (blockArgMinCosted xs k start).value = blockArgMin xs k start := by
  induction k generalizing start with
  | zero =>
      simp [blockArgMinCosted, blockArgMin]
  | succ k ih =>
      simp [blockArgMinCosted, blockArgMin, ih]

@[simp] theorem blockArgMinCosted_erase
    (xs : List Int) (k start : Nat) :
    Costed.erase (blockArgMinCosted xs k start) =
      blockArgMin xs k start := by
  exact blockArgMinCosted_value xs k start

theorem blockArgMinCosted_cost
    (xs : List Int) (k start : Nat) :
    (blockArgMinCosted xs k start).cost = blockArgMinCost k := by
  induction k generalizing start with
  | zero =>
      simp [blockArgMinCosted, blockArgMinCost]
  | succ k ih =>
      simp [blockArgMinCosted, blockArgMinCost, ih]
      omega

/-- Cost of materializing one sparse-table row. -/
def sparseRowBuildCost (xs : List Int) (k : Nat) : Nat :=
  xs.length * blockArgMinCost k

/-- Costed materialization of one sparse-table row. -/
def sparseRowCosted (xs : List Int) (k : Nat) :
    Costed (List (Option Nat)) :=
  Costed.tickValue (sparseRowBuildCost xs k) (sparseRow xs k)

@[simp] theorem sparseRowCosted_value
    (xs : List Int) (k : Nat) :
    (sparseRowCosted xs k).value = sparseRow xs k := by
  rfl

@[simp] theorem sparseRowCosted_erase
    (xs : List Int) (k : Nat) :
    Costed.erase (sparseRowCosted xs k) = sparseRow xs k := by
  rfl

theorem sparseRowCosted_cost
    (xs : List Int) (k : Nat) :
    (sparseRowCosted xs k).cost = sparseRowBuildCost xs k := by
  rfl

/-- Cost of materializing the full sparse table used by this implementation. -/
def buildSparseTableCost (xs : List Int) : Nat :=
  ((List.finRange (xs.length + 1)).map fun k =>
    sparseRowBuildCost xs k.val).sum

/-- Costed materialization of the full sparse table. -/
def buildSparseTableCosted (xs : List Int) :
    Costed (List (List (Option Nat))) :=
  Costed.tickValue (buildSparseTableCost xs) (buildSparseTable xs)

@[simp] theorem buildSparseTableCosted_value (xs : List Int) :
    (buildSparseTableCosted xs).value = buildSparseTable xs := by
  rfl

@[simp] theorem buildSparseTableCosted_erase (xs : List Int) :
    Costed.erase (buildSparseTableCosted xs) = buildSparseTable xs := by
  rfl

theorem buildSparseTableCosted_cost (xs : List Int) :
    (buildSparseTableCosted xs).cost = buildSparseTableCost xs := by
  rfl

theorem buildSparseTableCosted_run (xs : List Int) :
    Costed.run (buildSparseTableCosted xs) =
      (buildSparseTable xs, buildSparseTableCost xs) := by
  rfl

/-- Costed table-row lookup. -/
def tableRowCosted
    (table : List (List (Option Nat))) (k : Nat) :
    Costed (List (Option Nat)) :=
  Costed.tickValue 1 (tableRow table k)

@[simp] theorem tableRowCosted_value
    (table : List (List (Option Nat))) (k : Nat) :
    (tableRowCosted table k).value = tableRow table k := by
  rfl

theorem tableRowCosted_cost
    (table : List (List (Option Nat))) (k : Nat) :
    (tableRowCosted table k).cost = 1 := by
  rfl

/-- Costed row-cell lookup. -/
def rowCellCosted (row : List (Option Nat)) (i : Nat) :
    Costed (Option Nat) :=
  Costed.tickValue 1 (rowCell row i)

@[simp] theorem rowCellCosted_value
    (row : List (Option Nat)) (i : Nat) :
    (rowCellCosted row i).value = rowCell row i := by
  rfl

theorem rowCellCosted_cost
    (row : List (Option Nat)) (i : Nat) :
    (rowCellCosted row i).cost = 1 := by
  rfl

/-- Costed sparse-table candidate combine. -/
def combineIndexCosted
    (xs : List Int) (leftCandidate rightCandidate : Option Nat) :
    Costed (Option Nat) :=
  Costed.tickValue 1 (combineIndex xs leftCandidate rightCandidate)

@[simp] theorem combineIndexCosted_value
    (xs : List Int) (leftCandidate rightCandidate : Option Nat) :
    (combineIndexCosted xs leftCandidate rightCandidate).value =
      combineIndex xs leftCandidate rightCandidate := by
  rfl

theorem combineIndexCosted_cost
    (xs : List Int) (leftCandidate rightCandidate : Option Nat) :
    (combineIndexCosted xs leftCandidate rightCandidate).cost = 1 := by
  rfl

/-- Query cost for a supplied materialized sparse table. -/
def queryFromTableCost (xs : List Int) (left right : Nat) : Nat :=
  if _h : RMQ.ValidRange xs left right then 4 else 1

/-- Costed query over a supplied sparse table. -/
def queryFromTableCosted
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) : Costed (Option Nat) :=
  if _h : RMQ.ValidRange xs left right then
    let len := right - left
    let k := Nat.log2 len
    let p := blockLen k
    Costed.bind (tableRowCosted table k) fun row =>
      Costed.bind (rowCellCosted row left) fun leftCell =>
        Costed.bind (rowCellCosted row (right - p)) fun rightCell =>
          combineIndexCosted xs leftCell rightCell
  else
    Costed.tickValue 1 none

@[simp] theorem queryFromTableCosted_value
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) :
    (queryFromTableCosted xs table left right).value =
      queryFromTable xs table left right := by
  unfold queryFromTableCosted queryFromTable
  by_cases h : RMQ.ValidRange xs left right
  case pos =>
    rw [dif_pos h, dif_pos h]
    simp [tableRowCosted, rowCellCosted, combineIndexCosted]
  case neg =>
    rw [dif_neg h, dif_neg h]
    simp

@[simp] theorem queryFromTableCosted_erase
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) :
    Costed.erase (queryFromTableCosted xs table left right) =
      queryFromTable xs table left right := by
  exact queryFromTableCosted_value xs table left right

theorem queryFromTableCosted_cost
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) :
    (queryFromTableCosted xs table left right).cost =
      queryFromTableCost xs left right := by
  unfold queryFromTableCosted queryFromTableCost
  by_cases h : RMQ.ValidRange xs left right
  case pos =>
    rw [dif_pos h, dif_pos h]
    simp [tableRowCosted, rowCellCosted, combineIndexCosted]
  case neg =>
    rw [dif_neg h, dif_neg h]
    simp

theorem queryFromTableCosted_run
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) :
    Costed.run (queryFromTableCosted xs table left right) =
      (queryFromTable xs table left right,
        queryFromTableCost xs left right) := by
  simp [Costed.run, queryFromTableCosted_value, queryFromTableCosted_cost]

/-- Sparse-table query over a freshly built costed table. -/
def queryCosted (xs : List Int) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind (buildSparseTableCosted xs) fun table =>
    queryFromTableCosted xs table left right

@[simp] theorem queryCosted_value
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).value = query xs left right := by
  simp [queryCosted, query]

@[simp] theorem queryCosted_erase
    (xs : List Int) (left right : Nat) :
    Costed.erase (queryCosted xs left right) = query xs left right := by
  exact queryCosted_value xs left right

theorem queryCosted_cost
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost =
      buildSparseTableCost xs + queryFromTableCost xs left right := by
  simp [queryCosted, buildSparseTableCosted_cost, queryFromTableCosted_cost]

theorem queryCosted_run
    (xs : List Int) (left right : Nat) :
    Costed.run (queryCosted xs left right) =
      (query xs left right,
        buildSparseTableCost xs + queryFromTableCost xs left right) := by
  simp [Costed.run, queryCosted_value, queryCosted_cost]

end RMQ.SparseTable

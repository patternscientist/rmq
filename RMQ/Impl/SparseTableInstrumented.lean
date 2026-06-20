import RMQ.Core.RAM
import RMQ.Core.Refine
import RMQ.Core.TableModel
import RMQ.Impl.SparseTableMemoCost

/-!
# Instrumented Array-backed sparse-table query

This module is the first M1 cost-substrate bridge.  It keeps the verified
list-level sparse-table semantics as the reference behavior, but runs the query
through Array reads in the tiny traced RAM model from `Core.RAM`.
-/

namespace RMQ.SparseTable

namespace Instrumented

/-- Valid range predicate for the Array-facing sparse-table query. -/
abbrev ArrayValidRange (xs : Array Int) (left right : Nat) : Prop :=
  left < right /\ right <= xs.size

/-- Derived step-count recurrence for instrumented sparse-table cells. -/
def blockArgMinArraySteps : Nat -> Nat
  | 0 => 1
  | k + 1 => blockArgMinArraySteps k + blockArgMinArraySteps k + 3

/-- Array view of a materialized sparse-table row. -/
def rowArray (row : List (Option Nat)) : Array (Option Nat) :=
  row.toArray

/-- Array view of a materialized sparse table. -/
def tableArray (table : List (List (Option Nat))) :
    Array (Array (Option Nat)) :=
  (table.map rowArray).toArray

/-- Fetch a table row, returning an empty array if the row is absent. -/
def tableRowArray (table : Array (Array (Option Nat))) (k : Nat) :
    RAM.Exec (Array (Option Nat)) :=
  RAM.Exec.bind (RAM.readArray? table k) fun
  | some row => RAM.Exec.pure row
  | none => RAM.Exec.pure #[]

/-- Fetch and flatten a sparse-table row cell. -/
def rowCellArray (row : Array (Option Nat)) (i : Nat) :
    RAM.Exec (Option Nat) :=
  RAM.Exec.bind (RAM.readArray? row i) fun
  | some cell => RAM.Exec.pure cell
  | none => RAM.Exec.pure none

/-- Array-backed version of `RMQ.betterIndex`, with reads and compare traced. -/
def betterIndexArray (xs : Array Int) (best i : Nat) :
    RAM.Exec Nat :=
  RAM.Exec.bind (RAM.readArray? xs best) fun bestVal? =>
    RAM.Exec.bind (RAM.readArray? xs i) fun iVal? =>
      match bestVal?, iVal? with
      | some bestVal, some iVal =>
          RAM.Exec.bind (RAM.compareLtInt iVal bestVal) fun takeI =>
            RAM.Exec.pure (if takeI then i else best)
      | none, some _ => RAM.Exec.pure i
      | _, _ => RAM.Exec.pure best

/-- Array-backed option-level candidate combine. -/
def combineIndexArray
    (xs : Array Int) : Option Nat -> Option Nat -> RAM.Exec (Option Nat)
  | none, other => RAM.Exec.pure other
  | other, none => RAM.Exec.pure other
  | some i, some j =>
      RAM.Exec.bind (betterIndexArray xs i j) fun idx =>
        RAM.Exec.pure (some idx)

/-- Instrumented memoized successor-row cell construction. -/
def memoNextCellArray
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat)) (i : Nat) :
    RAM.Exec (Option Nat) :=
  RAM.Exec.bind (rowCellArray prev i) fun leftCell =>
    RAM.Exec.bind (rowCellArray prev (i + blockLen k)) fun rightCell =>
      combineIndexArray xs leftCell rightCell

/-- Instrumented array of memoized successor-row cells. -/
def memoNextRowArrayValuesFrom
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat)) :
    Nat -> Nat -> RAM.Exec (Array (Option Nat))
  | 0, _start => RAM.allocArray #[]
  | fuel + 1, start =>
      RAM.Exec.bind (memoNextRowArrayValuesFrom xs k prev fuel start)
        fun cellsPrefix =>
          RAM.Exec.bind (memoNextCellArray xs k prev (start + fuel)) fun cell =>
            RAM.pushArray cellsPrefix cell

/-- Instrumented memoized successor-row materialization. -/
def memoNextRowArray
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat)) :
    RAM.Exec (Array (Option Nat)) :=
  memoNextRowArrayValuesFrom xs k prev xs.size 0

/-- Instrumented sparse-table cell construction over an Array input. -/
def blockArgMinArray
    (xs : Array Int) : Nat -> Nat -> RAM.Exec (Option Nat)
  | 0, start =>
      RAM.Exec.bind (RAM.branch (decide (start < xs.size))) fun ok =>
        RAM.Exec.pure (if ok then some start else none)
  | k + 1, start =>
      RAM.Exec.bind (blockArgMinArray xs k start) fun leftCell =>
        RAM.Exec.bind (blockArgMinArray xs k (start + blockLen k))
          fun rightCell =>
            combineIndexArray xs leftCell rightCell

/-- Instrumented array of sparse-table cells for starts `[start, start + fuel)`. -/
def rowArrayValuesFrom
    (xs : Array Int) (k : Nat) : Nat -> Nat -> RAM.Exec (Array (Option Nat))
  | 0, _start => RAM.allocArray #[]
  | fuel + 1, start =>
      RAM.Exec.bind (rowArrayValuesFrom xs k fuel start) fun cellsPrefix =>
        RAM.Exec.bind (blockArgMinArray xs k (start + fuel)) fun cell =>
          RAM.pushArray cellsPrefix cell

/-- Instrumented materialization of one sparse-table row as an Array. -/
def sparseRowArrayBuild (xs : Array Int) (k : Nat) :
    RAM.Exec (Array (Option Nat)) :=
  rowArrayValuesFrom xs k xs.size 0

/-- Instrumented memoized successor-row suffix. -/
def memoBuildRowsFromArray
    (xs : Array Int) : Nat -> Nat -> Array (Option Nat) ->
    RAM.Exec (List (Array (Option Nat)))
  | 0, _k, _prev => RAM.Exec.pure []
  | fuel + 1, k, prev =>
      RAM.Exec.bind (memoNextRowArray xs k prev) fun row =>
        RAM.Exec.bind (memoBuildRowsFromArray xs fuel (k + 1) row)
          fun rows =>
            RAM.Exec.pure (row :: rows)

/-- Step budget for `memoBuildRowsFromArray`. -/
def memoBuildRowsFromArraySteps (rowSize fuel : Nat) : Nat :=
  fuel * (rowSize * 6 + 1)

/-- Step budget for `memoBuildSparseTableArray`. -/
def memoBuildSparseTableArraySteps (n : Nat) : Nat :=
  if n = 0 then
    2
  else
    1 + (n * (blockArgMinArraySteps 0 + 1) + 1) +
      memoBuildRowsFromArraySteps n (Nat.log2 n) + 1

/-- Instrumented memoized sparse-table build. -/
def memoBuildSparseTableArray (xs : Array Int) :
    RAM.Exec (Array (Array (Option Nat))) :=
  RAM.Exec.bind (RAM.branch (decide (xs.size = 0))) fun empty =>
    if empty then
      RAM.allocArray #[]
    else
      RAM.Exec.bind (sparseRowArrayBuild xs 0) fun base =>
        RAM.Exec.bind (memoBuildRowsFromArray xs (Nat.log2 xs.size) 0 base)
          fun rows =>
            RAM.allocArray (base :: rows).toArray

/-- Instrumented supplied-table sparse query over Array views. -/
def queryFromArrayTable
    (xs : Array Int) (table : Array (Array (Option Nat)))
    (left right : Nat) : RAM.Exec (Option Nat) :=
  if _h : ArrayValidRange xs left right then
    RAM.Exec.bind (RAM.branch true) fun _ =>
      let len := right - left
      let k := Nat.log2 len
      let p := blockLen k
      RAM.Exec.bind (tableRowArray table k) fun row =>
        RAM.Exec.bind (rowCellArray row left) fun leftCell =>
          RAM.Exec.bind (rowCellArray row (right - p)) fun rightCell =>
            combineIndexArray xs leftCell rightCell
  else
    RAM.Exec.bind (RAM.branch false) fun _ =>
      RAM.Exec.pure none

/-- Instrumented sparse-table query over freshly materialized Array views. -/
def query (xs : List Int) (left right : Nat) : RAM.Exec (Option Nat) :=
  queryFromArrayTable xs.toArray (tableArray (buildSparseTable xs)) left right

/-- Instrumented memoized sparse-table build followed by an Array-backed query. -/
def memoQueryWithTracedBuild
    (xs : List Int) (left right : Nat) : RAM.Exec (Option Nat) :=
  RAM.Exec.bind (memoBuildSparseTableArray xs.toArray) fun table =>
    queryFromArrayTable xs.toArray table left right

/-- Stored sparse-table representation backed by the shared table model. -/
abbrev StoredTable (abs : List (List (Option Nat))) : Type :=
  RMQ.Refine.StoredMatrix (Option Nat) abs

/-- Query a supplied stored sparse table through its Array-backed representation. -/
def queryFromStoredTable
    (xs : List Int) {abs : List (List (Option Nat))}
    (table : StoredTable abs) (left right : Nat) :
    RAM.Exec (Option Nat) :=
  queryFromArrayTable xs.toArray table.repr left right

@[simp] theorem rowArray_get? (row : List (Option Nat)) (i : Nat) :
    (rowArray row)[i]? = row[i]? := by
  simp [rowArray, List.getElem?_toArray]

theorem tableRowArray_value_toList
    (table : List (List (Option Nat))) (k : Nat) :
    ((tableRowArray (tableArray table) k).value).toList =
      tableRow table k := by
  unfold tableRowArray tableArray tableRow
  simp [RAM.Exec.bind, RAM.Exec.pure, List.getElem?_toArray]
  cases table[k]? <;> simp [rowArray]

theorem tableRowArray_value_toList_of_stored
    {table : List (List (Option Nat))}
    (stored : StoredTable table) (k : Nat) :
    ((tableRowArray stored.repr k).value).toList =
      tableRow table k := by
  unfold tableRowArray tableRow
  have hrow :=
    RMQ.Refine.StoredMatrix.row?_getD_toList_eq_absRow?_getD stored k
  unfold RMQ.Refine.StoredMatrix.row? at hrow
  unfold RMQ.Refine.StoredMatrix.absRow? at hrow
  cases hstored : stored.repr[k]? <;> cases htable : table[k]? <;>
    simp [hstored, htable, RAM.Exec.bind, RAM.Exec.pure] at hrow ⊢ <;>
      exact hrow

theorem tableRowArray_value_toList_of_refines
    (tableA : Array (Array (Option Nat)))
    (table : List (List (Option Nat)))
    (hTable : tableA.toList.map Array.toList = table) (k : Nat) :
    ((tableRowArray tableA k).value).toList = tableRow table k := by
  exact tableRowArray_value_toList_of_stored
    ({ repr := tableA, erases := hTable } : StoredTable table) k

theorem rowCellArray_value
    (row : List (Option Nat)) (i : Nat) :
    (rowCellArray (rowArray row) i).value = rowCell row i := by
  unfold rowCellArray rowCell
  simp [RAM.Exec.bind, RAM.Exec.pure, rowArray, List.getElem?_toArray]
  cases row[i]? <;> simp

theorem rowCellArray_value_toList
    (row : Array (Option Nat)) (i : Nat) :
    (rowCellArray row i).value = rowCell row.toList i := by
  unfold rowCellArray rowCell
  simp [RAM.Exec.bind, RAM.Exec.pure]
  cases row[i]? <;> simp

theorem betterIndexArray_value
    (xs : List Int) (best i : Nat) :
    (betterIndexArray xs.toArray best i).value =
      RMQ.betterIndex xs best i := by
  unfold betterIndexArray RMQ.betterIndex
  simp [RAM.readArray?, RAM.compareLtInt, RAM.Exec.bind, RAM.Exec.pure,
    List.getElem?_toArray]
  cases xs[best]? <;> cases xs[i]? <;> simp

theorem combineIndexArray_value
    (xs : List Int) (leftCandidate rightCandidate : Option Nat) :
    (combineIndexArray xs.toArray leftCandidate rightCandidate).value =
      combineIndex xs leftCandidate rightCandidate := by
  cases leftCandidate <;> cases rightCandidate <;>
    simp [combineIndexArray, combineIndex, RMQ.combineIndex,
      betterIndexArray_value]

theorem betterIndexArray_steps_le_three
    (xs : Array Int) (best i : Nat) :
    (betterIndexArray xs best i).steps <= 3 := by
  unfold betterIndexArray
  simp [RAM.Exec.steps_bind]
  cases xs[best]? <;> cases xs[i]? <;> simp

theorem combineIndexArray_steps_le_three
    (xs : Array Int) (leftCandidate rightCandidate : Option Nat) :
    (combineIndexArray xs leftCandidate rightCandidate).steps <= 3 := by
  cases leftCandidate <;> cases rightCandidate <;>
    simp [combineIndexArray, betterIndexArray_steps_le_three]

theorem memoNextCellArray_value
    (xs : List Int) (k : Nat) (prev : Array (Option Nat)) (i : Nat) :
    (memoNextCellArray xs.toArray k prev i).value =
      combineIndex xs (rowCell prev.toList i)
        (rowCell prev.toList (i + blockLen k)) := by
  unfold memoNextCellArray
  simp [RAM.Exec.bind, rowCellArray_value_toList, combineIndexArray_value]

theorem memoNextCellArray_steps_le_five
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat)) (i : Nat) :
    (memoNextCellArray xs k prev i).steps <= 5 := by
  unfold memoNextCellArray
  simp [RAM.Exec.steps_bind]
  have hleft : (rowCellArray prev i).steps = 1 := by
    unfold rowCellArray
    cases h : prev[i]? <;> simp [h, RAM.Exec.steps_bind]
  have hright : (rowCellArray prev (i + blockLen k)).steps = 1 := by
    unfold rowCellArray
    cases h : prev[i + blockLen k]? <;> simp [h, RAM.Exec.steps_bind]
  have hcombine :=
    combineIndexArray_steps_le_three xs
      (rowCellArray prev i).value
      (rowCellArray prev (i + blockLen k)).value
  omega

theorem memoNextRowArrayValuesFrom_value_toList
    (xs : List Int) (k : Nat) (prev : Array (Option Nat))
    (fuel start : Nat) :
    ((memoNextRowArrayValuesFrom xs.toArray k prev fuel start).value).toList =
      (List.range fuel).map fun offset =>
        combineIndex xs (rowCell prev.toList (start + offset))
          (rowCell prev.toList (start + offset + blockLen k)) := by
  induction fuel generalizing start with
  | zero =>
      simp [memoNextRowArrayValuesFrom]
  | succ fuel ih =>
      simp [memoNextRowArrayValuesFrom, ih, memoNextCellArray_value,
        List.range_succ, List.map_append, Nat.add_assoc]

theorem memoNextRowArrayValuesFrom_steps_le
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat))
    (fuel start : Nat) :
    (memoNextRowArrayValuesFrom xs k prev fuel start).steps <= fuel * 6 + 1 := by
  induction fuel generalizing start with
  | zero =>
      simp [memoNextRowArrayValuesFrom]
  | succ fuel ih =>
      unfold memoNextRowArrayValuesFrom
      simp [RAM.Exec.steps_bind]
      have hprefix := ih start
      have hcell := memoNextCellArray_steps_le_five xs k prev (start + fuel)
      omega

private theorem memoNextRow_eq_range_map
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    memoNextRow xs k prev =
      (List.range xs.length).map fun i =>
        combineIndex xs (rowCell prev i) (rowCell prev (i + blockLen k)) := by
  apply List.ext_getElem?
  intro i
  unfold memoNextRow
  rw [List.getElem?_ofFn, List.getElem?_map]
  by_cases h : i < xs.length
  · have hrange : (List.range xs.length)[i]? = some i :=
      List.getElem?_range h
    simp [h]
  · have hle : (List.range xs.length).length <= i := by
      simp [List.length_range]
      omega
    have hrange : (List.range xs.length)[i]? = none :=
      List.getElem?_eq_none hle
    simp [h]

theorem memoNextRowArray_value_toList
    (xs : List Int) (k : Nat) (prev : Array (Option Nat)) :
    ((memoNextRowArray xs.toArray k prev).value).toList =
      memoNextRow xs k prev.toList := by
  unfold memoNextRowArray
  simp [memoNextRowArrayValuesFrom_value_toList, memoNextRow_eq_range_map]

theorem memoNextRowArray_steps_le
    (xs : Array Int) (k : Nat) (prev : Array (Option Nat)) :
    (memoNextRowArray xs k prev).steps <= xs.size * 6 + 1 := by
  unfold memoNextRowArray
  exact memoNextRowArrayValuesFrom_steps_le xs k prev xs.size 0

@[simp] theorem blockArgMinArraySteps_pos (k : Nat) :
    0 < blockArgMinArraySteps k := by
  induction k with
  | zero =>
      simp [blockArgMinArraySteps]
  | succ k ih =>
      simp [blockArgMinArraySteps]

theorem blockArgMinArray_value
    (xs : List Int) (k start : Nat) :
    (blockArgMinArray xs.toArray k start).value =
      blockArgMin xs k start := by
  induction k generalizing start with
  | zero =>
      unfold blockArgMinArray blockArgMin
      by_cases h : start < xs.length <;>
        simp [h]
  | succ k ih =>
      unfold blockArgMinArray blockArgMin
      simp [RAM.Exec.bind, ih, combineIndexArray_value]

theorem blockArgMinArray_steps_le
    (xs : Array Int) (k start : Nat) :
    (blockArgMinArray xs k start).steps <= blockArgMinArraySteps k := by
  induction k generalizing start with
  | zero =>
      unfold blockArgMinArray blockArgMinArraySteps
      by_cases h : start < xs.size <;>
        simp [RAM.Exec.steps_bind, h]
  | succ k ih =>
      unfold blockArgMinArray blockArgMinArraySteps
      simp [RAM.Exec.steps_bind]
      have hleft := ih start
      have hright := ih (start + blockLen k)
      have hcombine :=
        combineIndexArray_steps_le_three xs
          (blockArgMinArray xs k start).value
          (blockArgMinArray xs k (start + blockLen k)).value
      omega

theorem rowArrayValuesFrom_value_toList
    (xs : List Int) (k fuel start : Nat) :
    ((rowArrayValuesFrom xs.toArray k fuel start).value).toList =
      (List.range fuel).map fun offset =>
        blockArgMin xs k (start + offset) := by
  induction fuel generalizing start with
  | zero =>
      simp [rowArrayValuesFrom]
  | succ fuel ih =>
      simp [rowArrayValuesFrom, ih, blockArgMinArray_value, List.range_succ,
        List.map_append]

theorem rowArrayValuesFrom_steps_le
    (xs : Array Int) (k fuel start : Nat) :
    (rowArrayValuesFrom xs k fuel start).steps <=
      fuel * (blockArgMinArraySteps k + 1) + 1 := by
  induction fuel generalizing start with
  | zero =>
      simp [rowArrayValuesFrom]
  | succ fuel ih =>
      unfold rowArrayValuesFrom
      simp [RAM.Exec.steps_bind]
      have hprefix := ih start
      have hcell := blockArgMinArray_steps_le xs k (start + fuel)
      have hbudget :
          fuel * (blockArgMinArraySteps k + 1) + 1 +
              blockArgMinArraySteps k + 1 <=
            (fuel + 1) * (blockArgMinArraySteps k + 1) + 1 := by
        rw [Nat.succ_mul]
        omega
      omega

private theorem sparseRow_eq_range_map (xs : List Int) (k : Nat) :
    sparseRow xs k =
      (List.range xs.length).map fun start => blockArgMin xs k start := by
  apply List.ext_getElem?
  intro i
  unfold sparseRow
  rw [List.getElem?_ofFn, List.getElem?_map]
  by_cases h : i < xs.length
  · have hrange : (List.range xs.length)[i]? = some i :=
      List.getElem?_range h
    simp [h]
  · have hle : (List.range xs.length).length <= i := by
      simp [List.length_range]
      omega
    have hrange : (List.range xs.length)[i]? = none :=
      List.getElem?_eq_none hle
    simp [h]

theorem sparseRowArrayBuild_value_toList
    (xs : List Int) (k : Nat) :
    ((sparseRowArrayBuild xs.toArray k).value).toList =
      sparseRow xs k := by
  unfold sparseRowArrayBuild
  simp [rowArrayValuesFrom_value_toList, sparseRow_eq_range_map]

theorem sparseRowArrayBuild_steps_le
    (xs : Array Int) (k : Nat) :
    (sparseRowArrayBuild xs k).steps <=
      xs.size * (blockArgMinArraySteps k + 1) + 1 := by
  unfold sparseRowArrayBuild
  exact rowArrayValuesFrom_steps_le xs k xs.size 0

theorem memoBuildRowsFromArray_value_toList
    (xs : List Int) (fuel k : Nat) (prev : Array (Option Nat)) :
    ((memoBuildRowsFromArray xs.toArray fuel k prev).value.map
        Array.toList) =
      memoBuildRowsFrom xs fuel k prev.toList := by
  induction fuel generalizing k prev with
  | zero =>
      simp [memoBuildRowsFromArray, memoBuildRowsFrom]
  | succ fuel ih =>
      simp [memoBuildRowsFromArray, memoBuildRowsFrom,
        memoNextRowArray_value_toList, ih]

theorem memoBuildRowsFromArray_steps_le
    (xs : Array Int) (fuel k : Nat) (prev : Array (Option Nat)) :
    (memoBuildRowsFromArray xs fuel k prev).steps <=
      memoBuildRowsFromArraySteps xs.size fuel := by
  induction fuel generalizing k prev with
  | zero =>
      simp [memoBuildRowsFromArray, memoBuildRowsFromArraySteps]
  | succ fuel ih =>
      unfold memoBuildRowsFromArray memoBuildRowsFromArraySteps
      simp [RAM.Exec.steps_bind]
      have hrow := memoNextRowArray_steps_le xs k prev
      have htail := ih (k + 1) (memoNextRowArray xs k prev).value
      have htail' :
          (memoBuildRowsFromArray xs fuel (k + 1)
              (memoNextRowArray xs k prev).value).steps <=
            fuel * (xs.size * 6 + 1) := by
        simpa [memoBuildRowsFromArraySteps] using htail
      have hmul :
          (fuel + 1) * (xs.size * 6 + 1) =
            (xs.size * 6 + 1) + fuel * (xs.size * 6 + 1) := by
        rw [Nat.succ_mul, Nat.add_comm]
      omega

theorem memoBuildSparseTableArray_value_toList
    (xs : List Int) :
    ((memoBuildSparseTableArray xs.toArray).value).toList.map Array.toList =
      memoBuildSparseTable xs := by
  unfold memoBuildSparseTableArray memoBuildSparseTable
  by_cases h : xs.length = 0
  · have hsize : xs.toArray.size = 0 := by
      simpa using h
    have hrowCount : memoRowCount xs = 0 := by
      unfold memoRowCount
      simp [h]
    simp [hsize, hrowCount, RAM.Exec.bind, RAM.branch,
      RAM.allocArray]
  · have hnotNil : xs ≠ [] := by
      intro hnil
      exact h (by simp [hnil])
    have hrowCount : Not (memoRowCount xs = 0) := by
      unfold memoRowCount
      simp [h]
    have hfuel : Nat.log2 xs.toArray.size = memoRowCount xs - 1 := by
      unfold memoRowCount
      simp [h]
    have hfuelList : Nat.log2 xs.length = memoRowCount xs - 1 := by
      simpa using hfuel
    simp [hnotNil, hrowCount, hfuelList, RAM.Exec.bind, RAM.branch,
      RAM.allocArray,
      sparseRowArrayBuild_value_toList,
      memoBuildRowsFromArray_value_toList]

theorem memoBuildSparseTableArray_steps_le
    (xs : Array Int) :
    (memoBuildSparseTableArray xs).steps <=
      memoBuildSparseTableArraySteps xs.size := by
  unfold memoBuildSparseTableArray memoBuildSparseTableArraySteps
  by_cases h : xs.size = 0
  · simp [h, RAM.Exec.steps_bind]
  · simp [h, RAM.Exec.steps_bind]
    have hbase := sparseRowArrayBuild_steps_le xs 0
    have hrows :=
      memoBuildRowsFromArray_steps_le xs (Nat.log2 xs.size) 0
        (sparseRowArrayBuild xs 0).value
    omega

@[simp] theorem tableRowArray_steps
    (table : Array (Array (Option Nat))) (k : Nat) :
  (tableRowArray table k).steps = 1 := by
  unfold tableRowArray
  cases h : table[k]? <;> simp [h, RAM.Exec.steps_bind]

@[simp] theorem rowCellArray_steps
    (row : Array (Option Nat)) (i : Nat) :
  (rowCellArray row i).steps = 1 := by
  unfold rowCellArray
  cases h : row[i]? <;> simp [h, RAM.Exec.steps_bind]

theorem queryFromArrayTable_value
    (xs : List Int) (table : List (List (Option Nat)))
    (left right : Nat) :
    (queryFromArrayTable xs.toArray (tableArray table) left right).value =
      queryFromTable xs table left right := by
  unfold queryFromArrayTable queryFromTable
  have hxs : xs.toArray.toList = xs := by
    simp
  by_cases h : RMQ.ValidRange xs left right
  case pos =>
    have hArray : ArrayValidRange xs.toArray left right := by
      simpa [ArrayValidRange] using h
    rw [dif_pos hArray, dif_pos h]
    simp [RAM.Exec.bind, RAM.branch]
    let len := right - left
    let k := Nat.log2 len
    let p := blockLen k
    have hrow :=
      tableRowArray_value_toList table k
    have hleft :=
      rowCellArray_value (tableRow table k) left
    have hright :=
      rowCellArray_value (tableRow table k) (right - p)
    change
      (combineIndexArray xs.toArray
        (rowCellArray (tableRowArray (tableArray table) k).value left).value
        (rowCellArray (tableRowArray (tableArray table) k).value
          (right - p)).value).value =
        combineIndex xs (rowCell (tableRow table k) left)
          (rowCell (tableRow table k) (right - p))
    have hleft' :
        (rowCellArray (tableRowArray (tableArray table) k).value left).value =
          rowCell (tableRow table k) left := by
      rw [<- hrow]
      exact rowCellArray_value ((tableRowArray (tableArray table) k).value.toList)
        left
    have hright' :
        (rowCellArray (tableRowArray (tableArray table) k).value
            (right - p)).value =
          rowCell (tableRow table k) (right - p) := by
      rw [<- hrow]
      exact rowCellArray_value ((tableRowArray (tableArray table) k).value.toList)
        (right - p)
    simp [hleft', hright', combineIndexArray_value]
  case neg =>
    have hArray : Not (ArrayValidRange xs.toArray left right) := by
      intro hbad
      exact h (by simpa [ArrayValidRange] using hbad)
    rw [dif_neg hArray, dif_neg h]
    simp [RAM.Exec.bind, RAM.Exec.pure, RAM.branch]

theorem queryFromArrayTable_value_of_refines
    (xs : List Int) (tableA : Array (Array (Option Nat)))
    (table : List (List (Option Nat)))
    (hTable : tableA.toList.map Array.toList = table)
    (left right : Nat) :
    (queryFromArrayTable xs.toArray tableA left right).value =
      queryFromTable xs table left right := by
  unfold queryFromArrayTable queryFromTable
  by_cases h : RMQ.ValidRange xs left right
  case pos =>
    have hArray : ArrayValidRange xs.toArray left right := by
      simpa [ArrayValidRange] using h
    rw [dif_pos hArray, dif_pos h]
    simp [RAM.Exec.bind, RAM.branch]
    let len := right - left
    let k := Nat.log2 len
    let p := blockLen k
    have hrow :
        ((tableRowArray tableA k).value).toList =
          tableRow table k :=
      tableRowArray_value_toList_of_refines tableA table hTable k
    change
      (combineIndexArray xs.toArray
        (rowCellArray (tableRowArray tableA k).value left).value
        (rowCellArray (tableRowArray tableA k).value
          (right - p)).value).value =
        combineIndex xs (rowCell (tableRow table k) left)
          (rowCell (tableRow table k) (right - p))
    have hleft' :
        (rowCellArray (tableRowArray tableA k).value left).value =
          rowCell (tableRow table k) left := by
      rw [<- hrow]
      exact rowCellArray_value ((tableRowArray tableA k).value.toList) left
    have hright' :
        (rowCellArray (tableRowArray tableA k).value (right - p)).value =
          rowCell (tableRow table k) (right - p) := by
      rw [<- hrow]
      exact rowCellArray_value ((tableRowArray tableA k).value.toList)
        (right - p)
    simp [hleft', hright', combineIndexArray_value]
  case neg =>
    have hArray : Not (ArrayValidRange xs.toArray left right) := by
      intro hbad
      exact h (by simpa [ArrayValidRange] using hbad)
    rw [dif_neg hArray, dif_neg h]
    simp [RAM.Exec.bind, RAM.Exec.pure, RAM.branch]

theorem queryFromStoredTable_value
    (xs : List Int) {abs : List (List (Option Nat))}
    (table : StoredTable abs) (left right : Nat) :
    (queryFromStoredTable xs table left right).value =
      SparseTable.queryFromTable xs abs left right := by
  unfold queryFromStoredTable
  exact queryFromArrayTable_value_of_refines xs table.repr abs table.erases
    left right

@[simp] theorem query_value (xs : List Int) (left right : Nat) :
    (query xs left right).value = SparseTable.query xs left right := by
  unfold query SparseTable.query
  exact queryFromArrayTable_value xs (buildSparseTable xs) left right

theorem queryFromArrayTable_steps_le_seven
    (xs : Array Int) (table : Array (Array (Option Nat)))
    (left right : Nat) :
    (queryFromArrayTable xs table left right).steps <= 7 := by
  unfold queryFromArrayTable
  by_cases h : ArrayValidRange xs left right
  case pos =>
    rw [dif_pos h]
    simp
    have hcombine :=
      combineIndexArray_steps_le_three xs
        (rowCellArray (tableRowArray table (Nat.log2 (right - left))).value
          left).value
        (rowCellArray
          (tableRowArray table (Nat.log2 (right - left))).value
          (right - blockLen (Nat.log2 (right - left)))).value
    omega
  case neg =>
    rw [dif_neg h]
    simp

theorem queryFromStoredTable_steps_le_seven
    (xs : List Int) {abs : List (List (Option Nat))}
    (table : StoredTable abs) (left right : Nat) :
    (queryFromStoredTable xs table left right).steps <= 7 := by
  unfold queryFromStoredTable
  exact queryFromArrayTable_steps_le_seven xs.toArray table.repr left right

theorem query_steps_le_seven
    (xs : List Int) (left right : Nat) :
    (query xs left right).steps <= 7 := by
  exact queryFromArrayTable_steps_le_seven xs.toArray
    (tableArray (buildSparseTable xs)) left right

theorem queryFromStoredTable_toCosted_run
    (xs : List Int) {abs : List (List (Option Nat))}
    (table : StoredTable abs) (left right : Nat) :
    (queryFromStoredTable xs table left right).toCosted.run =
      (SparseTable.queryFromTable xs abs left right,
        (queryFromStoredTable xs table left right).steps) := by
  simp [RAM.Exec.toCosted_run_eq_value_steps, queryFromStoredTable_value]

theorem query_toCosted_sound
    (xs : List Int) (left right : Nat) :
    (query xs left right).toCosted.cost =
      (query xs left right).steps := by
  rfl

/--
Headline M1 query theorem: the instrumented Array-backed sparse-table query
refines the verified List query, and its operational trace has constant length.
-/
theorem query_refines_and_steps_le_seven
    (xs : List Int) (left right : Nat) :
    (query xs left right).value = SparseTable.query xs left right /\
      (query xs left right).steps <= 7 := by
  exact ⟨query_value xs left right, query_steps_le_seven xs left right⟩

/--
Headline M1 memoized-build theorem: the instrumented Array build follows the
optimized log-row sparse-table construction and its cost bound is derived from
the primitive trace rather than asserted as a lump cost.
-/
theorem memoBuild_refine_with_steps
    (xs : List Int) :
    ((memoBuildSparseTableArray xs.toArray).value).toList.map Array.toList =
        memoBuildSparseTable xs /\
      (memoBuildSparseTableArray xs.toArray).steps <=
        memoBuildSparseTableArraySteps xs.length := by
  refine ⟨memoBuildSparseTableArray_value_toList xs, ?_⟩
  simpa using memoBuildSparseTableArray_steps_le xs.toArray

/--
Headline M1 memoized build/query theorem: the traced memoized sparse-table
builder produces a table that can be supplied to the traced Array query, and
the resulting query refines the verified sparse-table query with the same
constant primitive-trace bound.
-/
theorem memoBuild_and_query_refine_with_steps
    (xs : List Int) (left right : Nat) :
    ((memoBuildSparseTableArray xs.toArray).value).toList.map Array.toList =
        memoBuildSparseTable xs /\
      (memoBuildSparseTableArray xs.toArray).steps <=
        memoBuildSparseTableArraySteps xs.length /\
      (queryFromArrayTable xs.toArray
          (memoBuildSparseTableArray xs.toArray).value left right).value =
        SparseTable.query xs left right /\
      (queryFromArrayTable xs.toArray
          (memoBuildSparseTableArray xs.toArray).value left right).steps <= 7 := by
  refine ⟨memoBuildSparseTableArray_value_toList xs, ?_, ?_, ?_⟩
  · simpa using memoBuildSparseTableArray_steps_le xs.toArray
  · calc
      (queryFromArrayTable xs.toArray
          (memoBuildSparseTableArray xs.toArray).value left right).value =
          queryFromTable xs (memoBuildSparseTable xs) left right := by
            exact queryFromArrayTable_value_of_refines xs
              (memoBuildSparseTableArray xs.toArray).value
              (memoBuildSparseTable xs)
              (memoBuildSparseTableArray_value_toList xs) left right
      _ = SparseTable.query xs left right := by
            simpa [SparseTable.memoQuery] using
              SparseTable.memoQuery_eq_query xs left right
  · exact queryFromArrayTable_steps_le_seven xs.toArray
      (memoBuildSparseTableArray xs.toArray).value left right

@[simp] theorem memoQueryWithTracedBuild_value
    (xs : List Int) (left right : Nat) :
    (memoQueryWithTracedBuild xs left right).value =
      SparseTable.query xs left right := by
  unfold memoQueryWithTracedBuild
  simp [RAM.Exec.bind]
  calc
    (queryFromArrayTable xs.toArray
        (memoBuildSparseTableArray xs.toArray).value left right).value =
        queryFromTable xs (memoBuildSparseTable xs) left right := by
          exact queryFromArrayTable_value_of_refines xs
            (memoBuildSparseTableArray xs.toArray).value
            (memoBuildSparseTable xs)
            (memoBuildSparseTableArray_value_toList xs) left right
    _ = SparseTable.query xs left right := by
          simpa [SparseTable.memoQuery] using
            SparseTable.memoQuery_eq_query xs left right

theorem memoQueryWithTracedBuild_steps_le
    (xs : List Int) (left right : Nat) :
    (memoQueryWithTracedBuild xs left right).steps <=
      memoBuildSparseTableArraySteps xs.length + 7 := by
  unfold memoQueryWithTracedBuild
  simp [RAM.Exec.steps_bind]
  have hbuild := memoBuildSparseTableArray_steps_le xs.toArray
  have hbuild' :
      (memoBuildSparseTableArray xs.toArray).steps <=
        memoBuildSparseTableArraySteps xs.length := by
    simpa using hbuild
  have hquery :=
    queryFromArrayTable_steps_le_seven xs.toArray
      (memoBuildSparseTableArray xs.toArray).value left right
  omega

/--
End-to-end M1 sparse-table theorem: the traced memoized build is sequenced with
the traced Array query, and the whole execution refines the verified sparse
table while charging only the derived build trace plus the seven query steps.
-/
theorem memoQueryWithTracedBuild_refine_with_steps
    (xs : List Int) (left right : Nat) :
    (memoQueryWithTracedBuild xs left right).value =
        SparseTable.query xs left right /\
      (memoQueryWithTracedBuild xs left right).steps <=
        memoBuildSparseTableArraySteps xs.length + 7 := by
  exact ⟨memoQueryWithTracedBuild_value xs left right,
    memoQueryWithTracedBuild_steps_le xs left right⟩

end Instrumented

end RMQ.SparseTable

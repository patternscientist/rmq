import RMQ.Core.Cost
import RMQ.Impl.SparseTable

/-!
# Memoized sparse-table build costs

This module contains the value-level memoized sparse-table build and the
remaining model-level build-cost API used by Fischer-Heun summaries. The older
naive fresh sparse-table build/query cost module has been retired; supplied
summary-table queries keep a small RAM/unit-cost adapter here until they are
migrated to the traced Array substrate end-to-end.

The first milestone is structural rather than asymptotic notation: memoized
successor rows are proved equal to the corresponding recursive `sparseRow`, the
costed row builder exposes an exact linear cost formula, and the log-row table
builder has an exact closed-form cost. The memoized table is also proved
sufficient for every valid sparse-table query level, giving a costed fresh-table
query that erases to the verified sparse-table query.
-/

namespace RMQ.SparseTable

/--
Sparse-table cells beyond the source list are absent at every level.

This helper lets memoized successor rows read past the materialized row tail and
still agree with the recursive `blockArgMin` definition.
-/
theorem blockArgMin_none_of_length_le_start
    (xs : List Int) (k start : Nat) (h : xs.length <= start) :
    blockArgMin xs k start = none := by
  induction k generalizing start with
  | zero =>
      have hnot : ¬ start < xs.length := Nat.not_lt_of_ge h
      simp [blockArgMin, hnot]
  | succ k ih =>
      have hright : xs.length <= start + blockLen k := by
        omega
      simp [blockArgMin, ih start h, ih (start + blockLen k) hright,
        combineIndex, RMQ.combineIndex]

/-- Row lookup agrees with `blockArgMin` even when the requested cell is absent. -/
theorem sparseRow_cell_eq_blockArgMin_total
    (xs : List Int) (k start : Nat) :
    rowCell (sparseRow xs k) start = blockArgMin xs k start := by
  by_cases h : start < xs.length
  · exact sparseRow_cell_eq_blockArgMin xs k start h
  · have hle : xs.length <= start := Nat.le_of_not_gt h
    have hrowLen : (sparseRow xs k).length <= start := by
      simpa [sparseRow] using hle
    have hnone : (sparseRow xs k)[start]? = none :=
      List.getElem?_eq_none hrowLen
    unfold rowCell
    simp [hnone, blockArgMin_none_of_length_le_start xs k start hle]

/-- Build level `k + 1` from a materialized level-`k` row. -/
def memoNextRow
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    List (Option Nat) :=
  List.ofFn fun i : Fin xs.length =>
    combineIndex xs (rowCell prev i.1) (rowCell prev (i.1 + blockLen k))

/-- The memoized successor construction agrees with the recursive row. -/
theorem memoNextRow_sparseRow
    (xs : List Int) (k : Nat) :
    memoNextRow xs k (sparseRow xs k) = sparseRow xs (k + 1) := by
  apply List.ext_getElem
  · simp [memoNextRow, sparseRow]
  · intro i hleft hright
    simp only [memoNextRow, List.getElem_ofFn]
    rw [sparseRow_cell_eq_blockArgMin_total xs k i,
      sparseRow_cell_eq_blockArgMin_total xs k (i + blockLen k)]
    simp [sparseRow, blockArgMin]

/-- Unit-cost reads plus one combine for one memoized successor-row cell. -/
def memoNextCellCost : Nat := 3

/-- Cost of building one memoized successor row from the previous row. -/
def memoNextRowCost (xs : List Int) : Nat :=
  xs.length * memoNextCellCost

/-- Costed successor-row construction. -/
def memoNextRowCosted
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    Costed (List (Option Nat)) :=
  Costed.tickValue (memoNextRowCost xs) (memoNextRow xs k prev)

@[simp] theorem memoNextRowCosted_value
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    (memoNextRowCosted xs k prev).value = memoNextRow xs k prev := by
  rfl

@[simp] theorem memoNextRowCosted_erase
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    Costed.erase (memoNextRowCosted xs k prev) = memoNextRow xs k prev := by
  rfl

theorem memoNextRowCosted_cost
    (xs : List Int) (k : Nat) (prev : List (Option Nat)) :
    (memoNextRowCosted xs k prev).cost = memoNextRowCost xs := by
  rfl

/-- Costed successor-row construction preserves the sparse-row value invariant. -/
theorem memoNextRowCosted_sparseRow_value
    (xs : List Int) (k : Nat) :
    (memoNextRowCosted xs k (sparseRow xs k)).value = sparseRow xs (k + 1) := by
  rw [memoNextRowCosted_value, memoNextRow_sparseRow]

/--
The number of rows in a textbook sparse table. Empty inputs need no rows; a
nonempty list needs levels `0` through `log2 xs.length`.
-/
def memoRowCount (xs : List Int) : Nat :=
  if xs.length = 0 then 0 else Nat.log2 xs.length + 1

/-- Cost of the direct level-zero memoized row. -/
def memoBaseRowCost (xs : List Int) : Nat :=
  xs.length

/-- Costed direct construction of level zero. -/
def memoBaseRowCosted (xs : List Int) : Costed (List (Option Nat)) :=
  Costed.tickValue (memoBaseRowCost xs) (sparseRow xs 0)

@[simp] theorem memoBaseRowCosted_value (xs : List Int) :
    (memoBaseRowCosted xs).value = sparseRow xs 0 := by
  rfl

@[simp] theorem memoBaseRowCosted_erase (xs : List Int) :
    Costed.erase (memoBaseRowCosted xs) = sparseRow xs 0 := by
  rfl

theorem memoBaseRowCosted_cost (xs : List Int) :
    (memoBaseRowCosted xs).cost = memoBaseRowCost xs := by
  rfl

/--
Closed-form cost target for the memoized log-row sparse-table build: one
direct base row plus one linear successor-row pass for each remaining row.
-/
def memoBuildSparseTableCost (xs : List Int) : Nat :=
  if memoRowCount xs = 0 then
    0
  else
    memoBaseRowCost xs + (memoRowCount xs - 1) * memoNextRowCost xs

/--
The memoized build cost is the textbook shape: one direct base row plus one
linear `3 * n` pass for each successor level.
-/
theorem memoBuildSparseTableCost_eq_log (xs : List Int) :
    memoBuildSparseTableCost xs =
      if xs.length = 0 then
        0
      else
        xs.length + Nat.log2 xs.length * (xs.length * memoNextCellCost) := by
  unfold memoBuildSparseTableCost memoRowCount memoBaseRowCost memoNextRowCost
  by_cases h : xs.length = 0
  · simp [h]
  · simp [h]

/--
Build `fuel` successor rows, starting from a materialized row for level `k`.
The returned list starts with level `k + 1`.
-/
def memoBuildRowsFrom
    (xs : List Int) : Nat -> Nat -> List (Option Nat) ->
    List (List (Option Nat))
  | 0, _k, _prev => []
  | fuel + 1, k, prev =>
      let row := memoNextRow xs k prev
      row :: memoBuildRowsFrom xs fuel (k + 1) row

/-- Cost of `memoBuildRowsFrom`: one linear successor-row pass per fuel step. -/
def memoBuildRowsFromCost (xs : List Int) (fuel : Nat) : Nat :=
  fuel * memoNextRowCost xs

/-- Costed construction of the successor-row suffix. -/
def memoBuildRowsFromCosted
    (xs : List Int) : Nat -> Nat -> List (Option Nat) ->
    Costed (List (List (Option Nat)))
  | 0, _k, _prev => Costed.pure []
  | fuel + 1, k, prev =>
      Costed.bind (memoNextRowCosted xs k prev) fun row =>
        Costed.bind (memoBuildRowsFromCosted xs fuel (k + 1) row) fun rows =>
          Costed.pure (row :: rows)

@[simp] theorem memoBuildRowsFromCosted_value
    (xs : List Int) (fuel k : Nat) (prev : List (Option Nat)) :
    (memoBuildRowsFromCosted xs fuel k prev).value =
      memoBuildRowsFrom xs fuel k prev := by
  induction fuel generalizing k prev with
  | zero =>
      simp [memoBuildRowsFromCosted, memoBuildRowsFrom, Costed.pure]
  | succ fuel ih =>
      simp [memoBuildRowsFromCosted, memoBuildRowsFrom, ih]

@[simp] theorem memoBuildRowsFromCosted_erase
    (xs : List Int) (fuel k : Nat) (prev : List (Option Nat)) :
    Costed.erase (memoBuildRowsFromCosted xs fuel k prev) =
      memoBuildRowsFrom xs fuel k prev := by
  exact memoBuildRowsFromCosted_value xs fuel k prev

theorem memoBuildRowsFromCosted_cost
    (xs : List Int) (fuel k : Nat) (prev : List (Option Nat)) :
    (memoBuildRowsFromCosted xs fuel k prev).cost =
      memoBuildRowsFromCost xs fuel := by
  induction fuel generalizing k prev with
  | zero =>
      simp [memoBuildRowsFromCosted, memoBuildRowsFromCost, Costed.pure]
  | succ fuel ih =>
      simp [memoBuildRowsFromCosted, memoBuildRowsFromCost, ih,
        memoNextRowCosted_cost, Nat.succ_mul]
      omega

/-- The successor-row suffix has exactly the requested number of rows. -/
theorem memoBuildRowsFrom_length
    (xs : List Int) (fuel k : Nat) (prev : List (Option Nat)) :
    (memoBuildRowsFrom xs fuel k prev).length = fuel := by
  induction fuel generalizing k prev with
  | zero =>
      simp [memoBuildRowsFrom]
  | succ fuel ih =>
      simp [memoBuildRowsFrom, ih]

/-- Starting from an exact sparse row, the memoized suffix contains exact sparse rows. -/
theorem memoBuildRowsFrom_get?_sparseRow_of_lt
    (xs : List Int) (fuel k j : Nat) (h : j < fuel) :
    (memoBuildRowsFrom xs fuel k (sparseRow xs k))[j]? =
      some (sparseRow xs (k + 1 + j)) := by
  induction fuel generalizing k j with
  | zero =>
      omega
  | succ fuel ih =>
      cases j with
      | zero =>
          simp [memoBuildRowsFrom, memoNextRow_sparseRow]
      | succ j =>
          have hj : j < fuel := by omega
          have hget := ih (k + 1) j hj
          have hrow :
              memoNextRow xs k (sparseRow xs k) = sparseRow xs (k + 1) :=
            memoNextRow_sparseRow xs k
          simp [memoBuildRowsFrom, hrow]
          have hidx : (k + 1) + 1 + j = k + 1 + (j + 1) := by
            omega
          simpa [hidx] using hget

/-- Memoized sparse-table build with only the textbook log-sized row prefix. -/
def memoBuildSparseTable (xs : List Int) : List (List (Option Nat)) :=
  if memoRowCount xs = 0 then
    []
  else
    let base := sparseRow xs 0
    base :: memoBuildRowsFrom xs (memoRowCount xs - 1) 0 base

/-- Costed memoized sparse-table build. -/
def memoBuildSparseTableCosted
    (xs : List Int) : Costed (List (List (Option Nat))) :=
  if memoRowCount xs = 0 then
    Costed.tickValue 0 []
  else
    Costed.bind (memoBaseRowCosted xs) fun base =>
      Costed.bind (memoBuildRowsFromCosted xs (memoRowCount xs - 1) 0 base)
        fun rows =>
          Costed.pure (base :: rows)

@[simp] theorem memoBuildSparseTableCosted_value (xs : List Int) :
    (memoBuildSparseTableCosted xs).value = memoBuildSparseTable xs := by
  unfold memoBuildSparseTableCosted memoBuildSparseTable
  by_cases h : memoRowCount xs = 0
  · simp [h]
  · simp [h]

@[simp] theorem memoBuildSparseTableCosted_erase (xs : List Int) :
    Costed.erase (memoBuildSparseTableCosted xs) = memoBuildSparseTable xs := by
  exact memoBuildSparseTableCosted_value xs

theorem memoBuildSparseTableCosted_cost (xs : List Int) :
    (memoBuildSparseTableCosted xs).cost = memoBuildSparseTableCost xs := by
  unfold memoBuildSparseTableCosted memoBuildSparseTableCost
  by_cases h : memoRowCount xs = 0
  · simp [h]
  · simp [h, memoBuildRowsFromCosted_cost, memoBuildRowsFromCost,
      memoBaseRowCosted_cost]

theorem memoBuildSparseTableCosted_run (xs : List Int) :
    Costed.run (memoBuildSparseTableCosted xs) =
      (memoBuildSparseTable xs, memoBuildSparseTableCost xs) := by
  simp [Costed.run, memoBuildSparseTableCosted_value,
    memoBuildSparseTableCosted_cost]

/-- The memoized table has exactly `memoRowCount xs` rows. -/
theorem memoBuildSparseTable_length (xs : List Int) :
    (memoBuildSparseTable xs).length = memoRowCount xs := by
  unfold memoBuildSparseTable
  by_cases h : memoRowCount xs = 0
  · simp [h]
  · have hpos : 0 < memoRowCount xs := Nat.pos_of_ne_zero h
    simp [h, memoBuildRowsFrom_length]
    omega

/-- The memoized table returns the same sparse row at every materialized level. -/
theorem tableRow_memoBuildSparseTable_eq_sparseRow
    (xs : List Int) (k : Nat) (hk : k < memoRowCount xs) :
    tableRow (memoBuildSparseTable xs) k = sparseRow xs k := by
  unfold tableRow memoBuildSparseTable
  by_cases hzero : memoRowCount xs = 0
  · omega
  · rw [if_neg hzero]
    cases k with
    | zero =>
        simp
    | succ k =>
        have hk_tail : k < memoRowCount xs - 1 := by
          omega
        have hget :=
          memoBuildRowsFrom_get?_sparseRow_of_lt
            xs (memoRowCount xs - 1) 0 k hk_tail
        simp at hget
        change
          (match
            (sparseRow xs 0 ::
              memoBuildRowsFrom xs (memoRowCount xs - 1) 0
                (sparseRow xs 0))[k + 1]? with
          | some row => row
          | none => []) = sparseRow xs (k + 1)
        simp only [List.getElem?_cons_succ]
        rw [hget]
        have hidx : 1 + k = k + 1 := by
          omega
        simp [hidx]

/-- Logarithm monotonicity in the form needed for query-level coverage. -/
theorem log2_le_log2_of_le
    {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0) (hle : m <= n) :
    Nat.log2 m <= Nat.log2 n := by
  have hpow : 2 ^ Nat.log2 m <= n :=
    Nat.le_trans (Nat.log2_self_le hm) hle
  exact (Nat.le_log2 hn).mpr hpow

/-- Every valid query level is present in the memoized log-row table. -/
theorem queryLevel_lt_memoRowCount
    (xs : List Int) (left right : Nat) (hValid : RMQ.ValidRange xs left right) :
    Nat.log2 (right - left) < memoRowCount xs := by
  have hlen_pos : 0 < right - left := by
    omega
  have hxs_pos : 0 < xs.length := by
    omega
  have hlen_le_xs : right - left <= xs.length := by
    omega
  have hlog :
      Nat.log2 (right - left) <= Nat.log2 xs.length :=
    log2_le_log2_of_le
      (Nat.ne_of_gt hlen_pos) (Nat.ne_of_gt hxs_pos) hlen_le_xs
  unfold memoRowCount
  simp [Nat.ne_of_gt hxs_pos]
  omega

/-- Query over the memoized log-row table. -/
def memoQuery (xs : List Int) (left right : Nat) : Option Nat :=
  queryFromTable xs (memoBuildSparseTable xs) left right

/-- The memoized table is extensionally equivalent to the original sparse query. -/
theorem memoQuery_eq_query
    (xs : List Int) (left right : Nat) :
    memoQuery xs left right = query xs left right := by
  unfold memoQuery query queryFromTable
  by_cases hValid : RMQ.ValidRange xs left right
  · rw [dif_pos hValid, dif_pos hValid]
    let len := right - left
    let k := Nat.log2 len
    have hk_memo : k < memoRowCount xs := by
      simpa [k, len] using queryLevel_lt_memoRowCount xs left right hValid
    have hk_old : k <= xs.length := by
      have hlog : k <= len := by
        unfold k
        exact Nat.log2_le_self len
      unfold len at hlog
      omega
    have hrow_memo :
        tableRow (memoBuildSparseTable xs) k = sparseRow xs k :=
      tableRow_memoBuildSparseTable_eq_sparseRow xs k hk_memo
    have hrow_old :
        tableRow (buildSparseTable xs) k = sparseRow xs k :=
      tableRow_build_eq_sparseRow xs k hk_old
    simp [k, len, hrow_memo, hrow_old]
  · rw [dif_neg hValid, dif_neg hValid]

/-- Sparse table backend using the cost-faithful memoized build. -/
def memoBackend (xs : List Int) : RMQ.RMQBackend xs where
  State := List (List (Option Nat))
  build := memoBuildSparseTable xs
  query := fun table => queryFromTable xs table
  sound := by
    intro left right idx hres
    have hmemo : memoQuery xs left right = some idx := by
      simpa [memoQuery] using hres
    have hquery : query xs left right = some idx := by
      rw [← memoQuery_eq_query xs left right]
      exact hmemo
    exact query_sound hquery
  complete := by
    intro left right idx harg
    have hquery : query xs left right = some idx := query_complete harg
    have hmemo : memoQuery xs left right = some idx := by
      rw [memoQuery_eq_query]
      exact hquery
    simpa [memoQuery] using hmemo
  invalid_none := by
    intro left right hbad
    have hquery : query xs left right = none := invalid_none hbad
    have hmemo : memoQuery xs left right = none := by
      rw [memoQuery_eq_query]
      exact hquery
    simpa [memoQuery] using hmemo

end RMQ.SparseTable

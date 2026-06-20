/-!
# Reference/executable refinement helpers

This module is the small hub-facing refinement layer.  It keeps value-level
reference data explicit while packaging executable representations with an
erasure certificate.

The first reusable objects are stored sequences and matrices: value-level List
reference tables paired with Array-backed representations and erasure
certificates.  Sparse tables and Fischer-Heun summary tables use the matrix
certificate; direct-address tables can share the sequence certificate.
-/

namespace RMQ

namespace Refine

/--
Concrete stored sequence refining a List-level reference sequence.

The `abs` parameter is the mathematical sequence used by correctness proofs;
the `repr` field is the executable Array-backed representation used by traced
queries.  The erasure certificate is intentionally the one-dimensional analogue
of `StoredMatrix.erases`.
-/
structure StoredSeq (alpha : Type u) (abs : List alpha) where
  repr : Array alpha
  erases : repr.toList = abs

namespace StoredSeq

/-- Canonical Array materialization of a List sequence. -/
def ofList (abs : List alpha) : StoredSeq alpha abs where
  repr := abs.toArray
  erases := by
    simp

@[simp] theorem ofList_repr (abs : List alpha) :
    (ofList abs).repr = abs.toArray := by
  rfl

@[simp] theorem ofList_erases (abs : List alpha) :
    (ofList abs).repr.toList = abs := by
  exact (ofList abs).erases

theorem erases_eq {abs : List alpha}
    (table : StoredSeq alpha abs) :
    table.repr.toList = abs :=
  table.erases

/-- Read from the executable sequence representation. -/
def get? {abs : List alpha}
    (table : StoredSeq alpha abs) (i : Nat) : Option alpha :=
  table.repr[i]?

/-- Reference read from the abstract List sequence. -/
def absGet? (abs : List alpha) (i : Nat) : Option alpha :=
  abs[i]?

/--
Stored sequence reads agree with abstract List reads.

This is the one-dimensional refinement fact used by direct-address Array
representations whose reference behavior remains List-based.
-/
theorem get?_eq_absGet?
    {abs : List alpha} (table : StoredSeq alpha abs) (i : Nat) :
    get? table i = absGet? abs i := by
  unfold get? absGet?
  have hget : table.repr.toList[i]? = abs[i]? := by
    rw [table.erases]
  simpa using hget

end StoredSeq

/--
Concrete stored matrix refining a list-of-lists reference table.

The `abs` parameter is the mathematical table used by correctness proofs; the
`repr` field is the executable Array-backed representation used by traced
queries.  Keeping the abstraction relation as a one-field certificate makes the
usual refinement step explicit without changing existing List-level specs.
-/
structure StoredMatrix (alpha : Type u) (abs : List (List alpha)) where
  repr : Array (Array alpha)
  erases : repr.toList.map Array.toList = abs

namespace StoredMatrix

/-- Canonical Array materialization of a list-of-lists table. -/
def ofList (abs : List (List alpha)) : StoredMatrix alpha abs where
  repr := (abs.map List.toArray).toArray
  erases := by
    induction abs with
    | nil =>
        rfl
    | cons _ rows ih =>
        simp [ih]

@[simp] theorem ofList_repr (abs : List (List alpha)) :
    (ofList abs).repr = (abs.map List.toArray).toArray := by
  rfl

@[simp] theorem ofList_erases (abs : List (List alpha)) :
    (ofList abs).repr.toList.map Array.toList = abs := by
  exact (ofList abs).erases

theorem erases_eq {abs : List (List alpha)}
    (table : StoredMatrix alpha abs) :
    table.repr.toList.map Array.toList = abs :=
  table.erases

@[simp] theorem ofList_heq_of_eq
    {abs abs' : List (List alpha)} (h : abs = abs') :
    HEq (ofList abs) (ofList abs') := by
  cases h
  rfl

/-- Read a concrete stored row from the executable representation. -/
def row? {abs : List (List alpha)}
    (table : StoredMatrix alpha abs) (i : Nat) : Option (Array alpha) :=
  table.repr[i]?

/-- Reference row read from the abstract table. -/
def absRow? (abs : List (List alpha)) (i : Nat) : Option (List alpha) :=
  abs[i]?

/--
Stored row erasure agrees with the abstract row read.

This is the reusable refinement fact behind sparse-table row reads and any
other Array-backed matrix representation that keeps a List-level reference
semantics.
-/
theorem row?_map_toList_eq_absRow?
    {abs : List (List alpha)} (table : StoredMatrix alpha abs) (i : Nat) :
    (row? table i).map Array.toList = absRow? abs i := by
  unfold row? absRow?
  have hget :
      (table.repr.toList.map Array.toList)[i]? = abs[i]? := by
    rw [table.erases]
  simpa [List.getElem?_map] using hget

theorem absRow?_eq_some_of_row?
    {abs : List (List alpha)} {table : StoredMatrix alpha abs}
    {i : Nat} {row : Array alpha}
    (hrow : row? table i = some row) :
    absRow? abs i = some row.toList := by
  have h := row?_map_toList_eq_absRow? table i
  simpa [hrow] using h.symm

theorem absRow?_eq_none_of_row?
    {abs : List (List alpha)} {table : StoredMatrix alpha abs}
    {i : Nat}
    (hrow : row? table i = none) :
    absRow? abs i = none := by
  have h := row?_map_toList_eq_absRow? table i
  simpa [hrow] using h.symm

/-- Missing stored rows and missing abstract rows agree under empty-row defaults. -/
theorem row?_getD_toList_eq_absRow?_getD
    {abs : List (List alpha)} (table : StoredMatrix alpha abs) (i : Nat) :
    ((row? table i).getD #[]).toList =
      (absRow? abs i).getD [] := by
  cases hrow : row? table i with
  | none =>
      have habs := absRow?_eq_none_of_row? (table := table) hrow
      simp [habs]
  | some row =>
      have habs := absRow?_eq_some_of_row? (table := table) hrow
      simp [habs]

/-- Concrete cell read through the executable matrix representation. -/
def cell? {abs : List (List alpha)}
    (table : StoredMatrix alpha abs) (i j : Nat) : Option alpha :=
  match row? table i with
  | some row => row[j]?
  | none => none

/-- Reference cell read through the abstract list-of-lists table. -/
def absCell? (abs : List (List alpha)) (i j : Nat) : Option alpha :=
  match absRow? abs i with
  | some row => row[j]?
  | none => none

/-- Stored matrix cell reads agree with abstract list-of-lists cell reads. -/
theorem cell?_eq_absCell?
    {abs : List (List alpha)} (table : StoredMatrix alpha abs)
    (i j : Nat) :
    cell? table i j = absCell? abs i j := by
  unfold cell? absCell?
  cases hrow : row? table i with
  | none =>
      have habs := absRow?_eq_none_of_row? (table := table) hrow
      simp [habs]
  | some row =>
      have habs := absRow?_eq_some_of_row? (table := table) hrow
      simp [habs]

/-- Stored and abstract cell reads agree under any chosen default value. -/
theorem cell?_getD_eq_absCell?_getD
    {abs : List (List alpha)} (table : StoredMatrix alpha abs)
    (i j : Nat) (default : alpha) :
    (cell? table i j).getD default =
      (absCell? abs i j).getD default := by
  rw [cell?_eq_absCell?]

end StoredMatrix

end Refine

end RMQ

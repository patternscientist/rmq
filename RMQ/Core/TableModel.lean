import RMQ.Core.Cost
import RMQ.Core.Refine

/-!
# Table and payload accounting model

This module is the first small abstraction layer between value-level reference
data and the RAM/unit-cost indexed-access model used by the cost theorems.

It deliberately does not provide an executable machine model. Instead it gives
shared names for:

* model-level unit-cost indexed reads, and
* payload-bit accounting views that distinguish counted payload from
  proof-only auxiliary fields.

Concrete list, array, packed-word, sparse-table, or microtable layers can later
refine to these interfaces without replacing the existing reference semantics.
-/

namespace RMQ

namespace TableModel

/-- Unit cost charged for a modeled indexed read. -/
def indexedReadCost : Nat := 1

/--
An abstract indexed-access object. The index type is intentionally generic so
the same wrapper can model row/cell reads, first-occurrence tables, node arrays,
or bitvector access.
-/
structure IndexedAccess (idx : Type u) (alpha : Type v) where
  get? : idx -> Option alpha

namespace IndexedAccess

/-- Costed modeled read through an indexed-access object. -/
def getCosted
    (table : IndexedAccess idx alpha) (i : idx) : Costed (Option alpha) :=
  Costed.tickValue indexedReadCost (table.get? i)

@[simp] theorem getCosted_value
    (table : IndexedAccess idx alpha) (i : idx) :
    (table.getCosted i).value = table.get? i := by
  rfl

@[simp] theorem getCosted_erase
    (table : IndexedAccess idx alpha) (i : idx) :
    (table.getCosted i).erase = table.get? i := by
  rfl

theorem getCosted_cost
    (table : IndexedAccess idx alpha) (i : idx) :
    (table.getCosted i).cost = indexedReadCost := by
  rfl

theorem getCosted_run
    (table : IndexedAccess idx alpha) (i : idx) :
    (table.getCosted i).run = (table.get? i, indexedReadCost) := by
  rfl

end IndexedAccess

/-- A finite Nat-indexed access object with a model length. -/
structure IndexedSeq (alpha : Type u) where
  length : Nat
  get? : Nat -> Option alpha

namespace IndexedSeq

/-- Reference adapter from Lean lists to the indexed-sequence model. -/
def ofList (xs : List alpha) : IndexedSeq alpha where
  length := xs.length
  get? i := xs[i]?

@[simp] theorem ofList_length (xs : List alpha) :
    (ofList xs).length = xs.length := by
  rfl

@[simp] theorem ofList_get? (xs : List alpha) (i : Nat) :
    (ofList xs).get? i = xs[i]? := by
  rfl

/-- Forget the length and view an indexed sequence as a generic access object. -/
def toAccess (seq : IndexedSeq alpha) : IndexedAccess Nat alpha where
  get? := seq.get?

/-- Costed modeled read through a finite Nat-indexed sequence. -/
def getCosted (seq : IndexedSeq alpha) (i : Nat) : Costed (Option alpha) :=
  seq.toAccess.getCosted i

@[simp] theorem getCosted_value (seq : IndexedSeq alpha) (i : Nat) :
    (seq.getCosted i).value = seq.get? i := by
  rfl

@[simp] theorem getCosted_erase (seq : IndexedSeq alpha) (i : Nat) :
    (seq.getCosted i).erase = seq.get? i := by
  rfl

theorem getCosted_cost (seq : IndexedSeq alpha) (i : Nat) :
    (seq.getCosted i).cost = indexedReadCost := by
  rfl

theorem getCosted_run (seq : IndexedSeq alpha) (i : Nat) :
    (seq.getCosted i).run = (seq.get? i, indexedReadCost) := by
  rfl

theorem ofList_getCosted_run (xs : List alpha) (i : Nat) :
    ((ofList xs).getCosted i).run = (xs[i]?, indexedReadCost) := by
  rfl

end IndexedSeq

/-- Compatibility alias for the hub-level stored-sequence refinement certificate. -/
abbrev StoredSeq (alpha : Type u) (abs : List alpha) :=
  RMQ.Refine.StoredSeq alpha abs

namespace StoredSeq

/-- Canonical Array materialization of a list-backed sequence. -/
def ofList (abs : List alpha) : StoredSeq alpha abs :=
  RMQ.Refine.StoredSeq.ofList abs

@[simp] theorem ofList_repr (abs : List alpha) :
    (ofList abs).repr = abs.toArray := by
  exact RMQ.Refine.StoredSeq.ofList_repr abs

@[simp] theorem ofList_erases (abs : List alpha) :
    (ofList abs).repr.toList = abs := by
  exact RMQ.Refine.StoredSeq.ofList_erases abs

theorem erases_eq {abs : List alpha}
    (table : StoredSeq alpha abs) :
    table.repr.toList = abs :=
  RMQ.Refine.StoredSeq.erases_eq table

/-- Stored sequence reads agree with abstract List reads. -/
theorem get?_eq_absGet?
    {abs : List alpha} (table : StoredSeq alpha abs) (i : Nat) :
    RMQ.Refine.StoredSeq.get? table i =
      RMQ.Refine.StoredSeq.absGet? abs i :=
  RMQ.Refine.StoredSeq.get?_eq_absGet? table i

end StoredSeq

/-- Compatibility alias for the hub-level stored-matrix refinement certificate. -/
abbrev StoredMatrix (alpha : Type u) (abs : List (List alpha)) :=
  RMQ.Refine.StoredMatrix alpha abs

namespace StoredMatrix

/-- Canonical Array materialization of a list-of-lists table. -/
def ofList (abs : List (List alpha)) : StoredMatrix alpha abs :=
  RMQ.Refine.StoredMatrix.ofList abs

@[simp] theorem ofList_repr (abs : List (List alpha)) :
    (ofList abs).repr = (abs.map List.toArray).toArray := by
  exact RMQ.Refine.StoredMatrix.ofList_repr abs

@[simp] theorem ofList_erases (abs : List (List alpha)) :
    (ofList abs).repr.toList.map Array.toList = abs := by
  exact RMQ.Refine.StoredMatrix.ofList_erases abs

theorem erases_eq {abs : List (List alpha)}
    (table : StoredMatrix alpha abs) :
    table.repr.toList.map Array.toList = abs :=
  RMQ.Refine.StoredMatrix.erases_eq table

@[simp] theorem ofList_heq_of_eq
    {abs abs' : List (List alpha)} (h : abs = abs') :
    HEq (ofList abs) (ofList abs') := by
  exact RMQ.Refine.StoredMatrix.ofList_heq_of_eq h

end StoredMatrix

/--
A payload-accounting view of a state.

`payloadBits` is the serialized semantic payload used in lower-bound and
space-accounting statements. `payloadBitCount` is the charged bit budget. The
inequality permits packed-word padding and side conditions while still making
the counted field explicit.
-/
structure PayloadView (state : Type u) where
  payloadBits : state -> List Bool
  payloadBitCount : state -> Nat
  payload_length_le :
    forall s, (payloadBits s).length <= payloadBitCount s

namespace PayloadView

/-- Exact payload view where the charged count is the serialized length. -/
def exact (payloadBits : state -> List Bool) : PayloadView state where
  payloadBits := payloadBits
  payloadBitCount s := (payloadBits s).length
  payload_length_le := by
    intro s
    exact Nat.le_refl _

@[simp] theorem exact_payloadBitCount
    (payloadBits : state -> List Bool) (s : state) :
    (exact payloadBits).payloadBitCount s = (payloadBits s).length := by
  rfl

theorem payloadBits_length_le
    (view : PayloadView state) (s : state) :
    (view.payloadBits s).length <= view.payloadBitCount s :=
  view.payload_length_le s

/--
Add proof-only or auxiliary data to a state without changing the counted
payload view.
-/
def withUnchargedAux
    (view : PayloadView state) (aux : state -> Type v) :
    PayloadView (Sigma aux) where
  payloadBits s := view.payloadBits s.1
  payloadBitCount s := view.payloadBitCount s.1
  payload_length_le := by
    intro s
    exact view.payload_length_le s.1

@[simp] theorem withUnchargedAux_payloadBits
    (view : PayloadView state) (aux : state -> Type v)
    (s : Sigma aux) :
    (view.withUnchargedAux aux).payloadBits s = view.payloadBits s.1 := by
  rfl

@[simp] theorem withUnchargedAux_payloadBitCount
    (view : PayloadView state) (aux : state -> Type v)
    (s : Sigma aux) :
    (view.withUnchargedAux aux).payloadBitCount s =
      view.payloadBitCount s.1 := by
  rfl

end PayloadView

end TableModel

end RMQ

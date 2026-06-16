import RMQ.Core.Cost
import RMQ.Core.Microtable

/-!
# Costed RMQ kernels

This module attaches the lightweight `Costed` carrier to the first concrete
RMQ kernels. The theorems here are erasure/cost facts only: they do not change
the value-correctness contracts in the implementation modules.
-/

namespace RMQ

/--
Costed version of `scanWindow`.

The cost counts one unit for each extension/comparison after the first element,
so a window of length `len` costs `len - 1`.
-/
def scanWindowCosted (xs : List Int) (start : Nat) : Nat -> Costed Nat
  | 0 => Costed.tickValue 0 start
  | 1 => Costed.tickValue 0 start
  | len + 2 =>
      Costed.bind (scanWindowCosted xs start (len + 1)) fun best =>
        Costed.tickValue 1 (betterIndex xs best (start + len + 1))

@[simp] theorem scanWindowCosted_value
    (xs : List Int) (start len : Nat) :
    (scanWindowCosted xs start len).value = scanWindow xs start len := by
  induction len with
  | zero =>
      simp [scanWindowCosted, scanWindow]
  | succ len ih =>
      cases len with
      | zero =>
          simp [scanWindowCosted, scanWindow]
      | succ len =>
          simp [scanWindowCosted, scanWindow, ih]

@[simp] theorem scanWindowCosted_erase
    (xs : List Int) (start len : Nat) :
    Costed.erase (scanWindowCosted xs start len) = scanWindow xs start len := by
  exact scanWindowCosted_value xs start len

theorem scanWindowCosted_cost
    (xs : List Int) (start len : Nat) :
    (scanWindowCosted xs start len).cost = len - 1 := by
  induction len with
  | zero =>
      simp [scanWindowCosted]
  | succ len ih =>
      cases len with
      | zero =>
          simp [scanWindowCosted]
      | succ len =>
          simp [scanWindowCosted, ih]

theorem scanWindowCosted_run
    (xs : List Int) (start len : Nat) :
    Costed.run (scanWindowCosted xs start len) =
      (scanWindow xs start len, len - 1) := by
  simp [Costed.run, scanWindowCosted_value, scanWindowCosted_cost]

theorem scanWindowCosted_leftmost
    (xs : List Int) (start len : Nat)
    (hlen : 0 < len) (hbound : start + len <= xs.length) :
    LeftmostArgMin xs start (start + len)
      (Costed.erase (scanWindowCosted xs start len)) := by
  simpa using scanWindow_leftmost xs start len hlen hbound

namespace Cartesian

namespace CartesianShape

/--
Costed version of `CartesianShape.queryOffset?`.

The cost counts one unit for every shape node (or empty leaf) inspected along
the recursive decision path.
-/
def queryOffsetCosted? : CartesianShape -> Nat -> Nat -> Costed (Option Nat)
  | empty, _left, _right => Costed.tickValue 1 none
  | node leftShape rightShape, left, right =>
      let pivot := leftShape.size
      let size := leftShape.size + 1 + rightShape.size
      if _hvalid : left < right /\ right <= size then
        if _hright_left : right <= pivot then
          Costed.bind (Costed.tick 1) fun _ =>
            queryOffsetCosted? leftShape left right
        else if _hroot_left : pivot < left then
          Costed.bind (Costed.tick 1) fun _ =>
            Costed.map
              (Option.map fun offset => pivot + 1 + offset)
              (queryOffsetCosted? rightShape
                (left - (pivot + 1)) (right - (pivot + 1)))
        else
          Costed.tickValue 1 (some pivot)
      else
        Costed.tickValue 1 none

@[simp] theorem queryOffsetCosted?_value
    (shape : CartesianShape) (left right : Nat) :
    (shape.queryOffsetCosted? left right).value =
      shape.queryOffset? left right := by
  induction shape generalizing left right with
  | empty =>
      simp [queryOffsetCosted?, queryOffset?]
  | node leftShape rightShape ihLeft ihRight =>
      simp [queryOffsetCosted?, queryOffset?]
      by_cases hvalid :
          left < right /\ right <= leftShape.size + 1 + rightShape.size
      case pos =>
        simp [hvalid]
        by_cases hleft : right <= leftShape.size
        case pos =>
          simp [hleft, ihLeft]
        case neg =>
          simp [hleft]
          by_cases hright : leftShape.size < left
          case pos =>
            simp [hright, ihRight, Costed.map_value]
          case neg =>
            simp [hright]
      case neg =>
        simp [hvalid]

@[simp] theorem queryOffsetCosted?_erase
    (shape : CartesianShape) (left right : Nat) :
    Costed.erase (shape.queryOffsetCosted? left right) =
      shape.queryOffset? left right := by
  exact queryOffsetCosted?_value shape left right

theorem queryOffsetCosted?_cost_le_size_succ
    (shape : CartesianShape) (left right : Nat) :
    (shape.queryOffsetCosted? left right).cost <= shape.size + 1 := by
  induction shape generalizing left right with
  | empty =>
      simp [queryOffsetCosted?, CartesianShape.size]
  | node leftShape rightShape ihLeft ihRight =>
      simp [queryOffsetCosted?, CartesianShape.size]
      by_cases hvalid :
          left < right /\ right <= leftShape.size + 1 + rightShape.size
      case pos =>
        simp [hvalid]
        by_cases hleft : right <= leftShape.size
        case pos =>
          have hrec := ihLeft left right
          simp [hleft]
          omega
        case neg =>
          simp [hleft]
          by_cases hright : leftShape.size < left
          case pos =>
            have hrec :=
              ihRight (left - (leftShape.size + 1))
                (right - (leftShape.size + 1))
            simp [hright, Costed.map_cost]
            omega
          case neg =>
            simp [hright]
      case neg =>
        simp [hvalid]

end CartesianShape

/-- Costed raw local microtable lookup for a concrete block signature. -/
def rawMicrotableLookupCosted
    (xs : List Int) (start blockSize left right : Nat) :
    Costed (Option Nat) :=
  (blockSignature xs start blockSize).queryOffsetCosted? left right

theorem rawMicrotableLookupCosted_value
    {xs : List Int} {start blockSize left right : Nat}
    (hbound : start + blockSize <= xs.length) :
    (rawMicrotableLookupCosted xs start blockSize left right).value =
      if _hvalid : LocalValid blockSize left right then
        some (localScanOffset xs start left right)
      else
        none := by
  unfold rawMicrotableLookupCosted
  rw [CartesianShape.queryOffsetCosted?_value]
  exact queryOffset?_blockSignature hbound

theorem rawMicrotableLookupCosted_erase
    {xs : List Int} {start blockSize left right : Nat}
    (hbound : start + blockSize <= xs.length) :
    Costed.erase
        (rawMicrotableLookupCosted xs start blockSize left right) =
      if _hvalid : LocalValid blockSize left right then
        some (localScanOffset xs start left right)
      else
        none := by
  exact rawMicrotableLookupCosted_value hbound

theorem rawMicrotableLookupCosted_cost_le
    (xs : List Int) (start blockSize left right : Nat) :
    (rawMicrotableLookupCosted xs start blockSize left right).cost <=
      blockSize + 1 := by
  unfold rawMicrotableLookupCosted
  have hcost :=
    CartesianShape.queryOffsetCosted?_cost_le_size_succ
      (blockSignature xs start blockSize) left right
  have hsize :=
    ShapeOfSize.size_eq (blockSignature_shapeOfSize xs start blockSize)
  omega

end Cartesian

end RMQ

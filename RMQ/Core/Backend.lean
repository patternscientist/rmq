import RMQ.Core.Window

/-!
# RMQ backend interface

The backend interface is intentionally explicit. A backend fixes a list, has a
build state, and exposes soundness, completeness, and invalid-query rejection
against `LeftmostArgMin`.
-/

namespace RMQ

structure RMQBackend (xs : List Int) where
  State : Type
  build : State
  query : State -> Nat -> Nat -> Option Nat
  sound :
    forall {left right idx},
      query build left right = some idx ->
        LeftmostArgMin xs left right idx
  complete :
    forall {left right idx},
      LeftmostArgMin xs left right idx ->
        query build left right = some idx
  invalid_none :
    forall {left right},
      Not (ValidRange xs left right) ->
        query build left right = none

namespace RMQBackend

/-- Query a backend using its canonical built state. -/
def queryBuilt {xs : List Int} (backend : RMQBackend xs) (left right : Nat) :
    Option Nat :=
  backend.query backend.build left right

/--
Any two built backends for the same list are extensionally equal.

Completeness forces every valid query to return the direct-scan leftmost
minimum witness, while invalid-query rejection forces every invalid query to
return `none`.
-/
theorem queryBuilt_eq {xs : List Int}
    (backendA backendB : RMQBackend xs) (left right : Nat) :
    queryBuilt backendA left right = queryBuilt backendB left right := by
  by_cases hValid : ValidRange xs left right
  · let len := right - left
    have hlen : 0 < len := by
      unfold len
      omega
    have hbound : left + len <= xs.length := by
      unfold len
      omega
    have hright : left + len = right := by
      unfold len
      omega
    have harg_scan := scanWindow_leftmost xs left len hlen hbound
    have harg :
        LeftmostArgMin xs left right (scanWindow xs left len) := by
      simpa [hright] using harg_scan
    have hA := backendA.complete harg
    have hB := backendB.complete harg
    unfold queryBuilt
    rw [hA, hB]
  · have hA := backendA.invalid_none hValid
    have hB := backendB.invalid_none hValid
    unfold queryBuilt
    rw [hA, hB]

end RMQBackend

end RMQ

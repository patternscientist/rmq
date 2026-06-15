import RMQ.Core.Spec

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

end RMQBackend

end RMQ


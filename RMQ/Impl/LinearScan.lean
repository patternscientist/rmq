import RMQ.Core.Backend
import RMQ.Core.Window

/-!
# Linear-scan RMQ backend

The first concrete backend is the simplest one: every valid query scans the
requested half-open window and returns the leftmost minimum index.
-/

namespace RMQ.LinearScan

/-- Functional linear-scan query. Invalid or empty ranges return `none`. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  if _h : RMQ.ValidRange xs left right then
    some (RMQ.scanWindow xs left (right - left))
  else
    none

theorem query_valid_exact
    (xs : List Int) (left right : Nat) (hValid : RMQ.ValidRange xs left right) :
    exists idx, query xs left right = some idx /\
      RMQ.LeftmostArgMin xs left right idx := by
  unfold query
  let len := right - left
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= xs.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have hscan := RMQ.scanWindow_leftmost xs left len hlen hbound
  refine ⟨RMQ.scanWindow xs left len, ?_, ?_⟩
  · simp [hValid, len]
  · simpa [len, hright] using hscan

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
  · unfold query at hres
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
  unfold query
  simp [hbad]

/-- Linear scan as an explicit `RMQBackend`. -/
def backend (xs : List Int) : RMQ.RMQBackend xs where
  State := Unit
  build := ()
  query := fun _ => query xs
  sound := by
    intro left right idx hres
    exact query_sound hres
  complete := by
    intro left right idx harg
    exact query_complete harg
  invalid_none := by
    intro left right hbad
    exact invalid_none hbad

example : query [5, 2, 7, 1, 3] 1 4 = some 3 := by decide
example : query [4, 1, 1, 2] 0 4 = some 1 := by decide
example : query [5, 2, 7] 2 2 = none := by decide

end RMQ.LinearScan


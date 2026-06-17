import RMQ.Core.PlusMinusOne
import RMQ.Impl.LinearScan

/-!
# First plus-minus-one RMQ backend

This module gives the initial verified instance of the plus-minus-one RMQ
package.  The implementation is deliberately conservative: it reuses the
already verified linear scan backend, while the `PlusMinusOne.Backend` wrapper
records the adjacent-depth invariant for future specialized backends.
-/

namespace RMQ

namespace PlusMinusOne

/-- A verified plus-minus-one backend implemented by direct linear scan. -/
def linearScanBackend (input : Input) : Backend input where
  rmq := RMQ.LinearScan.backend input.depths

/-- Functional query for the first plus-minus-one backend instance. -/
def query (input : Input) (left right : Nat) : Option Nat :=
  Backend.queryBuilt (linearScanBackend input) left right

theorem query_sound
    {input : Input} {left right idx : Nat}
    (hres : query input left right = some idx) :
    LeftmostArgMin input.depths left right idx := by
  exact Backend.queryBuilt_sound (linearScanBackend input) hres

theorem query_complete
    {input : Input} {left right idx : Nat}
    (harg : LeftmostArgMin input.depths left right idx) :
    query input left right = some idx := by
  exact Backend.queryBuilt_complete (linearScanBackend input) harg

theorem query_invalid_none
    {input : Input} {left right : Nat}
    (hbad : Not (ValidRange input.depths left right)) :
    query input left right = none := by
  exact Backend.queryBuilt_invalid_none (linearScanBackend input) hbad

/-- Euler traces immediately instantiate the plus-minus-one linear backend. -/
def linearScanBackendOfEulerTrace (trace : EulerTrace) :
    Backend (Input.ofEulerTrace trace) :=
  linearScanBackend (Input.ofEulerTrace trace)

/-- Generated rose-tree Euler traces immediately instantiate the backend. -/
def linearScanBackendOfRoseTree (tree : RoseTree) :
    Backend (Input.ofRoseTree tree) :=
  linearScanBackend (Input.ofRoseTree tree)

end PlusMinusOne

end RMQ

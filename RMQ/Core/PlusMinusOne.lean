import RMQ.Core.LCA

/-!
# Plus-minus-one RMQ inputs

This module packages the Euler-depth invariant as a first-class RMQ input
class.  A plus-minus-one input is still queried through the ordinary RMQ
contract, but it carries the extra adjacent-depth fact needed by specialized
RMQ algorithms and, later, succinct encodings.
-/

namespace RMQ

namespace PlusMinusOne

/-- Depth lists whose adjacent entries differ by exactly one. -/
def IsDepthTrace (depths : List Int) : Prop :=
  AdjacentDepthsDifferByOne depths

/-- A fixed RMQ input carrying the plus-minus-one adjacent-depth invariant. -/
structure Input where
  depths : List Int
  adjacent : IsDepthTrace depths

namespace Input

/-- Package an existing Euler trace as a plus-minus-one RMQ input. -/
def ofEulerTrace (trace : EulerTrace) : Input where
  depths := trace.depths
  adjacent := trace.adjacent_depths

theorem ofEulerTrace_depths (trace : EulerTrace) :
    (ofEulerTrace trace).depths = trace.depths := by
  rfl

theorem ofEulerTrace_adjacent (trace : EulerTrace) :
    IsDepthTrace (ofEulerTrace trace).depths := by
  exact (ofEulerTrace trace).adjacent

/-- Package the generated Euler-depth trace of a rose tree. -/
def ofRoseTree (tree : RoseTree) : Input :=
  ofEulerTrace tree.eulerTrace

theorem ofRoseTree_depths (tree : RoseTree) :
    (ofRoseTree tree).depths = tree.eulerTrace.depths := by
  rfl

theorem ofRoseTree_depths_eq_eulerDepths (tree : RoseTree) :
    (ofRoseTree tree).depths = tree.eulerDepths := by
  rfl

theorem ofRoseTree_adjacent (tree : RoseTree) :
    IsDepthTrace (ofRoseTree tree).depths := by
  exact (ofRoseTree tree).adjacent

theorem roseTree_eulerDepths_are_trace (tree : RoseTree) :
    IsDepthTrace tree.eulerDepths := by
  exact tree.eulerDepths_adjacent

end Input

/--
A verified plus-minus-one RMQ backend.

The backend is intentionally just an exact `RMQBackend` over an input that also
carries the plus-minus-one invariant.  Specialized implementations can expose
the same structure, while generic RMQ/LCA code can forget the invariant via
`toRMQBackend`.
-/
structure Backend (input : Input) where
  rmq : RMQBackend input.depths

namespace Backend

/-- Forget the plus-minus-one invariant and use the underlying RMQ backend. -/
def toRMQBackend {input : Input} (backend : Backend input) :
    RMQBackend input.depths :=
  backend.rmq

/-- Query a plus-minus-one backend using its canonical built state. -/
def queryBuilt {input : Input} (backend : Backend input)
    (left right : Nat) : Option Nat :=
  RMQBackend.queryBuilt backend.rmq left right

theorem queryBuilt_sound
    {input : Input} (backend : Backend input) {left right idx : Nat}
    (hres : queryBuilt backend left right = some idx) :
    LeftmostArgMin input.depths left right idx := by
  exact backend.rmq.sound hres

theorem queryBuilt_complete
    {input : Input} (backend : Backend input) {left right idx : Nat}
    (harg : LeftmostArgMin input.depths left right idx) :
    queryBuilt backend left right = some idx := by
  exact backend.rmq.complete harg

theorem queryBuilt_invalid_none
    {input : Input} (backend : Backend input) {left right : Nat}
    (hbad : Not (ValidRange input.depths left right)) :
    queryBuilt backend left right = none := by
  exact backend.rmq.invalid_none hbad

theorem queryBuilt_eq
    {input : Input} (leftBackend rightBackend : Backend input)
    (left right : Nat) :
    queryBuilt leftBackend left right =
      queryBuilt rightBackend left right := by
  exact RMQBackend.queryBuilt_eq
    leftBackend.rmq rightBackend.rmq left right

end Backend

end PlusMinusOne

end RMQ

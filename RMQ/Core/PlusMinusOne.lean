import RMQ.Core.LCA
import RMQ.Core.Microtable

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

/-- A delta bit encodes whether the next depth is one higher or one lower. -/
def stepValue (up : Bool) : Int :=
  if up then 1 else -1

/-- Convert a concrete adjacent pair into a delta bit. -/
def stepBit (current next : Int) : Bool :=
  next = current + 1

/--
Replay a delta signature from a starting depth.  The result includes the
starting depth, so a signature with `k` deltas describes a block of `k + 1`
depth values.
-/
def traceFromSignatureAt (start : Int) : List Bool -> List Int
  | [] => [start]
  | up :: rest => start :: traceFromSignatureAt (start + stepValue up) rest

/-- Normalized depth block represented by a plus-minus-one delta signature. -/
def traceFromSignature (signature : List Bool) : List Int :=
  traceFromSignatureAt 0 signature

theorem traceFromSignatureAt_length (start : Int) (signature : List Bool) :
    (traceFromSignatureAt start signature).length = signature.length + 1 := by
  induction signature generalizing start with
  | nil =>
      simp [traceFromSignatureAt]
  | cons up rest ih =>
      simp [traceFromSignatureAt, ih]

theorem traceFromSignature_length (signature : List Bool) :
    (traceFromSignature signature).length = signature.length + 1 := by
  exact traceFromSignatureAt_length 0 signature

theorem traceFromSignatureAt_adjacent
    (start : Int) (signature : List Bool) :
    AdjacentDepthsDifferByOne (traceFromSignatureAt start signature) := by
  induction signature generalizing start with
  | nil =>
      simp [traceFromSignatureAt, AdjacentDepthsDifferByOne]
  | cons up rest ih =>
      cases rest with
      | nil =>
          cases up <;>
            simp [traceFromSignatureAt, AdjacentDepthsDifferByOne, stepValue] <;>
            omega
      | cons next more =>
          have htail :=
            ih (start + stepValue up)
          cases up
          case false =>
            simp [traceFromSignatureAt, stepValue] at htail
            simp [traceFromSignatureAt, AdjacentDepthsDifferByOne,
              stepValue]
            constructor
            case left =>
              omega
            case right =>
              exact htail
          case true =>
            simp [traceFromSignatureAt, stepValue] at htail
            simp [traceFromSignatureAt, AdjacentDepthsDifferByOne,
              stepValue, htail]

theorem traceFromSignature_adjacent (signature : List Bool) :
    IsDepthTrace (traceFromSignature signature) := by
  exact traceFromSignatureAt_adjacent 0 signature

/--
Read the delta signature of a concrete block.  The function is total; callers
use bounds and adjacency hypotheses when they need semantic guarantees.
-/
def blockDeltaSignature (depths : List Int) (start : Nat) : Nat -> List Bool
  | 0 => []
  | 1 => []
  | len + 2 =>
      let current := depths.getD start 0
      let next := depths.getD (start + 1) current
      stepBit current next ::
        blockDeltaSignature depths (start + 1) (len + 1)

theorem blockDeltaSignature_length
    (depths : List Int) (start len : Nat) :
    (blockDeltaSignature depths start len).length = len - 1 := by
  induction len generalizing start with
  | zero =>
      simp [blockDeltaSignature]
  | succ len ih =>
      cases len with
      | zero =>
          simp [blockDeltaSignature]
      | succ len =>
          simp [blockDeltaSignature, ih]

/--
Certified local table for plus-minus-one delta signatures.

The table is exact for the normalized trace represented by the signature.  A
future packed implementation can materialize the same function over bit-coded
signatures; clients only need this contract.
-/
structure SignatureTable where
  queryOffset? : List Bool -> Nat -> Nat -> Option Nat
  exact :
    forall {signature : List Bool} {left right : Nat},
      queryOffset? signature left right =
        if _hvalid : Cartesian.LocalValid (signature.length + 1) left right then
          some (Cartesian.localScanOffset
            (traceFromSignature signature) 0 left right)
        else
          none

namespace SignatureTable

/-- The canonical table computes the normalized local scan directly. -/
def raw : SignatureTable where
  queryOffset? signature left right :=
    if _hvalid : Cartesian.LocalValid (signature.length + 1) left right then
      some (Cartesian.localScanOffset
        (traceFromSignature signature) 0 left right)
    else
      none
  exact := by
    intro signature left right
    rfl

/-- Query a normalized signature block and return an offset in that block. -/
def queryIndex? (table : SignatureTable)
    (signature : List Bool) (left right : Nat) : Option Nat :=
  table.queryOffset? signature left right

theorem queryIndex?_eq (table : SignatureTable)
    {signature : List Bool} {left right : Nat} :
    table.queryIndex? signature left right =
      if _hvalid : Cartesian.LocalValid (signature.length + 1) left right then
        some (scanWindow (traceFromSignature signature) left (right - left))
      else
        none := by
  unfold queryIndex?
  rw [table.exact]
  by_cases hvalid : Cartesian.LocalValid (signature.length + 1) left right
  case pos =>
    rw [dif_pos hvalid, dif_pos hvalid]
    have hlocal := Cartesian.localScanOffset_add_start
      (xs := traceFromSignature signature)
      (start := 0)
      (blockSize := signature.length + 1)
      (left := left)
      (right := right)
      hvalid
    simpa using hlocal
  case neg =>
    rw [dif_neg hvalid, dif_neg hvalid]

theorem queryIndex?_leftmost
    (table : SignatureTable)
    {signature : List Bool} {left right : Nat}
    (hvalid : Cartesian.LocalValid (signature.length + 1) left right) :
    exists idx,
      table.queryIndex? signature left right = some idx /\
        LeftmostArgMin (traceFromSignature signature) left right idx := by
  have hbound :
      0 + (signature.length + 1) <=
        (traceFromSignature signature).length := by
    simp [traceFromSignature_length]
  refine
    Exists.intro
      (Cartesian.localScanOffset (traceFromSignature signature) 0 left right)
      ?_
  constructor
  case left =>
    unfold queryIndex?
    rw [table.exact, dif_pos hvalid]
  case right =>
    simpa using
      Cartesian.localScanOffset_leftmost
        (xs := traceFromSignature signature)
        (start := 0)
        (blockSize := signature.length + 1)
        (left := left)
        (right := right)
        hbound hvalid

theorem queryIndex?_sound
    (table : SignatureTable)
    {signature : List Bool} {left right idx : Nat}
    (hquery : table.queryIndex? signature left right = some idx) :
    LeftmostArgMin (traceFromSignature signature) left right idx := by
  rw [queryIndex?_eq table] at hquery
  by_cases hvalid : Cartesian.LocalValid (signature.length + 1) left right
  case pos =>
    rw [dif_pos hvalid] at hquery
    simp at hquery
    have hbound :
        0 + (signature.length + 1) <=
          (traceFromSignature signature).length := by
      simp [traceFromSignature_length]
    have hscan :=
      Cartesian.localScanOffset_leftmost
        (xs := traceFromSignature signature)
        (start := 0)
        (blockSize := signature.length + 1)
        (left := left)
        (right := right)
        hbound hvalid
    have hidx := Cartesian.localScanOffset_add_start
      (xs := traceFromSignature signature)
      (start := 0)
      (blockSize := signature.length + 1)
      (left := left)
      (right := right)
      hvalid
    have hscan' :
        LeftmostArgMin (traceFromSignature signature) left right
          (scanWindow (traceFromSignature signature) left (right - left)) := by
      simpa [hidx] using hscan
    simpa [hquery] using hscan'
  case neg =>
    rw [dif_neg hvalid] at hquery
    simp at hquery

theorem queryIndex?_complete
    (table : SignatureTable)
    {signature : List Bool} {left right idx : Nat}
    (harg : LeftmostArgMin (traceFromSignature signature) left right idx) :
    table.queryIndex? signature left right = some idx := by
  rw [queryIndex?_eq table]
  have hvalid : Cartesian.LocalValid (signature.length + 1) left right := by
    have hright := harg.2.1
    rw [traceFromSignature_length] at hright
    exact And.intro harg.1 hright
  rw [dif_pos hvalid]
  have hbound :
      0 + (signature.length + 1) <=
        (traceFromSignature signature).length := by
    simp [traceFromSignature_length]
  have hscan :=
    Cartesian.localScanOffset_leftmost
      (xs := traceFromSignature signature)
      (start := 0)
      (blockSize := signature.length + 1)
      (left := left)
      (right := right)
      hbound hvalid
  have hidx := Cartesian.localScanOffset_add_start
    (xs := traceFromSignature signature)
    (start := 0)
    (blockSize := signature.length + 1)
    (left := left)
    (right := right)
    hvalid
  have hsame :
      scanWindow (traceFromSignature signature) left (right - left) = idx := by
    have hscan' :
        LeftmostArgMin (traceFromSignature signature) left right
          (scanWindow (traceFromSignature signature) left (right - left)) := by
      simpa [hidx] using hscan
    exact leftmostArgMin_unique
      (traceFromSignature signature) left right
      (scanWindow (traceFromSignature signature) left (right - left))
      idx hscan' harg
  simp [hsame]

theorem queryIndex?_invalid
    (table : SignatureTable)
    {signature : List Bool} {left right : Nat}
    (hbad : Not (Cartesian.LocalValid (signature.length + 1) left right)) :
    table.queryIndex? signature left right = none := by
  rw [queryIndex?_eq table]
  simp [hbad]

end SignatureTable

/-- A fixed RMQ input carrying the plus-minus-one adjacent-depth invariant. -/
structure Input where
  depths : List Int
  adjacent : IsDepthTrace depths

/-- The plus-minus-one input represented by a normalized delta signature. -/
def inputOfSignature (signature : List Bool) : Input where
  depths := traceFromSignature signature
  adjacent := traceFromSignature_adjacent signature

theorem inputOfSignature_depths (signature : List Bool) :
    (inputOfSignature signature).depths = traceFromSignature signature := by
  rfl

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

namespace SignatureTable

/-- A signature table gives an RMQ backend for the normalized signature trace. -/
def backend (signature : List Bool) (table : SignatureTable) :
    Backend (inputOfSignature signature) where
  rmq := {
    State := Unit
    build := ()
    query := fun _ left right => table.queryIndex? signature left right
    sound := by
      intro left right idx hquery
      exact queryIndex?_sound table hquery
    complete := by
      intro left right idx harg
      exact queryIndex?_complete table harg
    invalid_none := by
      intro left right hbad
      have hbadLocal :
          Not (Cartesian.LocalValid (signature.length + 1) left right) := by
        intro hvalid
        apply hbad
        rw [inputOfSignature_depths]
        exact And.intro hvalid.1 (by
          rw [traceFromSignature_length]
          exact hvalid.2)
      exact queryIndex?_invalid table hbadLocal
  }

/-- The canonical normalized-signature backend. -/
def rawBackend (signature : List Bool) :
    Backend (inputOfSignature signature) :=
  backend signature raw

end SignatureTable

end PlusMinusOne

end RMQ

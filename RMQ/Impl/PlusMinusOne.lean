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

/-- Verified backend for the normalized trace represented by a delta signature. -/
def signatureBackend (signature : List Bool) :
    Backend (inputOfSignature signature) :=
  SignatureTable.rawBackend signature

/-- Query the normalized trace represented by a delta signature. -/
def signatureQuery (signature : List Bool) (left right : Nat) : Option Nat :=
  Backend.queryBuilt (signatureBackend signature) left right

theorem signatureQuery_sound
    {signature : List Bool} {left right idx : Nat}
    (hres : signatureQuery signature left right = some idx) :
    LeftmostArgMin (traceFromSignature signature) left right idx := by
  exact Backend.queryBuilt_sound (signatureBackend signature) hres

theorem signatureQuery_complete
    {signature : List Bool} {left right idx : Nat}
    (harg : LeftmostArgMin (traceFromSignature signature) left right idx) :
    signatureQuery signature left right = some idx := by
  exact Backend.queryBuilt_complete (signatureBackend signature) harg

theorem signatureQuery_invalid_none
    {signature : List Bool} {left right : Nat}
    (hbad : Not (ValidRange (traceFromSignature signature) left right)) :
    signatureQuery signature left right = none := by
  exact Backend.queryBuilt_invalid_none (signatureBackend signature) hbad

theorem signatureQuery_eq_linearQuery
    (signature : List Bool) (left right : Nat) :
    signatureQuery signature left right =
      query (inputOfSignature signature) left right := by
  exact Backend.queryBuilt_eq
    (signatureBackend signature)
    (linearScanBackend (inputOfSignature signature))
    left right

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

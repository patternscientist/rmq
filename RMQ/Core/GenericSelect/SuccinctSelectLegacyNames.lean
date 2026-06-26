import RMQ.Core.GenericSelect.Primitives
import RMQ.Core.SuccinctSelect

/-!
# Generic select legacy bridges for historical SuccinctSelect names

Terminal compatibility aliases/equations for old false-select helper names
exported by `RMQ.SuccinctSelect`. New generic-select code should use the
target-threaded helpers in `RMQ.GenericSelect` or the neutral helper names in
`RMQ.SuccinctSelect`.
-/

namespace RMQ.GenericSelect

open RMQ.SuccinctSelect

/-- The BP-specialised primitive is the `target := false` instance. -/
theorem denseTwoWordFalseSelectCosted_eq
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    SuccinctSelect.denseTwoWordFalseSelectCosted
        bitWords basePosition baseOccurrence q =
      denseTwoWordSelectCosted false bitWords basePosition baseOccurrence q :=
  rfl

theorem falseSelectPositions_eq (bits : List Bool) (base count : Nat) :
    SuccinctSelect.falseSelectPositions bits base count =
      selectPositions false bits base count :=
  rfl

theorem falseSelectRelativeOffsetsOrZero_eq
    (bits : List Bool) (baseOccurrence count endOccurrence basePosition : Nat) :
    SuccinctSelect.falseSelectRelativeOffsetsOrZero
        bits baseOccurrence count endOccurrence basePosition =
      relativeOffsetsOrZero false bits baseOccurrence count endOccurrence
        basePosition :=
  rfl

end RMQ.GenericSelect

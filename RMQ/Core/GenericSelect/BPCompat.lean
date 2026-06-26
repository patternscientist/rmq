import RMQ.Core.GenericSelect.Family
import RMQ.Core.SuccinctSelect

/-!
# BP compatibility facts for generic select

This module keeps the `shape.bpCode`, `target := false` bridge facts above the
plain bitvector generic-select core.
-/

namespace RMQ.GenericSelect

open RMQ.SuccinctSelect

/-- The BP `false`-specialised occurrence count is the `target := false`
instance over `shape.bpCode`. -/
theorem falseSelectOccurrenceCount_eq (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape = occurrenceCount shape.bpCode false :=
  rfl

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

import RMQ.Core.GenericSelect.Family
import RMQ.Core.GenericSelect.SuccinctSelectLegacyNames
import RMQ.Core.SuccinctSelect

/-!
# BP compatibility facts for generic select

This module keeps the `shape.bpCode`, `target := false` bridge facts above the
plain bitvector generic-select core. Historical SuccinctSelect helper-name
bridges are imported from `GenericSelect.SuccinctSelectLegacyNames` so this
file only declares BP-shaped facts directly.
-/

namespace RMQ.GenericSelect

open RMQ.SuccinctSelect

/-- The BP `false`-specialised occurrence count is the `target := false`
instance over `shape.bpCode`. -/
theorem falseSelectOccurrenceCount_eq (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape = occurrenceCount shape.bpCode false :=
  rfl

end RMQ.GenericSelect

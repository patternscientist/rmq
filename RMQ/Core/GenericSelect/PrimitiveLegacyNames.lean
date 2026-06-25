import RMQ.Core.GenericSelect.Primitives
import RMQ.Core.GenericSelect.LegacyNames

/-!
# Generic select primitive legacy names

Compatibility aliases for older primitive names that were false-specialized in
spelling. New code should use `denseLocalEntrySelectCosted`.
-/

namespace RMQ.GenericSelect

def denseLocalEntryFalseSelectCosted
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) : Costed (Option Nat) :=
  denseLocalEntrySelectCosted false bitWords entry q

theorem denseLocalEntryFalseSelectCosted_eq
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry) (q : Nat) :
    denseLocalEntryFalseSelectCosted bitWords entry q =
      denseLocalEntrySelectCosted false bitWords entry q :=
  rfl

end RMQ.GenericSelect

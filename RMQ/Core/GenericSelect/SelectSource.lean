import RMQ.Core.SuccinctRankProposal

/-!
# Generic charged select-position source

This module contains the neutral, target-parametric interface for a payload-live
select-position source over a plain bitvector. Proposal-specific descriptor
sampling lemmas live above this file.
-/

namespace RMQ.GenericSelect

/-- Payload-live select-position source over a plain bitvector. -/
structure ChargedSelectPositionSource
    (target : Bool) (bits : List Bool)
    (overhead : Nat -> Nat) (queryCost : Nat) where
  domainSize : Nat
  payload : List Bool
  readWords : List (List Bool)
  selectPositionCosted : Nat -> Costed (Option Nat)
  payload_length_le : payload.length <= overhead domainSize
  overhead_littleO : SuccinctSpace.LittleOLinear overhead
  selectPositionCosted_cost_le :
    forall occurrence, (selectPositionCosted occurrence).cost <= queryCost
  selectPositionCosted_exact :
    forall occurrence,
      (selectPositionCosted occurrence).erase =
        RMQ.Succinct.select target bits occurrence
  read_word_length_le_machine :
    forall {word : List Bool},
      List.Mem word readWords ->
        word.length <= SuccinctRankProposal.machineWordBits bits.length

end RMQ.GenericSelect

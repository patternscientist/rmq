import RMQ.Core.WordRAM.Bitvector.CanonicalRankAccessSafety

namespace RMQ.PackedBitvector.CanonicalRankAccessSafetyConsumer

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

theorem actual_access_source_required (bits : List Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .access).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .access false argument).regs, .running⟩ :=
  canonical_access_source_safe bits argument ha

theorem actual_rank_source_required (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .rank).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .rank target argument).regs, .running⟩ :=
  canonical_rank_source_safe bits target argument ha

theorem actual_access_execution_required (bits : List Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .access false argument
    (∀ instruction ∈ program .access, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .access).size + 1 →
      (run (Allocation.memory bits) (program .access) index
        (initial .access false argument)).final.Fits (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  canonical_access_execution_safe bits argument ha

theorem actual_rank_execution_required (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .rank target argument
    (∀ instruction ∈ program .rank, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .rank).size + 1 →
      (run (Allocation.memory bits) (program .rank) index
        (initial .rank target argument)).final.Fits (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  canonical_rank_execution_safe bits target argument ha

#print axioms actual_access_source_required
#print axioms actual_rank_source_required
#print axioms actual_access_execution_required
#print axioms actual_rank_execution_required

end RMQ.PackedBitvector.CanonicalRankAccessSafetyConsumer

import RMQ.Core.WordRAM.Bitvector.CanonicalSelectSafety
open RMQ RMQ.PackedBitvector RMQ.PackedBitvector.Controller
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1CanonicalSelectSafetyConsumer
example (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    ControllerSafetyBounds (loadedModel bits operation target argument) (canonicalLimits bits.length) :=
  loadedModel_safetyBounds bits operation target argument
example (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    Controller.ReaderSafe (loadedModel bits operation target argument)
      (Experiment.width bits.length) (Allocation.memory bits) Experiment.physicalReader :=
  loadedModel_readerSafe bits operation target argument
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .select).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .select target argument).regs, .running⟩ :=
  canonical_select_source_safe bits target argument ha
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .select) ((source .select).size + 1) (initial .select target argument) :=
  canonical_select_execution_safe bits target argument ha
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .select target argument
    (∀ instruction ∈ program .select, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .select).size + 1 →
      (run (Allocation.memory bits) (program .select) index (initial .select target argument)).final.Fits
        (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt), actual.transitions[index]? = some t →
      t.receipt = some receipt → receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  canonical_select_execution_safe_expectedType bits target argument ha
example : (source .select).size + 1 = 10030 := canonical_select_source_budget
example (target : Bool) : RankExecutionSafety (Allocation.memory []) (Experiment.width 0)
    (program .select) ((source .select).size + 1) (initial .select target 0) :=
  canonical_select_execution_safe [] target 0 (Nat.two_pow_pos _)
example (target : Bool) : RankExecutionSafety (Allocation.memory []) (Experiment.width 0)
    (program .select) ((source .select).size + 1)
    (initial .select target (2 ^ Experiment.width 0 - 1)) := by
  exact canonical_select_execution_safe [] target _ (by change 2 ^ Experiment.width 0 - 1 < 2 ^ Experiment.width 0; have := Nat.two_pow_pos (Experiment.width 0); omega)
#print axioms loadedMetadata_envelope
#print axioms loadedModel_safetyBounds
#print axioms loadedModel_readerSafe
#print axioms initial_data_fits
#print axioms canonical_select_source_safe
#print axioms canonical_select_source_fieldsFit
#print axioms canonical_select_source_budget
#print axioms canonical_select_execution_safe
#print axioms canonical_select_execution_safe_expectedType
end BV1CanonicalSelectSafetyConsumer

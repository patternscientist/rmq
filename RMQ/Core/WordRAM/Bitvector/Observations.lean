import RMQ.Core.WordRAM.Bitvector.Source
import RMQ.Core.WordRAM.Bitvector.NumericReader
import RMQ.Core.WordRAM.Packed.RankProof
import RMQ.Core.WordRAM.Packed.SelectProof

/-! # Literal instruction budgets and execution-derived category counts -/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def instructionBound : Operation → Nat
  | .access => 132
  | .rank => 1450
  | .select => 10030

theorem source_budget (operation : Operation) :
    (source operation).size + 1 = instructionBound operation := by
  cases operation <;>
    simp [instructionBound, source, operationBody, rankQuery, rankPrepare, accessQuery,
      Experiment.setup, Experiment.targetSetup, rankBlock_size, selectCloseBlock_size,
      physicalReader_size, Block.sequence, Block.size]
  all_goals decide

theorem program_length (operation : Operation) : (program operation).length = instructionBound operation := by
  simp only [program, List.length_append, Block.compile_length, List.length_cons, List.length_nil]
  exact source_budget operation

theorem execute_steps_bound (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    (execute bits operation target argument).steps ≤ instructionBound operation := by
  have h := run_steps_le_fuel (Allocation.memory bits) (program operation)
    ((source operation).size+1) (initial operation target argument)
  simpa only [execute, source_budget] using h

theorem execute_steps_partition (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    let actual := execute bits operation target argument
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  Run.steps_partition _

theorem execute_category_bound (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) (category : Category) :
    (execute bits operation target argument).categoryCount category ≤ instructionBound operation := by
  have hsteps := execute_steps_bound bits operation target argument
  have hpartition := execute_steps_partition bits operation target argument
  dsimp only at hpartition
  cases category <;> omega

end RMQ.PackedBitvector

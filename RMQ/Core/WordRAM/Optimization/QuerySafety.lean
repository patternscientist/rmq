import RMQ.Core.WordRAM.Optimization.Query
import RMQ.Core.WordRAM.Optimization.CompactSafety
import RMQ.Core.WordRAM.Packed.QuerySafety

/-! # Canonical compact execution safety on the original allocation and width -/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

set_option maxRecDepth 30000

theorem compactQuerySource_initial_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    compactQuerySource.Safe (buildMemory xs) (wordWidth xs.length)
      (Data.ofState (initialState xs.length left right)) := by
  have hs := querySource_initial_safe xs left right hl hr
  apply Block.safe_seq hs
  exact Block.safe_exit (buildMemory xs) (wordWidth xs.length) 3 _
    (querySource.eval_fits (buildMemory xs) (wordWidth xs.length) _ hs)

/-- Static fields and all dynamic primitives/prefixes concern the same compact
program, initial state, counted allocation and query-independent word width. -/
theorem compactQueryRun_execution_safe (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length)
      compactQueryProgram compactQueryBudget (initialState xs.length left right) := by
  have bound : compactSize compactQuerySource < 2 ^ wordWidth xs.length := by
    have h := compactQuery_size_reduction
    rw [compactQueryProgram_length, queryProgram_length, queryBudget_eq] at h
    exact Nat.lt_trans h (query_small_fields_fit xs.length)
  have hs := compact_compile_safe_run (wordWidth xs.length) (buildMemory xs)
    compactQuerySource compactQueryFresh 0 (initialState xs.length left right) rfl
    compactQuerySource_registersBelow (compactQueryProgram_fits xs.length) bound
    (initialState_fits xs.length left right hl hr)
    (compactQuerySource_initial_safe xs left right hl hr)
    compactQueryBudget (Nat.le_refl _)
  refine ⟨compactQueryProgram_fits xs.length, hs.2.2.2.1, ?_, hs.2.2.2.2.2, ?_⟩
  · intro index t occurrence
    exact hs.2.2.2.2.1 t (List.mem_of_getElem? occurrence)
  · intro index t receipt occurrence read
    have safe := hs.2.2.2.2.1 t (List.mem_of_getElem? occurrence)
    exact run_read_fits occurrence read safe.1 safe.2

end RMQ.SuccinctFinal.PackedWordRAM.Optimization

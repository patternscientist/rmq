import RMQ.Core.WordRAM.Optimization.Query
import RMQ.Core.WordRAM.Optimization.CompactProof
import RMQ.Core.WordRAM.Packed.QueryCertificate

/-! # Whole compact query through the unchanged independent source evaluator -/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured

set_option maxRecDepth 30000

theorem compactQueryRun_refines_source (memory : Memory) (n left right : Nat) :
    let source := querySource.eval memory (Data.ofState (initialState n left right))
    let actual := compactQueryRun memory n left right
    actual.result = (match source.final.status with
      | .running => some (source.final.regs 3)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ compactQueryBudget ∧
    actual.final.status ≠ .running := by
  have hb : BlockRegistersBelow compactQueryFresh querySource :=
    compactQuerySource_registersBelow.1
  have ho : 3 < compactQueryFresh := by
    unfold compactQueryFresh
    rw [queryRegisterCount_eq]
    decide
  exact compact_compile_with_halt memory querySource compactQueryFresh 3
    (initialState n left right) rfl hb ho

/-- Arbitrary-memory correspondence preserves actual failures and attempted
read order. Canonical answer and safety claims use buildMemory separately. -/
theorem compactQueryRun_original_observations (memory : Memory) (n left right : Nat) :
    (compactQueryRun memory n left right).result = (queryRun memory n left right).result ∧
    (compactQueryRun memory n left right).reads = (queryRun memory n left right).reads := by
  have hc := compactQueryRun_refines_source memory n left right
  have ho := queryRun_refines_source memory n left right
  exact ⟨hc.1.trans ho.1.symm, hc.2.1.trans ho.2.1.symm⟩

/-- This bound is obtained from adequate compact compilation, not fuel alone. -/
theorem compactQueryRun_steps_le (memory : Memory) (n left right : Nat) :
    (compactQueryRun memory n left right).steps ≤ compactQueryBudget :=
  (compactQueryRun_refines_source memory n left right).2.2.1

theorem compactQueryRun_stopped (memory : Memory) (n left right : Nat) :
    (compactQueryRun memory n left right).final.status ≠ .running :=
  (compactQueryRun_refines_source memory n left right).2.2.2

/-- Any larger adequate fuel produces the identical full compact run,
including its primitive transitions, not merely the same projected answer. -/
theorem compactQueryRun_fuel_eq (memory : Memory) (n left right fuel : Nat)
    (enough : compactQueryBudget ≤ fuel) :
    run memory compactQueryProgram fuel (initialState n left right) =
      compactQueryRun memory n left right := by
  apply compact_run_extend_stopped memory compactQueryProgram
    (initialState n left right) compactQueryBudget fuel enough
  change step memory compactQueryProgram (compactQueryRun memory n left right).final = none
  have stopped := compactQueryRun_stopped memory n left right
  cases status : (compactQueryRun memory n left right).final.status with
  | running => exact False.elim (stopped status)
  | halted value => simp [step, status]
  | fault => simp [step, status]

theorem compactQueryRun_result (xs : List Int) (left right : Nat) :
    (compactQueryRun (buildMemory xs) xs.length left right).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  rw [(compactQueryRun_original_observations (buildMemory xs) xs.length left right).1]
  exact queryRun_result xs left right

theorem compactQueryRun_halts (xs : List Int) (left right : Nat) :
    (compactQueryRun (buildMemory xs) xs.length left right).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  Run.status_of_result _ _ (compactQueryRun_result xs left right)

theorem compactQueryRun_invalid (memory : Memory) (n left right : Nat)
    (invalid : ¬ (left < right ∧ right ≤ n)) :
    (compactQueryRun memory n left right).result = some 0 ∧
    (compactQueryRun memory n left right).reads = [] := by
  have hc := compactQueryRun_original_observations memory n left right
  have ho := queryRun_invalid memory n left right invalid
  exact ⟨hc.1.trans ho.1, hc.2.trans ho.2.1⟩

theorem compactQueryRun_agreement (memory supplied : Memory) (n left right : Nat)
    (agree : ∀ receipt ∈ (compactQueryRun memory n left right).reads,
      supplied[receipt.address]? = memory[receipt.address]?) :
    compactQueryRun supplied n left right = compactQueryRun memory n left right :=
  run_eq_of_agree memory supplied compactQueryProgram compactQueryBudget
    (initialState n left right) agree

/-- Packet decoding uses the same representable-input boundary and the same
observed machine answer on every supplied memory. -/
theorem compactQueryNat_eq_original (memory : Memory) (n left right : Nat) :
    compactQueryNat memory n left right = queryNat memory n left right := by
  by_cases capacity : left < 2 ^ wordWidth n ∧ right < 2 ^ wordWidth n
  · rw [compactQueryNat, queryNat, encodeInputs, if_pos capacity]
    change (compactQueryRun memory n left right).result.bind _ =
      (queryRun memory n left right).result.bind _
    rw [(compactQueryRun_original_observations memory n left right).1]
  · simp only [compactQueryNat, queryNat, encodeInputs, if_neg capacity]

theorem compactQueryNat_exact (xs : List Int) (left right : Nat) :
    compactQueryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none := by
  rw [compactQueryNat_eq_original]
  exact queryNat_exact xs left right

theorem compactQueryNat_leftmost (xs : List Int) (left right index : Nat)
    (answer : compactQueryNat (buildMemory xs) xs.length left right = some index) :
    LeftmostArgMin xs left right index := by
  rw [compactQueryNat_eq_original] at answer
  exact queryNat_leftmost xs left right index answer

theorem compactQueryRun_scanWindow (xs : List Int) (left right : Nat)
    (valid : ValidRange xs left right) :
    (compactQueryRun (buildMemory xs) xs.length left right).result =
      some (scanWindow xs left (right - left) + 1) := by
  rw [(compactQueryRun_original_observations (buildMemory xs) xs.length left right).1]
  exact queryRun_scanWindow xs left right valid

end RMQ.SuccinctFinal.PackedWordRAM.Optimization

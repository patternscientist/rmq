import RMQ.Core.WordRAM.Optimization.BranchBound
import RMQ.Core.WordRAM.Optimization.Certificate
import RMQ.Core.WordRAM.Packed.Capstone

/-!
# Additive query optimization theorems

The branch-sensitive theorem bounds the unchanged complete query execution.
Its reduced-fuel equality retains every transition and ordered receipt. The
historical program-length budget remains unchanged.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured
open Cartesian SuccinctSpace PackedCellProbe

def branchQueryBudget : Nat := branchBound querySource + 1

set_option maxRecDepth 30000 in
theorem branchQueryBudget_eq : branchQueryBudget = 150739 := by rfl

theorem branchQueryBudget_le_original : branchQueryBudget ≤ queryBudget := by
  have h := branchBound_le_size querySource
  simpa only [branchQueryBudget, querySource, guardedBlock_size, queryBudget] using
    Nat.add_le_add_right h 1

set_option maxRecDepth 30000 in
private theorem whole_bound :
    branchBound (Block.seq querySource (.exit 3)) = branchQueryBudget := rfl

private theorem whole_program :
    (Block.seq querySource (.exit 3)).compileAt 0 = queryProgram := rfl

/-- The original adequately fuelled run is bounded by a witnessed primitive
segment; both fuel settings preserve the complete machine run. -/
theorem queryRun_branchBound_and_fuel_eq (memory : Memory) (n left right : Nat) :
    (queryRun memory n left right).steps ≤ branchQueryBudget ∧
    queryRun memory n left right =
      run memory queryProgram branchQueryBudget (initialState n left right) := by
  have h := compiled_run_bound_and_fuel_eq memory
    (Block.seq querySource (.exit 3)) (initialState n left right) rfl
    queryBudget branchQueryBudget (by rw [whole_bound]; exact branchQueryBudget_le_original)
    (by rw [whole_bound]; exact Nat.le_refl _)
  simpa only [whole_bound, whole_program, queryRun] using h

/-- Universal bound on the original complete queryRun, not a truncated run at
the displayed constant. Arbitrary numeric memory, including malformed metadata,
is covered; no successful-load or validity premise is used. -/
theorem branchSensitiveQueryBound (memory : Memory) (n left right : Nat) :
    (queryRun memory n left right).steps ≤ 150739 := by
  simpa only [branchQueryBudget_eq] using
    (queryRun_branchBound_and_fuel_eq memory n left right).1

/-- The smaller fuel retains the full final state and complete transitions. -/
theorem reducedFuel_queryRun_eq (memory : Memory) (n left right : Nat) :
    run memory queryProgram 150739 (initialState n left right) =
      queryRun memory n left right := by
  simpa only [branchQueryBudget_eq] using
    (queryRun_branchBound_and_fuel_eq memory n left right).2.symm

/-- On the unchanged canonical allocation, reduced fuel halts with the same
reference packet and the same ordered attempted reads and replies. -/
theorem reducedFuel_query_correct (xs : List Int) (left right : Nat) :
    let actual := run (buildMemory xs) queryProgram 150739
      (initialState xs.length left right)
    actual.final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    actual.result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    actual.reads = (queryRun (buildMemory xs) xs.length left right).reads := by
  dsimp only
  rw [reducedFuel_queryRun_eq]
  exact ⟨queryRun_halts xs left right, queryRun_result xs left right, rfl⟩

namespace OptimizationConsumers

theorem original_run_bound_expectedType (memory : Memory) (n left right : Nat) :
    (run memory queryProgram queryBudget (initialState n left right)).steps ≤ 150739 :=
  branchSensitiveQueryBound memory n left right

theorem reduced_fuel_expectedType (memory : Memory) (n left right : Nat) :
    run memory queryProgram 150739 (initialState n left right) =
      run memory queryProgram queryBudget (initialState n left right) :=
  reducedFuel_queryRun_eq memory n left right

end OptimizationConsumers

set_option maxRecDepth 30000 in
/-- The actual compact emitter and execution meet the whole contract on the
unchanged counted allocation, with no supplied correctness or safety premise. -/
theorem compactPackedQueryCapstone_holds : CompactPackedQueryCapstone where
  -- OPT1-REPLAY-INITIALIZERS-BEGIN
  allocationResidualLittleO := allocationRho_littleO
  completeResidualLittleO := compactQueryCompleteRho_littleO
  widthBounds n := ⟨wordWidth_log_lower n, wordWidth_le_log n⟩
  dataCapacity := buildMemory_capacity_le
  completeCapacity xs := compactQuery_complete_capacity xs
  memoryWordsFit := buildMemory_words_fit
  allocationAddressesFit := buildMemory_address_fit
  programFieldsFit := compactQueryProgram_fits
  budgetExact := compactQueryBudget_eq
  programLength := compactQueryProgram_length_eq
  encodedProgramLength := compactQueryProgramWords_eq
  programReduction := compactQuery_size_reduction
  emittedProgram := rfl
  originalExecutionBound := branchSensitiveQueryBound
  originalReducedFuel := reducedFuel_queryRun_eq
  arbitraryMemoryObservations := compactQueryRun_original_observations
  completedExecution := compactQueryRun_stopped
  adequateFuel := compactQueryRun_fuel_eq
  registerCount := compactQueryRegisterCount_eq
  scratchCount := compactQueryScratchWords_eq
  unusedRegisters xs left right fuel r outside :=
    compactQuery_finite_registers (buildMemory xs) xs.length left right fuel r outside
  validInputs xs left right valid := ⟨valid_inputs_encode xs.length left right valid.1 valid.2,
    validEndpoints_fit xs left right valid⟩
  natContract := compactQueryNat_exact
  leftmost := compactQueryNat_leftmost
  result xs left right _ _ := compactQueryRun_result xs left right
  halt xs left right _ _ := compactQueryRun_halts xs left right
  invalidGuard xs left right _ _ invalid :=
    compactQueryRun_invalid (buildMemory xs) xs.length left right invalid
  stepBound xs left right := compactQueryRun_steps_le (buildMemory xs) xs.length left right
  categoryPartition xs left right := Run.steps_partition _
  finalStateFit xs left right hl hr := (compactQueryRun_execution_safe xs left right hl hr).2.1
  transitionSafety xs left right hl hr :=
    (compactQueryRun_execution_safe xs left right hl hr).2.2.1
  prefixSafety xs left right hl hr := (compactQueryRun_execution_safe xs left right hl hr).2.2.2.1
  readWidth xs left right hl hr := (compactQueryRun_execution_safe xs left right hl hr).2.2.2.2
  positionalReadBacking xs left right index t receipt occurrence read := run_read_at occurrence read
  orderedLogicalRefinement xs left right := by
    change (compactQueryRun (buildMemory xs) xs.length left right).reads = _
    rw [(compactQueryRun_original_observations (buildMemory xs) xs.length left right).2]
    exact queryRun_reference_reads xs left right
  logicalReadOnly := queryTraceResult_readOnly
  suppliedMemoryAgreement xs memory left right agree :=
    compactQueryRun_agreement (buildMemory xs) memory xs.length left right agree
  specResult := compactQueryRun_scanWindow
  noFailedLoads xs left right _ receipt member := by
    change receipt ∈ (compactQueryRun (buildMemory xs) xs.length left right).reads at member
    rw [(compactQueryRun_original_observations (buildMemory xs) xs.length left right).2] at member
    exact queryRun_reads_reply xs left right receipt member
  -- OPT1-REPLAY-INITIALIZERS-END

end RMQ.SuccinctFinal.PackedWordRAM.Optimization

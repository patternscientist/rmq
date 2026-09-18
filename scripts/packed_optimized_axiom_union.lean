import Lean.Elab.Command
import Lean.Util.CollectAxioms
import RMQ.Core.WordRAM.Optimization.Consumers

/-! One shared traversal of the builtin kernel-environment axiom collector.
The 93 roots are checked for existence and distinctness before traversal;
each must be visited afterward. This reports the exact union, not a separate
axiom distribution per declaration. The two named public targets also retain
explicit standard print commands below.
-/

open Lean Elab Command

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.branchSensitiveQueryBound,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.reducedFuel_queryRun_eq,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactPackedQueryCapstone_holds,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compact_realizes,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compact_compile_run,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compact_compile_with_halt,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compact_compile_safe_run,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactAt_fits,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactAt_encoding_length,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQueryRun_original_observations,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQueryRun_stopped,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQueryRun_fuel_eq,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQueryRun_execution_safe,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQuery_complete_capacity,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactQueryCompleteRho_littleO,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.allocationResidualLittleO_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.allocationResidualLittleO_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completeResidualLittleO_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completeResidualLittleO_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.widthBounds_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.widthBounds_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.dataCapacity_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.dataCapacity_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completeCapacity_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completeCapacity_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.memoryWordsFit_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.memoryWordsFit_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.allocationAddressesFit_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.allocationAddressesFit_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programFieldsFit_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programFieldsFit_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.budgetExact_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.budgetExact_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programLength_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programLength_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.encodedProgramLength_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.encodedProgramLength_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programReduction_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.programReduction_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.emittedProgram_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.emittedProgram_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.originalExecutionBound_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.originalExecutionBound_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.originalReducedFuel_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.originalReducedFuel_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.arbitraryMemoryObservations_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.arbitraryMemoryObservations_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completedExecution_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.completedExecution_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.adequateFuel_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.adequateFuel_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.registerCount_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.registerCount_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.scratchCount_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.scratchCount_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.unusedRegisters_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.unusedRegisters_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.validInputs_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.validInputs_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.natContract_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.natContract_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.leftmost_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.leftmost_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.result_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.result_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.halt_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.halt_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.invalidGuard_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.invalidGuard_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.stepBound_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.stepBound_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.categoryPartition_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.categoryPartition_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.finalStateFit_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.finalStateFit_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.transitionSafety_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.transitionSafety_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.prefixSafety_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.prefixSafety_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.readWidth_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.readWidth_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.positionalReadBacking_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.positionalReadBacking_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.orderedLogicalRefinement_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.orderedLogicalRefinement_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.logicalReadOnly_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.logicalReadOnly_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.suppliedMemoryAgreement_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.suppliedMemoryAgreement_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.specResult_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.specResult_canonical,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.noFailedLoads_expectedType,
    ``RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers.noFailedLoads_canonical]
  unless roots.size == 93 && roots.toList.eraseDups.length == 93 do
    throwError "OPT1-AXIOM-FAIL: wrong or duplicate roots"
  for root in roots do
    unless (env.checked.get.find? root).isSome do
      throwError "OPT1-AXIOM-FAIL: missing kernel declaration {root}"
  let (_, state) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}
  for root in roots do
    unless state.visited.contains root do
      throwError "OPT1-AXIOM-FAIL: root not visited {root}"
    logInfo m!"OPT1-AXIOM-ROOT {root}"
  let union := state.axioms.qsort Name.lt
  let text := String.intercalate "," (union.toList.map Name.toString)
  logInfo m!"OPT1-AXIOM-UNION {text}"

#print axioms RMQ.SuccinctFinal.PackedWordRAM.Optimization.branchSensitiveQueryBound
#print axioms RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactPackedQueryCapstone_holds

import RMQ.Headlines.Lifecycle
import RMQ.Validation.LifecycleContract
import RMQ.Core.WordRAM.Lifecycle.Controls
import RMQ.Core.WordRAM.Lifecycle.Provenance

/-! Exact public types and transitive proof trust for LIFE-1.
The independent client is the dependency check; this file records its types.
-/

open RMQ RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedLifecycle

#print ContinuousConstructionQuery
#print ConstructionChain
#print ExecutedOwner
#print ReusableOwner
#print PhysicalRun
#check @continuousConstructionQuery_holds
#check @wordInputContinuousConstructionQuery
#check @comparisonInputContinuousConstructionQuery
#check @ContinuousConstructionQuery.valid
#check @ContinuousConstructionQuery.invalid
#check @lifecycle_store_determinism
#check @load_occurrence_value_dependency
#check @RMQ.Headlines.succinctRMQContinuousLifecycle
#check @ContractChecks.checkC01_construction
#check @ContractChecks.checkC02_retained
#check @ContractChecks.checkC03_safety
#check @ContractChecks.checkC04_physical
#check @ContractChecks.checkC05_executable
#check @ContractChecks.checkC06_reusable
#check @ContractChecks.checkC07_uniform
#check @ContractChecks.checkC10_constants
#check @ContractChecks.checkC13_store
#check @ContractChecks.checkC14_store_guard
#check @Executable.initial_owner_refinement
#check @Executable.initial_array_refinement
#check @Executable.query_owner_refinement
#check @Executable.query_array_refinement
#check @Ownership.Ready.query
#check @Physical.run_fetched_words
#check @Physical.run_read_at
#check @Physical.failed_load
#check @Physical.canonical_capacity
#check @Reusable.query_read_occurrence
#check @Reusable.query_valid
#check @Reusable.query_invalid
#print Provenance.ProductionReceipts
#check @Provenance.continuous_production
#check @Provenance.production_receipts

#print axioms continuousConstructionQuery_holds
#print axioms wordInputContinuousConstructionQuery
#print axioms comparisonInputContinuousConstructionQuery
#print axioms ContinuousConstructionQuery.valid
#print axioms ContinuousConstructionQuery.invalid
#print axioms lifecycle_store_determinism
#print axioms load_occurrence_value_dependency
#print axioms RMQ.Headlines.succinctRMQContinuousLifecycle
#print axioms ContractChecks.checkC01_construction
#print axioms ContractChecks.checkC02_retained
#print axioms ContractChecks.checkC03_safety
#print axioms ContractChecks.checkC04_physical
#print axioms ContractChecks.checkC05_executable
#print axioms ContractChecks.checkC06_reusable
#print axioms ContractChecks.checkC07_uniform
#print axioms ContractChecks.checkC10_constants
#print axioms ContractChecks.checkC13_store
#print axioms ContractChecks.checkC14_store_guard
#print axioms Executable.initial_owner_refinement
#print axioms Executable.initial_array_refinement
#print axioms Executable.query_owner_refinement
#print axioms Executable.query_array_refinement
#print axioms Ownership.Ready.query
#print axioms Physical.run_fetched_words
#print axioms Physical.run_read_at
#print axioms Physical.canonical_capacity
#print axioms Reusable.query_read_occurrence
#print axioms Reusable.query_valid
#print axioms Reusable.query_invalid
#print axioms Controls.output_source_value_dependency
#print axioms Controls.initialization_reject
#print axioms Controls.stale_tail_reject
#print axioms Controls.absent_copy_reply_reject
#print axioms Controls.omitted_release_reject
#print axioms Controls.backward_copy_reject
#print axioms Controls.key_extent_reject
#print axioms Controls.wrong_entry_result_reject
#print axioms Controls.field_width_reject
#print axioms Controls.dirty_register_rejects_entry
#print axioms Provenance.continuous_production
#print axioms Provenance.production_receipts

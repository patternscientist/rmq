import RMQ.Headlines

/-!
Focused trust-base check for the Word-RAM refinement boundary.

This is intentionally smaller than `scripts/axiom_check.lean`: it checks the
first-order interpreter provenance lemmas and the public interpreted capstones
that consume the Word-RAM bridge layer.
-/

#print axioms RMQ.WordRAM.Program.eval_toCosted_cost_eq_trace_length
#print axioms RMQ.WordRAM.Program.eval_reads_subset_payload
#print axioms RMQ.WordRAM.Program.eval_readWord_event_eq_store
#print axioms RMQ.WordRAM.Program.eval_word_reads_length_le_machine
#print axioms RMQ.WordRAM.Program.eval_eq_of_readWord_eq
#print axioms RMQ.WordRAM.Program.eval_toCosted_eq_of_readWord_eq

#print axioms RMQ.RankSelectSpec.subLogAccessInterpretedCosted_refines_subLogAccessCosted
#print axioms RMQ.RankSelectSpec.subLogRankInterpretedCosted_refines_subLogRankCosted
#print axioms RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteInterpretedCosted_refines
#print axioms RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile

#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
#print axioms RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile

#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile
#print axioms RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted

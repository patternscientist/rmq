import RMQ.Core.ModelHub

/-!
Curated trust-base check for the reusable hub layer.

This file intentionally imports `RMQ.Core.ModelHub`, not `RMQ`, so it checks
that the hub surface stands on its own without the RMQ spoke. Standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) are allowed.
-/

#print axioms RMQ.LowerBound.domain_length_le_two_pow_of_lossless_encoding
#print axioms RMQ.LowerBound.count_log_lower_of_quadratic_bound
#print axioms RMQ.LowerBound.PayloadLosslessEncoding.domain_length_le_two_pow
#print axioms RMQ.LowerBound.PayloadLosslessEncoding.lower_le_bits_of_count_lower_bound
#print axioms RMQ.LowerBound.PayloadLosslessEncoding.payloadBitCount_ge_bits_of_mem
#print axioms RMQ.LowerBound.PayloadLosslessEncoding.lower_le_payloadBitCount_of_mem_of_count_lower_bound
#print axioms RMQ.LowerBound.PayloadLosslessEncoding.lower_le_budget_of_payloadBitCount_bound
#print axioms RMQ.LowerBound.domain_length_le_two_pow_of_payload_lossless_encoding
#print axioms RMQ.LowerBound.lower_le_budget_of_payload_lossless_encoding
#print axioms RMQ.LowerBound.PayloadSpaceBounds.lower_le_bits
#print axioms RMQ.LowerBound.PayloadSpaceBounds.lower_le_payloadBitCount_of_mem
#print axioms RMQ.LowerBound.PayloadSpaceBounds.lower_le_budget
#print axioms RMQ.LowerBound.PayloadSpaceBounds.lower_le_upper
#print axioms RMQ.RAM.Exec.toCosted_run_eq_value_steps
#print axioms RMQ.RAM.writeArray?_run
#print axioms RMQ.RAM.arrayOfList_refines_with_steps
#print axioms RMQ.Amortized.compose
#print axioms RMQ.Amortized.costed_bind
#print axioms RMQ.Amortized.costed_map
#print axioms RMQ.Amortized.deltaCredit
#print axioms RMQ.Amortized.costed_deltaCredit
#print axioms RMQ.Amortized.runBound
#print axioms RMQ.Amortized.totalActual_le
#print axioms RMQ.Amortized.Step.totalCredit_le_length_mul
#print axioms RMQ.Amortized.totalActual_le_length_mul
#print axioms RMQ.Refine.StoredMatrix.ofList_erases
#print axioms RMQ.Refine.StoredMatrix.cell?_eq_absCell?
#print axioms RMQ.Refine.StoredMatrix.row?_getD_toList_eq_absRow?_getD
#print axioms RMQ.Refine.StoredMatrix.cell?_getD_eq_absCell?_getD
#print axioms RMQ.Refine.StoredSeq.get?_eq_absGet?

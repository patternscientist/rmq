import RMQ
import RMQ.Core.EncodingLowerBound
import RMQ.Headlines
import RMQ.Core.SuccinctFinal

/-!
Concise trust-base check for the public headline path.

The full `scripts/axiom_check.lean` is the acceptance gate. This smaller file
prints only the theorem surfaces most likely to appear in a public overview:
shared contract, RMQ/LCA reduction, lower bound, Fischer-Heun/LCA costs, and
the BP-native succinct capstone.
-/

#print axioms RMQ.RMQBackend.queryBuilt_eq
#print axioms RMQ.Cartesian.certifiedReduction
#print axioms RMQ.EncodingLowerBound.shapeCount_quadratic_lower
#print axioms RMQ.EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding
#print axioms RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound
#print axioms RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
#print axioms RMQ.FischerHeun.fischerHeun_refines_with_steps
#print axioms RMQ.LCAFischerHeun.denseLCA_linearBuild_constantQuery_profile
#print axioms RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize_pos_of_size_ge
#print axioms RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_eq_positive_dispatch_of_size_ge
#print axioms RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_exact_of_query
#print axioms RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_exact_of_query_of_size_ge
#print axioms RMQ.SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily_profile
#print axioms RMQ.Headlines.rankSelectNPlusOConstantQuery
#print axioms RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightConstantQuery
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile
#print axioms RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
#print axioms RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted
#print axioms RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery

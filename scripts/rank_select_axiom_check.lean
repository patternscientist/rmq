import RMQRankSelect

/-!
Focused trust-base check for the standalone rank/select spoke.

The full RMQ gate still runs `scripts/axiom_check.lean`.  This smaller check is
for the reusable plain-bitvector surface: stored-bit access, Jacobson rank,
Clark-style sparse-exception select, `n + o(n)` auxiliary payload, and constant
modeled query cost.
-/

#print axioms RMQ.RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
#print axioms RMQ.RankSelectSpec.fixedWeightBitstrings_length
#print axioms RMQ.RankSelectSpec.fixedWeightBitstrings_mem_length_trueCount
#print axioms RMQ.RankSelectSpec.fixedWeightBitstrings_mem_of_length_trueCount
#print axioms RMQ.RankSelectSpec.fixedWeightBitstrings_mem_iff
#print axioms RMQ.RankSelectSpec.CompressedBitVectorRankSelectDirectory.profile
#print axioms RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
#print axioms RMQ.RankSelect.compressedFixedWeightConstantQueryProfile
#print axioms RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
#print axioms RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
#print axioms RMQ.GenericSelect.sparseExceptionSelectSource_profile
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile

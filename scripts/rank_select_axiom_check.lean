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
#print axioms RMQ.RankSelectSpec.fixedWeightBitstrings_nodup
#print axioms RMQ.RankSelectSpec.fixedWeightCodec_roundTrip
#print axioms RMQ.RankSelectSpec.fixedWeightEncode?_lt_binomialCount
#print axioms RMQ.RankSelectSpec.fixedWeightEncode?_eq_some_fixedWeightCode
#print axioms RMQ.RankSelectSpec.fixedWeightCode_lt_binomialCount
#print axioms RMQ.RankSelectSpec.fixedWeightEncode?_lt_payloadBudgetPow
#print axioms RMQ.RankSelectSpec.fixedWeightCode_lt_payloadBudgetPow
#print axioms RMQ.RankSelectSpec.fixedWeightPackedPayload_length
#print axioms RMQ.RankSelectSpec.fixedWeightPackedPayload_bitsToNatLE
#print axioms RMQ.RankSelectSpec.fixedWeightDecode?_packedPayload
#print axioms RMQ.RankSelectSpec.fixedWeightPackedPayload_profile
#print axioms RMQ.RankSelectSpec.fixedWeightPackedReadbackDirectory_profile
#print axioms RMQ.RankSelectSpec.FixedWeightPackedReadbackData.profile
#print axioms RMQ.RankSelectSpec.FixedWeightPackedReadbackData.ofChunks_profile
#print axioms RMQ.RankSelectSpec.fixedWeightEncode?_fixedWeightDecode?
#print axioms RMQ.RankSelectSpec.fixedWeightDecode?_eq_some_iff
#print axioms RMQ.RankSelectSpec.fixedWeightDecode?_mem_length_trueCount
#print axioms RMQ.RankSelectSpec.CompressedBitVectorRankSelectDirectory.profile
#print axioms RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
#print axioms RMQ.RankSelect.compressedFixedWeightConstantQueryProfile
#print axioms RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
#print axioms RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
#print axioms RMQ.GenericSelect.sparseExceptionSelectSource_profile
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
#print axioms RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile

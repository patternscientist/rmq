import RMQ.Validation.VariablePayloadLowerBound

/-! Explicit dependency diagnostics for the LB-1 counting/serialization join and
its independent consumers. These commands report theorem assumptions; they add
none. Exact propositions and mandatory field dependencies are checked separately
by the validation module and the committed mutation replay. -/

#print axioms RMQ.EncodingVariableLowerBound.boundedBitStrings_cardinality
#print axioms RMQ.ExactRMQBoundedEncoding.shapeEncode_injective_on
#print axioms RMQ.ExactRMQBoundedEncoding.shapeCount_le
#print axioms RMQ.ExactRMQBoundedEncoding.doubledLogSlackLower_le

#print axioms RMQ.SuccinctFinal.PackedWordRAM.deserializeWords_serializeWords
#print axioms RMQ.SuccinctFinal.PackedWordRAM.serializeWords_injective
#print axioms RMQ.SuccinctFinal.PackedWordRAM.allocationBits_length
#print axioms RMQ.SuccinctFinal.PackedWordRAM.reconstructedMemory_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedWordRAM.allocationDecoder_exact
#print axioms RMQ.SuccinctFinal.PackedWordRAM.allocationBits_shape_injective

#print axioms RMQ.SuccinctFinal.PackedWordRAM.uniformAllocation_shapeCount_le
#print axioms RMQ.SuccinctFinal.PackedWordRAM.uniformAllocation_doubledLogSlackLower_le
#print axioms RMQ.SuccinctFinal.PackedWordRAM.canonicalAllocation_shapeCount_le
#print axioms RMQ.SuccinctFinal.PackedWordRAM.canonicalAllocation_doubledLogSlackLower_le
#print axioms RMQ.SuccinctFinal.PackedWordRAM.allocationBits_capacity_le
#print axioms RMQ.SuccinctFinal.PackedWordRAM.reconstructedRun_eq
#print axioms RMQ.SuccinctFinal.PackedWordRAM.reconstructedPackedQueryCapstone_holds
#print axioms RMQ.SuccinctFinal.PackedWordRAM.packedAllocationOptimality_holds

#print axioms RMQ.Validation.VariablePayloadLowerBound.publicContract
#print axioms RMQ.Validation.VariablePayloadLowerBound.composedConsumer

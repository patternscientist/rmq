import RMQ.Core.WordRAM.E1InteriorSpanBlock
import RMQ.Core.WordRAM.E1InteriorMerge

-- #2 / #3 instantiation
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.spanValue_localSpan_eq_routeValue
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.spanValue_globalSpan_eq_routeValue
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.geomCell_localSpan_eq_routeDecode
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.geomCell_globalSpan_eq_routeDecode
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.cellOpt_spanCell_localSpan
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.cellOpt_spanCell_globalSpan
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.legValue_eq_minCandidateComputation_value
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.localSpanGeom_cap
#print axioms RMQ.WordRAM.E1InteriorSpanBlock.globalSpanGeom_cap
#print axioms RMQ.WordRAM.E1InteriorStoreConcrete.hexact_local_concrete
#print axioms RMQ.WordRAM.E1InteriorStoreConcrete.hexact_global_concrete

-- the two-way merge block
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeBlock_runsTo
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeBlock_readFree
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeUntouched_at_crossBlockArm_operands
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeProgram_correct_eq_mergeBlock

-- discriminators and non-entailments
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeTie_discriminates
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeTie_traces_agree
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeTie_catLogs_differ
#print axioms RMQ.WordRAM.E1InteriorMerge.mergePos_discriminates
#print axioms RMQ.WordRAM.E1InteriorMerge.mergePos_traces_agree
#print axioms RMQ.WordRAM.E1InteriorMerge.mergePos_catLogs_agree
#print axioms RMQ.WordRAM.E1InteriorMerge.mergePos_both_halt
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeOperands_preserved_correct
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeOperands_preserved_exitArm
#print axioms RMQ.WordRAM.E1InteriorMerge.mergeOperands_preserved_impostor

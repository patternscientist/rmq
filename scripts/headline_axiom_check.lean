import RMQPaper
import RMQ
import RMQ.Core.EncodingLowerBound
import RMQ.Headlines
import RMQ.Core.SuccinctFinal

/-!
Concise trust-base check for the public headline path.

The full `scripts/axiom_check.lean` is the acceptance gate. This smaller file
prints only the theorem surfaces most likely to appear in a public overview:
shared contract, RMQ/LCA reduction, lower bound, Fischer-Heun/LCA costs, and
the canonical physical-payload/global-trace succinct capstone. Historical RMQ
profiles are checked by broader inventories, not promoted here.
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
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory
#print axioms RMQ.Headlines.rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreBoundedExecutionStory
#print axioms RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile
#print axioms RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery
#print axioms RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory
#print axioms RMQ.Headlines.listIntSuccinctRMQOccurrenceProvenanceOfValid
#print axioms RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalFootprintRecorded
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency
#print axioms RMQ.Headlines.listIntSuccinctRMQReviewerPhysicalExecutionRefinesLogical
#print axioms RMQ.Headlines.listIntSuccinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint
#print axioms RMQ.Headlines.succinctRMQProgramOccurrenceActualProducer
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalSourcesNodup
#print axioms RMQ.Headlines.succinctRMQReviewerSourceRegionInjective
#print axioms RMQ.Headlines.succinctRMQReviewerSegmentSourceCoverage
#print axioms RMQ.Headlines.succinctRMQReviewerEveryReadHasListedRegion
#print axioms RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance
#print axioms RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence
#print axioms RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence
#print axioms RMQ.Headlines.succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer
#print axioms RMQ.Headlines.succinctRMQReviewerRepeatedEqualOccurrencesRemainDistinct
#print axioms RMQ.Headlines.succinctRMQB7Cost33WholeQueryReachability
#print axioms RMQ.Headlines.succinctRMQB7SingletonRepeatedReadExactPositions

/- The headline cost-33 alias must retain the guarded whole trace and the
identical component, not only the isolated component theorem. -/
example :
    let shape :=
      RMQ.SuccinctClose.canonicalRelativeRmmInteriorCost33WitnessShape
    let interior :=
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments 143 146
    RMQ.SuccinctClassic.queryTraceResult
        RMQ.SuccinctClose.canonicalRelativeRmmInteriorCost33WitnessInput
        1704 3469 =
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape 1704 3469 ∧
    (∃ prefixTrace suffixTrace,
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape 1704 3469).trace =
          prefixTrace ++ interior.trace ++ suffixTrace) ∧
    interior.toCosted.cost = 33 ∧
    interior.trace.length = 33 ∧
    Not (interior.toCosted.cost <= 30) := by
  have hpublic : RMQ.SuccinctClassic.B7Cost33WholeQueryReachability :=
    RMQ.Headlines.succinctRMQB7Cost33WholeQueryReachability
  unfold RMQ.SuccinctClassic.B7Cost33WholeQueryReachability at hpublic
  rcases hpublic with ⟨hquery, hsource⟩
  unfold RMQ.SuccinctFinal.ConcreteBPNativeB7Cost33WholeQueryReachability
    at hsource
  rcases hsource with
    ⟨_hvalid, _hshape, _hleft, _hright, _hbeforeLength,
      _hpreLeft, _hpreRight, _hprogram, _hlcaEval, _hmiddle,
      _hlcaContains, hwholeContains, hcost, hlength, hnotLeThirty⟩
  exact ⟨hquery, hwholeContains, hcost, hlength, hnotLeThirty⟩

/- The headline occurrence alias must retain both literal producers and both
receipts; existential positions or one collapsed producer do not inhabit it. -/
example :
    ∃ word : RMQ.WordRAM.Word,
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1).trace[0]? =
          some (.readWord 1 0 (some word)) ∧
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1).trace[15]? =
          some (.readWord 1 0 (some word)) ∧
      RMQ.SuccinctFinal.WholeQueryProgram.ProducesEventAt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1
        (.readWord 1 0 (some word))
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram
        RMQ.SuccinctFinal.WholeQueryState.empty 0 0
        (RMQ.SuccinctFinal.WholeQueryInstr.selectClose .leftClose .inputLeft)
        RMQ.SuccinctFinal.WholeQueryState.empty 0 ∧
      RMQ.SuccinctFinal.WholeQueryProgram.ProducesEventAt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1
        (.readWord 1 0 (some word))
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram
        RMQ.SuccinctFinal.WholeQueryState.empty 15 1
        (RMQ.SuccinctFinal.WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1)))
        (RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace
          (RMQ.Cartesian.shape ([7] : List Int)) 0 1
          [RMQ.SuccinctFinal.WholeQueryInstr.selectClose .leftClose .inputLeft]
          RMQ.SuccinctFinal.WholeQueryState.empty).value 0 ∧
      RMQ.SuccinctFinal.ReviewerReadOccurrenceReceipt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1 0 1 0 (some word) ∧
      RMQ.SuccinctFinal.ReviewerReadOccurrenceReceipt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1 15 1 0 (some word) := by
  have hpublic : RMQ.SuccinctClassic.B7SingletonRepeatedReadExactPositions :=
    RMQ.Headlines.succinctRMQB7SingletonRepeatedReadExactPositions
  unfold RMQ.SuccinctClassic.B7SingletonRepeatedReadExactPositions at hpublic
  rcases hpublic with ⟨_hquery, hsource⟩
  unfold
    RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQSingletonRepeatedReadExactPositions
    at hsource
  rcases hsource with
    ⟨word, _hvalid, _hlength, _hinstrNe, hget0, hget15,
      hproducer0, hproducer15, hreceipt0, hreceipt15⟩
  exact ⟨word, hget0, hget15, hproducer0, hproducer15,
    hreceipt0, hreceipt15⟩
#print axioms RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer
#print axioms RMQ.Headlines.succinctRMQReviewerPhysicalSourcesExcludeLegacyClose
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryCostedEmptyRange
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryCostedReversedRange
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryCostedOutOfBounds
#print axioms RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid
#print axioms RMQ.Headlines.listIntSuccinctRMQInvalidPhysicalSemantics
#print axioms RMQ.Headlines.listIntSuccinctRMQPhysicalValueFromSuppliedStore
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint
#print axioms RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
#print axioms RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal
#print axioms RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory
#print axioms RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory
#print axioms RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory
#print axioms RMQ.Headlines.succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory
#print axioms RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory
#print axioms RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory
#print axioms RMQ.Headlines.succinctRMQFinalTraceModelAdequacy
#print axioms RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy
#print axioms RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact
#print axioms RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreReadsSubsetFootprint
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadsSubsetFootprint
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreEqGlobalOfFootprint
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostEqTraceLength
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultEventReadWordOrWordRankOrWordSelect
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultSyntheticCostOnlyPrimitiveNotMem
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqTraceLength
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqCost
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe210
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly
#print axioms RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveNotReadWordOrWordRankOrWordSelect
#print axioms RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveMemBreaksNonSyntheticWeightLengthEquality
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal
#print axioms RMQ.Headlines.succinctRMQQueryCostEq
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreExactOfFootprintGlobal
#print axioms RMQ.Headlines.succinctRMQFinalFullModelSoundness
#print axioms RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal
#print axioms RMQ.Headlines.succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal
#print axioms RMQ.Headlines.concreteBPCloseNavigationProfile
#print axioms RMQ.Headlines.concreteBPCloseNavigationGlobalPayloadStoreExecutionStory
#print axioms RMQ.Headlines.concreteBPCloseNavigationGlobalPayloadStoreBoundedExecutionStory
#print axioms RMQ.Headlines.concreteSuccinctBPTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStoreObstruction
#print axioms RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery

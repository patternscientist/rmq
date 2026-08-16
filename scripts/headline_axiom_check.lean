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
#check RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed
#check RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
#print axioms RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed.requiredFacts
#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
#check RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy
#print axioms RMQ.SuccinctClassic.listIntSuccinctRMQReviewerNativeMachineAdequacy
#print axioms RMQ.Headlines.succinctRMQReviewerMachineWellFormed
#print axioms RMQ.Headlines.succinctRMQReviewerMachineRequiredFacts
#print axioms RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy
#print axioms RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint
#print axioms RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreReadSegmentLt
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

-- Packed cell-probe architecture (Stage A). The producer is also audited from
-- `scripts/axiom_check.lean`, but it is the paper's headline claim and is now
-- exported from `RMQPaper`, so its trust story belongs in the headline
-- inventory a reviewer runs: one command, one screenful.
#print axioms RMQ.Headlines.succinctRMQPackedCellProbeArchitecture


/-!
Frozen public expected type for the reviewer-native M1 paper theorem.

This proposition is intentionally written independently of the theorem's
mutable declaration.  The example below uses the paper theorem value itself as
its entire proof; it does not reconstruct any conjunct from the reviewer
packet, certificate fields, `requiredFacts`, or neighboring lemmas.
-/
namespace M1PublicExpectedTypeCheck

-- M1R3-PUBLIC-TYPE-PIN-ANCHOR
def M1ReviewerNativeExpectedPaperType : Prop :=
  RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy /\
  RMQ.SuccinctClassic.queryCost = 210 /\
  RMQ.SuccinctSpace.LittleOLinear RMQ.SuccinctClassic.overhead /\
    forall xs : List Int,
      (RMQ.SuccinctClassic.buildPayload xs).length <=
        2 * xs.length + RMQ.SuccinctClassic.overhead xs.length /\
      RMQ.SuccinctSpace.flattenPayloadWords
          (RMQ.SuccinctClassic.reviewerPhysicalWords xs) =
        RMQ.SuccinctClassic.buildPayload xs /\
      (forall left right,
        RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy
          xs left right) /\
      (forall left right,
        RMQ.ValidRange xs left right ->
          RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
            (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
      (forall left right,
        RMQ.ValidRange xs left right ->
          RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
            (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
      (forall left right,
        RMQ.ValidRange xs left right ->
          ((RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
              (RMQ.SuccinctClassic.cartesianShape xs) left right).trace.map
            RMQ.WordRAM.TraceEvent.nonSyntheticWeight).sum <= 210) /\
      (forall left right,
        (RMQ.SuccinctClassic.queryCosted xs left right).cost <=
          RMQ.SuccinctClassic.queryCost) /\
      (forall left right,
        Not (RMQ.ValidRange xs left right) ->
          (RMQ.SuccinctClassic.queryCosted xs left right).erase = none) /\
      (forall {left len : Nat},
        0 < len ->
          left + len <= xs.length ->
            (RMQ.SuccinctClassic.queryCosted xs left (left + len)).erase =
              some (RMQ.scanWindow xs left len)) /\
      (forall {left len idx : Nat},
        0 < len ->
          left + len <= xs.length ->
            (RMQ.SuccinctClassic.queryCosted xs left (left + len)).erase =
              some idx ->
              RMQ.LeftmostArgMin xs left (left + len) idx) /\
      (forall left right,
        RMQ.SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory
          xs left right) /\
      (forall left right,
        RMQ.ValidRange xs left right ->
          RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
            (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
      (forall left right,
        RMQ.ValidRange xs left right ->
          RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance
            (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
      (forall left right,
        Not (RMQ.ValidRange xs left right) ->
          RMQ.SuccinctClassic.queryTraceResult xs left right =
              RMQ.WordRAM.TraceResult.pure none /\
          RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right =
              RMQ.WordRAM.TraceResult.pure none /\
          RMQ.SuccinctClassic.queryCosted xs left right =
              RMQ.Costed.pure none /\
          RMQ.SuccinctClassic.reviewerPhysicalFootprint xs left right = [] /\
          forall store : RMQ.WordRAM.ReadStore,
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs store left right =
              RMQ.WordRAM.TraceResult.pure none) /\
      (forall (store : RMQ.WordRAM.ReadStore) left right,
        RMQ.ValidRange xs left right ->
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            xs store left right).value =
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (RMQ.SuccinctClassic.cartesianShape xs)
            (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
              (RMQ.SuccinctClassic.cartesianShape xs) store)
            left right).value) /\
      (forall left right,
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
            xs left right).value =
            (RMQ.SuccinctClassic.queryTraceResult xs left right).value /\
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
            xs left right).trace =
            (RMQ.SuccinctClassic.queryTraceResult xs left right).trace.map
              (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent
                (RMQ.SuccinctClassic.cartesianShape xs)) /\
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
            xs left right).toCosted =
            RMQ.SuccinctClassic.queryCosted xs left right) /\
      (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
        RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
            xs storeA storeB left right ->
          RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
              xs storeA left right =
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
              xs storeB left right) /\
      (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
        RMQ.SuccinctClassic.storesAgreeOnOrderedReadFootprint
            xs storeA storeB left right ->
          RMQ.SuccinctClassic.queryTraceResultWithStore
              xs storeA left right =
            RMQ.SuccinctClassic.queryTraceResultWithStore
              xs storeB left right) /\
      (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
        RMQ.SuccinctClassic.storesAgreeOnFootprint xs storeA storeB ->
          RMQ.SuccinctClassic.queryTraceResultWithStore
              xs storeA left right =
            RMQ.SuccinctClassic.queryTraceResultWithStore
              xs storeB left right)

example : M1ReviewerNativeExpectedPaperType :=
  RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem

end M1PublicExpectedTypeCheck

/-!
Frozen public expected type for the packed cell-probe architecture headline.

`RMQ.Headlines.succinctRMQPackedCellProbeArchitecture` is an `abbrev`, so its
type is whatever `PackedReviewerArchitectureCapstone` currently says.  Weaken a
field of that 39-field structure -- `427` to `999`, or drop field 39 -- and the
alias weakens with it silently, while `#print axioms` above still reports the
same three standard axioms.  Axiom checking reports the trust base, never the
statement; only a type can pin a statement.

The proposition below is written independently of the structure: it names the
underlying definitions directly and never mentions
`PackedReviewerArchitectureCapstone`.  The `example` uses the headline value as
its entire proof, projecting the fields it needs; it reconstructs nothing.

It pins exactly the three readings the manuscript's Section 9 theorem
publishes, and nothing more:

  1. complete allocated capacity `2n + rho n`, with `rho` little-o linear;
  2. at most `427` attempted aligned probes into that same memory;
  3. a valid half-open query is actually answered, with an index that is the
     leftmost argmin and agrees with the reference decoder.

Verified to fail closed: changing the cap to `428`, or weakening the third
conjunct's `LeftmostArgMin` to `True`, both stop this file compiling.
-/
namespace PackedCellProbePublicExpectedTypeCheck

-- EG-CP-PUBLIC-TYPE-PIN-ANCHOR
def PackedCellProbeExpectedPaperType : Prop :=
  RMQ.SuccinctSpace.LittleOLinear RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRho /\
  forall (xs : List Int) (left right : Nat),
    ((RMQ.SuccinctFinal.PackedCellProbe.packedReviewerMemory
          (RMQ.SuccinctClassic.cartesianShape xs)).length *
        RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCellWidth
          (RMQ.SuccinctClassic.cartesianShape xs).size <=
      2 * (RMQ.SuccinctClassic.cartesianShape xs).size +
        RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRho
          (RMQ.SuccinctClassic.cartesianShape xs).size) /\
    ((RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRunAgainstMemory
          (RMQ.SuccinctFinal.PackedCellProbe.packedReviewerMemory
            (RMQ.SuccinctClassic.cartesianShape xs))
          (RMQ.SuccinctClassic.cartesianShape xs).size left right).trace.length <= 427) /\
    (left < right -> right <= (RMQ.SuccinctClassic.cartesianShape xs).size ->
      exists index : Nat,
        (RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRunAgainstMemory
            (RMQ.SuccinctFinal.PackedCellProbe.packedReviewerMemory
              (RMQ.SuccinctClassic.cartesianShape xs))
            (RMQ.SuccinctClassic.cartesianShape xs).size left right).terminal =
          some (some index) /\
        (RMQ.SuccinctClassic.queryTraceResult xs left right).value = some index /\
        RMQ.LeftmostArgMin xs left right index)

example : PackedCellProbeExpectedPaperType :=
  ⟨(RMQ.Headlines.succinctRMQPackedCellProbeArchitecture [] 0 0).rho_little_o,
   fun xs left right =>
     ⟨(RMQ.Headlines.succinctRMQPackedCellProbeArchitecture xs left right).allocation_two_n_plus_rho,
      (RMQ.Headlines.succinctRMQPackedCellProbeArchitecture xs left right).derived_cap_le_427,
      (RMQ.Headlines.succinctRMQPackedCellProbeArchitecture xs left right).valid_answer_is_index⟩⟩

end PackedCellProbePublicExpectedTypeCheck

/-!
Persistent counterfactuals for the encoding lower bound's `query_exact`.

The lower bound reads "any encoding answering RMQ exactly needs at least this
many bits". Its force rests entirely on `query_exact` describing a decoder that
really answers RMQ. If that field were satisfiable by something trivial, the
theorem would still be true and would still be about nothing.

Two directions are needed and only one was covered. Non-vacuity of the
HYPOTHESIS is already established inside the theorem itself: the third conjunct
of `exactRMQ_tight_fixed_length_payload_space_bound` exhibits an encoding at
`2 * n` bits, so the quantifier ranges over something. What was missing is the
other direction -- that the hypothesis is not trivially satisfiable.

`null_decoder_impossible` and `wrong_answer_impossible` supply it: a decoder
that answers nothing, and a decoder that answers something wrong, each
contradict `query_exact`. Together with the existing witness they bracket the
hypothesis: inhabited, and not cheaply inhabited.

The final `example` discharges every premise of `null_decoder_impossible`
concretely at `n = 1` except two: the null decoder itself, and **the existence
of an `ExactRMQShapeEncoding`, which it assumes**. An earlier version of this
comment said the null decoder was "the only unmet premise"; that is false, and
DD-20260816-112 records it.

**Scope, stated precisely.** These counterfactuals quantify over
`ExactRMQShapeEncoding`. `exactRMQ_tight_fixed_length_payload_space_bound`
quantifies over `ExactRMQStateEncoding` -- a different structure with its own
`query_exact` field. They are connected only by
`exactRMQShapeEncoding_of_stateEncoding`, whose `query_exact := encoding.query_exact`
makes the coupling hold by construction. So these theorems establish that
`ExactRMQShapeEncoding.query_exact` is not trivially satisfiable, and reach the
cited lower bound only through that bridge. Retargeting them at
`ExactRMQStateEncoding` is open work, not something this file has done. A counterfactual whose premises were jointly unsatisfiable
would prove nothing while looking like a proof.

Verified to fail closed: weakening `wrong_answer_impossible`'s wrong answer
from `+ 1` to `+ 0` stops this file compiling.
-/
namespace ExactRMQQueryExactNonTriviality

-- EG-LB-QUERY-EXACT-COUNTERFACTUAL-ANCHOR

/-- The `n = 1` shape family is inhabited. -/
theorem singleton_mem_shapesOfSize_one :
    RMQ.Cartesian.CartesianShape.node .empty .empty ∈ RMQ.Cartesian.shapesOfSize 1 :=
  RMQ.Cartesian.shapeOfSize_mem_shapesOfSize
    (show RMQ.Cartesian.ShapeOfSize 1
        (RMQ.Cartesian.CartesianShape.node .empty .empty) from
      .node .empty .empty)

/-- `query_exact` forces an answer on every valid window. -/
theorem query_ne_none
    {n bits : Nat} (encoding : RMQ.EncodingLowerBound.ExactRMQShapeEncoding n bits)
    {shape : RMQ.Cartesian.CartesianShape}
    (hmem : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    encoding.query (encoding.encode shape) left (left + len) = none -> False := by
  rw [encoding.query_exact hmem hlen hbound]
  exact fun h => Option.noConfusion h

/-- A decoder that answers nothing cannot inhabit the structure. -/
theorem null_decoder_impossible
    {n bits : Nat} (encoding : RMQ.EncodingLowerBound.ExactRMQShapeEncoding n bits)
    (hnull : forall bs l r, encoding.query bs l r = none)
    {shape : RMQ.Cartesian.CartesianShape}
    (hmem : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) : False :=
  query_ne_none encoding hmem hlen hbound (hnull _ _ _)

/-- A decoder that returns a WRONG answer cannot inhabit the structure either:
`query_exact` pins the value, not merely the presence of one. -/
theorem wrong_answer_impossible
    {n bits : Nat} (encoding : RMQ.EncodingLowerBound.ExactRMQShapeEncoding n bits)
    {shape : RMQ.Cartesian.CartesianShape}
    (hmem : List.Mem shape (RMQ.Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n)
    (hwrong :
      encoding.query (encoding.encode shape) left (left + len) =
        some (RMQ.scanWindow (encoding.sample shape) left len + 1)) : False := by
  rw [encoding.query_exact hmem hlen hbound] at hwrong
  have hvalue := Option.some.inj hwrong
  omega

/-- Non-vacuity, checked rather than argued: every premise of
`null_decoder_impossible` except `hnull` is discharged concretely at `n = 1`. -/
example {bits : Nat} (encoding : RMQ.EncodingLowerBound.ExactRMQShapeEncoding 1 bits)
    (hnull : forall bs l r, encoding.query bs l r = none) : False :=
  null_decoder_impossible encoding hnull singleton_mem_shapesOfSize_one
    (show 0 < 1 by omega) (show 0 + 1 <= 1 by omega)

end ExactRMQQueryExactNonTriviality

/-!
Typed M1 anti-bypass checks.  The positive examples ascribe the exact guarded,
complete-result, value-projection, and canonical-object propositions used by
the paper surface.  The `fail_if_success` examples mechanically reject the
specified weaker or sibling types; they do not treat declaration names or
constructor initialization as evidence.
-/
namespace M1CertificateAntiBypassCheck

example {shape : RMQ.Cartesian.CartesianShape} {left right : Nat}
    (h : RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
      shape left right) :
    RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
      shape left right :=
  h.requiredFacts

example {xs : List Int} {left right : Nat}
    (packet : RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy
      xs left right) :
    RMQ.ValidRange xs left right ->
      RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
        (RMQ.SuccinctClassic.cartesianShape xs) left right :=
  packet.machine_required_facts_of_valid

example {xs : List Int} {left right : Nat}
    (packet : RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy
      xs left right) :
    forall storeA storeB : RMQ.WordRAM.ReadStore,
      RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
          xs storeA storeB left right ->
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            xs storeA left right =
          RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            xs storeB left right :=
  packet.exact_dynamic_physical_store_agreement

example {xs : List Int} {left right : Nat}
    (packet : RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy
      xs left right) :
    forall storeA storeB : RMQ.WordRAM.ReadStore,
      RMQ.ValidRange xs left right ->
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (RMQ.SuccinctClassic.cartesianShape xs)
        (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (RMQ.SuccinctClassic.cartesianShape xs) storeA)
        left right).value ≠
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (RMQ.SuccinctClassic.cartesianShape xs)
        (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (RMQ.SuccinctClassic.cartesianShape xs) storeB)
        left right).value ->
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeA left right).value ≠
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeB left right).value :=
  packet.physical_value_dependency_of_valid

example {xs : List Int} {left right : Nat}
    (hWeak :
      forall storeA storeB : RMQ.WordRAM.ReadStore,
        RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
            xs storeA storeB left right ->
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            xs storeA left right).value =
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            xs storeB left right).value) : True := by
  fail_if_success
    have _ :
        forall storeA storeB : RMQ.WordRAM.ReadStore,
          RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right =
              RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right := hWeak
  trivial

example {shapeA shapeB : RMQ.Cartesian.CartesianShape}
    {left right : Nat}
    (hSibling :
      RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
        shapeB left right) : True := by
  fail_if_success
    have _ :
        RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
          shapeA left right := hSibling
  trivial

example {shape : RMQ.Cartesian.CartesianShape}
    {leftA rightA leftB rightB : Nat}
    (hSibling :
      RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
        shape leftB rightB) : True := by
  fail_if_success
    have _ :
        RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
          shape leftA rightA := hSibling
  trivial

example {xs : List Int} {storeA storeB : RMQ.WordRAM.ReadStore}
    {left right : Nat}
    (hSafe :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs storeA storeB) : True := by
  fail_if_success
    have _ :
        RMQ.SuccinctClassic.storesAgreeOnOrderedReadFootprint
          xs storeA storeB left right := hSafe
  trivial

example {xs : List Int} {storeA storeB : RMQ.WordRAM.ReadStore}
    {left right : Nat}
    (hAggregate :
      RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeA left right ≠
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeB left right) : True := by
  fail_if_success
    have _ :
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeA left right).value ≠
        (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
          xs storeB left right).value := hAggregate
  trivial


example {shape : RMQ.Cartesian.CartesianShape} {left right : Nat}
    (h : RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
      shape left right) :
    ((RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
      RMQ.WordRAM.TraceEvent.nonSyntheticWeight).sum <= 210 :=
  h.requires_certificate_weight_le_210

end M1CertificateAntiBypassCheck

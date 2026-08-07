# Paper Claim Correspondence

## Canonical Claim Rows

| Paper claim | Public alias | Source theorem | Source file | Check |
| --- | --- | --- | --- | --- |
| Uniform all-size canonical global trace has principled charged-trace cost `210`: every actual event is `readWord`, the synthetic fallback is absent, and the `nonSyntheticWeight` certificate sum equals both trace length and the `Costed` cost of the same execution. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, `...SyntheticCostOnlyPrimitiveNotMem`, `...NonSyntheticWeightSumEqTraceLength`, `...NonSyntheticWeightSumEqCost`, `...NonSyntheticWeightSumLe210` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` and corresponding non-synthetic/cost theorems | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| The named component cap is `2*select35 + (2*rank11 + 2*fringe37 + interior33) + rank11 = 210`; `TraceResult.toCosted` charges trace length, while a synthetic event cannot satisfy the genuine-event classification and its presence makes the `nonSyntheticWeight` certificate sum differ from trace length. | `RMQ.Headlines.succinctRMQChargedTraceCostAlgebra`, `RMQ.Headlines.succinctRMQQueryCostEq`, `RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveNotReadWordOrWordRankOrWordSelect`, `RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveMemBreaksNonSyntheticWeightLengthEquality` | `RMQ.SuccinctFinal.CanonicalRMQChargedTraceCostAlgebra`; `RMQ.WordRAM.TraceEvent.syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect`; `...sum_nonSyntheticWeight_ne_length_of_synthetic_mem` | `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/WordRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Footprint-agreeing supplied stores preserve the canonical result and `210` bound. | `RMQ.Headlines.succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Ordinary lists inherit the same principled supplied-store cost transfer. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper` |
| Successful supplied-store reads are backed by the canonical reviewer payload, including the segment-20 component. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| One pre-execution physical word list erases exactly to the public reviewer payload, and the existing supplied-store evaluator reads a supplied flat store through checked address translation. Canonical physical execution refines logical execution with result, cost, ordered trace, failures, repetitions, and footprint preserved. | `RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload`, `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical`, `RMQ.Headlines.succinctRMQReviewerPhysicalFootprintRecorded`, `RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter` | `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`; `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/wordram_axiom_check.lean`; `lake env lean scripts/headline_axiom_check.lean` |
| Agreement on the first physical execution's consumed ordered footprint determines the complete physical execution. At the answer projection, the flat value is exactly the translated supplied-store evaluator value; differing translated evaluator values imply differing physical values, and a decisive singleton corruption changes `some 0` to `none`. | `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint`, `RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore`, `RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint`, `...FlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator`, `...FlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne`, plus the six validation guards | `RMQ/Core/SuccinctFinalStoreParam.lean`; `RMQ/Validation/SuccinctClassic.lean` | `lake env lean scripts/wordram_axiom_check.lean`; `lake env lean scripts/headline_axiom_check.lean`; `lake build RMQExamples` |
| One exhaustive typed 22-source universe (23 logical segments; segments 0 and 19 share the BP-code source) includes canonical close and the fringe/select chunk-table sources. For the current query, every indexed read retains its global/program/local occurrences, folded state, exact invocation parameters, source, and multiplicity-preserving embedding. Separately, the query-independent manifest packet proves that every counted source and shared-BP consumer has some successful actual closed-valid query witness; that the fringe chunk table (segment 21) has a successful witness for each of its three reader leaves; and that both chunk-table segments carry repeated-equal-read witnesses with two distinct indexed provenance receipts on one actual valid execution. The successful positive predicate bridges to the arbitrary-result mutation predicate, and fresh segment 23 fails that common relation. Source-region exclusivity, logical-segment coverage, and legacy-slot exclusion remain checked. | `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy`, `RMQ.Headlines.listIntSuccinctRMQRawAdequacyOfValid`, `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance`, `RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence`, `RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence`, `RMQ.Headlines.succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer`, `RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer` | `RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace_getElem?_producer`, `...evalGlobalWordTrace_getElem?_read_invocation`, `...WholeQueryOccurrenceProvenance_checked`, `...ReviewerManifestSemanticAdequacy`, `...ReviewerSource_counted_successful_closed_valid_occurrence`, `...ReviewerSharedBPConsumer_successful_closed_valid_occurrence`, `ReviewerProducerClaim.hasOperationalProducer_of_successful`, `...FreshUnusedCanonicalSource_no_producer`, `...ReviewerPhysicalSources_nodup`, `...ReviewerSource_region_injective`, `...ReviewerSegmentSource?_coverage`, `...ReviewerPhysicalSources_exclude_legacy_close`, `...CanonicalReviewerReadStore_legacyTail_none` | `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/SuccinctFinal/RAM/ReviewerReachability*.lean`; `RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean`; `RMQ/Core/SuccinctRMQClassicProvenance.lean` | `lake env lean scripts/wordram_axiom_check.lean`; `lake env lean scripts/headline_axiom_check.lean` |
| The whole-query reviewer capacity is linear and one query-independent logarithmic word width bounds physical words, successful returned words, consumed physical addresses, and charged primitive data. | `RMQ.Headlines.succinctRMQReviewerPhysicalWordsFitLinearCapacity`, `RMQ.Headlines.succinctRMQReviewerWordBitsLogarithmic`, `RMQ.Headlines.succinctRMQReviewerPhysicalWordFits`, `RMQ.Headlines.succinctRMQReviewerSuccessfulReadWordFits`, `RMQ.Headlines.succinctRMQReviewerPhysicalFootprintAddressFits` | Corresponding `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewer*` and `...WholeQueryFlatPhysical*` theorems | `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`; `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/wordram_axiom_check.lean`; `lake env lean scripts/headline_axiom_check.lean` |
| One validity boundary rejects invalid or empty ranges across canonical, supplied-store, trace, costed, and physical list surfaces. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid`, `...QueryCostedEmptyRange`, `...QueryCostedReversedRange`, `...QueryCostedOutOfBounds` | `RMQ.SuccinctClassic.queryCosted_invalid`, `...queryCosted_empty_range`, `...queryCosted_reversed_range`, `...queryCosted_out_of_bounds`, plus the corresponding trace/supplied-store/physical invalid theorems | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |

Earlier cost and dispatch rows are deliberately excluded from this current
correspondence table and live in the explicit
[`compatibility history`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).


This document maps paper-facing claims to checked Lean names and exact
reviewer commands. Its role is different from `../artifact/CLAIMS.md`: that
file is a compact artifact claims packet, while this file is organized by how a
paper or reviewer table would cite the result.

For code orientation and import boundaries, use `CODE_MAP.md`. For the
one-command artifact gate, use `../artifact/README.md` and
`../scripts/reproduce_artifact.sh`.

The narrow paper import root is `RMQPaper`, which imports
`RMQ.Headlines.RMQ`. The supporting-spoke rows near the end of this document are
checked repository surfaces, but they are deliberately outside the RMQ paper
root.

## How To Read The Table

The `Lean alias` column gives the public name a paper should cite when one is
available. The `Source theorem` column gives the construction-level theorem or
record packaged by the alias. The `Exact check command` is intentionally
concrete: it is the smallest advertised command in this repository that prints
the relevant `#print axioms` surface, or the reproduction command that runs the
whole paper artifact gate.

The proof trust base is Lean kernel checking of the committed declarations
under the pinned toolchain. Axiom scripts and hygiene scans are reviewer and
reproducibility checks around that kernel-checked surface.

## Main RMQ Claims

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Main paper theorem over ordinary `List Int`: existing payload/answer/invalid/provenance facts plus guarded reviewer-native certificate, independent 24-field required facts, guarded four-link list packet, literal same-execution weighted-trace bound `<= 210`, and complete supplied-store result equality under exact ordered dynamic-read agreement. | `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` via `RMQ.Headlines.RMQ` / `RMQPaper` | `RMQ.SuccinctClassic.listIntSuccinctRMQReviewerNativeMachineAdequacy`; `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed.requiredFacts` | `RMQ/Headlines/RMQ.lean`; `RMQ/Core/SuccinctRMQClassic.lean`; `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean`; `scripts/m1_certificate_mutation_regression.ps1` |
| The current 24-field certificate and independent required-facts consumer use the same canonical execution and expose `sum (map nonSyntheticWeight trace) <= 210`, filled from the named current trace theorem derived through the principled charged-trace equality. | `RMQ.Headlines.succinctRMQReviewerMachineWellFormed`; `RMQ.Headlines.succinctRMQReviewerMachineRequiredFacts`; `RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed`; `...MachineRequiredFacts`; `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210` | `RMQ/Core/SuccinctFinalModelAdequacy.lean`; `RMQ/Core/SuccinctFinalRAM.lean` | `lake build RMQ.Core.SuccinctFinalModelAdequacy`; `lake env lean scripts/headline_axiom_check.lean` |
| Short list-facing succinct RMQ profile: the same public payload, exact range semantics, no-synthetic physical execution story, and canonical modeled query cost. | `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Canonical construction-facing profile over Cartesian shapes: doubled-Catalan envelopes, canonical reviewer payload at most `2*n + o(n)`, exact physical erasure, direct positional physical backing for every successful trace read, exact canonical global-trace answers, non-synthetic certificate weight equal to trace length and the same `Costed.cost`, and uniform bound `210`. | `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Information-theoretic exact RMQ lower bound in doubled Catalan slack form. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack` | `RMQ/Core/EncodingLowerBound.lean` | `lake env lean scripts/headline_axiom_check.lean` |

## Final Trace And Model Adequacy

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Final trace model-adequacy packet: `Costed` equals `TraceResult.toCosted`, the trace refines the interpreted whole-query program, event data are bounded, no synthetic cost-only markers occur, and successful reads are backed by counted flat payload. The accepted route's separate strong theorem proves every event is `readWord`. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` | `RMQ/Core/SuccinctFinalModelAdequacy.lean`; `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exactness paired with the final trace model-adequacy packet. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Supplied-store adequacy: reads report the caller-provided store, the canonical global store recovers the canonical trace, no synthetic markers occur, and footprint agreement gives store-parametricity. | `RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Full model-soundness packet combining trace adequacy, supplied-store adequacy, footprint containment, and footprint-agreement transfer. | `RMQ.Headlines.succinctRMQFinalFullModelSoundness` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exact RMQ answers for any supplied store agreeing with the canonical global store on the declared footprint. | `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Successful supplied-store reads are backed by the canonical reviewer payload under footprint agreement. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Modeled cost bound transfers to footprint-agreeing supplied stores. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Final all-size globally segmented execution story: reads agree with the concrete global store, and the separate strong current theorem proves every emitted event is `readWord`. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Bounded all-size execution story: payload-read addresses and exposed primitive operands/results fit a trace-local finite width. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| All-size no-synthetic execution story for the final global trace. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Flat-payload no-synthetic execution story tying successful reads to one query-independent counted flat payload layout. | `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing flat-payload no-synthetic execution story. | `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing safe-footprint supplied-store equality is a corollary of exact agreement on the first execution's ordered dynamic reads and equality of the complete `TraceResult`. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint` | `RMQ.SuccinctClassic.storesAgreeOnOrderedReadFootprint_of_footprint`; `RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`; `RMQ.SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store exactness under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store all-size cost transfer under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |

## Compatibility And History Boundary

Historical query profiles and conservative envelopes remain kernel-checked in
their source modules and are re-exported only by
`RMQ.Headlines.RMQCompatibility` under names containing `Legacy` or
`Compatibility`. They are intentionally absent from `RMQPaper`, from the
current claim rows above, and from the headline axiom inventory.
The literal-pinned historical identity is
`RMQ.SuccinctClassic.canonicalTransitionalQueryCost = 328`; the separately
named live raw-expression compatibility constant is
`RMQ.SuccinctClassic.liveCompatibilityQueryCost = 352`.

## Supporting Spoke Claims

These rows are checked for the full repository, but `RMQPaper` does not import
the standalone rank/select public capstones, standalone BP-navigation public
capstones, or their current obstruction/history rows.

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Standalone Jacobson/Clark-style rank/select family with `n + o(n)` payload and constant modeled access/rank/select. | `RMQ.Headlines.rankSelectNPlusOConstantQuery` | `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` | `RMQ/Core/RankSelectPublic/Capstones.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Fixed-weight compressed/FID rank/select family: compressed payload plus `o(n)` auxiliary payload and constant modeled access/rank/select. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile` | `RMQ/Core/RankSelectPublic/Capstones.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Interpreted fixed-weight compressed/FID rank/select family. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` | `RMQ/Core/RankSelectPublicRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| No-synthetic compressed/FID global-store fused capstone. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile` | `RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile` | `RMQ/Core/RankSelectPublicRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Concrete BP close-navigation profile consumed by the final succinct RMQ path. | `RMQ.Headlines.concreteBPCloseNavigationProfile` | `RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile` | `RMQ/Core/BPNavigationPublic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Concrete BP close-navigation global payload-store execution story. | `RMQ.Headlines.concreteBPCloseNavigationGlobalPayloadStoreExecutionStory` | `RMQ.BPNavigation.concreteBPCloseNavigationGlobalTrace_execution_story` | `RMQ/Core/BPNavigationRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Checked obstruction for reusing the current close/LCA store as the matching-open leg for fuller succinct tree navigation. | `RMQ.Headlines.concreteSuccinctBPTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStoreObstruction` | `RMQ.BPNavigation.concreteSuccinctTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStore_obstruction` | `RMQ/Core/BPNavigationRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |

## Packed Cell-Probe Architecture (Stage A, accepted 2026-08-07)

| Claim | Public identity | Source declaration | File | Check |
| --- | --- | --- | --- | --- |
| One allocated `header ++ buildPayload ++ padding` packed memory answers every valid half-open query with the leftmost minimum's index, in at most `427` attempted aligned `w(n)`-bit cell probes into that same memory, with complete allocated capacity `2n + o(n)`, under a closed controller whose dynamic inputs are exactly `n`, the endpoints, and prior probe replies. | `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone` | `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds` | `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean` | `lake env lean scripts/axiom_check.lean` |
| Complete allocated capacity, counting header cell, every payload cell and final padding at full cell width, is at most `2n + rho(n)` with `rho` little-`o`-linear. | field 8 `allocation_two_n_plus_rho` with field 9 `rho_little_o` | same producer | same file (`:356`, `:361`) | same |
| Every valid half-open query's terminal state carries an index equal to the reference leftmost-minimum answer. | field 39 `valid_answer_is_index` | same producer | same file | same |
| Attempted probes are capped by the derived numeral `427`. | field `derived_cap_le_427` | same producer | same file (`:490`) | same |

Reading rules for this block, each of which a reader will otherwise get wrong:

- `427` is an upper bound derived from the run's own measure, **not** an
  attainment claim; the pinned fixture issues 68 probes.
- The result is **cell-probe**: computation between probes is free and
  controller steps are uncharged. It is not word-RAM time, not preprocessing
  time, not measured runtime.
- The `210` in `427 = 1 + 2*3 + 2*210` is the packed controller's structural
  fuel and is **a different quantity** from the canonical route's charged-trace
  `210` in the table above, despite being the same numeral. They are provably
  independent; nothing under `PackedCellProbe/` references
  `SuccinctClassic.queryCost` or `nonSyntheticWeight`.

## Reproduction Commands

The table above uses focused per-row commands. The reviewer one-command path is:

```bash
bash scripts/reproduce_artifact.sh
```

That script runs the build, public root builds, validation executable,
headline/WordRAM/full axiom checks, the PowerShell gate when available,
forbidden-token scans, reduction-shortcut scans, and whitespace checks.

Validation and examples are not proof trust-base components. They are smoke and
reviewer checks; theorem truth comes from Lean kernel checking of declarations
under the pinned toolchain.

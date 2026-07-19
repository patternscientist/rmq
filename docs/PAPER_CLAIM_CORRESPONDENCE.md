# Paper Claim Correspondence

## Canonical Claim Rows

| Paper claim | Public alias | Source theorem | Source file | Check |
| --- | --- | --- | --- | --- |
| Uniform all-size canonical global trace has principled charged-trace cost `207`: universally over that accepted trace, every actual event is `readWord` (the compatibility constructors `wordRank` and `wordSelect` are never emitted on this route), the synthetic fallback is absent, and the `nonSyntheticWeight` certificate sum equals both trace length and the `Costed` cost of the same execution. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, `...SyntheticCostOnlyPrimitiveNotMem`, `...NonSyntheticWeightSumEqTraceLength`, `...NonSyntheticWeightSumEqCost`, `...NonSyntheticWeightSumLe207` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` and the corresponding no-synthetic/`nonSyntheticWeight` theorems over the same `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` object | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| The named component cap is `2*select35 + (2*rank11 + 2*fringe37 + interior30) + rank11 = 207`; `TraceResult.toCosted` charges trace length, while a synthetic event cannot satisfy the genuine-event classification and its presence makes the `nonSyntheticWeight` certificate sum differ from trace length. | `RMQ.Headlines.succinctRMQChargedTraceCostAlgebra`, `RMQ.Headlines.succinctRMQQueryCostEq`, `RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveNotReadWordOrWordRankOrWordSelect`, `RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveMemBreaksNonSyntheticWeightLengthEquality` | `RMQ.SuccinctFinal.CanonicalRMQChargedTraceCostAlgebra`; `RMQ.WordRAM.TraceEvent.syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect`; `...sum_nonSyntheticWeight_ne_length_of_synthetic_mem` | `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/WordRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Footprint-agreeing supplied stores preserve the canonical result and `207` bound. | `RMQ.Headlines.succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
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
| Main paper theorem over ordinary `List Int`: literal `queryCost = 207`, `buildPayload.length <= 2*n + overhead n`, `overhead = o(n)`, invalid-range rejection, exact valid half-open leftmost answers, physical erasure, final no-synthetic execution, and current-query adequacy/provenance. | `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` via `RMQ.Headlines.RMQ` / `RMQPaper` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` plus canonical adequacy consumers | `RMQ/Headlines/RMQ.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| Short list-facing succinct RMQ profile: the same public payload, exact range semantics, no-synthetic physical execution story, and canonical modeled query cost. | `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Canonical construction-facing profile over Cartesian shapes: doubled-Catalan envelopes, canonical reviewer payload at most `2*n + o(n)`, exact physical erasure, direct positional physical backing for every successful trace read, exact canonical global-trace answers, non-synthetic certificate weight equal to trace length and the same `Costed.cost`, and uniform bound `207`. | `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Information-theoretic exact RMQ lower bound in doubled Catalan slack form. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack` | `RMQ/Core/EncodingLowerBound.lean` | `lake env lean scripts/headline_axiom_check.lean` |

## Final Trace And Model Adequacy

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Final trace model-adequacy packet: `Costed` equals `TraceResult.toCosted`, the trace refines the interpreted whole-query program, event data are bounded, no synthetic cost-only markers occur, and successful reads are backed by counted flat payload. Its read-or-primitive field is weaker compatibility support; on that same accepted trace, the current signature proves every event is `readWord`. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` | `RMQ/Core/SuccinctFinalModelAdequacy.lean`; `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exactness paired with the final trace model-adequacy packet. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Supplied-store adequacy: reads report the caller-provided store, the canonical global store recovers the canonical trace, no synthetic markers occur, and footprint agreement gives store-parametricity. | `RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Full model-soundness packet combining trace adequacy, supplied-store adequacy, footprint containment, and footprint-agreement transfer. | `RMQ.Headlines.succinctRMQFinalFullModelSoundness` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exact RMQ answers for any supplied store agreeing with the canonical global store on the declared footprint. | `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Successful supplied-store reads are backed by the canonical reviewer payload under footprint agreement. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Modeled cost bound transfers to footprint-agreeing supplied stores. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Final all-size globally segmented execution story: every event on the accepted trace is `readWord`, and reads agree with the concrete global store. The generic read-or-primitive theorem is retained as weaker supporting evidence for the same trace object. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Bounded all-size execution story: payload-read addresses and exposed primitive operands/results fit a trace-local finite width. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| All-size no-synthetic execution story for the final global trace. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Flat-payload no-synthetic execution story tying successful reads to one query-independent counted flat payload layout. | `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing flat-payload no-synthetic execution story. | `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store query equality under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint` | `RMQ.SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store exactness under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store all-size cost transfer under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |

## Compatibility And History Boundary

Historical query profiles and conservative envelopes remain kernel-checked in
their source modules and are re-exported only by
`RMQ.Headlines.RMQCompatibility` under names containing `Legacy` or
`Compatibility`. They are intentionally absent from `RMQPaper`, from the
current claim rows above, and from the headline axiom inventory.

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

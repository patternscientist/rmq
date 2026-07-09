# Paper Claim Correspondence

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
| Main paper theorem over ordinary `List Int`: advertised `2*n + overhead`, `overhead = o(n)`, exact half-open leftmost RMQ answers, constant modeled query cost, and final no-synthetic flat-payload execution story. | `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` via `RMQ.Headlines.RMQ` / `RMQPaper` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| Short list-facing succinct RMQ profile: `2*n + o(n)` payload and constant modeled query cost for valid list queries. | `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | `RMQ.SuccinctClassic.listInt_two_n_plus_o_constant_query_profile` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Construction-facing BP-native succinct RMQ upper-bound profile over Cartesian shapes, paired with doubled-Catalan slack comparison. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile` | `RMQ/Core/SuccinctFinal.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Information-theoretic exact RMQ lower bound in doubled Catalan slack form. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack` | `RMQ/Core/EncodingLowerBound.lean` | `lake env lean scripts/headline_axiom_check.lean` |

## Final Trace And Model Adequacy

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Final trace model-adequacy packet: `Costed` equals `TraceResult.toCosted`, the trace refines the interpreted whole-query program, events are reads or word primitives, event data are bounded, no synthetic cost-only markers occur, and successful reads are backed by counted flat payload. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exactness paired with the final trace model-adequacy packet. | `RMQ.Headlines.succinctRMQFinalTraceModelAdequacyExact` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Supplied-store adequacy: reads report the caller-provided store, the canonical global store recovers the canonical trace, no synthetic markers occur, and footprint agreement gives store-parametricity. | `RMQ.Headlines.succinctRMQFinalSuppliedStoreAdequacy` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Full model-soundness packet combining trace adequacy, supplied-store adequacy, footprint containment, and footprint-agreement transfer. | `RMQ.Headlines.succinctRMQFinalFullModelSoundness` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Exact RMQ answers for any supplied store agreeing with the canonical global store on the declared footprint. | `RMQ.Headlines.succinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Successful supplied-store reads are backed by counted flat payload under footprint agreement. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCountedFlatPayloadOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Modeled cost bound transfers to footprint-agreeing supplied stores. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Final all-size globally segmented execution story: every event is a payload read or word primitive, and reads agree with the concrete global store. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Bounded all-size execution story: payload-read addresses and exposed primitive operands/results fit a trace-local finite width. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| All-size no-synthetic execution story for the final global trace. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Flat-payload no-synthetic execution story tying successful reads to one query-independent counted flat payload layout. | `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing flat-payload no-synthetic execution story. | `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store query equality under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint` | `RMQ.SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store exactness under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| List-facing supplied-store all-size cost transfer under final footprint agreement with the canonical global store. | `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |

## Cost Regimes And Compatibility Rows

| Paper theorem / claim row | Lean alias | Source theorem | Source file | Exact check command |
| --- | --- | --- | --- | --- |
| Conservative all-size query-cost statement: the final global trace cost is bounded by the named all-size cost expression, and that expression computes to the fixed modeled constant `196727`. | `RMQ.Headlines.succinctRMQQueryCostEq`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe`, `RMQ.Headlines.succinctRMQFinalTraceModelAdequacy`, and `RMQ.Headlines.succinctRMQFinalFullModelSoundness` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost_eq`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le`, `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy`, and `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness` | `RMQ/Core/SuccinctFinal.lean`; `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Fast-regime theorem for the same final global trace: modeled cost at most `118` under `SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= shape.size`, where the real readiness threshold is `2^15`. | `RMQ.Headlines.succinctRMQFastRegimeGlobalPayloadStoreCostLeOfReadyThreshold` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_of_size_ge_readyThreshold` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Fast-regime supplied-store cost transfer under footprint agreement. | `RMQ.Headlines.succinctRMQFastRegimeSuppliedStoreCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_of_size_ge_readyThreshold` | `RMQ/Core/SuccinctFinalStoreParam.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Fast-regime full-model cost theorem under footprint agreement. | `RMQ.Headlines.succinctRMQFastRegimeFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_of_size_ge_readyThreshold` | `RMQ/Core/SuccinctFinalModelAdequacy.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| List-facing fast-regime supplied-store full-model cost transfer under footprint agreement and the Ready-threshold condition on `(SuccinctClassic.cartesianShape xs).size`. | `RMQ.Headlines.listIntSuccinctRMQFastRegimeFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.listIntFastRegimeFinalFullModelCostLeOfFootprintGlobal` | `RMQ/Core/SuccinctRMQClassic.lean` | `lake build RMQPaper`; `lake env lean scripts/headline_axiom_check.lean` |
| Large-regime compatibility theorem with an explicit `2^128 <= shape.size` premise where the existing theorem surface says so. This is not the current readiness explanation for the fast path. | `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |
| Bounded large-regime compatibility companion. | `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story` | `RMQ/Core/SuccinctFinalRAM.lean` | `lake env lean scripts/headline_axiom_check.lean` |

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

# Claims Packet

This file is a compact public-facing map from headline claims to the exact
Lean theorem surfaces that support them. It is intentionally narrower than
`docs/FAMILY_SUMMARY.md`: use it when auditing what the repository currently
claims, what it does not claim, and which command checks the relevant surface.

For the reviewer path through the artifact, start with `import RMQPaper` and
the RMQ-only headline module `RMQ.Headlines.RMQ`; see `README.md`.
For a concise map of public import roots, final theorem spines, proof-core
files, compatibility shims, archive surfaces, examples, and validation code,
see `../docs/CODE_MAP.md`.
For a paper-row correspondence table with source files and exact check
commands, see `../docs/PAPER_CLAIM_CORRESPONDENCE.md`.

## Scope

- The project is Mathlib-free: Lean 4, Std, and `omega`.
- Correctness statements use the repository's half-open, leftmost RMQ contract.
- Cost statements are model-level statements, not compiled Lean execution
  benchmarks.
- Payload-space statements count modeled stored bits, not proof-only fields.
- Word-RAM statements concern the explicit `WordRAM` model and trace events.

## Headline RMQ Claims

| Claim | Public theorem alias | Source theorem | Check command |
| --- | --- | --- | --- |
| Exact RMQ requires essentially `2*n` bits in the fixed-length payload model, with doubled Catalan slack. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` via `RMQ.Headlines.RMQ` | `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack` | `lake build RMQPaper` and `lake env lean scripts/headline_axiom_check.lean` |
| The BP-native succinct RMQ family answers exact RMQ queries with `2*n + o(n)` payload bits and constant modeled query cost, paired with a numeric doubled-Catalan slack comparison. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` via `RMQ.Headlines.RMQ` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile` | `lake build RMQPaper` and `lake env lean scripts/headline_axiom_check.lean` |
| The ordinary `List Int` succinct RMQ surface combines the classic half-open leftmost contract, the existing `2*n + o(n)` counted-payload story, and the final flat-payload no-synthetic WordRAM execution story. | `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_execution_story` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |
| The same RMQ family has a closed `WordRAM`/register-program query controller over interpreted leaves. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same RMQ family emits an explicit domain-leaf trace before projection back to `Costed`. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same RMQ family emits a unified `WordRAM.TraceEvent` stream for the final query. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| In the large regime, the WordRAM final query routes the compact close/LCA leg through structural local/fringe/interior trace replay rather than the all-size fallback. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |
| The final all-size RMQ query has one globally segmented payload-store execution story: every event is a payload read or word primitive, and every payload read agrees with the concrete global store. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same all-size global trace is store-extensional: any read store agreeing with the concrete global store on emitted payload-read events validates the same trace. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The zero-block same-block close leaf has a store-parametric evaluator: two supplied stores agreeing on BP-code segment reads produce the same value and trace. | `RMQ.Headlines.succinctRMQZeroBlockSameBlockStoreParametric` | `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.zeroBlockSameBlockCloseStructuralTraceResult_store_parametric` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same global execution story has a finite trace-local bit width bounding every payload-read address and every natural operand/result exposed by word primitives. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| In the Ready-threshold fast regime, the final globally segmented BP-native RMQ trace has modeled query cost at most `118`, excluding the zero-block same-block and active non-Ready bounded scans. | `RMQ.Headlines.succinctRMQFastRegimeGlobalPayloadStoreCostLeOfReadyThreshold` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_of_size_ge_readyThreshold` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |
| The same all-size global trace is structurally replayed without dedicated synthetic cost-only marker events. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The no-synthetic execution story is tied to one query-independent flat payload layout with source/component/offset backing evidence for successful reads. | `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The large-regime global-store execution story also has the same bounded-address and bounded-primitive-operand packet under the explicit size premise. | `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |

## Rank/Select And BP Claims

These are checked repository spokes and remain in the aggregate
`RMQ.Headlines` barrel. They are not imported by `RMQPaper`.

| Claim | Public theorem alias | Source theorem | Check command |
| --- | --- | --- | --- |
| Standalone Jacobson/Clark rank/select gives `n + o(n)` payload bits and constant modeled query cost. | `RMQ.Headlines.rankSelectNPlusOConstantQuery` | `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` | `lake env lean scripts/headline_axiom_check.lean` |
| The word-bounded Jacobson/Clark surface keeps the same family profile with bounded concrete payload words. | `RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery` | `RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery` | `lake env lean scripts/headline_axiom_check.lean` |
| Fixed-weight compressed/FID rank/select has a family theorem with compressed payload plus `o(n)` overhead and constant modeled query cost. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile` | `lake env lean scripts/headline_axiom_check.lean` |
| The compressed/FID family has an interpreted WordRAM bridge. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` | `lake env lean scripts/wordram_axiom_check.lean` |
| The compressed/FID global-store capstone also has component-backed successful reads and no synthetic cost-only trace events. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile` | `RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile` | `lake env lean scripts/headline_axiom_check.lean` |
| BP close-navigation has a conditional interpreted component-level `2*n + o(n)`, constant-query profile, assuming a supplied word-bounded sampled encoded close-navigation family. | `RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` | `RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile` | `lake env lean scripts/headline_axiom_check.lean` |

## Non-Claims

- The `WordRAM` model is not a proof about Lean's compiled runtime.
- The BP-native capstone's doubled-Catalan clause is a numeric theorem-surface
  comparison. The encoding-quantified fixed-length lower-bound statement is
  the separate public theorem
  `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`.
- The all-size final RMQ query now has a single global payload-store execution
  theorem and a no-synthetic structural replay theorem. The flat-payload theorem
  is an execution-story layout theorem; the separately cited `2*n + o(n)`
  theorem remains the asymptotic payload theorem.
- The large-regime WordRAM theorem still carries an explicit size premise as a
  compatibility strengthening. The public all-input theorem is total,
  store-backed, and structurally dispatches the compact close/LCA path; legacy
  finite-small interior store slots `26` and `27` read as `none` and are not
  part of the counted flat payload.
- The current concrete BP-native query-cost bound is the fixed model constant
  `196727`. It includes bounded all-size scans below
  `SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold = 2^15`; this is a
  disclosed model constant, not a hidden asymptotic variable. The separate
  fast-regime theorem under that readiness premise proves the named constant
  `SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost = 118`.
- The bounded execution-story theorem supplies a trace-local finite bit width
  for exposed addresses and primitive operands. It is not yet a tight
  asymptotic machine-word side-condition for every component.
- Proof-only fields and certificates are not counted as payload bits.
- Register arithmetic and branching are model-control operations, not charged
  machine instructions in the current model.
- The BP close-navigation headline is a conditional component theorem; the repo
  does not yet expose a concrete witness inhabiting
  `WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily`.

## Current Provenance Frontier

The global payload-store theorem, no-synthetic all-size structural replay, and
Ready-threshold fast-regime cost theorem are landed. The live hardening frontier
is now tighter rather than existential: push the trace-local event-width theorem
toward component-level machine-word side conditions consumed by the public
capstone, package the artifact/paper claim correspondence, and reuse the
flat-store / no-synthetic pattern in the rank/select and BP-navigation spokes.

# Claims Packet

This file is a compact public-facing map from headline claims to the exact
Lean theorem surfaces that support them. It is intentionally narrower than
`docs/FAMILY_SUMMARY.md`: use it when auditing what the repository currently
claims, what it does not claim, and which command checks the relevant surface.

## Scope

- The project is Mathlib-free: Lean 4, Std, and `omega`.
- Correctness statements use the repository's half-open, leftmost RMQ contract.
- Cost statements are model-level statements, not Lean-runtime benchmarks.
- Payload-space statements count modeled stored bits, not proof-only fields.
- Word-RAM statements concern the explicit `WordRAM` model and trace events.

## Headline RMQ Claims

| Claim | Public theorem alias | Source theorem | Check command |
| --- | --- | --- | --- |
| Exact RMQ requires essentially `2*n` bits in the fixed-length payload model, with doubled Catalan slack. | `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack` | `lake env lean scripts/headline_axiom_check.lean` |
| The BP-native succinct RMQ family answers exact RMQ queries with `2*n + o(n)` payload bits and constant modeled query cost. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile` | `lake env lean scripts/headline_axiom_check.lean` |
| The same RMQ family has a closed first-order query controller over interpreted leaves. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same RMQ family emits an explicit domain-leaf trace before projection back to `Costed`. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same RMQ family emits a unified `WordRAM.TraceEvent` stream for the final query. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile` | `lake env lean scripts/wordram_axiom_check.lean` |
| In the large regime, the WordRAM final query routes the compact close/LCA leg through structural local/fringe/interior trace replay rather than the all-size fallback. | `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime` | `RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |

## Rank/Select And BP Claims

| Claim | Public theorem alias | Source theorem | Check command |
| --- | --- | --- | --- |
| Standalone Jacobson/Clark rank/select gives `n + o(n)` payload bits and constant modeled query cost. | `RMQ.Headlines.rankSelectNPlusOConstantQuery` | `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` | `lake env lean scripts/headline_axiom_check.lean` |
| The word-bounded Jacobson/Clark surface keeps the same family profile with bounded concrete payload words. | `RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery` | `RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery` | `lake env lean scripts/headline_axiom_check.lean` |
| Fixed-weight compressed/FID rank/select has a family theorem with compressed payload plus `o(n)` overhead and constant modeled query cost. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile` | `lake env lean scripts/headline_axiom_check.lean` |
| The compressed/FID family has an interpreted WordRAM bridge. | `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile` | `lake env lean scripts/wordram_axiom_check.lean` |
| BP close-navigation has an interpreted component-level `2*n + o(n)`, constant-query profile. | `RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` | `RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile` | `lake env lean scripts/headline_axiom_check.lean` |

## Non-Claims

- The `WordRAM` model is not a proof about Lean's compiled runtime.
- The current final RMQ trace is not yet a single globally laid-out payload
  store theorem. Component traces currently use local segment numbering.
- The current large-regime WordRAM theorem does not remove the explicit size
  premise; the all-input wrapper remains total for correctness.
- Proof-only fields and certificates are not counted as payload bits.
- Register arithmetic and branching are model-control operations, not charged
  machine instructions in the current model.

## Current Provenance Frontier

The live hardening target is a global payload-store provenance theorem for the
final RMQ trace. The first honest intermediate theorem is component-local:
every event in the large-regime final stream is either a non-read primitive or
comes from one of the concrete select-close, compact close/LCA, or answer-rank
component traces. A stronger single-store theorem needs a segment relabeling
layer and one global payload layout.

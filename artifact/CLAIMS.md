# Claims Packet

## Canonical Reviewer Payload And Trace

The occurrence-provenance layer preserves an exhaustive typed universe of 22
physical sources over logical segments `0..22`, including canonical close;
logical segments `0` and `19` share the BP-code source. It sits inside one
whole-machine physical word list. That
list erases exactly to the public `SuccinctClassic.buildPayload`. The existing
supplied-store evaluator runs through an adapter that actually reads the supplied
flat store at checked translated addresses; canonical flat-physical execution
preserves decoded result, modeled cost, ordered successes and failures, repeated
reads, and the execution-derived footprint. Agreement on the first execution's
consumed ordered physical footprint determines the complete physical
`TraceResult`, while a checked consumed-address disagreement witness proves that
the evaluator observes its supplied store. The linear capacity and
query-independent logarithmic width bound
all stored/returned words, physical addresses, and charged primitive data.
For every indexed read in the global trace, the checked relation retains that same global
occurrence, its program-instruction occurrence, exact folded prefix state,
component-local occurrence, invocation parameters, source, and offset in the
composed trace for that exact query. Separately, the query-independent manifest
packet proves every counted source and named shared-BP consumer has some
successful witness through an actual closed whole-query execution under a
valid ordinary `List Int` query. Fresh unused segment `23` is rejected by the
same common closed-valid-occurrence predicate; live segment `21` is the fringe
chunk table. A checked bridge runs from the
successful positive predicate to the mutation-side arbitrary-result predicate.
The singleton executable regression checks that identical events at global
positions `0` and `15`, produced by program instructions `0` and `1`, remain
distinct obligations. Earlier event-value and
component may-read facts remain compatibility facts only.
The unchanged canonical execution now has the checked principled charged-trace
cap `207 = 2*35 + (2*11 + 2*37 + 30) + 11`, and modeled cost is exactly emitted
trace length. The emitted payload-word reads are charged;
controller dispatch, input/register access, arithmetic, branching, decoding,
local scanning, candidate merging, trace assembly, and the validity guard are
currently uncharged. Earlier cost and dispatch theorems are documented only in
the explicit
[`compatibility history`](../docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
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
| The canonical reviewer payload and canonical global trace form one construction-facing profile: doubled-Catalan envelopes, `2*n + o(n)` payload, exact physical erasure, direct positional physical backing for every successful read, exact RMQ answers, non-synthetic certificate weight equal to trace length and the same `Costed.cost`, and the uniform bound `207`. | `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile` via `RMQ.Headlines.RMQ` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile` | `lake build RMQPaper` and `lake env lean scripts/headline_axiom_check.lean` |
| The ordinary `List Int` succinct RMQ surface proves `buildPayload.length <= 2*n + overhead n` with `overhead = o(n)`, rejects invalid or empty ranges, preserves the classic valid half-open leftmost contract, and supplies the final no-synthetic execution story. Exact physical erasure is separate and no padding is used. | `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory`, `RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid` | `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`, `RMQ.SuccinctClassic.queryCosted_invalid` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |
| The reviewer capstone is genuine supplied flat-physical execution, determined by its first consumed ordered footprint; its `.value` is exactly the translated supplied-store evaluator value, and a decisive singleton corruption changes the answer. | `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical`, `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint`, `RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore`, `RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency` | Corresponding `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical*` projection and footprint theorems plus the validation guards | `lake env lean scripts/wordram_axiom_check.lean`, `lake env lean scripts/headline_axiom_check.lean`, and `lake build RMQExamples` |
| The reviewer provenance layer preserves indexed occurrences and exact invocation parameters for the current trace. A separate query-independent packet gives every counted source and shared-BP consumer some successful closed-valid whole-query witness, checks the positive-to-mutation bridge, and rejects fresh segment `23` with the common predicate. | `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance`, `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy`, `RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence`, `RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence`, `RMQ.Headlines.succinctRMQReviewerSuccessfulOccurrenceImpliesOperationalProducer`, `RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`, `...ReviewerManifestSemanticAdequacy`, `...ReviewerSource_counted_successful_closed_valid_occurrence`, `...ReviewerSharedBPConsumer_successful_closed_valid_occurrence`, `ReviewerProducerClaim.hasOperationalProducer_of_successful`, `...FreshUnusedCanonicalSource_no_producer` | `lake env lean scripts/wordram_axiom_check.lean` and `lake env lean scripts/headline_axiom_check.lean` |
| The ordinary `List Int` supplied-store surface runs `SuccinctClassic.queryCostedWithStore` against a caller-provided store agreeing with `SuccinctClassic.globalReadStore xs` on the checked footprint: equality, valid-window exactness, and the principled all-size charged-trace cost `207` transfer. | `RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint`, `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`, `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | `RMQ.SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint`, `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal`, `RMQ.SuccinctClassic.listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal` | `lake build RMQPaper` and `lake env lean scripts/headline_axiom_check.lean` |
| The final all-size RMQ query has one globally segmented payload-store execution story: every event is a payload read or word primitive, and every payload read agrees with the concrete global store. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The same all-size global trace is store-extensional: any read store agreeing with the concrete global store on emitted payload-read events validates the same trace. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The canonical reviewer word model uses an input/addressable-store/sentinel capacity; its component occupies an exact physical suffix and every consumed interior physical address plus valid query operand fits the derived word width. | `RMQ.Headlines.succinctRMQCanonicalReviewerMachineWordsComponentSlice`, `RMQ.Headlines.succinctRMQCanonicalInteriorPhysicalFootprintFits`, `RMQ.Headlines.succinctRMQCanonicalReviewerValidQueryOperandsFit` | Corresponding `RMQ.SuccinctFinal` theorems | `lake env lean scripts/wordram_axiom_check.lean` |
| The uniform canonical reviewer trace has the principled charged-trace bound `207`. Every actual emitted event is `readWord`, `wordRank`, or `wordSelect`; the trace contains no synthetic marker, so its direct `WordRAM.TraceEvent.nonSyntheticWeight` certificate sum equals both trace length and the `Costed` cost of the same execution, and is at most `207`. `TraceResult.toCosted` itself charges trace length and would count a synthetic compatibility marker if one were present. | `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultEventReadWordOrWordRankOrWordSelect`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultSyntheticCostOnlyPrimitiveNotMem`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqTraceLength`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqCost`, `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe207` | Corresponding `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_*` theorems; `RMQ.WordRAM.TraceEvent.nonSyntheticWeight` | `lake env lean scripts/headline_axiom_check.lean` and `lake env lean scripts/wordram_axiom_check.lean` |
| The same all-size global trace is structurally replayed without dedicated synthetic cost-only marker events. | `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |
| The no-synthetic execution story is tied to one query-independent flat payload layout with source/component/offset backing evidence for successful reads. | `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story` | `lake env lean scripts/wordram_axiom_check.lean` |

Historical direct/interpreted/leaf/word profiles remain checked only through
`RMQ.Headlines.RMQCompatibility` and its explicitly `Legacy`/`Compatibility`
aliases. They are outside `RMQPaper` and outside this current-claim table.

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
- Earlier conditional WordRAM strengthening and retired dispatch details live
  only in the explicit compatibility history. The public all-input theorem is
  total and store-backed; legacy finite-small interior store slots `26` and
  `27` read as `none` and are not part of the counted flat payload.
- The canonical reviewer route has the principled charged-trace bound `207`.
  It does not charge controller operations and is not a conventional word-RAM
  theorem. Earlier checked cost and dispatch surfaces are indexed in the
  explicit compatibility history rather than repeated here.
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

The canonical segment-`20` component-store route, supplied-store
parametricity, counted-payload backing, total reviewer width, edge-case
evidence, and principled `207` charged-trace cap are consumed by
the public all-size path. The next cost-model consumer is E1: define richer
controller-instruction semantics and prove a fully charged small-step
simulation of this same execution. The current theorem exposes only the actual emitted
`WordRAM.TraceEvent` stream and its direct weights; controller dispatch,
arithmetic, branching, decoding, local scanning, and merging remain
documentary uncharged omissions rather than a checked substitute machine.
Serialized-payload querying, complete preprocessing, and conventional
word-RAM claims remain separate M1/E1/construction obligations. Rank/select
and BP-navigation retain their own separate hardening frontiers.

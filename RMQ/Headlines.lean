import RMQ.Core.EncodingLowerBound
import RMQ.Core.BPNavigationPublic
import RMQ.Core.BPNavigationRAM
import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectPublicRAM
import RMQ.Core.SuccinctSpace.BPCloseRMQNavigationRAM
import RMQ.Core.SuccinctFinal
import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.SuccinctRMQClassic

/-!
Short public aliases for the main citeable theorem surfaces.

The original declarations keep their precise construction-heavy names. This
module gives README/public-facing names to the same checked objects without
changing theorem statements or proof dependencies.
-/

namespace RMQ.Headlines

/-- Tight fixed-length RMQ lower bound with the doubled Catalan slack form. -/
abbrev exactRMQLowerBoundDoubledCatalanSlack :=
  RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack

/-- Standalone Jacobson/Clark rank/select family: `n + o(n)`, constant query. -/
abbrev rankSelectNPlusOConstantQuery :=
  RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery

/--
Standalone Jacobson/Clark rank/select family with the same `n + o(n)`,
constant-query profile plus machine-word-bounded concrete payload reads.
-/
abbrev rankSelectWordBoundedNPlusOConstantQuery :=
  RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery

/-- Fixed-weight compressed/FID rank/select, pointwise form. -/
abbrev rankSelectCompressedFIDFixedWeightConstantQuery :=
  RMQ.RankSelect.compressedFIDFixedWeightConstantQueryProfile

/-- Fixed-weight compressed/FID rank/select family: compressed payload plus `o(n)`, constant query. -/
abbrev rankSelectCompressedFIDFixedWeightFamilyProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile

/--
Interpreted fixed-weight compressed/FID rank/select family: same compressed
payload and constant-query theorem shape, with access/rank/select reads routed
through `WordRAM` bridges.
-/
abbrev rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile

/--
Fused fixed-weight compressed/FID rank/select capstone: compressed payload plus
`o(n)`, constant exact access/rank/select, interpreted WordRAM replay, one
target-independent global payload store, and bounded trace-local event widths.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreFusedProfile

/--
No-synthetic fused fixed-weight compressed/FID rank/select capstone:
compressed payload plus `o(n)`, constant exact access/rank/select,
interpreted WordRAM replay, one target-independent global payload store,
bounded trace-local event widths, successful-read component backing, and no
synthetic cost-only trace events.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile

/--
Target-independent global payload-store execution story for fixed-weight
compressed/FID rank/select. For each fixed `bits`, access, rank false/true,
and select false/true traces all read from one concrete global read store.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_execution_story

/--
Bounded target-independent global payload-store execution story for
fixed-weight compressed/FID rank/select. It extends the shared access/rank
false/true/select false/true store packet with trace-local bit widths for
payload-read addresses and word-primitive operands/results.
-/
abbrev rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightGlobalPayloadStore_bounded_execution_story

/--
Target-indexed global payload-store execution story for fixed-weight
compressed/FID rank/select. For each fixed `bits` and `target`, access, rank,
and select traces are relabeled into one concrete read store.
-/
abbrev rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_execution_story

/--
Bounded target-indexed global payload-store execution story for fixed-weight
compressed/FID rank/select. It extends the combined access/rank/select global
store packet with trace-local bit widths for payload-read addresses and
word-primitive operands/results.
-/
abbrev rankSelectCompressedFIDFixedWeightTargetGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.RankSelect.compressedFIDFixedWeightTargetGlobalPayloadStore_bounded_execution_story

/--
BP-native succinct RMQ capstone: exact RMQ, `2*n + o(n)`, constant query, and
a numeric doubled-Catalan lower-bound comparison in the same theorem surface.
The encoding-quantified lower-bound theorem is exposed separately as
`exactRMQLowerBoundDoubledCatalanSlack`.
-/
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

/--
Classic list-facing succinct RMQ theorem: for every ordinary `xs : List Int`,
the built payload has length `2*n + o(n)` and valid half-open queries return
the exact leftmost RMQ answer within constant modeled query cost.
-/
abbrev succinctRMQListIntTwoNPlusOConstantQuery :=
  RMQ.SuccinctClassic.listInt_two_n_plus_o_constant_query_profile

/--
List-facing flat-payload no-synthetic execution story: for every ordinary
`xs : List Int`, the same final query keeps the classic half-open/leftmost
RMQ contract and constant modeled query story while its global WordRAM trace is
backed by one query-independent counted flat payload layout/read store: every
actual successful read has source/component/offset evidence, event data are
bounded, and no synthetic cost-only events occur. The flat execution payload is
the advertised `2*n + o(n)` `buildPayload`, with no finite-small same-block
appendix; retired finite-small interior slots have empty stores.
-/
abbrev listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story

/--
Whole-query-interpreted BP-native succinct RMQ capstone: the same two-sided
`2*n + o(n)`, constant-query theorem shape, with the final query control routed
through a closed first-order query program whose leaves are the interpreted
close-select, compact close/LCA, and answer-rank operations.
-/
abbrev succinctRMQTwoNPlusOConstantQueryInterpreted :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile

/--
Leaf-trace-preserving BP-native succinct RMQ capstone: the same theorem shape
as the whole-query-interpreted headline, with the closed controller evaluating
to an explicit domain-leaf trace before projection back to `Costed`.
-/
abbrev succinctRMQTwoNPlusOConstantQueryLeafTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile

/--
Unified-`WordRAM.TraceEvent` BP-native succinct RMQ capstone. The final query
control now emits one `TraceEvent` stream. Select-close, answer-rank, and
compact-close rank-seed reads are structural payload/register traces; the
all-size global execution story below additionally replaces the former
close-navigation fallback leaves with a structural BP-code zero-block
same-block scan and the all-size structural cross-block interior route.
-/
abbrev succinctRMQTwoNPlusOConstantQueryWordTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile

/--
Large-regime unified-`WordRAM.TraceEvent` BP-native succinct RMQ capstone. This
has the same two-sided `2*n + o(n)`, constant-query theorem shape, but the query
clauses carry the explicit size hypothesis that lets the compact close/LCA leg
expand through the Ready local/fringe/interior trace replay. The public
all-size route is also structural: Ready two-level, active bounded summary
scan, or inactive pure-none.
-/
abbrev succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile

/--
Large-regime globally segmented `WordRAM.TraceEvent` BP-native succinct RMQ
capstone. This strengthens the large-regime word-trace headline by relabeling
the final query's select, rank, and compact close/LCA payload reads into one
shared segment convention. The matching execution-story theorem below proves
those events agree with one concrete payload store.
-/
abbrev succinctRMQTwoNPlusOConstantQueryGlobalWordTraceLargeRegime :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_global_word_trace_large_regime_profile

/--
Public execution-story theorem for the final all-size succinct RMQ query: the
query is the `Costed` projection of one globally segmented `WordRAM` trace,
refines the whole-query interpreter, every event is a payload read or bounded
word primitive, and every payload read agrees with the single concrete global
read store. The final all-size global trace consumes the structural compact
close/LCA path, so the former close-navigation `TraceResult.ofCosted` fallback
leaves are no longer on this path.
-/
abbrev succinctRMQGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story

/--
Store-extensional execution-story theorem for the final all-size succinct RMQ
query. Any read store that agrees with the concrete global store on the
payload-read events emitted by the query validates the same trace.
-/
abbrev succinctRMQGlobalPayloadStoreExtensionalExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_store_extensional_execution_story

/--
Bounded execution-story theorem for the final all-size succinct RMQ query. This
extends `succinctRMQGlobalPayloadStoreExecutionStory` with a concrete finite
trace-local bit width bounding every payload-read address and every natural
operand/result exposed by word-local primitive events.
-/
abbrev succinctRMQGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story

/--
All-size structural execution-story theorem for the final all-size succinct
RMQ query. This is the citation anchor for the globally segmented trace after
the zero-block same-block and cross-block interior close-navigation leaves have
been replaced by structural BP-code, bounded-summary, and two-level payload
traces.
-/
abbrev succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_allSizeStructural_execution_story

/--
No-synthetic all-size execution-story theorem for the final succinct RMQ query.
This strengthens the structural story by proving that the globally segmented
trace contains no dedicated `TraceEvent.syntheticCostOnlyPrimitive` events.
-/
abbrev succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story

/--
Flat-payload no-synthetic execution story for the final succinct RMQ query.
This is the strongest current execution-model citation: the final query reads
from one query-independent counted flat payload layout, every actual successful
payload read has a source/component/offset backing witness, all events are
reads or bounded word-local primitives, and no event is the synthetic cost-only
marker. The flat payload is exactly the advertised BP-native build payload.
Cross-block interior replay is all-size structural: Ready shapes use the
compact two-level directory, active non-Ready shapes use a bounded summary scan,
and inactive shapes have no interior read obligation.
-/
abbrev succinctRMQFlatPayloadStoreNoSyntheticExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story

/--
Large-regime companion to `succinctRMQGlobalPayloadStoreExecutionStory`; this
uses the positive-block local/fringe/interior close-navigation replay under the
explicit `2^128 <= shape.size` compatibility premise. It is no longer the
theorem used to justify the old numeric compatibility story in the all-size
payload story.
-/
abbrev succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story

/--
Large-regime bounded companion to
`succinctRMQGlobalPayloadStoreBoundedExecutionStory`.
-/
abbrev succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story

/--
Concrete payload-backed BP close-navigation profile. This is the preferred
current BP-close navigation citation: it fixes the concrete relative-split
close-access family and compact relative-rmM close/LCA directory, proving
`2*n + o(n)` payload, constant modeled query cost, exact Cartesian-shape RMQ
answer semantics, and machine-word-bounded component payload reads.
-/
abbrev concreteBPCloseNavigationProfile :=
  RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile

/--
Concrete BP close-navigation global payload-store execution story. This
consumes `concreteBPCloseNavigationFamily_profile`'s concrete query surface and
proves the costed query is the `toCosted` projection of a globally segmented
`WordRAM.TraceResult` whose payload reads match one concrete store.
-/
abbrev concreteBPCloseNavigationGlobalPayloadStoreExecutionStory :=
  RMQ.BPNavigation.concreteBPCloseNavigationGlobalTrace_execution_story

/--
Bounded concrete BP close-navigation global payload-store execution story. This
adds a finite trace-local bit width bounding payload-read addresses and
word-primitive operands/results for the same concrete global trace.
-/
abbrev concreteBPCloseNavigationGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.BPNavigation.concreteBPCloseNavigationGlobalTrace_bounded_execution_story

/--
Checked obstruction for the current close/LCA-store adapter route toward a
fuller succinct BP tree-navigation execution story. The existing concrete
close/LCA WordRAM trace cannot be reused as the matching-open leg required by
public parent/enclose/subtree navigation.
-/
abbrev concreteSuccinctBPTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStoreObstruction :=
  RMQ.BPNavigation.concreteSuccinctTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStore_obstruction

/--
Interpreter-backed BP close-navigation profile: `2*n + o(n)`, constant query,
with rank/select/LCA leaves routed through the first-order `WordRAM` bridges.

This is a conditional component-level profile: it requires a supplied
word-bounded sampled encoded close-navigation family. The final BP-native RMQ
capstone has its own constructed interpreter-backed headlines above.
-/
abbrev bpCloseNavigationInterpretedTwoNPlusOConstantQuery
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :=
  RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile
    family

end RMQ.Headlines

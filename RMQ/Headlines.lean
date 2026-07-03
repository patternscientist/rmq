import RMQ.Core.EncodingLowerBound
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

/-- BP-native succinct RMQ capstone: exact RMQ, `2*n + o(n)`, constant query. -/
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
compact-close rank-seed reads are structural payload/register traces; bounded
local/fringe/interior close-navigation leaves remain explicit charged fallback
boundaries in tiny/inactive all-size cases. The large-regime execution-story
alias below is the stronger global payload-store provenance theorem.
-/
abbrev succinctRMQTwoNPlusOConstantQueryWordTrace :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile

/--
Large-regime unified-`WordRAM.TraceEvent` BP-native succinct RMQ capstone. This
has the same two-sided `2*n + o(n)`, constant-query theorem shape, but the query
clauses carry the explicit size hypothesis that lets the compact close/LCA leg
expand through the structural local/fringe/interior trace replay instead of the
all-size fallback.
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
read store. Tiny/inactive close-navigation fallback work appears only as
synthetic word-primitive events, not as payload reads.
-/
abbrev succinctRMQGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_execution_story

/--
Bounded execution-story theorem for the final all-size succinct RMQ query. This
extends `succinctRMQGlobalPayloadStoreExecutionStory` with a concrete finite
trace-local bit width bounding every payload-read address and every natural
operand/result exposed by word-local primitive events.
-/
abbrev succinctRMQGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_bounded_execution_story

/--
Large-regime companion to `succinctRMQGlobalPayloadStoreExecutionStory`; this
uses the positive-block local/fringe/interior close-navigation replay under the
explicit `2^128 <= shape.size` premise.
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
Interpreter-backed BP close-navigation profile: `2*n + o(n)`, constant query,
with rank/select/LCA leaves routed through the first-order `WordRAM` bridges.

This is a component-level profile; the final BP-native RMQ capstone also has an
interpreter-backed headline above.
-/
abbrev bpCloseNavigationInterpretedTwoNPlusOConstantQuery
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :=
  RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile
    family

end RMQ.Headlines

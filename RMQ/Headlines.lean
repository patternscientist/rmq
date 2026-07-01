import RMQ.Core.EncodingLowerBound
import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectPublicRAM
import RMQ.Core.SuccinctSpace.BPCloseRMQNavigationRAM
import RMQ.Core.SuccinctFinal
import RMQ.Core.SuccinctFinalRAM

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

/-- BP-native succinct RMQ capstone: exact RMQ, `2*n + o(n)`, constant query. -/
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

/--
Whole-query-interpreted BP-native succinct RMQ capstone: the same two-sided
`2*n + o(n)`, constant-query theorem shape, with the final query control routed
through a closed first-order query program whose leaves are the interpreted
close-select, compact close/LCA, and answer-rank operations.
-/
abbrev succinctRMQTwoNPlusOConstantQueryInterpreted :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile

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

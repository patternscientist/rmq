import RMQ.Core.EncodingLowerBound
import RMQ.Core.GenericSelectBuilder
import RMQ.Core.SuccinctFinal

/-!
Short public aliases for the main citeable theorem surfaces.

The original declarations keep their precise construction-heavy names. This
module gives README/demo-facing names to the same checked objects without
changing theorem statements or proof dependencies.
-/

namespace RMQ.Headlines

/-- Tight fixed-length RMQ lower bound with the doubled Catalan slack form. -/
abbrev exactRMQLowerBoundDoubledCatalanSlack :=
  RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack

/-- Standalone Jacobson/Clark rank/select family: `n + o(n)`, constant query. -/
abbrev rankSelectNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile

/-- BP-native succinct RMQ capstone: exact RMQ, `2*n + o(n)`, constant query. -/
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

end RMQ.Headlines

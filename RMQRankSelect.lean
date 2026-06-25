import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctRankProposal
import RMQ.Core.SuccinctSelectProposal
import RMQ.Core.GenericSelectParams
import RMQ.Core.GenericSelectPrimitives
import RMQ.Core.GenericSelectBuilder

/-!
# Standalone rank/select spoke

This import root exposes the plain-bitvector rank/select surface without
importing RMQ windows, Cartesian trees, Fischer-Heun, LCA, or the final RMQ
capstone modules.

The public headline theorem is
`RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile`.
-/

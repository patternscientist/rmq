import RMQ.Core.RankSelectSpec
import RMQ.Core.GenericSelect.Family

/-!
Public facade for the standalone rank/select spoke.

The construction modules keep detailed Jacobson/Clark and sparse-exception
names. This module gives the reusable bitvector surface short, neutral names
for downstream data-structure spokes.
-/

namespace RMQ.RankSelect

/-- Public bitvector rank/select directory shape. -/
abbrev Directory :=
  RMQ.RankSelectSpec.BitVectorRankSelectDirectory

/-- Public bitvector rank/select family shape. -/
abbrev Family :=
  RMQ.RankSelectSpec.BitVectorRankSelectFamily

/-- Auxiliary-overhead budget for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkOverhead :=
  RMQ.GenericSelect.jacobsonClarkRankSelectOverhead

/-- Uniform modeled query cost for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkQueryCost :=
  RMQ.GenericSelect.jacobsonClarkRankSelectQueryCost

/-- Concrete Jacobson/Clark directory for one stored bitvector. -/
abbrev jacobsonClarkDirectory :=
  RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory

/-- Concrete Jacobson/Clark rank/select family. -/
abbrev jacobsonClarkFamily :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily

/--
Public `n + o(n)`, constant-query theorem for the concrete Jacobson/Clark
rank/select family.
-/
abbrev jacobsonClarkNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile

end RMQ.RankSelect

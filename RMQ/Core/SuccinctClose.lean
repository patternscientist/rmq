import RMQ.Core.SuccinctClose.BlockLocal
import RMQ.Core.SuccinctClose.RangeSummary
import RMQ.Core.SuccinctClose.RelativeSummary
import RMQ.Core.SuccinctClose.RangeWitness
import RMQ.Core.SuccinctClose.EndpointFringe
import RMQ.Core.SuccinctClose.RelativeRmmMacro

/-!
# Succinct BP close proposal helpers

Thin import barrel for the split BP close/LCA proposal layers. The old
`RMQ.Core.SuccinctCloseProposal` module remains as a compatibility import root
for downstream users that still import the historical proposal name.
-/

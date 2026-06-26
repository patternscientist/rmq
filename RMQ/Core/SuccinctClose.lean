import RMQ.Core.SuccinctClose.BlockLocal
import RMQ.Core.SuccinctClose.RangeSummary
import RMQ.Core.SuccinctClose.RelativeSummary
import RMQ.Core.SuccinctClose.RangeWitness
import RMQ.Core.SuccinctClose.EndpointFringe
import RMQ.Core.SuccinctClose.RelativeRmmMacro

/-!
# Succinct BP close navigation

Thin import barrel for the split BP close/LCA navigation layers. New code should
import this module and use the canonical `RMQ.SuccinctClose` namespace. The old
`RMQ.Core.SuccinctCloseProposal` module remains as a compatibility import root.
-/

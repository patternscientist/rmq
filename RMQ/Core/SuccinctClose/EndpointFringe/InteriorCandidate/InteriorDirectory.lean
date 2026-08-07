import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.ValueDependency

/-!
# Endpoint-fringe relative-rmM interior directory

Split from `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.

This module is a hub: the declarations live in `.Base`,
`.SparseLevelWidth`, and `.ValueDependency`, chained by import in that
order. Downstream code imports this module and is unaffected by the
split.
-/

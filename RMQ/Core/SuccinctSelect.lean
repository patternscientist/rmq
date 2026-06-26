import RMQ.Core.SuccinctSelect.TwoLevel
import RMQ.Core.SuccinctSelect.Obstructions
import RMQ.Core.SuccinctSelect.DenseLocalTables
import RMQ.Core.SuccinctSelect.CloseSelect

/-!
# Succinct select construction

Canonical import barrel for the select-side helper layers, two-level
rank/select adapters, and the remaining C1-specific sparse/dense relative-split
close locator. The historical `RMQ.Core.SuccinctSelectProposal` module is now a
compatibility root for old imports and namespace names.
-/

import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalSemanticProvenanceAdequacy

/-!
# Proof-only W19 manifest provenance import seam

The paper surface imports the query-independent reviewer-manifest packet here.
Keeping this module separate preserves the executable validator's genuine
`SuccinctRMQClassic` path without linking the large symbolic witness families
into its native runtime.  There is intentionally no `List Int`/`ValidRange`
wrapper for the global existential source-liveness facts.
-/

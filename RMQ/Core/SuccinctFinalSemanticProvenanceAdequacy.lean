import RMQ.Core.SuccinctFinalModelAdequacy
import RMQ.Core.SuccinctFinal.RAM.ReviewerReachability

/-!
# W19 semantic-provenance adequacy for the final succinct RMQ model

This proof-only extension keeps the symbolic source witnesses out of the
native validator link closure while making their successful closed-valid-query
reachability a required consumer of the final trace-model adequacy packet.
-/

namespace RMQ.SuccinctFinal

/-- The final trace-model adequacy packet together with W19's nonvacuous
closed-valid-query reachability obligations for every counted source and every
named shared-BP consumer. -/
structure ConcreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop where
  finalTraceModelAdequacy :
    ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right
  canonical_counted_sources_have_successful_closed_valid_occurrence :
    forall source : ReviewerSource, source.Counted ->
      source.HasSuccessfulClosedValidOccurrence
  all_shared_bp_dependencies_have_successful_closed_valid_occurrence :
    forall consumer : ReviewerSharedBPConsumer,
      consumer.HasSuccessfulClosedValidOccurrence

/-- The concrete final model discharges the W19 semantic-provenance extension
with the actual small, symbolic long-super, and symbolic sparse-local witness
families. -/
theorem concreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy
      shape left right :=
  { finalTraceModelAdequacy :=
      concreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right
    canonical_counted_sources_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence
    all_shared_bp_dependencies_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence }

end RMQ.SuccinctFinal

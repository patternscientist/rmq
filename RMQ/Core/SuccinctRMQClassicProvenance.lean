import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalSemanticProvenanceAdequacy

/-!
# List-facing W19 semantic provenance

The public proof story consumes the W19 proof-only final-model adequacy
extension.  Keeping this module separate preserves the executable validator's
genuine `SuccinctRMQClassic` path without linking the large symbolic witness
families into its native runtime.
-/

namespace RMQ.SuccinctClassic

/-- A valid ordinary `List Int` query exposes the proof-only W19 extension of
the final trace-model adequacy packet. -/
theorem flatPayloadStoreNoSyntheticExecutionStory_semanticProvenanceAdequacy_of_valid
    (xs : List Int) (left right : Nat) (_hvalid : ValidRange xs left right) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy
      (cartesianShape xs) left right :=
  SuccinctFinal.concreteBPNativeSuccinctRMQFinalSemanticProvenanceAdequacy
    (cartesianShape xs) left right

/-- Under the valid List-facing story, every counted source has a successful
occurrence in some actual closed valid whole-query execution. -/
theorem reviewerCountedSource_successfulClosedValidOccurrence_of_valid
    (xs : List Int) (left right : Nat) (hvalid : ValidRange xs left right)
    (source : SuccinctFinal.ReviewerSource) (hcounted : source.Counted) :
    source.HasSuccessfulClosedValidOccurrence :=
  (flatPayloadStoreNoSyntheticExecutionStory_semanticProvenanceAdequacy_of_valid
    xs left right hvalid).canonical_counted_sources_have_successful_closed_valid_occurrence
      source hcounted

/-- Under the valid List-facing story, each named shared-BP consumer has a
successful occurrence through its exact leaf in a closed valid execution. -/
theorem reviewerSharedBPConsumer_successfulClosedValidOccurrence_of_valid
    (xs : List Int) (left right : Nat) (hvalid : ValidRange xs left right)
    (consumer : SuccinctFinal.ReviewerSharedBPConsumer) :
    consumer.HasSuccessfulClosedValidOccurrence :=
  (flatPayloadStoreNoSyntheticExecutionStory_semanticProvenanceAdequacy_of_valid
    xs left right hvalid).all_shared_bp_dependencies_have_successful_closed_valid_occurrence
      consumer

end RMQ.SuccinctClassic

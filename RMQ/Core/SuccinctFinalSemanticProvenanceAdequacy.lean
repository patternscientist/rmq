import RMQ.Core.SuccinctFinal.RAM.ReviewerReachability

/-!
# W19 reviewer-manifest semantic adequacy

This proof-only packet keeps the symbolic source witnesses out of the native
validator link closure.  Its claims are deliberately not parameterized by a
current shape or query: each live manifest source has some successful closed
valid execution witness, while indexed forward provenance remains in the
query-specific final trace-model packet.
-/

namespace RMQ.SuccinctFinal

/-- Query-independent semantic adequacy of the canonical reviewer manifest.
The positive predicate is successful indexed occurrence in some actual closed
whole-query execution under a valid ordinary-list query.  The mutation
predicate is the same existential execution relation with arbitrary read
result, and the checked bridge below relates the two. -/
structure ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy : Prop where
  canonical_counted_sources_have_successful_closed_valid_occurrence :
    forall source : ReviewerSource, source.Counted ->
      source.HasSuccessfulClosedValidOccurrence
  all_shared_bp_dependencies_have_successful_closed_valid_occurrence :
    forall consumer : ReviewerSharedBPConsumer,
      consumer.HasSuccessfulClosedValidOccurrence
  successful_closed_valid_occurrence_implies_operational_producer :
    forall claim : ReviewerProducerClaim,
      claim.HasSuccessfulClosedValidOccurrence -> claim.HasOperationalProducer
  fresh_unused_source_rejected_by_operational_producer :
    ¬ concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.HasOperationalProducer
  canonical_manifest_nodup :
    List.Nodup concreteBPNativeSuccinctRMQReviewerPhysicalSources
  canonical_segments_complete :
    forall segment : Nat,
      (Exists fun source =>
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source) <->
          segment < 22

/-- The concrete manifest discharges the global W19 packet using the actual
small, symbolic long-super, and symbolic sparse-local witness families. -/
theorem concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy :
    ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy :=
  { canonical_counted_sources_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence
    all_shared_bp_dependencies_have_successful_closed_valid_occurrence :=
      concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence
    successful_closed_valid_occurrence_implies_operational_producer :=
      fun _ hclaim =>
        ReviewerProducerClaim.hasOperationalProducer_of_successful hclaim
    fresh_unused_source_rejected_by_operational_producer :=
      concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer
    canonical_manifest_nodup :=
      concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup
    canonical_segments_complete :=
      concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage }

end RMQ.SuccinctFinal

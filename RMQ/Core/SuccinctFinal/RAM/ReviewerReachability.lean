import RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall
import RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilityLong
import RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySparse

/-!
The closed-valid-query reachability theorem for the complete canonical
reviewer-source universe.  The three imported modules isolate the executable
small witnesses, the symbolic long-super witness, and the symbolic
sparse-local witness so the public theorem remains narrow and auditable.
-/

namespace RMQ.SuccinctFinal

/-- Every counted canonical source is successfully read in some actual closed
whole-query execution of a valid ordinary `List Int` query. -/
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence
    (source : ReviewerSource) (_hsource : source.Counted) :
    source.HasSuccessfulClosedValidOccurrence := by
  have hcluster :
      source ∈
          [ .sharedBPCode
          , .finalRankSuperFalse
          , .finalRankBlockFalse
          , .selectSuperBaseOccurrence
          , .selectSuperBaseWordIndex
          , .selectSuperRankBefore
          , .selectSuperFirstOffset
          , .selectLocalBaseOccurrence
          , .selectLocalBaseWordIndex
          , .selectLocalRankBefore
          , .selectLocalFirstOffset
          , .canonicalClose
          , .fringeChunkTable
          , .selectChunkTable ] ∨
      source ∈
          [ .selectLongFlagRankSuperTrue
          , .selectLongFlagRankBlockTrue
          , .selectLongFlagBits
          , .selectLongRelative ] ∨
      source ∈
          [ .selectSparseRankSuperTrue
          , .selectSparseRankBlockTrue
          , .selectSparseFlagBits
          , .selectSparseRelative ] := by
    cases source <;> simp
  rcases hcluster with hsmall | hlong | hsparse
  · exact
      concreteBPNativeSuccinctRMQReviewerSource_small_successful_closed_valid_occurrence
        source hsmall
  · exact
      concreteBPNativeSuccinctRMQReviewerSource_long_successful_closed_valid_occurrence
        source hlong
  · exact
      concreteBPNativeSuccinctRMQReviewerSource_sparse_successful_closed_valid_occurrence
        source hsparse

end RMQ.SuccinctFinal

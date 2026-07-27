import RMQ.Core.SuccinctFinal.RAM.SourceInventory
open RMQ
namespace C06SI

/-- Expected type written from the row's clause, not from the module. -/
def ExpectedCoverage : Prop :=
  ∀ (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore) (left right : Nat)
    (segment index : Nat) (word? : Option WordRAM.Word),
    WordRAM.TraceEvent.readWord segment index word? ∈
        (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape store left right).trace →
      ∃ source : SuccinctFinal.ReviewerSource,
        source ∈ SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources ∧
        SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
        segment ∈ SuccinctFinal.SourceInventory.reviewerSourceLogicalSegments source ∧
        SuccinctFinal.ReviewerSource.region source < 22

example : ExpectedCoverage := by
  intro shape store l r segment index word? hmem
  exact SuccinctFinal.SourceInventory.storeParametricRead_hasListedSource shape store l r hmem

/-- The source universe is closed and fully enumerated: 22 constructors, all listed. -/
example (source : SuccinctFinal.ReviewerSource) :
    source ∈ SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources := by
  cases source <;> decide

example : SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalSources.length = 22 := by
  decide

end C06SI

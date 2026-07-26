import RMQ.Core.SuccinctFinalStoreParam

/-!
QZ-F03: one item on the prior agent's "NOT closed" residual list is simply
wrong.  They listed

    `ite: idx < occurrenceCount bits target`
    (SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore)

as "a branch on content that did not come from a probe".  On the route,
`bits` is `shape.bpCode`, and the popcount of a balanced-parenthesis code is
*forced* by its size: exactly `n` opens and `n` closes.  So that guard is
`idx < n` -- verdict S, not a content branch.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose

namespace QZPop

/-- Number of `true` bits of any shape's BP code is exactly `shape.size`. -/
theorem occurrenceCount_bpCode_true (s : CartesianShape) :
    GenericSelect.occurrenceCount s.bpCode true = s.size := by
  unfold GenericSelect.occurrenceCount
  exact bpCode_rankTrue_full s

/-- Number of `false` bits of any shape's BP code is exactly `shape.size`. -/
theorem occurrenceCount_bpCode_false (s : CartesianShape) :
    GenericSelect.occurrenceCount s.bpCode false = s.size := by
  unfold GenericSelect.occurrenceCount
  exact SuccinctSpace.bpCode_rankFalse_full s

/-- Hence the guard is size-congruent across ALL shapes of a common size. -/
theorem occurrenceCount_congr {a b : CartesianShape} (h : a.size = b.size)
    (target : Bool) :
    GenericSelect.occurrenceCount a.bpCode target =
      GenericSelect.occurrenceCount b.bpCode target := by
  cases target with
  | true => rw [occurrenceCount_bpCode_true, occurrenceCount_bpCode_true, h]
  | false => rw [occurrenceCount_bpCode_false, occurrenceCount_bpCode_false, h]

/-- Every derived slot count is therefore size-only too. -/
theorem superSlotCount_congr {a b : CartesianShape} (h : a.size = b.size)
    (target : Bool) :
    GenericSelect.superSlotCount a.bpCode target =
      GenericSelect.superSlotCount b.bpCode target := by
  unfold GenericSelect.superSlotCount
  rw [occurrenceCount_congr h target, CartesianShape.bpCode_length,
    CartesianShape.bpCode_length, h]

#print axioms occurrenceCount_bpCode_true
#print axioms occurrenceCount_bpCode_false
#print axioms occurrenceCount_congr
#print axioms superSlotCount_congr

end QZPop

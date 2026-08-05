import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCrossing

/-!
# Allocated space over the payload the accepted semantics consumes

`FG-06-ALLOCATED-SPACE` at the new target: allocated cells times width, header and
final padding included, inside `2 * n + rho n` with `rho` little-o linear.

The row insists the bound be stated on **allocated cells times width**, not on the
serialized length, so that padding is charged rather than dropped.
`packedReviewerMemory_length_mul_width_le` is stated in exactly that form, on the
memory object itself.

`packedReviewerRho` has two components: the consumed payload's own advertised
overhead, and two cell widths -- the header cell plus the ceiling remainder of the
final cell, each counted at full width. The second is logarithmic in the input
size, so it is `o(n)`, but it is counted rather than dropped.

## What the decoded-count dependence costs here

`packedReviewerAllocatedBits` takes `longCount` and `sparseCount`, so the
arithmetic core carries the hypothesis that their exact payload length is within
the advertised bound. At an actual shape that hypothesis is discharged
unconditionally by `packedReviewerPayloadLength_le_bound`. The resulting residual
is still a function of `n` alone.

## Layer boundary

This module proves only the allocation bound.  The controller-to-allocation
connection is supplied separately by `ReviewerControllerProof`, so the space
proof itself remains independent of query execution.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-- The residual: the consumed payload's own overhead, plus two cell widths. -/
def packedReviewerRho (n : Nat) : Nat :=
  concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n +
    2 * packedReviewerCellWidth n

theorem packedReviewerAllocatedBits_le (n longCount sparseCount : Nat)
    (hlen :
      packedReviewerPayloadLength n longCount sparseCount <=
        2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n) :
    packedReviewerAllocatedBits n longCount sparseCount <=
      2 * n + packedReviewerRho n := by
  have hceil :
      GenericSelect.selectCeilDiv
            (packedReviewerPayloadLength n longCount sparseCount)
            (packedReviewerCellWidth n) *
          packedReviewerCellWidth n <=
        packedReviewerPayloadLength n longCount sparseCount +
          packedReviewerCellWidth n :=
    GenericSelect.selectCeilDiv_mul_le_add _ _
  unfold packedReviewerAllocatedBits packedReviewerCellCount packedReviewerRho
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- **`FG-06` at the consumed payload**: allocated cells times width. -/
theorem packedReviewerMemory_length_mul_width_le
    (shape : CartesianShape) :
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size := by
  rw [packedReviewerMemory_length]
  exact packedReviewerAllocatedBits_le shape.size (longCount shape)
    (packedReviewerSparseCount shape)
    (packedReviewerPayloadLength_le_bound shape)

/-! ### The residual is little-o linear -/

theorem packedReviewerCellBound_add_two_eventually_linear :
    exists bound : Nat, forall n : Nat, bound <= n ->
      packedReviewerCellBound n + 2 <= 3 * n + 2 := by
  obtain ⟨t, ht⟩ := packedReviewerOverhead_littleO 1 (by omega)
  refine ⟨Nat.max t 1, ?_⟩
  intro n hn
  have hnt : t <= n := Nat.le_trans (Nat.le_max_left t 1) hn
  have hover :
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n <= n := by
    have := ht n hnt
    omega
  unfold packedReviewerCellBound
  omega

theorem packedReviewerCellWidth_littleO :
    SuccinctSpace.LittleOLinear packedReviewerCellWidth :=
  littleOLinear_machineWordBits_comp
    (f := fun n => packedReviewerCellBound n + 2)
    (K := 3) (C := 2)
    packedReviewerCellBound_add_two_eventually_linear

theorem packedReviewerRho_littleO :
    SuccinctSpace.LittleOLinear packedReviewerRho :=
  packedReviewerOverhead_littleO.add
    (packedReviewerCellWidth_littleO.mul_left 2)

end PackedCellProbe
end SuccinctFinal
end RMQ

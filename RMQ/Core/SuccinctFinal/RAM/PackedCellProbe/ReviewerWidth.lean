import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLength

/-!
# The cell width for the payload the accepted semantics consumes

Step two of the `DD-20260804-038` re-target. `ReviewerLength.lean` showed that the
consumed payload has no input-size-only length, so the width cannot be derived
from its exact length. It is derived from the advertised size-only bound instead:

```
packedReviewerCellBound n = 2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n
packedReviewerCellWidth n = machineWordBits (packedReviewerCellBound n + 2)
```

This is what keeps cell zero readable. The width is a function of `n` alone, so a
controller can address the header before it knows `longCount`; only the cell
*count* needs the header, and that is what the header is for.
`packedReviewerPayloadLength_le_bound` is the clause that makes this legitimate:
the exact length never exceeds the bound the width is built from.

## Why every stride still fits

Each arm below is the corresponding arm of `packedSourceStride_le_cellWidth` with
the flat payload length replaced by this bound. Every arm but one passes a
quantity bounded by `2 * n`, and `2 * n <= packedReviewerCellBound n` holds by
construction.

The exception is `finalRankBlockFalse`, whose stride is `machineWordBits` of a
*square* rather than of something the payload obviously contains. It transfers
because `packedAccessOverhead` -- the budget dominating the rank directory -- is
literally the first summand of
`concreteBPNativeSuccinctRMQCanonicalReviewerOverhead`, so
`packedRankAux_le_reviewerBound` follows from the existing
`packedRankAuxLength_le_accessOverhead` with no new arithmetic.

## What this module does not establish

* No memory is re-pointed here. `packedMemory` still chunks the flat payload at
  `packedCellWidth`; this width is defined alongside it, not in place of it.
* Nothing here bounds an address. Address representability needs a cell count,
  and the count needs the header.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### `(a + 1)` squared, since the flat module's copy is private -/

private theorem packedReviewerSucc_sq (a : Nat) :
    (a + 1) * (a + 1) = a * a + (2 * a + 1) := by
  rw [Nat.add_mul, Nat.mul_add]
  omega

def packedReviewerCellBound (n : Nat) : Nat :=
  2 * n + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n

def packedReviewerCellWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedReviewerCellBound n + 2)

theorem packedReviewerCellWidth_pos (n : Nat) : 0 < packedReviewerCellWidth n :=
  SuccinctRank.machineWordBits_pos _

theorem packedReviewerMachineWordBits_le_cellWidth {n bound : Nat}
    (h : bound <= packedReviewerCellBound n + 2) :
    SuccinctRank.machineWordBits bound <= packedReviewerCellWidth n := by
  unfold packedReviewerCellWidth
  exact SuccinctRank.machineWordBits_mono_le h

theorem packedTwoMul_le_reviewerBound (n : Nat) :
    2 * n <= packedReviewerCellBound n := by
  unfold packedReviewerCellBound
  omega

theorem packedReviewerCellBound_lt_two_pow_width (n : Nat) :
    packedReviewerCellBound n + 2 < 2 ^ packedReviewerCellWidth n :=
  SuccinctRank.self_lt_two_pow_machineWordBits _

theorem packedRankAux_le_reviewerBound (n : Nat) :
    2 * n + packedRankAuxLength n <= packedReviewerCellBound n := by
  have h := packedRankAuxLength_le_accessOverhead n
  unfold packedReviewerCellBound packedAccessOverhead
    concreteBPNativeSuccinctRMQCanonicalReviewerOverhead at *
  omega

theorem packedRankBlockWidth_le_reviewerCellWidth (n : Nat) :
    packedRankBlockWidth n <= packedReviewerCellWidth n := by
  have hw : packedRankWordSize n = Nat.log2 (2 * n) + 1 := rfl
  have haux := packedRankAux_le_reviewerBound n
  have hlow := packedRankWordSize_two_le_aux n
  have hsq :
      packedRankWordSize n * packedRankWordSize n <=
        packedReviewerCellBound n + 2 := by
    by_cases hn : n = 0
    · subst hn
      have hzero : packedRankWordSize 0 = 1 := by
        unfold packedRankWordSize SuccinctRank.machineWordBits
        simp
      rw [hzero]
      omega
    · have hne : 2 * n ≠ 0 := by omega
      have hpow : 2 ^ Nat.log2 (2 * n) <= 2 * n := Nat.log2_self_le hne
      have hk := packedSq_le_two_pow_add_three (Nat.log2 (2 * n))
      have hexp :
          packedRankWordSize n * packedRankWordSize n =
            Nat.log2 (2 * n) * Nat.log2 (2 * n) +
              (2 * Nat.log2 (2 * n) + 1) := by
        rw [hw]
        exact packedReviewerSucc_sq _
      have hlin : 2 * Nat.log2 (2 * n) + 1 <= 2 * packedRankWordSize n := by
        rw [hw]
        omega
      omega
  unfold packedRankBlockWidth
  exact packedReviewerMachineWordBits_le_cellWidth hsq

theorem packedLocalWidth_le_reviewerCellWidth (n : Nat) :
    packedLocalWidth n <= packedReviewerCellWidth n := by
  have hpay := packedTwoMul_le_reviewerBound n
  have hmin :
      Nat.min (2 * n) (GenericSelect.superLongSpan (2 * n)) <= 2 * n :=
    Nat.min_le_left _ _
  unfold packedLocalWidth
  exact packedReviewerMachineWordBits_le_cellWidth (by omega)

theorem packedSourceStride_le_reviewerCellWidth (n : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hcounted : PackedSourceCounted n source) :
    packedSourceStride n source <= packedReviewerCellWidth n := by
  have hpay := packedTwoMul_le_reviewerBound n
  have htwo :
      SuccinctRank.machineWordBits (2 * n) <= packedReviewerCellWidth n :=
    packedReviewerMachineWordBits_le_cellWidth (by omega)
  cases source with
  | bpCode => exact htwo
  | selectSuperBaseOccurrence => exact htwo
  | selectSuperBaseWordIndex => exact htwo
  | selectSuperRankBefore => exact htwo
  | selectSuperFirstOffset => exact htwo
  | selectLocalBaseOccurrence => exact packedLocalWidth_le_reviewerCellWidth n
  | selectLocalBaseWordIndex => exact packedLocalWidth_le_reviewerCellWidth n
  | selectLocalRankBefore => exact packedLocalWidth_le_reviewerCellWidth n
  | selectLocalFirstOffset => exact packedLocalWidth_le_reviewerCellWidth n
  | selectLongFlagBits =>
      have := packedSuperSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectLongFlagRankSuperTrue =>
      have := packedSuperSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectLongFlagRankBlockTrue =>
      have := packedSuperSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectLongRelative => exact htwo
  | selectSparseFlagBits =>
      have := packedSparseSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectSparseRankSuperTrue =>
      have := packedSparseSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectSparseRankBlockTrue =>
      have := packedSparseSlots_le_input n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | selectSparseRelative => exact packedLocalWidth_le_reviewerCellWidth n
  | finalRankSuperFalse => exact htwo
  | finalRankBlockFalse => exact packedRankBlockWidth_le_reviewerCellWidth n
  | finalRankBPCodeAlias => exact htwo
  | closeSummaryBaseline => exact htwo
  | closeSummaryMinRel =>
      show packedSummaryRelativeWidth n <= packedReviewerCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeSummaryMaxRel =>
      show packedSummaryRelativeWidth n <= packedReviewerCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeSummaryArgOffset =>
      show packedSummaryRelativeWidth n <= packedReviewerCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeInteriorLocal =>
      have hready : PackedInteriorReady n := hcounted
      have := packedInteriorMacroSize_le_of_ready hready
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | closeInteriorGlobal =>
      have := packedSummaryBlockCount_le n
      exact packedReviewerMachineWordBits_le_cellWidth (by omega)
  | closeFiniteSmallInteriorMin => exact absurd hcounted (by simp [PackedSourceCounted])
  | closeFiniteSmallInteriorArg => exact absurd hcounted (by simp [PackedSourceCounted])
  | closeFiniteSmallSameBlock => exact absurd hcounted (by simp [PackedSourceCounted])

end PackedCellProbe
end SuccinctFinal
end RMQ

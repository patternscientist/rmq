import RMQ.Core.WordRAM.E1ReviewerWidth
import RMQ.Core.WordRAM.E1InteriorDispatchWidth

/-!
# The canonical interior's width side conditions (E1-LaneM)

`E1InteriorDispatchWidth.lean` certifies `interiorDispatchBlock` PARAMETRICALLY
in a layout, four geometries and seven numerals.  This module discharges the
part of that parameter list which belongs to the SUMMARY LAYOUT, at the
canonical instantiation and at the reviewer width, so that
`canonicalInteriorDispatchBlock` can eventually be certified rather than
assumed.

## The step that was missing, and why it was not an arithmetic problem

`LayoutFits` demands `L.deadAddress < 2 ^ w`.  The canonical layout's
`deadAddress` is DEFINITIONALLY the interior component store's word count
(`InteriorDirectory.lean:1646`), and the tree's only bound on it
(`canonicalRelativeRmmInteriorDeadAddress_fits_reviewerWordBits`,
`InteriorDirectory.lean:2771`) is stated against a capacity that CONTAINS that
same word count as a `Nat.max` argument.  That statement is therefore true of
any store whatsoever and carries no information about the pre-execution
envelope; chasing it is circular.

`canonicalRelativeRmmInteriorComponentStore_words_size_le_linear`
(`ReviewerPhysical.lean:2258`, DD-20260719-262) supplies the non-circular
bound, and `lt_capacity_of_le_mul` below is the capacity step that can consume
it: `lt_capacity_of_le_linear` (`E1ReviewerWidth.lean:135`) has slope `8`,
which `527 * (n + 1)` outruns from `n = 770` upward.

DD-20260719-263.
-/

namespace RMQ
namespace WordRAM
namespace E1CanonicalInteriorWidth

open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1ReviewerWidth
open E1InteriorSummaryGroup
open E1InteriorDispatchWidth

/-! ## Arithmetic: the fourth-power companion of `sq_le_two_pow` -/

theorem machineWordBits_le_self {L : Nat} (h : 0 < L) :
    SuccinctRank.machineWordBits L <= L := by
  unfold SuccinctRank.machineWordBits
  have hself := Nat.log2_self_le (by omega : L ≠ 0)
  have hlt : Nat.log2 L < 2 ^ Nat.log2 L := Nat.lt_two_pow_self
  omega

theorem pow4_le_two_pow : ∀ m : Nat, 17 <= m → m * m * m * m <= 2 ^ m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      rcases Nat.lt_or_ge k 17 with hk | hk
      · have hk16 : k = 16 := by omega
        subst hk16
        decide
      · have hkk := ih (by omega)
        have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
          rw [Nat.pow_succ]; omega
        have hexp : (k + 1) * (k + 1) * (k + 1) * (k + 1) =
            k * k * k * k + 4 * (k * k * k) + 6 * (k * k) + 4 * k + 1 := by
          simp [Nat.add_mul, Nat.mul_add]; omega
        have h3 : 17 * (k * k * k) <= k * (k * k * k) := Nat.mul_le_mul_right _ hk
        have h4 : k * (k * k * k) = k * k * k * k := by simp [Nat.mul_assoc]
        have h2 : 17 * (k * k) <= k * (k * k) := Nat.mul_le_mul_right _ hk
        have h2' : k * (k * k) = k * k * k := by simp [Nat.mul_assoc]
        have h1 : 17 * k <= k * k := Nat.mul_le_mul_right _ hk
        omega

/-! ## The canonical layout's own quantities -/

/-- The canonical base IS the modeled width of the size. -/
theorem base_eq (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape =
      SuccinctRank.machineWordBits shape.size := by
  unfold canonicalBPRelativeSummaryBase SuccinctRank.machineWordBits
  rfl

theorem base_pos (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBase shape := by
  unfold canonicalBPRelativeSummaryBase; omega

theorem base_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape <= 2 * shape.size + 1 := by
  rw [base_eq]; exact machineWordBits_le shape.size

/-- `2 ^ base <= 2 * size + 2`: the base's own power, linear in the size. -/
theorem two_pow_base_le (shape : Cartesian.CartesianShape) :
    2 ^ canonicalBPRelativeSummaryBase shape <= 2 * shape.size + 2 := by
  rw [base_eq]; exact two_pow_machineWordBits_le shape.size

/-- `base^2 <= 2 * size + 11`, the macro size's bound. -/
theorem base_sq_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape * canonicalBPRelativeSummaryBase shape
      <= 2 * shape.size + 11 := by
  rcases Nat.lt_or_ge (canonicalBPRelativeSummaryBase shape) 4 with hb | hb
  · have hb3 : canonicalBPRelativeSummaryBase shape <= 3 := by omega
    have := Nat.mul_le_mul hb3 hb3
    omega
  · have hsq := sq_le_two_pow (canonicalBPRelativeSummaryBase shape) hb
    have := two_pow_base_le shape
    omega

/-- `base^4 <= 2 * size + 65536`, the level slab's bound. -/
theorem base_pow4_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape * canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape
      <= 2 * shape.size + 65536 := by
  rcases Nat.lt_or_ge (canonicalBPRelativeSummaryBase shape) 17 with hb | hb
  · have h16 : canonicalBPRelativeSummaryBase shape <= 16 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h16 h16) h16) h16
    omega
  · have hp4 := pow4_le_two_pow (canonicalBPRelativeSummaryBase shape) hb
    have := two_pow_base_le shape
    omega

/-! ## The capacity step, the offsets, and the layout numerals -/

theorem lt_capacity_of_le_mul {n x c : Nat} (hc : c < 400000)
    (h : x <= c * (n + 1)) :
    x < concreteBPNativeSuccinctRMQReviewerCapacity n := by
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  have hpos : 0 < n + 1 := by omega
  have : c * (n + 1) < 400000 * (n + 1) := (Nat.mul_lt_mul_right hpos).2 hc
  omega

theorem deadAddress_le (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress
      <= 527 * (shape.size + 1) := by
  have h := canonicalRelativeRmmInteriorComponentStore_words_size_le_linear shape
  have heq : (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size := rfl
  omega

theorem deadAddress_lt (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress
      < 2 ^ shapeWidth shape :=
  lt_reviewerWordBits_of_lt_capacity
    (lt_capacity_of_le_mul (by omega) (deadAddress_le shape))

theorem offsets_le_deadAddress (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).baseline
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).minRel
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress := by
  have hsum := canonicalRelativeRmmInteriorComponentStore_words_size_eq shape
  have heq : (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size := rfl
  simp only [canonicalRelativeRmmInteriorComponentOffsets] at *
  omega

/-! ## The layout's own numerals -/

theorem blockCountRaw_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape <= shape.size := by
  unfold canonicalBPRelativeSummaryBlockCountRaw
  exact Nat.div_le_self _ _

theorem superCountRaw_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummarySuperCountRaw shape <= shape.size + 1 := by
  unfold canonicalBPRelativeSummarySuperCountRaw
  have h1 : canonicalBPRelativeSummaryBlockCountRaw shape /
      canonicalBPRelativeSummaryBlocksPerSuperRaw shape
      <= canonicalBPRelativeSummaryBlockCountRaw shape := Nat.div_le_self _ _
  have h2 := blockCountRaw_le shape
  omega

/-! ## `LayoutFits` at the canonical summary layout -/

theorem canonicalSummaryLayout_fits (shape : Cartesian.CartesianShape) :
    LayoutFits (shapeWidth shape) (canonicalSummaryLayout shape) := by
  obtain ⟨hb, hmin, hmax, harg⟩ := offsets_le_deadAddress shape
  have hdead := deadAddress_lt shape
  have hpowpos : 0 < 2 ^ SuccinctRank.machineWordBits shape.bpCode.length :=
    Nat.two_pow_pos _
  have hbasepos : 0 < canonicalBPRelativeSummaryBase shape := by
    unfold canonicalBPRelativeSummaryBase; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩⟩
  -- segment
  · exact lt_reviewerWordBits_of_lt_capacity
      (lt_capacity_of_le_linear (by simp [canonicalSummaryLayout,
        E1InteriorStoreConcrete.interiorSegment,
        concreteBPNativeInteriorTraceSegments]))
  -- deadAddress
  · simpa [canonicalSummaryLayout] using hdead
  -- wordScale positive
  · simpa [canonicalSummaryLayout] using hpowpos
  -- wordScale bound
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have h := two_pow_machineWordBits_le shape.bpCode.length
    have hL := bpCode_length_eq shape
    simp only [canonicalSummaryLayout]
    omega
  -- blocksPerSuper positive
  · simpa [canonicalSummaryLayout] using hbasepos
  -- blocksPerSuper bound
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := base_le shape
    simp only [canonicalSummaryLayout, RelativeRmm.canonicalLayout_blocksPerSuper,
      canonicalBPRelativeSummaryBlocksPerSuperRaw]
    omega
  -- baseline geom
  · simpa [canonicalSummaryLayout] using
      Nat.lt_of_le_of_lt hb hdead
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := superCountRaw_le shape
    simp only [canonicalSummaryLayout, bpSuperblockBaselineEntries_length,
      RelativeRmm.canonicalLayout_superSampleCount]
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := canonicalSummaryLayout_baseline_cap shape
    omega
  -- minRel geom
  · simpa [canonicalSummaryLayout] using Nat.lt_of_le_of_lt hmin hdead
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := blockCountRaw_le shape
    simp only [canonicalSummaryLayout, bpBlockRelativeMinExcessEntries_length,
      RelativeRmm.canonicalLayout_blockCount]
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := canonicalSummaryLayout_minRel_cap shape
    omega
  -- maxRel geom
  · simpa [canonicalSummaryLayout] using Nat.lt_of_le_of_lt hmax hdead
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := blockCountRaw_le shape
    simp only [canonicalSummaryLayout, bpBlockRelativeMaxExcessEntries_length,
      RelativeRmm.canonicalLayout_blockCount]
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := canonicalSummaryLayout_maxRel_cap shape
    omega
  -- argOffset geom
  · simpa [canonicalSummaryLayout] using Nat.lt_of_le_of_lt harg hdead
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := blockCountRaw_le shape
    simp only [canonicalSummaryLayout, bpBlockArgMinLocalOffsetEntries_length,
      RelativeRmm.canonicalLayout_blockCount]
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := canonicalSummaryLayout_argOffset_cap shape
    omega

end E1CanonicalInteriorWidth
end WordRAM
end RMQ

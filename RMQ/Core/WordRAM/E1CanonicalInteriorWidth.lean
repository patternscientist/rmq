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
(`ReviewerPhysical.lean:2280`, DD-20260719-262) supplies the non-circular
bound, and `lt_capacity_of_le_mul` below is the capacity step that can consume
it: `lt_capacity_of_le_linear` (`E1ReviewerWidth.lean:135`) has slope `8`,
which `527 * (n + 1)` outruns from `n = 770` upward.

DD-20260719-263.
-/

namespace RMQ
namespace WordRAM
namespace E1CanonicalInteriorWidth

open RMQ.SuccinctClose
open E1Machine
open RMQ.SuccinctFinal
open E1ReviewerWidth
open E1InteriorSummaryGroup
open E1InteriorSpanBlock
open E1InteriorTwoSpan
open E1InteriorDispatchWidth
open E1InteriorDispatchCompose

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

/-! ## The level quantities

E1-LaneM's residual list named `levelCount <= 2 * base` as the one missing
arithmetic fact behind the level slab and the two span products.  It is
NOT missing: `SuccinctRank.machineWordBits_mul_self_log_bound`
(`SuccinctRank.lean:1656`) already gives
`machineWordBits (m * m) <= 2 * machineWordBits m + 1`, and
`machineWordBits_le_self` above closes the gap to the base itself.  The
bound proved here is `2 * base + 1`, one more than predicted and equally
usable.  DD-20260719-300.

The reason these quantities close LINEARLY at all is that every one of them
is a product in which a DIVISION by the same base is never cancelled.
`prod_div_bound` is that step, named once: `macroSampleCount` carries
`blockCount / macroSize`, and multiplying it back by `macroSize` returns at
most `blockCount`, never the product of the two factors.  Cancelling the
division first would leave a genuinely superlinear quantity, and the
envelope is linear, so the order of these two steps is load-bearing. -/

theorem slab_bound {lc b : Nat} (hb : 0 < b) (hlc : lc <= 3 * b) :
    lc * (b * b) <= 3 * (b * b * b * b) := by
  have h1 : lc * (b * b) <= (3 * b) * (b * b) := Nat.mul_le_mul_right _ hlc
  have h2 : (3 * b) * (b * b) = 3 * (b * b * b) := by simp [Nat.mul_assoc]
  have h3 : b * b * b <= b * b * b * b := Nat.le_mul_of_pos_right _ hb
  have h4 : 3 * (b * b * b) <= 3 * (b * b * b * b) := Nat.mul_le_mul_left _ h3
  omega

/-- THE STEP THAT KEEPS THE SPAN PRODUCTS LINEAR: the division inside
`macroSampleCount` is absorbed, never cancelled. -/
theorem prod_div_bound (m a d : Nat) : m * (a / d * d) <= m * a :=
  Nat.mul_le_mul_left _ (Nat.div_mul_le_self a d)

/-- `machineWordBits n <= k` from `n < 2 ^ k`.  The `0 < n` hypothesis is
real: `machineWordBits 0 = 1`, so the statement is false at `n = k = 0`. -/
theorem machineWordBits_le_of_lt_pow {n k : Nat} (hn : 0 < n)
    (h : n < 2 ^ k) : SuccinctRank.machineWordBits n <= k := by
  unfold SuccinctRank.machineWordBits
  have hne : n ≠ 0 := by omega
  have := (Nat.log2_lt hne).2 h
  omega

/-- `size < 2 ^ base`: the base really is a logarithm of the size. -/
theorem size_lt_two_pow_base (shape : Cartesian.CartesianShape) :
    shape.size < 2 ^ canonicalBPRelativeSummaryBase shape := by
  unfold canonicalBPRelativeSummaryBase
  exact Nat.lt_log2_self

/-- **THE LEVEL COUNT IS LOGARITHMIC**, not linear: at most `2 * base + 1`. -/
theorem levelCount_le (shape : Cartesian.CartesianShape) :
    SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
      <= 2 * canonicalBPRelativeSummaryBase shape + 1 := by
  have h1 := SuccinctRank.machineWordBits_mul_self_log_bound
    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
  have h2 : SuccinctRank.machineWordBits
      (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
      <= canonicalBPRelativeSummaryBlocksPerSuperRaw shape := by
    refine machineWordBits_le_self ?_
    unfold canonicalBPRelativeSummaryBlocksPerSuperRaw
      canonicalBPRelativeSummaryBase
    omega
  have h3 : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  omega

/-- The GLOBAL level count is at most `2 * base + 2`.  Proved through
`size < 2 ^ base` rather than through `machineWordBits_le`, because the
latter is LINEAR in its argument and would leave the global span product
quadratic. -/
theorem globalLevelCount_le (shape : Cartesian.CartesianShape) :
    SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlockCountRaw shape /
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
            canonicalBPRelativeSummaryBlocksPerSuperRaw shape) + 1)
      <= 2 * canonicalBPRelativeSummaryBase shape + 2 := by
  refine machineWordBits_le_of_lt_pow (Nat.succ_pos _) ?_
  have hdiv : canonicalBPRelativeSummaryBlockCountRaw shape /
      (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
      <= canonicalBPRelativeSummaryBlockCountRaw shape := Nat.div_le_self _ _
  have hbc := blockCountRaw_le shape
  have hsz := size_lt_two_pow_base shape
  have hmono : (2 : Nat) ^ canonicalBPRelativeSummaryBase shape <
      2 ^ (2 * canonicalBPRelativeSummaryBase shape + 2) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- The macro sample count is at most the size plus one. -/
theorem macroSampleCount_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape /
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape) + 1
      <= shape.size + 1 := by
  have h1 : canonicalBPRelativeSummaryBlockCountRaw shape /
      (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
      <= canonicalBPRelativeSummaryBlockCountRaw shape := Nat.div_le_self _ _
  have h2 := blockCountRaw_le shape
  omega

/-- **THE LEVEL SLAB IS LINEAR IN THE SIZE.**  This is the quantity
`localArmSetup` carries, and the one E1-LaneM flagged as blocked. -/
theorem levelSlab_le (shape : Cartesian.CartesianShape) :
    SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape) *
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
      <= 6 * shape.size + 196608 := by
  have hb : 0 < canonicalBPRelativeSummaryBase shape := base_pos shape
  have hlc := levelCount_le shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  rw [hbps] at hlc ⊢
  have hs := slab_bound (b := canonicalBPRelativeSummaryBase shape) hb
    (lc := SuccinctRank.machineWordBits
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape)) (by omega)
  have hp4 := base_pow4_le shape
  omega

/-! ## The four geometry bases

The four span/level bases are four more PREFIX SUMS of the same eight stores
whose total is `deadAddress`, exactly as `offsets_le_deadAddress`'s four are.
The three `rfl` bridges are needed because the offsets name the later stores
through their own abbreviations (`canonicalRelativeRmmLocalMachineStore` and
friends, `InteriorDirectory.lean:1532`) while the sum names them through
`.table.machineStore`; the two are definitionally equal but not syntactically,
and `omega` is syntactic. -/

theorem span_offsets_le_deadAddress (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress ∧
      (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
        <= (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress := by
  have hsum := canonicalRelativeRmmInteriorComponentStore_words_size_eq shape
  have heq : (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words.size := rfl
  have hlocal : (canonicalRelativeRmmLocalMachineStore shape).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable shape).table.machineStore
        (SuccinctRank.machineWordBits_pos shape.bpCode.length)).store.words.size :=
    rfl
  have hglobal :
      (canonicalRelativeRmmGlobalMachineStore shape).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable shape).table.machineStore
        (SuccinctRank.machineWordBits_pos shape.bpCode.length)).store.words.size :=
    rfl
  have hlocalLevel :
      (canonicalRelativeRmmLocalLevelMachineStore shape).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.machineStore
        (SuccinctRank.machineWordBits_pos shape.bpCode.length)).store.words.size :=
    rfl
  simp only [canonicalRelativeRmmInteriorComponentOffsets] at *
  omega

/-! ## The four geometry entry lengths -/

theorem span_rearr (q lc M : Nat) : q * (lc * M) = lc * (q * M) := by
  simp [Nat.mul_left_comm]

theorem lc_div_bound {lc b sz : Nat} (hlc : lc <= 3 * b) :
    lc * (sz / b) <= 3 * sz := by
  have h1 : lc * (sz / b) <= (3 * b) * (sz / b) := Nat.mul_le_mul_right _ hlc
  have h2 : (3 * b) * (sz / b) = 3 * (b * (sz / b)) := Nat.mul_assoc 3 b (sz / b)
  have h2' : b * (sz / b) = sz / b * b := Nat.mul_comm b (sz / b)
  have h3 : sz / b * b <= sz := Nat.div_mul_le_self sz b
  omega

theorem g_div_bound {g M bc : Nat} (hg : g <= 4 * M) :
    g * (bc / M) <= 4 * bc := by
  have h1 : g * (bc / M) <= (4 * M) * (bc / M) := Nat.mul_le_mul_right _ hg
  have h2 : (4 * M) * (bc / M) = 4 * (M * (bc / M)) := Nat.mul_assoc 4 M (bc / M)
  have h2' : M * (bc / M) = bc / M * M := Nat.mul_comm M (bc / M)
  have h3 : bc / M * M <= bc := Nat.div_mul_le_self bc M
  omega

/-- LOCAL SPAN: `macroSampleCount * (levelCount * macroSize)`
(`LocalGlobalSparse.lean:838`), LINEAR in the size.  The division inside
`macroSampleCount` is absorbed by `prod_div_bound` and `blockCount`'s own
division by the base is absorbed by `lc_div_bound`; cancelling either would
leave the product superlinear against a linear envelope. -/
theorem localSpanGeom_entriesLen_le (shape : Cartesian.CartesianShape) :
    (localSpanGeom shape).entriesLen <= 9 * shape.size + 196608 := by
  simp only [localSpanGeom, bpLocalSparseOffsetEntries_length,
    RelativeRmm.canonicalLayout_blockSize, RelativeRmm.canonicalLayout_blockCount,
    RelativeRmm.canonicalLayout_macroSize,
    RelativeRmm.canonicalLayout_macroSampleCount,
    RelativeRmm.canonicalLayout_levelCount]
  rw [Nat.add_mul, Nat.one_mul,
    span_rearr
      (canonicalBPRelativeSummaryBlockCountRaw shape /
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape))
      (SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape))
      (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape)]
  have hb := base_pos shape
  have habs := prod_div_bound
    (SuccinctRank.machineWordBits
      (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape))
    (canonicalBPRelativeSummaryBlockCountRaw shape)
    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
      canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
  have hbc : canonicalBPRelativeSummaryBlockCountRaw shape =
      shape.size / canonicalBPRelativeSummaryBase shape := rfl
  have hlc := levelCount_le shape
  have hfinal : SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape) *
      canonicalBPRelativeSummaryBlockCountRaw shape <= 3 * shape.size := by
    rw [hbc]
    exact lc_div_bound (by omega)
  have hslab := levelSlab_le shape
  omega

/-- GLOBAL SPAN: `globalLevelCount * macroSampleCount`
(`LocalGlobalSparse.lean:866`), LINEAR in the size. -/
theorem globalSpanGeom_entriesLen_le (shape : Cartesian.CartesianShape) :
    (globalSpanGeom shape).entriesLen <= 8 * shape.size + 8 := by
  simp only [globalSpanGeom, bpGlobalSparseBlockEntries_length,
    RelativeRmm.canonicalLayout_blockSize, RelativeRmm.canonicalLayout_blockCount,
    RelativeRmm.canonicalLayout_macroSize,
    RelativeRmm.canonicalLayout_macroSampleCount,
    RelativeRmm.canonicalLayout_globalLevelCount]
  rw [Nat.mul_add, Nat.mul_one]
  have hglc := globalLevelCount_le shape
  have hb := base_pos shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  have hbpspos : 0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape := hb
  have hsq : canonicalBPRelativeSummaryBlocksPerSuperRaw shape <=
      canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape :=
    Nat.le_mul_of_pos_left _ hbpspos
  have hg4 : SuccinctRank.machineWordBits
        (canonicalBPRelativeSummaryBlockCountRaw shape /
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
            canonicalBPRelativeSummaryBlocksPerSuperRaw shape) + 1)
      <= 4 * (canonicalBPRelativeSummaryBlocksPerSuperRaw shape *
          canonicalBPRelativeSummaryBlocksPerSuperRaw shape) := by omega
  have hgd := g_div_bound (bc := canonicalBPRelativeSummaryBlockCountRaw shape) hg4
  have hbc := blockCountRaw_le shape
  have hbase := base_le shape
  omega

/-- LOCAL LEVEL: `bpSparseLevelDomain macroSize = macroSize + 2`. -/
theorem localLevelGeom_entriesLen_le (shape : Cartesian.CartesianShape) :
    (localLevelGeom shape).entriesLen <= 2 * shape.size + 13 := by
  simp only [localLevelGeom, bpSparseLevelEntries_length, bpSparseLevelDomain,
    RelativeRmm.canonicalLayout_macroSize]
  have hsq := base_sq_le shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  rw [hbps]
  omega

/-- GLOBAL LEVEL: `bpSparseLevelDomain macroSampleCount`. -/
theorem globalLevelGeom_entriesLen_le (shape : Cartesian.CartesianShape) :
    (globalLevelGeom shape).entriesLen <= shape.size + 3 := by
  simp only [globalLevelGeom, bpSparseLevelEntries_length, bpSparseLevelDomain,
    RelativeRmm.canonicalLayout_macroSampleCount]
  have h := macroSampleCount_le shape
  omega

/-! ## `GeomFits` at the four canonical geometries -/

theorem localSpanGeom_fits (shape : Cartesian.CartesianShape) :
    GeomFits (shapeWidth shape) (localSpanGeom shape) := by
  obtain ⟨hlo, _, _, _⟩ := span_offsets_le_deadAddress shape
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (by simpa [localSpanGeom] using hlo)
      (deadAddress_lt shape)
  · refine lt_reviewerWordBits_of_lt_capacity
      (lt_capacity_of_le_mul (c := 196608) (by omega) ?_)
    have := localSpanGeom_entriesLen_le shape
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := localSpanGeom_cap shape
    omega

theorem globalSpanGeom_fits (shape : Cartesian.CartesianShape) :
    GeomFits (shapeWidth shape) (globalSpanGeom shape) := by
  obtain ⟨_, hgb, _, _⟩ := span_offsets_le_deadAddress shape
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (by simpa [globalSpanGeom] using hgb)
      (deadAddress_lt shape)
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := globalSpanGeom_entriesLen_le shape
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := globalSpanGeom_cap shape
    omega

theorem localLevelGeom_fits (shape : Cartesian.CartesianShape) :
    GeomFits (shapeWidth shape) (localLevelGeom shape) := by
  obtain ⟨_, _, hll, _⟩ := span_offsets_le_deadAddress shape
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (by simpa [localLevelGeom] using hll)
      (deadAddress_lt shape)
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := localLevelGeom_entriesLen_le shape
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := localLevelGeom_cap shape
    omega

theorem globalLevelGeom_fits (shape : Cartesian.CartesianShape) :
    GeomFits (shapeWidth shape) (globalLevelGeom shape) := by
  obtain ⟨_, _, _, hgl⟩ := span_offsets_le_deadAddress shape
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (by simpa [globalLevelGeom] using hgl)
      (deadAddress_lt shape)
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := globalLevelGeom_entriesLen_le shape
    omega
  · refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
    have := globalLevelGeom_cap shape
    omega

/-! ## The seven numerals -/

theorem macroSize_pos (shape : Cartesian.CartesianShape) :
    0 < (RelativeRmm.canonicalLayout shape).macroSize := by
  simp only [RelativeRmm.canonicalLayout_macroSize]
  have hb := base_pos shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  rw [hbps]
  exact Nat.mul_pos hb hb

theorem macroSize_lt (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).macroSize < 2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [RelativeRmm.canonicalLayout_macroSize]
  have hsq := base_sq_le shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  rw [hbps]
  omega

theorem macroSampleCount_lt (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).macroSampleCount <
      2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [RelativeRmm.canonicalLayout_macroSampleCount]
  have h := macroSampleCount_le shape
  omega

theorem levelSlab_lt (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).levelCount *
        (RelativeRmm.canonicalLayout shape).macroSize <
      2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [RelativeRmm.canonicalLayout_levelCount,
    RelativeRmm.canonicalLayout_macroSize]
  have h := levelSlab_le shape
  omega

theorem Dl_pos (shape : Cartesian.CartesianShape) :
    0 < bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize := by
  unfold bpSparseLevelDomain; omega

theorem Dl_lt (shape : Cartesian.CartesianShape) :
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize <
      2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [bpSparseLevelDomain, RelativeRmm.canonicalLayout_macroSize]
  have hsq := base_sq_le shape
  have hbps : canonicalBPRelativeSummaryBlocksPerSuperRaw shape =
      canonicalBPRelativeSummaryBase shape := rfl
  rw [hbps]
  omega

theorem Dg_pos (shape : Cartesian.CartesianShape) :
    0 < bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount := by
  unfold bpSparseLevelDomain; omega

theorem Dg_lt (shape : Cartesian.CartesianShape) :
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount <
      2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [bpSparseLevelDomain, RelativeRmm.canonicalLayout_macroSampleCount]
  have h := macroSampleCount_le shape
  omega

theorem blockSize_pos (shape : Cartesian.CartesianShape) :
    0 < (RelativeRmm.canonicalLayout shape).blockSize := by
  simp only [RelativeRmm.canonicalLayout_blockSize,
    canonicalBPRelativeSummaryBlockSizeRaw]
  have := base_pos shape
  omega

theorem blockSize_lt (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).blockSize < 2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [RelativeRmm.canonicalLayout_blockSize]
  have := blockSizeRaw_le shape
  omega

/-- The span the dispatch preamble carries: `blocksPerSuper * blockSize + 2`,
which at canonical parameters is `2 * base ^ 2 + 2`. -/
theorem span_lt (shape : Cartesian.CartesianShape) :
    (RelativeRmm.canonicalLayout shape).blocksPerSuper *
        (RelativeRmm.canonicalLayout shape).blockSize + 2 <
      2 ^ shapeWidth shape := by
  refine lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_)
  simp only [RelativeRmm.canonicalLayout_blocksPerSuper,
    RelativeRmm.canonicalLayout_blockSize, canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw]
  have hsq := base_sq_le shape
  have hre : canonicalBPRelativeSummaryBase shape *
      (2 * canonicalBPRelativeSummaryBase shape) =
      2 * (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) := by
    simp [Nat.mul_left_comm]
  omega

/-- The register bound, `151` being `wLeft` (`E1InteriorDispatch.lean:117`). -/
theorem reg_lt (shape : Cartesian.CartesianShape) :
    151 < 2 ^ shapeWidth shape :=
  lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear (by omega))

/-! ## THE CANONICAL INTERIOR DISPATCH BLOCK FITS -/

/--
**ALL 4204 INSTRUCTIONS OF `canonicalInteriorDispatchBlock` FIT THE REVIEWER
WIDTH, AT EVERY SHAPE.**

This is E1-LaneM's residual 1, closed.  `interiorDispatchBlock_fits`
(`E1InteriorDispatchWidth.lean:386`) is parametric in a layout, four
geometries and seven numerals; every one of those parameters is discharged
here at the canonical instantiation, so the theorem carries no premise about
the interior beyond `hQ`, which is about the block's own host address and is
discharged by its caller.

`hQ` is the ONE remaining hypothesis and it is not an owed premise in the
sense rule 1 forbids: at the intended instantiation the block is hosted at
`Q = 1007` (`closeLcaCrossArm`'s `A + 4 + 176` with `A = 827`), where
`1007 + 4204 = 5211` is far below the envelope.
-/
theorem canonicalInteriorDispatchBlock_fits (shape : Cartesian.CartesianShape)
    {Q : Nat} (hQ : Q + 4204 < 2 ^ shapeWidth shape) :
    ∀ instr ∈ canonicalInteriorDispatchBlock shape Q,
      Instr.FieldsFit (shapeWidth shape) instr := by
  intro instr hmem
  rw [canonicalInteriorDispatchBlock] at hmem
  exact interiorDispatchBlock_fits (canonicalSummaryLayout_fits shape)
    (localLevelGeom_fits shape) (localSpanGeom_fits shape)
    (globalLevelGeom_fits shape) (globalSpanGeom_fits shape)
    (reg_lt shape) hQ (macroSize_pos shape) (macroSize_lt shape)
    (macroSampleCount_lt shape) (levelSlab_lt shape) (Dl_pos shape)
    (Dl_lt shape) (Dg_pos shape) (Dg_lt shape) (blockSize_pos shape)
    (blockSize_lt shape) (span_lt shape) instr hmem

end E1CanonicalInteriorWidth
end WordRAM
end RMQ

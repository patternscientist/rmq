import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
EG-CP-F01: THE HEADER ARITY DECISION, `K = 1` vs `K = 3`.

The question is whether the frozen header must carry, besides `n`, two extra
descriptor fields naming the bases of the two select regions whose lengths were
never proved size-only:

  * the long-super relative table  (`selLongRelative`)
  * the sparse-exception relative table (`selSparseRelative`)

`K = 1` is available only if each region is padded to an `n`-only budget.  This
file supplies the three things the decision requires:

  (1) the budget is a PROVED upper bound on the region's actual length, for all
      shapes and all sizes -- not merely a defined quantity;
  (2) the padded total still fits `2*n + rho n` with `rho` little-o linear, with
      `rho` computed explicitly WITH the padding included;
  (3) the padding is COUNTED: allocated = content + named padding.

and then the sharper fact that decides the "is this a real space overrun"
question: a refined, still-`n`-only budget makes the padding EXACTLY ZERO in a
closed `n`-decidable regime.
-/

namespace ZkdK

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

/-! ############################################################
    # 1. The `K = 1` header: one field, one cell
    ############################################################ -/

/-- The frozen word width, restated (`EG-CP-F01` width phase). -/
def frozenWordWidth (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)

/-- The proposed header arity. -/
def headerArity : Nat := 1

theorem frozenWordWidth_closed_form (n : Nat) :
    frozenWordWidth n = Nat.log2 (2 * n) + 1 := rfl

/-- The single header field `n` is representable in one frozen-width cell, at
every size including `0`. -/
theorem header_field_fits (n : Nat) : n < 2 ^ frozenWordWidth n := by
  have h : 2 * n < 2 ^ (Nat.log2 (2 * n) + 1) := Nat.lt_log2_self
  have : n <= 2 * n := by omega
  exact Nat.lt_of_le_of_lt this h

theorem header_field_succ_le (n : Nat) : n + 1 <= 2 ^ frozenWordWidth n :=
  header_field_fits n

/-! ############################################################
    # 2. Condition (1): the budgets are PROVED upper bounds
    ############################################################ -/

/-- Allocated bit length of the long-super relative region under padding. -/
def paddedLongBits (n : Nat) : Nat := compactLongSuperRelativeTableOverhead n

/-- Allocated bit length of the sparse-exception relative region under
padding. -/
def paddedSparseBits (n : Nat) : Nat := sparseExceptionRelativeTableOverhead n

theorem paddedLongBits_closed (n : Nat) :
    paddedLongBits n = 1 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 1 :=
  rfl

theorem paddedSparseBits_closed (n : Nat) :
    paddedSparseBits n =
      512 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 512 :=
  rfl

/-- CONDITION (1), long region: for EVERY shape, the actual serialized length is
at most the `n`-only budget.  In-tree, unconditional, no regime hypothesis. -/
theorem long_actual_le_padded (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      paddedLongBits shape.size :=
  compactLongSuperRelativeTable_payload_le_overhead shape

/-- CONDITION (1), sparse region: same, unconditional. -/
theorem sparse_actual_le_padded (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      paddedSparseBits shape.size :=
  builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
    shape

/-! ############################################################
    # 3. Condition (3): the padding is COUNTED
    ############################################################ -/

/-- The named padding of the long region: allocated minus content. -/
def longPadBits (shape : CartesianShape) : Nat :=
  paddedLongBits shape.size -
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length

def sparsePadBits (shape : CartesianShape) : Nat :=
  paddedSparseBits shape.size -
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length

/-- CONDITION (3), long region: the allocated region is exactly content plus
named padding.  Nothing is free. -/
theorem long_allocation_counted (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length +
        longPadBits shape = paddedLongBits shape.size := by
  have h := long_actual_le_padded shape
  unfold longPadBits
  omega

theorem sparse_allocation_counted (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
          shape).payload.length +
        sparsePadBits shape = paddedSparseBits shape.size := by
  have h := sparse_actual_le_padded shape
  unfold sparsePadBits
  omega

/-! ############################################################
    # 4. Condition (2): the explicit `rho` WITH padding, and its little-o
    ############################################################ -/

/-- The complete padded allocation of the two content-dependent select regions,
as an explicit closed function of `n`. -/
def selectPadRho (n : Nat) : Nat := paddedLongBits n + paddedSparseBits n

theorem selectPadRho_closed (n : Nat) :
    selectPadRho n =
      513 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 513 := by
  unfold selectPadRho paddedLongBits paddedSparseBits
    compactLongSuperRelativeTableOverhead sparseExceptionRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead
  omega

/-- CONDITION (2a): the padded allocation is little-o linear. -/
theorem selectPadRho_littleO : SuccinctSpace.LittleOLinear selectPadRho := by
  unfold selectPadRho paddedLongBits paddedSparseBits
  exact
    compactLongSuperRelativeTableOverhead_littleO.add
      sparseExceptionRelativeTableOverhead_littleO

/-- CONDITION (2b), the decisive fact: the padded allocation is ALREADY inside
the overhead function that the existing `2*n + rho n` theorem charges.  Padding
each region up to its budget therefore adds NOTHING to the frozen space
contract: `rho` is unchanged, not merely still little-o. -/
theorem selectPadRho_le_charged_overhead (n : Nat) :
    selectPadRho n <=
      SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n := by
  unfold selectPadRho paddedLongBits paddedSparseBits
    compactLongSuperRelativeTableOverhead
    sparseExceptionRelativeTableOverhead
    SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead
    SuccinctFinal.relativeSplitSparseExceptionBPCloseRankOverhead
    GenericSelect.canonicalSparseExceptionSelectOverhead
    GenericSelect.longSuperRelativeTableOverhead
    GenericSelect.canonicalSparseExceptionDirectoryOverhead
    GenericSelect.sparseExceptionRelativeTableOverhead
  omega

/-- Consequently the padded `rho` inherits the existing little-o proof. -/
theorem padded_rho_littleO :
    SuccinctSpace.LittleOLinear
      SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead :=
  SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead_littleO

/-! ############################################################
    # 5. The refined `n`-only budget: padding is EXACTLY ZERO in a closed
    #    `n`-decidable regime
    ############################################################ -/

/-- Nat-only mirror of the long-super span threshold. -/
def longSpanOfSize (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n) *
      SuccinctRank.machineWordBits (2 * n) *
      SuccinctRank.machineWordBits (2 * n) *
    (Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1)

/-- Nat-only mirror of the local stride. -/
def localStrideOfSize (n : Nat) : Nat :=
  max 1
    (SuccinctRank.machineWordBits (2 * n) /
      ((Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1) *
        (Nat.log2 (SuccinctRank.machineWordBits (2 * n)) + 1)))

theorem superLongSpan_closed (shape : CartesianShape) :
    sparseDenseFalseSelectSuperLongSpan shape = longSpanOfSize shape.size := by
  simp only [sparseDenseFalseSelectSuperLongSpan,
    sparseDenseFalseSelectSuperStride, sparseDenseFalseSelectEll,
    sparseDenseFalseSelectWordBits, longSpanOfSize,
    CartesianShape.bpCode_length]

theorem localStride_closed (shape : CartesianShape) :
    sparseDenseFalseSelectLocalStride shape = localStrideOfSize shape.size := by
  simp only [sparseDenseFalseSelectLocalStride, sparseDenseFalseSelectEll,
    sparseDenseFalseSelectWordBits, localStrideOfSize,
    CartesianShape.bpCode_length]

/-! ### 5a. Long region: empty below the long-span crossover -/

theorem long_count_zero_below_crossover (shape : CartesianShape)
    (hcross : 2 * shape.size < longSpanOfSize shape.size) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape) = 0 := by
  have hmul :=
    longSuperExceptionCount_mul_superLongSpan_le_spanSum shape
      (n := builtRectangularFalseSelectSuperSlotCount shape) (Nat.le_refl _)
  have hsum :=
    builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length shape
  have hbp : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  rw [superLongSpan_closed] at hmul
  cases Nat.eq_zero_or_pos
      (RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape)) with
  | inl hzero => exact hzero
  | inr hpos =>
      exfalso
      have hspan :
          longSpanOfSize shape.size <=
            RMQ.Succinct.rankPrefix true
                (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
                (builtRectangularFalseSelectSuperSlotCount shape) *
              longSpanOfSize shape.size :=
        Nat.le_mul_of_pos_left _ hpos
      omega

/-- Below the crossover the long-super relative region is EMPTY, for every
shape. -/
theorem long_actual_zero_below_crossover (shape : CartesianShape)
    (hcross : 2 * shape.size < longSpanOfSize shape.size) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).payload.length = 0 := by
  rw [compactLongSuperRelativeTable_payload_length,
    long_count_zero_below_crossover shape hcross]
  simp

/-! ### 5b. Sparse region: empty when the local stride is one -/

theorem shortSuperLocalSpan_le_one (shape : CartesianShape) (slot : Nat)
    (hstride : localStrideOfSize shape.size = 1) :
    builtRelativeSplitFalseSelectShortSuperLocalSpan shape slot <= 1 := by
  have hstride' : sparseDenseFalseSelectLocalStride shape = 1 := by
    rw [localStride_closed]; exact hstride
  have hend :
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence shape slot <=
        builtRectangularFalseSelectLocalBaseOccurrence shape slot + 1 := by
    unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    rw [hstride']
    exact Nat.min_le_left _ _
  have hmono :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
            shape slot - 1) <=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence shape slot) :=
    builtRelativeSplitFalseSelectPosition_mono shape (by omega)
  show
    builtRelativeSplitFalseSelectPosition shape
        (builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape slot - 1) + 1 -
      builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence shape slot) <= 1
  omega

theorem localIsSparseException_false_of_unit_stride
    (shape : CartesianShape) (slot : Nat)
    (hstride : localStrideOfSize shape.size = 1) :
    builtRelativeSplitFalseSelectLocalIsSparseException shape slot = false := by
  have hspan := shortSuperLocalSpan_le_one shape slot hstride
  have hword : 0 < sparseDenseFalseSelectWordBits shape := by
    unfold sparseDenseFalseSelectWordBits
    exact SuccinctRank.machineWordBits_pos _
  unfold builtRelativeSplitFalseSelectLocalIsSparseException
  simp
  intro _
  omega

theorem sparseFlag_get? (shape : CartesianShape) {slot : Nat}
    (hslot : slot < builtRectangularFalseSelectLocalSlotCount shape) :
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)[slot]? =
      some (builtRelativeSplitFalseSelectLocalIsSparseException shape slot) := by
  unfold builtRelativeSplitFalseSelectSparseExceptionFlagBits
  rw [List.getElem?_map]
  rw [List.getElem?_range hslot]
  rfl

theorem sparse_count_zero_of_unit_stride (shape : CartesianShape)
    (hstride : localStrideOfSize shape.size = 1) :
    forall m, m <= builtRectangularFalseSelectLocalSlotCount shape ->
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape) m = 0 := by
  intro m
  induction m with
  | zero => intro _; simp [RMQ.Succinct.rankPrefix]
  | succ m ih =>
      intro hm
      have hslot : m < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hget := sparseFlag_get? shape hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          (n := m) hget
      rw [hrank, ih (by omega),
        localIsSparseException_false_of_unit_stride shape m hstride]
      simp

/-- With unit local stride the sparse-exception relative region is EMPTY, for
every shape. -/
theorem sparse_actual_zero_of_unit_stride (shape : CartesianShape)
    (hstride : localStrideOfSize shape.size = 1) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length = 0 := by
  rw [builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_length,
    sparse_count_zero_of_unit_stride shape hstride
      (builtRectangularFalseSelectLocalSlotCount shape) (Nat.le_refl _)]
  simp

/-! ### 5c. The refined budgets -/

def refinedLongBudget (n : Nat) : Nat :=
  if 2 * n < longSpanOfSize n then 0 else paddedLongBits n

def refinedSparseBudget (n : Nat) : Nat :=
  if localStrideOfSize n = 1 then 0 else paddedSparseBits n

def refinedPadRho (n : Nat) : Nat := refinedLongBudget n + refinedSparseBudget n

/-- The refined long budget is still an unconditional upper bound, all shapes. -/
theorem long_actual_le_refined (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      refinedLongBudget shape.size := by
  unfold refinedLongBudget
  by_cases hc : 2 * shape.size < longSpanOfSize shape.size
  · rw [if_pos hc, long_actual_zero_below_crossover shape hc]
    exact Nat.le_refl 0
  · rw [if_neg hc]
    exact long_actual_le_padded shape

/-- The refined sparse budget is still an unconditional upper bound. -/
theorem sparse_actual_le_refined (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      refinedSparseBudget shape.size := by
  unfold refinedSparseBudget
  by_cases hc : localStrideOfSize shape.size = 1
  · rw [if_pos hc, sparse_actual_zero_of_unit_stride shape hc]
    exact Nat.le_refl 0
  · rw [if_neg hc]
    exact sparse_actual_le_padded shape

theorem refinedPadRho_le_selectPadRho (n : Nat) :
    refinedPadRho n <= selectPadRho n := by
  unfold refinedPadRho refinedLongBudget refinedSparseBudget selectPadRho
  by_cases h1 : 2 * n < longSpanOfSize n <;>
    by_cases h2 : localStrideOfSize n = 1 <;>
    simp [h1, h2]

theorem refinedPadRho_littleO : SuccinctSpace.LittleOLinear refinedPadRho :=
  SuccinctSpace.LittleOLinear.of_le selectPadRho_littleO
    refinedPadRho_le_selectPadRho

/-- IN THE REFINED REGIME THE PADDING IS EXACTLY ZERO: allocated equals content,
so there is no dead cell at all. -/
theorem no_padding_in_refined_regime (shape : CartesianShape)
    (hlong : 2 * shape.size < longSpanOfSize shape.size)
    (hsparse : localStrideOfSize shape.size = 1) :
    refinedLongBudget shape.size = 0 /\ refinedSparseBudget shape.size = 0 /\
      (builtRelativeSplitFalseSelectLongSuperRelativeTable
        shape).payload.length = 0 /\
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length = 0 := by
  refine ⟨?_, ?_, long_actual_zero_below_crossover shape hlong,
    sparse_actual_zero_of_unit_stride shape hsparse⟩
  · unfold refinedLongBudget; rw [if_pos hlong]
  · unfold refinedSparseBudget; rw [if_pos hsparse]

/-! ############################################################
    # 6. The `K = 3` counterfactual: what the two fields would cost
    ############################################################ -/

/-- If we decline to pad, each header field must name a value up to the region's
proved bound.  Both fit in `w(n) + 11` bits, for every shape. -/
theorem k3_long_field_width (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <
      2 ^ (frozenWordWidth shape.size + 11) := by
  have hb := long_actual_le_padded shape
  have hdiv :
      2 * shape.size / (Nat.log2 (Nat.log2 (2 * shape.size) + 1) + 1) <=
        2 * shape.size := Nat.div_le_self _ _
  have hcell := header_field_succ_le shape.size
  have h11 : (2 : Nat) ^ 11 = 2048 := by decide
  have hpow : 2 ^ (frozenWordWidth shape.size + 11) =
      2048 * 2 ^ frozenWordWidth shape.size := by
    rw [Nat.pow_add, h11, Nat.mul_comm]
  unfold paddedLongBits compactLongSuperRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead at hb
  omega

theorem k3_sparse_field_width (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <
      2 ^ (frozenWordWidth shape.size + 11) := by
  have hb := sparse_actual_le_padded shape
  have hdiv :
      2 * shape.size / (Nat.log2 (Nat.log2 (2 * shape.size) + 1) + 1) <=
        2 * shape.size := Nat.div_le_self _ _
  have hcell := header_field_succ_le shape.size
  have h11 : (2 : Nat) ^ 11 = 2048 := by decide
  have hpow : 2 ^ (frozenWordWidth shape.size + 11) =
      2048 * 2 ^ frozenWordWidth shape.size := by
    rw [Nat.pow_add, h11, Nat.mul_comm]
  unfold paddedSparseBits sparseExceptionRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead at hb
  omega

/-- Sharper: the long-region length field needs only `w(n) + 1` bits. -/
theorem k3_long_field_width_tight (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <
      2 ^ (frozenWordWidth shape.size + 1) := by
  have hb := long_actual_le_padded shape
  have hdiv :
      2 * shape.size / (Nat.log2 (Nat.log2 (2 * shape.size) + 1) + 1) <=
        2 * shape.size := Nat.div_le_self _ _
  have hcell := header_field_succ_le shape.size
  have hpow : 2 ^ (frozenWordWidth shape.size + 1) =
      2 * 2 ^ frozenWordWidth shape.size := by
    rw [Nat.pow_add, Nat.mul_comm]
  unfold paddedLongBits compactLongSuperRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead at hb
  omega

/-! ### Explicit magnitudes, so the space cost is not hidden behind `o(n)` -/

theorem paddedLongBits_le (n : Nat) : paddedLongBits n <= 2 * n + 1 := by
  have hdiv : 2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1) <= 2 * n :=
    Nat.div_le_self _ _
  unfold paddedLongBits compactLongSuperRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead
  omega

theorem paddedSparseBits_le (n : Nat) : paddedSparseBits n <= 1024 * n + 512 := by
  have hdiv : 2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1) <= 2 * n :=
    Nat.div_le_self _ _
  unfold paddedSparseBits sparseExceptionRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead
  omega

/-- The padded select allocation is at most `1026 * n + 513` at EVERY size.
This is the honest magnitude behind the little-o: the `o(n)` term dominates
`2 * n` at every size a reviewer will ever build.  It is inherited from the
existing budgets, not introduced by padding -- see
`selectPadRho_le_charged_overhead`. -/
theorem selectPadRho_le_linear (n : Nat) : selectPadRho n <= 1026 * n + 513 := by
  have h1 := paddedLongBits_le n
  have h2 := paddedSparseBits_le n
  unfold selectPadRho
  omega

/-! ############################################################
    # 7. Executed numbers
    ############################################################ -/

-- `(n, w n, refinedLong, refinedSparse, unrefinedLong, unrefinedSparse, 2n)`
-- at powers of two.
#eval (List.range 20).map (fun k =>
  let n := 2 ^ k
  (n, frozenWordWidth n, refinedLongBudget n, refinedSparseBudget n,
    paddedLongBits n, paddedSparseBits n, 2 * n))

-- The two crossovers, as a function of the element count `n`.
#eval (List.range 20).map (fun k =>
  let n := 2 ^ k
  (n, 2 * n, longSpanOfSize n, decide (2 * n < longSpanOfSize n),
    localStrideOfSize n))

-- The sparse crossover in terms of the word width `w`: unit stride holds while
-- `w < 2 * (log2 w + 1)^2`.
#eval [96, 97, 98, 99, 100, 128].map (fun w =>
  (w, max 1 (w / ((Nat.log2 w + 1) * (Nat.log2 w + 1)))))

#print axioms header_field_fits
#print axioms long_actual_le_padded
#print axioms sparse_actual_le_padded
#print axioms long_allocation_counted
#print axioms sparse_allocation_counted
#print axioms selectPadRho_closed
#print axioms selectPadRho_littleO
#print axioms selectPadRho_le_charged_overhead
#print axioms long_actual_zero_below_crossover
#print axioms sparse_actual_zero_of_unit_stride
#print axioms long_actual_le_refined
#print axioms sparse_actual_le_refined
#print axioms refinedPadRho_littleO
#print axioms no_padding_in_refined_regime
#print axioms k3_long_field_width
#print axioms k3_long_field_width_tight
#print axioms k3_sparse_field_width
#print axioms selectPadRho_le_linear

end ZkdK

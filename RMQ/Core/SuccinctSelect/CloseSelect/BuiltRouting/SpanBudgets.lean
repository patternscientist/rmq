import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.FlagRankTables

/-!
# Sparse/dense span and overhead budgets

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

theorem natList_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc]

def builtRelativeSplitFalseSelectShortSuperLocalSpanSum
    (shape : Cartesian.CartesianShape) (slotCount : Nat) : Nat :=
  (List.range slotCount).map
    (builtRelativeSplitFalseSelectShortSuperLocalSpan shape)
    |>.sum

theorem builtRelativeSplitFalseSelectShortSuperLocalSpanSum_prefix_le_position
    (shape : Cartesian.CartesianShape) {slotCount : Nat}
    (hslotCount :
      slotCount <= builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape slotCount <=
      builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape slotCount) := by
  induction slotCount with
  | zero =>
      simp [builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
  | succ slotCount ih =>
      have hprefix :
          slotCount <= builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hslot :
          slotCount < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have ih' := ih hprefix
      let prefixSum :=
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum
          shape slotCount
      let span :=
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape slotCount
      let basePos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape slotCount)
      let nextPos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        simpa [span, basePos, nextPos] using
          builtRelativeSplitFalseSelectShortSuperLocalSpan_le_next_gap
            shape hslot
      have hbaseNext :
          builtRectangularFalseSelectLocalBaseOccurrence
              shape slotCount <=
            builtRectangularFalseSelectLocalBaseOccurrence
              shape (slotCount + 1) :=
        builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
          shape slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using
          builtRelativeSplitFalseSelectPosition_mono shape hbaseNext
      unfold builtRelativeSplitFalseSelectShortSuperLocalSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem falseSelectCeilDiv_mul_ge_of_pos
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride := by
  unfold falseSelectCeilDiv
  cases n with
  | zero =>
      simp
  | succ n =>
      have hleStride : stride <= n + 1 + stride - 1 := by
        omega
      have hlt :
          n + 1 + stride - 1 - stride <
          (n + 1 + stride - 1) / stride * stride :=
        Nat.lt_div_mul_self hstride hleStride
      omega

theorem falseSelectCeilDiv_slot_mul_lt
    {n stride slot : Nat} (hstride : 0 < stride)
    (hslot : slot < falseSelectCeilDiv n stride) :
    slot * stride < n := by
  unfold falseSelectCeilDiv at hslot
  have hsucc :
      slot + 1 <= (n + stride - 1) / stride := by
    omega
  have hmul :
      (slot + 1) * stride <= n + stride - 1 := by
    exact (Nat.le_div_iff_mul_le hstride).mp hsucc
  cases n with
  | zero =>
      have hstrideLe :
          stride <= (slot + 1) * stride := by
        have hslot : 1 <= slot + 1 := by omega
        have hmulSlot := Nat.mul_le_mul_right stride hslot
        simpa [Nat.mul_comm] using hmulSlot
      omega
  | succ n =>
      have hleft :
          (slot + 1) * stride = slot * stride + stride := by
        simp [Nat.add_mul, Nat.one_mul]
      have hright :
          n + 1 + stride - 1 = n + stride := by
        omega
      rw [hleft, hright] at hmul
      omega

theorem builtRectangularFalseSelectFinalLocalBaseOccurrence
    (shape : Cartesian.CartesianShape) :
    builtRectangularFalseSelectLocalBaseOccurrence shape
        (builtRectangularFalseSelectLocalSlotCount shape) =
      builtRectangularFalseSelectSuperSlotCount shape *
        sparseDenseFalseSelectSuperStride shape := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hdiv :
      (builtRectangularFalseSelectLocalSlotCount shape) / slots =
        superCount := by
    simp [builtRectangularFalseSelectLocalSlotCount, superCount, slots,
      Nat.mul_div_left, hslots]
  have hmod :
      (builtRectangularFalseSelectLocalSlotCount shape) % slots = 0 := by
    simp [builtRectangularFalseSelectLocalSlotCount, slots,
      Nat.mul_mod_left]
  rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
  change
    ((builtRectangularFalseSelectLocalSlotCount shape) / slots) *
        sparseDenseFalseSelectSuperStride shape +
      ((builtRectangularFalseSelectLocalSlotCount shape) % slots) *
        sparseDenseFalseSelectLocalStride shape =
      superCount * sparseDenseFalseSelectSuperStride shape
  rw [hdiv, hmod]
  simp [superCount]

theorem builtRelativeSplitFalseSelectShortSuperLocalSpanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
        (builtRectangularFalseSelectLocalSlotCount shape) <=
      shape.bpCode.length := by
  have hprefix :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum_prefix_le_position
      shape (Nat.le_refl _)
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape)
  have hbase :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectLocalBaseOccurrence shape
          (builtRectangularFalseSelectLocalSlotCount shape) := by
    rw [builtRectangularFalseSelectFinalLocalBaseOccurrence]
    exact hocc
  have hpos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence shape
            (builtRectangularFalseSelectLocalSlotCount shape)) =
        shape.bpCode.length :=
    builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hbase
  rwa [hpos] at hprefix

theorem builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
      falseSelectOccurrenceCount shape := by
  simpa [builtRectangularFalseSelectSuperSlotCount,
    builtRelativeSplitFalseSelectSuperBaseOccurrence] using
    falseSelectCeilDiv_slot_mul_lt
      (n := falseSelectOccurrenceCount shape)
      (stride := sparseDenseFalseSelectSuperStride shape)
      (slot := superSlot)
      (sparseDenseFalseSelectSuperStride_pos shape) hslot

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_le_count
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.min_le_right _ _

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_pos
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    0 < builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
  have hbaseCount :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
      shape hslot
  have hstride := sparseDenseFalseSelectSuperStride_pos shape
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, by omega⟩

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot <=
      builtRelativeSplitFalseSelectSuperBaseOccurrence
        shape (superSlot + 1) := by
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    builtRelativeSplitFalseSelectSuperBaseOccurrence
  have hleft :
      Nat.min
          (superSlot * sparseDenseFalseSelectSuperStride shape +
            sparseDenseFalseSelectSuperStride shape)
          (falseSelectOccurrenceCount shape) <=
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape :=
    Nat.min_le_left _ _
  simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hleft

theorem builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
      builtRelativeSplitFalseSelectSuperBaseOccurrence
        shape (superSlot + 1) := by
  unfold builtRelativeSplitFalseSelectSuperBaseOccurrence
  exact
    Nat.mul_le_mul_right
      (sparseDenseFalseSelectSuperStride shape)
      (Nat.le_succ superSlot)

theorem builtRelativeSplitFalseSelectSuperBase_lt_end_of_base_lt_count
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    (hbaseCount :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
        falseSelectOccurrenceCount shape) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
      builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
  have hstride := sparseDenseFalseSelectSuperStride_pos shape
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hbaseCount⟩

theorem builtRelativeSplitFalseSelectSuperSpan_le_next_gap
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectSuperSpan shape superSlot <=
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape (superSlot + 1)) -
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) := by
  let base :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let endOcc :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  let next :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape (superSlot + 1)
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  let nextPos := builtRelativeSplitFalseSelectPosition shape next
  have hbaseCount : base < falseSelectOccurrenceCount shape := by
    simpa [base] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
        shape hslot
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_le_count
        shape superSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_pos
        shape hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_le_next_base
        shape superSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
        shape superSlot
  have hbaseEnd : base < endOcc := by
    simpa [base, endOcc] using
      builtRelativeSplitFalseSelectSuperBase_lt_end_of_base_lt_count
        shape superSlot hbaseCount
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hbaseEq : basePos = baseWitness := by
    simpa [basePos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hbaseLast :
      baseWitness <= lastWitness := by
    exact
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := base) (hi := endOcc - 1)
        (posLo := baseWitness) (posHi := lastWitness)
        (by omega) hbaseSelect hlastSelect
  have hlastNext : lastWitness + 1 <= nextPos := by
    by_cases hnextCount : next < falseSelectOccurrenceCount shape
    · rcases falseSelect_exists_of_lt_occurrence_count
        shape hnextCount with ⟨nextWitness, hnextSelect⟩
      have hstrict :
          lastWitness < nextWitness :=
        select_index_strict_mono (target := false)
          (bits := shape.bpCode)
          (lo := endOcc - 1) (hi := next)
          (posLo := lastWitness) (posHi := nextWitness)
          (by omega) hlastSelect hnextSelect
      have hnextEq : nextPos = nextWitness := by
        simpa [nextPos] using
          builtRelativeSplitFalseSelectPosition_eq_of_select
            shape hnextSelect
      rw [hnextEq]
      omega
    · have hnextCountLe :
          falseSelectOccurrenceCount shape <= next := by
        omega
      have hnextEq :
          nextPos = shape.bpCode.length := by
        simpa [nextPos] using
          builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
            shape hnextCountLe
      have hlastBounds : lastWitness < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hlastSelect
      rw [hnextEq]
      omega
  unfold builtRelativeSplitFalseSelectSuperSpan
  change lastPos + 1 - basePos <= nextPos - basePos
  rw [hlastEq, hbaseEq]
  omega

theorem builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectLocalSlotCount shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape) n *
        sparseDenseFalseSelectWordBits shape <=
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix,
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectSparseExceptionFlagBits_get?
          shape (globalLocalSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectSparseExceptionFlagBits
            shape)
          (n := n)
          hget
      have ih' := ih hn'
      rw [hrank]
      unfold builtRelativeSplitFalseSelectShortSuperLocalSpanSum
      rw [List.range_succ]
      rw [List.map_append, natList_sum_append]
      simp
      by_cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            true
      · have hspanLt :=
          (builtRelativeSplitFalseSelectLocalIsSparseException_true_short
            shape n hflag).2
        have hwordLe :
            sparseDenseFalseSelectWordBits shape <=
              builtRelativeSplitFalseSelectShortSuperLocalSpan
                shape n := by
          omega
        have hcalc :
            (RMQ.Succinct.rankPrefix true
                  (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                    shape) n +
                1) *
                sparseDenseFalseSelectWordBits shape <=
              builtRelativeSplitFalseSelectShortSuperLocalSpanSum
                  shape n +
                builtRelativeSplitFalseSelectShortSuperLocalSpan
                  shape n := by
          rw [Nat.add_mul]
          simp
          omega
        simpa [hflag, builtRelativeSplitFalseSelectShortSuperLocalSpanSum,
          Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using hcalc
      · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparseException shape n
          · rfl
          · contradiction
        simpa [hfalse, builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
          using
          Nat.le_trans ih'
            (Nat.le_add_right
              (builtRelativeSplitFalseSelectShortSuperLocalSpanSum
                shape n)
              (builtRelativeSplitFalseSelectShortSuperLocalSpan
                shape n))

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_of_span_product_bound
    (shape : Cartesian.CartesianShape) {budget : Nat}
    (hspanProduct :
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) *
          sparseDenseFalseSelectLocalStride shape *
          builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
        sparseDenseFalseSelectWordBits shape * budget) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length <= budget := by
  let count :=
    RMQ.Succinct.rankPrefix true
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRectangularFalseSelectLocalSlotCount shape)
  let spanSum :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
      (builtRectangularFalseSelectLocalSlotCount shape)
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  have hcountWord :
      count * wordBits <= spanSum := by
    simpa [count, spanSum, wordBits] using
      builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
        shape (Nat.le_refl _)
  have hscaled :
      (count * wordBits) * (localStride * relativeWidth) <=
        spanSum * (localStride * relativeWidth) :=
    Nat.mul_le_mul_right (localStride * relativeWidth) hcountWord
  have hspan' :
      spanSum * (localStride * relativeWidth) <= budget * wordBits := by
    simpa [spanSum, localStride, relativeWidth, wordBits, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hspanProduct
  have hpayloadMul :
      (count * localStride * relativeWidth) * wordBits <=
        budget * wordBits := by
    have h := Nat.le_trans hscaled hspan'
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hpayloadMulLeft :
      wordBits * (count * localStride * relativeWidth) <=
        wordBits * budget := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul
  have hwordBits : 0 < wordBits := by
    simp [wordBits, sparseDenseFalseSelectWordBits,
      SuccinctRankProposal.machineWordBits_pos]
  apply
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_of_count_bound
      shape
  exact Nat.le_of_mul_le_mul_left hpayloadMulLeft hwordBits

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length *
        sparseDenseFalseSelectEll shape <=
      512 *
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) := by
  let count :=
    RMQ.Succinct.rankPrefix true
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRectangularFalseSelectLocalSlotCount shape)
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  let ell := sparseDenseFalseSelectEll shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let spanSum :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
      (builtRectangularFalseSelectLocalSlotCount shape)
  have hpayload :
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
          shape).payload.length =
        count * localStride * relativeWidth := by
    simpa [count, localStride, relativeWidth] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_length
        shape
  have hcodec :
      localStride * relativeWidth * ell <= 512 * wordBits := by
    simpa [localStride, relativeWidth, ell, wordBits] using
      builtRelativeSplitFalseSelectSparseException_localStride_mul_width_mul_ell_le_const_wordBits
        shape
  have hpayloadEll :
      count * localStride * relativeWidth * ell <=
        count * (512 * wordBits) := by
    have hmul := Nat.mul_le_mul_left count hcodec
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hcountWord :
      count * wordBits <= spanSum := by
    simpa [count, wordBits, spanSum] using
      builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
        shape (Nat.le_refl _)
  have hcountScaled :
      count * (512 * wordBits) <= 512 * spanSum := by
    have hmul := Nat.mul_le_mul_left 512 hcountWord
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  rw [hpayload]
  exact Nat.le_trans hpayloadEll hcountScaled

def sparseExceptionRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 512 (2 * n) + 512

theorem sparseExceptionRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead := by
  unfold sparseExceptionRelativeTableOverhead
  exact
    ((SuccinctSpace.idDivLogLogOverhead_littleO 512).comp_two_mul_arg).add_const
      512

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (hspan :
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) <=
        shape.bpCode.length) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      sparseExceptionRelativeTableOverhead shape.size := by
  let payload :=
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length
  let ell := sparseDenseFalseSelectEll shape
  let n := shape.bpCode.length
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hpayloadEll :
      payload * ell <= 512 * n := by
    have hscaled :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
        shape
    have hspanScaled :
        512 *
            builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
              (builtRectangularFalseSelectLocalSlotCount shape) <=
          512 * n := by
      exact Nat.mul_le_mul_left 512 (by simpa [n] using hspan)
    exact Nat.le_trans (by simpa [payload, ell] using hscaled) hspanScaled
  let overheadLen := 512 * (n / ell) + 512
  have hn_lt :
      n < n / ell * ell + ell :=
    Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict :
      512 * n < overheadLen * ell := by
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hn_lt (by decide : 0 < 512)
    simpa [overheadLen, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm, Nat.left_distrib, Nat.right_distrib] using hmul
  have hpayloadStrict :
      payload * ell < overheadLen * ell :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft :
      ell * payload < ell * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  have hbp : n = 2 * shape.size := by
    simpa [n] using Cartesian.CartesianShape.bpCode_length shape
  simpa [payload, overheadLen, sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ell, n, hbp,
    sparseDenseFalseSelectEll, sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      sparseExceptionRelativeTableOverhead shape.size := by
  exact
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
      shape
      (builtRelativeSplitFalseSelectShortSuperLocalSpanSum_le_bpCode_length
        shape)

def builtRelativeSplitFalseSelectLongSuperFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range (builtRectangularFalseSelectSuperSlotCount shape)).map
    (builtRelativeSplitFalseSelectSuperIsLong shape)

def builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    List Nat :=
  if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
    let baseOccurrence :=
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
      (sparseDenseFalseSelectSuperStride shape)
      (builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
      basePosition
  else
    []

def builtRelativeSplitFalseSelectLongSuperRelativeEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  (List.range (builtRectangularFalseSelectSuperSlotCount shape)).flatMap
    (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot shape)

def builtRelativeSplitFalseSelectLongSuperRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_get?
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape)[superSlot]? =
      some (builtRelativeSplitFalseSelectSuperIsLong shape superSlot) := by
  simp [builtRelativeSplitFalseSelectLongSuperFlagBits,
    List.getElem?_map, List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
      shape superSlot).length =
      if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
        sparseDenseFalseSelectSuperStride shape
      else
        0 := by
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hlong, falseSelectRelativeOffsetsOrZero_length]
  · have hfalse :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hfalse]

theorem compactLongSuperFlagRank_eq_segmentIndex
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectSuperSlotCount shape) :
    ((List.range n).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
          sparseDenseFalseSelectSuperStride shape := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectLongSuperFlagBits_get?
          shape (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          (n := n)
          hget
      have hprefix :
          (List.map
              (List.length ∘
                builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
                  shape)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
                sparseDenseFalseSelectSuperStride shape := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap,
        builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length,
        hrank]
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape n = true
      · rw [hprefix]
        simp [hlong, Nat.add_mul, Nat.add_comm]
      · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape n = false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem compactLongSuperRelativeEntries_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape) *
          sparseDenseFalseSelectSuperStride shape := by
  simpa [builtRelativeSplitFalseSelectLongSuperRelativeEntries] using
    compactLongSuperFlagRank_eq_segmentIndex shape (Nat.le_refl _)

def builtRelativeSplitFalseSelectLongSuperSpanSum
    (shape : Cartesian.CartesianShape) (slotCount : Nat) : Nat :=
  (List.range slotCount).map
    (fun superSlot =>
      if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
        builtRelativeSplitFalseSelectSuperSpan shape superSlot
      else
        0)
    |>.sum

theorem builtRelativeSplitFalseSelectLongSuperSpanSum_prefix_le_position
    (shape : Cartesian.CartesianShape) {slotCount : Nat}
    (hslotCount :
      slotCount <= builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectLongSuperSpanSum shape slotCount <=
      builtRelativeSplitFalseSelectPosition shape
        (builtRelativeSplitFalseSelectSuperBaseOccurrence shape slotCount) := by
  induction slotCount with
  | zero =>
      simp [builtRelativeSplitFalseSelectLongSuperSpanSum,
        builtRelativeSplitFalseSelectSuperBaseOccurrence,
        builtRelativeSplitFalseSelectPosition]
  | succ slotCount ih =>
      have hprefix :
          slotCount <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          slotCount < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have ih' := ih hprefix
      let prefixSum :=
        builtRelativeSplitFalseSelectLongSuperSpanSum shape slotCount
      let span :=
        if builtRelativeSplitFalseSelectSuperIsLong shape slotCount then
          builtRelativeSplitFalseSelectSuperSpan shape slotCount
        else
          0
      let basePos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape slotCount)
      let nextPos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        by_cases hlong :
            builtRelativeSplitFalseSelectSuperIsLong shape slotCount =
              true
        · have hspanGap :
              builtRelativeSplitFalseSelectSuperSpan shape slotCount <=
                nextPos - basePos := by
            simpa [basePos, nextPos] using
              builtRelativeSplitFalseSelectSuperSpan_le_next_gap
                shape hslot
          simpa [span, hlong] using hspanGap
        · have hfalse :
            builtRelativeSplitFalseSelectSuperIsLong shape slotCount =
              false := by
            cases h :
                builtRelativeSplitFalseSelectSuperIsLong shape slotCount
            · rfl
            · contradiction
          simp [span, hfalse]
      have hbaseNext :
          builtRelativeSplitFalseSelectSuperBaseOccurrence shape slotCount <=
            builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape (slotCount + 1) :=
        builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
          shape slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using
          builtRelativeSplitFalseSelectPosition_mono shape hbaseNext
      unfold builtRelativeSplitFalseSelectLongSuperSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongSuperSpanSum shape
        (builtRectangularFalseSelectSuperSlotCount shape) <=
      shape.bpCode.length := by
  have hprefix :=
    builtRelativeSplitFalseSelectLongSuperSpanSum_prefix_le_position
      shape (Nat.le_refl _)
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape)
  have hbase :
      falseSelectOccurrenceCount shape <=
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape
          (builtRectangularFalseSelectSuperSlotCount shape) := by
    simpa [builtRelativeSplitFalseSelectSuperBaseOccurrence] using hocc
  have hpos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
            (builtRectangularFalseSelectSuperSlotCount shape)) =
        shape.bpCode.length :=
    builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hbase
  rwa [hpos] at hprefix

theorem longSuperExceptionCount_mul_superLongSpan_le_spanSum
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectSuperSlotCount shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
        sparseDenseFalseSelectSuperLongSpan shape <=
      builtRelativeSplitFalseSelectLongSuperSpanSum shape n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix,
        builtRelativeSplitFalseSelectLongSuperSpanSum]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectLongSuperFlagBits_get?
          shape (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          (n := n)
          hget
      have ih' := ih hn'
      unfold builtRelativeSplitFalseSelectLongSuperSpanSum
      rw [List.range_succ]
      rw [List.map_append, natList_sum_append]
      simp [hrank]
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape n = true
      · have hspan :
            sparseDenseFalseSelectSuperLongSpan shape <=
              builtRelativeSplitFalseSelectSuperSpan shape n := by
          unfold builtRelativeSplitFalseSelectSuperIsLong at hlong
          by_cases hlt :
              sparseDenseFalseSelectSuperLongSpan shape <
                builtRelativeSplitFalseSelectSuperSpan shape n
          · omega
          · simp [hlt] at hlong
        simp [hlong]
        have hadd := Nat.add_le_add ih' hspan
        simpa [builtRelativeSplitFalseSelectLongSuperSpanSum,
          Nat.add_mul, Nat.one_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hadd
      · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape n = false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape n
          · rfl
          · contradiction
        simp [hfalse]
        exact ih'

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectLongSuperRelativeEntries shape =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape superSlot ++
      (((List.range
            (builtRectangularFalseSelectSuperSlotCount shape -
              superSlot - 1)).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectLongSuperRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectSuperSlotCount shape - superSlot - 1
  have hcount :
      builtRectangularFalseSelectSuperSlotCount shape =
        superSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectSuperSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) =
      (List.range (superSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) := by
        rw [hcount]
    _ =
      ((List.range superSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => superSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
        rw [List.range_add]
    _ =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => superSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape superSlot ++
      (((List.range tailCount).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntries_mem_lt_width
    {shape : Cartesian.CartesianShape} {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectLongSuperRelativeWidth shape := by
  unfold builtRelativeSplitFalseSelectLongSuperRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨superSlot, _hslotMem, hentryMem⟩
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · let baseOccurrence :=
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    have hmemOffsets :
        List.Mem entry
          (falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
            (sparseDenseFalseSelectSuperStride shape)
            (builtRelativeSplitFalseSelectSuperEndOccurrence
              shape superSlot)
            basePosition) := by
      simpa [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
        hlong, baseOccurrence, basePosition] using hentryMem
    rcases falseSelectRelativeOffsetsOrZero_mem_cases
        hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with
        ⟨offset, pos, _hoff, _hend, hselect, hentry⟩
      have hposLen : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < shape.bpCode.length := by
        rw [hentry]
        omega
      exact Nat.lt_trans hentryLen
        (by
          simpa [builtRelativeSplitFalseSelectLongSuperRelativeWidth,
            SuccinctRankProposal.machineWordBits] using
            (Nat.lt_log2_self (n := shape.bpCode.length)))
  · have hfalse :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hfalse] at hentryMem

def builtRelativeSplitFalseSelectLongSuperRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)
      (builtRelativeSplitFalseSelectLongSuperRelativeWidth shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)
    (builtRelativeSplitFalseSelectLongSuperRelativeWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectLongSuperRelativeEntries_mem_lt_width
          hmem)

theorem compactLongSuperRelativeTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).payload.length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape) *
          sparseDenseFalseSelectSuperStride shape *
          builtRelativeSplitFalseSelectLongSuperRelativeWidth shape := by
  rw [(builtRelativeSplitFalseSelectLongSuperRelativeTable
    shape).payload_length_eq]
  rw [compactLongSuperRelativeEntries_length]

theorem compactLongSuperRelativeTable_payload_mul_ell_le_spanSum
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length *
        sparseDenseFalseSelectEll shape <=
      builtRelativeSplitFalseSelectLongSuperSpanSum shape
        (builtRectangularFalseSelectSuperSlotCount shape) := by
  have hcount :=
    longSuperExceptionCount_mul_superLongSpan_le_spanSum
      shape (Nat.le_refl _)
  rw [compactLongSuperRelativeTable_payload_length]
  simpa [builtRelativeSplitFalseSelectLongSuperRelativeWidth,
    sparseDenseFalseSelectSuperLongSpan,
    sparseDenseFalseSelectWordBits,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcount

def compactLongSuperRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 1 (2 * n) + 1

theorem compactLongSuperRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear
      compactLongSuperRelativeTableOverhead := by
  unfold compactLongSuperRelativeTableOverhead
  exact
    ((SuccinctSpace.idDivLogLogOverhead_littleO 1).comp_two_mul_arg).add_const
      1

theorem compactLongSuperRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (hspan :
      builtRelativeSplitFalseSelectLongSuperSpanSum shape
          (builtRectangularFalseSelectSuperSlotCount shape) <=
        shape.bpCode.length) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      compactLongSuperRelativeTableOverhead shape.size := by
  let payload :=
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length
  let ell := sparseDenseFalseSelectEll shape
  let n := shape.bpCode.length
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hpayloadEll :
      payload * ell <= n := by
    have hscaled :=
      compactLongSuperRelativeTable_payload_mul_ell_le_spanSum shape
    exact Nat.le_trans (by simpa [payload, ell] using hscaled)
      (by simpa [n] using hspan)
  let overheadLen := n / ell + 1
  have hn_lt :
      n < n / ell * ell + ell :=
    Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict :
      n < overheadLen * ell := by
    simpa [overheadLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn_lt
  have hpayloadStrict :
      payload * ell < overheadLen * ell :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft :
      ell * payload < ell * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  have hbp : n = 2 * shape.size := by
    simpa [n] using Cartesian.CartesianShape.bpCode_length shape
  simpa [payload, overheadLen, compactLongSuperRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ell, n, hbp,
    sparseDenseFalseSelectEll, sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem compactLongSuperRelativeTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      compactLongSuperRelativeTableOverhead shape.size := by
  exact
    compactLongSuperRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
      shape
      (builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length
        shape)


end SuccinctSelectProposal
end RMQ

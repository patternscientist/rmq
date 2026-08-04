import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.SourceGeometry

/-!
# Every stored word fits one packed cell

`INV-WORD-WIDTH` asks that stored and returned words fit one declared modeled
machine word, and the probe plan of `Probe.lean` needs the same fact as a
hypothesis: `packedProbePlan_decode` is stated for reads of at most one cell,
because a wider read would need more than two cells and the plan issues at most
two.

Almost every source's stride is `machineWordBits` of something the payload already
contains, so the bound follows from monotonicity. Two are not:

* the final rank **block** sample width is `machineWordBits (w * w)` for
  `w = machineWordBits (2 * n)`, and `w * w` is not bounded by `2 * n` at small
  sizes -- at `n = 2` it is `9` against `4`. The rank directory the payload
  carries supplies the slack, and the residual is a pure arithmetic fact,
  `k * k <= 2 ^ k + 3`; and
* the close interior macro size is the summary base squared, which the
  **readiness guard** bounds -- `PackedInteriorReady` says exactly that the macro
  size is at most the block count. The guard `FG-07` requires the controller to
  consult is what makes this source's width admissible, not a separate estimate.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian
open SuccinctSpace

/-! ## The arithmetic residual -/

private theorem packedSucc_sq (a : Nat) :
    (a + 1) * (a + 1) = a * a + (2 * a + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

private theorem packedTwoMulAddOne_le_two_pow :
    forall j : Nat, 2 * (3 + j) + 1 <= 2 ^ (3 + j) := by
  intro j
  induction j with
  | zero => decide
  | succ i ih =>
      have hstep : (3 : Nat) + (i + 1) = (3 + i) + 1 := by omega
      have hpow : (2 : Nat) ^ ((3 + i) + 1) = 2 ^ (3 + i) * 2 := by
        rw [Nat.pow_succ]
      have hone : (1 : Nat) <= 2 ^ (3 + i) := Nat.one_le_two_pow
      rw [hstep, hpow]
      omega

private theorem packedSq_le_two_pow :
    forall j : Nat, (5 + j) * (5 + j) <= 2 ^ (5 + j) := by
  intro j
  induction j with
  | zero => decide
  | succ i ih =>
      have hstep : (5 : Nat) + (i + 1) = (5 + i) + 1 := by omega
      have hpow : (2 : Nat) ^ ((5 + i) + 1) = 2 ^ (5 + i) * 2 := by
        rw [Nat.pow_succ]
      have hlin : 2 * (5 + i) + 1 <= 2 ^ (5 + i) := by
        have := packedTwoMulAddOne_le_two_pow (i + 2)
        have h3 : (3 : Nat) + (i + 2) = 5 + i := by omega
        rw [h3] at this
        exact this
      have hexp := packedSucc_sq (5 + i)
      rw [hstep, hpow, hexp]
      omega

/-- The residual arithmetic fact behind the rank block sample width. -/
theorem packedSq_le_two_pow_add_three (k : Nat) : k * k <= 2 ^ k + 3 := by
  match k with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | (j + 5) =>
      have hcomm : j + 5 = 5 + j := by omega
      rw [hcomm]
      have := packedSq_le_two_pow j
      omega

/-! ## The payload is at least the code plus the rank directory -/

/-- A shape of every size, so that a size-only bound proved through a shape is
available at every `n`. -/
def packedSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (packedSpine k)

theorem packedSpine_size (k : Nat) : (packedSpine k).size = k := by
  induction k with
  | zero => rfl
  | succ i ih =>
      simp [packedSpine, CartesianShape.size, ih]
      omega

theorem packedRankAuxLength_le_accessOverhead (n : Nat) :
    packedRankAuxLength n <= packedAccessOverhead n := by
  have hsize := packedSpine_size n
  have hsum := accessComponents_add_padding (packedSpine n)
  have hrank := rankAuxPayload_length (packedSpine n)
  rw [hsize] at hsum hrank
  omega

theorem packedPayloadLength_eq_sum (n : Nat) :
    packedPayloadLength n =
      2 * n + packedAccessOverhead n + packedCloseOverhead n := by
  unfold packedPayloadLength packedAccessOverhead packedCloseOverhead
    concreteBPNativeSuccinctRMQOverhead
  omega

theorem packedRankAux_le_payload (n : Nat) :
    2 * n + packedRankAuxLength n <= packedPayloadLength n := by
  have h := packedRankAuxLength_le_accessOverhead n
  rw [packedPayloadLength_eq_sum n]
  omega

theorem packedRankWordSize_two_le_aux (n : Nat) :
    2 * packedRankWordSize n <= packedRankAuxLength n := by
  unfold packedRankAuxLength packedRankSuperOverhead
  have hone :
      packedRankWordSize n <=
        (2 * n / packedRankWordSize n / packedRankWordSize n + 1) *
          packedRankWordSize n :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

/-! ## The size-only width bound -/

theorem packedMachineWordBits_le_cellWidth {n bound : Nat}
    (h : bound <= packedPayloadLength n + 2) :
    SuccinctRank.machineWordBits bound <= packedCellWidth n := by
  unfold packedCellWidth
  exact SuccinctRank.machineWordBits_mono_le h

/--
**The rank block sample width fits a cell.** The only source whose stride is not
`machineWordBits` of something the payload obviously contains.
-/
theorem packedRankBlockWidth_le_cellWidth (n : Nat) :
    packedRankBlockWidth n <= packedCellWidth n := by
  have hw : packedRankWordSize n = Nat.log2 (2 * n) + 1 := rfl
  have haux := packedRankAux_le_payload n
  have hlow := packedRankWordSize_two_le_aux n
  have hsq :
      packedRankWordSize n * packedRankWordSize n <=
        packedPayloadLength n + 2 := by
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
        exact packedSucc_sq _
      have hlin : 2 * Nat.log2 (2 * n) + 1 <= 2 * packedRankWordSize n := by
        rw [hw]
        omega
      omega
  unfold packedRankBlockWidth
  exact packedMachineWordBits_le_cellWidth hsq

/-! ## The remaining strides -/

theorem packedTwoMul_le_payload (n : Nat) : 2 * n <= packedPayloadLength n := by
  unfold packedPayloadLength
  omega

theorem packedSuperSlots_le_input (n : Nat) : packedSuperSlots n <= n := by
  unfold packedSuperSlots
  by_cases hn : n = 0
  · subst hn
    have hs : 0 < GenericSelect.superStride (2 * 0) :=
      GenericSelect.superStride_pos _
    unfold GenericSelect.selectCeilDiv
    have hzero :
        (0 + GenericSelect.superStride (2 * 0) - 1) /
            GenericSelect.superStride (2 * 0) = 0 :=
      Nat.div_eq_of_lt (by omega)
    omega
  · exact
      GenericSelect.selectCeilDiv_le_self_of_pos (by omega)
        (GenericSelect.superStride_pos (2 * n))

theorem packedSparseSlots_le_input (n : Nat) : packedSparseSlots n <= n := by
  unfold packedSparseSlots
  exact Nat.min_le_right _ _

theorem packedLocalWidth_le_cellWidth (n : Nat) :
    packedLocalWidth n <= packedCellWidth n := by
  have hpay := packedTwoMul_le_payload n
  have hmin :
      Nat.min (2 * n) (GenericSelect.superLongSpan (2 * n)) <= 2 * n :=
    Nat.min_le_left _ _
  unfold packedLocalWidth
  exact packedMachineWordBits_le_cellWidth (by omega)

theorem packedSummaryBlockCount_le (n : Nat) : packedSummaryBlockCount n <= n := by
  unfold packedSummaryBlockCount packedSummaryBlockCountRaw
  by_cases hactive : PackedSummaryActive n
  · rw [if_pos hactive]
    exact Nat.div_le_self _ _
  · rw [if_neg hactive]
    omega

theorem packedInteriorMacroSize_le_of_ready {n : Nat}
    (hready : PackedInteriorReady n) : packedInteriorMacroSize n <= n := by
  have hle := packedSummaryBlockCount_le n
  have := hready.2
  omega

/--
**Every stored word fits one packed cell**, under exactly the guard the
controller is required to consult. `PackedSourceCounted` is the `n`-only
readiness predicate of `SourceFactorization`; for the two close interior sources
it is what bounds the macro size, and for every other source the bound holds
without it.
-/
theorem packedSourceStride_le_cellWidth (n : Nat)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hcounted : PackedSourceCounted n source) :
    packedSourceStride n source <= packedCellWidth n := by
  have hpay := packedTwoMul_le_payload n
  have htwo :
      SuccinctRank.machineWordBits (2 * n) <= packedCellWidth n :=
    packedMachineWordBits_le_cellWidth (by omega)
  cases source with
  | bpCode => exact packedBpCodeWordWidth_le_cellWidth n
  | selectSuperBaseOccurrence => exact htwo
  | selectSuperBaseWordIndex => exact htwo
  | selectSuperRankBefore => exact htwo
  | selectSuperFirstOffset => exact htwo
  | selectLocalBaseOccurrence => exact packedLocalWidth_le_cellWidth n
  | selectLocalBaseWordIndex => exact packedLocalWidth_le_cellWidth n
  | selectLocalRankBefore => exact packedLocalWidth_le_cellWidth n
  | selectLocalFirstOffset => exact packedLocalWidth_le_cellWidth n
  | selectLongFlagBits =>
      have := packedSuperSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectLongFlagRankSuperTrue =>
      have := packedSuperSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectLongFlagRankBlockTrue =>
      have := packedSuperSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectLongRelative => exact htwo
  | selectSparseFlagBits =>
      have := packedSparseSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectSparseRankSuperTrue =>
      have := packedSparseSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectSparseRankBlockTrue =>
      have := packedSparseSlots_le_input n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | selectSparseRelative => exact packedLocalWidth_le_cellWidth n
  | finalRankSuperFalse => exact htwo
  | finalRankBlockFalse => exact packedRankBlockWidth_le_cellWidth n
  | finalRankBPCodeAlias => exact htwo
  | closeSummaryBaseline => exact htwo
  | closeSummaryMinRel =>
      show packedSummaryRelativeWidth n <= packedCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeSummaryMaxRel =>
      show packedSummaryRelativeWidth n <= packedCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeSummaryArgOffset =>
      show packedSummaryRelativeWidth n <= packedCellWidth n
      unfold packedSummaryRelativeWidth
      by_cases hactive : PackedSummaryActive n
      · rw [if_pos hactive]
        exact Nat.le_trans hactive.2.2.2.2.2 htwo
      · rw [if_neg hactive]
        omega
  | closeInteriorLocal =>
      have hready : PackedInteriorReady n := hcounted
      have := packedInteriorMacroSize_le_of_ready hready
      exact packedMachineWordBits_le_cellWidth (by omega)
  | closeInteriorGlobal =>
      have := packedSummaryBlockCount_le n
      exact packedMachineWordBits_le_cellWidth (by omega)
  | closeFiniteSmallInteriorMin => exact absurd hcounted (by simp [PackedSourceCounted])
  | closeFiniteSmallInteriorArg => exact absurd hcounted (by simp [PackedSourceCounted])
  | closeFiniteSmallSameBlock => exact absurd hcounted (by simp [PackedSourceCounted])

/-! ## Addresses fit the modeled machine word

`INV-ADDRESS-WIDTH` rejects a host-array bound: `packedProbePlan_lt_cellCount`
bounds an issued address by `packedCellCount n`, which says the address indexes an
allocated cell, not that it is representable in one modeled word. The two are
related by the cell width's own definition -- it is `machineWordBits` of the
payload length plus two -- and the gap is one application of `Nat.log2_lt`.
-/

theorem packedCellCount_lt_two_pow_cellWidth (n : Nat) :
    packedCellCount n < 2 ^ packedCellWidth n := by
  have hw : 0 < packedCellWidth n := packedCellWidth_pos n
  have hceil :
      GenericSelect.selectCeilDiv (packedPayloadLength n)
          (packedCellWidth n) <= packedPayloadLength n := by
    by_cases hp : packedPayloadLength n = 0
    · rw [hp]
      unfold GenericSelect.selectCeilDiv
      have hzero :
          (0 + packedCellWidth n - 1) / packedCellWidth n = 0 :=
        Nat.div_eq_of_lt (by omega)
      omega
    · exact
        GenericSelect.selectCeilDiv_le_self_of_pos (by omega) hw
  have hlog : packedPayloadLength n + 2 < 2 ^ packedCellWidth n := by
    unfold packedCellWidth SuccinctRank.machineWordBits
    exact (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
  unfold packedCellCount
  omega

/--
**Every issued probe address is representable in one modeled machine word.**
Not merely below the host array's length.
-/
theorem packedProbeAddress_lt_two_pow_cellWidth
    {n bit width addr : Nat}
    (hfit : bit + width <= packedAllocatedBits n)
    (hmem : addr ∈ packedProbePlan n bit width) :
    addr < 2 ^ packedCellWidth n := by
  have hcell := packedProbePlan_lt_cellCount hfit hmem
  have hcount := packedCellCount_lt_two_pow_cellWidth n
  omega

/-! ## Stored and returned values, not just widths

`INV-WORD-WIDTH` is about *values*: every stored and returned word must fit one
declared modeled machine word. The stride bound above is what the probe plan
needs; this is what the row asks.
-/

/-- **Every stored cell's value fits one modeled word.** -/
theorem packedStoredCellValue_lt_two_pow
    (shape : CartesianShape) {cell : List Bool}
    (hmem : cell ∈ packedMemory shape) :
    SuccinctSpace.bitsToNatLE cell < 2 ^ packedCellWidth shape.size := by
  have hlen := packedMemory_cell_length shape hmem
  have hlt := GenericSelect.bitsToNatLE_lt_two_pow_length cell
  rw [hlen] at hlt
  exact hlt

/--
**Every returned word's value fits one modeled word.** A decoded span is a
`List.take` of the fetched cells, so it is never wider than the request, and the
request is never wider than a cell.
-/
theorem packedDecodedWordValue_lt_two_pow
    (n bit width : Nat) (cells : List (List Bool))
    (hwidth : width <= packedCellWidth n) :
    SuccinctSpace.bitsToNatLE (packedDecodeSpan n bit width cells) <
      2 ^ packedCellWidth n := by
  have hlen : (packedDecodeSpan n bit width cells).length <= width := by
    unfold packedDecodeSpan
    exact List.length_take_le _ _
  have hlt :=
    GenericSelect.bitsToNatLE_lt_two_pow_length (packedDecodeSpan n bit width cells)
  have hmono :
      (2 : Nat) ^ (packedDecodeSpan n bit width cells).length <=
        2 ^ packedCellWidth n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end PackedCellProbe

end SuccinctFinal

end RMQ

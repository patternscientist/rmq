import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Memory

/-!
# Allocated space for the packed representation

This module works towards `EG-CP` falsification row `FG-06-ALLOCATED-SPACE`.

The quantity bounded here is `packedAllocatedBits n = (packedMemory shape).length *
packedCellWidth n`: every allocated cell at full width, including the header cell
and the zero padding in the final cell. It is deliberately not the number of
meaningful bits, which is smaller whenever the padding is nonzero.

The residual `rho` therefore contains a logarithmic term, because the header cell
and the ceiling remainder are each one full cell wide. That term is genuinely
`o(n)` but it is genuinely present, so it is named rather than dropped.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ### A width composed with a linear argument is still little-o linear -/

/--
If `f` is eventually bounded by a linear function, then `machineWordBits ∘ f` is
little-o linear.

Needed because the packed cell width is `machineWordBits` of the payload length,
not of the input size, and the payload length is linear in the input size rather
than equal to it.
-/
theorem littleOLinear_machineWordBits_comp
    {f : Nat -> Nat} {K C : Nat}
    (hf : exists bound : Nat, forall n : Nat, bound <= n -> f n <= K * n + C) :
    SuccinctSpace.LittleOLinear fun n => SuccinctRank.machineWordBits (f n) := by
  obtain ⟨bound, hbound⟩ := hf
  intro scale _hscale
  obtain ⟨t0, ht0⟩ :=
    SuccinctSpace.eventually_scale_log2_succ_le_self (scale * (K + C + 1))
  refine ⟨Nat.max (Nat.max t0 bound) 1, ?_⟩
  intro n hn
  have hn1 : 1 <= n :=
    Nat.le_trans (Nat.le_max_right _ 1) hn
  have hnrest : Nat.max t0 bound <= n :=
    Nat.le_trans (Nat.le_max_left _ 1) hn
  have hnt0 : t0 <= n := Nat.le_trans (Nat.le_max_left t0 bound) hnrest
  have hnb : bound <= n := Nat.le_trans (Nat.le_max_right t0 bound) hnrest
  have hflin : f n <= K * n + C := hbound n hnb
  -- `log2 (f n) + 1 <= log2 n + (K + C + 1)`
  have hkey : Nat.log2 (f n) + 1 <= Nat.log2 n + (K + C + 1) := by
    by_cases hfz : f n = 0
    · rw [hfz, Nat.log2_zero]
      omega
    · -- `f n` is under `(K + C + 1) * n`, which is under `2 ^ (log2 n + K + C + 1)`
      have hlin : f n <= (K + C + 1) * n := by
        have hC : C <= C * n := Nat.le_mul_of_pos_right C hn1
        have hexp : (K + C + 1) * n = K * n + C * n + n := by
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
        omega
      have hnlt : n + 1 <= 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      have hpowKC : K + C + 1 <= 2 ^ (K + C) :=
        SuccinctSpace.nat_succ_le_two_pow (K + C)
      have hexp :
          2 ^ (Nat.log2 n + (K + C + 1)) =
            2 ^ (K + C) * 2 ^ (Nat.log2 n + 1) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hprod :
          (K + C + 1) * (n + 1) <= 2 ^ (K + C) * 2 ^ (Nat.log2 n + 1) :=
        Nat.mul_le_mul hpowKC hnlt
      have hgap : (K + C + 1) * n + 1 <= (K + C + 1) * (n + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hchain : f n < 2 ^ (Nat.log2 n + (K + C + 1)) := by
        rw [hexp]
        omega
      have := (Nat.log2_lt hfz).mpr hchain
      omega
  -- conclude
  have hstep :
      scale * SuccinctRank.machineWordBits (f n) <=
        (scale * (K + C + 1)) * (Nat.log2 n + 1) := by
    unfold SuccinctRank.machineWordBits
    have hexpand :
        Nat.log2 n + (K + C + 1) <= (K + C + 1) * (Nat.log2 n + 1) := by
      have : (K + C + 1) * (Nat.log2 n + 1) =
          (K + C + 1) * Nat.log2 n + (K + C + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      have hge : Nat.log2 n <= (K + C + 1) * Nat.log2 n :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    calc
      scale * (Nat.log2 (f n) + 1) <= scale * (Nat.log2 n + (K + C + 1)) :=
          Nat.mul_le_mul_left scale hkey
      _ <= scale * ((K + C + 1) * (Nat.log2 n + 1)) :=
          Nat.mul_le_mul_left scale hexpand
      _ = (scale * (K + C + 1)) * (Nat.log2 n + 1) := by
          rw [Nat.mul_assoc]
  exact Nat.le_trans hstep (ht0 n hnt0)

/-! ### The residual -/

/--
The packed representation's residual over `2 * n`.

Two components: the canonical payload's own overhead, and two cell widths. The
second is the header cell plus the ceiling remainder of the final cell, each one
full cell wide. It is logarithmic in the input size, so it is `o(n)`, but it is
counted rather than dropped.
-/
def packedRho (n : Nat) : Nat :=
  concreteBPNativeSuccinctRMQOverhead
      genericSparseExceptionBPCloseAccessOverhead n +
    2 * packedCellWidth n

/--
**Allocated space.** Every allocated cell, at full width, header and final padding
included, fits inside `2 * n + packedRho n`.
-/
theorem packedAllocatedBits_le (n : Nat) :
    packedAllocatedBits n <= 2 * n + packedRho n := by
  have hceil :
      GenericSelect.selectCeilDiv (packedPayloadLength n) (packedCellWidth n) *
          packedCellWidth n <=
        packedPayloadLength n + packedCellWidth n :=
    GenericSelect.selectCeilDiv_mul_le_add _ _
  unfold packedAllocatedBits packedCellCount packedRho packedPayloadLength
  rw [Nat.add_mul, Nat.one_mul]
  unfold packedPayloadLength at hceil
  omega

/-- The same bound stated on the memory itself, at the object the controller probes. -/
theorem packedMemory_length_mul_width_le (shape : CartesianShape) :
    (packedMemory shape).length * packedCellWidth shape.size <=
      2 * shape.size + packedRho shape.size := by
  rw [packedMemory_length]
  exact packedAllocatedBits_le shape.size

/-! ### The residual is little-o linear -/

/-- The payload length plus two is eventually linear in the input size. -/
theorem packedPayloadLength_add_two_eventually_linear :
    exists bound : Nat, forall n : Nat, bound <= n ->
      packedPayloadLength n + 2 <= 19909 * n + 563 := by
  obtain ⟨t, ht⟩ :=
    SuccinctClose.compactBPCloseOverhead_littleO 1 (by omega)
  refine ⟨Nat.max t 1, ?_⟩
  intro n hn
  have hnt : t <= n := Nat.le_trans (Nat.le_max_left t 1) hn
  have hn1 : 1 <= n := Nat.le_trans (Nat.le_max_right t 1) hn
  have hclose : SuccinctClose.compactBPCloseOverhead n <= n := by
    have := ht n hnt
    omega
  have haccess :
      genericSparseExceptionBPCloseAccessOverhead n <= 19906 * n + 561 :=
    genericSparseExceptionBPCloseAccessOverhead_le_linear n
  unfold packedPayloadLength concreteBPNativeSuccinctRMQOverhead
  omega

theorem packedCellWidth_littleO :
    SuccinctSpace.LittleOLinear packedCellWidth := by
  have h :=
    littleOLinear_machineWordBits_comp
      (f := fun n => packedPayloadLength n + 2)
      (K := 19909) (C := 563)
      packedPayloadLength_add_two_eventually_linear
  exact h

/-- **`rho` is `o(n)`.** -/
theorem packedRho_littleO : SuccinctSpace.LittleOLinear packedRho := by
  have hoverhead :
      SuccinctSpace.LittleOLinear fun n =>
        concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead n := by
    unfold concreteBPNativeSuccinctRMQOverhead
    exact genericSparseExceptionBPCloseAccessOverhead_littleO.add
      SuccinctClose.compactBPCloseOverhead_littleO
  exact hoverhead.add (packedCellWidth_littleO.mul_left 2)

end PackedCellProbe
end SuccinctFinal
end RMQ

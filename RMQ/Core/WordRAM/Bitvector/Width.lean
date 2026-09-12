import RMQ.Core.WordRAM.Bitvector.WordBounds

/-! # Query-independent logarithmic width and input encoding bounds -/

namespace RMQ.PackedBitvector

open SuccinctRank Experiment

theorem width_floor (n : Nat) : 32 ≤ width n := by unfold width; omega

theorem size_lt_capacity (n : Nat) : n < 2 ^ width n := by
  have hn : n < 2 ^ machineWordBits n := Nat.lt_log2_self
  exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide)
    (Nat.le_of_lt (machineWordBits_lt_width n)))

theorem valid_argument_fits (n argument : Nat) (ha : argument ≤ n) :
    argument < 2 ^ width n := Nat.lt_of_le_of_lt ha (size_lt_capacity n)

theorem fixed_floor_capacity (n value : Nat) (hv : value < 2 ^ 32) :
    value < 2 ^ width n :=
  Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (width_floor n))

theorem width_le_log (n : Nat) : width n ≤ 48 * (Nat.log2 (n + 2) + 1) := by
  have hm := machineWordBits_mono_le (show n ≤ n + 2 by omega)
  unfold width machineWordBits at *
  omega

theorem log_le_width (n : Nat) : Nat.log2 (n + 2) + 1 ≤ width n := by
  have hn : n < 2 ^ machineWordBits n := Nat.lt_log2_self
  have hp : 0 < 2 ^ machineWordBits n := Nat.two_pow_pos _
  have hsmall : n + 2 < 2 ^ (machineWordBits n + 2) := by
    simp only [Nat.pow_add, Nat.reducePow]
    omega
  have hl : Nat.log2 (n + 2) < machineWordBits n + 2 :=
    (Nat.log2_lt (by omega)).2 hsmall
  unfold width
  omega

theorem width_bounds (n : Nat) :
    Nat.log2 (n + 2) + 1 ≤ width n ∧ width n ≤ 48 * (Nat.log2 (n + 2) + 1) :=
  ⟨log_le_width n, width_le_log n⟩

end RMQ.PackedBitvector

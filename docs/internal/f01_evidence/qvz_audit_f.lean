import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL AUDIT part F.

The lane's decision argument (3) says K = 3's fields "do not provably fit one
`w(n)` cell (only `w(n)+1` and `w(n)+11` are proved)", concluding K = 3 could
cost up to 5 probes.  Test whether the LONG field in fact fits one cell, i.e.
whether `ZkdK.k3_long_field_width_tight` is merely a loose bound.
-/

namespace QvzF

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctSelect

def frozenWordWidth (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)

theorem width_ge (n : Nat) : 2 * n + 1 <= 2 ^ frozenWordWidth n :=
  Nat.lt_log2_self

theorem two_le_width_pow (n : Nat) : 2 <= 2 ^ frozenWordWidth n := by
  have h : 1 <= frozenWordWidth n := SuccinctRank.machineWordBits_pos _
  have h1 : (2 : Nat) ^ 1 <= 2 ^ frozenWordWidth n :=
    Nat.pow_le_pow_right (by omega) h
  simpa using h1

theorem one_le_log2 {m : Nat} (h : 2 <= m) : 1 <= Nat.log2 m :=
  (Nat.le_log2 (by omega)).2 (by simpa using h)

/-- The log-log denominator is at least 2 once `n >= 1`. -/
theorem denom_ge_two {n : Nat} (hn : 1 <= n) :
    2 <= Nat.log2 (Nat.log2 (2 * n) + 1) + 1 := by
  have hlog : 1 <= Nat.log2 (2 * n) := one_le_log2 (by omega)
  have := one_le_log2 (m := Nat.log2 (2 * n) + 1) (by omega)
  omega

theorem div_le_self_half (n : Nat) :
    2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1) <= n := by
  rcases Nat.eq_zero_or_pos n with hz | hpos
  · subst hz; simp
  · have hd := denom_ge_two hpos
    have hle : 2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1) <= 2 * n / 2 :=
      Nat.div_le_div_left hd (by omega)
    omega

/-- CHECKED: the long-region length field DOES fit exactly one `w(n)` cell, for
every shape and every size including 0 and 1. -/
theorem k3_long_field_fits_one_cell (shape : CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <
      2 ^ frozenWordWidth shape.size := by
  have hb := compactLongSuperRelativeTable_payload_le_overhead shape
  have hcell := width_ge shape.size
  have hpow2 := two_le_width_pow shape.size
  have hdiv := div_le_self_half shape.size
  unfold compactLongSuperRelativeTableOverhead
    SuccinctSpace.idDivLogLogOverhead at hb
  omega

#print axioms k3_long_field_fits_one_cell

end QvzF

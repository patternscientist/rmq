import RMQ.Core.GenericSelect.SelectFacts

/-!
# Generic select arithmetic

Shape-free arithmetic and overhead helpers shared by sparse/dense select.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRankProposal

theorem natList_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc]

theorem nat_div_succ_le_div_add_one
    (n w : Nat) (hw : 0 < w) :
    (n + 1) / w <= n / w + 1 := by
  apply Nat.div_le_of_le_mul
  have hlt : n < n / w * w + w :=
    Nat.lt_div_mul_add hw (a := n)
  calc
    n + 1 <= n / w * w + w := by omega
    _ = (n / w + 1) * w := by
      rw [Nat.add_mul]
      simp [Nat.mul_comm, Nat.add_comm]
    _ = w * (n / w + 1) := by
      rw [Nat.mul_comm]

theorem nat_div_add_sub_div_le_add
    (b d w : Nat) (hw : 0 < w) :
    (b + d) / w - b / w <= d := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hstep :
          (b + (d + 1)) / w <= (b + d) / w + 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          nat_div_succ_le_div_add_one (b + d) w hw
      have hmono :
          b / w <= (b + d) / w :=
        Nat.div_le_div_right (by omega)
      omega

theorem nat_div_sub_div_le_sub
    {a b w : Nat} (hw : 0 < w) (hb : b <= a) :
    a / w - b / w <= a - b := by
  have hsplit : a = b + (a - b) := by omega
  rw [hsplit]
  simpa using nat_div_add_sub_div_le_add b (a - b) w hw

theorem one_lt_two_pow_of_pos {k : Nat} (hk : 0 < k) :
    1 < 2 ^ k := by
  cases k with
  | zero =>
      omega
  | succ k =>
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega : 0 < 2)
      simp [Nat.pow_succ]
      omega

theorem machineWordBits_le_self_of_pos {n : Nat} (hn : 0 < n) :
    SuccinctRankProposal.machineWordBits n <= n := by
  unfold SuccinctRankProposal.machineWordBits
  by_cases hone : n = 1
  · subst n
    have hpow := Nat.log2_self_le (n := 1) (by omega : 1 ≠ 0)
    by_cases hlog : 0 < Nat.log2 1
    · have htwo : 2 <= 2 ^ Nat.log2 1 := by
        have honeLt := one_lt_two_pow_of_pos hlog
        omega
      omega
    · omega
  · have hn_ne : n ≠ 0 := by omega
    have hpow : n < 2 ^ n := by
      have hsucc := SuccinctSpace.nat_succ_le_two_pow n
      omega
    have hlog_lt : Nat.log2 n < n :=
      (Nat.log2_lt hn_ne).2 hpow
    omega

theorem lt_two_pow_machineWordBits_of_lt
    {x n : Nat} (hx : x < n) :
    x < 2 ^ SuccinctRankProposal.machineWordBits n := by
  exact Nat.lt_trans hx
    (by
      simpa [SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := n)))

theorem natLog2_succ_le_of_pos_lt_pow
    {n k : Nat} (hnpos : 0 < n) (hlt : n < 2 ^ k) :
    Nat.log2 n + 1 <= k := by
  by_cases hk : k <= Nat.log2 n
  · have hn : n ≠ 0 := by omega
    have hpow : 2 ^ k <= n := (Nat.le_log2 hn).1 hk
    omega
  · omega

theorem nat_succ_square_le_two_pow_of_six_le
    (q : Nat) :
    6 <= q -> (q + 1) * (q + 1) <= 2 ^ q := by
  exact Nat.strongRecOn q (fun q ih hq => by
    by_cases hq8 : 8 <= q
    · have hprev : 6 <= q - 2 := by omega
      have hprev_lt : q - 2 < q := by omega
      have ihprev := ih (q - 2) hprev_lt hprev
      have hlin : q + 1 <= 2 * ((q - 2) + 1) := by omega
      have hsq :
          (q + 1) * (q + 1) <=
            2 * (2 * (((q - 2) + 1) * ((q - 2) + 1))) := by
        have hmul := Nat.mul_le_mul hlin hlin
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hpowMul : 2 * (2 * 2 ^ (q - 2)) = 2 ^ q := by
        have hqeq : q = (q - 2) + 2 := by omega
        calc
          2 * (2 * 2 ^ (q - 2)) = 2 ^ ((q - 2) + 2) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by rw [<- hqeq]
      exact Nat.le_trans hsq
        (by
          have hmul := Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left 2 ihprev)
          simpa [hpowMul] using hmul)
    · have hqCases : q = 6 ∨ q = 7 := by omega
      rcases hqCases with hqeq | hqeq
      · subst q
        decide
      · subst q
        decide)

theorem nat_succ_square_le_four_mul_two_pow (q : Nat) :
    (q + 1) * (q + 1) <= 4 * 2 ^ q := by
  by_cases hlarge : 6 <= q
  · have hsq := nat_succ_square_le_two_pow_of_six_le q hlarge
    exact Nat.le_trans hsq (by
      have hpos : 0 < 2 ^ q := Nat.pow_pos (by omega : 0 < 2)
      omega)
  · have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      omega
    rcases hq with hq | hq | hq | hq | hq | hq
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide

theorem machineWordBits_sq_le_four_mul_self_of_pos
    {n : Nat} (hn : 0 < n) :
    SuccinctRankProposal.machineWordBits n *
        SuccinctRankProposal.machineWordBits n <=
      4 * n := by
  let q := Nat.log2 n
  have hn_ne : n ≠ 0 := by omega
  have hpow : 2 ^ q <= n := by
    simpa [q] using Nat.log2_self_le hn_ne
  have hsq :
      (q + 1) * (q + 1) <= 4 * 2 ^ q :=
    nat_succ_square_le_four_mul_two_pow q
  have hscale :
      4 * 2 ^ q <= 4 * n := Nat.mul_le_mul_left 4 hpow
  exact Nat.le_trans (by
    simpa [q, SuccinctRankProposal.machineWordBits] using hsq) hscale

/-- Fixed model cost for one sparse/dense select query. -/
def sparseDenseSelectQueryCost : Nat := 16

/-- Generic sparse/dense select overhead budget. -/
def sparseDenseSelectOverhead
    (superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots : Nat)
    (n : Nat) : Nat :=
  SuccinctSpace.sampledDirectoryOverhead superDirectorySlots n +
    SuccinctSpace.idDivLogLogOverhead longSuperExplicitSlots n +
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        localDirectorySlots n +
        SuccinctSpace.idDivLogLogOverhead sparseLocalExplicitSlots n

theorem sparseDenseSelectOverhead_littleO
    (superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (sparseDenseSelectOverhead
        superDirectorySlots longSuperExplicitSlots localDirectorySlots
        sparseLocalExplicitSlots) := by
  unfold sparseDenseSelectOverhead
  simpa [Nat.add_assoc] using
    (((SuccinctSpace.sampledDirectoryOverhead_littleO
        superDirectorySlots).add
      (SuccinctSpace.idDivLogLogOverhead_littleO
        longSuperExplicitSlots)).add
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO
        localDirectorySlots)).add
      (SuccinctSpace.idDivLogLogOverhead_littleO
        sparseLocalExplicitSlots)

def selectSuperSlot (q superStride : Nat) : Nat :=
  q / superStride

/-- Number of rectangular local slots reserved for each super interval. -/
def selectLocalSlotsPerSuper
    (superStride localStride : Nat) : Nat :=
  (superStride + localStride - 1) / localStride

def selectCeilDiv (n stride : Nat) : Nat :=
  (n + stride - 1) / stride

end RMQ.GenericSelect

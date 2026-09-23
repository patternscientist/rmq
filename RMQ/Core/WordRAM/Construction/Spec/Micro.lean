import RMQ.Core.WordRAM.Construction.Spec.Access

/-!
# PRE-1 S6: reference facts for the microtables

Machine-free specification layer (outside the builder firewall). A chunk
pattern `natToBitsLE c v` is read one bit per scan offset, `v / 2 ^ t % 2`;
the offset-encoded prefix excess moves by one per bit without underflow below
`c`; the leftmost-argmin scan grows by one keep-left comparison per offset; and
the select position of rank `k` is fixed at the unique close whose running
close count is `k`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.GenericSelect RMQ.SuccinctClose

theorem natToBitsLE_getElem? : ∀ (c v t : Nat), t < c →
    (SuccinctSpace.natToBitsLE c v)[t]? = some (decide (v / 2 ^ t % 2 = 1))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | c + 1, v, 0, _ => by simp [SuccinctSpace.natToBitsLE]
  | c + 1, v, t + 1, h => by
      simp only [SuccinctSpace.natToBitsLE, List.getElem?_cons_succ]
      rw [natToBitsLE_getElem? c (v / 2) t (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ,
        Nat.mul_comm (2 ^ t) 2]

/-- The pattern bit at offset `t`. -/
theorem pattern_getElem? {c t : Nat} (v : Nat) (ht : t < c) :
    (bpFringeChunkPattern c v)[t]? = some (decide (v / 2 ^ t % 2 = 1)) :=
  natToBitsLE_getElem? c v t ht

theorem pattern_rank_true_succ {c t : Nat} (v : Nat) (ht : t < c) :
    RMQ.Succinct.rankPrefix true (bpFringeChunkPattern c v) (t + 1) =
      RMQ.Succinct.rankPrefix true (bpFringeChunkPattern c v) t + v / 2 ^ t % 2 := by
  rw [rankPrefix_succ_eq_of_get? (target := true) (pattern_getElem? v ht)]
  have := Nat.mod_lt (v / 2 ^ t) (show 0 < 2 by decide)
  by_cases h : v / 2 ^ t % 2 = 1
  · simp [h]
  · have h0 : v / 2 ^ t % 2 = 0 := by omega
    simp [h0]

theorem pattern_rank_false_succ {c t : Nat} (v : Nat) (ht : t < c) :
    RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1) =
      RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t + (1 - v / 2 ^ t % 2) := by
  rw [rankPrefix_succ_eq_of_get? (target := false) (pattern_getElem? v ht)]
  have := Nat.mod_lt (v / 2 ^ t) (show 0 < 2 by decide)
  by_cases h : v / 2 ^ t % 2 = 1
  · simp [h]
  · have h0 : v / 2 ^ t % 2 = 0 := by omega
    simp [h0]

/-- One scan step of the offset-encoded excess below `c`. -/
theorem excessOffset_succ {c t : Nat} (v : Nat) (ht : t < c) :
    bpFringeChunkExcessOffsetAt c v (t + 1) + 1 =
      bpFringeChunkExcessOffsetAt c v t + 2 * (v / 2 ^ t % 2) ∧
      1 ≤ bpFringeChunkExcessOffsetAt c v t := by
  have hT := pattern_rank_true_succ (c := c) v ht
  have hF := pattern_rank_false_succ (c := c) v ht
  have hFle := RMQ.Succinct.rankPrefix_le_limit false (bpFringeChunkPattern c v) t
  have hb := Nat.mod_lt (v / 2 ^ t) (show 0 < 2 by decide)
  unfold bpFringeChunkExcessOffsetAt
  omega

/-- The leftmost-argmin scan over `[a, a + m + 1)` extends the scan over
`[a, a + m)` by one keep-left comparison (for `m ≥ 1`), and a scan of zero or one
offset is its start. -/
theorem scanArgMin_snoc (f : Nat → Nat) (a m : Nat) (hm : 1 ≤ m) :
    bpFringeScanArgMin f a (m + 1) = bpFringeScanBetter f (bpFringeScanArgMin f a m) (a + m) :=
  bpFringeScanArgMin_append f a m 1 hm (by decide)

theorem scanArgMin_zero (f : Nat → Nat) (a : Nat) : bpFringeScanArgMin f a 0 = a := rfl

theorem scanArgMin_one (f : Nat → Nat) (a : Nat) : bpFringeScanArgMin f a 1 = a := rfl

/-- The select position of rank `k` in a pattern prefix: the close of rank `k`
once `t` offsets have passed it, else `c`. -/
theorem selectPos_step {c t k : Nat} (v : Nat) (ht : t < c) (pos : Nat)
    (hpos : pos = if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t
      then bpChunkSelectPos c false v k else c) :
    (if RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = k then 1 else 0) *
        (1 - v / 2 ^ t % 2) * t +
      (1 - (if RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = k then 1 else 0) *
        (1 - v / 2 ^ t % 2)) * pos =
    if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1)
      then bpChunkSelectPos c false v k else c := by
  have hF := pattern_rank_false_succ (c := c) v ht
  have hb := Nat.mod_lt (v / 2 ^ t) (show 0 < 2 by decide)
  generalize hFt : RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = F at hF hpos
  rw [hF]
  by_cases hbit : v / 2 ^ t % 2 = 1
  · rw [hbit] at ⊢
    simp only [Nat.sub_self, Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.sub_zero, Nat.one_mul,
      Nat.add_zero]
    exact hpos
  · have h0 : v / 2 ^ t % 2 = 0 := by omega
    rw [h0]
    simp only [Nat.sub_zero]
    by_cases hk : F = k
    · -- the close at `t` has rank `k`
      have hget : (bpFringeChunkPattern c v)[t]? = some false := by
        rw [pattern_getElem? v ht]
        simp [h0]
      have hsel := select_at_close (bpFringeChunkPattern c v) hget
      rw [hFt, hk] at hsel
      have hposEq : bpChunkSelectPos c false v k = t := by
        unfold bpChunkSelectPos
        rw [hsel]
        rfl
      simp only [hk, if_true, Nat.one_mul, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
      rw [if_pos (by omega), hposEq]
    · simp only [hk, if_false]
      rw [hpos]
      by_cases hlt : k < F
      · rw [if_pos hlt, if_pos (by omega)]; simp
      · rw [if_neg hlt, if_neg (by omega)]; simp

/-- At the end of the pattern the running position is the reference entry. -/
theorem selectPos_final (c v k : Nat) :
    (if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) c
      then bpChunkSelectPos c false v k else c) = bpChunkSelectPos c false v k := by
  by_cases hk : k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) c
  · rw [if_pos hk]
  · rw [if_neg hk]
    have hlen : (bpFringeChunkPattern c v).length = c := bpFringeChunkPattern_length c v
    have hnone : RMQ.Succinct.select false (bpFringeChunkPattern c v) k = none :=
      select_none_of_rankPrefix_length_le (by rw [hlen]; omega)
    unfold bpChunkSelectPos
    rw [hnone]
    rfl

/-- One offset of the leftmost-argmin scan over `[a, b)` in the branch-free form
the builder computes, `take = [t = a] + [a < t] * [t < b] * [f t < bv]`. -/
theorem fringeBest_step (f : Nat → Nat) (a b t bp bv : Nat)
    (hinv : a < t → bp = bpFringeScanArgMin f a (min t b - a) ∧ bv = f bp) (hat : a ≤ t) :
    ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0)) * t +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0))) * bp =
        bpFringeScanArgMin f a (min (t + 1) b - a) ∧
    ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0)) * f t +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0))) * bv =
        f (bpFringeScanArgMin f a (min (t + 1) b - a)) := by
  by_cases hta : t = a
  · subst hta
    have hm : min (t + 1) b - t = 0 ∨ min (t + 1) b - t = 1 := by omega
    have hscan : bpFringeScanArgMin f t (min (t + 1) b - t) = t := by
      rcases hm with h | h <;> rw [h] <;> rfl
    rw [hscan]
    simp
  · have hlt : a < t := by omega
    obtain ⟨hbp, hbv⟩ := hinv hlt
    by_cases htb : t < b
    · have hmin1 : min (t + 1) b - a = (t - a) + 1 := by omega
      have hmin0 : min t b - a = t - a := by omega
      have hsnoc := scanArgMin_snoc f a (t - a) (by omega)
      rw [show a + (t - a) = t by omega] at hsnoc
      rw [hmin1, hsnoc, ← hmin0, ← hbp]
      unfold bpFringeScanBetter
      rw [hbv]
      by_cases hf : f t < f bp
      · simp [hta, hlt, htb, hf]
      · simp [hta, hlt, htb, hf]
    · have hmin : min (t + 1) b - a = min t b - a := by omega
      rw [hmin, ← hbp]
      simp [hta, htb, hbv]

end RMQ.SuccinctFinal.PackedConstruction.Spec

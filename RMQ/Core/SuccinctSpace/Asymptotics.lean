import RMQ.Core.Succinct

/-!
# Mathlib-free little-o arithmetic for succinct payload budgets

This module contains the natural-valued `LittleOLinear` predicate and the
sampled-directory overhead envelopes used by the succinct RMQ and rank/select
space profiles.
-/

namespace RMQ

namespace SuccinctSpace

/--
Mathlib-free `f = o(n)` predicate for natural-valued overhead functions.

For every positive scale factor, eventually `scale * f n <= n`.  This avoids
real-valued asymptotics while giving the exact arithmetic shape needed for a
`2*n + o(n)` payload theorem.
-/
def LittleOLinear (f : Nat -> Nat) : Prop :=
  forall scale : Nat, 0 < scale ->
    exists threshold : Nat,
      forall n : Nat, threshold <= n -> scale * f n <= n

theorem littleOLinear_zero : LittleOLinear (fun _ => 0) := by
  intro scale _hscale
  exact ⟨0, by intro n _hn; simp⟩

theorem littleOLinear_const (c : Nat) : LittleOLinear (fun _ => c) := by
  intro scale _hscale
  exact ⟨scale * c, by intro n hn; simpa using hn⟩

theorem LittleOLinear.of_le
    {f g : Nat -> Nat}
    (hg : LittleOLinear g)
    (hle : forall n, f n <= g n) :
    LittleOLinear f := by
  intro scale hscale
  rcases hg scale hscale with ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact Nat.le_trans
      (Nat.mul_le_mul_left scale (hle n))
      (hthreshold n hn)⟩

theorem LittleOLinear.of_eventually_le
    {f g : Nat -> Nat}
    (hg : LittleOLinear g)
    (hle : exists threshold : Nat,
      forall n : Nat, threshold <= n -> f n <= g n) :
    LittleOLinear f := by
  intro scale hscale
  rcases hg scale hscale with ⟨tg, hgEventually⟩
  rcases hle with ⟨tle, hleEventually⟩
  exact ⟨Nat.max tg tle, by
    intro n hn
    have hng : tg <= n := Nat.le_trans (Nat.le_max_left tg tle) hn
    have hnle : tle <= n := Nat.le_trans (Nat.le_max_right tg tle) hn
    exact Nat.le_trans
      (Nat.mul_le_mul_left scale (hleEventually n hnle))
      (hgEventually n hng)⟩

private theorem pow_two_pos (k : Nat) : 0 < 2 ^ k := by
  exact Nat.pow_pos (by omega)

private theorem log2_ge_of_pow_le
    {k n : Nat} (hpow : 2 ^ k <= n) :
    k <= Nat.log2 n := by
  have hn : n ≠ 0 := by
    intro hzero
    subst n
    have hpos := pow_two_pos k
    omega
  exact (Nat.le_log2 hn).2 hpow

theorem eventually_scale_le_log2_succ
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n -> scale <= Nat.log2 n + 1 := by
  exact ⟨2 ^ scale, by
    intro n hn
    have hlog : scale <= Nat.log2 n := log2_ge_of_pow_le hn
    omega⟩

theorem scale_mul_div_log2_succ_le_self
    {scale n : Nat}
    (hscale : scale <= Nat.log2 n + 1) :
    scale * (n / (Nat.log2 n + 1)) <= n := by
  have hden_pos : 0 < Nat.log2 n + 1 := by omega
  have hmul :
      scale * (n / (Nat.log2 n + 1)) <=
        (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) :=
    Nat.mul_le_mul_right (n / (Nat.log2 n + 1)) hscale
  have hdiv :
      (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) <= n := by
    simpa [Nat.mul_comm] using
      Nat.div_mul_le_self n (Nat.log2 n + 1)
  exact Nat.le_trans hmul hdiv

theorem littleOLinear_id_div_log2_succ :
    LittleOLinear (fun n => n / (Nat.log2 n + 1)) := by
  intro scale _hscale
  rcases eventually_scale_le_log2_succ scale with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact scale_mul_div_log2_succ_le_self (hthreshold n hn)⟩

theorem eventually_scale_le_logLog_succ
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale <= Nat.log2 (Nat.log2 n + 1) + 1 := by
  rcases eventually_scale_le_log2_succ scale with
    ⟨logThreshold, hlogThreshold⟩
  rcases eventually_scale_le_log2_succ logThreshold with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact hlogThreshold (Nat.log2 n + 1) (hthreshold n hn)⟩

theorem scale_mul_div_logLog_succ_le_self
    {scale n : Nat}
    (hscale : scale <= Nat.log2 (Nat.log2 n + 1) + 1) :
    scale * (n / (Nat.log2 (Nat.log2 n + 1) + 1)) <= n := by
  have hmul :
      scale * (n / (Nat.log2 (Nat.log2 n + 1) + 1)) <=
        (Nat.log2 (Nat.log2 n + 1) + 1) *
          (n / (Nat.log2 (Nat.log2 n + 1) + 1)) :=
    Nat.mul_le_mul_right (n / (Nat.log2 (Nat.log2 n + 1) + 1)) hscale
  have hdiv :
      (Nat.log2 (Nat.log2 n + 1) + 1) *
          (n / (Nat.log2 (Nat.log2 n + 1) + 1)) <= n := by
    simpa [Nat.mul_comm] using
      Nat.div_mul_le_self n (Nat.log2 (Nat.log2 n + 1) + 1)
  exact Nat.le_trans hmul hdiv

theorem littleOLinear_id_div_logLog_succ :
    LittleOLinear
      (fun n => n / (Nat.log2 (Nat.log2 n + 1) + 1)) := by
  intro scale _hscale
  rcases eventually_scale_le_logLog_succ scale with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact scale_mul_div_logLog_succ_le_self (hthreshold n hn)⟩

/-- Sampled explicit-exception budget with denominator `log log n`. -/
def idDivLogLogOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * (n / (Nat.log2 (Nat.log2 n + 1) + 1))

theorem nat_succ_le_two_pow (n : Nat) : n + 1 <= 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.pow_succ]
      have hpos : 1 <= 2 ^ n :=
        Nat.succ_le_of_lt (Nat.pow_pos (by omega : 0 < 2))
      omega

theorem nat_le_two_pow (n : Nat) : n <= 2 ^ n := by
  have h := nat_succ_le_two_pow n
  omega

theorem two_mul_le_two_pow (n : Nat) : 2 * n <= 2 ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      have h := Nat.mul_le_mul_left 2 (nat_succ_le_two_pow n)
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using h

private theorem scale_mul_log_arg_le_pow_of_large_log
    {scale q : Nat}
    (hlarge : 2 * scale + 1 <= q) :
    scale * (q + 1) <= 2 ^ q := by
  have hscale_le_q : scale <= q := by omega
  have hqplus :
      q + 1 <= 2 * (q - scale) := by
    omega
  have hqpow :
      q + 1 <= 2 ^ (q - scale) :=
    Nat.le_trans hqplus (two_mul_le_two_pow (q - scale))
  have hscale : scale <= 2 ^ scale := nat_le_two_pow scale
  have hmul := Nat.mul_le_mul hscale hqpow
  have hpows :
      2 ^ scale * 2 ^ (q - scale) = 2 ^ q := by
    rw [← Nat.pow_add]
    have hsum : scale + (q - scale) = q :=
      Nat.add_sub_of_le hscale_le_q
    rw [hsum]
  exact Nat.le_trans hmul (Nat.le_of_eq hpows)

theorem eventually_scale_log2_succ_le_self
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale * (Nat.log2 n + 1) <= n := by
  refine ⟨2 ^ (2 * scale + 1), ?_⟩
  intro n hn
  have hlog : 2 * scale + 1 <= Nat.log2 n :=
    log2_ge_of_pow_le hn
  have hpow :
      scale * (Nat.log2 n + 1) <= 2 ^ Nat.log2 n :=
    scale_mul_log_arg_le_pow_of_large_log hlog
  have hn_ne : n ≠ 0 := by
    intro hzero
    subst n
    have hpos : 0 < 2 ^ (2 * scale + 1) := pow_two_pos _
    omega
  exact Nat.le_trans hpow (Nat.log2_self_le hn_ne)

theorem eventually_scale_logLog_succ_le_log_succ
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale * (Nat.log2 (Nat.log2 n + 1) + 1) <=
          Nat.log2 n + 1 := by
  rcases eventually_scale_log2_succ_le_self scale with
    ⟨logThreshold, hlogThreshold⟩
  rcases eventually_scale_le_log2_succ logThreshold with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact hlogThreshold (Nat.log2 n + 1) (hthreshold n hn)⟩

/--
Canonical local-directory budget for one table with about `n / log n`
entries and `log log n`-bit fields.

This is the arithmetic envelope needed by two-level rank/select directories:
payload words stay machine-sized (`Theta(log n)`), while local deltas use only
`Theta(log log n)` bits per sampled machine word or occurrence bucket.
-/
def logLogSampledDirectoryOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * ((n / (Nat.log2 n + 1)) *
    (Nat.log2 (Nat.log2 n + 1) + 1))

theorem logLogSampledDirectoryOverhead_littleO (slots : Nat) :
    LittleOLinear (logLogSampledDirectoryOverhead slots) := by
  intro scale _hscale
  rcases eventually_scale_logLog_succ_le_log_succ (scale * slots) with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    have hlog :
        (scale * slots) *
            (Nat.log2 (Nat.log2 n + 1) + 1) <=
          Nat.log2 n + 1 :=
      hthreshold n hn
    have hmul :=
      Nat.mul_le_mul_right (n / (Nat.log2 n + 1)) hlog
    have hfirst :
        scale *
            (slots * ((n / (Nat.log2 n + 1)) *
              (Nat.log2 (Nat.log2 n + 1) + 1))) <=
          (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hdiv :
        (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) <= n := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self n (Nat.log2 n + 1)
    exact Nat.le_trans hfirst hdiv⟩

theorem four_mul_add_eighteen_le_two_pow_add_five
    (n : Nat) :
    4 * n + 18 <= 2 ^ (n + 5) := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have hlinear : 4 * (n + 1) + 18 <= 2 * (4 * n + 18) := by
        omega
      have hpow := Nat.mul_le_mul_left 2 ih
      have htwo :
          2 * 2 ^ (n + 5) = 2 ^ (n + 1 + 5) := by
        simp [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans hlinear (by simpa [htwo] using hpow)

theorem eight_mul_add_fifty_one_le_two_pow_add_seven
    (n : Nat) :
    8 * n + 51 <= 2 ^ (n + 7) := by
  induction n with
  | zero =>
      decide
  | succ n ih =>
      have hlinear : 8 * (n + 1) + 51 <= 2 * (8 * n + 51) := by
        omega
      have hpow := Nat.mul_le_mul_left 2 ih
      have htwo :
          2 * 2 ^ (n + 7) = 2 ^ (n + 1 + 7) := by
        simp [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans hlinear (by simpa [htwo] using hpow)

private theorem scale_mul_log_succ_square_le_pow_of_large_log
    {scale q : Nat}
    (hlarge : 4 * scale + 16 <= q) :
    scale * ((q + 1) * (q + 1)) <= 2 ^ q := by
  exact
    (Nat.strongRecOn q
      (motive := fun q =>
        4 * scale + 16 <= q ->
          scale * ((q + 1) * (q + 1)) <= 2 ^ q)
      (fun q ih hlarge => by
    by_cases hstep : 4 * scale + 18 <= q
    · have hprevLarge : 4 * scale + 16 <= q - 2 := by
        omega
      have hprev_lt : q - 2 < q := by
        omega
      have ihprev := ih (q - 2) hprev_lt hprevLarge
      have hlin : q + 1 <= 2 * ((q - 2) + 1) := by
        omega
      have hsq :
          (q + 1) * (q + 1) <=
            2 * (2 * (((q - 2) + 1) * ((q - 2) + 1))) := by
        have hmul := Nat.mul_le_mul hlin hlin
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hscaled :
          scale * ((q + 1) * (q + 1)) <=
            2 * (2 * (scale * (((q - 2) + 1) * ((q - 2) + 1)))) := by
        have hmul := Nat.mul_le_mul_left scale hsq
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hpowMul :
          2 * (2 * 2 ^ (q - 2)) = 2 ^ q := by
        have hqeq : q = (q - 2) + 2 := by
          omega
        calc
          2 * (2 * 2 ^ (q - 2)) = 2 ^ ((q - 2) + 2) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by rw [← hqeq]
      exact Nat.le_trans hscaled (by
        have hmul := Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left 2 ihprev)
        simpa [hpowMul] using hmul)
    · have hqUpper : q <= 4 * scale + 17 := by
        omega
      have hqSucc :
          q + 1 <= 2 ^ (scale + 5) := by
        exact Nat.le_trans (by omega)
          (four_mul_add_eighteen_le_two_pow_add_five scale)
      have hscale : scale <= 2 ^ scale := nat_le_two_pow scale
      have hsq :
          (q + 1) * (q + 1) <=
            2 ^ (scale + 5) * 2 ^ (scale + 5) :=
        Nat.mul_le_mul hqSucc hqSucc
      have hmul :
          scale * ((q + 1) * (q + 1)) <=
            2 ^ scale *
              (2 ^ (scale + 5) * 2 ^ (scale + 5)) :=
        Nat.mul_le_mul hscale hsq
      have hpows :
          2 ^ scale *
              (2 ^ (scale + 5) * 2 ^ (scale + 5)) =
            2 ^ (3 * scale + 10) := by
        calc
          2 ^ scale *
              (2 ^ (scale + 5) * 2 ^ (scale + 5)) =
            (2 ^ scale * 2 ^ (scale + 5)) *
              2 ^ (scale + 5) := by
              rw [Nat.mul_assoc]
          _ =
            2 ^ (scale + (scale + 5)) * 2 ^ (scale + 5) := by
              rw [← Nat.pow_add]
          _ = 2 ^ ((scale + (scale + 5)) + (scale + 5)) := by
              rw [← Nat.pow_add]
          _ = 2 ^ (3 * scale + 10) := by
              congr 1
              omega
      have hexp_le : 3 * scale + 10 <= q := by
        omega
      have hpow_le :
          2 ^ (3 * scale + 10) <= 2 ^ q :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hexp_le
      exact Nat.le_trans hmul (by simpa [hpows] using hpow_le))) hlarge

theorem eventually_scale_log2_succ_square_le_self
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale * ((Nat.log2 n + 1) * (Nat.log2 n + 1)) <= n := by
  refine ⟨2 ^ (4 * scale + 16), ?_⟩
  intro n hn
  have hlog : 4 * scale + 16 <= Nat.log2 n :=
    log2_ge_of_pow_le hn
  have hpow :
      scale * ((Nat.log2 n + 1) * (Nat.log2 n + 1)) <=
        2 ^ Nat.log2 n :=
    scale_mul_log_succ_square_le_pow_of_large_log hlog
  have hn_ne : n ≠ 0 := by
    intro hzero
    subst n
    have hpos : 0 < 2 ^ (4 * scale + 16) := pow_two_pos _
    omega
  exact Nat.le_trans hpow (Nat.log2_self_le hn_ne)

theorem eventually_scale_logLog_succ_square_le_log_succ
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale *
            ((Nat.log2 (Nat.log2 n + 1) + 1) *
              (Nat.log2 (Nat.log2 n + 1) + 1)) <=
          Nat.log2 n + 1 := by
  rcases eventually_scale_log2_succ_square_le_self scale with
    ⟨logThreshold, hlogThreshold⟩
  rcases eventually_scale_le_log2_succ logThreshold with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact hlogThreshold (Nat.log2 n + 1) (hthreshold n hn)⟩

private theorem scale_mul_log_succ_cube_le_pow_of_large_log
    {scale q : Nat}
    (hlarge : 8 * scale + 48 <= q) :
    scale * ((q + 1) * ((q + 1) * (q + 1))) <= 2 ^ q := by
  exact
    (Nat.strongRecOn q
      (motive := fun q =>
        8 * scale + 48 <= q ->
          scale * ((q + 1) * ((q + 1) * (q + 1))) <= 2 ^ q)
      (fun q ih hlarge => by
    by_cases hstep : 8 * scale + 51 <= q
    · have hprevLarge : 8 * scale + 48 <= q - 3 := by
        omega
      have hprev_lt : q - 3 < q := by
        omega
      have ihprev := ih (q - 3) hprev_lt hprevLarge
      have hlin : q + 1 <= 2 * ((q - 3) + 1) := by
        omega
      have hcube :
          (q + 1) * ((q + 1) * (q + 1)) <=
            2 * (2 * (2 *
              (((q - 3) + 1) *
                (((q - 3) + 1) * ((q - 3) + 1))))) := by
        have hmul :=
          Nat.mul_le_mul hlin (Nat.mul_le_mul hlin hlin)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hscaled :
          scale * ((q + 1) * ((q + 1) * (q + 1))) <=
            2 * (2 * (2 *
              (scale * (((q - 3) + 1) *
                (((q - 3) + 1) * ((q - 3) + 1)))))) := by
        have hmul := Nat.mul_le_mul_left scale hcube
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hpowMul :
          2 * (2 * (2 * 2 ^ (q - 3))) = 2 ^ q := by
        have hqeq : q = (q - 3) + 3 := by
          omega
        calc
          2 * (2 * (2 * 2 ^ (q - 3))) =
              2 ^ ((q - 3) + 3) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by rw [← hqeq]
      exact Nat.le_trans hscaled (by
        have hmul := Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left 2 ihprev))
        simpa [hpowMul] using hmul)
    · have hqUpper : q <= 8 * scale + 50 := by
        omega
      have hqSucc :
          q + 1 <= 2 ^ (scale + 7) := by
        exact Nat.le_trans (by omega)
          (eight_mul_add_fifty_one_le_two_pow_add_seven scale)
      have hscale : scale <= 2 ^ scale := nat_le_two_pow scale
      have hcube :
          (q + 1) * ((q + 1) * (q + 1)) <=
            2 ^ (scale + 7) *
              (2 ^ (scale + 7) * 2 ^ (scale + 7)) :=
        Nat.mul_le_mul hqSucc (Nat.mul_le_mul hqSucc hqSucc)
      have hmul :
          scale * ((q + 1) * ((q + 1) * (q + 1))) <=
            2 ^ scale *
              (2 ^ (scale + 7) *
                (2 ^ (scale + 7) * 2 ^ (scale + 7))) :=
        Nat.mul_le_mul hscale hcube
      have hpows :
          2 ^ scale *
              (2 ^ (scale + 7) *
                (2 ^ (scale + 7) * 2 ^ (scale + 7))) =
            2 ^ (4 * scale + 21) := by
        calc
          2 ^ scale *
              (2 ^ (scale + 7) *
                (2 ^ (scale + 7) * 2 ^ (scale + 7))) =
            (((2 ^ scale * 2 ^ (scale + 7)) *
              2 ^ (scale + 7)) * 2 ^ (scale + 7)) := by
              rw [Nat.mul_assoc]
              rw [Nat.mul_assoc]
          _ =
            ((2 ^ (scale + (scale + 7)) *
              2 ^ (scale + 7)) * 2 ^ (scale + 7)) := by
              rw [← Nat.pow_add]
          _ =
            (2 ^ ((scale + (scale + 7)) + (scale + 7)) *
              2 ^ (scale + 7)) := by
              rw [← Nat.pow_add]
          _ =
            2 ^ (((scale + (scale + 7)) + (scale + 7)) +
              (scale + 7)) := by
              rw [← Nat.pow_add]
          _ = 2 ^ (4 * scale + 21) := by
              congr 1
              omega
      have hexp_le : 4 * scale + 21 <= q := by
        omega
      have hpow_le :
          2 ^ (4 * scale + 21) <= 2 ^ q :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hexp_le
      exact Nat.le_trans hmul (by simpa [hpows] using hpow_le))) hlarge

theorem eventually_scale_log2_succ_cube_le_self
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale * ((Nat.log2 n + 1) *
          ((Nat.log2 n + 1) * (Nat.log2 n + 1))) <= n := by
  refine ⟨2 ^ (8 * scale + 48), ?_⟩
  intro n hn
  have hlog : 8 * scale + 48 <= Nat.log2 n :=
    log2_ge_of_pow_le hn
  have hpow :
      scale * ((Nat.log2 n + 1) *
        ((Nat.log2 n + 1) * (Nat.log2 n + 1))) <=
        2 ^ Nat.log2 n :=
    scale_mul_log_succ_cube_le_pow_of_large_log hlog
  have hn_ne : n ≠ 0 := by
    intro hzero
    subst n
    have hpos : 0 < 2 ^ (8 * scale + 48) := pow_two_pos _
    omega
  exact Nat.le_trans hpow (Nat.log2_self_le hn_ne)

theorem eventually_scale_logLog_succ_cube_le_log_succ
    (scale : Nat) :
    exists threshold : Nat,
      forall n : Nat, threshold <= n ->
        scale *
            ((Nat.log2 (Nat.log2 n + 1) + 1) *
              ((Nat.log2 (Nat.log2 n + 1) + 1) *
                (Nat.log2 (Nat.log2 n + 1) + 1))) <=
          Nat.log2 n + 1 := by
  rcases eventually_scale_log2_succ_cube_le_self scale with
    ⟨logThreshold, hlogThreshold⟩
  rcases eventually_scale_le_log2_succ logThreshold with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    exact hlogThreshold (Nat.log2 n + 1) (hthreshold n hn)⟩

/--
Canonical local-directory budget for two-level interior sparse tables over
about `n / log n` block minima with `log log n`-bit offsets and another
`log log n` factor for sparse-table levels.
-/
def logLogSquaredSampledDirectoryOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * ((n / (Nat.log2 n + 1)) *
    ((Nat.log2 (Nat.log2 n + 1) + 1) *
      (Nat.log2 (Nat.log2 n + 1) + 1)))

theorem logLogSquaredSampledDirectoryOverhead_littleO (slots : Nat) :
    LittleOLinear (logLogSquaredSampledDirectoryOverhead slots) := by
  intro scale _hscale
  rcases eventually_scale_logLog_succ_square_le_log_succ
      (scale * slots) with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    have hlog :
        (scale * slots) *
            ((Nat.log2 (Nat.log2 n + 1) + 1) *
              (Nat.log2 (Nat.log2 n + 1) + 1)) <=
          Nat.log2 n + 1 :=
      hthreshold n hn
    have hmul :=
      Nat.mul_le_mul_right (n / (Nat.log2 n + 1)) hlog
    have hfirst :
        scale *
            (slots * ((n / (Nat.log2 n + 1)) *
              ((Nat.log2 (Nat.log2 n + 1) + 1) *
                (Nat.log2 (Nat.log2 n + 1) + 1)))) <=
          (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hdiv :
        (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) <= n := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self n (Nat.log2 n + 1)
    exact Nat.le_trans hfirst hdiv⟩

/--
Canonical sparse/dense select-local budget with one extra `log log n` factor.

The final false-select locator uses this envelope for local directory codecs
whose number of sampled slots is about `n / log n` and whose per-slot payload
has three `log log n`-sized factors in the current arithmetic model.
-/
def logLogCubedSampledDirectoryOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * ((n / (Nat.log2 n + 1)) *
    ((Nat.log2 (Nat.log2 n + 1) + 1) *
      ((Nat.log2 (Nat.log2 n + 1) + 1) *
        (Nat.log2 (Nat.log2 n + 1) + 1))))

theorem logLogCubedSampledDirectoryOverhead_littleO (slots : Nat) :
    LittleOLinear (logLogCubedSampledDirectoryOverhead slots) := by
  intro scale _hscale
  rcases eventually_scale_logLog_succ_cube_le_log_succ
      (scale * slots) with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    have hlog :
        (scale * slots) *
            ((Nat.log2 (Nat.log2 n + 1) + 1) *
              ((Nat.log2 (Nat.log2 n + 1) + 1) *
                (Nat.log2 (Nat.log2 n + 1) + 1))) <=
          Nat.log2 n + 1 :=
      hthreshold n hn
    have hmul := Nat.mul_le_mul_right (n / (Nat.log2 n + 1)) hlog
    have hfirst :
        scale *
            (slots * ((n / (Nat.log2 n + 1)) *
              ((Nat.log2 (Nat.log2 n + 1) + 1) *
                ((Nat.log2 (Nat.log2 n + 1) + 1) *
                  (Nat.log2 (Nat.log2 n + 1) + 1))))) <=
          (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hdiv :
        (Nat.log2 n + 1) * (n / (Nat.log2 n + 1)) <= n := by
      simpa [Nat.mul_comm] using
        Nat.div_mul_le_self n (Nat.log2 n + 1)
    exact Nat.le_trans hfirst hdiv⟩

/--
Canonical Mathlib-free sampled-directory budget used by the succinct frontier.

This intentionally names only the asymptotic envelope: a concrete encoder can
spend any fixed number of such sampled slots for rank, select, navigation, or
microtable metadata and still obtain `o(n)` auxiliary space.
-/
def sampledDirectoryOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * (n / (Nat.log2 n + 1))

theorem LittleOLinear.mul_left
    {f : Nat -> Nat} (c : Nat)
    (hf : LittleOLinear f) :
    LittleOLinear (fun n => c * f n) := by
  intro scale hscale
  by_cases hc : c = 0
  · subst c
    exact ⟨0, by intro n _hn; simp⟩
  · have hscale_c : 0 < scale * c := Nat.mul_pos hscale (Nat.pos_of_ne_zero hc)
    rcases hf (scale * c) hscale_c with ⟨threshold, hthreshold⟩
    exact ⟨threshold, by
      intro n hn
      have h := hthreshold n hn
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h⟩

theorem LittleOLinear.mul_right
    {f : Nat -> Nat} (c : Nat)
    (hf : LittleOLinear f) :
    LittleOLinear (fun n => f n * c) := by
  simpa [Nat.mul_comm] using hf.mul_left c

theorem idDivLogLogOverhead_littleO (slots : Nat) :
    LittleOLinear (idDivLogLogOverhead slots) := by
  unfold idDivLogLogOverhead
  exact littleOLinear_id_div_logLog_succ.mul_left slots

theorem sampledDirectoryOverhead_littleO (slots : Nat) :
    LittleOLinear (sampledDirectoryOverhead slots) := by
  unfold sampledDirectoryOverhead
  exact littleOLinear_id_div_log2_succ.mul_left slots

private theorem le_of_two_mul_le_two_mul
    {a b : Nat} (h : 2 * a <= 2 * b) : a <= b := by
  exact Nat.le_of_mul_le_mul_left h (by omega)

theorem LittleOLinear.comp_two_mul_arg
    {f : Nat -> Nat}
    (hf : LittleOLinear f) :
    LittleOLinear (fun n => f (2 * n)) := by
  intro scale hscale
  have htwoScale : 0 < 2 * scale := Nat.mul_pos (by omega) hscale
  rcases hf (2 * scale) htwoScale with ⟨threshold, hthreshold⟩
  exact ⟨threshold, by
    intro n hn
    have hthreshold' : threshold <= 2 * n := by
      have hnle : n <= 2 * n := by omega
      exact Nat.le_trans hn hnle
    have h := hthreshold (2 * n) hthreshold'
    have htwo :
        2 * (scale * f (2 * n)) <= 2 * n := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    exact le_of_two_mul_le_two_mul htwo⟩

theorem LittleOLinear.add
    {f g : Nat -> Nat}
    (hf : LittleOLinear f) (hg : LittleOLinear g) :
    LittleOLinear (fun n => f n + g n) := by
  intro scale hscale
  have htwo_scale : 0 < 2 * scale := Nat.mul_pos (by omega) hscale
  rcases hf (2 * scale) htwo_scale with ⟨tf, hfEventually⟩
  rcases hg (2 * scale) htwo_scale with ⟨tg, hgEventually⟩
  exact ⟨Nat.max tf tg, by
    intro n hn
    have hnf : tf <= n := Nat.le_trans (Nat.le_max_left tf tg) hn
    have hng : tg <= n := Nat.le_trans (Nat.le_max_right tf tg) hn
    have hfBound := hfEventually n hnf
    have hgBound := hgEventually n hng
    have hsum :
        (2 * scale) * f n + (2 * scale) * g n <= n + n :=
      Nat.add_le_add hfBound hgBound
    have hleft :
        (2 * scale) * f n + (2 * scale) * g n =
          2 * (scale * (f n + g n)) := by
      calc
        (2 * scale) * f n + (2 * scale) * g n =
            (2 * scale) * (f n + g n) := by
          rw [Nat.mul_add]
        _ = 2 * (scale * (f n + g n)) := by
          rw [Nat.mul_assoc]
    have hright : n + n = 2 * n := by omega
    have htwo :
        2 * (scale * (f n + g n)) <= 2 * n := by
      simpa [hleft, hright] using hsum
    exact le_of_two_mul_le_two_mul htwo⟩

theorem LittleOLinear.add_const
    {f : Nat -> Nat} (c : Nat)
    (hf : LittleOLinear f) :
    LittleOLinear (fun n => f n + c) := by
  simpa using hf.add (littleOLinear_const c)

theorem LittleOLinear.const_add
    {f : Nat -> Nat} (c : Nat)
    (hf : LittleOLinear f) :
    LittleOLinear (fun n => c + f n) := by
  simpa [Nat.add_comm] using hf.add_const c

end SuccinctSpace

end RMQ

import RMQ.Core.EncodingLowerBound
import RMQ.Core.Succinct

/-!
# Succinct RMQ space/profile interface

This module is the first broadword-facing layer for the final succinct RMQ
upper-bound story.  It does not assert that Lean's executable representation is
a machine-word implementation.  Instead, it packages the standard word-RAM
claim shape:

* an exact `2*n` Cartesian-shape payload,
* counted auxiliary payload bits,
* a costed query decoder whose cost is bounded by a constant independent of
  `n`, and
* an explicit `o(n)` predicate for the auxiliary payload budget.

Concrete balanced-parentheses/rank-select directories can instantiate this
interface without changing the RMQ contract or the lower-bound framework.
-/

namespace RMQ

namespace SuccinctSpace

/-- Cartesian-shape balanced-parentheses codes are genuinely balanced. -/
theorem bpCode_balanced (shape : Cartesian.CartesianShape) :
    Succinct.Balanced shape.bpCode := by
  induction shape with
  | empty =>
      simpa [Cartesian.CartesianShape.bpCode] using Succinct.balanced_nil
  | node left right ihleft ihright =>
      simpa [Cartesian.CartesianShape.bpCode] using
        Succinct.balanced_wrap_append
          (inside := left.bpCode) (rest := right.bpCode)
          ihleft ihright

/-- Package a Cartesian shape's BP code as a balanced-parentheses bitvector. -/
def bpParensOfShape (shape : Cartesian.CartesianShape) :
    Succinct.BalancedParens where
  bits := shape.bpCode
  balanced := bpCode_balanced shape

theorem bpParensOfShape_bits (shape : Cartesian.CartesianShape) :
    (bpParensOfShape shape).bits = shape.bpCode := by
  rfl

theorem bpParensOfShape_bits_length_of_shapeOfSize
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : Cartesian.ShapeOfSize n shape) :
    (bpParensOfShape shape).bits.length = 2 * n := by
  exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshape

/-- Close-parenthesis position for the node with the given inorder index. -/
def bpCloseOfInorder? :
    Cartesian.CartesianShape -> Nat -> Option Nat
  | Cartesian.CartesianShape.empty, _ => none
  | Cartesian.CartesianShape.node left right, idx =>
      if idx < left.size then
        (bpCloseOfInorder? left idx).map (fun pos => pos + 1)
      else if idx = left.size then
        some (left.bpCode.length + 1)
      else
        (bpCloseOfInorder? right (idx - left.size - 1)).map
          (fun pos => left.bpCode.length + 2 + pos)

theorem bpCloseOfInorder?_some_of_lt
    (shape : Cartesian.CartesianShape) {idx : Nat}
    (hidx : idx < shape.size) :
    exists pos, bpCloseOfInorder? shape idx = some pos := by
  induction shape generalizing idx with
  | empty =>
      simp [Cartesian.CartesianShape.size] at hidx
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · rcases ihleft hleft with ⟨pos, hpos⟩
        exact ⟨pos + 1, by
          simp [bpCloseOfInorder?, hleft, hpos]⟩
      · by_cases hroot : idx = left.size
        · exact ⟨left.bpCode.length + 1, by
            simp [bpCloseOfInorder?, hroot]⟩
        · have hright : idx - left.size - 1 < right.size := by
            simp [Cartesian.CartesianShape.size] at hidx
            omega
          rcases ihright hright with ⟨pos, hpos⟩
          exact ⟨left.bpCode.length + 2 + pos, by
            simp [bpCloseOfInorder?, hleft, hroot, hpos]⟩

theorem bpCloseOfInorder?_bounds
    (shape : Cartesian.CartesianShape) {idx pos : Nat}
    (hpos : bpCloseOfInorder? shape idx = some pos) :
    pos < shape.bpCode.length := by
  induction shape generalizing idx pos with
  | empty =>
      simp [bpCloseOfInorder?] at hpos
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · cases hrec : bpCloseOfInorder? left idx with
        | none =>
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
        | some inner =>
            have hinner := ihleft hrec
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
            subst pos
            simp [Cartesian.CartesianShape.bpCode]
            omega
      · by_cases hroot : idx = left.size
        · simp [bpCloseOfInorder?, hroot] at hpos
          subst pos
          simp [Cartesian.CartesianShape.bpCode]
        · cases hrec :
            bpCloseOfInorder? right (idx - left.size - 1) with
          | none =>
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
          | some inner =>
              have hinner := ihright hrec
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
              subst pos
              simp [Cartesian.CartesianShape.bpCode]
              omega

theorem bpCode_rankFalse_full (shape : Cartesian.CartesianShape) :
    Succinct.rankPrefix false shape.bpCode shape.bpCode.length =
      shape.size := by
  induction shape with
  | empty =>
      simp [Cartesian.CartesianShape.bpCode,
        Cartesian.CartesianShape.size, Succinct.rankPrefix]
  | node left right ihleft ihright =>
      have htail :
          Succinct.rankPrefix false
              (left.bpCode ++ false :: right.bpCode)
              (left.bpCode ++ false :: right.bpCode).length =
            left.size + (1 + right.size) := by
        have happend :=
          Succinct.rankPrefix_append_of_ge false left.bpCode
            (false :: right.bpCode)
            (limit := (left.bpCode ++ false :: right.bpCode).length)
            (by simp)
        have hright :
            Succinct.rankPrefix false (false :: right.bpCode)
                (false :: right.bpCode).length =
              1 + right.size := by
          simp [Succinct.rankPrefix, ihright]
        have hright' :
            Succinct.rankPrefix false (false :: right.bpCode)
                ((left.bpCode ++ false :: right.bpCode).length -
                  left.bpCode.length) =
              1 + right.size := by
          simpa using hright
        rw [happend]
        rw [ihleft, hright']
      calc
        Succinct.rankPrefix false
            (Cartesian.CartesianShape.node left right).bpCode
            (Cartesian.CartesianShape.node left right).bpCode.length =
          Succinct.rankPrefix false
            (left.bpCode ++ false :: right.bpCode)
            (left.bpCode ++ false :: right.bpCode).length := by
            simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix]
        _ = left.size + (1 + right.size) := htail
        _ = (Cartesian.CartesianShape.node left right).size := by
            simp [Cartesian.CartesianShape.size]
            omega

theorem bpCloseOfInorder?_rankFalse_succ
    (shape : Cartesian.CartesianShape) {idx pos : Nat}
    (hpos : bpCloseOfInorder? shape idx = some pos) :
    Succinct.rankPrefix false shape.bpCode (pos + 1) = idx + 1 := by
  induction shape generalizing idx pos with
  | empty =>
      simp [bpCloseOfInorder?] at hpos
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · cases hrec : bpCloseOfInorder? left idx with
        | none =>
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
        | some inner =>
            have hinnerBound :
                inner < left.bpCode.length :=
              bpCloseOfInorder?_bounds left hrec
            have hrank := ihleft hrec
            simp [bpCloseOfInorder?, hleft, hrec] at hpos
            subst pos
            have happend :
                Succinct.rankPrefix false
                    (left.bpCode ++ false :: right.bpCode)
                    (inner + 1) =
                  Succinct.rankPrefix false left.bpCode (inner + 1) :=
              Succinct.rankPrefix_append_of_le false left.bpCode
                (false :: right.bpCode) (limit := inner + 1) (by omega)
            calc
              Succinct.rankPrefix false
                  (Cartesian.CartesianShape.node left right).bpCode
                  (inner + 1 + 1) =
                Succinct.rankPrefix false
                    (left.bpCode ++ false :: right.bpCode)
                    (inner + 1) := by
                  simp [Cartesian.CartesianShape.bpCode,
                    Succinct.rankPrefix, Nat.add_assoc]
              _ = Succinct.rankPrefix false left.bpCode (inner + 1) := happend
              _ = idx + 1 := hrank
      · by_cases hroot : idx = left.size
        · simp [bpCloseOfInorder?, hroot] at hpos
          subst pos
          have happend :
              Succinct.rankPrefix false
                  (left.bpCode ++ false :: right.bpCode)
                  (left.bpCode.length + 1) =
                Succinct.rankPrefix false left.bpCode left.bpCode.length +
                  Succinct.rankPrefix false (false :: right.bpCode) 1 := by
            have hge :
                left.bpCode.length <= left.bpCode.length + 1 := by omega
            have happ :=
              Succinct.rankPrefix_append_of_ge false left.bpCode
                (false :: right.bpCode)
                (limit := left.bpCode.length + 1) hge
            simpa using happ
          calc
            Succinct.rankPrefix false
                (Cartesian.CartesianShape.node left right).bpCode
                (left.bpCode.length + 1 + 1) =
              Succinct.rankPrefix false
                  (left.bpCode ++ false :: right.bpCode)
                  (left.bpCode.length + 1) := by
                simp [Cartesian.CartesianShape.bpCode,
                  Succinct.rankPrefix, Nat.add_assoc]
            _ = left.size + 1 := by
                rw [happend, bpCode_rankFalse_full left]
                simp [Succinct.rankPrefix]
            _ = idx + 1 := by
                omega
        · cases hrec :
            bpCloseOfInorder? right (idx - left.size - 1) with
          | none =>
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
          | some inner =>
              have hrank := ihright hrec
              simp [bpCloseOfInorder?, hleft, hroot, hrec] at hpos
              subst pos
              have happend :
                  Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) =
                    Succinct.rankPrefix false left.bpCode
                        left.bpCode.length +
                      Succinct.rankPrefix false (false :: right.bpCode)
                        (2 + inner) := by
                have hge :
                    left.bpCode.length <=
                      left.bpCode.length + 2 + inner := by omega
                have happ :=
                  Succinct.rankPrefix_append_of_ge false left.bpCode
                    (false :: right.bpCode)
                    (limit := left.bpCode.length + 2 + inner) hge
                have hsub :
                    left.bpCode.length + 2 + inner -
                        left.bpCode.length =
                      2 + inner := by
                  omega
                simpa [hsub] using happ
              have htail :
                  Succinct.rankPrefix false (false :: right.bpCode)
                      (2 + inner) =
                    1 +
                      Succinct.rankPrefix false right.bpCode
                        (inner + 1) := by
                have htailRaw :
                    Succinct.rankPrefix false (false :: right.bpCode)
                        ((inner + 1) + 1) =
                      1 +
                        Succinct.rankPrefix false right.bpCode
                          (inner + 1) := by
                  simp [Succinct.rankPrefix]
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                  using htailRaw
              have hlead :
                  Succinct.rankPrefix false
                      (true :: (left.bpCode ++ false :: right.bpCode))
                      (left.bpCode.length + 2 + inner + 1) =
                    Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) := by
                simp [Succinct.rankPrefix]
              calc
                Succinct.rankPrefix false
                    (Cartesian.CartesianShape.node left right).bpCode
                    (left.bpCode.length + 2 + inner + 1) =
                  Succinct.rankPrefix false
                      (left.bpCode ++ false :: right.bpCode)
                      (left.bpCode.length + 2 + inner) := by
                    simpa [Cartesian.CartesianShape.bpCode,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                      using hlead
                _ = left.size + (1 +
                    Succinct.rankPrefix false right.bpCode (inner + 1)) := by
                    rw [happend, bpCode_rankFalse_full left, htail]
                _ = idx + 1 := by
                    rw [hrank]
                    omega

theorem select_false_bpCode_eq_bpCloseOfInorder?
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Succinct.select false shape.bpCode idx =
      bpCloseOfInorder? shape idx := by
  induction shape generalizing idx with
  | empty =>
      simp [Cartesian.CartesianShape.bpCode, bpCloseOfInorder?,
        Succinct.select, Succinct.selectFrom]
  | node left right ihleft ihright =>
      by_cases hleft : idx < left.size
      · rcases bpCloseOfInorder?_some_of_lt left hleft with
          ⟨leftClose, hleftClose⟩
        have hleftSelect :
            Succinct.select false left.bpCode idx = some leftClose := by
          simpa [hleftClose] using ihleft idx
        have hshift :
            Succinct.selectFrom false left.bpCode 1 idx =
              some (1 + leftClose) :=
          Succinct.selectFrom_of_select hleftSelect
        have happend :
            Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx =
              some (1 + leftClose) :=
          Succinct.selectFrom_append_left_of_some
            (ys := false :: right.bpCode) hshift
        simp [Cartesian.CartesianShape.bpCode, bpCloseOfInorder?,
          Succinct.select, Succinct.selectFrom, hleft, hleftClose, happend]
        omega
      · by_cases hroot : idx = left.size
        · have hcount :
              Succinct.rankPrefix false left.bpCode left.bpCode.length <=
                idx := by
            rw [bpCode_rankFalse_full left]
            omega
          have hdrop :=
            Succinct.selectFrom_append_right_after_count false
              left.bpCode (false :: right.bpCode) 1 idx hcount
          calc
            Succinct.select false
                (Cartesian.CartesianShape.node left right).bpCode idx =
              Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx := by
                simp [Cartesian.CartesianShape.bpCode, Succinct.select,
                  Succinct.selectFrom]
            _ = Succinct.selectFrom false (false :: right.bpCode)
                (1 + left.bpCode.length) (idx - left.size) := by
                simpa [bpCode_rankFalse_full left] using hdrop
            _ = some (left.bpCode.length + 1) := by
                simp [Succinct.selectFrom, hroot]
                omega
            _ = bpCloseOfInorder?
                (Cartesian.CartesianShape.node left right) idx := by
                simp [bpCloseOfInorder?, hroot]
        · have hcount :
              Succinct.rankPrefix false left.bpCode left.bpCode.length <=
                idx := by
            rw [bpCode_rankFalse_full left]
            omega
          have hdrop :=
            Succinct.selectFrom_append_right_after_count false
              left.bpCode (false :: right.bpCode) 1 idx hcount
          have hdrop' :
              Succinct.selectFrom false
                  (left.bpCode ++ false :: right.bpCode) 1 idx =
                Succinct.selectFrom false (false :: right.bpCode)
                  (1 + left.bpCode.length) (idx - left.size) := by
            simpa [bpCode_rankFalse_full left] using hdrop
          have hocc : idx - left.size ≠ 0 := by
            omega
          have htail :
              Succinct.selectFrom false (false :: right.bpCode)
                  (1 + left.bpCode.length) (idx - left.size) =
                Succinct.selectFrom false right.bpCode
                  (left.bpCode.length + 2) (idx - left.size - 1) := by
            have hbase :
                1 + left.bpCode.length + 1 = left.bpCode.length + 2 := by
              omega
            simp [Succinct.selectFrom, hocc, hbase]
          have hbaseSelect :=
            Succinct.selectFrom_base_eq false right.bpCode
              (left.bpCode.length + 2) (idx - left.size - 1)
          calc
            Succinct.select false
                (Cartesian.CartesianShape.node left right).bpCode idx =
              Succinct.selectFrom false
                (left.bpCode ++ false :: right.bpCode) 1 idx := by
                simp [Cartesian.CartesianShape.bpCode, Succinct.select,
                  Succinct.selectFrom]
            _ = Succinct.selectFrom false (false :: right.bpCode)
                (1 + left.bpCode.length) (idx - left.size) := by
                exact hdrop'
            _ = Succinct.selectFrom false right.bpCode
                (left.bpCode.length + 2) (idx - left.size - 1) := htail
            _ = (Succinct.select false right.bpCode
                (idx - left.size - 1)).map
                  (fun pos => left.bpCode.length + 2 + pos) := hbaseSelect
            _ = (bpCloseOfInorder? right (idx - left.size - 1)).map
                  (fun pos => left.bpCode.length + 2 + pos) := by
                rw [ihright]
            _ = bpCloseOfInorder?
                (Cartesian.CartesianShape.node left right) idx := by
                simp [bpCloseOfInorder?, hleft, hroot]

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

/-- Interpret one Boolean bit as a binary digit. -/
def bitToNat (bit : Bool) : Nat :=
  if bit then 1 else 0

/--
Little-endian interpretation of one machine word as a natural number.

This is a word-level decoder.  Structures using it still have to prove that the
queried word is fetched from the counted payload, rather than from an
unaccounted proof-side table.
-/
def bitsToNatLE : List Bool -> Nat
  | [] => 0
  | bit :: rest => bitToNat bit + 2 * bitsToNatLE rest

/-- Fixed-width little-endian encoding of a natural number. -/
def natToBitsLE : Nat -> Nat -> List Bool
  | 0, _ => []
  | width + 1, n =>
      decide (n % 2 = 1) :: natToBitsLE width (n / 2)

theorem natToBitsLE_length (width n : Nat) :
    (natToBitsLE width n).length = width := by
  induction width generalizing n with
  | zero =>
      simp [natToBitsLE]
  | succ width ih =>
      simp [natToBitsLE, ih]

theorem bitToNat_decide_mod_two (n : Nat) :
    bitToNat (decide (n % 2 = 1)) = n % 2 := by
  unfold bitToNat
  by_cases h : n % 2 = 1
  · simp [h]
  · have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
    have hzero : n % 2 = 0 := by omega
    simp [hzero]

theorem bitsToNatLE_natToBitsLE_of_lt
    {width n : Nat} (hbound : n < 2 ^ width) :
    bitsToNatLE (natToBitsLE width n) = n := by
  induction width generalizing n with
  | zero =>
      have hn : n = 0 := by
        simpa using hbound
      simp [natToBitsLE, bitsToNatLE, hn]
  | succ width ih =>
      have hhalf : n / 2 < 2 ^ width := by
        have hpow :
            2 ^ (width + 1) = 2 ^ width * 2 := by
          rw [Nat.pow_succ]
        have hlt : n < 2 ^ width * 2 := by
          simpa [hpow] using hbound
        exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 hlt
      have hrec := ih hhalf
      have hdecomp : n % 2 + 2 * (n / 2) = n := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div n 2)
      simp [natToBitsLE, bitsToNatLE, bitToNat_decide_mod_two,
        hrec, hdecomp]

/-- Flatten a list of payload words into the payload bitstream they store. -/
def flattenPayloadWords : List (List Bool) -> List Bool
  | [] => []
  | word :: rest => word ++ flattenPayloadWords rest

theorem flattenPayloadWords_append
    (xs ys : List (List Bool)) :
    flattenPayloadWords (xs ++ ys) =
      flattenPayloadWords xs ++ flattenPayloadWords ys := by
  induction xs with
  | nil =>
      simp [flattenPayloadWords]
  | cons word rest ih =>
      simp [flattenPayloadWords, ih, List.append_assoc]

theorem flattenPayloadWords_replicate_nil (n : Nat) :
    flattenPayloadWords (List.replicate n []) = [] := by
  induction n with
  | zero =>
      simp [flattenPayloadWords]
  | succ n ih =>
      simp [List.replicate, flattenPayloadWords, ih]

theorem flattenPayloadWords_length_of_forall_length
    {words : List (List Bool)} {width : Nat}
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    (flattenPayloadWords words).length = words.length * width := by
  induction words with
  | nil =>
      simp [flattenPayloadWords]
  | cons word rest ih =>
      have hword : word.length = width :=
        hwidth List.mem_cons_self
      have hrest :
          forall {tailWord : List Bool},
            List.Mem tailWord rest -> tailWord.length = width := by
        intro tailWord hmem
        exact hwidth (List.mem_cons_of_mem word hmem)
      simp [flattenPayloadWords, hword, ih hrest, Nat.succ_mul,
        Nat.add_comm]

/--
Fuelled fixed-size payload chunker.

The `fuel` argument keeps the definition structurally recursive.  The public
constructor below supplies enough fuel and proves that, for positive word size,
flattening the chunks recovers the original payload.
-/
def chunkPayloadWordsFuel
    (wordSize fuel : Nat) (payload : List Bool) : List (List Bool) :=
  match fuel, payload with
  | 0, _ => []
  | _ + 1, [] => []
  | fuel' + 1, bits =>
      bits.take wordSize ::
        chunkPayloadWordsFuel wordSize fuel' (bits.drop wordSize)

/-- Split payload bits into fixed-size words.  The final word may be shorter. -/
def chunkPayloadWords (wordSize : Nat) (payload : List Bool) :
    List (List Bool) :=
  chunkPayloadWordsFuel wordSize (payload.length + 1) payload

theorem flattenPayloadWords_chunkPayloadWordsFuel
    {wordSize fuel : Nat} (hword : 0 < wordSize) :
    forall payload : List Bool,
      payload.length <= fuel ->
        flattenPayloadWords
          (chunkPayloadWordsFuel wordSize fuel payload) =
          payload := by
  induction fuel with
  | zero =>
      intro payload hlen
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel, flattenPayloadWords]
      | cons bit rest =>
          simp at hlen
  | succ fuel ih =>
      intro payload hlen
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel, flattenPayloadWords]
      | cons bit rest =>
          have hdrop :
              ((bit :: rest).drop wordSize).length <= fuel := by
            rw [List.length_drop]
            omega
          have hrec := ih ((bit :: rest).drop wordSize) hdrop
          calc
            flattenPayloadWords
                (chunkPayloadWordsFuel wordSize (fuel + 1)
                  (bit :: rest)) =
              (bit :: rest).take wordSize ++
                flattenPayloadWords
                  (chunkPayloadWordsFuel wordSize fuel
                    ((bit :: rest).drop wordSize)) := by
                simp [chunkPayloadWordsFuel, flattenPayloadWords]
            _ = (bit :: rest).take wordSize ++
                (bit :: rest).drop wordSize := by
                  rw [hrec]
            _ = bit :: rest := by
                  exact List.take_append_drop wordSize (bit :: rest)

theorem flattenPayloadWords_chunkPayloadWords
    {wordSize : Nat} (hword : 0 < wordSize) (payload : List Bool) :
    flattenPayloadWords (chunkPayloadWords wordSize payload) = payload := by
  unfold chunkPayloadWords
  exact flattenPayloadWords_chunkPayloadWordsFuel hword payload (by omega)

theorem chunkPayloadWordsFuel_word_length_le
    (wordSize fuel : Nat) :
    forall {payload word : List Bool},
      List.Mem word (chunkPayloadWordsFuel wordSize fuel payload) ->
        word.length <= wordSize := by
  induction fuel with
  | zero =>
      intro payload word hmem
      simp [chunkPayloadWordsFuel] at hmem
      cases hmem
  | succ fuel ih =>
      intro payload word hmem
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel] at hmem
          cases hmem
      | cons bit rest =>
          change
            List.Mem word
              ((bit :: rest).take wordSize ::
                chunkPayloadWordsFuel wordSize fuel
                  ((bit :: rest).drop wordSize)) at hmem
          cases hmem with
          | head =>
            rw [List.length_take]
            exact Nat.min_le_left wordSize (bit :: rest).length
          | tail _ htail =>
              exact ih htail

theorem chunkPayloadWords_word_length_le
    (wordSize : Nat) {payload word : List Bool}
    (hmem : List.Mem word (chunkPayloadWords wordSize payload)) :
    word.length <= wordSize := by
  unfold chunkPayloadWords at hmem
  exact chunkPayloadWordsFuel_word_length_le
    wordSize (payload.length + 1) hmem

theorem chunkPayloadWordsFuel_get?_eq_take_drop
    {wordSize fuel : Nat} :
    forall {payload word : List Bool} {i : Nat},
      (chunkPayloadWordsFuel wordSize fuel payload)[i]? = some word ->
        word = (payload.drop (i * wordSize)).take wordSize := by
  induction fuel with
  | zero =>
      intro payload word i hget
      simp [chunkPayloadWordsFuel] at hget
  | succ fuel ih =>
      intro payload word i hget
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel] at hget
      | cons bit rest =>
          cases i with
          | zero =>
              simp [chunkPayloadWordsFuel] at hget
              simpa using hget.symm
          | succ i =>
              have htail :
                  (chunkPayloadWordsFuel wordSize fuel
                    ((bit :: rest).drop wordSize))[i]? = some word := by
                simpa [chunkPayloadWordsFuel] using hget
              have hrec := ih htail
              calc
                word = (((bit :: rest).drop wordSize).drop
                    (i * wordSize)).take wordSize := hrec
                _ = ((bit :: rest).drop ((i + 1) * wordSize)).take
                    wordSize := by
                  simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem chunkPayloadWords_get?_eq_take_drop
    {wordSize : Nat} {payload word : List Bool} {i : Nat}
    (hget : (chunkPayloadWords wordSize payload)[i]? = some word) :
    word = (payload.drop (i * wordSize)).take wordSize := by
  unfold chunkPayloadWords at hget
  exact chunkPayloadWordsFuel_get?_eq_take_drop hget

theorem chunkPayloadWordsFuel_get?_some_of_mul_lt
    {wordSize fuel : Nat} (hword : 0 < wordSize) :
    forall {payload : List Bool} {i : Nat},
      payload.length <= fuel ->
      i * wordSize < payload.length ->
        exists word,
          (chunkPayloadWordsFuel wordSize fuel payload)[i]? =
            some word := by
  induction fuel with
  | zero =>
      intro payload i hlen hi
      cases payload with
      | nil =>
          simp at hi
      | cons bit rest =>
          simp at hlen
  | succ fuel ih =>
      intro payload i hlen hi
      cases payload with
      | nil =>
          simp at hi
      | cons bit rest =>
          cases i with
          | zero =>
              refine ⟨(bit :: rest).take wordSize, ?_⟩
              simp [chunkPayloadWordsFuel]
          | succ i =>
              have hdropLen :
                  ((bit :: rest).drop wordSize).length <= fuel := by
                rw [List.length_drop]
                omega
              have hiTail :
                  i * wordSize < ((bit :: rest).drop wordSize).length := by
                rw [List.length_drop]
                have hmul :
                    (i + 1) * wordSize = i * wordSize + wordSize := by
                  simp [Nat.succ_mul]
                omega
              rcases ih hdropLen hiTail with ⟨word, hget⟩
              exact ⟨word, by simpa [chunkPayloadWordsFuel] using hget⟩

theorem chunkPayloadWords_get?_some_of_mul_lt
    {wordSize : Nat} (hword : 0 < wordSize)
    {payload : List Bool} {i : Nat}
    (hi : i * wordSize < payload.length) :
    exists word,
      (chunkPayloadWords wordSize payload)[i]? = some word := by
  unfold chunkPayloadWords
  exact chunkPayloadWordsFuel_get?_some_of_mul_lt hword (by omega) hi

/--
A stored word array whose flattened word contents are exactly the counted
payload bits.

This is the first payload-live representation boundary for the succinct layer:
query procedures may read `words`, but the represented bits are tied directly to
the payload whose length is charged in space theorems.
-/
structure PayloadWordStore (payload : List Bool) where
  words : Array (List Bool)
  erases : flattenPayloadWords words.toList = payload

namespace PayloadWordStore

def readWordCosted
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    Costed (Option (List Bool)) :=
  (RAM.readArray? store.words i).toCosted

@[simp] theorem readWordCosted_erase
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).erase = store.words[i]? := by
  rfl

@[simp] theorem readWordCosted_cost
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).cost = 1 := by
  rfl

theorem readWordCosted_cost_le_one
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).cost <= 1 := by
  simp

theorem payload_eq_words_join
    {payload : List Bool}
    (store : PayloadWordStore payload) :
    flattenPayloadWords store.words.toList = payload :=
  store.erases

end PayloadWordStore

/--
Payload store with an explicit upper bound on each stored word.

This is the representation discipline needed for broadword claims: clients can
still use `PayloadWordStore` directly for reference scaffolding, while final
succinct profiles can require this bounded wrapper to rule out one giant
payload word pretending to be a machine word.
-/
structure BoundedPayloadWordStore
    (payload : List Bool) (wordSize : Nat) where
  store : PayloadWordStore payload
  word_length_le :
    forall {word : List Bool},
      List.Mem word store.words.toList -> word.length <= wordSize

namespace BoundedPayloadWordStore

def ofChunks
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    BoundedPayloadWordStore payload wordSize where
  store :=
    { words := (chunkPayloadWords wordSize payload).toArray
      erases := by
        simpa using flattenPayloadWords_chunkPayloadWords hword payload }
  word_length_le := by
    intro word hmem
    simpa using chunkPayloadWords_word_length_le wordSize hmem

/--
Chunked payload store with empty sentinel padding.

The sentinel preserves the represented payload but gives boundary-sensitive
word-RAM clients, such as rank at an exact word boundary, concrete empty
words to read after the real chunks.
-/
def ofChunksWithSentinel
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    BoundedPayloadWordStore payload wordSize where
  store :=
    { words :=
        (chunkPayloadWords wordSize payload ++
          List.replicate (payload.length + 1) []).toArray
      erases := by
        rw [flattenPayloadWords_append,
          flattenPayloadWords_chunkPayloadWords hword payload,
          flattenPayloadWords_replicate_nil]
        simp }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (chunkPayloadWords wordSize payload ++
            List.replicate (payload.length + 1) []) := by
      simpa using hmem
    rcases List.mem_append.mp hlist with hchunk | hsentinel
    ·
        exact chunkPayloadWords_word_length_le wordSize hchunk
    ·
        simp at hsentinel
        subst word
        simp

theorem erases
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) :
    flattenPayloadWords store.store.words.toList = payload :=
  store.store.erases

theorem word_length_le_of_mem
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    {word : List Bool}
    (hmem : List.Mem word store.store.words.toList) :
    word.length <= wordSize :=
  store.word_length_le hmem

theorem ofChunks_erases
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    flattenPayloadWords
      ((BoundedPayloadWordStore.ofChunks payload hword).store.words.toList) =
      payload := by
  exact (BoundedPayloadWordStore.ofChunks payload hword).erases

theorem ofChunks_word_length_le
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize)
    {word : List Bool}
    (hmem : List.Mem word
      (BoundedPayloadWordStore.ofChunks payload hword).store.words.toList) :
    word.length <= wordSize :=
  (BoundedPayloadWordStore.ofChunks payload hword).word_length_le hmem

theorem ofChunksWithSentinel_erases
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    flattenPayloadWords
      ((BoundedPayloadWordStore.ofChunksWithSentinel
        payload hword).store.words.toList) =
      payload := by
  exact (BoundedPayloadWordStore.ofChunksWithSentinel payload hword).erases

theorem ofChunksWithSentinel_word_length_le
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize)
    {word : List Bool}
    (hmem : List.Mem word
      (BoundedPayloadWordStore.ofChunksWithSentinel
        payload hword).store.words.toList) :
    word.length <= wordSize :=
  (BoundedPayloadWordStore.ofChunksWithSentinel
    payload hword).word_length_le hmem

end BoundedPayloadWordStore

/--
Fixed-width natural-number table stored inside counted payload words.

`read_exact` is the semantic codec obligation: decoding the stored word at slot
`i` gives the reference entry `entries[i]?`.  Unlike the older
payload-backed wrappers, the query path below reads the payload word itself,
not an arbitrary decoded `IndexedSeq Nat` supplied beside the payload.
-/
structure FixedWidthNatTable (entries : List Nat) (width : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq : payload.length = entries.length * width
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits -> bits.length = width
  read_exact :
    forall i : Nat, (store.words[i]?).map bitsToNatLE = entries[i]?

namespace FixedWidthNatTable

def ofEncodedWords
    (entries : List Nat) (width : Nat) (words : List (List Bool))
    (hentries : words.map bitsToNatLE = entries)
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    FixedWidthNatTable entries width where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length = words.length * width :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * width := by
        rw [<- hentries]
        simp
  word_length_of_get? := by
    intro i bits hget
    have hlist : words[i]? = some bits := by
      simpa [Array.getElem?_toList] using hget
    exact hwidth (List.mem_of_getElem? hlist)
  read_exact := by
    intro i
    have hmap : (words.map bitsToNatLE)[i]? = entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    FixedWidthNatTable entries width :=
  ofEncodedWords entries width (entries.map (natToBitsLE width)) (by
    induction entries with
    | nil =>
        simp
    | cons entry rest ih =>
        have hentry : entry < 2 ^ width :=
          hbound List.mem_cons_self
        have hrest :
            forall {tailEntry : Nat},
              List.Mem tailEntry rest -> tailEntry < 2 ^ width := by
          intro tailEntry hmem
          exact hbound (List.mem_cons_of_mem entry hmem)
        simp [bitsToNatLE_natToBitsLE_of_lt hentry, ih hrest])
    (by
      intro word hmem
      rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
      exact natToBitsLE_length width entry)

def readCosted
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun word? => word?.map bitsToNatLE)
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_one
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, Costed.erase_map, table.read_exact i]

theorem payload_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload.length = entries.length * width :=
  table.payload_length_eq

theorem read_word_length_of_some
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {i : Nat} {word : List Bool}
    (hword : table.store.words[i]? = some word) :
    word.length = width :=
  table.word_length_of_get? hword

theorem profile
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload.length = entries.length * width /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      flattenPayloadWords table.store.words.toList = table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List Nat) (width : Nat) (words : List (List Bool))
    (hentries : words.map bitsToNatLE = entries)
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    (ofEncodedWords entries width words hentries hwidth).payload.length =
        entries.length * width /\
      (forall i,
        ((ofEncodedWords entries width words hentries hwidth).readCosted i).cost <=
            1 /\
          ((ofEncodedWords entries width words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries width words hentries hwidth).store.words.toList =
        (ofEncodedWords entries width words hentries hwidth).payload := by
  exact (ofEncodedWords entries width words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    (ofEntries entries width hbound).payload.length =
        entries.length * width /\
      (forall i,
        ((ofEntries entries width hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries width hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries width hbound).store.words.toList =
        (ofEntries entries width hbound).payload := by
  exact (ofEntries entries width hbound).profile

end FixedWidthNatTable

/-- Decode a fixed-width optional natural number from one payload word. -/
def bitsToOptionNatLE (width : Nat) (bits : List Bool) : Option Nat :=
  match bits with
  | [] => none
  | present :: rest =>
      if present then
        some (bitsToNatLE (rest.take width))
      else
        none

def optionNatWordWidth (width : Nat) : Nat :=
  1 + width

def optionNatToBitsLE (width : Nat) : Option Nat -> List Bool
  | none => false :: List.replicate width false
  | some n => true :: natToBitsLE width n

theorem optionNatToBitsLE_length
    (width : Nat) (entry : Option Nat) :
    (optionNatToBitsLE width entry).length =
      optionNatWordWidth width := by
  cases entry <;>
    simp [optionNatToBitsLE, optionNatWordWidth, natToBitsLE_length,
      Nat.add_comm]

theorem bitsToOptionNatLE_optionNatToBitsLE_of_bound
    {width : Nat} {entry : Option Nat}
    (hbound : forall n : Nat, entry = some n -> n < 2 ^ width) :
    bitsToOptionNatLE width (optionNatToBitsLE width entry) = entry := by
  cases entry with
  | none =>
      simp [optionNatToBitsLE, bitsToOptionNatLE]
  | some n =>
      have hn : n < 2 ^ width := hbound n rfl
      have htake :
          (natToBitsLE width n).take width = natToBitsLE width n := by
        rw [List.take_of_length_le]
        rw [natToBitsLE_length]
        exact Nat.le_refl width
      simp [optionNatToBitsLE, bitsToOptionNatLE,
        htake, bitsToNatLE_natToBitsLE_of_lt hn]

/--
Fixed-width optional natural-number table stored inside counted payload words.

The outer option of `readCosted` is the indexed read; the inner option is the
stored payload value.
-/
structure FixedWidthOptionNatTable
    (entries : List (Option Nat)) (width : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq :
    payload.length = entries.length * optionNatWordWidth width
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits -> bits.length = optionNatWordWidth width
  read_exact :
    forall i : Nat,
      (store.words[i]?).map (bitsToOptionNatLE width) = entries[i]?

namespace FixedWidthOptionNatTable

def ofEncodedWords
    (entries : List (Option Nat)) (width : Nat)
    (words : List (List Bool))
    (hentries : words.map (bitsToOptionNatLE width) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words -> word.length = optionNatWordWidth width) :
    FixedWidthOptionNatTable entries width where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length =
          words.length * optionNatWordWidth width :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * optionNatWordWidth width := by
        rw [<- hentries]
        simp
  word_length_of_get? := by
    intro i bits hget
    have hlist : words[i]? = some bits := by
      simpa [Array.getElem?_toList] using hget
    exact hwidth (List.mem_of_getElem? hlist)
  read_exact := by
    intro i
    have hmap :
        (words.map (bitsToOptionNatLE width))[i]? = entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List (Option Nat)) (width : Nat)
    (hbound :
      forall {entry : Option Nat} {n : Nat},
        List.Mem entry entries -> entry = some n -> n < 2 ^ width) :
    FixedWidthOptionNatTable entries width :=
  ofEncodedWords entries width (entries.map (optionNatToBitsLE width)) (by
    induction entries with
    | nil =>
        simp
    | cons entry rest ih =>
        have hentry :
            bitsToOptionNatLE width (optionNatToBitsLE width entry) =
              entry := by
          exact bitsToOptionNatLE_optionNatToBitsLE_of_bound
            (entry := entry)
            (fun n hsome => hbound List.mem_cons_self hsome)
        have hrest :
            forall {tailEntry : Option Nat} {n : Nat},
              List.Mem tailEntry rest ->
                tailEntry = some n -> n < 2 ^ width := by
          intro tailEntry n hmem hsome
          exact hbound (List.mem_cons_of_mem entry hmem) hsome
        simp [hentry, ih hrest])
    (by
      intro word hmem
      rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
      exact optionNatToBitsLE_length width entry)

def readCosted
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    Costed (Option (Option Nat)) :=
  Costed.map (fun word? => word?.map (bitsToOptionNatLE width))
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_one
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, Costed.erase_map, table.read_exact i]

theorem payload_length
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    table.payload.length = entries.length * optionNatWordWidth width :=
  table.payload_length_eq

theorem profile
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    table.payload.length = entries.length * optionNatWordWidth width /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      flattenPayloadWords table.store.words.toList = table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List (Option Nat)) (width : Nat)
    (words : List (List Bool))
    (hentries : words.map (bitsToOptionNatLE width) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words -> word.length = optionNatWordWidth width) :
    (ofEncodedWords entries width words hentries hwidth).payload.length =
        entries.length * optionNatWordWidth width /\
      (forall i,
        ((ofEncodedWords entries width words hentries hwidth).readCosted i).cost <=
            1 /\
          ((ofEncodedWords entries width words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries width words hentries hwidth).store.words.toList =
        (ofEncodedWords entries width words hentries hwidth).payload := by
  exact (ofEncodedWords entries width words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List (Option Nat)) (width : Nat)
    (hbound :
      forall {entry : Option Nat} {n : Nat},
        List.Mem entry entries -> entry = some n -> n < 2 ^ width) :
    (ofEntries entries width hbound).payload.length =
        entries.length * optionNatWordWidth width /\
      (forall i,
        ((ofEntries entries width hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries width hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries width hbound).store.words.toList =
        (ofEntries entries width hbound).payload := by
  exact (ofEntries entries width hbound).profile

end FixedWidthOptionNatTable

/--
Payload-live true/false rank-sample tables.

This is the small codec layer that the final succinct rank directory should
consume: each sample query reads one fixed-width word from the counted payload
for the requested bit value.  It deliberately does not claim that these tables
are `o(n)`; full-precision sample arrays are a fidelity layer, not the final
succinct directory.
-/
structure FixedWidthRankSampleTables
    (trueEntries falseEntries : List Nat) (width : Nat) where
  trueTable : FixedWidthNatTable trueEntries width
  falseTable : FixedWidthNatTable falseEntries width

namespace FixedWidthRankSampleTables

def ofEncodedWords
    (trueEntries falseEntries : List Nat) (width : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue : trueWords.map bitsToNatLE = trueEntries)
    (hfalse : falseWords.map bitsToNatLE = falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords -> word.length = width)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords -> word.length = width) :
    FixedWidthRankSampleTables trueEntries falseEntries width where
  trueTable :=
    FixedWidthNatTable.ofEncodedWords
      trueEntries width trueWords htrue htrueWidth
  falseTable :=
    FixedWidthNatTable.ofEncodedWords
      falseEntries width falseWords hfalse hfalseWidth

def ofEntries
    (trueEntries falseEntries : List Nat) (width : Nat)
    (htrue :
      forall {entry : Nat}, List.Mem entry trueEntries -> entry < 2 ^ width)
    (hfalse :
      forall {entry : Nat}, List.Mem entry falseEntries -> entry < 2 ^ width) :
    FixedWidthRankSampleTables trueEntries falseEntries width where
  trueTable := FixedWidthNatTable.ofEntries trueEntries width htrue
  falseTable := FixedWidthNatTable.ofEntries falseEntries width hfalse

def payload
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    List Bool :=
  tables.trueTable.payload ++ tables.falseTable.payload

def entries
    {trueEntries falseEntries : List Nat} {width : Nat}
    (_tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) : List Nat :=
  match target with
  | true => trueEntries
  | false => falseEntries

def sampleCosted
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) : Costed (Option Nat) :=
  match target with
  | true => tables.trueTable.readCosted i
  | false => tables.falseTable.readCosted i

@[simp] theorem sampleCosted_cost
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost = 1 := by
  cases target <;> simp [sampleCosted]

theorem sampleCosted_cost_le_one
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost <= 1 := by
  simp

@[simp] theorem sampleCosted_erase
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).erase =
      (tables.entries target)[i]? := by
  cases target <;> simp [sampleCosted, entries]

theorem payload_length
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    tables.payload.length =
      trueEntries.length * width + falseEntries.length * width := by
  simp [payload, tables.trueTable.payload_length,
    tables.falseTable.payload_length]

theorem profile
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    tables.payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        (tables.sampleCosted target i).cost <= 1 /\
          (tables.sampleCosted target i).erase =
            (tables.entries target)[i]? := by
  constructor
  · exact tables.payload_length
  · intro target i
    exact ⟨tables.sampleCosted_cost_le_one target i,
      tables.sampleCosted_erase target i⟩

theorem ofEncodedWords_profile
    (trueEntries falseEntries : List Nat) (width : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue : trueWords.map bitsToNatLE = trueEntries)
    (hfalse : falseWords.map bitsToNatLE = falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords -> word.length = width)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords -> word.length = width) :
    (ofEncodedWords trueEntries falseEntries width trueWords falseWords
        htrue hfalse htrueWidth hfalseWidth).payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted target i).cost <=
            1 /\
          ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).erase =
            ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
              htrue hfalse htrueWidth hfalseWidth).entries target)[i]? := by
  exact
    (ofEncodedWords trueEntries falseEntries width trueWords falseWords
      htrue hfalse htrueWidth hfalseWidth).profile

theorem ofEntries_profile
    (trueEntries falseEntries : List Nat) (width : Nat)
    (htrue :
      forall {entry : Nat}, List.Mem entry trueEntries -> entry < 2 ^ width)
    (hfalse :
      forall {entry : Nat}, List.Mem entry falseEntries -> entry < 2 ^ width) :
    (ofEntries trueEntries falseEntries width htrue hfalse).payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        ((ofEntries trueEntries falseEntries width htrue hfalse).sampleCosted
            target i).cost <= 1 /\
          ((ofEntries trueEntries falseEntries width htrue hfalse).sampleCosted
              target i).erase =
            ((ofEntries trueEntries falseEntries width htrue hfalse).entries
              target)[i]? := by
  exact (ofEntries trueEntries falseEntries width htrue hfalse).profile

end FixedWidthRankSampleTables

/--
Payload-live stored-word rank data.

The bitvector itself is stored as counted payload words erasing to `bits`, while
the true/false prefix samples are stored in fixed-width auxiliary payload
tables.  The query path reads exactly those stores and then invokes one
word-level rank primitive; the correctness fields state the usual sampled-rank
decomposition against the reference `Succinct.rankPrefix`.
-/
structure PayloadLiveStoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  sampleWidth : Nat
  trueEntries : List Nat
  falseEntries : List Nat
  samples : FixedWidthRankSampleTables trueEntries falseEntries sampleWidth
  bitWords : PayloadWordStore bits
  aux_length_eq : samples.payload.length = overhead
  sample_present :
    forall target pos,
      pos <= bits.length ->
        exists sample, (samples.entries target)[pos / wordSize]? = some sample
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, bitWords.words[pos / wordSize]? = some word
  rank_parts_exact :
    forall target pos sample word,
      pos <= bits.length ->
        (samples.entries target)[pos / wordSize]? = some sample ->
        bitWords.words[pos / wordSize]? = some word ->
          sample +
              RAM.boolRankPrefix target word
                (pos - (pos / wordSize) * wordSize) =
            Succinct.rankPrefix target bits pos

namespace PayloadLiveStoredWordRankData

def wordIndex
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  pos / data.wordSize

def wordStart
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  data.wordIndex pos * data.wordSize

def wordOffset
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) (pos : Nat) :
    Nat :=
  pos - data.wordStart pos

def auxPayload
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) : List Bool :=
  data.samples.payload

def rankCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind (data.samples.sampleCosted target (data.wordIndex pos))
    fun sample? =>
      Costed.bind (data.bitWords.readWordCosted (data.wordIndex pos))
        fun word? =>
          match sample?, word? with
          | some sample, some word =>
              Costed.map (fun localRank => sample + localRank)
                (RAM.rankBoolWordPrefix target word
                  (data.wordOffset pos)).toCosted
          | _, _ => Costed.pure 0

def rankCostedClamped
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  data.rankCosted target (Nat.min pos bits.length)

theorem auxPayload_length
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) :
    data.auxPayload.length = overhead := by
  exact data.aux_length_eq

theorem rankCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= 3 := by
  unfold rankCosted
  cases hsample :
      (data.samples.sampleCosted target (data.wordIndex pos)).value with
  | none =>
      cases hword :
          (data.bitWords.readWordCosted (data.wordIndex pos)).value with
      | none =>
          simp [Costed.bind, Costed.pure, hsample, hword]
      | some word =>
          simp [Costed.bind, Costed.pure, hsample, hword]
  | some sample =>
      cases hword :
          (data.bitWords.readWordCosted (data.wordIndex pos)).value with
      | none =>
          simp [Costed.bind, Costed.pure, hsample, hword]
      | some word =>
          simp [Costed.bind, Costed.map, Costed.pure, hsample, hword]

theorem rankCostedClamped_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).cost <= 3 := by
  exact data.rankCosted_cost_le_three target (Nat.min pos bits.length)

theorem rankCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rcases data.sample_present target pos hpos with ⟨sample, hsample⟩
  rcases data.word_present pos hpos with ⟨word, hword⟩
  have hsampleValue :
      (data.samples.sampleCosted target (data.wordIndex pos)).value =
        some sample := by
    have h :=
      data.samples.sampleCosted_erase target (data.wordIndex pos)
    simpa [Costed.erase, wordIndex, hsample] using h
  have hwordValue :
      (data.bitWords.readWordCosted (data.wordIndex pos)).value =
        some word := by
    have h :=
      data.bitWords.readWordCosted_erase (data.wordIndex pos)
    simpa [Costed.erase, wordIndex, hword] using h
  have hsum :
      sample +
          RAM.boolRankPrefix target word (data.wordOffset pos) =
        Succinct.rankPrefix target bits pos := by
    simpa [wordOffset, wordStart, wordIndex] using
      data.rank_parts_exact target pos sample word hpos hsample hword
  unfold rankCosted
  simp [Costed.bind, Costed.map, Costed.pure, Costed.erase,
    hsampleValue, hwordValue, hsum]

theorem rankCostedClamped_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCostedClamped
  have hmin : Nat.min pos bits.length <= bits.length :=
    Nat.min_le_right pos bits.length
  calc
    (data.rankCosted target (Nat.min pos bits.length)).erase =
        Succinct.rankPrefix target bits (Nat.min pos bits.length) := by
      exact data.rankCosted_exact target hmin
    _ = Succinct.rankPrefix target bits pos := by
      exact Succinct.rankPrefix_min_length_eq target bits pos

theorem profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      (forall target pos,
        (data.rankCostedClamped target pos).cost <= 3 /\
          (data.rankCostedClamped target pos).erase =
            Succinct.rankPrefix target bits pos) := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target pos
      exact ⟨data.rankCostedClamped_cost_le_three target pos,
        data.rankCostedClamped_exact target pos⟩

end PayloadLiveStoredWordRankData

/--
Certified rank/select directory over a fixed bitvector.

The reference semantics remain `Succinct.rankPrefix` and `Succinct.select`.
The `encodeAux` length is counted separately from the payload bits themselves,
and the costed queries must refine the reference operations at a uniform
`queryCost` bound.  This is the rank/select component slot used by the
componentized balanced-parentheses RMQ space profile below.
-/
structure RankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  Aux : Type
  buildAux : Aux
  encodeAux : Aux -> List Bool
  rankCosted : Aux -> Bool -> Nat -> Costed Nat
  selectCosted : Aux -> Bool -> Nat -> Costed (Option Nat)
  aux_length_eq : (encodeAux buildAux).length = overhead
  rank_cost_le :
    forall target pos, (rankCosted buildAux target pos).cost <= queryCost
  select_cost_le :
    forall target occurrence,
      (selectCosted buildAux target occurrence).cost <= queryCost
  rank_exact :
    forall target pos,
      (rankCosted buildAux target pos).erase =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall target occurrence,
      (selectCosted buildAux target occurrence).erase =
        Succinct.select target bits occurrence

namespace RankSelectDirectory

def auxPayload
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost) :
    List Bool :=
  directory.encodeAux directory.buildAux

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost) :
    directory.auxPayload.length = overhead := by
  exact directory.aux_length_eq

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted directory.buildAux target pos

def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.selectCosted directory.buildAux target occurrence

theorem rankQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).cost <= queryCost := by
  exact directory.rank_cost_le target pos

theorem selectQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).cost <= queryCost := by
  exact directory.select_cost_le target occurrence

@[simp] theorem rankQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  exact directory.rank_exact target pos

@[simp] theorem selectQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : RankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  exact directory.select_exact target occurrence

end RankSelectDirectory

/--
Family-level rank/select component: every bitvector gets a certified directory
whose auxiliary payload is `o(n)` and whose query bound is one fixed constant.
-/
structure RankSelectFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      RankSelectDirectory bits (overhead bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace RankSelectFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : RankSelectFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length = overhead bits.length) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted target occurrence).cost <=
                queryCost /\
              ((family.directory bits).selectQueryCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    constructor
    · exact (family.directory bits).auxPayload_length
    · constructor
      · intro target pos
        exact ⟨(family.directory bits).rankQueryCosted_cost_le target pos,
          (family.directory bits).rankQueryCosted_erase target pos⟩
      · intro target occurrence
        exact ⟨(family.directory bits).selectQueryCosted_cost_le target occurrence,
          (family.directory bits).selectQueryCosted_erase target occurrence⟩

end RankSelectFamily

def rankSampleSeqOf
    (target : Bool)
    (trueSamples falseSamples : TableModel.IndexedSeq Nat) :
    TableModel.IndexedSeq Nat :=
  match target with
  | true => trueSamples
  | false => falseSamples

/--
Stored data needed for a faithful bounded rank query.

The query path reads one sampled prefix rank, reads one payload word, and then
uses the RAM word-rank primitive inside that word.  The fields below certify
that those stored objects correspond to the reference bitstring; they do not
let the query compute `rankPrefix` directly.
-/
structure StoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  words : TableModel.IndexedSeq (List Bool)
  trueSamples : TableModel.IndexedSeq Nat
  falseSamples : TableModel.IndexedSeq Nat
  encodeAux : List Bool
  aux_length_eq : encodeAux.length = overhead
  sample_present :
    forall target pos,
      pos <= bits.length ->
        exists sample,
          (rankSampleSeqOf target trueSamples falseSamples).get?
            (pos / wordSize) = some sample
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, words.get? (pos / wordSize) = some word
  rank_parts_exact :
    forall target pos sample word,
      pos <= bits.length ->
        (rankSampleSeqOf target trueSamples falseSamples).get?
            (pos / wordSize) = some sample ->
        words.get? (pos / wordSize) = some word ->
          sample +
              RAM.boolRankPrefix target word
                (pos - (pos / wordSize) * wordSize) =
            Succinct.rankPrefix target bits pos

namespace StoredWordRankData

def sampleSeq
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (target : Bool) :
    TableModel.IndexedSeq Nat :=
  rankSampleSeqOf target data.trueSamples data.falseSamples

def wordIndex
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  pos / data.wordSize

def wordStart
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  data.wordIndex pos * data.wordSize

def wordOffset
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) (pos : Nat) : Nat :=
  pos - data.wordStart pos

def rankCosted
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind ((data.sampleSeq target).getCosted (data.wordIndex pos))
    fun sample? =>
      Costed.bind (data.words.getCosted (data.wordIndex pos)) fun word? =>
        match sample?, word? with
        | some sample, some word =>
            Costed.map (fun localRank => sample + localRank)
              (RAM.rankBoolWordPrefix target word
                (data.wordOffset pos)).toCosted
        | _, _ => Costed.pure 0

/--
Total rank query adapter.

The stored-word data is exact on valid prefix positions.  For a total
rank/select directory we clamp out-of-range positions to `bits.length`, using
the fact that prefix rank saturates once the whole bitvector has been counted.
-/
def rankCostedClamped
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  data.rankCosted target (Nat.min pos bits.length)

theorem rankCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= 3 := by
  unfold rankCosted sampleSeq wordIndex wordOffset wordStart
  cases hsample :
      (rankSampleSeqOf target data.trueSamples data.falseSamples).get?
        (pos / data.wordSize) with
  | none =>
      cases hword : data.words.get? (pos / data.wordSize) with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some word =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
  | some sample =>
      cases hword : data.words.get? (pos / data.wordSize) with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some word =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hsample, hword,
            Costed.bind, Costed.map, Costed.pure,
            TableModel.indexedReadCost]

theorem rankCostedClamped_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).cost <= 3 := by
  exact data.rankCosted_cost_le_three target (Nat.min pos bits.length)

theorem rankCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  rcases data.sample_present target pos hpos with ⟨sample, hsample⟩
  rcases data.word_present pos hpos with ⟨word, hword⟩
  have hsum :=
    data.rank_parts_exact target pos sample word hpos hsample hword
  have hsum' :
      sample +
          RAM.boolRankPrefix target word
            (pos - data.wordStart pos) =
        Succinct.rankPrefix target bits pos := by
    simpa [wordStart, wordIndex] using hsum
  unfold rankCosted sampleSeq wordIndex wordOffset
  simp [TableModel.IndexedSeq.getCosted,
    TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
    hsample, hword, Costed.bind, Costed.map, Costed.pure, hsum']

theorem rankCostedClamped_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    (data.rankCostedClamped target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCostedClamped
  have hmin : Nat.min pos bits.length <= bits.length :=
    Nat.min_le_right pos bits.length
  calc
    (data.rankCosted target (Nat.min pos bits.length)).erase =
        Succinct.rankPrefix target bits (Nat.min pos bits.length) := by
      exact data.rankCosted_exact target hmin
    _ = Succinct.rankPrefix target bits pos := by
      exact Succinct.rankPrefix_min_length_eq target bits pos

theorem rankCosted_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    data.encodeAux.length = overhead /\
      forall target pos,
        (data.rankCosted target pos).cost <= 3 /\
          (pos <= bits.length ->
            (data.rankCosted target pos).erase =
              Succinct.rankPrefix target bits pos) := by
  constructor
  · exact data.aux_length_eq
  · intro target pos
    exact ⟨data.rankCosted_cost_le_three target pos,
      fun hpos => data.rankCosted_exact target hpos⟩

end StoredWordRankData

/-- Stored locator for a word-level select query. -/
structure StoredWordSelectSample where
  wordIndex : Nat
  wordStart : Nat
  rankBefore : Nat

def selectSampleSeqOf
    (target : Bool)
    (trueSamples falseSamples :
      TableModel.IndexedSeq (Option StoredWordSelectSample)) :
    TableModel.IndexedSeq (Option StoredWordSelectSample) :=
  match target with
  | true => trueSamples
  | false => falseSamples

/--
Decode one fixed-width select locator word.

The first bit is a presence bit.  When present, the remaining payload is split
into three little-endian fields of width `fieldWidth`: `wordIndex`,
`wordStart`, and `rankBefore`.
-/
def bitsToStoredWordSelectSample
    (fieldWidth : Nat) (bits : List Bool) :
    Option StoredWordSelectSample :=
  match bits with
  | [] => none
  | present :: rest =>
      if present then
        some
          { wordIndex := bitsToNatLE (rest.take fieldWidth)
            wordStart := bitsToNatLE ((rest.drop fieldWidth).take fieldWidth)
            rankBefore :=
              bitsToNatLE ((rest.drop (2 * fieldWidth)).take fieldWidth) }
      else
        none

def selectSampleWordWidth (fieldWidth : Nat) : Nat :=
  1 + 3 * fieldWidth

def storedWordSelectSampleToBitsLE
    (fieldWidth : Nat) (sample : StoredWordSelectSample) :
    List Bool :=
  natToBitsLE fieldWidth sample.wordIndex ++
    natToBitsLE fieldWidth sample.wordStart ++
      natToBitsLE fieldWidth sample.rankBefore

theorem storedWordSelectSampleToBitsLE_length
    (fieldWidth : Nat) (sample : StoredWordSelectSample) :
    (storedWordSelectSampleToBitsLE fieldWidth sample).length =
      3 * fieldWidth := by
  simp [storedWordSelectSampleToBitsLE, natToBitsLE_length]
  omega

def optionStoredWordSelectSampleToBitsLE
    (fieldWidth : Nat) : Option StoredWordSelectSample -> List Bool
  | none => false :: List.replicate (3 * fieldWidth) false
  | some sample => true :: storedWordSelectSampleToBitsLE fieldWidth sample

theorem optionStoredWordSelectSampleToBitsLE_length
    (fieldWidth : Nat) (entry : Option StoredWordSelectSample) :
    (optionStoredWordSelectSampleToBitsLE fieldWidth entry).length =
      selectSampleWordWidth fieldWidth := by
  cases entry with
  | none =>
      simp [optionStoredWordSelectSampleToBitsLE, selectSampleWordWidth]
      omega
  | some sample =>
      simp [optionStoredWordSelectSampleToBitsLE, selectSampleWordWidth,
        storedWordSelectSampleToBitsLE_length]
      omega

theorem bitsToStoredWordSelectSample_optionToBits_of_bound
    {fieldWidth : Nat} {entry : Option StoredWordSelectSample}
    (hbound :
      forall sample : StoredWordSelectSample,
        entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    bitsToStoredWordSelectSample fieldWidth
        (optionStoredWordSelectSampleToBitsLE fieldWidth entry) =
      entry := by
  cases entry with
  | none =>
      simp [optionStoredWordSelectSampleToBitsLE,
        bitsToStoredWordSelectSample]
  | some sample =>
      rcases hbound sample rfl with ⟨hwordIndex, hwordStart, hrankBefore⟩
      let wordIndexBits := natToBitsLE fieldWidth sample.wordIndex
      let wordStartBits := natToBitsLE fieldWidth sample.wordStart
      let rankBeforeBits := natToBitsLE fieldWidth sample.rankBefore
      have hwordIndexLen : wordIndexBits.length = fieldWidth := by
        simp [wordIndexBits, natToBitsLE_length]
      have hwordStartLen : wordStartBits.length = fieldWidth := by
        simp [wordStartBits, natToBitsLE_length]
      have hrankBeforeLen : rankBeforeBits.length = fieldWidth := by
        simp [rankBeforeBits, natToBitsLE_length]
      have htakeWordIndex :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).take
              fieldWidth =
            wordIndexBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).take
              fieldWidth =
              (wordIndexBits ++ (wordStartBits ++ rankBeforeBits)).take
                wordIndexBits.length := by
            rw [hwordIndexLen]
            simp [List.append_assoc]
          _ = wordIndexBits := by
            rw [List.take_append_of_le_length (Nat.le_refl _)]
            rw [List.take_of_length_le (Nat.le_refl _)]
      have hdropWordIndex :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth =
            wordStartBits ++ rankBeforeBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth =
              (wordIndexBits ++ (wordStartBits ++ rankBeforeBits)).drop
                wordIndexBits.length := by
            rw [hwordIndexLen]
            simp [List.append_assoc]
          _ = wordStartBits ++ rankBeforeBits := by
            rw [List.drop_append_of_le_length (Nat.le_refl _)]
            rw [List.drop_of_length_le (Nat.le_refl _)]
            simp
      have htakeWordStart :
          ((wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth).take fieldWidth =
            wordStartBits := by
        rw [hdropWordIndex]
        calc
          (wordStartBits ++ rankBeforeBits).take fieldWidth =
              (wordStartBits ++ rankBeforeBits).take wordStartBits.length := by
            rw [hwordStartLen]
          _ = wordStartBits := by
            rw [List.take_append_of_le_length (Nat.le_refl _)]
            rw [List.take_of_length_le (Nat.le_refl _)]
      have hdropTwo :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth) =
            rankBeforeBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth) =
              ((wordIndexBits ++ wordStartBits) ++ rankBeforeBits).drop
                (wordIndexBits ++ wordStartBits).length := by
            have hlen :
                (wordIndexBits ++ wordStartBits).length =
                  2 * fieldWidth := by
              simp [hwordIndexLen, hwordStartLen]
              omega
            rw [hlen]
          _ = rankBeforeBits := by
            rw [List.drop_append_of_le_length (Nat.le_refl _)]
            rw [List.drop_of_length_le (Nat.le_refl _)]
            simp
      have htakeRankBefore :
          ((wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth)).take fieldWidth =
            rankBeforeBits := by
        rw [hdropTwo]
        rw [List.take_of_length_le]
        rw [hrankBeforeLen]
        exact Nat.le_refl fieldWidth
      have htakeWordIndexRaw :
          (natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).take
              fieldWidth =
            natToBitsLE fieldWidth sample.wordIndex := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeWordIndex
      have htakeWordStartRaw :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).drop
              fieldWidth).take fieldWidth =
            natToBitsLE fieldWidth sample.wordStart := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeWordStart
      have htakeRankBeforeRaw :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).drop
              (2 * fieldWidth)).take fieldWidth =
            natToBitsLE fieldWidth sample.rankBefore := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeRankBefore
      have htakeWordIndexRight :
          (natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).take
              fieldWidth =
            natToBitsLE fieldWidth sample.wordIndex := by
        simpa [List.append_assoc] using htakeWordIndexRaw
      have htakeWordStartRight :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).drop
              fieldWidth).take fieldWidth =
            natToBitsLE fieldWidth sample.wordStart := by
        simpa [List.append_assoc] using htakeWordStartRaw
      have htakeRankBeforeRight :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).drop
              (2 * fieldWidth)).take fieldWidth =
            natToBitsLE fieldWidth sample.rankBefore := by
        simpa [List.append_assoc] using htakeRankBeforeRaw
      simp [optionStoredWordSelectSampleToBitsLE,
        storedWordSelectSampleToBitsLE, bitsToStoredWordSelectSample]
      rw [htakeWordIndexRight, htakeWordStartRight, htakeRankBeforeRight]
      simp [bitsToNatLE_natToBitsLE_of_lt hwordIndex,
        bitsToNatLE_natToBitsLE_of_lt hwordStart,
        bitsToNatLE_natToBitsLE_of_lt hrankBefore]

/--
Payload-live fixed-width table of optional select locators.

Outer `none` is an out-of-table read; `some none` is a stored certificate that
the requested occurrence is absent.
-/
structure FixedWidthSelectSampleTable
    (entries : List (Option StoredWordSelectSample)) (fieldWidth : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq :
    payload.length = entries.length * selectSampleWordWidth fieldWidth
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits ->
        bits.length = selectSampleWordWidth fieldWidth
  read_exact :
    forall i : Nat,
      (store.words[i]?).map (bitsToStoredWordSelectSample fieldWidth) =
        entries[i]?

namespace FixedWidthSelectSampleTable

def ofEncodedWords
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToStoredWordSelectSample fieldWidth) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length = selectSampleWordWidth fieldWidth) :
    FixedWidthSelectSampleTable entries fieldWidth where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length =
          words.length * selectSampleWordWidth fieldWidth :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * selectSampleWordWidth fieldWidth := by
        rw [<- hentries]
        simp
  word_length_of_get? := by
    intro i bits hget
    have hlist : words[i]? = some bits := by
      simpa [Array.getElem?_toList] using hget
    exact hwidth (List.mem_of_getElem? hlist)
  read_exact := by
    intro i
    have hmap :
        (words.map (bitsToStoredWordSelectSample fieldWidth))[i]? =
          entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (hbound :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry entries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    FixedWidthSelectSampleTable entries fieldWidth :=
  ofEncodedWords entries fieldWidth
    (entries.map (optionStoredWordSelectSampleToBitsLE fieldWidth)) (by
      induction entries with
      | nil =>
          simp
      | cons entry rest ih =>
          have hentry :
              bitsToStoredWordSelectSample fieldWidth
                  (optionStoredWordSelectSampleToBitsLE fieldWidth entry) =
                entry := by
            exact bitsToStoredWordSelectSample_optionToBits_of_bound
              (entry := entry)
              (fun sample hsome => hbound List.mem_cons_self hsome)
          have hrest :
              forall {tailEntry : Option StoredWordSelectSample}
                  {sample : StoredWordSelectSample},
                List.Mem tailEntry rest ->
                  tailEntry = some sample ->
                    sample.wordIndex < 2 ^ fieldWidth /\
                      sample.wordStart < 2 ^ fieldWidth /\
                        sample.rankBefore < 2 ^ fieldWidth := by
            intro tailEntry sample hmem hsome
            exact hbound (List.mem_cons_of_mem entry hmem) hsome
          simp [hentry, ih hrest])
      (by
        intro word hmem
        rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
        exact optionStoredWordSelectSampleToBitsLE_length fieldWidth entry)

def readCosted
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  Costed.map
    (fun word? => word?.map (bitsToStoredWordSelectSample fieldWidth))
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_one
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, Costed.erase_map, table.read_exact i]

theorem payload_length
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    table.payload.length =
      entries.length * selectSampleWordWidth fieldWidth :=
  table.payload_length_eq

theorem profile
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    table.payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      flattenPayloadWords table.store.words.toList = table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToStoredWordSelectSample fieldWidth) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length = selectSampleWordWidth fieldWidth) :
    (ofEncodedWords entries fieldWidth words hentries hwidth).payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      (forall i,
        ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
            i).cost <= 1 /\
          ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries fieldWidth words hentries hwidth).store.words.toList =
        (ofEncodedWords entries fieldWidth words hentries hwidth).payload := by
  exact (ofEncodedWords entries fieldWidth words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (hbound :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry entries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    (ofEntries entries fieldWidth hbound).payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      (forall i,
        ((ofEntries entries fieldWidth hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries fieldWidth hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries fieldWidth hbound).store.words.toList =
        (ofEntries entries fieldWidth hbound).payload := by
  exact (ofEntries entries fieldWidth hbound).profile

end FixedWidthSelectSampleTable

/-- Payload-live true/false select-locator tables. -/
structure FixedWidthSelectSampleTables
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) where
  trueTable : FixedWidthSelectSampleTable trueEntries fieldWidth
  falseTable : FixedWidthSelectSampleTable falseEntries fieldWidth

namespace FixedWidthSelectSampleTables

def ofEncodedWords
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue :
      trueWords.map (bitsToStoredWordSelectSample fieldWidth) = trueEntries)
    (hfalse :
      falseWords.map (bitsToStoredWordSelectSample fieldWidth) =
        falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords ->
          word.length = selectSampleWordWidth fieldWidth)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords ->
          word.length = selectSampleWordWidth fieldWidth) :
    FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth where
  trueTable :=
    FixedWidthSelectSampleTable.ofEncodedWords
      trueEntries fieldWidth trueWords htrue htrueWidth
  falseTable :=
    FixedWidthSelectSampleTable.ofEncodedWords
      falseEntries fieldWidth falseWords hfalse hfalseWidth

def ofEntries
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (htrue :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry trueEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth)
    (hfalse :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry falseEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth where
  trueTable :=
    FixedWidthSelectSampleTable.ofEntries
      trueEntries fieldWidth htrue
  falseTable :=
    FixedWidthSelectSampleTable.ofEntries
      falseEntries fieldWidth hfalse

def payload
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    List Bool :=
  tables.trueTable.payload ++ tables.falseTable.payload

def entries
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (_tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) : List (Option StoredWordSelectSample) :=
  match target with
  | true => trueEntries
  | false => falseEntries

def sampleCosted
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  match target with
  | true => tables.trueTable.readCosted i
  | false => tables.falseTable.readCosted i

@[simp] theorem sampleCosted_cost
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost = 1 := by
  cases target <;> simp [sampleCosted]

theorem sampleCosted_cost_le_one
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost <= 1 := by
  simp

@[simp] theorem sampleCosted_erase
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).erase =
      (tables.entries target)[i]? := by
  cases target <;> simp [sampleCosted, entries]

theorem payload_length
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    tables.payload.length =
      trueEntries.length * selectSampleWordWidth fieldWidth +
        falseEntries.length * selectSampleWordWidth fieldWidth := by
  simp [payload, tables.trueTable.payload_length,
    tables.falseTable.payload_length]

theorem profile
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    tables.payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        (tables.sampleCosted target i).cost <= 1 /\
          (tables.sampleCosted target i).erase =
            (tables.entries target)[i]? := by
  constructor
  · exact tables.payload_length
  · intro target i
    exact ⟨tables.sampleCosted_cost_le_one target i,
      tables.sampleCosted_erase target i⟩

theorem ofEncodedWords_profile
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue :
      trueWords.map (bitsToStoredWordSelectSample fieldWidth) = trueEntries)
    (hfalse :
      falseWords.map (bitsToStoredWordSelectSample fieldWidth) =
        falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords ->
          word.length = selectSampleWordWidth fieldWidth)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords ->
          word.length = selectSampleWordWidth fieldWidth) :
    (ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
        htrue hfalse htrueWidth hfalseWidth).payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).cost <= 1 /\
          ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).erase =
            ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords
              falseWords htrue hfalse htrueWidth hfalseWidth).entries
                target)[i]? := by
  exact
    (ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
      htrue hfalse htrueWidth hfalseWidth).profile

theorem ofEntries_profile
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (htrue :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry trueEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth)
    (hfalse :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry falseEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    (ofEntries trueEntries falseEntries fieldWidth htrue hfalse).payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).sampleCosted
            target i).cost <= 1 /\
          ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).sampleCosted
              target i).erase =
            ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).entries
              target)[i]? := by
  exact (ofEntries trueEntries falseEntries fieldWidth htrue hfalse).profile

end FixedWidthSelectSampleTables

/--
Payload-live stored-word select data.

Locator reads come from fixed-width payload words; payload-bit reads come from
the bitvector word store; the final in-word selection is the typed word-RAM
primitive.  This closes the same proof-only table gap for select that
`PayloadLiveStoredWordRankData` closes for rank.
-/
structure PayloadLiveStoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  fieldWidth : Nat
  trueEntries : List (Option StoredWordSelectSample)
  falseEntries : List (Option StoredWordSelectSample)
  samples : FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth
  bitWords : PayloadWordStore bits
  aux_length_eq : samples.payload.length = overhead
  sample_entry_present :
    forall (target : Bool) (occurrence : Nat),
      exists entry, (samples.entries target)[occurrence]? = some entry
  word_present_of_sample :
    forall (target : Bool) (occurrence : Nat)
        (sample : StoredWordSelectSample),
      (samples.entries target)[occurrence]? = some (some sample) ->
        exists word, bitWords.words[sample.wordIndex]? = some word
  select_some_exact :
    forall (target : Bool) (occurrence : Nat)
        (sample : StoredWordSelectSample) (word : List Bool),
      (samples.entries target)[occurrence]? = some (some sample) ->
        bitWords.words[sample.wordIndex]? = some word ->
          (RAM.boolSelectInWord target word
              (occurrence - sample.rankBefore)).map
              (fun offset => sample.wordStart + offset) =
            Succinct.select target bits occurrence
  select_none_exact :
    forall (target : Bool) (occurrence : Nat),
      (samples.entries target)[occurrence]? =
          some (none : Option StoredWordSelectSample) ->
        Succinct.select target bits occurrence = none

namespace PayloadLiveStoredWordSelectData

def auxPayload
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) : List Bool :=
  data.samples.payload

def selectCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind (data.samples.sampleCosted target occurrence)
    fun entry? =>
      match entry? with
      | none => Costed.pure none
      | some none => Costed.pure none
      | some (some sample) =>
          Costed.bind
            (data.bitWords.readWordCosted sample.wordIndex)
            fun word? =>
              match word? with
              | none => Costed.pure none
              | some word =>
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => sample.wordStart + offset)
                    (RAM.selectBoolWord target word
                      (occurrence - sample.rankBefore)).toCosted

theorem auxPayload_length
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) :
    data.auxPayload.length = overhead :=
  data.aux_length_eq

theorem selectCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 3 := by
  unfold selectCosted
  cases hentry :
      (data.samples.sampleCosted target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hentry]
  | some entry =>
      cases entry with
      | none =>
          simp [Costed.bind, Costed.pure, hentry]
      | some sample =>
          cases hword :
              (data.bitWords.readWordCosted sample.wordIndex).value with
          | none =>
              simp [Costed.bind, Costed.pure, hentry, hword]
          | some word =>
              simp [Costed.bind, Costed.map, Costed.pure, hentry, hword]

theorem selectCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  rcases data.sample_entry_present target occurrence with ⟨entry, hentry⟩
  have hentryValue :
      (data.samples.sampleCosted target occurrence).value =
        some entry := by
    have h := data.samples.sampleCosted_erase target occurrence
    simpa [Costed.erase, hentry] using h
  cases entry with
  | none =>
      have hnone := data.select_none_exact target occurrence hentry
      unfold selectCosted
      simp [Costed.bind, Costed.pure, Costed.erase, hentryValue, hnone]
  | some sample =>
      rcases data.word_present_of_sample target occurrence sample hentry with
        ⟨word, hword⟩
      have hwordValue :
          (data.bitWords.readWordCosted sample.wordIndex).value =
            some word := by
        have h := data.bitWords.readWordCosted_erase sample.wordIndex
        simpa [Costed.erase, hword] using h
      have hexact :=
        data.select_some_exact target occurrence sample word hentry hword
      unfold selectCosted
      simp [Costed.bind, Costed.map, Costed.pure, Costed.erase,
        hentryValue, hwordValue, hexact]

theorem profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= 3 /\
          (data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target occurrence
      exact ⟨data.selectCosted_cost_le_three target occurrence,
        data.selectCosted_exact target occurrence⟩

end PayloadLiveStoredWordSelectData

/--
Combined rank/select directory whose rank and select components both read from
payload-live stores.

This is still a component boundary, not the final asymptotic instantiation: the
caller must supply compressed sample/locator tables and prove their overhead.
The query path itself is no longer allowed to read arbitrary decoded tables.
-/
def RankSelectDirectory.ofPayloadLiveRankSelectData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.auxPayload
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.auxPayload_length]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofPayloadLiveRankSelectData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofPayloadLiveRankSelectData
        rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).rankQueryCosted target pos).cost <= 3 /\
          ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).selectQueryCosted target occurrence).cost <=
              3 /\
          ((RankSelectDirectory.ofPayloadLiveRankSelectData
            rankData selectData).selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact
      (RankSelectDirectory.ofPayloadLiveRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/-- Family of payload-live stored-word rank/select components. -/
structure PayloadLiveStoredWordRankSelectFamily
    (rankOverhead selectOverhead : Nat -> Nat) where
  rankComponent :
    forall bits : List Bool,
      PayloadLiveStoredWordRankData bits (rankOverhead bits.length)
  selectComponent :
    forall bits : List Bool,
      PayloadLiveStoredWordSelectData bits (selectOverhead bits.length)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadLiveStoredWordRankSelectFamily

def overhead
    {rankOverhead selectOverhead : Nat -> Nat}
    (_family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    Nat -> Nat :=
  fun n => rankOverhead n + selectOverhead n

theorem overhead_littleO
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead := by
  exact family.rank_littleO.add family.select_littleO

def toRankSelectFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    RankSelectFamily family.overhead 3 where
  directory bits :=
    RankSelectDirectory.ofPayloadLiveRankSelectData
      (family.rankComponent bits) (family.selectComponent bits)
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall bits : List Bool,
        (((family.toRankSelectFamily).directory bits).auxPayload.length =
          rankOverhead bits.length + selectOverhead bits.length) /\
          (forall target pos,
            (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact
      RankSelectDirectory.ofPayloadLiveRankSelectData_profile
        (family.rankComponent bits) (family.selectComponent bits)

end PayloadLiveStoredWordRankSelectFamily

/--
Stored data needed for a faithful bounded select query.

The query path reads one occurrence locator, reads one payload word, and then
uses a RAM word-select primitive inside that word.  A `none` locator certifies
that the requested occurrence does not exist.
-/
structure StoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  words : TableModel.IndexedSeq (List Bool)
  trueSamples : TableModel.IndexedSeq (Option StoredWordSelectSample)
  falseSamples : TableModel.IndexedSeq (Option StoredWordSelectSample)
  encodeAux : List Bool
  aux_length_eq : encodeAux.length = overhead
  sample_entry_present :
    forall target occurrence,
      exists entry,
        (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some entry
  word_present_of_sample :
    forall target occurrence sample,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some (some sample) ->
        exists word, words.get? sample.wordIndex = some word
  select_some_exact :
    forall target occurrence sample word,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some (some sample) ->
        words.get? sample.wordIndex = some word ->
          (RAM.boolSelectInWord target word
              (occurrence - sample.rankBefore)).map
              (fun offset => sample.wordStart + offset) =
            Succinct.select target bits occurrence
  select_none_exact :
    forall target occurrence,
      (selectSampleSeqOf target trueSamples falseSamples).get?
          occurrence = some none ->
        Succinct.select target bits occurrence = none

namespace StoredWordSelectData

def sampleSeq
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead) (target : Bool) :
    TableModel.IndexedSeq (Option StoredWordSelectSample) :=
  selectSampleSeqOf target data.trueSamples data.falseSamples

def selectCosted
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind ((data.sampleSeq target).getCosted occurrence) fun entry? =>
    match entry? with
    | none => Costed.pure none
    | some none => Costed.pure none
    | some (some sample) =>
        Costed.bind (data.words.getCosted sample.wordIndex) fun word? =>
          match word? with
          | none => Costed.pure none
          | some word =>
              Costed.map
                (fun local? =>
                  local?.map fun offset => sample.wordStart + offset)
                (RAM.selectBoolWord target word
                  (occurrence - sample.rankBefore)).toCosted

theorem selectCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= 3 := by
  unfold selectCosted sampleSeq
  cases hentry :
      (selectSampleSeqOf target data.trueSamples data.falseSamples).get?
        occurrence with
  | none =>
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, Costed.bind, Costed.pure, TableModel.indexedReadCost]
  | some entry =>
      cases entry with
      | none =>
          simp [TableModel.IndexedSeq.getCosted,
            TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
            hentry, Costed.bind, Costed.pure, TableModel.indexedReadCost]
      | some sample =>
          cases hword : data.words.get? sample.wordIndex with
          | none =>
              simp [TableModel.IndexedSeq.getCosted,
                TableModel.IndexedSeq.toAccess,
                TableModel.IndexedAccess.getCosted,
                hentry, hword, Costed.bind, Costed.pure,
                TableModel.indexedReadCost]
          | some word =>
              simp [TableModel.IndexedSeq.getCosted,
                TableModel.IndexedSeq.toAccess,
                TableModel.IndexedAccess.getCosted,
                hentry, hword, Costed.bind, Costed.map, Costed.pure,
                TableModel.indexedReadCost]

theorem selectCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  rcases data.sample_entry_present target occurrence with ⟨entry, hentry⟩
  cases entry with
  | none =>
      have hnone := data.select_none_exact target occurrence hentry
      unfold selectCosted sampleSeq
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, Costed.bind, Costed.pure, hnone]
  | some sample =>
      rcases data.word_present_of_sample target occurrence sample hentry with
        ⟨word, hword⟩
      have hexact :=
        data.select_some_exact target occurrence sample word hentry hword
      unfold selectCosted sampleSeq
      simp [TableModel.IndexedSeq.getCosted,
        TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
        hentry, hword, Costed.bind, Costed.map, Costed.pure, hexact]

theorem selectCosted_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordSelectData bits overhead) :
    data.encodeAux.length = overhead /\
      forall target occurrence,
        (data.selectCosted target occurrence).cost <= 3 /\
          (data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact data.aux_length_eq
  · intro target occurrence
    exact ⟨data.selectCosted_cost_le_three target occurrence,
      data.selectCosted_exact target occurrence⟩

end StoredWordSelectData

/--
Combined rank/select directory with payload-live rank samples.

This is an intermediate migration adapter: rank goes through
`PayloadLiveStoredWordRankData`, so its sample and bit-word reads are tied to
concrete counted payload stores.  Select is still the existing stored-word
component and remains a separate target for the next payload-live migration.
-/
def RankSelectDirectory.ofPayloadLiveRankStoredSelectData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.encodeAux
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.aux_length_eq]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofPayloadLiveRankStoredSelectData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
        rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).rankQueryCosted target pos).cost <= 3 /\
          ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).selectQueryCosted target occurrence).cost <=
              3 /\
          ((RankSelectDirectory.ofPayloadLiveRankStoredSelectData
            rankData selectData).selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact
      (RankSelectDirectory.ofPayloadLiveRankStoredSelectData
        rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankStoredSelectData
          rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofPayloadLiveRankStoredSelectData
          rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/--
Combined faithful stored-word rank/select directory.

Rank uses the clamped valid-prefix adapter; select uses the occurrence-locator
and word-select path.  Both operations are bounded by three modeled primitive
steps and erase to the reference list-level semantics.
-/
def RankSelectDirectory.ofStoredWordData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : StoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.encodeAux ++ selectData.encodeAux
  rankCosted _ target pos := rankData.rankCostedClamped target pos
  selectCosted _ target occurrence := selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.aux_length_eq, selectData.aux_length_eq]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCostedClamped_cost_le_three target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le_three target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCostedClamped_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem RankSelectDirectory.ofStoredWordData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : StoredWordRankData bits rankOverhead)
    (selectData : StoredWordSelectData bits selectOverhead) :
    ((RankSelectDirectory.ofStoredWordData rankData selectData).auxPayload.length =
        rankOverhead + selectOverhead) /\
      (forall target pos,
        ((RankSelectDirectory.ofStoredWordData rankData selectData).rankQueryCosted
            target pos).cost <= 3 /\
          ((RankSelectDirectory.ofStoredWordData rankData selectData).rankQueryCosted
            target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((RankSelectDirectory.ofStoredWordData rankData selectData).selectQueryCosted
            target occurrence).cost <= 3 /\
          ((RankSelectDirectory.ofStoredWordData rankData selectData).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact (RankSelectDirectory.ofStoredWordData rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory :=
        RankSelectDirectory.ofStoredWordData rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory :=
        RankSelectDirectory.ofStoredWordData rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

/--
Payload-backed stored rank data.

The `StoredWordRankData` fields provide the operational read path and semantic
certificates.  This wrapper records that the stored words and rank samples are
decoded from the counted auxiliary payload rather than existing only as
proof-side fields.
-/
structure PayloadBackedStoredWordRankData
    (bits : List Bool) (overhead : Nat) where
  data : StoredWordRankData bits overhead
  payload : List Bool
  payload_eq_encodeAux : payload = data.encodeAux
  decodeWords : List Bool -> TableModel.IndexedSeq (List Bool)
  decodeTrueSamples : List Bool -> TableModel.IndexedSeq Nat
  decodeFalseSamples : List Bool -> TableModel.IndexedSeq Nat
  words_eq_decode : decodeWords payload = data.words
  trueSamples_eq_decode : decodeTrueSamples payload = data.trueSamples
  falseSamples_eq_decode : decodeFalseSamples payload = data.falseSamples

namespace PayloadBackedStoredWordRankData

theorem payload_length_eq
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordRankData bits overhead) :
    backed.payload.length = overhead := by
  rw [backed.payload_eq_encodeAux]
  exact backed.data.aux_length_eq

theorem rankCosted_profile
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordRankData bits overhead) :
    backed.payload.length = overhead /\
      backed.decodeWords backed.payload = backed.data.words /\
      backed.decodeTrueSamples backed.payload = backed.data.trueSamples /\
      backed.decodeFalseSamples backed.payload = backed.data.falseSamples /\
      forall target pos,
        (backed.data.rankCostedClamped target pos).cost <= 3 /\
          (backed.data.rankCostedClamped target pos).erase =
            Succinct.rankPrefix target bits pos := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.words_eq_decode
    · constructor
      · exact backed.trueSamples_eq_decode
      · constructor
        · exact backed.falseSamples_eq_decode
        · intro target pos
          exact ⟨backed.data.rankCostedClamped_cost_le_three target pos,
            backed.data.rankCostedClamped_exact target pos⟩

end PayloadBackedStoredWordRankData

/--
Payload-backed stored select data, tying occurrence locators and payload words
to the counted auxiliary payload through explicit decoders.
-/
structure PayloadBackedStoredWordSelectData
    (bits : List Bool) (overhead : Nat) where
  data : StoredWordSelectData bits overhead
  payload : List Bool
  payload_eq_encodeAux : payload = data.encodeAux
  decodeWords : List Bool -> TableModel.IndexedSeq (List Bool)
  decodeTrueSamples :
    List Bool -> TableModel.IndexedSeq (Option StoredWordSelectSample)
  decodeFalseSamples :
    List Bool -> TableModel.IndexedSeq (Option StoredWordSelectSample)
  words_eq_decode : decodeWords payload = data.words
  trueSamples_eq_decode : decodeTrueSamples payload = data.trueSamples
  falseSamples_eq_decode : decodeFalseSamples payload = data.falseSamples

namespace PayloadBackedStoredWordSelectData

theorem payload_length_eq
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordSelectData bits overhead) :
    backed.payload.length = overhead := by
  rw [backed.payload_eq_encodeAux]
  exact backed.data.aux_length_eq

theorem selectCosted_profile
    {bits : List Bool} {overhead : Nat}
    (backed : PayloadBackedStoredWordSelectData bits overhead) :
    backed.payload.length = overhead /\
      backed.decodeWords backed.payload = backed.data.words /\
      backed.decodeTrueSamples backed.payload = backed.data.trueSamples /\
      backed.decodeFalseSamples backed.payload = backed.data.falseSamples /\
      forall target occurrence,
        (backed.data.selectCosted target occurrence).cost <= 3 /\
          (backed.data.selectCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.words_eq_decode
    · constructor
      · exact backed.trueSamples_eq_decode
      · constructor
        · exact backed.falseSamples_eq_decode
        · intro target occurrence
          exact ⟨backed.data.selectCosted_cost_le_three target occurrence,
            backed.data.selectCosted_exact target occurrence⟩

end PayloadBackedStoredWordSelectData

/-- Payload-backed combined stored-word rank/select component. -/
structure PayloadBackedStoredWordRankSelectData
    (bits : List Bool) (rankOverhead selectOverhead : Nat) where
  rank : PayloadBackedStoredWordRankData bits rankOverhead
  select : PayloadBackedStoredWordSelectData bits selectOverhead

namespace PayloadBackedStoredWordRankSelectData

def payload
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    List Bool :=
  backed.rank.payload ++ backed.select.payload

def toRankSelectDirectory
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    RankSelectDirectory bits (rankOverhead + selectOverhead) 3 :=
  RankSelectDirectory.ofStoredWordData backed.rank.data backed.select.data

theorem payload_length_eq
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead := by
  simp [payload, backed.rank.payload_length_eq,
    backed.select.payload_length_eq]

theorem directory_auxPayload_eq_payload
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.toRankSelectDirectory.auxPayload = backed.payload := by
  simp [toRankSelectDirectory, RankSelectDirectory.ofStoredWordData,
    RankSelectDirectory.auxPayload, payload,
    ← backed.rank.payload_eq_encodeAux,
    ← backed.select.payload_eq_encodeAux]

theorem directory_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData bits rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      backed.toRankSelectDirectory.auxPayload = backed.payload /\
      (forall target pos,
        (backed.toRankSelectDirectory.rankQueryCosted target pos).cost <= 3 /\
          (backed.toRankSelectDirectory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (backed.toRankSelectDirectory.selectQueryCosted target occurrence).cost <=
            3 /\
          (backed.toRankSelectDirectory.selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro target pos
        exact ⟨backed.toRankSelectDirectory.rankQueryCosted_cost_le target pos,
          backed.toRankSelectDirectory.rankQueryCosted_erase target pos⟩
      · intro target occurrence
        exact ⟨
          backed.toRankSelectDirectory.selectQueryCosted_cost_le
            target occurrence,
          backed.toRankSelectDirectory.selectQueryCosted_erase
            target occurrence⟩

end PayloadBackedStoredWordRankSelectData

/-- Family of payload-backed stored-word rank/select components. -/
structure PayloadBackedStoredWordRankSelectFamily
    (rankOverhead selectOverhead : Nat -> Nat) where
  component :
    forall bits : List Bool,
      PayloadBackedStoredWordRankSelectData bits
        (rankOverhead bits.length) (selectOverhead bits.length)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadBackedStoredWordRankSelectFamily

def overhead
    {rankOverhead selectOverhead : Nat -> Nat}
    (_family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    Nat -> Nat :=
  fun n => rankOverhead n + selectOverhead n

theorem overhead_littleO
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead := by
  exact family.rank_littleO.add family.select_littleO

def toRankSelectFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    RankSelectFamily family.overhead 3 where
  directory bits := (family.component bits).toRankSelectDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.component bits).payload.length =
          rankOverhead bits.length + selectOverhead bits.length) /\
          (((family.toRankSelectFamily).directory bits).auxPayload =
            (family.component bits).payload) /\
          (forall target pos,
            (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).cost <= 3 /\
              (((family.toRankSelectFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    have hprofile := (family.component bits).directory_profile
    exact hprofile

end PayloadBackedStoredWordRankSelectFamily

/--
Rank-only directory with the validity condition made explicit.

The older `RankSelectDirectory` requires total rank exactness for every `pos`.
Faithful stored-word rank is naturally exact for `pos <= bits.length`, because
out-of-domain positions need not have a stored sample or payload word.  This
interface is therefore the honest component boundary for broadword
balanced-parentheses access: queries are still uniformly costed for every
input, while semantic exactness is stated on the valid prefix range.
-/
structure ValidRankDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  Aux : Type
  buildAux : Aux
  encodeAux : Aux -> List Bool
  rankCosted : Aux -> Bool -> Nat -> Costed Nat
  aux_length_eq : (encodeAux buildAux).length = overhead
  rank_cost_le :
    forall target pos, (rankCosted buildAux target pos).cost <= queryCost
  rank_exact_of_le :
    forall target {pos : Nat}, pos <= bits.length ->
      (rankCosted buildAux target pos).erase =
        Succinct.rankPrefix target bits pos

namespace ValidRankDirectory

def auxPayload
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost) :
    List Bool :=
  directory.encodeAux directory.buildAux

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost) :
    directory.auxPayload.length = overhead := by
  exact directory.aux_length_eq

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted directory.buildAux target pos

theorem rankQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).cost <= queryCost := by
  exact directory.rank_cost_le target pos

theorem rankQueryCosted_exact_of_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (directory.rankQueryCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  exact directory.rank_exact_of_le target hpos

/-- Faithful stored-word rank data exposed through the valid-rank interface. -/
def ofStoredWordRankData
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    ValidRankDirectory bits overhead 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := data.encodeAux
  rankCosted _ target pos := data.rankCosted target pos
  aux_length_eq := data.aux_length_eq
  rank_cost_le := by
    intro target pos
    exact data.rankCosted_cost_le_three target pos
  rank_exact_of_le := by
    intro target pos hpos
    exact data.rankCosted_exact target hpos

theorem ofStoredWordRankData_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    ((ofStoredWordRankData data).auxPayload.length = overhead) /\
      forall target pos,
        ((ofStoredWordRankData data).rankQueryCosted target pos).cost <= 3 /\
          (pos <= bits.length ->
            ((ofStoredWordRankData data).rankQueryCosted target pos).erase =
              Succinct.rankPrefix target bits pos) := by
  constructor
  · exact (ofStoredWordRankData data).auxPayload_length
  · intro target pos
    exact ⟨
      (ofStoredWordRankData data).rankQueryCosted_cost_le target pos,
      fun hpos =>
        (ofStoredWordRankData data).rankQueryCosted_exact_of_le target hpos⟩

end ValidRankDirectory

/--
Family-level valid rank component.

This is the rank half of the eventual rank/select layer.  It can already be
fed by `StoredWordRankData`, and later select/navigation components can be
added without weakening this validity-scoped exactness theorem.
-/
structure ValidRankFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      ValidRankDirectory bits (overhead bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace ValidRankFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length = overhead bits.length) /\
          forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              (pos <= bits.length ->
                ((family.directory bits).rankQueryCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    constructor
    · exact (family.directory bits).auxPayload_length
    · intro target pos
      exact ⟨
        (family.directory bits).rankQueryCosted_cost_le target pos,
        fun hpos =>
          (family.directory bits).rankQueryCosted_exact_of_le target hpos⟩

end ValidRankFamily

/-- Family of faithful stored-word rank directories over arbitrary bitvectors. -/
structure StoredWordRankDataFamily
    (overhead : Nat -> Nat) where
  data :
    forall bits : List Bool,
      StoredWordRankData bits (overhead bits.length)
  overhead_littleO : LittleOLinear overhead

namespace StoredWordRankDataFamily

def toValidRankFamily
    {overhead : Nat -> Nat}
    (family : StoredWordRankDataFamily overhead) :
    ValidRankFamily overhead 3 where
  directory bits := ValidRankDirectory.ofStoredWordRankData (family.data bits)
  overhead_littleO := family.overhead_littleO

theorem constant_rank_profile
    {overhead : Nat -> Nat}
    (family : StoredWordRankDataFamily overhead) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        (((family.toValidRankFamily).directory bits).auxPayload.length =
            overhead bits.length) /\
          forall target pos,
            (((family.toValidRankFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (pos <= bits.length ->
                (((family.toValidRankFamily).directory bits).rankQueryCosted
                    target pos).erase =
                  Succinct.rankPrefix target bits pos) := by
  exact family.toValidRankFamily.constant_query_profile

end StoredWordRankDataFamily

/--
Balanced-parentheses rank/excess access backed by any valid-position rank
directory.

This is the generic version of the stored-word rank/excess component below:
rank exactness is only required for valid prefix positions, which is exactly
what balanced-parentheses excess and prefix-balance facts consume.
-/
structure ValidRankBalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead queryCost : Nat) where
  rankDirectory : ValidRankDirectory parens.bits overhead queryCost

namespace ValidRankBalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankDirectory.rankQueryCosted target pos

def excessCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

theorem auxPayload_length
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    access.rankDirectory.auxPayload.length = overhead := by
  exact access.rankDirectory.auxPayload_length

theorem rankCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= queryCost := by
  exact access.rankDirectory.rankQueryCosted_cost_le target pos

theorem rankCosted_exact_of_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankDirectory.rankQueryCosted_exact_of_le target hpos

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_exact_of_le false hpos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_exact_of_le true hpos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  have hpos : parens.bits.length <= parens.bits.length := Nat.le_refl _
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_exact_of_le true hpos
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_exact_of_le false hpos).symm

theorem excessCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 2 * queryCost := by
  have hopen := access.rankCosted_cost_le true pos
  have hclose := access.rankCosted_cost_le false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <=
        queryCost + queryCost :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map, Nat.two_mul] using hsum

theorem excessCosted_exact_of_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_exact_of_le true hpos,
    access.rankCosted_exact_of_le false hpos]

theorem profile
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    access.rankDirectory.auxPayload.length = overhead /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (pos <= parens.bits.length ->
            (access.rankCosted target pos).erase =
              Succinct.rankPrefix target parens.bits pos)) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (pos <= parens.bits.length ->
            (access.excessCosted pos).erase =
              Succinct.rankPrefix true parens.bits pos -
                Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        fun hpos => access.rankCosted_exact_of_le target hpos⟩
    · constructor
      · intro pos hpos
        exact access.close_rank_le_open_rank hpos
      · constructor
        · exact access.final_rank_eq
        · intro pos
          exact ⟨access.excessCosted_cost_le pos,
            fun hpos => access.excessCosted_exact_of_le hpos⟩

end ValidRankBalancedParensAccess

/-- Family-level BP rank/excess component backed by valid-position rank. -/
structure ValidRankBalancedParensAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      ValidRankBalancedParensAccess parens
        (overhead parens.bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace ValidRankBalancedParensAccessFamily

def ofValidRankFamily
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    ValidRankBalancedParensAccessFamily overhead queryCost where
  access parens := { rankDirectory := family.directory parens.bits }
  overhead_littleO := family.overhead_littleO

theorem constant_rank_excess_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankBalancedParensAccessFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankDirectory.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <=
                queryCost /\
              (pos <= parens.bits.length ->
                ((family.access parens).rankCosted target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <=
                2 * queryCost /\
              (pos <= parens.bits.length ->
                ((family.access parens).excessCosted pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    exact (family.access parens).profile

theorem ofValidRankFamily_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        (((ofValidRankFamily family).access parens).rankDirectory.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            (((ofValidRankFamily family).access parens).rankCosted
                target pos).cost <= queryCost /\
              (pos <= parens.bits.length ->
                (((ofValidRankFamily family).access parens).rankCosted
                    target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              (((ofValidRankFamily family).access parens).rankCosted
                  false pos).erase <=
                (((ofValidRankFamily family).access parens).rankCosted
                  true pos).erase) /\
          ((((ofValidRankFamily family).access parens).rankCosted
              true parens.bits.length).erase =
            (((ofValidRankFamily family).access parens).rankCosted
              false parens.bits.length).erase) /\
          (forall pos,
            (((ofValidRankFamily family).access parens).excessCosted pos).cost <=
                2 * queryCost /\
              (pos <= parens.bits.length ->
                (((ofValidRankFamily family).access parens).excessCosted
                    pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  exact (ofValidRankFamily family).constant_rank_excess_profile

end ValidRankBalancedParensAccessFamily

/--
Balanced-parentheses rank/excess access backed by the faithful stored word-rank
component above.
-/
structure StoredRankBalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead : Nat) where
  rankData : StoredWordRankData parens.bits overhead

namespace StoredRankBalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankData.rankCosted target pos

def excessCosted
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

theorem rankCosted_cost_le_three
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= 3 := by
  exact access.rankData.rankCosted_cost_le_three target pos

theorem rankCosted_exact
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankData.rankCosted_exact target hpos

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_exact false hpos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_exact true hpos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  have hpos : parens.bits.length <= parens.bits.length := Nat.le_refl _
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_exact true hpos
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_exact false hpos).symm

theorem excessCosted_cost_le_six
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 6 := by
  have hopen := access.rankCosted_cost_le_three true pos
  have hclose := access.rankCosted_cost_le_three false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <= 3 + 3 :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map] using hsum

theorem excessCosted_exact
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_exact true hpos,
    access.rankCosted_exact false hpos]

theorem profile
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead) :
    access.rankData.encodeAux.length = overhead /\
      (forall target pos,
        (access.rankCosted target pos).cost <= 3 /\
          (pos <= parens.bits.length ->
            (access.rankCosted target pos).erase =
              Succinct.rankPrefix target parens.bits pos)) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 6 /\
          (pos <= parens.bits.length ->
            (access.excessCosted pos).erase =
              Succinct.rankPrefix true parens.bits pos -
                Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact access.rankData.aux_length_eq
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le_three target pos,
        fun hpos => access.rankCosted_exact target hpos⟩
    · constructor
      · intro pos hpos
        exact access.close_rank_le_open_rank hpos
      · constructor
        · exact access.final_rank_eq
        · intro pos
          exact ⟨access.excessCosted_cost_le_six pos,
            fun hpos => access.excessCosted_exact hpos⟩

end StoredRankBalancedParensAccess

/-- Family of faithful stored-read BP rank/excess access structures. -/
structure StoredRankBalancedParensAccessFamily
    (overhead : Nat -> Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      StoredRankBalancedParensAccess parens (overhead parens.bits.length)
  overhead_littleO : LittleOLinear overhead

namespace StoredRankBalancedParensAccessFamily

theorem constant_rank_excess_profile
    {overhead : Nat -> Nat}
    (family : StoredRankBalancedParensAccessFamily overhead) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankData.encodeAux.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <= 3 /\
              (pos <= parens.bits.length ->
                ((family.access parens).rankCosted target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <= 6 /\
              (pos <= parens.bits.length ->
                ((family.access parens).excessCosted pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    exact (family.access parens).profile

end StoredRankBalancedParensAccessFamily

/--
Balanced-parentheses access layer backed by a certified rank/select directory.

This is the next component slot toward a BP-native succinct RMQ/LCA structure:
the parenthesis balance facts are transported through costed rank queries, and
the excess operation charges exactly two rank queries.
-/
structure BalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead queryCost : Nat) where
  rankSelect : RankSelectDirectory parens.bits overhead queryCost

namespace BalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankSelect.rankQueryCosted target pos

def selectCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  access.rankSelect.selectQueryCosted target occurrence

def excessCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

def ofPayloadBackedStoredWordRankSelectData
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData parens.bits
        rankOverhead selectOverhead) :
    BalancedParensAccess parens (rankOverhead + selectOverhead) 3 where
  rankSelect := backed.toRankSelectDirectory

/--
Payload-live stored-word rank/select data instantiate balanced-parentheses
rank/select access without routing through decoded auxiliary tables.
-/
def ofPayloadLiveStoredWordRankSelectData
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData parens.bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData parens.bits selectOverhead) :
    BalancedParensAccess parens (rankOverhead + selectOverhead) 3 where
  rankSelect :=
    RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData

theorem auxPayload_length
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost) :
    access.rankSelect.auxPayload.length = overhead := by
  exact access.rankSelect.auxPayload_length

theorem rankCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= queryCost := by
  exact access.rankSelect.rankQueryCosted_cost_le target pos

theorem selectCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (access.selectCosted target occurrence).cost <= queryCost := by
  exact access.rankSelect.selectQueryCosted_cost_le target occurrence

@[simp] theorem rankCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankSelect.rankQueryCosted_erase target pos

@[simp] theorem selectCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (access.selectCosted target occurrence).erase =
      Succinct.select target parens.bits occurrence := by
  exact access.rankSelect.selectQueryCosted_erase target occurrence

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_erase false pos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_erase true pos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_erase true parens.bits.length
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_erase false parens.bits.length).symm

theorem excessCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_erase true pos, access.rankCosted_erase false pos]

theorem excessCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 2 * queryCost := by
  have hopen := access.rankCosted_cost_le true pos
  have hclose := access.rankCosted_cost_le false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <=
        queryCost + queryCost :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map, Nat.two_mul] using hsum

theorem ofPayloadBackedStoredWordRankSelectData_profile
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData parens.bits
        rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      ((ofPayloadBackedStoredWordRankSelectData backed).rankSelect.auxPayload =
        backed.payload) /\
      (forall target pos,
        ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
            target pos).cost <= 3 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
            target pos).erase =
            Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        ((ofPayloadBackedStoredWordRankSelectData backed).selectCosted
            target occurrence).cost <= 3 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).selectCosted
            target occurrence).erase =
            Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
              false pos).erase <=
            ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
              true pos).erase) /\
      (((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
          true parens.bits.length).erase =
        ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
          false parens.bits.length).erase) /\
      (forall pos,
        ((ofPayloadBackedStoredWordRankSelectData backed).excessCosted pos).cost <=
            6 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).excessCosted
            pos).erase =
            Succinct.rankPrefix true parens.bits pos -
              Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro target pos
        let access := ofPayloadBackedStoredWordRankSelectData backed
        exact ⟨access.rankCosted_cost_le target pos,
          access.rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          let access := ofPayloadBackedStoredWordRankSelectData backed
          exact ⟨access.selectCosted_cost_le target occurrence,
            access.selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            let access := ofPayloadBackedStoredWordRankSelectData backed
            exact access.close_rank_le_open_rank hpos
          · constructor
            · exact
                (ofPayloadBackedStoredWordRankSelectData backed).final_rank_eq
            · intro pos
              let access := ofPayloadBackedStoredWordRankSelectData backed
              exact ⟨by
                simpa using access.excessCosted_cost_le pos,
                access.excessCosted_erase pos⟩

theorem ofPayloadLiveStoredWordRankSelectData_profile
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData parens.bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData parens.bits selectOverhead) :
    ((ofPayloadLiveStoredWordRankSelectData
        rankData selectData).rankSelect.auxPayload.length =
        rankOverhead + selectOverhead) /\
      ((ofPayloadLiveStoredWordRankSelectData
          rankData selectData).rankSelect.auxPayload =
        rankData.auxPayload ++ selectData.auxPayload) /\
      (forall target pos,
        ((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
            target pos).cost <= 3 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted target pos).erase =
            Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        ((ofPayloadLiveStoredWordRankSelectData
            rankData selectData).selectCosted target occurrence).cost <= 3 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).selectCosted target occurrence).erase =
            Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted false pos).erase <=
            ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted true pos).erase) /\
      (((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
          true parens.bits.length).erase =
        ((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
          false parens.bits.length).erase) /\
      (forall pos,
        ((ofPayloadLiveStoredWordRankSelectData
            rankData selectData).excessCosted pos).cost <= 6 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).excessCosted pos).erase =
            Succinct.rankPrefix true parens.bits pos -
              Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact
      (ofPayloadLiveStoredWordRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · simp [ofPayloadLiveStoredWordRankSelectData,
        RankSelectDirectory.ofPayloadLiveRankSelectData,
        RankSelectDirectory.auxPayload]
    · constructor
      · intro target pos
        let access :=
          ofPayloadLiveStoredWordRankSelectData rankData selectData
        exact ⟨access.rankCosted_cost_le target pos,
          access.rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          let access :=
            ofPayloadLiveStoredWordRankSelectData rankData selectData
          exact ⟨access.selectCosted_cost_le target occurrence,
            access.selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            let access :=
              ofPayloadLiveStoredWordRankSelectData rankData selectData
            exact access.close_rank_le_open_rank hpos
          · constructor
            · exact
                (ofPayloadLiveStoredWordRankSelectData
                  rankData selectData).final_rank_eq
            · intro pos
              let access :=
                ofPayloadLiveStoredWordRankSelectData rankData selectData
              exact ⟨by
                simpa using access.excessCosted_cost_le pos,
                access.excessCosted_erase pos⟩

def ofShapePayloadBackedStoredWordRankSelectData
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData shape.bpCode
        rankOverhead selectOverhead) :
    BalancedParensAccess (bpParensOfShape shape)
      (rankOverhead + selectOverhead) 3 :=
  ofPayloadBackedStoredWordRankSelectData backed

/-- Payload-live BP rank/select access specialized to Cartesian BP codes. -/
def ofShapePayloadLiveStoredWordRankSelectData
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (selectData :
      PayloadLiveStoredWordSelectData shape.bpCode selectOverhead) :
    BalancedParensAccess (bpParensOfShape shape)
      (rankOverhead + selectOverhead) 3 :=
  ofPayloadLiveStoredWordRankSelectData rankData selectData

theorem ofShapePayloadBackedStoredWordRankSelectData_close_profile
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData shape.bpCode
        rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      ((ofShapePayloadBackedStoredWordRankSelectData backed).rankSelect.auxPayload =
        backed.payload) /\
      (forall idx,
        ((ofShapePayloadBackedStoredWordRankSelectData backed).selectCosted
            false idx).cost <= 3 /\
          ((ofShapePayloadBackedStoredWordRankSelectData backed).selectCosted
              false idx).erase =
            bpCloseOfInorder? shape idx) /\
      (forall pos,
        ((ofShapePayloadBackedStoredWordRankSelectData backed).rankCosted
            false pos).cost <= 3 /\
          ((ofShapePayloadBackedStoredWordRankSelectData backed).rankCosted
              false pos).erase =
            Succinct.rankPrefix false shape.bpCode pos) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro idx
        let access := ofShapePayloadBackedStoredWordRankSelectData backed
        constructor
        · exact access.selectCosted_cost_le false idx
        · calc
            (access.selectCosted false idx).erase =
              Succinct.select false shape.bpCode idx := by
                exact access.selectCosted_erase false idx
            _ = bpCloseOfInorder? shape idx := by
                exact select_false_bpCode_eq_bpCloseOfInorder? shape idx
      · intro pos
        let access := ofShapePayloadBackedStoredWordRankSelectData backed
        exact ⟨access.rankCosted_cost_le false pos,
          access.rankCosted_erase false pos⟩

theorem ofShapePayloadLiveStoredWordRankSelectData_close_profile
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (selectData :
      PayloadLiveStoredWordSelectData shape.bpCode selectOverhead) :
    ((ofShapePayloadLiveStoredWordRankSelectData
        rankData selectData).rankSelect.auxPayload.length =
        rankOverhead + selectOverhead) /\
      ((ofShapePayloadLiveStoredWordRankSelectData
          rankData selectData).rankSelect.auxPayload =
        rankData.auxPayload ++ selectData.auxPayload) /\
      (forall idx,
        ((ofShapePayloadLiveStoredWordRankSelectData
            rankData selectData).selectCosted false idx).cost <= 3 /\
          ((ofShapePayloadLiveStoredWordRankSelectData
              rankData selectData).selectCosted false idx).erase =
            bpCloseOfInorder? shape idx) /\
      (forall pos,
        ((ofShapePayloadLiveStoredWordRankSelectData
            rankData selectData).rankCosted false pos).cost <= 3 /\
          ((ofShapePayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted false pos).erase =
            Succinct.rankPrefix false shape.bpCode pos) := by
  constructor
  · exact
      (ofShapePayloadLiveStoredWordRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · simp [ofShapePayloadLiveStoredWordRankSelectData,
        ofPayloadLiveStoredWordRankSelectData,
        RankSelectDirectory.ofPayloadLiveRankSelectData,
        RankSelectDirectory.auxPayload]
    · constructor
      · intro idx
        let access :=
          ofShapePayloadLiveStoredWordRankSelectData rankData selectData
        constructor
        · exact access.selectCosted_cost_le false idx
        · calc
            (access.selectCosted false idx).erase =
              Succinct.select false shape.bpCode idx := by
                exact access.selectCosted_erase false idx
            _ = bpCloseOfInorder? shape idx := by
                exact select_false_bpCode_eq_bpCloseOfInorder? shape idx
      · intro pos
        let access :=
          ofShapePayloadLiveStoredWordRankSelectData rankData selectData
        exact ⟨access.rankCosted_cost_le false pos,
          access.rankCosted_erase false pos⟩

end BalancedParensAccess

/--
Family-level balanced-parentheses access component.

This is the BP analogue of `RankSelectFamily`: every certified balanced
parentheses string gets rank/select access, transported balance facts, and
two-rank excess queries under one uniform cost bound and one `o(n)` auxiliary
overhead function.
-/
structure BalancedParensAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      BalancedParensAccess parens (overhead parens.bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BalancedParensAccessFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BalancedParensAccessFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankSelect.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <=
                queryCost /\
              ((family.access parens).rankCosted target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            ((family.access parens).selectCosted target occurrence).cost <=
                queryCost /\
              ((family.access parens).selectCosted target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <=
                2 * queryCost /\
              ((family.access parens).excessCosted pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    constructor
    · exact (family.access parens).auxPayload_length
    · constructor
      · intro target pos
        exact ⟨(family.access parens).rankCosted_cost_le target pos,
          (family.access parens).rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          exact ⟨(family.access parens).selectCosted_cost_le target occurrence,
            (family.access parens).selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            exact (family.access parens).close_rank_le_open_rank hpos
          · constructor
            · exact (family.access parens).final_rank_eq
            · intro pos
              exact ⟨(family.access parens).excessCosted_cost_le pos,
                (family.access parens).excessCosted_erase pos⟩

end BalancedParensAccessFamily

/--
Payload-live stored-word rank/select components instantiate the generic
balanced-parentheses access-family interface.
-/
def PayloadLiveStoredWordRankSelectFamily.toBalancedParensAccessFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    BalancedParensAccessFamily family.overhead 3 where
  access parens :=
    BalancedParensAccess.ofPayloadLiveStoredWordRankSelectData
      (family.rankComponent parens.bits) (family.selectComponent parens.bits)
  overhead_littleO := family.overhead_littleO

theorem PayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall parens : Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
          (forall target pos,
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                false pos).erase <=
                (((family.toBalancedParensAccessFamily).access parens).rankCosted
                  true pos).erase) /\
          ((((family.toBalancedParensAccessFamily).access parens).rankCosted
              true parens.bits.length).erase =
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              false parens.bits.length).erase) /\
          (forall pos,
            (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).cost <= 6 /\
              (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  have hprofile :=
    (family.toBalancedParensAccessFamily).constant_query_profile
  constructor
  · exact hprofile.1
  · intro parens
    rcases hprofile.2 parens with
      ⟨haux, hrank, hselect, hprefix, hfinal, hexcess⟩
    constructor
    · exact haux
    · constructor
      · exact hrank
      · constructor
        · exact hselect
        · constructor
          · exact hprefix
          · constructor
            · exact hfinal
            · intro pos
              exact hexcess pos

/--
Payload-backed stored-word rank/select components instantiate the generic
balanced-parentheses access-family interface.
-/
def PayloadBackedStoredWordRankSelectFamily.toBalancedParensAccessFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    BalancedParensAccessFamily family.overhead 3 where
  access parens :=
    BalancedParensAccess.ofPayloadBackedStoredWordRankSelectData
      (family.component parens.bits)
  overhead_littleO := family.overhead_littleO

theorem PayloadBackedStoredWordRankSelectFamily.bp_constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall parens : Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
          (forall target pos,
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                false pos).erase <=
                (((family.toBalancedParensAccessFamily).access parens).rankCosted
                  true pos).erase) /\
          ((((family.toBalancedParensAccessFamily).access parens).rankCosted
              true parens.bits.length).erase =
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              false parens.bits.length).erase) /\
          (forall pos,
            (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).cost <= 6 /\
              (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  have hprofile :=
    (family.toBalancedParensAccessFamily).constant_query_profile
  constructor
  · exact hprofile.1
  · intro parens
    rcases hprofile.2 parens with
      ⟨haux, hrank, hselect, hprefix, hfinal, hexcess⟩
    constructor
    · exact haux
    · constructor
      · exact hrank
      · constructor
        · exact hselect
        · constructor
          · exact hprefix
          · constructor
            · exact hfinal
            · intro pos
              have h := hexcess pos
              exact ⟨by simpa using h.1, h.2⟩

/--
A certified word-RAM/broadword directory for exact RMQ over Cartesian-shape
representatives of size `n`.

The encoded payload is the canonical `2*n` shape payload followed by an
auxiliary payload of exactly `overhead` bits.  The query procedure consumes only
that encoded payload and is costed by the supplied model.  The `query_exact`
field is the anti-vacuity condition: the costed query must refine the ordinary
leftmost RMQ answer on the canonical representative array.
-/
structure BroadwordRMQDirectory
    (n overhead queryCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  queryEncodedCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  query_cost_le :
    forall payload left right,
      (queryEncodedCosted payload left right).cost <= queryCost
  query_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len : Nat},
          0 < len ->
            left + len <= n ->
              (queryEncodedCosted
                (EncodingLowerBound.canonicalShapePayload shape ++
                  encodeAux (buildAux shape))
                left (left + len)).erase =
                  some (scanWindow shape.representative left len)

namespace BroadwordRMQDirectory

private theorem take_append_replicate_of_lengths
    {alpha : Type} (xs ys : List alpha) (pad : Nat) (x : alpha)
    {xsLen ysLen : Nat}
    (hxs : xs.length = xsLen) (hys : ys.length = ysLen) :
    ((xs ++ ys) ++ List.replicate pad x).take (xsLen + ysLen) =
      xs ++ ys := by
  have hlen : (xs ++ ys).length = xsLen + ysLen := by
    simp [hxs, hys]
  calc
    ((xs ++ ys) ++ List.replicate pad x).take (xsLen + ysLen) =
        ((xs ++ ys) ++ List.replicate pad x).take (xs ++ ys).length := by
      rw [hlen]
    _ = (xs ++ ys).take (xs ++ ys).length := by
      rw [List.take_append_of_le_length (Nat.le_refl _)]
    _ = xs ++ ys := by
      rw [List.take_of_length_le (Nat.le_refl _)]

def State {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) : Type :=
  Cartesian.CartesianShape × directory.Aux

def buildState {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) : directory.State :=
  (shape, directory.buildAux shape)

def encodeState {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) : List Bool :=
  EncodingLowerBound.canonicalShapePayload state.1 ++
    directory.encodeAux state.2

def queryStateCosted {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) : Costed (Option Nat) :=
  directory.queryEncodedCosted (directory.encodeState state) left right

theorem queryStateCosted_cost_le
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) :
    (directory.queryStateCosted state left right).cost <= queryCost := by
  exact directory.query_cost_le (directory.encodeState state) left right

theorem queryStateCosted_exact
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryStateCosted (directory.buildState shape)
        left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  exact directory.query_exact hshape hlen hbound

/-- Forget a certified broadword directory to the existing exact RMQ payload API. -/
def stateEncoding
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.ExactRMQStateEncoding n (2 * n + overhead) where
  State := directory.State
  buildState := directory.buildState
  encodeState := directory.encodeState
  queryEncoded := fun payload left right =>
    (directory.queryEncodedCosted payload left right).erase
  sample shape := shape.representative
  length_eq := by
    intro shape hshape
    have hshapePayload :
        (EncodingLowerBound.canonicalShapePayload shape).length = 2 * n := by
      simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
        (EncodingLowerBound.canonicalRepresentativeStateEncoding n).length_eq
          hshape
    have haux := directory.aux_length_eq hshape
    simp [encodeState, buildState, hshapePayload, haux]
  sample_length_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_length_eq
        hshape
  sample_shape_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_shape_eq
        hshape
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.query_exact hshape hlen hbound

theorem payloadBitCount_eq
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((directory.stateEncoding).payloadView).payloadBitCount
        ((directory.stateEncoding).buildState shape) =
      2 * n + overhead := by
  exact
    EncodingLowerBound.ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem
      directory.stateEncoding hshape

/-- Payload-space bounds induced by a certified broadword directory. -/
def payloadSpaceBounds
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    LowerBound.PayloadSpaceBounds
      (Cartesian.shapesOfSize n)
      (EncodingLowerBound.logSlackLower n)
      (2 * n + overhead) where
  nodup := Cartesian.shapesOfSize_nodup n
  count_lower := by
    simpa [EncodingLowerBound.logSlackLower, Cartesian.shapeCount] using
      EncodingLowerBound.shapeCount_log_lower_of_quadratic_bound
        (EncodingLowerBound.shapeCount_quadratic_lower n)
  upperEncoding := directory.stateEncoding.payloadLosslessEncoding

theorem payloadSpaceBounds_lower_le_upper
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  exact directory.payloadSpaceBounds.lower_le_upper

theorem logSlackLower_le_payloadBudget
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  have hbudget :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          ((directory.stateEncoding).payloadView).payloadBitCount
            ((directory.stateEncoding).buildState shape) <=
              2 * n + overhead := by
    intro shape hmem
    rw [directory.payloadBitCount_eq hmem]
    exact Nat.le_refl _
  exact
    EncodingLowerBound.logSlackLower_le_budget_of_exactRMQStateEncoding
      directory.stateEncoding hshape hbudget

/--
Pad a certified directory to a larger published overhead budget.

This is useful when a concrete construction has an exact auxiliary encoding
length but the final theorem wants a cleaner upper-bound expression.  The query
decoder truncates the padded payload back to the original exact prefix, so the
query proof and query-cost bound are preserved rather than re-assumed.
-/
def padToOverhead
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget) :
    BroadwordRMQDirectory n budget queryCost where
  Aux := directory.Aux
  buildAux := directory.buildAux
  encodeAux aux :=
    directory.encodeAux aux ++ List.replicate (budget - overhead) false
  queryEncodedCosted payload left right :=
    directory.queryEncodedCosted (payload.take (2 * n + overhead)) left right
  aux_length_eq := by
    intro shape hshape
    have haux := directory.aux_length_eq hshape
    simp [haux]
    omega
  query_cost_le := by
    intro payload left right
    exact directory.query_cost_le (payload.take (2 * n + overhead)) left right
  query_exact := by
    intro shape hshape left len hlen hbound
    have hshapePayload :
        (EncodingLowerBound.canonicalShapePayload shape).length = 2 * n := by
      simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
        (EncodingLowerBound.canonicalRepresentativeStateEncoding n).length_eq
          hshape
    have haux := directory.aux_length_eq hshape
    have htake :
        ((EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape)) ++
              List.replicate (budget - overhead) false).take
            (2 * n + overhead) =
          EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape) :=
      take_append_replicate_of_lengths
        (EncodingLowerBound.canonicalShapePayload shape)
        (directory.encodeAux (directory.buildAux shape))
        (budget - overhead) false hshapePayload haux
    have hexact := directory.query_exact hshape hlen hbound
    have hpayload :
        (EncodingLowerBound.canonicalShapePayload shape ++
            (directory.encodeAux (directory.buildAux shape) ++
              List.replicate (budget - overhead) false)).take
            (2 * n + overhead) =
          EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape) := by
      simpa [List.append_assoc] using htake
    simpa [hpayload] using hexact

theorem padToOverhead_payloadBitCount_eq
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((((directory.padToOverhead hbudget).stateEncoding).payloadView).payloadBitCount
        (((directory.padToOverhead hbudget).stateEncoding).buildState shape)) =
      2 * n + budget := by
  exact (directory.padToOverhead hbudget).payloadBitCount_eq hshape

theorem padToOverhead_queryStateCosted_cost_le
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget)
    (state : (directory.padToOverhead hbudget).State)
    (left right : Nat) :
    ((directory.padToOverhead hbudget).queryStateCosted state left right).cost <=
      queryCost := by
  exact (directory.padToOverhead hbudget).queryStateCosted_cost_le
    state left right

end BroadwordRMQDirectory

/--
A family of certified broadword RMQ directories with one query-cost constant and
sublinear auxiliary payload overhead.
-/
structure BroadwordSuccinctRMQFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat, BroadwordRMQDirectory n (overhead n) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BroadwordSuccinctRMQFamily

/--
The theorem shape for a researcher-facing `2*n + o(n)`, constant-query RMQ
upper bound in the word-RAM model.

The statement keeps all anti-vacuity witnesses visible: each size has an exact
RMQ state encoding, every on-domain built state charges exactly `2*n + overhead
n` payload bits, every supplied broadword query costs at most `queryCost`, and
valid queries refine the canonical representative RMQ answer.
-/
theorem two_n_plus_o_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BroadwordSuccinctRMQFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((((family.directory n).stateEncoding).payloadView).payloadBitCount
              (((family.directory n).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall (state : (family.directory n).State) left right,
          ((family.directory n).queryStateCosted state left right).cost <=
            queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryStateCosted
                    ((family.directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact (family.directory n).payloadSpaceBounds_lower_le_upper
    · constructor
      · intro shape hshape
        exact (family.directory n).payloadBitCount_eq hshape
      · constructor
        · intro state left right
          exact (family.directory n).queryStateCosted_cost_le state left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryStateCosted_exact hshape hlen hbound

end BroadwordSuccinctRMQFamily

/--
Canonical componentized auxiliary-budget shape for the eventual
balanced-parentheses broadword directory.

The four slots are intentionally generic: rank directory, select directory,
excess/RMQ navigation directory, and fixed microtable/block metadata.  Concrete
implementations can set unused components to zero.
-/
def bpAuxOverhead
    (rank select excess micro : Nat -> Nat) (n : Nat) : Nat :=
  rank n + select n + excess n + micro n

theorem bpAuxOverhead_littleO
    {rank select excess micro : Nat -> Nat}
    (hrank : LittleOLinear rank)
    (hselect : LittleOLinear select)
    (hexcess : LittleOLinear excess)
    (hmicro : LittleOLinear micro) :
    LittleOLinear (bpAuxOverhead rank select excess micro) := by
  unfold bpAuxOverhead
  exact ((hrank.add hselect).add hexcess).add hmicro

def sampledBPAuxOverhead
    (rankSlots selectSlots excessSlots microSlots : Nat) : Nat -> Nat :=
  bpAuxOverhead
    (sampledDirectoryOverhead rankSlots)
    (sampledDirectoryOverhead selectSlots)
    (sampledDirectoryOverhead excessSlots)
    (sampledDirectoryOverhead microSlots)

theorem sampledBPAuxOverhead_littleO
    (rankSlots selectSlots excessSlots microSlots : Nat) :
    LittleOLinear
      (sampledBPAuxOverhead rankSlots selectSlots excessSlots microSlots) := by
  unfold sampledBPAuxOverhead
  exact bpAuxOverhead_littleO
    (sampledDirectoryOverhead_littleO rankSlots)
    (sampledDirectoryOverhead_littleO selectSlots)
    (sampledDirectoryOverhead_littleO excessSlots)
    (sampledDirectoryOverhead_littleO microSlots)

/--
BP-native certified word-RAM/broadword directory for exact RMQ over
Cartesian-shape representatives of size `n`.

Unlike `BroadwordRMQDirectory`, whose base payload is the decoder-oriented
`canonicalShapePayload`, this interface stores the literal balanced-parentheses
code `shape.bpCode` as the counted `2*n` payload.  This is the representation
boundary expected by a packed BP/rank-select RMQ construction.
-/
structure BPBroadwordRMQDirectory
    (n overhead queryCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  queryEncodedCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  query_cost_le :
    forall payload left right,
      (queryEncodedCosted payload left right).cost <= queryCost
  query_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len : Nat},
          0 < len ->
            left + len <= n ->
              (queryEncodedCosted
                (shape.bpCode ++ encodeAux (buildAux shape))
                left (left + len)).erase =
                  some (scanWindow shape.representative left len)

namespace BPBroadwordRMQDirectory

def State {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) : Type :=
  Cartesian.CartesianShape × directory.Aux

def buildState {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) : directory.State :=
  (shape, directory.buildAux shape)

def encodeState {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) : List Bool :=
  state.1.bpCode ++ directory.encodeAux state.2

def queryStateCosted {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) : Costed (Option Nat) :=
  directory.queryEncodedCosted (directory.encodeState state) left right

theorem queryStateCosted_cost_le
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) :
    (directory.queryStateCosted state left right).cost <= queryCost := by
  exact directory.query_cost_le (directory.encodeState state) left right

theorem queryStateCosted_exact
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryStateCosted (directory.buildState shape)
        left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  exact directory.query_exact hshape hlen hbound

/-- Forget a BP-native directory to the existing exact RMQ payload API. -/
def stateEncoding
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.ExactRMQStateEncoding n (2 * n + overhead) where
  State := directory.State
  buildState := directory.buildState
  encodeState := directory.encodeState
  queryEncoded := fun payload left right =>
    (directory.queryEncodedCosted payload left right).erase
  sample shape := shape.representative
  length_eq := by
    intro shape hshape
    have hshapePayload :
        shape.bpCode.length = 2 * n :=
      Cartesian.CartesianShape.bpCode_length_of_shapeOfSize
        (Cartesian.mem_shapesOfSize_shapeOfSize hshape)
    have haux := directory.aux_length_eq hshape
    simp [encodeState, buildState, hshapePayload, haux]
  sample_length_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_length_eq
        hshape
  sample_shape_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_shape_eq
        hshape
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.query_exact hshape hlen hbound

theorem payloadOf_eq
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) :
    (directory.stateEncoding).payloadOf shape =
      shape.bpCode ++ directory.encodeAux (directory.buildAux shape) := by
  rfl

theorem payloadBitCount_eq
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((directory.stateEncoding).payloadView).payloadBitCount
        ((directory.stateEncoding).buildState shape) =
      2 * n + overhead := by
  exact
    EncodingLowerBound.ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem
      directory.stateEncoding hshape

/-- Payload-space bounds induced by a BP-native broadword directory. -/
def payloadSpaceBounds
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    LowerBound.PayloadSpaceBounds
      (Cartesian.shapesOfSize n)
      (EncodingLowerBound.logSlackLower n)
      (2 * n + overhead) where
  nodup := Cartesian.shapesOfSize_nodup n
  count_lower := by
    simpa [EncodingLowerBound.logSlackLower, Cartesian.shapeCount] using
      EncodingLowerBound.shapeCount_log_lower_of_quadratic_bound
        (EncodingLowerBound.shapeCount_quadratic_lower n)
  upperEncoding := directory.stateEncoding.payloadLosslessEncoding

theorem payloadSpaceBounds_lower_le_upper
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  exact directory.payloadSpaceBounds.lower_le_upper

end BPBroadwordRMQDirectory

/--
Stored one-read directory for the BP LCA-close primitive.

Given the close positions of two inorder endpoints, this component reads a
stored navigation table and returns the close position of their BP LCA.  The
table is intentionally separated from the select/rank plumbing below: stored
rank/select now has its own faithful component theorem, while this table is the
remaining navigation slot for the broadword/microtable implementation.
-/
structure StoredBPCloseLCADirectory
    (n overhead : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  decodeTable : List Bool -> TableModel.IndexedSeq (Option Nat)
  slotIndex : Nat -> Nat -> Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  entry_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  (decodeTable
                    (shape.bpCode ++ encodeAux (buildAux shape))).get?
                      (slotIndex leftClose rightClose) =
                    some
                      (bpCloseOfInorder? shape
                        (scanWindow shape.representative left len))

namespace StoredBPCloseLCADirectory

def lcaCloseCosted
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((directory.decodeTable payload).getCosted
      (directory.slotIndex leftClose rightClose))

theorem lcaCloseCosted_cost
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted payload leftClose rightClose).cost =
      TableModel.indexedReadCost := by
  simp [lcaCloseCosted, Costed.map_cost,
    TableModel.IndexedSeq.getCosted_cost]

theorem lcaCloseCosted_cost_le_one
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted payload leftClose rightClose).cost <= 1 := by
  simp [directory.lcaCloseCosted_cost payload leftClose rightClose,
    TableModel.indexedReadCost]

theorem lcaCloseCosted_exact
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len) (hbound : left + len <= n)
    (hleftClose : bpCloseOfInorder? shape left = some leftClose)
    (hrightClose :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    (directory.lcaCloseCosted
      (shape.bpCode ++ directory.encodeAux (directory.buildAux shape))
      leftClose rightClose).erase =
        bpCloseOfInorder? shape
          (scanWindow shape.representative left len) := by
  have hentry :=
    directory.entry_exact hshape hlen hbound hleftClose hrightClose
  simp [lcaCloseCosted, TableModel.IndexedSeq.getCosted,
    TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
    Costed.map, hentry]

theorem profile
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.encodeAux (directory.buildAux shape)).length =
          overhead) /\
      (forall payload leftClose rightClose,
        (directory.lcaCloseCosted payload leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (directory.lcaCloseCosted
                      (shape.bpCode ++
                        directory.encodeAux (directory.buildAux shape))
                      leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.aux_length_eq hshape
  · constructor
    · intro payload leftClose rightClose
      exact directory.lcaCloseCosted_cost_le_one payload leftClose rightClose
    · intro shape hshape left len leftClose rightClose
        hlen hbound hleftClose hrightClose
      exact directory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose

end StoredBPCloseLCADirectory

/--
Payload-live one-read directory for the BP LCA-close primitive.

This is the representation-refinement version of `StoredBPCloseLCADirectory`:
the built auxiliary state carries a fixed-width optional-Nat table, and the
query reads that table directly.  It still leaves the asymptotically succinct
construction of the table to the final navigation implementation.
-/
structure PayloadLiveBPCloseLCADirectory
    (n overhead : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  fieldWidth : Nat
  entries : Aux -> List (Option Nat)
  table : (aux : Aux) -> FixedWidthOptionNatTable (entries aux) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        ((table (buildAux shape)).payload).length = overhead
  entry_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  ((table (buildAux shape)).readCosted
                    (slotIndex leftClose rightClose)).erase =
                    some
                      (bpCloseOfInorder? shape
                        (scanWindow shape.representative left len))

namespace PayloadLiveBPCloseLCADirectory

def encodeAux
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) : List Bool :=
  (directory.table aux).payload

def lcaCloseCosted
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((directory.table aux).readCosted
      (directory.slotIndex leftClose rightClose))

theorem lcaCloseCosted_cost
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted aux leftClose rightClose).cost = 1 := by
  simp [lcaCloseCosted, Costed.map_cost]

theorem lcaCloseCosted_cost_le_one
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted aux leftClose rightClose).cost <= 1 := by
  simp [directory.lcaCloseCosted_cost aux leftClose rightClose]

theorem lcaCloseCosted_exact
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len) (hbound : left + len <= n)
    (hleftClose : bpCloseOfInorder? shape left = some leftClose)
    (hrightClose :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    (directory.lcaCloseCosted (directory.buildAux shape)
      leftClose rightClose).erase =
        bpCloseOfInorder? shape
          (scanWindow shape.representative left len) := by
  have hentry :=
    directory.entry_exact hshape hlen hbound hleftClose hrightClose
  simp [lcaCloseCosted, Costed.erase_map, hentry]

theorem profile
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.encodeAux (directory.buildAux shape)).length =
          overhead) /\
      (forall aux leftClose rightClose,
        (directory.lcaCloseCosted aux leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (directory.lcaCloseCosted
                      (directory.buildAux shape)
                      leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.aux_length_eq hshape
  · constructor
    · intro aux leftClose rightClose
      exact directory.lcaCloseCosted_cost_le_one aux leftClose rightClose
    · intro shape hshape left len leftClose rightClose
        hlen hbound hleftClose hrightClose
      exact directory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose

/--
Build a payload-live BP LCA-close directory from fixed-width optional entries.

This is only a representation constructor: the caller still supplies the actual
navigation entries, their field-width bound, and the semantic exactness proof.
It keeps the one-read query path tied to the counted fixed-width payload table.
-/
def ofEntries
    (n overhead fieldWidth : Nat)
    (Aux : Type)
    (buildAux : Cartesian.CartesianShape -> Aux)
    (entries : Aux -> List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall (aux : Aux) {entry : Option Nat} {value : Nat},
        List.Mem entry (entries aux) ->
          entry = some value -> value < 2 ^ fieldWidth)
    (hlength :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (entries (buildAux shape)).length *
              optionNatWordWidth fieldWidth =
            overhead)
    (hentryExact :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (entries (buildAux shape))[
                        slotIndex leftClose rightClose]? =
                      some
                        (bpCloseOfInorder? shape
                          (scanWindow shape.representative left len))) :
    PayloadLiveBPCloseLCADirectory n overhead where
  Aux := Aux
  buildAux := buildAux
  fieldWidth := fieldWidth
  entries := entries
  table aux :=
    FixedWidthOptionNatTable.ofEntries
      (entries aux) fieldWidth (hentryBound aux)
  slotIndex := slotIndex
  aux_length_eq := by
    intro shape hshape
    simpa [FixedWidthOptionNatTable.payload_length]
      using hlength hshape
  entry_exact := by
    intro shape hshape left len leftClose rightClose
      hlen hbound hleftClose hrightClose
    simpa using
      hentryExact hshape hlen hbound hleftClose hrightClose

theorem ofEntries_profile
    (n overhead fieldWidth : Nat)
    (Aux : Type)
    (buildAux : Cartesian.CartesianShape -> Aux)
    (entries : Aux -> List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall (aux : Aux) {entry : Option Nat} {value : Nat},
        List.Mem entry (entries aux) ->
          entry = some value -> value < 2 ^ fieldWidth)
    (hlength :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (entries (buildAux shape)).length *
              optionNatWordWidth fieldWidth =
            overhead)
    (hentryExact :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (entries (buildAux shape))[
                        slotIndex leftClose rightClose]? =
                      some
                        (bpCloseOfInorder? shape
                          (scanWindow shape.representative left len))) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
          hentryBound hlength hentryExact).encodeAux
            ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
              hentryBound hlength hentryExact).buildAux shape)).length =
          overhead) /\
      (forall aux leftClose rightClose,
        ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
          hentryBound hlength hentryExact).lcaCloseCosted
            aux leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    ((ofEntries n overhead fieldWidth Aux buildAux entries
                      slotIndex hentryBound hlength hentryExact).lcaCloseCosted
                        ((ofEntries n overhead fieldWidth Aux buildAux entries
                          slotIndex hentryBound hlength hentryExact).buildAux
                            shape)
                        leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  exact
    (ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
      hentryBound hlength hentryExact).profile

end PayloadLiveBPCloseLCADirectory

/-- Family of stored one-read BP LCA-close directories. -/
structure StoredBPCloseLCAFamily
    (overhead : Nat -> Nat) where
  directory :
    forall n : Nat, StoredBPCloseLCADirectory n (overhead n)
  overhead_littleO : LittleOLinear overhead

namespace StoredBPCloseLCAFamily

theorem constant_lca_close_profile
    {overhead : Nat -> Nat}
    (family : StoredBPCloseLCAFamily overhead) :
    LittleOLinear overhead /\
      forall n : Nat,
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).encodeAux
              ((family.directory n).buildAux shape)).length =
              overhead n) /\
        (forall payload leftClose rightClose,
          ((family.directory n).lcaCloseCosted
            payload leftClose rightClose).cost <= 1) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len leftClose rightClose : Nat},
              0 < len ->
                left + len <= n ->
                  bpCloseOfInorder? shape left = some leftClose ->
                    bpCloseOfInorder? shape (left + len - 1) =
                        some rightClose ->
                      ((family.directory n).lcaCloseCosted
                        (shape.bpCode ++
                          (family.directory n).encodeAux
                            ((family.directory n).buildAux shape))
                        leftClose rightClose).erase =
                        bpCloseOfInorder? shape
                          (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    exact (family.directory n).profile

end StoredBPCloseLCAFamily

/--
BP close-navigation RMQ directory.

This is the BP/LCA query skeleton: select the close parenthesis for the two
endpoint inorder nodes, compute the close parenthesis of their BP-LCA, then use
rank over closing parentheses to recover the inorder/RMQ index.  The primitive
navigation operation is abstract, but the endpoint/rank plumbing is proved
once here.
-/
structure BPCloseRMQNavigationDirectory
    (n overhead selectCost lcaCost rankCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  selectCloseCosted : List Bool -> Nat -> Costed (Option Nat)
  lcaCloseCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  rankCloseCosted : List Bool -> Nat -> Costed Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  select_cost_le :
    forall payload occurrence,
      (selectCloseCosted payload occurrence).cost <= selectCost
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseCosted payload leftClose rightClose).cost <= lcaCost
  rank_cost_le :
    forall payload pos,
      (rankCloseCosted payload pos).cost <= rankCost
  select_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {idx : Nat},
          idx < n ->
            (selectCloseCosted
              (shape.bpCode ++ encodeAux (buildAux shape))
              idx).erase =
                bpCloseOfInorder? shape idx
  lca_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  (lcaCloseCosted
                    (shape.bpCode ++ encodeAux (buildAux shape))
                    leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)
  rank_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {idx close : Nat},
          bpCloseOfInorder? shape idx = some close ->
            (rankCloseCosted
              (shape.bpCode ++ encodeAux (buildAux shape))
              (close + 1)).erase =
                Succinct.rankPrefix false shape.bpCode (close + 1)

namespace BPCloseRMQNavigationDirectory

def queryEncodedCosted
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    (payload : List Bool) (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (directory.selectCloseCosted payload left) fun leftClose? =>
    Costed.bind (directory.selectCloseCosted payload (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (directory.lcaCloseCosted payload leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (directory.rankCloseCosted payload (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem queryEncodedCosted_cost_le
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    (payload : List Bool) (left right : Nat) :
    (directory.queryEncodedCosted payload left right).cost <=
      2 * selectCost + lcaCost + rankCost := by
  unfold queryEncodedCosted
  have hleft := directory.select_cost_le payload left
  have hright := directory.select_cost_le payload (right - 1)
  cases hleftValue : (directory.selectCloseCosted payload left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          (directory.selectCloseCosted payload (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            directory.lca_cost_le payload leftClose rightClose
          cases hlcaValue :
              (directory.lcaCloseCosted payload leftClose rightClose).value with
          | none =>
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                directory.rank_cost_le payload (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem queryEncodedCosted_exact
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryEncodedCosted
      (shape.bpCode ++ directory.encodeAux (directory.buildAux shape))
      left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hreprLen : shape.representative.length = n := by
    rw [Cartesian.CartesianShape.representative_length,
      Cartesian.ShapeOfSize.size_eq hshapeSize]
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len (by omega)
  have hscanLt : scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :=
    directory.select_close_exact hshape (idx := left) hleftLt
  have hselectRight :=
    directory.select_close_exact hshape
      (idx := left + len - 1) hrightLt
  have hlca :=
    directory.lca_close_exact hshape hlen hbound
      hleftClose hrightClose
  have hrank :=
    directory.rank_close_exact hshape hanswerClose
  have hrankRecover :=
    bpCloseOfInorder?_rankFalse_succ shape hanswerClose
  unfold queryEncodedCosted
  simp [Costed.erase_bind, Costed.erase_map, hselectLeft, hleftClose,
    hselectRight, hrightClose, hlca, hanswerClose, hrank, hrankRecover]

def toBPBroadwordRMQDirectory
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost) :
    BPBroadwordRMQDirectory n overhead
      (2 * selectCost + lcaCost + rankCost) where
  Aux := directory.Aux
  buildAux := directory.buildAux
  encodeAux := directory.encodeAux
  queryEncodedCosted := directory.queryEncodedCosted
  aux_length_eq := by
    intro shape hshape
    exact directory.aux_length_eq hshape
  query_cost_le := by
    intro payload left right
    exact directory.queryEncodedCosted_cost_le payload left right
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.queryEncodedCosted_exact hshape hlen hbound

end BPCloseRMQNavigationDirectory

/-- Family form of the BP close-navigation RMQ adapter. -/
structure BPCloseRMQNavigationFamily
    (overhead : Nat -> Nat) (selectCost lcaCost rankCost : Nat) where
  directory :
    forall n : Nat,
      BPCloseRMQNavigationDirectory
        n (overhead n) selectCost lcaCost rankCost
  overhead_littleO : LittleOLinear overhead

namespace BPCloseRMQNavigationFamily

theorem two_n_plus_o_close_navigation_profile
    {overhead : Nat -> Nat} {selectCost lcaCost rankCost : Nat}
    (family :
      BPCloseRMQNavigationFamily
        overhead selectCost lcaCost rankCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadOf shape =
              shape.bpCode ++
                ((family.directory n).toBPBroadwordRMQDirectory).encodeAux
                  (((family.directory n).toBPBroadwordRMQDirectory).buildAux shape)) /\
            (((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadView).payloadBitCount
              ((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall
          (state : ((family.directory n).toBPBroadwordRMQDirectory).State)
          left right,
          (((family.directory n).toBPBroadwordRMQDirectory).queryStateCosted
            state left right).cost <=
              2 * selectCost + lcaCost + rankCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (((family.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                    (((family.directory n).toBPBroadwordRMQDirectory).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact
        BPBroadwordRMQDirectory.payloadSpaceBounds_lower_le_upper
          ((family.directory n).toBPBroadwordRMQDirectory)
    · constructor
      · intro shape hshape
        exact
          ⟨BPBroadwordRMQDirectory.payloadOf_eq
              ((family.directory n).toBPBroadwordRMQDirectory) shape,
            BPBroadwordRMQDirectory.payloadBitCount_eq
              ((family.directory n).toBPBroadwordRMQDirectory) hshape⟩
      · constructor
        · intro state left right
          exact
            BPBroadwordRMQDirectory.queryStateCosted_cost_le
              ((family.directory n).toBPBroadwordRMQDirectory)
              state left right
        · intro shape hshape left len hlen hbound
          exact
            BPBroadwordRMQDirectory.queryStateCosted_exact
              ((family.directory n).toBPBroadwordRMQDirectory)
              hshape hlen hbound

end BPCloseRMQNavigationFamily

/-- Auxiliary budget for the payload-live BP close-navigation construction. -/
def bpCloseNavigationOverhead
    (rank select lca : Nat -> Nat) (n : Nat) : Nat :=
  rank n + select n + lca n

theorem bpCloseNavigationOverhead_littleO
    {rank select lca : Nat -> Nat}
    (hrank : LittleOLinear rank)
    (hselect : LittleOLinear select)
    (hlca : LittleOLinear lca) :
    LittleOLinear (bpCloseNavigationOverhead rank select lca) := by
  unfold bpCloseNavigationOverhead
  exact (hrank.add hselect).add hlca

/--
Payload-live BP close-navigation RMQ directory for built Cartesian shapes.

Unlike the retired one-read RMQ answer-table boundary, this query is an explicit
composition: select the two close parentheses, read the BP LCA-close navigation
entry, and rank that close position back to an inorder index.  The component
stores are tied to counted payload words by their own payload-live profiles.
-/
structure PayloadLiveBPCloseRMQNavigationDirectory
    (n rankOverhead selectOverhead lcaOverhead : Nat) where
  rankData :
    (shape : Cartesian.CartesianShape) ->
      PayloadLiveStoredWordRankData
        shape.bpCode rankOverhead
  selectData :
    (shape : Cartesian.CartesianShape) ->
      PayloadLiveStoredWordSelectData
        shape.bpCode selectOverhead
  lcaDirectory : PayloadLiveBPCloseLCADirectory n lcaOverhead

namespace PayloadLiveBPCloseRMQNavigationDirectory

def overhead
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (_directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) : Nat :=
  rankOverhead + selectOverhead + lcaOverhead

def encodeAux
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) : List Bool :=
  (directory.rankData shape).auxPayload ++
    (directory.selectData shape).auxPayload ++
      directory.lcaDirectory.encodeAux
        (directory.lcaDirectory.buildAux shape)

def payload
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) : List Bool :=
  shape.bpCode ++ directory.encodeAux shape

def selectCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Costed (Option Nat) :=
  (directory.selectData shape).selectCosted false idx

def lcaCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  directory.lcaDirectory.lcaCloseCosted
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

def rankCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    Costed Nat :=
  (directory.rankData shape).rankCostedClamped false pos

def queryBuiltCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.selectCloseCosted shape left) fun leftClose? =>
    Costed.bind (directory.selectCloseCosted shape (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (directory.lcaCloseCosted shape leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (directory.rankCloseCosted shape (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem encodeAux_length
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.encodeAux shape).length =
      rankOverhead + selectOverhead + lcaOverhead := by
  have hrank : (directory.rankData shape).auxPayload.length = rankOverhead :=
    (directory.rankData shape).auxPayload_length
  have hselect :
      (directory.selectData shape).auxPayload.length = selectOverhead :=
    (directory.selectData shape).auxPayload_length
  have hlca :
      (directory.lcaDirectory.encodeAux
          (directory.lcaDirectory.buildAux shape)).length =
        lcaOverhead :=
    directory.lcaDirectory.aux_length_eq (shape := shape) hshape
  simp [encodeAux, hrank, hselect, hlca]
  omega

theorem payload_length
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.payload shape).length =
      2 * n + (rankOverhead + selectOverhead + lcaOverhead) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n := by
    exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux := directory.encodeAux_length hshape
  simp [payload, hbp, haux]

theorem selectCloseCosted_cost_le_three
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).cost <= 3 := by
  exact (directory.selectData shape).selectCosted_cost_le_three false idx

theorem lcaCloseCosted_cost_le_one
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted shape leftClose rightClose).cost <= 1 := by
  exact directory.lcaDirectory.lcaCloseCosted_cost_le_one
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

theorem rankCloseCosted_cost_le_three
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).cost <= 3 := by
  exact (directory.rankData shape).rankCostedClamped_cost_le_three false pos

theorem queryBuiltCosted_cost_le_ten
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (directory.queryBuiltCosted shape left right).cost <= 10 := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft :=
    (directory.selectData shape).selectCosted_cost_le_three false left
  have hright :=
    (directory.selectData shape).selectCosted_cost_le_three
      false (right - 1)
  cases hleftValue :
      ((directory.selectData shape).selectCosted false left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((directory.selectData shape).selectCosted false (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            directory.lcaDirectory.lcaCloseCosted_cost_le_one
              (directory.lcaDirectory.buildAux shape) leftClose rightClose
          cases hlcaValue :
              (directory.lcaDirectory.lcaCloseCosted
                (directory.lcaDirectory.buildAux shape)
                leftClose rightClose).value with
          | none =>
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (directory.rankData shape).rankCostedClamped_cost_le_three
                  false (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem selectCloseCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).erase =
      bpCloseOfInorder? shape idx := by
  calc
    (directory.selectCloseCosted shape idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact (directory.selectData shape).selectCosted_exact false idx
    _ = bpCloseOfInorder? shape idx := by
      exact select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact (directory.rankData shape).rankCostedClamped_exact false pos

theorem queryBuiltCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryBuiltCosted shape left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (directory.selectCloseCosted shape left).value =
        some leftClose := by
    have h := directory.selectCloseCosted_exact shape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (directory.selectCloseCosted shape (left + len - 1)).value =
        some rightClose := by
    have h := directory.selectCloseCosted_exact shape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (directory.lcaCloseCosted shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      directory.lcaDirectory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose
    simpa [Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (directory.rankCloseCosted shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact := directory.rankCloseCosted_exact shape (answerClose + 1)
    have hrankRecover :=
      bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (directory.rankCloseCosted shape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hselectLeftRaw :
      ((directory.selectData shape).selectCosted false left).value =
        some leftClose := by
    simpa [selectCloseCosted] using hselectLeft
  have hselectRightRaw :
      ((directory.selectData shape).selectCosted false (left + len - 1)).value =
        some rightClose := by
    simpa [selectCloseCosted] using hselectRight
  have hlcaRaw :
      (directory.lcaDirectory.lcaCloseCosted
          (directory.lcaDirectory.buildAux shape)
          leftClose rightClose).value =
        some answerClose := by
    simpa [lcaCloseCosted] using hlca
  have hrankRaw :
      ((directory.rankData shape).rankCostedClamped false
          (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted, Costed.erase,
    Costed.bind, Costed.map, Costed.pure,
    hselectLeftRaw, hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem profile
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.payload shape).length =
          2 * n + (rankOverhead + selectOverhead + lcaOverhead)) /\
      (forall shape left right,
        (directory.queryBuiltCosted shape left right).cost <= 10) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (directory.queryBuiltCosted shape left (left + len)).erase =
                  some (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.payload_length hshape
  · constructor
    · intro shape left right
      exact directory.queryBuiltCosted_cost_le_ten shape left right
    · intro shape hshape left len hlen hbound
      exact directory.queryBuiltCosted_exact hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationDirectory

/--
Payload-only component view for a payload-live BP close-navigation directory.

The functions in this view are the only operations used by the encoded query.
The agreement fields certify that, on payloads produced by the built directory,
they are extensionally the same as the stateful component queries.  This is the
honest bridge toward `BPBroadwordRMQDirectory`: no payload decoder or shape
reconstruction is hidden in the bridge theorem.
-/
structure EncodedPayloadLiveBPCloseRMQNavigationView
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) where
  selectCloseEncoded : List Bool -> Nat -> Costed (Option Nat)
  lcaCloseEncoded : List Bool -> Nat -> Nat -> Costed (Option Nat)
  rankCloseEncoded : List Bool -> Nat -> Costed Nat
  select_cost_le :
    forall payload idx, (selectCloseEncoded payload idx).cost <= 3
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseEncoded payload leftClose rightClose).cost <= 1
  rank_cost_le :
    forall payload pos, (rankCloseEncoded payload pos).cost <= 3
  select_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall idx,
          selectCloseEncoded (directory.payload shape) idx =
            directory.selectCloseCosted shape idx
  lca_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall leftClose rightClose,
          lcaCloseEncoded (directory.payload shape)
              leftClose rightClose =
            directory.lcaCloseCosted shape leftClose rightClose
  rank_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall pos,
          rankCloseEncoded (directory.payload shape) pos =
            directory.rankCloseCosted shape pos

namespace EncodedPayloadLiveBPCloseRMQNavigationView

def toBPCloseRMQNavigationDirectory
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    {directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead}
    (view : EncodedPayloadLiveBPCloseRMQNavigationView directory) :
    BPCloseRMQNavigationDirectory n
      (rankOverhead + selectOverhead + lcaOverhead) 3 1 3 where
  Aux := Cartesian.CartesianShape
  buildAux shape := shape
  encodeAux shape := directory.encodeAux shape
  selectCloseCosted := view.selectCloseEncoded
  lcaCloseCosted := view.lcaCloseEncoded
  rankCloseCosted := view.rankCloseEncoded
  aux_length_eq := by
    intro shape hshape
    exact directory.encodeAux_length hshape
  select_cost_le := by
    intro payload idx
    exact view.select_cost_le payload idx
  lca_cost_le := by
    intro payload leftClose rightClose
    exact view.lca_cost_le payload leftClose rightClose
  rank_cost_le := by
    intro payload pos
    exact view.rank_cost_le payload pos
  select_close_exact := by
    intro shape hshape idx hidx
    have hagree := view.select_agrees_on_built_payload hshape idx
    calc
      (view.selectCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape) idx).erase =
          (directory.selectCloseCosted shape idx).erase := by
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = bpCloseOfInorder? shape idx := by
            exact directory.selectCloseCosted_exact shape idx
  lca_close_exact := by
    intro shape hshape left len leftClose rightClose
      hlen hbound hleftClose hrightClose
    have hagree :=
      view.lca_agrees_on_built_payload hshape leftClose rightClose
    calc
      (view.lcaCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          leftClose rightClose).erase =
          (directory.lcaCloseCosted shape leftClose rightClose).erase := by
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = bpCloseOfInorder? shape
            (scanWindow shape.representative left len) := by
            exact directory.lcaDirectory.lcaCloseCosted_exact
              hshape hlen hbound hleftClose hrightClose
  rank_close_exact := by
    intro shape hshape idx close hclose
    have hagree := view.rank_agrees_on_built_payload hshape (close + 1)
    calc
      (view.rankCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          (close + 1)).erase =
          (directory.rankCloseCosted shape (close + 1)).erase := by
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = Succinct.rankPrefix false shape.bpCode (close + 1) := by
            exact directory.rankCloseCosted_exact shape (close + 1)

end EncodedPayloadLiveBPCloseRMQNavigationView

/-- Family form of the payload-encoded BP close-navigation query. -/
structure EncodedPayloadLiveBPCloseRMQNavigationFamily
    (rank select lca : Nat -> Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory
        n (rank n) (select n) (lca n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  lca_littleO : LittleOLinear lca

namespace EncodedPayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rank select lca : Nat -> Nat}
    (_family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    Nat -> Nat :=
  bpCloseNavigationOverhead rank select lca

def toBPCloseRMQNavigationFamily
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    BPCloseRMQNavigationFamily family.overhead 3 1 3 where
  directory n := (family.view n).toBPCloseRMQNavigationDirectory
  overhead_littleO :=
    bpCloseNavigationOverhead_littleO
      family.rank_littleO family.select_littleO family.lca_littleO

theorem overhead_littleO
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead := by
  exact family.toBPCloseRMQNavigationFamily.overhead_littleO

def Profile
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) : Prop :=
  LittleOLinear family.overhead /\
    forall n : Nat,
      EncodingLowerBound.logSlackLower n <= 2 * n + family.overhead n /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadOf shape =
            shape.bpCode ++
              ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).encodeAux
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildAux shape)) /\
          (((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadView).payloadBitCount
            ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).buildState shape) =
              2 * n + family.overhead n)) /\
      (forall
        (state : ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).State)
        left right,
        (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
          state left right).cost <=
            2 * 3 + 1 + 3) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                  (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildState shape)
                  left (left + len)).erase =
                    some (scanWindow shape.representative left len))

/--
Payload-encoded `2*n + o(n)` close-navigation profile.

The query operates through encoded payload functions only.  The view fields are
the refinement certificates connecting those payload functions back to the
stateful payload-live directory on payloads produced by `buildState`.
-/
theorem two_n_plus_o_encoded_query_profile
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    family.Profile := by
  exact
    BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile
      family.toBPCloseRMQNavigationFamily

end EncodedPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled-envelope payload-encoded BP close-navigation family.

This combines the two current fronts: payload-only encoded component operations
and the canonical sampled-directory `o(n)` auxiliary budget.
-/
structure SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)

namespace SampledEncodedPayloadLiveBPCloseRMQNavigationFamily

def rankOverhead (rankSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead rankSlots

def selectOverhead (selectSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead selectSlots

def lcaOverhead (lcaSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead lcaSlots

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (_family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  bpCloseNavigationOverhead
    (rankOverhead rankSlots)
    (selectOverhead selectSlots)
    (lcaOverhead lcaSlots)

def toEncodedFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    EncodedPayloadLiveBPCloseRMQNavigationFamily
      (rankOverhead rankSlots)
      (selectOverhead selectSlots)
      (lcaOverhead lcaSlots) where
  directory := family.directory
  view := family.view
  rank_littleO := sampledDirectoryOverhead_littleO rankSlots
  select_littleO := sampledDirectoryOverhead_littleO selectSlots
  lca_littleO := sampledDirectoryOverhead_littleO lcaSlots

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toEncodedFamily.overhead_littleO

theorem two_n_plus_o_sampled_encoded_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    family.toEncodedFamily.Profile := by
  exact family.toEncodedFamily.two_n_plus_o_encoded_query_profile

end SampledEncodedPayloadLiveBPCloseRMQNavigationFamily

/-- Family form of the payload-live BP close-navigation query. -/
structure PayloadLiveBPCloseRMQNavigationFamily
    (rank select lca : Nat -> Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory
        n (rank n) (select n) (lca n)
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  lca_littleO : LittleOLinear lca

namespace PayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rank select lca : Nat -> Nat}
    (_family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    Nat -> Nat :=
  bpCloseNavigationOverhead rank select lca

theorem overhead_littleO
    {rank select lca : Nat -> Nat}
    (family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead :=
  bpCloseNavigationOverhead_littleO
    family.rank_littleO family.select_littleO family.lca_littleO

theorem two_n_plus_o_built_query_profile
    {rank select lca : Nat -> Nat}
    (family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · have hbase :=
        EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
      simp [overhead, bpCloseNavigationOverhead]
      omega
    · constructor
      · intro shape hshape
        exact (family.directory n).payload_length hshape
      · constructor
        · intro shape left right
          exact (family.directory n).queryBuiltCosted_cost_le_ten
            shape left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryBuiltCosted_exact
            hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationFamily

/--
Payload-live BP close-navigation family with all auxiliary components budgeted
by the canonical sampled-directory envelope.

This is the narrow sampled-budget capstone: it does not construct a rank/select
or LCA-close scheme, but it fixes the target asymptotic budget that concrete
sampled codecs must meet.
-/
structure SampledPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)

namespace SampledPayloadLiveBPCloseRMQNavigationFamily

def rankOverhead (rankSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead rankSlots

def selectOverhead (selectSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead selectSlots

def lcaOverhead (lcaSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead lcaSlots

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (_family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  bpCloseNavigationOverhead
    (rankOverhead rankSlots)
    (selectOverhead selectSlots)
    (lcaOverhead lcaSlots)

def toPayloadLiveBPCloseRMQNavigationFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    PayloadLiveBPCloseRMQNavigationFamily
      (rankOverhead rankSlots)
      (selectOverhead selectSlots)
      (lcaOverhead lcaSlots) where
  directory := family.directory
  rank_littleO := sampledDirectoryOverhead_littleO rankSlots
  select_littleO := sampledDirectoryOverhead_littleO selectSlots
  lca_littleO := sampledDirectoryOverhead_littleO lcaSlots

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO

theorem two_n_plus_o_built_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    PayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile
      family.toPayloadLiveBPCloseRMQNavigationFamily

end SampledPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled BP close-navigation family with explicit word-size bounds for the
rank/select payload stores.

This keeps the existing stateful query theorem, but strengthens the
representation discipline needed for a broadword interpretation: the BP payload
stores used by rank and select cannot be a single unbounded word.
-/
structure WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  selectWordSize : Nat -> Cartesian.CartesianShape -> Nat
  select_wordSize_pos :
    forall n shape, 0 < selectWordSize n shape
  rank_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).rankData shape).bitWords.words.toList) ->
        word.length <= ((directory n).rankData shape).wordSize
  select_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).selectData shape).bitWords.words.toList) ->
        word.length <= selectWordSize n shape

namespace WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily

def toSampledFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    SampledPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  family.toSampledFamily.overhead

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toSampledFamily.overhead_littleO

theorem two_n_plus_o_bounded_built_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).rankData shape).bitWords.words.toList) ->
            word.length <=
              ((family.directory n).rankData shape).wordSize) /\
        (forall shape, 0 < family.selectWordSize n shape) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).selectData shape).bitWords.words.toList) ->
            word.length <= family.selectWordSize n shape) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    have hprofile :=
      family.toSampledFamily.two_n_plus_o_built_query_profile.2 n
    rcases hprofile with
      ⟨hlower, hpayload, hcost, hexact⟩
    constructor
    · exact hlower
    · constructor
      · exact hpayload
      · constructor
        · exact hcost
        · constructor
          · exact hexact
          · constructor
            · intro shape word hmem
              exact family.rank_word_length_le n shape hmem
            · constructor
              · intro shape
                exact family.select_wordSize_pos n shape
              · intro shape word hmem
                exact family.select_word_length_le n shape hmem

end WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled encoded BP close-navigation family with explicit word-size bounds.

This is the strongest abstract upper-bound target currently exposed: queries
run through payload-only encoded functions, auxiliary payloads fit the sampled
`o(n)` envelope, and the rank/select stored payload words are bounded instead
of being modeled as one unbounded aggregate word.
-/
structure WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)
  selectWordSize : Nat -> Cartesian.CartesianShape -> Nat
  select_wordSize_pos :
    forall n shape, 0 < selectWordSize n shape
  rank_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).rankData shape).bitWords.words.toList) ->
        word.length <= ((directory n).rankData shape).wordSize
  select_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).selectData shape).bitWords.words.toList) ->
        word.length <= selectWordSize n shape

namespace WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

def toSampledEncodedFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory
  view := family.view

def toWordBoundedSampledFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory
  selectWordSize := family.selectWordSize
  select_wordSize_pos := family.select_wordSize_pos
  rank_word_length_le := family.rank_word_length_le
  select_word_length_le := family.select_word_length_le

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  family.toSampledEncodedFamily.overhead

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toSampledEncodedFamily.overhead_littleO

theorem two_n_plus_o_word_bounded_encoded_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    family.toSampledEncodedFamily.toEncodedFamily.Profile /\
      forall n : Nat,
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).rankData shape).bitWords.words.toList) ->
            word.length <=
              ((family.directory n).rankData shape).wordSize) /\
        (forall shape, 0 < family.selectWordSize n shape) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).selectData shape).bitWords.words.toList) ->
            word.length <= family.selectWordSize n shape) := by
  constructor
  · exact family.toSampledEncodedFamily.two_n_plus_o_sampled_encoded_query_profile
  · intro n
    constructor
    · intro shape word hmem
      exact family.rank_word_length_le n shape hmem
    · constructor
      · intro shape
        exact family.select_wordSize_pos n shape
      · intro shape word hmem
        exact family.select_word_length_le n shape hmem

end WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

/-- A family of certified BP-native broadword RMQ directories. -/
structure BPBroadwordSuccinctRMQFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat, BPBroadwordRMQDirectory n (overhead n) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BPBroadwordSuccinctRMQFamily

/--
Research-facing BP-native `2*n + o(n)`, constant-query profile.

The payload equality clause exposes the concrete representation: the counted
`2*n` part is the Cartesian shape's balanced-parentheses code.
-/
theorem two_n_plus_o_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BPBroadwordSuccinctRMQFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (((family.directory n).stateEncoding).payloadOf shape =
              shape.bpCode ++
                (family.directory n).encodeAux
                  ((family.directory n).buildAux shape)) /\
            ((((family.directory n).stateEncoding).payloadView).payloadBitCount
              (((family.directory n).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall (state : (family.directory n).State) left right,
          ((family.directory n).queryStateCosted state left right).cost <=
            queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryStateCosted
                    ((family.directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact (family.directory n).payloadSpaceBounds_lower_le_upper
    · constructor
      · intro shape hshape
        exact ⟨(family.directory n).payloadOf_eq shape,
          (family.directory n).payloadBitCount_eq hshape⟩
      · constructor
        · intro state left right
          exact (family.directory n).queryStateCosted_cost_le state left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryStateCosted_exact hshape hlen hbound

end BPBroadwordSuccinctRMQFamily

/--
Componentized version of the broadword family interface.  This is the shape
expected from a concrete BP/rank-select implementation: each auxiliary
component supplies its own `o(n)` proof, while the directory states the exact
sum of their counted bits.
-/
structure ComponentizedBPRMQFamily
    (rank select excess micro : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat,
      BroadwordRMQDirectory n
        (bpAuxOverhead rank select excess micro n) queryCost
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  excess_littleO : LittleOLinear excess
  micro_littleO : LittleOLinear micro

namespace ComponentizedBPRMQFamily

def overhead
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (_family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    Nat -> Nat :=
  bpAuxOverhead rank select excess micro

theorem overhead_littleO
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    LittleOLinear family.overhead := by
  exact bpAuxOverhead_littleO
    family.rank_littleO family.select_littleO
    family.excess_littleO family.micro_littleO

def toBroadwordSuccinctRMQFamily
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    BroadwordSuccinctRMQFamily family.overhead queryCost where
  directory := family.directory
  overhead_littleO := family.overhead_littleO

theorem two_n_plus_o_constant_query_profile
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (((((family.toBroadwordSuccinctRMQFamily).directory n).stateEncoding).payloadView).payloadBitCount
              ((((family.toBroadwordSuccinctRMQFamily).directory n).stateEncoding).buildState shape) =
                2 * n + family.overhead n)) /\
        (forall
          (state :
            ((family.toBroadwordSuccinctRMQFamily).directory n).State)
          left right,
          (((family.toBroadwordSuccinctRMQFamily).directory n).queryStateCosted
              state left right).cost <= queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (((family.toBroadwordSuccinctRMQFamily).directory n).queryStateCosted
                    (((family.toBroadwordSuccinctRMQFamily).directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  exact
    BroadwordSuccinctRMQFamily.two_n_plus_o_constant_query_profile
      family.toBroadwordSuccinctRMQFamily

end ComponentizedBPRMQFamily

end SuccinctSpace

end RMQ

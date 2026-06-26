import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.SlotBasics

/-!
# Sparse/dense width bounds

Split implementation layer for built sparse/dense close-select routing.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

theorem natLog2_le_log2_of_le
    {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0) (hle : m <= n) :
    Nat.log2 m <= Nat.log2 n := by
  have hpow : 2 ^ Nat.log2 m <= n :=
    Nat.le_trans (Nat.log2_self_le hm) hle
  exact (Nat.le_log2 hn).mpr hpow

theorem machineWordBits_mono_le
    {m n : Nat} (hle : m <= n) :
    SuccinctRank.machineWordBits m <=
      SuccinctRank.machineWordBits n := by
  unfold SuccinctRank.machineWordBits
  by_cases hm : m = 0
  · simp [hm]
  · have hn : n ≠ 0 := by omega
    exact Nat.succ_le_succ (natLog2_le_log2_of_le hm hn hle)

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
    SuccinctRank.machineWordBits n <= n := by
  unfold SuccinctRank.machineWordBits
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
    have htwo : 2 <= n := by omega
    have hpow : n < 2 ^ n := by
      have hsucc := SuccinctSpace.nat_succ_le_two_pow n
      omega
    have hlog_lt : Nat.log2 n < n :=
      (Nat.log2_lt hn_ne).2 hpow
    omega

theorem lt_two_pow_machineWordBits_of_lt
    {x n : Nat} (hx : x < n) :
    x < 2 ^ SuccinctRank.machineWordBits n := by
  exact Nat.lt_trans hx
    (by
      simpa [SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := n)))

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
  exact machineWordBits_mono_le
    (Nat.min_le_left shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape))

theorem natLog2_succ_le_of_pos_lt_pow
    {n k : Nat} (hnpos : 0 < n) (hlt : n < 2 ^ k) :
    Nat.log2 n + 1 <= k := by
  by_cases hk : k <= Nat.log2 n
  · have hn : n ≠ 0 := by omega
    have hpow : 2 ^ k <= n := (Nat.le_log2 hn).1 hk
    omega
  · omega

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
      4 * sparseDenseFalseSelectEll shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let m :=
    Nat.min shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape)
  by_cases hm : m = 0
  · have hell_pos : 0 < ell := by
      simp [ell, sparseDenseFalseSelectEll]
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits, m, hm,
      sparseDenseFalseSelectEll]
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hword_pos : 0 < wordBits := by
      simp [wordBits, sparseDenseFalseSelectWordBits,
        SuccinctRank.machineWordBits_pos]
    have hell_pos : 0 < ell := by
      simp [ell, sparseDenseFalseSelectEll]
    have hword_lt_pow :
        wordBits < 2 ^ ell := by
      simpa [wordBits, ell, sparseDenseFalseSelectEll,
        sparseDenseFalseSelectWordBits,
        SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := wordBits))
    have hword_le_pow : wordBits <= 2 ^ ell :=
      Nat.le_of_lt hword_lt_pow
    have hell_le_pow : ell <= 2 ^ ell :=
      SuccinctSpace.nat_le_two_pow ell
    have hww_le :
        wordBits * wordBits <= 2 ^ ell * 2 ^ ell :=
      Nat.mul_le_mul hword_le_pow hword_le_pow
    have hww_pos : 0 < wordBits * wordBits :=
      Nat.mul_pos hword_pos hword_pos
    have hwww_lt_step :
        (wordBits * wordBits) * wordBits <
          (wordBits * wordBits) * 2 ^ ell :=
      Nat.mul_lt_mul_of_pos_left hword_lt_pow hww_pos
    have hwww_le_step :
        (wordBits * wordBits) * 2 ^ ell <=
          (2 ^ ell * 2 ^ ell) * 2 ^ ell :=
      Nat.mul_le_mul_right (2 ^ ell) hww_le
    have hwww_lt :
        wordBits * wordBits * wordBits <
          2 ^ ell * 2 ^ ell * 2 ^ ell := by
      exact Nat.lt_of_lt_of_le
        (by simpa [Nat.mul_assoc] using hwww_lt_step)
        (by simpa [Nat.mul_assoc] using hwww_le_step)
    have hleft_lt :
        (wordBits * wordBits * wordBits) * ell <
          (2 ^ ell * 2 ^ ell * 2 ^ ell) * ell :=
      Nat.mul_lt_mul_of_pos_right hwww_lt hell_pos
    have hright_le :
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * ell <=
          (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell :=
      Nat.mul_le_mul_left (2 ^ ell * 2 ^ ell * 2 ^ ell)
        hell_le_pow
    have hpows :
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell =
          2 ^ (4 * ell) := by
      calc
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell =
            (((2 ^ ell * 2 ^ ell) * 2 ^ ell) * 2 ^ ell) := by
              simp [Nat.mul_assoc]
        _ = ((2 ^ (ell + ell) * 2 ^ ell) * 2 ^ ell) := by
              rw [← Nat.pow_add]
        _ = (2 ^ (ell + ell + ell) * 2 ^ ell) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (ell + ell + ell + ell) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (4 * ell) := by
              congr 1
              omega
    have hsuper_lt :
        sparseDenseFalseSelectSuperLongSpan shape < 2 ^ (4 * ell) := by
      have hraw :
          (wordBits * wordBits * wordBits) * ell <
            2 ^ (4 * ell) := by
        have h :=
          Nat.lt_of_lt_of_le hleft_lt hright_le
        rwa [hpows] at h
      simpa [sparseDenseFalseSelectSuperLongSpan,
        sparseDenseFalseSelectSuperStride, wordBits, ell,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hraw
    have hm_lt : m < 2 ^ (4 * ell) := by
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hsuper_lt
    have hlog := natLog2_succ_le_of_pos_lt_pow hmpos hm_lt
    simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRank.machineWordBits, m, ell] using hlog

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
          _ = 2 ^ q := by rw [← hqeq]
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

theorem sparseDenseFalseSelectEll_square_le_sixtyFour_wordBits
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectEll shape *
        sparseDenseFalseSelectEll shape <=
      64 * sparseDenseFalseSelectWordBits shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let q := Nat.log2 wordBits
  have hword_pos : 0 < wordBits := by
    simp [wordBits, sparseDenseFalseSelectWordBits,
      SuccinctRank.machineWordBits_pos]
  by_cases hlarge : 6 <= q
  · have hword_ne : wordBits ≠ 0 := by omega
    have hsq :
        (q + 1) * (q + 1) <= wordBits :=
      Nat.le_trans
        (nat_succ_square_le_two_pow_of_six_le q hlarge)
        (Nat.log2_self_le hword_ne)
    have hword_le : wordBits <= 64 * wordBits := by omega
    exact Nat.le_trans
      (by
        simpa [q, wordBits, sparseDenseFalseSelectEll] using hsq)
      hword_le
  · have hq_le : q <= 5 := by omega
    have hell_le :
        sparseDenseFalseSelectEll shape <= 6 := by
      simpa [sparseDenseFalseSelectEll, q, wordBits] using
        Nat.succ_le_succ hq_le
    have hell_square_le :
        sparseDenseFalseSelectEll shape *
            sparseDenseFalseSelectEll shape <= 6 * 6 :=
      Nat.mul_le_mul hell_le hell_le
    have hword_one : 1 <= wordBits := by omega
    have hconst : 6 * 6 <= 64 * wordBits := by omega
    exact Nat.le_trans hell_square_le hconst

theorem builtRelativeSplitFalseSelectSparseException_localStride_mul_width_mul_ell_le_const_wordBits
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectLocalStride shape *
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape *
        sparseDenseFalseSelectEll shape <=
      512 * sparseDenseFalseSelectWordBits shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let denom := ell * ell
  let q := wordBits / denom
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  have hstride : localStride <= q + 1 := by
    have hmax : max 1 q <= q + 1 := by
      exact Nat.max_le.2 ⟨Nat.succ_pos q, Nat.le_succ q⟩
    simpa [localStride, q, denom, wordBits, ell,
      sparseDenseFalseSelectLocalStride, sparseDenseFalseSelectEll] using
      hmax
  have hwidth : relativeWidth <= 4 * ell := by
    simpa [relativeWidth, ell] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
        shape
  have hfirst :
      localStride * relativeWidth * ell <=
        (q + 1) * (4 * ell) * ell := by
    have hmul := Nat.mul_le_mul hstride hwidth
    exact Nat.mul_le_mul_right ell hmul
  have hqdenom : q * denom <= wordBits := by
    exact Nat.div_mul_le_self wordBits denom
  have hqdenom_succ :
      (q + 1) * denom <= wordBits + denom := by
    calc
      (q + 1) * denom = q * denom + denom := by
        rw [Nat.add_mul]
        simp
      _ <= wordBits + denom := Nat.add_le_add_right hqdenom denom
  have hell_square :
      denom <= 64 * wordBits := by
    simpa [denom, ell, wordBits] using
      sparseDenseFalseSelectEll_square_le_sixtyFour_wordBits shape
  have hqdenom_budget :
      4 * ((q + 1) * denom) <= 512 * wordBits := by
    have hsum : wordBits + denom <= 65 * wordBits := by
      omega
    have hsucc_le : (q + 1) * denom <= 65 * wordBits :=
      Nat.le_trans hqdenom_succ hsum
    have hmul := Nat.mul_le_mul_left 4 hsucc_le
    omega
  have hright :
      (q + 1) * (4 * ell) * ell <= 512 * wordBits := by
    have hrewrite :
        (q + 1) * (4 * ell) * ell =
      4 * ((q + 1) * denom) := by
      simp [denom, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    simpa [hrewrite] using hqdenom_budget
  exact Nat.le_trans hfirst hright

theorem falseSelectCeilDiv_mul_le_add
    (n stride : Nat) :
    falseSelectCeilDiv n stride * stride <= n + stride := by
  unfold falseSelectCeilDiv
  have hdiv :
      ((n + stride - 1) / stride) * stride <=
        n + stride - 1 := Nat.div_mul_le_self _ _
  omega

theorem falseSelectLocalSlotsPerSuper_mul_localStride_le_add
    (superStride localStride : Nat) :
    falseSelectLocalSlotsPerSuper superStride localStride *
        localStride <=
      superStride + localStride := by
  unfold falseSelectLocalSlotsPerSuper
  have hdiv :
      ((superStride + localStride - 1) / localStride) *
          localStride <=
        superStride + localStride - 1 := Nat.div_mul_le_self _ _
  omega

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
    SuccinctRank.machineWordBits n *
        SuccinctRank.machineWordBits n <=
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
    simpa [q, SuccinctRank.machineWordBits] using hsq) hscale

theorem sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectWordBits shape <=
      2 * sparseDenseFalseSelectLocalStride shape *
        (sparseDenseFalseSelectEll shape *
          sparseDenseFalseSelectEll shape) := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let denom := ell * ell
  let q := wordBits / denom
  let localStride := sparseDenseFalseSelectLocalStride shape
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hdenom_pos : 0 < denom := Nat.mul_pos hell_pos hell_pos
  have hlt : wordBits < q * denom + denom := by
    simpa [q, denom] using Nat.lt_div_mul_add hdenom_pos (a := wordBits)
  have hsucc_le :
      q + 1 <= 2 * localStride := by
    have hlocal_def : localStride = max 1 q := by
      simp [localStride, q, denom, ell, wordBits,
        sparseDenseFalseSelectLocalStride, sparseDenseFalseSelectEll]
    by_cases hq : q = 0
    · have hlocal_ge : 1 <= localStride := by
        rw [hlocal_def]
        exact Nat.le_max_left 1 q
      omega
    · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
      have hlocal : localStride = q := by
        rw [hlocal_def]
        exact Nat.max_eq_right (by omega)
      rw [hlocal]
      omega
  have hmul :
      (q + 1) * denom <= 2 * localStride * denom := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right denom hsucc_le
  have hle : wordBits <= (q + 1) * denom := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_of_lt hlt
  exact Nat.le_trans hle (by
    simpa [wordBits, ell, denom, localStride, q,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
    (shape : Cartesian.CartesianShape) {payload scale : Nat}
    (hmul :
      payload * sparseDenseFalseSelectWordBits shape <=
        scale * shape.bpCode.length *
          (sparseDenseFalseSelectEll shape *
            (sparseDenseFalseSelectEll shape *
              sparseDenseFalseSelectEll shape))) :
    payload <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        (2 * scale) shape.bpCode.length := by
  let n := shape.bpCode.length
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  have hwordPos : 0 < wordBits := by
    simpa [wordBits] using sparseDenseFalseSelectWordBits_pos shape
  by_cases hn : n = 0
  · have hzeroMul : payload * wordBits = 0 := by
      have hle0 : payload * wordBits <= 0 := by
        simpa [n, wordBits, ell, ell3, hn,
          sparseDenseFalseSelectWordBits, sparseDenseFalseSelectEll] using hmul
      omega
    have hpayload : payload = 0 := by
      cases payload with
      | zero =>
          rfl
      | succ payload =>
          have hpos : 0 < (payload + 1) * wordBits :=
            Nat.mul_pos (by omega) hwordPos
          omega
    simp [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      hpayload, n, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hwordLeN : wordBits <= n := by
      simpa [wordBits, sparseDenseFalseSelectWordBits] using
        machineWordBits_le_self_of_pos hnPos
    let q := n / wordBits
    have hqPos : 0 < q := Nat.div_pos hwordLeN hwordPos
    have hnLt : n < q * wordBits + wordBits := by
      simpa [q] using Nat.lt_div_mul_add hwordPos (a := n)
    have hnLeQ :
        n <= 2 * q * wordBits := by
      have hsucc : q + 1 <= 2 * q := by omega
      have hleSucc : n <= (q + 1) * wordBits := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.le_of_lt hnLt
      have hmul := Nat.mul_le_mul_right wordBits hsucc
      exact Nat.le_trans hleSucc (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    have hbudget :
        scale * n * ell3 <=
          (2 * scale) * (q * ell3) * wordBits := by
      have hscaled := Nat.mul_le_mul_left scale hnLeQ
      have hell := Nat.mul_le_mul_right ell3 hscaled
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hell
    have hpayloadWord :
        payload * wordBits <=
          (2 * scale) * (q * ell3) * wordBits := by
      exact Nat.le_trans
        (by
          simpa [n, wordBits, ell, ell3,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
        hbudget
    have hpayloadWordLeft :
        wordBits * payload <=
          wordBits * ((2 * scale) * (q * ell3)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadWord
    have hpayloadLe :
        payload <= (2 * scale) * (q * ell3) :=
      Nat.le_of_mul_le_mul_left hpayloadWordLeft hwordPos
    simpa [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      n, wordBits, ell, ell3, q, sparseDenseFalseSelectWordBits,
      sparseDenseFalseSelectEll, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hpayloadLe

theorem sparseDenseFalseSelectLocalStride_le_superStride
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectLocalStride shape <=
      sparseDenseFalseSelectSuperStride shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  have hword_pos : 0 < wordBits := by
    simpa [wordBits] using sparseDenseFalseSelectWordBits_pos shape
  have hlocal_le_word :
      sparseDenseFalseSelectLocalStride shape <= wordBits := by
    unfold sparseDenseFalseSelectLocalStride
    exact Nat.max_le.2
      ⟨by simpa [wordBits] using hword_pos,
        Nat.div_le_self wordBits
          (sparseDenseFalseSelectEll shape *
            sparseDenseFalseSelectEll shape)⟩
  have hword_le_square : wordBits <= wordBits * wordBits := by
    simpa using Nat.mul_le_mul_left wordBits (by omega : 1 <= wordBits)
  exact Nat.le_trans hlocal_le_word (by
    simpa [wordBits, sparseDenseFalseSelectSuperStride] using
      hword_le_square)

theorem builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRectangularFalseSelectLocalSlotCount shape *
        sparseDenseFalseSelectLocalStride shape <=
      10 * shape.bpCode.length := by
  let count := falseSelectOccurrenceCount shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  by_cases hcount : count = 0
  · have hsuperCount : superCount = 0 := by
      unfold superCount builtRectangularFalseSelectSuperSlotCount
        falseSelectCeilDiv
      rw [show falseSelectOccurrenceCount shape = 0 by
        simpa [count] using hcount]
      have hstride_pos : 0 < superStride := by
        simpa [superStride] using sparseDenseFalseSelectSuperStride_pos shape
      have hpred_lt : superStride - 1 < superStride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStride] using Nat.div_eq_of_lt hpred_lt
    simp [builtRectangularFalseSelectLocalSlotCount, superCount,
      hsuperCount]
  · have hcount_pos : 0 < count := Nat.pos_of_ne_zero hcount
    have hcountSize : count = shape.size := by
      simpa [count] using falseSelectOccurrenceCount_eq_size shape
    have hbpLen : shape.bpCode.length = 2 * shape.size := by
      exact Cartesian.CartesianShape.bpCode_length shape
    have hbp_pos : 0 < shape.bpCode.length := by
      omega
    have hcount_le_bp : count <= shape.bpCode.length := by
      omega
    have hsuperStride_le :
        superStride <= 4 * shape.bpCode.length := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := shape.bpCode.length) hbp_pos
      simpa [superStride, sparseDenseFalseSelectSuperStride,
        sparseDenseFalseSelectWordBits] using hsq
    have hsuperCountMul :
        superCount * superStride <= count + superStride := by
      simpa [superCount, count, superStride,
        builtRectangularFalseSelectSuperSlotCount] using
        falseSelectCeilDiv_mul_le_add count superStride
    have hslotsMul :
        slots * localStride <= superStride + localStride := by
      simpa [slots, superStride, localStride,
        builtRectangularFalseSelectLocalSlotsPerSuper] using
        falseSelectLocalSlotsPerSuper_mul_localStride_le_add
          superStride localStride
    have hlocal_le_super :
        localStride <= superStride := by
      simpa [localStride, superStride] using
        sparseDenseFalseSelectLocalStride_le_superStride shape
    have hslotsMul' :
        slots * localStride <= 2 * superStride := by
      omega
    have hlocalPayload :
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape <=
          2 * (superCount * superStride) := by
      have hmul := Nat.mul_le_mul_left superCount hslotsMul'
      simpa [builtRectangularFalseSelectLocalSlotCount, superCount,
        slots, localStride, superStride, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hsuperBudget :
        2 * (superCount * superStride) <=
          10 * shape.bpCode.length := by
      have hscaled := Nat.mul_le_mul_left 2 hsuperCountMul
      have hbudget : 2 * (count + superStride) <=
          10 * shape.bpCode.length := by
        omega
      exact Nat.le_trans (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          hscaled) hbudget
    exact Nat.le_trans hlocalPayload hsuperBudget


end SuccinctSelect
end RMQ

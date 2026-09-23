import RMQ.Core.WordRAM.Construction.Proof.GeometryBank
import RMQ.Core.WordRAM.Construction.Spec.Metadata
import RMQ.Core.WordRAM.Construction.Spec.Envelope

/-! # PRE-1 builder proofs: the metadata envelope (stage S7)

Outside the builder firewall. `metaAtoms` collects the arithmetic facts behind
the metadata bank: the access length is the sum of the source lengths, the
interior overhead is the sum of the eight interior table bit counts, every word
count is at most its bit count, and the small widths are linear in `n`.
`metaVal_le` bounds every metadata bank value by `3 * (400000 * (n + 1))`
whenever the payload length is within the payload envelope; the stage proof
supplies that premise from `planPayload_length_add_two_le`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

theorem ceilDiv_le_self' (k ws : Nat) (hws : 0 < ws) :
    k / ws + (if k % ws = 0 then 0 else 1) ≤ k := by
  split
  · exact Nat.div_le_self _ _
  · rename_i h
    have hk : k ≠ 0 := fun h0 => h (by rw [h0, Nat.zero_mod])
    have hws2 : ws ≠ 1 := fun h1 => h (by rw [h1, Nat.mod_one])
    have := Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by omega : 1 < ws)
    omega

theorem lt0_le_one (x : Nat) : (if x = 0 then 0 else 1) ≤ 1 := by split <;> omega

theorem log2_add_one_le (x : Nat) : Nat.log2 x + 1 ≤ x + 1 := by
  have := Nat.log2_le_self x; omega

section Bounds

variable (n lc c : Nat)

/-- Atom facts behind every metadata bound. -/
theorem metaAtoms :
    mv_acc n lc c = mv_len1 n lc c + mv_len2 n lc c + 4 * mv_len3 n lc c + 4 * mv_len7 n lc c +
      2 * mv_len11 n lc c + packedSuperSlots n + mv_len14 n lc c + 2 * mv_len15 n lc c +
      packedSparseSlots n + mv_len18 n lc c ∧
    mv_sc n lc c ≤ mv_len18 n lc c ∧ mv_lcS n lc c ≤ mv_len14 n lc c ∧
    packedSuperSlots n ≤ mv_len3 n lc c ∧
    canonicalRelativeRmmInteriorRawPayloadOverhead n = mv_q1bits n lc c + 3 * mv_q2bits n lc c +
      mv_q5bits n lc c + mv_q6bits n lc c + mv_q7bits n lc c +
      bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount *
        bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) ∧
    mv_BW n lc c ≤ mv_q1bits n lc c ∧ mv_MR n lc c ≤ mv_q2bits n lc c ∧
    mv_LT n lc c ≤ mv_q5bits n lc c ∧ mv_GT n lc c ≤ mv_q6bits n lc c ∧
    mv_LL n lc c ≤ mv_q7bits n lc c ∧
    mv_GL n lc c ≤ bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount *
        bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) ∧
    bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize) ≤ mv_q7bits n lc c ∧
    bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) ≤
      bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount *
        bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) ∧
    packedRankWordSize n ≤ 2 * n + 1 ∧ 1 ≤ packedRankWordSize n ∧
    (packedInteriorLayout n).relativeWidth ≤ 2 * n + 5 ∧
    (packedInteriorLayout n).offsetWidth ≤ 2 * n + 2 ∧
    (packedInteriorLayout n).blockAddressWidth ≤ n + 1 ∧
    wordWidth n ≤ 192 * n + 576 ∧ packedReviewerCellWidth n < wordWidth n ∧
    1 ≤ packedReviewerCellWidth n ∧
    mv_fbits n lc c = bpFringeTableOverhead n ∧ mv_sbits n lc c = bpChunkSelectTableOverhead n := by
  have hws1 : 1 ≤ packedRankWordSize n := SuccinctRank.machineWordBits_pos _
  have hlw1 : 0 < packedLocalWidth n := SuccinctRank.machineWordBits_pos _
  have hlsw : 0 < packedRankWordSize n := hws1
  have dom1 : 1 ≤ bpSparseLevelDomain (packedInteriorLayout n).macroSize := by
    unfold bpSparseLevelDomain; omega
  have dom2 : 1 ≤ bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount := by
    unfold bpSparseLevelDomain; omega
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hws1, ?_, ?_, ?_,
    wordWidth_le_linear n, oldWidth_lt_wordWidth n, packedReviewerCellWidth_pos n, rfl, rfl⟩
  · simp only [mv_acc, mv_o18, mv_o17, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10,
      mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]
    omega
  · exact Nat.le_mul_of_pos_right _ hlw1
  · exact Nat.le_mul_of_pos_right _ hlsw
  · exact Nat.le_mul_of_pos_right _ hlsw
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.mul_le_mul_left _ (ceilDiv_le_self' _ _ hlsw)
  · exact Nat.le_mul_of_pos_left _ dom1
  · exact Nat.le_mul_of_pos_left _ dom2
  · have := log2_add_one_le (2 * n)
    show Nat.log2 (2 * n) + 1 ≤ _
    omega
  · show 2 * (Nat.log2 (Nat.log2 n + 1) + 1) + 3 ≤ _
    have h1 := log2_succ_le_of_pos (show 1 ≤ Nat.log2 n + 1 by omega)
    have h2 := Nat.log2_le_self n
    omega
  · have h := bnd_ow n
    exact h
  · show Nat.log2 (n / (Nat.log2 n + 1)) + 1 ≤ _
    have h1 := Nat.log2_le_self (n / (Nat.log2 n + 1))
    have h2 := Nat.div_le_self n (Nat.log2 n + 1)
    omega

set_option maxHeartbeats 1600000 in
/-- **Metadata envelope.** Every metadata bank value is at most three times the
payload envelope, whenever the payload length itself is within it. -/
theorem metaVal_le (hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1)) :
    ∀ i, i < 108 → metaVal n lc c i ≤ 3 * (400000 * (n + 1)) := by
  obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how,
    hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
  have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + canonicalRelativeRmmInteriorRawPayloadOverhead n +
      bpFringeTableOverhead n + bpChunkSelectTableOverhead n := rfl
  have hold : mv_oldBits n lc c ≤ mv_pay n lc c + 2 * packedReviewerCellWidth n := by
    have h := oldBits_le n lc (c * GenericSelect.localStride (2 * n))
    rw [cellCount_eq, pay_eq] at h
    exact h
  have hoc : mv_oldCount n lc c ≤ mv_pay n lc c + packedReviewerCellWidth n := by
    unfold mv_oldCount
    have := Nat.div_le_self (mv_pay n lc c + packedReviewerCellWidth n - 1) (packedReviewerCellWidth n)
    omega
  have hdc : mv_dcount n lc c ≤ mv_oldBits n lc c + wordWidth n := by
    unfold mv_dcount
    have := Nat.div_le_self (mv_oldBits n lc c + wordWidth n - 1) (wordWidth n)
    omega
  have hq2n : mv_q2n n lc c ≤ 2 * n := Nat.div_le_self _ _
  have hcc2n : mv_cc2n n lc c ≤ 2 * n + 1 := by
    unfold mv_cc2n; have := lt0_le_one ((2 * n) % packedRankWordSize n); omega
  have hqsup : mv_qsup n lc c ≤ packedSuperSlots n := Nat.div_le_self _ _
  have hlfwc : mv_lfwc n lc c ≤ 2 * packedSuperSlots n + 2 := by
    unfold mv_lfwc; have := lt0_le_one (packedSuperSlots n % packedLongFlagWordSize n); omega
  have hqsp : mv_qsp n lc c ≤ packedSparseSlots n := Nat.div_le_self _ _
  have hsfwc : mv_sfwc n lc c ≤ 2 * packedSparseSlots n + 2 := by
    unfold mv_sfwc; have := lt0_le_one (packedSparseSlots n % packedSparseWordSize n); omega
  have hq_39 : mv_q_39 n lc c ≤ packedRankWordSize n := Nat.div_le_self _ _
  have hcc_39 : mv_cc_39 n lc c ≤ packedRankWordSize n + 1 := by
    unfold mv_cc_39; have := lt0_le_one ((packedRankWordSize n) % packedRankWordSize n); omega
  have hcd_39 : mv_cd_39 n lc c ≤ packedRankWordSize n + packedRankWordSize n := by
    unfold mv_cd_39; have := Nat.div_le_self ((packedRankWordSize n) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  have hq_61 : mv_q_61 n lc c ≤ (packedInteriorLayout n).relativeWidth := Nat.div_le_self _ _
  have hcc_61 : mv_cc_61 n lc c ≤ (packedInteriorLayout n).relativeWidth + 1 := by
    unfold mv_cc_61; have := lt0_le_one (((packedInteriorLayout n).relativeWidth) % packedRankWordSize n); omega
  have hcd_61 : mv_cd_61 n lc c ≤ (packedInteriorLayout n).relativeWidth + packedRankWordSize n := by
    unfold mv_cd_61; have := Nat.div_le_self (((packedInteriorLayout n).relativeWidth) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  have hq_58 : mv_q_58 n lc c ≤ (packedInteriorLayout n).offsetWidth := Nat.div_le_self _ _
  have hcc_58 : mv_cc_58 n lc c ≤ (packedInteriorLayout n).offsetWidth + 1 := by
    unfold mv_cc_58; have := lt0_le_one (((packedInteriorLayout n).offsetWidth) % packedRankWordSize n); omega
  have hcd_58 : mv_cd_58 n lc c ≤ (packedInteriorLayout n).offsetWidth + packedRankWordSize n := by
    unfold mv_cd_58; have := Nat.div_le_self (((packedInteriorLayout n).offsetWidth) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  have hq_60 : mv_q_60 n lc c ≤ (packedInteriorLayout n).blockAddressWidth := Nat.div_le_self _ _
  have hcc_60 : mv_cc_60 n lc c ≤ (packedInteriorLayout n).blockAddressWidth + 1 := by
    unfold mv_cc_60; have := lt0_le_one (((packedInteriorLayout n).blockAddressWidth) % packedRankWordSize n); omega
  have hcd_60 : mv_cd_60 n lc c ≤ (packedInteriorLayout n).blockAddressWidth + packedRankWordSize n := by
    unfold mv_cd_60; have := Nat.div_le_self (((packedInteriorLayout n).blockAddressWidth) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  have hq_36 : mv_q_36 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize) := Nat.div_le_self _ _
  have hcc_36 : mv_cc_36 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize) + 1 := by
    unfold mv_cc_36; have := lt0_le_one ((bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize)) % packedRankWordSize n); omega
  have hcd_36 : mv_cd_36 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize) + packedRankWordSize n := by
    unfold mv_cd_36; have := Nat.div_le_self ((bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSize)) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  have hq_37 : mv_q_37 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) := Nat.div_le_self _ _
  have hcc_37 : mv_cc_37 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) + 1 := by
    unfold mv_cc_37; have := lt0_le_one ((bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) % packedRankWordSize n); omega
  have hcd_37 : mv_cd_37 n lc c ≤ bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) + packedRankWordSize n := by
    unfold mv_cd_37; have := Nat.div_le_self ((bpSparseLevelWidth (bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) + packedRankWordSize n - 1) (packedRankWordSize n); omega
  intro i hi
  match i, hi with
  | 0, _ => show mv_sc n lc c ≤ _; omega
  | 1, _ => show mv_len1 n lc c ≤ _; omega
  | 2, _ => show mv_len2 n lc c ≤ _; omega
  | 3, _ => show mv_len3 n lc c ≤ _; omega
  | 4, _ => show mv_len7 n lc c ≤ _; omega
  | 5, _ => show mv_len11 n lc c ≤ _; omega
  | 6, _ => show mv_lcS n lc c ≤ _; omega
  | 7, _ => show mv_len14 n lc c ≤ _; omega
  | 8, _ => show mv_len15 n lc c ≤ _; omega
  | 9, _ => show mv_len18 n lc c ≤ _; omega
  | 10, _ => show mv_o3 n lc c ≤ _; simp only [mv_o3]; omega
  | 11, _ => show mv_o4 n lc c ≤ _; simp only [mv_o4, mv_o3]; omega
  | 12, _ => show mv_o5 n lc c ≤ _; simp only [mv_o5, mv_o4, mv_o3]; omega
  | 13, _ => show mv_o6 n lc c ≤ _; simp only [mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 14, _ => show mv_o7 n lc c ≤ _; simp only [mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 15, _ => show mv_o8 n lc c ≤ _; simp only [mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 16, _ => show mv_o9 n lc c ≤ _; simp only [mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 17, _ => show mv_o10 n lc c ≤ _; simp only [mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 18, _ => show mv_o11 n lc c ≤ _; simp only [mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 19, _ => show mv_o12 n lc c ≤ _; simp only [mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 20, _ => show mv_o13 n lc c ≤ _; simp only [mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 21, _ => show mv_o14 n lc c ≤ _; simp only [mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 22, _ => show mv_o15 n lc c ≤ _; simp only [mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 23, _ => show mv_o16 n lc c ≤ _; simp only [mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 24, _ => show mv_o17 n lc c ≤ _; simp only [mv_o17, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 25, _ => show mv_o18 n lc c ≤ _; simp only [mv_o18, mv_o17, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3]; omega
  | 26, _ => show mv_acc n lc c ≤ _; omega
  | 27, _ => show mv_a n lc c ≤ _; simp only [mv_a]; omega
  | 28, _ => show mv_b2 n lc c ≤ _; simp only [mv_b2, mv_a]; omega
  | 29, _ => show mv_b3 n lc c ≤ _; simp only [mv_b3, mv_o3, mv_a]; omega
  | 30, _ => show mv_b4 n lc c ≤ _; simp only [mv_b4, mv_o4, mv_o3, mv_a]; omega
  | 31, _ => show mv_b5 n lc c ≤ _; simp only [mv_b5, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 32, _ => show mv_b6 n lc c ≤ _; simp only [mv_b6, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 33, _ => show mv_b7 n lc c ≤ _; simp only [mv_b7, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 34, _ => show mv_b8 n lc c ≤ _; simp only [mv_b8, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 35, _ => show mv_b9 n lc c ≤ _; simp only [mv_b9, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 36, _ => show mv_b10 n lc c ≤ _; simp only [mv_b10, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 37, _ => show mv_b11 n lc c ≤ _; simp only [mv_b11, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 38, _ => show mv_b12 n lc c ≤ _; simp only [mv_b12, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 39, _ => show mv_b13 n lc c ≤ _; simp only [mv_b13, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 40, _ => show mv_b14 n lc c ≤ _; simp only [mv_b14, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 41, _ => show mv_b15 n lc c ≤ _; simp only [mv_b15, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 42, _ => show mv_b16 n lc c ≤ _; simp only [mv_b16, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 43, _ => show mv_b17 n lc c ≤ _; simp only [mv_b17, mv_o17, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 44, _ => show mv_b18 n lc c ≤ _; simp only [mv_b18, mv_o18, mv_o17, mv_o16, mv_o15, mv_o14, mv_o13, mv_o12, mv_o11, mv_o10, mv_o9, mv_o8, mv_o7, mv_o6, mv_o5, mv_o4, mv_o3, mv_a]; omega
  | 45, _ => show mv_pay n lc c ≤ _; omega
  | 46, _ => show mv_oldCount n lc c ≤ _; omega
  | 47, _ => show mv_oldBits n lc c ≤ _; omega
  | 48, _ => show mv_dcount n lc c ≤ _; omega
  | 49, _ => show mv_wc n lc c ≤ _; simp only [mv_wc]; omega
  | 50, _ => show mv_ioff n lc c ≤ _; simp only [mv_ioff]; omega
  | 51, _ => show mv_foff n lc c ≤ _; simp only [mv_foff, mv_ioff]; omega
  | 52, _ => show mv_soff n lc c ≤ _; simp only [mv_soff, mv_foff, mv_ioff]; omega
  | 53, _ => show mv_fbase n lc c ≤ _; simp only [mv_fbase, mv_foff, mv_ioff]; omega
  | 54, _ => show mv_sbase n lc c ≤ _; simp only [mv_sbase, mv_soff, mv_foff, mv_ioff]; omega
  | 55, _ => show mv_ib0 n lc c ≤ _; simp only [mv_ib0, mv_ioff]; omega
  | 56, _ => show mv_q2n n lc c ≤ _; omega
  | 57, _ => show mv_cc2n n lc c ≤ _; omega
  | 58, _ => show mv_aliasWc n lc c ≤ _; simp only [mv_aliasWc]; omega
  | 59, _ => show mv_qsup n lc c ≤ _; omega
  | 60, _ => show mv_lfwc n lc c ≤ _; omega
  | 61, _ => show mv_qsp n lc c ≤ _; omega
  | 62, _ => show mv_sfwc n lc c ≤ _; omega
  | 63, _ => show mv_fbits n lc c ≤ _; omega
  | 64, _ => show mv_sbits n lc c ≤ _; omega
  | 65, _ => show mv_q_39 n lc c ≤ _; omega
  | 66, _ => show mv_cc_39 n lc c ≤ _; omega
  | 67, _ => show mv_q_61 n lc c ≤ _; omega
  | 68, _ => show mv_cc_61 n lc c ≤ _; omega
  | 69, _ => show mv_q_58 n lc c ≤ _; omega
  | 70, _ => show mv_cc_58 n lc c ≤ _; omega
  | 71, _ => show mv_q_60 n lc c ≤ _; omega
  | 72, _ => show mv_cc_60 n lc c ≤ _; omega
  | 73, _ => show mv_q_36 n lc c ≤ _; omega
  | 74, _ => show mv_cc_36 n lc c ≤ _; omega
  | 75, _ => show mv_q_37 n lc c ≤ _; omega
  | 76, _ => show mv_cc_37 n lc c ≤ _; omega
  | 77, _ => show mv_cd_39 n lc c ≤ _; omega
  | 78, _ => show mv_cd_61 n lc c ≤ _; omega
  | 79, _ => show mv_cd_58 n lc c ≤ _; omega
  | 80, _ => show mv_cd_60 n lc c ≤ _; omega
  | 81, _ => show mv_cd_36 n lc c ≤ _; omega
  | 82, _ => show mv_cd_37 n lc c ≤ _; omega
  | 83, _ => show mv_BW n lc c ≤ _; omega
  | 84, _ => show mv_MR n lc c ≤ _; omega
  | 85, _ => show mv_LT n lc c ≤ _; omega
  | 86, _ => show mv_GT n lc c ≤ _; omega
  | 87, _ => show mv_LL n lc c ≤ _; omega
  | 88, _ => show mv_GL n lc c ≤ _; omega
  | 89, _ => show mv_p2 n lc c ≤ _; simp only [mv_p2]; omega
  | 90, _ => show mv_p3 n lc c ≤ _; simp only [mv_p3, mv_p2]; omega
  | 91, _ => show mv_p4 n lc c ≤ _; simp only [mv_p4, mv_p3, mv_p2]; omega
  | 92, _ => show mv_p5 n lc c ≤ _; simp only [mv_p5, mv_p4, mv_p3, mv_p2]; omega
  | 93, _ => show mv_p6 n lc c ≤ _; simp only [mv_p6, mv_p5, mv_p4, mv_p3, mv_p2]; omega
  | 94, _ => show mv_p7 n lc c ≤ _; simp only [mv_p7, mv_p6, mv_p5, mv_p4, mv_p3, mv_p2]; omega
  | 95, _ => show mv_ptot n lc c ≤ _; simp only [mv_ptot, mv_p7, mv_p6, mv_p5, mv_p4, mv_p3, mv_p2]; omega
  | 96, _ => show mv_q1bits n lc c ≤ _; omega
  | 97, _ => show mv_q2bits n lc c ≤ _; omega
  | 98, _ => show mv_q5bits n lc c ≤ _; omega
  | 99, _ => show mv_q6bits n lc c ≤ _; omega
  | 100, _ => show mv_q7bits n lc c ≤ _; omega
  | 101, _ => show mv_ib1 n lc c ≤ _; simp only [mv_ib1, mv_ib0, mv_ioff]; omega
  | 102, _ => show mv_ib2 n lc c ≤ _; simp only [mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | 103, _ => show mv_ib3 n lc c ≤ _; simp only [mv_ib3, mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | 104, _ => show mv_ib4 n lc c ≤ _; simp only [mv_ib4, mv_ib3, mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | 105, _ => show mv_ib5 n lc c ≤ _; simp only [mv_ib5, mv_ib4, mv_ib3, mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | 106, _ => show mv_ib6 n lc c ≤ _; simp only [mv_ib6, mv_ib5, mv_ib4, mv_ib3, mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | 107, _ => show mv_ib7 n lc c ≤ _; simp only [mv_ib7, mv_ib6, mv_ib5, mv_ib4, mv_ib3, mv_ib2, mv_ib1, mv_ib0, mv_ioff]; omega
  | _ + 108, h => exact absurd h (by omega)

end Bounds

end RMQ.SuccinctFinal.PackedConstruction.Proof

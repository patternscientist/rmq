import RMQ.Core.WordRAM.Construction.Proof.MetaSteps

/-! # PRE-1 builder proofs: metadata bank steps 54-107 and the chain (stage S7)

Outside the builder firewall. The remaining metadata bank steps, then
`metaChain_spec`: the first `k ≤ 108` steps establish the first `k` metadata
registers, keep the geometry bank and both counts, and change no register
outside `[229, 229 + k)`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

section Steps

variable {W n lc c : Nat} (hW : 32 ≤ W) (hcap : 32 * (400000 * (n + 1)) < 2 ^ W)
  (hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1))
include hW hcap hpay

theorem metaStep54 : MetaStepOK W n lc c 54 (metaStepBlock 54) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m52 : r 281 = mv_soff n lc c := by simpa only [metaVal_52, Nat.reduceAdd] using hm 52 (by decide)
    have e : mv_sbase n lc c = (packedReviewerCellWidth n) + (mv_soff n lc c) := rfl
    have hv54 : mv_sbase n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_54] using metaVal_le n lc c hpay 54 (by decide)
    pre1_meta_simp [g75, m52]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m52 : r 281 = mv_soff n lc c := by simpa only [metaVal_52, Nat.reduceAdd] using hm 52 (by decide)
    pre1_meta_simp [g75, m52, metaVal_54]
    rfl

theorem metaStep55 : MetaStepOK W n lc c 55 (metaStepBlock 55) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m50 : r 279 = mv_ioff n lc c := by simpa only [metaVal_50, Nat.reduceAdd] using hm 50 (by decide)
    have e : mv_ib0 n lc c = (packedReviewerCellWidth n) + (mv_ioff n lc c) := rfl
    have hv55 : mv_ib0 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_55] using metaVal_le n lc c hpay 55 (by decide)
    pre1_meta_simp [g75, m50]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m50 : r 279 = mv_ioff n lc c := by simpa only [metaVal_50, Nat.reduceAdd] using hm 50 (by decide)
    pre1_meta_simp [g75, m50, metaVal_55]
    rfl

theorem metaStep56 : MetaStepOK W n lc c 56 (metaStepBlock 56) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q2n n lc c = (2 * n) / (packedRankWordSize n) := rfl
    have hv56 : mv_q2n n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_56] using metaVal_le n lc c hpay 56 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((2 * n)) ((packedRankWordSize n))
    pre1_meta_simp [g38, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g38, g39, metaVal_56]
    rfl

theorem metaStep57 : MetaStepOK W n lc c 57 (metaStepBlock 57) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m56 : r 285 = mv_q2n n lc c := by simpa only [metaVal_56, Nat.reduceAdd] using hm 56 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc2n n lc c = (mv_q2n n lc c) + ((if (2 * n) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv57 : mv_cc2n n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_57] using metaVal_le n lc c hpay 57 (by decide)
    have hv56 : mv_q2n n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_56] using metaVal_le n lc c hpay 56 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((2 * n)) ((packedRankWordSize n))
    pre1_meta_simp [g38, g39, m56, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m56 : r 285 = mv_q2n n lc c := by simpa only [metaVal_56, Nat.reduceAdd] using hm 56 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g38, g39, m56, g0, metaVal_57]
    rfl

theorem metaStep58 : MetaStepOK W n lc c 58 (metaStepBlock 58) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m57 : r 286 = mv_cc2n n lc c := by simpa only [metaVal_57, Nat.reduceAdd] using hm 57 (by decide)
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_aliasWc n lc c = ((mv_cc2n n lc c) + (2 * n)) + 1 := rfl
    have hv58 : mv_aliasWc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_58] using metaVal_le n lc c hpay 58 (by decide)
    have hv57 : mv_cc2n n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_57] using metaVal_le n lc c hpay 57 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    pre1_meta_simp [m57, g38, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m57 : r 286 = mv_cc2n n lc c := by simpa only [metaVal_57, Nat.reduceAdd] using hm 57 (by decide)
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [m57, g38, g2, metaVal_58]
    rfl

theorem metaStep59 : MetaStepOK W n lc c 59 (metaStepBlock 59) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    have e : mv_qsup n lc c = (packedSuperSlots n) / (packedLongFlagWordSize n) := rfl
    have hv59 : mv_qsup n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_59] using metaVal_le n lc c hpay 59 (by decide)
    have hpos50 : 0 < (packedLongFlagWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((packedSuperSlots n)) ((packedLongFlagWordSize n))
    pre1_meta_simp [g45, g50]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    pre1_meta_simp [g45, g50, metaVal_59]
    rfl

theorem metaStep60 : MetaStepOK W n lc c 60 (metaStepBlock 60) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    have m59 : r 288 = mv_qsup n lc c := by simpa only [metaVal_59, Nat.reduceAdd] using hm 59 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have g0 : r 0 = 0 := h0
    have e : mv_lfwc n lc c = (((mv_qsup n lc c) + ((if (packedSuperSlots n) % (packedLongFlagWordSize n) = 0 then 0 else 1))) + (packedSuperSlots n)) + 1 := rfl
    have hv60 : mv_lfwc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_60] using metaVal_le n lc c hpay 60 (by decide)
    have hv59 : mv_qsup n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_59] using metaVal_le n lc c hpay 59 (by decide)
    have hv3 : mv_len3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_3] using metaVal_le n lc c hpay 3 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos50 : 0 < (packedLongFlagWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((packedSuperSlots n)) ((packedLongFlagWordSize n))
    pre1_meta_simp [g45, g50, m59, g2, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    have m59 : r 288 = mv_qsup n lc c := by simpa only [metaVal_59, Nat.reduceAdd] using hm 59 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g45, g50, m59, g2, g0, metaVal_60]
    rfl

theorem metaStep61 : MetaStepOK W n lc c 61 (metaStepBlock 61) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    have e : mv_qsp n lc c = (packedSparseSlots n) / (packedSparseWordSize n) := rfl
    have hv61 : mv_qsp n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_61] using metaVal_le n lc c hpay 61 (by decide)
    have hpos51 : 0 < (packedSparseWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((packedSparseSlots n)) ((packedSparseWordSize n))
    pre1_meta_simp [g47, g51]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    pre1_meta_simp [g47, g51, metaVal_61]
    rfl

theorem metaStep62 : MetaStepOK W n lc c 62 (metaStepBlock 62) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    have m61 : r 290 = mv_qsp n lc c := by simpa only [metaVal_61, Nat.reduceAdd] using hm 61 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have g0 : r 0 = 0 := h0
    have e : mv_sfwc n lc c = (((mv_qsp n lc c) + ((if (packedSparseSlots n) % (packedSparseWordSize n) = 0 then 0 else 1))) + (packedSparseSlots n)) + 1 := rfl
    have hv62 : mv_sfwc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_62] using metaVal_le n lc c hpay 62 (by decide)
    have hv61 : mv_qsp n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_61] using metaVal_le n lc c hpay 61 (by decide)
    have hv26 : mv_acc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_26] using metaVal_le n lc c hpay 26 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos51 : 0 < (packedSparseWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((packedSparseSlots n)) ((packedSparseWordSize n))
    pre1_meta_simp [g47, g51, m61, g2, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    have m61 : r 290 = mv_qsp n lc c := by simpa only [metaVal_61, Nat.reduceAdd] using hm 61 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g47, g51, m61, g2, g0, metaVal_62]
    rfl

theorem metaStep63 : MetaStepOK W n lc c 63 (metaStepBlock 63) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g65 : r 65 = (packedReviewerFringeCount n) := hg 27 (by decide)
    have g66 : r 66 = (packedReviewerFringeWidth n) := hg 28 (by decide)
    have e : mv_fbits n lc c = (packedReviewerFringeCount n) * (packedReviewerFringeWidth n) := rfl
    have hv63 : mv_fbits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_63] using metaVal_le n lc c hpay 63 (by decide)
    pre1_meta_simp [g65, g66]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g65 : r 65 = (packedReviewerFringeCount n) := hg 27 (by decide)
    have g66 : r 66 = (packedReviewerFringeWidth n) := hg 28 (by decide)
    pre1_meta_simp [g65, g66, metaVal_63]
    rfl

theorem metaStep64 : MetaStepOK W n lc c 64 (metaStepBlock 64) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g67 : r 67 = (packedReviewerSelectChunkCount n) := hg 29 (by decide)
    have g68 : r 68 = (packedReviewerSelectChunkWidth n) := hg 30 (by decide)
    have e : mv_sbits n lc c = (packedReviewerSelectChunkCount n) * (packedReviewerSelectChunkWidth n) := rfl
    have hv64 : mv_sbits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_64] using metaVal_le n lc c hpay 64 (by decide)
    pre1_meta_simp [g67, g68]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g67 : r 67 = (packedReviewerSelectChunkCount n) := hg 29 (by decide)
    have g68 : r 68 = (packedReviewerSelectChunkWidth n) := hg 30 (by decide)
    pre1_meta_simp [g67, g68, metaVal_64]
    rfl

theorem metaStep65 : MetaStepOK W n lc c 65 (metaStepBlock 65) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_39 n lc c = (packedRankWordSize n) / (packedRankWordSize n) := rfl
    have hv65 : mv_q_39 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_65] using metaVal_le n lc c hpay 65 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((packedRankWordSize n)) ((packedRankWordSize n))
    pre1_meta_simp [g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g39, metaVal_65]
    rfl

theorem metaStep66 : MetaStepOK W n lc c 66 (metaStepBlock 66) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m65 : r 294 = mv_q_39 n lc c := by simpa only [metaVal_65, Nat.reduceAdd] using hm 65 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_39 n lc c = (mv_q_39 n lc c) + ((if (packedRankWordSize n) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv66 : mv_cc_39 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_66] using metaVal_le n lc c hpay 66 (by decide)
    have hv65 : mv_q_39 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_65] using metaVal_le n lc c hpay 65 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((packedRankWordSize n)) ((packedRankWordSize n))
    pre1_meta_simp [g39, m65, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m65 : r 294 = mv_q_39 n lc c := by simpa only [metaVal_65, Nat.reduceAdd] using hm 65 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g39, m65, g0, metaVal_66]
    rfl

theorem metaStep67 : MetaStepOK W n lc c 67 (metaStepBlock 67) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_61 n lc c = ((packedInteriorLayout n).relativeWidth) / (packedRankWordSize n) := rfl
    have hv67 : mv_q_61 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_67] using metaVal_le n lc c hpay 67 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((packedInteriorLayout n).relativeWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g61, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g61, g39, metaVal_67]
    rfl

theorem metaStep68 : MetaStepOK W n lc c 68 (metaStepBlock 68) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m67 : r 296 = mv_q_61 n lc c := by simpa only [metaVal_67, Nat.reduceAdd] using hm 67 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_61 n lc c = (mv_q_61 n lc c) + ((if ((packedInteriorLayout n).relativeWidth) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv68 : mv_cc_61 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_68] using metaVal_le n lc c hpay 68 (by decide)
    have hv67 : mv_q_61 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_67] using metaVal_le n lc c hpay 67 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le (((packedInteriorLayout n).relativeWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g61, g39, m67, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m67 : r 296 = mv_q_61 n lc c := by simpa only [metaVal_67, Nat.reduceAdd] using hm 67 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g61, g39, m67, g0, metaVal_68]
    rfl

theorem metaStep69 : MetaStepOK W n lc c 69 (metaStepBlock 69) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_58 n lc c = ((packedInteriorLayout n).offsetWidth) / (packedRankWordSize n) := rfl
    have hv69 : mv_q_58 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_69] using metaVal_le n lc c hpay 69 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((packedInteriorLayout n).offsetWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g58, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g58, g39, metaVal_69]
    rfl

theorem metaStep70 : MetaStepOK W n lc c 70 (metaStepBlock 70) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m69 : r 298 = mv_q_58 n lc c := by simpa only [metaVal_69, Nat.reduceAdd] using hm 69 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_58 n lc c = (mv_q_58 n lc c) + ((if ((packedInteriorLayout n).offsetWidth) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv70 : mv_cc_58 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_70] using metaVal_le n lc c hpay 70 (by decide)
    have hv69 : mv_q_58 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_69] using metaVal_le n lc c hpay 69 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le (((packedInteriorLayout n).offsetWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g58, g39, m69, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m69 : r 298 = mv_q_58 n lc c := by simpa only [metaVal_69, Nat.reduceAdd] using hm 69 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g58, g39, m69, g0, metaVal_70]
    rfl

theorem metaStep71 : MetaStepOK W n lc c 71 (metaStepBlock 71) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_60 n lc c = ((packedInteriorLayout n).blockAddressWidth) / (packedRankWordSize n) := rfl
    have hv71 : mv_q_60 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_71] using metaVal_le n lc c hpay 71 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((packedInteriorLayout n).blockAddressWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g60, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g60, g39, metaVal_71]
    rfl

theorem metaStep72 : MetaStepOK W n lc c 72 (metaStepBlock 72) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m71 : r 300 = mv_q_60 n lc c := by simpa only [metaVal_71, Nat.reduceAdd] using hm 71 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_60 n lc c = (mv_q_60 n lc c) + ((if ((packedInteriorLayout n).blockAddressWidth) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv72 : mv_cc_60 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_72] using metaVal_le n lc c hpay 72 (by decide)
    have hv71 : mv_q_60 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_71] using metaVal_le n lc c hpay 71 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le (((packedInteriorLayout n).blockAddressWidth)) ((packedRankWordSize n))
    pre1_meta_simp [g60, g39, m71, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m71 : r 300 = mv_q_60 n lc c := by simpa only [metaVal_71, Nat.reduceAdd] using hm 71 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g60, g39, m71, g0, metaVal_72]
    rfl

theorem metaStep73 : MetaStepOK W n lc c 73 (metaStepBlock 73) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_36 n lc c = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) / (packedRankWordSize n) := rfl
    have hv73 : mv_q_36 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_73] using metaVal_le n lc c hpay 73 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize))) ((packedRankWordSize n))
    pre1_meta_simp [g36, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g36, g39, metaVal_73]
    rfl

theorem metaStep74 : MetaStepOK W n lc c 74 (metaStepBlock 74) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m73 : r 302 = mv_q_36 n lc c := by simpa only [metaVal_73, Nat.reduceAdd] using hm 73 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_36 n lc c = (mv_q_36 n lc c) + ((if (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv74 : mv_cc_36 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_74] using metaVal_le n lc c hpay 74 (by decide)
    have hv73 : mv_q_36 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_73] using metaVal_le n lc c hpay 73 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize))) ((packedRankWordSize n))
    pre1_meta_simp [g36, g39, m73, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m73 : r 302 = mv_q_36 n lc c := by simpa only [metaVal_73, Nat.reduceAdd] using hm 73 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g36, g39, m73, g0, metaVal_74]
    rfl

theorem metaStep75 : MetaStepOK W n lc c 75 (metaStepBlock 75) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q_37 n lc c = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) / (packedRankWordSize n) := rfl
    have hv75 : mv_q_37 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_75] using metaVal_le n lc c hpay 75 (by decide)
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount))) ((packedRankWordSize n))
    pre1_meta_simp [g37, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g37, g39, metaVal_75]
    rfl

theorem metaStep76 : MetaStepOK W n lc c 76 (metaStepBlock 76) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m75 : r 304 = mv_q_37 n lc c := by simpa only [metaVal_75, Nat.reduceAdd] using hm 75 (by decide)
    have g0 : r 0 = 0 := h0
    have e : mv_cc_37 n lc c = (mv_q_37 n lc c) + ((if (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) % (packedRankWordSize n) = 0 then 0 else 1)) := rfl
    have hv76 : mv_cc_37 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_76] using metaVal_le n lc c hpay 76 (by decide)
    have hv75 : mv_q_37 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_75] using metaVal_le n lc c hpay 75 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.mod_le ((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount))) ((packedRankWordSize n))
    pre1_meta_simp [g37, g39, m75, g0]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have m75 : r 304 = mv_q_37 n lc c := by simpa only [metaVal_75, Nat.reduceAdd] using hm 75 (by decide)
    have g0 : r 0 = 0 := h0
    pre1_meta_simp [g37, g39, m75, g0, metaVal_76]
    rfl

theorem metaStep77 : MetaStepOK W n lc c 77 (metaStepBlock 77) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_39 n lc c = (((packedRankWordSize n) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv77 : mv_cd_39 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_77] using metaVal_le n lc c hpay 77 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((((packedRankWordSize n) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g39, g2, metaVal_77]
    rfl

theorem metaStep78 : MetaStepOK W n lc c 78 (metaStepBlock 78) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_61 n lc c = ((((packedInteriorLayout n).relativeWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv78 : mv_cd_61 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_78] using metaVal_le n lc c hpay 78 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((((packedInteriorLayout n).relativeWidth) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g61, g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g61, g39, g2, metaVal_78]
    rfl

theorem metaStep79 : MetaStepOK W n lc c 79 (metaStepBlock 79) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_58 n lc c = ((((packedInteriorLayout n).offsetWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv79 : mv_cd_58 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_79] using metaVal_le n lc c hpay 79 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((((packedInteriorLayout n).offsetWidth) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g58, g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g58, g39, g2, metaVal_79]
    rfl

theorem metaStep80 : MetaStepOK W n lc c 80 (metaStepBlock 80) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_60 n lc c = ((((packedInteriorLayout n).blockAddressWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv80 : mv_cd_60 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_80] using metaVal_le n lc c hpay 80 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self (((((packedInteriorLayout n).blockAddressWidth) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g60, g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g60, g39, g2, metaVal_80]
    rfl

theorem metaStep81 : MetaStepOK W n lc c 81 (metaStepBlock 81) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_36 n lc c = (((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv81 : mv_cd_36 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_81] using metaVal_le n lc c hpay 81 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g36, g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g36, g39, g2, metaVal_81]
    rfl

theorem metaStep82 : MetaStepOK W n lc c 82 (metaStepBlock 82) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_cd_37 n lc c = (((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) + (packedRankWordSize n)) - 1) / (packedRankWordSize n) := rfl
    have hv82 : mv_cd_37 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_82] using metaVal_le n lc c hpay 82 (by decide)
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos39 : 0 < (packedRankWordSize n) := SuccinctRank.machineWordBits_pos _
    have := Nat.div_le_self ((((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) + (packedRankWordSize n)) - 1)) ((packedRankWordSize n))
    pre1_meta_simp [g37, g39, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [g37, g39, g2, metaVal_82]
    rfl

theorem metaStep83 : MetaStepOK W n lc c 83 (metaStepBlock 83) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g57 : r 57 = ((packedInteriorLayout n).superSampleCount) := hg 19 (by decide)
    have m66 : r 295 = mv_cc_39 n lc c := by simpa only [metaVal_66, Nat.reduceAdd] using hm 66 (by decide)
    have e : mv_BW n lc c = ((packedInteriorLayout n).superSampleCount) * (mv_cc_39 n lc c) := rfl
    have hv83 : mv_BW n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_83] using metaVal_le n lc c hpay 83 (by decide)
    pre1_meta_simp [g57, m66]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g57 : r 57 = ((packedInteriorLayout n).superSampleCount) := hg 19 (by decide)
    have m66 : r 295 = mv_cc_39 n lc c := by simpa only [metaVal_66, Nat.reduceAdd] using hm 66 (by decide)
    pre1_meta_simp [g57, m66, metaVal_83]
    rfl

theorem metaStep84 : MetaStepOK W n lc c 84 (metaStepBlock 84) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g32 : r 32 = ((packedInteriorLayout n).blockCount) := hb.2.2.2.2.2.1
    have m68 : r 297 = mv_cc_61 n lc c := by simpa only [metaVal_68, Nat.reduceAdd] using hm 68 (by decide)
    have e : mv_MR n lc c = ((packedInteriorLayout n).blockCount) * (mv_cc_61 n lc c) := rfl
    have hv84 : mv_MR n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_84] using metaVal_le n lc c hpay 84 (by decide)
    pre1_meta_simp [g32, m68]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g32 : r 32 = ((packedInteriorLayout n).blockCount) := hb.2.2.2.2.2.1
    have m68 : r 297 = mv_cc_61 n lc c := by simpa only [metaVal_68, Nat.reduceAdd] using hm 68 (by decide)
    pre1_meta_simp [g32, m68, metaVal_84]
    rfl

theorem metaStep85 : MetaStepOK W n lc c 85 (metaStepBlock 85) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g62 : r 62 = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) := hg 24 (by decide)
    have m70 : r 299 = mv_cc_58 n lc c := by simpa only [metaVal_70, Nat.reduceAdd] using hm 70 (by decide)
    have e : mv_LT n lc c = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) * (mv_cc_58 n lc c) := rfl
    have hv85 : mv_LT n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_85] using metaVal_le n lc c hpay 85 (by decide)
    pre1_meta_simp [g62, m70]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g62 : r 62 = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) := hg 24 (by decide)
    have m70 : r 299 = mv_cc_58 n lc c := by simpa only [metaVal_70, Nat.reduceAdd] using hm 70 (by decide)
    pre1_meta_simp [g62, m70, metaVal_85]
    rfl

theorem metaStep86 : MetaStepOK W n lc c 86 (metaStepBlock 86) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g63 : r 63 = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) := hg 25 (by decide)
    have m72 : r 301 = mv_cc_60 n lc c := by simpa only [metaVal_72, Nat.reduceAdd] using hm 72 (by decide)
    have e : mv_GT n lc c = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) * (mv_cc_60 n lc c) := rfl
    have hv86 : mv_GT n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_86] using metaVal_le n lc c hpay 86 (by decide)
    pre1_meta_simp [g63, m72]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g63 : r 63 = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) := hg 25 (by decide)
    have m72 : r 301 = mv_cc_60 n lc c := by simpa only [metaVal_72, Nat.reduceAdd] using hm 72 (by decide)
    pre1_meta_simp [g63, m72, metaVal_86]
    rfl

theorem metaStep87 : MetaStepOK W n lc c 87 (metaStepBlock 87) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g34 : r 34 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) := hb.2.2.2.2.2.2.2.1
    have m74 : r 303 = mv_cc_36 n lc c := by simpa only [metaVal_74, Nat.reduceAdd] using hm 74 (by decide)
    have e : mv_LL n lc c = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) * (mv_cc_36 n lc c) := rfl
    have hv87 : mv_LL n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_87] using metaVal_le n lc c hpay 87 (by decide)
    pre1_meta_simp [g34, m74]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g34 : r 34 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) := hb.2.2.2.2.2.2.2.1
    have m74 : r 303 = mv_cc_36 n lc c := by simpa only [metaVal_74, Nat.reduceAdd] using hm 74 (by decide)
    pre1_meta_simp [g34, m74, metaVal_87]
    rfl

theorem metaStep88 : MetaStepOK W n lc c 88 (metaStepBlock 88) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g35 : r 35 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) := hb.2.2.2.2.2.2.2.2.1
    have m76 : r 305 = mv_cc_37 n lc c := by simpa only [metaVal_76, Nat.reduceAdd] using hm 76 (by decide)
    have e : mv_GL n lc c = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) * (mv_cc_37 n lc c) := rfl
    have hv88 : mv_GL n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_88] using metaVal_le n lc c hpay 88 (by decide)
    pre1_meta_simp [g35, m76]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g35 : r 35 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) := hb.2.2.2.2.2.2.2.2.1
    have m76 : r 305 = mv_cc_37 n lc c := by simpa only [metaVal_76, Nat.reduceAdd] using hm 76 (by decide)
    pre1_meta_simp [g35, m76, metaVal_88]
    rfl

theorem metaStep89 : MetaStepOK W n lc c 89 (metaStepBlock 89) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m83 : r 312 = mv_BW n lc c := by simpa only [metaVal_83, Nat.reduceAdd] using hm 83 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    have e : mv_p2 n lc c = (mv_BW n lc c) + (mv_MR n lc c) := rfl
    have hv89 : mv_p2 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_89] using metaVal_le n lc c hpay 89 (by decide)
    pre1_meta_simp [m83, m84]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m83 : r 312 = mv_BW n lc c := by simpa only [metaVal_83, Nat.reduceAdd] using hm 83 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    pre1_meta_simp [m83, m84, metaVal_89]
    rfl

theorem metaStep90 : MetaStepOK W n lc c 90 (metaStepBlock 90) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m89 : r 318 = mv_p2 n lc c := by simpa only [metaVal_89, Nat.reduceAdd] using hm 89 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    have e : mv_p3 n lc c = (mv_p2 n lc c) + (mv_MR n lc c) := rfl
    have hv90 : mv_p3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_90] using metaVal_le n lc c hpay 90 (by decide)
    pre1_meta_simp [m89, m84]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m89 : r 318 = mv_p2 n lc c := by simpa only [metaVal_89, Nat.reduceAdd] using hm 89 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    pre1_meta_simp [m89, m84, metaVal_90]
    rfl

theorem metaStep91 : MetaStepOK W n lc c 91 (metaStepBlock 91) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m90 : r 319 = mv_p3 n lc c := by simpa only [metaVal_90, Nat.reduceAdd] using hm 90 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    have e : mv_p4 n lc c = (mv_p3 n lc c) + (mv_MR n lc c) := rfl
    have hv91 : mv_p4 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_91] using metaVal_le n lc c hpay 91 (by decide)
    pre1_meta_simp [m90, m84]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m90 : r 319 = mv_p3 n lc c := by simpa only [metaVal_90, Nat.reduceAdd] using hm 90 (by decide)
    have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
    pre1_meta_simp [m90, m84, metaVal_91]
    rfl

theorem metaStep92 : MetaStepOK W n lc c 92 (metaStepBlock 92) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m91 : r 320 = mv_p4 n lc c := by simpa only [metaVal_91, Nat.reduceAdd] using hm 91 (by decide)
    have m85 : r 314 = mv_LT n lc c := by simpa only [metaVal_85, Nat.reduceAdd] using hm 85 (by decide)
    have e : mv_p5 n lc c = (mv_p4 n lc c) + (mv_LT n lc c) := rfl
    have hv92 : mv_p5 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_92] using metaVal_le n lc c hpay 92 (by decide)
    pre1_meta_simp [m91, m85]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m91 : r 320 = mv_p4 n lc c := by simpa only [metaVal_91, Nat.reduceAdd] using hm 91 (by decide)
    have m85 : r 314 = mv_LT n lc c := by simpa only [metaVal_85, Nat.reduceAdd] using hm 85 (by decide)
    pre1_meta_simp [m91, m85, metaVal_92]
    rfl

theorem metaStep93 : MetaStepOK W n lc c 93 (metaStepBlock 93) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m92 : r 321 = mv_p5 n lc c := by simpa only [metaVal_92, Nat.reduceAdd] using hm 92 (by decide)
    have m86 : r 315 = mv_GT n lc c := by simpa only [metaVal_86, Nat.reduceAdd] using hm 86 (by decide)
    have e : mv_p6 n lc c = (mv_p5 n lc c) + (mv_GT n lc c) := rfl
    have hv93 : mv_p6 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_93] using metaVal_le n lc c hpay 93 (by decide)
    pre1_meta_simp [m92, m86]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m92 : r 321 = mv_p5 n lc c := by simpa only [metaVal_92, Nat.reduceAdd] using hm 92 (by decide)
    have m86 : r 315 = mv_GT n lc c := by simpa only [metaVal_86, Nat.reduceAdd] using hm 86 (by decide)
    pre1_meta_simp [m92, m86, metaVal_93]
    rfl

theorem metaStep94 : MetaStepOK W n lc c 94 (metaStepBlock 94) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m93 : r 322 = mv_p6 n lc c := by simpa only [metaVal_93, Nat.reduceAdd] using hm 93 (by decide)
    have m87 : r 316 = mv_LL n lc c := by simpa only [metaVal_87, Nat.reduceAdd] using hm 87 (by decide)
    have e : mv_p7 n lc c = (mv_p6 n lc c) + (mv_LL n lc c) := rfl
    have hv94 : mv_p7 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_94] using metaVal_le n lc c hpay 94 (by decide)
    pre1_meta_simp [m93, m87]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m93 : r 322 = mv_p6 n lc c := by simpa only [metaVal_93, Nat.reduceAdd] using hm 93 (by decide)
    have m87 : r 316 = mv_LL n lc c := by simpa only [metaVal_87, Nat.reduceAdd] using hm 87 (by decide)
    pre1_meta_simp [m93, m87, metaVal_94]
    rfl

theorem metaStep95 : MetaStepOK W n lc c 95 (metaStepBlock 95) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m94 : r 323 = mv_p7 n lc c := by simpa only [metaVal_94, Nat.reduceAdd] using hm 94 (by decide)
    have m88 : r 317 = mv_GL n lc c := by simpa only [metaVal_88, Nat.reduceAdd] using hm 88 (by decide)
    have e : mv_ptot n lc c = (mv_p7 n lc c) + (mv_GL n lc c) := rfl
    have hv95 : mv_ptot n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_95] using metaVal_le n lc c hpay 95 (by decide)
    pre1_meta_simp [m94, m88]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m94 : r 323 = mv_p7 n lc c := by simpa only [metaVal_94, Nat.reduceAdd] using hm 94 (by decide)
    have m88 : r 317 = mv_GL n lc c := by simpa only [metaVal_88, Nat.reduceAdd] using hm 88 (by decide)
    pre1_meta_simp [m94, m88, metaVal_95]
    rfl

theorem metaStep96 : MetaStepOK W n lc c 96 (metaStepBlock 96) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g57 : r 57 = ((packedInteriorLayout n).superSampleCount) := hg 19 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_q1bits n lc c = ((packedInteriorLayout n).superSampleCount) * (packedRankWordSize n) := rfl
    have hv96 : mv_q1bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_96] using metaVal_le n lc c hpay 96 (by decide)
    pre1_meta_simp [g57, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g57 : r 57 = ((packedInteriorLayout n).superSampleCount) := hg 19 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g57, g39, metaVal_96]
    rfl

theorem metaStep97 : MetaStepOK W n lc c 97 (metaStepBlock 97) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g32 : r 32 = ((packedInteriorLayout n).blockCount) := hb.2.2.2.2.2.1
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    have e : mv_q2bits n lc c = ((packedInteriorLayout n).blockCount) * ((packedInteriorLayout n).relativeWidth) := rfl
    have hv97 : mv_q2bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_97] using metaVal_le n lc c hpay 97 (by decide)
    pre1_meta_simp [g32, g61]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g32 : r 32 = ((packedInteriorLayout n).blockCount) := hb.2.2.2.2.2.1
    have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
    pre1_meta_simp [g32, g61, metaVal_97]
    rfl

theorem metaStep98 : MetaStepOK W n lc c 98 (metaStepBlock 98) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g62 : r 62 = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) := hg 24 (by decide)
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    have e : mv_q5bits n lc c = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) * ((packedInteriorLayout n).offsetWidth) := rfl
    have hv98 : mv_q5bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_98] using metaVal_le n lc c hpay 98 (by decide)
    pre1_meta_simp [g62, g58]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g62 : r 62 = ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) := hg 24 (by decide)
    have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
    pre1_meta_simp [g62, g58, metaVal_98]
    rfl

theorem metaStep99 : MetaStepOK W n lc c 99 (metaStepBlock 99) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g63 : r 63 = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) := hg 25 (by decide)
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    have e : mv_q6bits n lc c = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) * ((packedInteriorLayout n).blockAddressWidth) := rfl
    have hv99 : mv_q6bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_99] using metaVal_le n lc c hpay 99 (by decide)
    pre1_meta_simp [g63, g60]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g63 : r 63 = ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) := hg 25 (by decide)
    have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
    pre1_meta_simp [g63, g60, metaVal_99]
    rfl

theorem metaStep100 : MetaStepOK W n lc c 100 (metaStepBlock 100) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g34 : r 34 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) := hb.2.2.2.2.2.2.2.1
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    have e : mv_q7bits n lc c = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) * (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := rfl
    have hv100 : mv_q7bits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_100] using metaVal_le n lc c hpay 100 (by decide)
    pre1_meta_simp [g34, g36]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g34 : r 34 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) := hb.2.2.2.2.2.2.2.1
    have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
    pre1_meta_simp [g34, g36, metaVal_100]
    rfl

theorem metaStep101 : MetaStepOK W n lc c 101 (metaStepBlock 101) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m55 : r 284 = mv_ib0 n lc c := by simpa only [metaVal_55, Nat.reduceAdd] using hm 55 (by decide)
    have m96 : r 325 = mv_q1bits n lc c := by simpa only [metaVal_96, Nat.reduceAdd] using hm 96 (by decide)
    have e : mv_ib1 n lc c = (mv_ib0 n lc c) + (mv_q1bits n lc c) := rfl
    have hv101 : mv_ib1 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_101] using metaVal_le n lc c hpay 101 (by decide)
    pre1_meta_simp [m55, m96]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m55 : r 284 = mv_ib0 n lc c := by simpa only [metaVal_55, Nat.reduceAdd] using hm 55 (by decide)
    have m96 : r 325 = mv_q1bits n lc c := by simpa only [metaVal_96, Nat.reduceAdd] using hm 96 (by decide)
    pre1_meta_simp [m55, m96, metaVal_101]
    rfl

theorem metaStep102 : MetaStepOK W n lc c 102 (metaStepBlock 102) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m101 : r 330 = mv_ib1 n lc c := by simpa only [metaVal_101, Nat.reduceAdd] using hm 101 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    have e : mv_ib2 n lc c = (mv_ib1 n lc c) + (mv_q2bits n lc c) := rfl
    have hv102 : mv_ib2 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_102] using metaVal_le n lc c hpay 102 (by decide)
    pre1_meta_simp [m101, m97]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m101 : r 330 = mv_ib1 n lc c := by simpa only [metaVal_101, Nat.reduceAdd] using hm 101 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    pre1_meta_simp [m101, m97, metaVal_102]
    rfl

theorem metaStep103 : MetaStepOK W n lc c 103 (metaStepBlock 103) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m102 : r 331 = mv_ib2 n lc c := by simpa only [metaVal_102, Nat.reduceAdd] using hm 102 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    have e : mv_ib3 n lc c = (mv_ib2 n lc c) + (mv_q2bits n lc c) := rfl
    have hv103 : mv_ib3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_103] using metaVal_le n lc c hpay 103 (by decide)
    pre1_meta_simp [m102, m97]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m102 : r 331 = mv_ib2 n lc c := by simpa only [metaVal_102, Nat.reduceAdd] using hm 102 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    pre1_meta_simp [m102, m97, metaVal_103]
    rfl

theorem metaStep104 : MetaStepOK W n lc c 104 (metaStepBlock 104) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m103 : r 332 = mv_ib3 n lc c := by simpa only [metaVal_103, Nat.reduceAdd] using hm 103 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    have e : mv_ib4 n lc c = (mv_ib3 n lc c) + (mv_q2bits n lc c) := rfl
    have hv104 : mv_ib4 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_104] using metaVal_le n lc c hpay 104 (by decide)
    pre1_meta_simp [m103, m97]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m103 : r 332 = mv_ib3 n lc c := by simpa only [metaVal_103, Nat.reduceAdd] using hm 103 (by decide)
    have m97 : r 326 = mv_q2bits n lc c := by simpa only [metaVal_97, Nat.reduceAdd] using hm 97 (by decide)
    pre1_meta_simp [m103, m97, metaVal_104]
    rfl

theorem metaStep105 : MetaStepOK W n lc c 105 (metaStepBlock 105) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m104 : r 333 = mv_ib4 n lc c := by simpa only [metaVal_104, Nat.reduceAdd] using hm 104 (by decide)
    have m98 : r 327 = mv_q5bits n lc c := by simpa only [metaVal_98, Nat.reduceAdd] using hm 98 (by decide)
    have e : mv_ib5 n lc c = (mv_ib4 n lc c) + (mv_q5bits n lc c) := rfl
    have hv105 : mv_ib5 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_105] using metaVal_le n lc c hpay 105 (by decide)
    pre1_meta_simp [m104, m98]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m104 : r 333 = mv_ib4 n lc c := by simpa only [metaVal_104, Nat.reduceAdd] using hm 104 (by decide)
    have m98 : r 327 = mv_q5bits n lc c := by simpa only [metaVal_98, Nat.reduceAdd] using hm 98 (by decide)
    pre1_meta_simp [m104, m98, metaVal_105]
    rfl

theorem metaStep106 : MetaStepOK W n lc c 106 (metaStepBlock 106) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m105 : r 334 = mv_ib5 n lc c := by simpa only [metaVal_105, Nat.reduceAdd] using hm 105 (by decide)
    have m99 : r 328 = mv_q6bits n lc c := by simpa only [metaVal_99, Nat.reduceAdd] using hm 99 (by decide)
    have e : mv_ib6 n lc c = (mv_ib5 n lc c) + (mv_q6bits n lc c) := rfl
    have hv106 : mv_ib6 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_106] using metaVal_le n lc c hpay 106 (by decide)
    pre1_meta_simp [m105, m99]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m105 : r 334 = mv_ib5 n lc c := by simpa only [metaVal_105, Nat.reduceAdd] using hm 105 (by decide)
    have m99 : r 328 = mv_q6bits n lc c := by simpa only [metaVal_99, Nat.reduceAdd] using hm 99 (by decide)
    pre1_meta_simp [m105, m99, metaVal_106]
    rfl

theorem metaStep107 : MetaStepOK W n lc c 107 (metaStepBlock 107) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m106 : r 335 = mv_ib6 n lc c := by simpa only [metaVal_106, Nat.reduceAdd] using hm 106 (by decide)
    have m100 : r 329 = mv_q7bits n lc c := by simpa only [metaVal_100, Nat.reduceAdd] using hm 100 (by decide)
    have e : mv_ib7 n lc c = (mv_ib6 n lc c) + (mv_q7bits n lc c) := rfl
    have hv107 : mv_ib7 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_107] using metaVal_le n lc c hpay 107 (by decide)
    pre1_meta_simp [m106, m100]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m106 : r 335 = mv_ib6 n lc c := by simpa only [metaVal_106, Nat.reduceAdd] using hm 106 (by decide)
    have m100 : r 329 = mv_q7bits n lc c := by simpa only [metaVal_100, Nat.reduceAdd] using hm 100 (by decide)
    pre1_meta_simp [m106, m100, metaVal_107]
    rfl

/-- Every metadata bank step meets its step contract. -/
theorem metaStep_all : ∀ i, i < 108 → MetaStepOK W n lc c i (metaStepBlock i)
  | 0, _ => metaStep0 hW hcap hpay
  | 1, _ => metaStep1 hW hcap hpay
  | 2, _ => metaStep2 hW hcap hpay
  | 3, _ => metaStep3 hW hcap hpay
  | 4, _ => metaStep4 hW hcap hpay
  | 5, _ => metaStep5 hW hcap hpay
  | 6, _ => metaStep6 hW hcap hpay
  | 7, _ => metaStep7 hW hcap hpay
  | 8, _ => metaStep8 hW hcap hpay
  | 9, _ => metaStep9 hW hcap hpay
  | 10, _ => metaStep10 hW hcap hpay
  | 11, _ => metaStep11 hW hcap hpay
  | 12, _ => metaStep12 hW hcap hpay
  | 13, _ => metaStep13 hW hcap hpay
  | 14, _ => metaStep14 hW hcap hpay
  | 15, _ => metaStep15 hW hcap hpay
  | 16, _ => metaStep16 hW hcap hpay
  | 17, _ => metaStep17 hW hcap hpay
  | 18, _ => metaStep18 hW hcap hpay
  | 19, _ => metaStep19 hW hcap hpay
  | 20, _ => metaStep20 hW hcap hpay
  | 21, _ => metaStep21 hW hcap hpay
  | 22, _ => metaStep22 hW hcap hpay
  | 23, _ => metaStep23 hW hcap hpay
  | 24, _ => metaStep24 hW hcap hpay
  | 25, _ => metaStep25 hW hcap hpay
  | 26, _ => metaStep26 hW hcap hpay
  | 27, _ => metaStep27 hW hcap hpay
  | 28, _ => metaStep28 hW hcap hpay
  | 29, _ => metaStep29 hW hcap hpay
  | 30, _ => metaStep30 hW hcap hpay
  | 31, _ => metaStep31 hW hcap hpay
  | 32, _ => metaStep32 hW hcap hpay
  | 33, _ => metaStep33 hW hcap hpay
  | 34, _ => metaStep34 hW hcap hpay
  | 35, _ => metaStep35 hW hcap hpay
  | 36, _ => metaStep36 hW hcap hpay
  | 37, _ => metaStep37 hW hcap hpay
  | 38, _ => metaStep38 hW hcap hpay
  | 39, _ => metaStep39 hW hcap hpay
  | 40, _ => metaStep40 hW hcap hpay
  | 41, _ => metaStep41 hW hcap hpay
  | 42, _ => metaStep42 hW hcap hpay
  | 43, _ => metaStep43 hW hcap hpay
  | 44, _ => metaStep44 hW hcap hpay
  | 45, _ => metaStep45 hW hcap hpay
  | 46, _ => metaStep46 hW hcap hpay
  | 47, _ => metaStep47 hW hcap hpay
  | 48, _ => metaStep48 hW hcap hpay
  | 49, _ => metaStep49 hW hcap hpay
  | 50, _ => metaStep50 hW hcap hpay
  | 51, _ => metaStep51 hW hcap hpay
  | 52, _ => metaStep52 hW hcap hpay
  | 53, _ => metaStep53 hW hcap hpay
  | 54, _ => metaStep54 hW hcap hpay
  | 55, _ => metaStep55 hW hcap hpay
  | 56, _ => metaStep56 hW hcap hpay
  | 57, _ => metaStep57 hW hcap hpay
  | 58, _ => metaStep58 hW hcap hpay
  | 59, _ => metaStep59 hW hcap hpay
  | 60, _ => metaStep60 hW hcap hpay
  | 61, _ => metaStep61 hW hcap hpay
  | 62, _ => metaStep62 hW hcap hpay
  | 63, _ => metaStep63 hW hcap hpay
  | 64, _ => metaStep64 hW hcap hpay
  | 65, _ => metaStep65 hW hcap hpay
  | 66, _ => metaStep66 hW hcap hpay
  | 67, _ => metaStep67 hW hcap hpay
  | 68, _ => metaStep68 hW hcap hpay
  | 69, _ => metaStep69 hW hcap hpay
  | 70, _ => metaStep70 hW hcap hpay
  | 71, _ => metaStep71 hW hcap hpay
  | 72, _ => metaStep72 hW hcap hpay
  | 73, _ => metaStep73 hW hcap hpay
  | 74, _ => metaStep74 hW hcap hpay
  | 75, _ => metaStep75 hW hcap hpay
  | 76, _ => metaStep76 hW hcap hpay
  | 77, _ => metaStep77 hW hcap hpay
  | 78, _ => metaStep78 hW hcap hpay
  | 79, _ => metaStep79 hW hcap hpay
  | 80, _ => metaStep80 hW hcap hpay
  | 81, _ => metaStep81 hW hcap hpay
  | 82, _ => metaStep82 hW hcap hpay
  | 83, _ => metaStep83 hW hcap hpay
  | 84, _ => metaStep84 hW hcap hpay
  | 85, _ => metaStep85 hW hcap hpay
  | 86, _ => metaStep86 hW hcap hpay
  | 87, _ => metaStep87 hW hcap hpay
  | 88, _ => metaStep88 hW hcap hpay
  | 89, _ => metaStep89 hW hcap hpay
  | 90, _ => metaStep90 hW hcap hpay
  | 91, _ => metaStep91 hW hcap hpay
  | 92, _ => metaStep92 hW hcap hpay
  | 93, _ => metaStep93 hW hcap hpay
  | 94, _ => metaStep94 hW hcap hpay
  | 95, _ => metaStep95 hW hcap hpay
  | 96, _ => metaStep96 hW hcap hpay
  | 97, _ => metaStep97 hW hcap hpay
  | 98, _ => metaStep98 hW hcap hpay
  | 99, _ => metaStep99 hW hcap hpay
  | 100, _ => metaStep100 hW hcap hpay
  | 101, _ => metaStep101 hW hcap hpay
  | 102, _ => metaStep102 hW hcap hpay
  | 103, _ => metaStep103 hW hcap hpay
  | 104, _ => metaStep104 hW hcap hpay
  | 105, _ => metaStep105 hW hcap hpay
  | 106, _ => metaStep106 hW hcap hpay
  | 107, _ => metaStep107 hW hcap hpay
  | _ + 108, h => absurd h (by omega)

/-- **The metadata chain.** -/
theorem metaChain_spec : ∀ k, k ≤ 108 → ∀ s : State, s.status = .running →
    MetaBase n lc c s.regs →
    ∃ s' j, SafeEval W (metaChain k) s s' j ∧ j ≤ 6 * k ∧ s'.status = .running ∧
      MetaBase n lc c s'.regs ∧ MetaUpTo n lc c k s'.regs ∧
      (∀ x : Nat, ¬ (229 ≤ x ∧ x < 229 + k) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs
  | 0, _, s, hrun, hb =>
      ⟨s, 0, EvalG.skip s hrun, by simp, hrun, hb, fun _ hi => absurd hi (by omega),
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, hrun, hb => by
      obtain ⟨s₁, j₁, e₁, hj₁, hr₁, hb₁, hm₁, hf₁, hmem₁, he₁, hks₁, hkr₁⟩ :=
        metaChain_spec k (by omega) s hrun hb
      obtain ⟨s₂, j₂, e₂, hj₂, hr₂, hv₂, hf₂, hmem₂, he₂, hks₂, hkr₂⟩ :=
        metaStep_all hW hcap hpay k (by omega) s₁ hr₁ hb₁ hm₁
      have hframe : ∀ x : Nat, ¬ (229 ≤ x ∧ x < 229 + (k + 1)) → s₂.regs x = s.regs x := by
        intro x hx
        rw [hf₂ x (by omega), hf₁ x (by omega)]
      refine ⟨s₂, j₁ + j₂, EvalG.seq e₁ e₂, by omega, hr₂, ?_, ?_, hframe,
        by rw [hmem₂, hmem₁], by rw [he₂, he₁], by rw [hks₂, hks₁], by rw [hkr₂, hkr₁]⟩
      · obtain ⟨⟨a1, a2, a9, a30, a31, a32, a33, a34, a35, a36, a37⟩, hg, a177, a178, a0⟩ := hb
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i hi => ?_, ?_, ?_, ?_⟩
        all_goals first
          | (rw [hframe _ (by omega)]; assumption)
          | (rw [hframe _ (by omega)]; exact hg i hi)
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rw [hf₂ (229 + i) (by omega)]; exact hm₁ i h
        · subst h; exact hv₂

end Steps

end RMQ.SuccinctFinal.PackedConstruction.Proof

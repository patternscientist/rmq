import RMQ.Core.WordRAM.Construction.Proof.InteriorClose
import RMQ.Core.WordRAM.Construction.Builder.Access
import RMQ.Core.WordRAM.Construction.Spec.Access

/-! # PRE-1 builder proofs: the occurrence pass (stage S5)

Outside the builder firewall. One scan of the BP cells of a shape fills the
close-position array `POS[k] = position shape.bpCode false k` for `k ≤ n` (the
clamp `2n` at `k = n`) and the word-boundary rank array
`RW[j] = rankPrefix false shape.bpCode (j * ws)` for `j * ws ≤ 2n`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect

/-- **One scan position.** -/
theorem posStep_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (B P0 R0 ws p : Nat) (h119 : u.regs 119 = B) (h159 : u.regs 159 = P0)
    (h160 : u.regs 160 = R0) (h39 : u.regs 39 = ws) (h38 : u.regs 38 = shape.bpCode.length)
    (h165 : u.regs 165 = p) (h168 : u.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode p)
    (hws : 1 ≤ ws) (hp : p ≤ shape.bpCode.length)
    (hR : Region u B shape.bpCode.length (bpCell shape))
    (hord : P0 + shape.size + 1 ≤ R0) (hordR : R0 + shape.bpCode.length / ws + 1 ≤ B)
    (hext : B + shape.bpCode.length ≤ u.extent) (hextW : u.extent < 2 ^ W) :
    ∃ u' j, SafeEval W posStepBlock u u' j ∧ j ≤ 16 ∧ u'.status = .running ∧
      u'.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) ∧
      (∀ a, (a < P0 ∨ R0 + shape.bpCode.length / ws + 1 ≤ a) → u'.memory a = u.memory a) ∧
      (∀ k, k < RMQ.Succinct.rankPrefix false shape.bpCode p →
        u'.memory (P0 + k) = u.memory (P0 + k)) ∧
      (RMQ.Succinct.rankPrefix false shape.bpCode p < RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) →
        u'.memory (P0 + RMQ.Succinct.rankPrefix false shape.bpCode p) =
          some (position shape.bpCode false (RMQ.Succinct.rankPrefix false shape.bpCode p))) ∧
      (∀ j, j * ws = p → u'.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode p)) ∧
      (∀ j, j * ws ≠ p → u'.memory (R0 + j) = u.memory (R0 + j)) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 130 → r ≠ 168 → r ≠ 169 → r ≠ 170 → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys := by
  generalize hc : RMQ.Succinct.rankPrefix false shape.bpCode p = c at *
  have hcn : c ≤ shape.size := by
    rw [← hc, ← SuccinctSpace.bpCode_rankFalse_full shape]
    exact RMQ.Succinct.rankPrefix_mono_limit false _ hp
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  have hpW : p < 2 ^ W := by omega
  have hdivle : p / ws ≤ shape.bpCode.length / ws := Nat.div_le_div_right hp
  generalize hLq : shape.bpCode.length / ws = Lq at *
  obtain ⟨pq, hpq⟩ : ∃ x, p / ws = x := ⟨_, rfl⟩
  rw [hpq] at hdivle
  -- A1 := p % ws
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ := prefix_pure hW (.arithmetic .mod rA1 rP rWS) u hrun (by
    simp only [pureOK, Arithmetic.eval, operand_val_165, operand_val_39, h165, h39, reduceCtorEq,
      false_implies, or_true, true_implies]
    repeat' apply And.intro
    all_goals first | trivial | omega | (intro h; simp at h) |
      (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  have v1r : v1.regs = put u.regs 169 (p % ws) := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_169, operand_val_165, operand_val_39,
      h165, h39]
  have ev1 := p1.close
  -- the word-boundary record
  obtain ⟨v2, j2, ev2, hj2, v2s, v2m, v2r, v2e, v2k⟩ :
      ∃ v2 j2, SafeEval W (.ifZero rA1
          (acts [.arithmetic .div rA2 rP rWS, .arithmetic .add rADDR rRWB rA2, .store rADDR rCNT])
          .skip) v1 v2 j2 ∧ j2 ≤ 4 ∧ v2.status = .running ∧
        v2.memory = (if p % ws = 0 then put u.memory (R0 + pq) (some c) else u.memory) ∧
        (∀ r : Nat, r ≠ 108 → r ≠ 170 → v2.regs r = v1.regs r) ∧
        v2.extent = u.extent ∧ v2.keys = u.keys := by
    by_cases hmod : p % ws = 0
    · have hz : v1.regs rA1 = 0 := by show v1.regs 169 = 0; rw [v1r, put_same, hmod]
      obtain ⟨w1, q1, s1, n1, x1, y1, z1⟩ := prefix_pure hW (.arithmetic .div rA2 rP rWS) v1 p1.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_165, operand_val_39, v1r,
          put_ne _ _ (show (165 : Nat) ≠ 169 by decide), put_ne _ _ (show (39 : Nat) ≠ 169 by decide),
          h165, h39, reduceCtorEq, false_implies, or_false, true_implies, and_true]
        repeat' apply And.intro
        all_goals first | trivial | omega | (intro h; simp at h) |
          (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega))
      have w1r : w1.regs = put (put u.regs 169 (p % ws)) 170 (pq) := by
        rw [s1, v1r]; simp only [pureReg, Arithmetic.eval, operand_val_170, operand_val_165,
          operand_val_39, put_ne _ _ (show (165 : Nat) ≠ 169 by decide),
          put_ne _ _ (show (39 : Nat) ≠ 169 by decide), h165, h39, hpq]
      obtain ⟨w2, q2, s2, n2, x2, y2, z2⟩ := prefix_pure hW (.arithmetic .add rADDR rRWB rA2) w1 q1.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_160, operand_val_170, w1r, put_same,
          put_ne _ _ (show (160 : Nat) ≠ 170 by decide), put_ne _ _ (show (160 : Nat) ≠ 169 by decide),
          h160, reduceCtorEq, false_implies, false_or, and_true]
        omega)
      have w2r : w2.regs = put (put (put u.regs 169 (p % ws)) 170 (pq)) 108 (R0 + pq) := by
        rw [s2, w1r]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_160,
          operand_val_170, put_same, put_ne _ _ (show (160 : Nat) ≠ 170 by decide),
          put_ne _ _ (show (160 : Nat) ≠ 169 by decide), h160]
      have hcW : c < 2 ^ W := by omega
      obtain ⟨w3, q3, s3, n3, x3, y3, z3⟩ := prefix_store hW rADDR rCNT w2 q2.1
        (by show w2.regs 108 < w2.extent; rw [w2r, put_same, x2, x1, e1]; omega)
        (by show w2.regs 168 < 2 ^ W
            rw [w2r, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), h168]
            exact hcW)
      have pre := q1.append (q2.append q3)
      refine ⟨w3, 1 + (1 + 1) + 1, EvalG.ifZeroTaken p1.1 hz pre.close, by omega, q3.1, ?_, ?_, ?_, ?_⟩
      · rw [if_pos hmod, n3, n2, n1, m1]
        show put u.memory (w2.regs 108) (some (w2.regs 168)) = _
        rw [w2r, put_same, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), h168]
      · intro r h108 h170
        rw [s3, w2r, put_ne _ _ h108, put_ne _ _ h170, ← v1r]
      · rw [x3, x2, x1, e1]
      · rw [y3, y2, y1, k1]
    · have hz : v1.regs rA1 ≠ 0 := by show v1.regs 169 ≠ 0; rw [v1r, put_same]; exact hmod
      refine ⟨v1, 0 + 2, EvalG.ifZeroFallthrough p1.1 hz (EvalG.skip v1 p1.1) p1.1, by omega, p1.1,
        by rw [if_neg hmod, m1], fun r _ _ => rfl, e1, k1⟩
  have v2get : ∀ r : Nat, r ≠ 108 → r ≠ 169 → r ≠ 170 → v2.regs r = u.regs r := fun r a b c => by
    rw [v2r r a c, v1r, put_ne _ _ b]
  -- A1 := [p < m]
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ := prefix_pure hW (.comparison .lt rA1 rP rM2) v2 v2s trivial
  have v3_169 : v3.regs 169 = if p < shape.bpCode.length then 1 else 0 := by
    rw [r3]; simp only [pureReg, Comparison.eval, operand_val_169, operand_val_165, operand_val_38,
      put_same, v2get 165 (by decide) (by decide) (by decide), v2get 38 (by decide) (by decide) (by decide),
      h165, h38]
  have v3get : ∀ r : Nat, r ≠ 108 → r ≠ 169 → r ≠ 170 → v3.regs r = u.regs r := fun r a b c => by
    rw [r3]; simp only [pureReg, operand_val_169]; rw [put_ne _ _ b, v2get r a b c]
  have ev3 := p3.close
  -- the cell
  obtain ⟨v4, j4, ev4, hj4, v4s, v4_168, v4m, v4r, v4e, v4k⟩ :
      ∃ v4 j4, SafeEval W (.ifZero rA1 .skip
          (.seq (acts [.arithmetic .add rADDR rBPB rP, .load rCELL rADDR])
            (.ifZero rCELL
              (acts [.arithmetic .add rADDR rPOSB rCNT, .store rADDR rP,
                .arithmetic .add rCNT rCNT rONE])
              .skip))) v3 v4 j4 ∧ j4 ≤ 9 ∧ v4.status = .running ∧
        v4.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) ∧
        v4.memory = (if c < RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) then
          put v3.memory (P0 + c) (some p) else v3.memory) ∧
        (∀ r : Nat, r ≠ 108 → r ≠ 130 → r ≠ 168 → v4.regs r = v3.regs r) ∧
        v4.extent = u.extent ∧ v4.keys = u.keys := by
    by_cases hpm : p < shape.bpCode.length
    · have hz : v3.regs rA1 ≠ 0 := by show v3.regs 169 ≠ 0; rw [v3_169, if_pos hpm]; decide
      have hsucc := rankPrefix_false_succ shape.bpCode hpm
      rw [hc] at hsucc
      obtain ⟨w1, q1, s1, n1, x1, y1, z1⟩ := prefix_pure hW (.arithmetic .add rADDR rBPB rP) v3 p3.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_119, operand_val_165,
          v3get 119 (by decide) (by decide) (by decide), v3get 165 (by decide) (by decide) (by decide),
          h119, h165, reduceCtorEq, false_implies, false_or, and_true]; omega)
      have w1_108 : w1.regs 108 = B + p := by
        rw [s1]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_119, operand_val_165,
          v3get 119 (by decide) (by decide) (by decide), v3get 165 (by decide) (by decide) (by decide),
          h119, h165, put_same]
      have hcell := bpCell_eq shape hpm
      obtain ⟨w2, q2, s2, n2, x2, y2, z2⟩ := prefix_load hW rCELL rADDR w1 q1.1 (x := bpCell shape p)
        (by show w1.regs 108 < w1.extent; rw [w1_108, x1, e3, v2e]; omega)
        (by show w1.memory (w1.regs 108) = _; rw [w1_108, n1, m3, v2m]
            split
            · rw [put_ne _ _ (by omega)]; exact hR p hpm
            · exact hR p hpm)
        (by rw [hcell]; split <;> omega)
      have w2_130 : w2.regs 130 = bpCell shape p := by rw [s2, operand_val_130, put_same]
      have w2get : ∀ r : Nat, r ≠ 108 → r ≠ 130 → w2.regs r = v3.regs r := fun r a b => by
        rw [s2, operand_val_130, put_ne _ _ b, s1]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ a]
      cases hb : shape.bpCode[p]
      · -- a close: record it
        have hcell0 : bpCell shape p = 0 := by rw [hcell, hb]; rfl
        have hz2 : w2.regs rCELL = 0 := by show w2.regs 130 = 0; rw [w2_130, hcell0]
        rw [hb] at hsucc
        simp only [Bool.false_eq_true, if_false] at hsucc
        have hcn' : c < shape.size := by
          have h1 := RMQ.Succinct.rankPrefix_mono_limit false shape.bpCode (show p + 1 ≤ shape.bpCode.length by omega)
          rw [SuccinctSpace.bpCode_rankFalse_full] at h1
          omega
        obtain ⟨w3, q3, s3, n3, x3, y3, z3⟩ := prefix_pure hW (.arithmetic .add rADDR rPOSB rCNT) w2 q2.1 (by
          simp only [pureOK, Arithmetic.eval, operand_val_159, operand_val_168,
            w2get 159 (by decide) (by decide), w2get 168 (by decide) (by decide),
            v3get 159 (by decide) (by decide) (by decide), v3get 168 (by decide) (by decide) (by decide),
            h159, h168, reduceCtorEq, false_implies, false_or, and_true]; omega)
        have w3_108 : w3.regs 108 = P0 + c := by
          rw [s3]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_159, operand_val_168,
            w2get 159 (by decide) (by decide), w2get 168 (by decide) (by decide),
            v3get 159 (by decide) (by decide) (by decide), v3get 168 (by decide) (by decide) (by decide),
            h159, h168, put_same]
        have w3get : ∀ r : Nat, r ≠ 108 → r ≠ 130 → w3.regs r = v3.regs r := fun r a b => by
          rw [s3]; simp only [pureReg, operand_val_108]; rw [put_ne _ _ a, w2get r a b]
        obtain ⟨w4, q4, s4, n4, x4, y4, z4⟩ := prefix_store hW rADDR rP w3 q3.1
          (by show w3.regs 108 < w3.extent; rw [w3_108, x3, x2, x1, e3, v2e]; omega)
          (by show w3.regs 165 < 2 ^ W
              rw [w3get 165 (by decide) (by decide), v3get 165 (by decide) (by decide) (by decide), h165]
              exact hpW)
        obtain ⟨w5, q5, s5, n5, x5, y5, z5⟩ := prefix_pure hW (.arithmetic .add rCNT rCNT rONE) w4 q4.1 (by
          simp only [pureOK, Arithmetic.eval, operand_val_168, operand_val_2, s4,
            w3get 168 (by decide) (by decide), w3get 2 (by decide) (by decide),
            v3get 168 (by decide) (by decide) (by decide), v3get 2 (by decide) (by decide) (by decide),
            h168, hone, reduceCtorEq, false_implies, false_or, and_true]; omega)
        have pre2 := q3.append (q4.append q5)
        refine ⟨w5, (1 + 1) + ((1 + (1 + 1)) + 1) + 2,
          EvalG.ifZeroFallthrough p3.1 hz (EvalG.seq (q1.append q2).close
            (EvalG.ifZeroTaken q2.1 hz2 pre2.close)) q5.1, by omega, q5.1, ?_, ?_, ?_, ?_, ?_⟩
        · rw [s5]; simp only [pureReg, Arithmetic.eval, operand_val_168, operand_val_2, s4,
            w3get 168 (by decide) (by decide), w3get 2 (by decide) (by decide),
            v3get 168 (by decide) (by decide) (by decide), v3get 2 (by decide) (by decide) (by decide),
            h168, hone, put_same, hsucc]
        · rw [if_pos (by omega), n5, n4, n3, n2, n1]
          show put v3.memory (w3.regs 108) (some (w3.regs 165)) = _
          rw [w3_108, w3get 165 (by decide) (by decide), v3get 165 (by decide) (by decide) (by decide),
            h165]
        · intro r h108 h130 h168'
          rw [s5]; simp only [pureReg, operand_val_168]
          rw [put_ne _ _ h168', s4, w3get r h108 h130]
        · rw [x5, x4, x3, x2, x1, e3, v2e]
        · rw [y5, y4, y3, y2, y1, k3, v2k]
      · -- an open: nothing to record
        have hcell1 : bpCell shape p = 1 := by rw [hcell, hb]; rfl
        have hz2 : w2.regs rCELL ≠ 0 := by show w2.regs 130 ≠ 0; rw [w2_130, hcell1]; decide
        rw [hb] at hsucc
        simp only [if_true, Nat.add_zero] at hsucc
        refine ⟨w2, (1 + 1) + (0 + 2) + 2,
          EvalG.ifZeroFallthrough p3.1 hz (EvalG.seq (q1.append q2).close
            (EvalG.ifZeroFallthrough q2.1 hz2 (EvalG.skip w2 q2.1) q2.1)) q2.1, by omega, q2.1,
          ?_, ?_, ?_, ?_, ?_⟩
        · rw [w2get 168 (by decide) (by decide), v3get 168 (by decide) (by decide) (by decide), h168, hsucc]
        · rw [if_neg (by omega), n2, n1]
        · intro r h108 h130 _; exact w2get r h108 h130
        · rw [x2, x1, e3, v2e]
        · rw [y2, y1, k3, v2k]
    · have hz : v3.regs rA1 = 0 := by show v3.regs 169 = 0; rw [v3_169, if_neg hpm]
      have hpeq : p = shape.bpCode.length := by omega
      have hr1 : RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) = c := by
        rw [bp_rank_end shape (by omega), ← hc, bp_rank_end shape (by omega)]
      refine ⟨v3, 0 + 1, EvalG.ifZeroTaken p3.1 hz (EvalG.skip v3 p3.1), by omega, p3.1, ?_, ?_,
        fun _ _ _ _ => rfl, by rw [e3, v2e], by rw [k3, v2k]⟩
      · rw [v3get 168 (by decide) (by decide) (by decide), h168, hr1]
      · rw [if_neg (by omega)]
  refine ⟨v4, 1 + (j2 + (1 + j4)), EvalG.seq ev1 (EvalG.seq ev2 (EvalG.seq ev3 ev4)), by omega, v4s,
    v4_168, ?_, ?_, ?_, ?_, ?_, ?_, v4e, v4k⟩
  · intro a ha
    rw [v4m, m3, v2m]
    have h1 : a ≠ R0 + pq := by omega
    split <;> split <;> first | rfl | (rw [put_ne _ _ (by omega)]) | skip
    all_goals first | rfl | (rw [put_ne _ _ h1]) | (rw [put_ne _ _ (by omega), put_ne _ _ h1])
  · intro k hk
    rw [v4m, m3, v2m]
    have h1 : P0 + k ≠ R0 + pq := by omega
    have h2 : P0 + k ≠ P0 + c := by omega
    split <;> split
    all_goals first | rfl | (rw [put_ne _ _ h2, put_ne _ _ h1]) | (rw [put_ne _ _ h2]) | (rw [put_ne _ _ h1])
  · intro hlt
    rw [v4m, if_pos hlt, put_same]
    have hb : shape.bpCode[p]? = some false := by
      have hpm : p < shape.bpCode.length := by
        by_cases hge : p < shape.bpCode.length
        · exact hge
        · have := bp_rank_end shape (show shape.bpCode.length ≤ p + 1 by omega)
          have := bp_rank_end shape (show shape.bpCode.length ≤ p by omega)
          omega
      have hsucc := rankPrefix_false_succ shape.bpCode hpm
      rw [hc] at hsucc
      rw [List.getElem?_eq_getElem hpm]
      cases h : shape.bpCode[p]
      · rfl
      · rw [h] at hsucc; simp at hsucc; omega
    rw [← hc, position_at_close shape.bpCode hb]
  · intro j hj
    rw [v4m, m3, v2m]
    have hmod : p % ws = 0 := by rw [← hj, Nat.mul_mod_left]
    have hdiv : pq = j := by rw [← hpq, ← hj, Nat.mul_div_cancel _ (by omega)]
    rw [if_pos hmod, hdiv]
    split
    · rw [put_ne _ _ (by omega), put_same]
    · rw [put_same]
  · intro j hj
    rw [v4m, m3, v2m]
    have hA : R0 + j ≠ P0 + c := by omega
    by_cases hmod : p % ws = 0
    · have hj' : R0 + j ≠ R0 + pq := by
        intro h
        apply hj
        have hjd : j = pq := by omega
        rw [hjd, ← hpq]; exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      rw [if_pos hmod]
      split
      · rw [put_ne _ _ hA, put_ne _ _ hj']
      · rw [put_ne _ _ hj']
    · rw [if_neg hmod]
      split
      · rw [put_ne _ _ hA]
      · rfl
  · intro r h108 h130 h168 h169 h170
    rw [v4r r h108 h130 h168, v3get r h108 h169 h170]

/-- **Occurrence pass.** -/
theorem posPass_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1)
    (B P0 R0 ws : Nat) (h119 : s.regs 119 = B) (h159 : s.regs 159 = P0)
    (h160 : s.regs 160 = R0) (h39 : s.regs 39 = ws) (h38 : s.regs 38 = shape.bpCode.length)
    (hws : 1 ≤ ws) (hR : Region s B shape.bpCode.length (bpCell shape))
    (hord : P0 + shape.size + 1 ≤ R0) (hordR : R0 + shape.bpCode.length / ws + 1 ≤ B)
    (hext : B + shape.bpCode.length ≤ s.extent) (hextW : s.extent < 2 ^ W) :
    ∃ s' j, SafeEval W posPassBlock s s' j ∧ j ≤ (shape.bpCode.length + 1) * 20 + 7 ∧
      s'.status = .running ∧
      (∀ k, k ≤ shape.size → s'.memory (P0 + k) = some (position shape.bpCode false k)) ∧
      (∀ j, j ≤ shape.bpCode.length / ws →
        s'.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode (j * ws))) ∧
      (∀ a, (a < P0 ∨ R0 + shape.bpCode.length / ws + 1 ≤ a) → s'.memory a = s.memory a) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 130 → ¬ (165 ≤ r ∧ r ≤ 170) → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys := by
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  have hLqle : shape.bpCode.length / ws * ws ≤ shape.bpCode.length := Nat.div_mul_le_self _ _
  generalize hLq : shape.bpCode.length / ws = Lq at *
  -- init
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, _⟩ :=
    RegSpec.pure hW [.constant rCNT 0, .arithmetic .add rM2P1 rM2 rONE] s hrun (by
      pre1_reg_simp [h38, hone]; omega)
  have t168 : t.regs 168 = 0 := by rw [htR]; pre1_reg_simp []
  have t167 : t.regs 167 = shape.bpCode.length + 1 := by rw [htR]; pre1_reg_simp [h38, hone]
  have tfr : ∀ r, r ≠ 167 → r ≠ 168 → t.regs r = s.regs r := fun r a b => by
    rw [htR]; pre1_reg_simp [a, b]
  let Inv : Nat → State → Prop := fun p u =>
    (∀ a, (a < P0 ∨ R0 + Lq + 1 ≤ a) → u.memory a = s.memory a) ∧
      u.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode p ∧
      (∀ k, k < RMQ.Succinct.rankPrefix false shape.bpCode p →
        u.memory (P0 + k) = some (position shape.bpCode false k)) ∧
      (∀ j, j * ws < p →
        u.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode (j * ws))) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 130 → ¬ (165 ≤ r ∧ r ≤ 170) → u.regs r = s.regs r) ∧
      u.extent = s.extent ∧ u.keys = s.keys
  obtain ⟨s1, k1, e1, hk1, hr1, ⟨I1, I2, I3, I4, I5, I6, I7⟩, _, _⟩ :=
    forSlots_spec hW rP rPGO rM2P1 posStepBlock 16 (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv t htr (by rw [tfr 2 (by decide) (by decide), hone])
      (by show t.regs 167 < 2 ^ W; rw [t167]; omega)
      (by
        intro u _ hur hum hue huk _
        have ufr : ∀ r, r ≠ 165 → r ≠ 166 → u.regs r = t.regs r := hur
        refine ⟨fun a _ => by rw [hum, htm], ?_, ?_, ?_, ?_, by rw [hue, hte], by rw [huk, htk]⟩
        · rw [ufr 168 (by decide) (by decide), t168, RMQ.Succinct.rankPrefix_zero]
        · intro k hk; rw [RMQ.Succinct.rankPrefix_zero] at hk; exact absurd hk (Nat.not_lt_zero _)
        · intro j hj; exact absurd hj (Nat.not_lt_zero _)
        · intro r h108 h130 hr
          rw [ufr r (by omega) (by omega), tfr r (by omega) (by omega)])
      (by
        intro p u hp ⟨U1, U2, U3, U4, U5, U6, U7⟩ hur hui hucnt huone
        have hp' : p ≤ shape.bpCode.length := by
          have : p < t.regs 167 := hp
          rw [t167] at this; omega
        have hRu : Region u B shape.bpCode.length (bpCell shape) := by
          intro a ha; rw [U1 _ (Or.inr (by omega))]; exact hR a ha
        have hstep : RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) ≤
            RMQ.Succinct.rankPrefix false shape.bpCode p + 1 := by
          by_cases hpl : p < shape.bpCode.length
          · rw [rankPrefix_false_succ shape.bpCode hpl]; split <;> omega
          · rw [bp_rank_end shape (by omega), bp_rank_end shape (by omega)]; omega
        obtain ⟨u', j, ev, hj, hr', S168, Smem, Sold, Snew, SRW, SRWo, Sfr, Se, Sk⟩ :=
          posStep_spec hW shape u hur huone B P0 R0 ws p
            (by rw [U5 119 (by decide) (by decide) (by decide), h119])
            (by rw [U5 159 (by decide) (by decide) (by decide), h159])
            (by rw [U5 160 (by decide) (by decide) (by decide), h160])
            (by rw [U5 39 (by decide) (by decide) (by decide), h39])
            (by rw [U5 38 (by decide) (by decide) (by decide), h38]) hui U2 hws hp' hRu hord
            (by rw [hLq]; exact hordR) (by rw [U6]; exact hext) (by rw [U6]; exact hextW)
        rw [hLq] at Smem
        refine ⟨u', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show u'.regs 165 = p
          rw [Sfr 165 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hui
        · show u'.regs 167 = t.regs 167
          rw [Sfr 167 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hucnt
        · rw [Sfr 2 (by decide) (by decide) (by decide) (by decide) (by decide), huone]
        · intro v _ hvr hvm hve hvk _
          have vfr : ∀ r, r ≠ 165 → r ≠ 166 → v.regs r = u'.regs r := hvr
          refine ⟨fun a ha => by rw [hvm, Smem a ha, U1 a ha], ?_, ?_, ?_, ?_,
            by rw [hve, Se, U6], by rw [hvk, Sk, U7]⟩
          · rw [vfr 168 (by decide) (by decide), S168]
          · intro k hk
            rw [hvm]
            by_cases hkp : k < RMQ.Succinct.rankPrefix false shape.bpCode p
            · rw [Sold k hkp]; exact U3 k hkp
            · have hkeq : k = RMQ.Succinct.rankPrefix false shape.bpCode p := by omega
              rw [hkeq]; exact Snew (by omega)
          · intro j hj
            rw [hvm]
            by_cases hjp : j * ws = p
            · rw [SRW j hjp, hjp]
            · rw [SRWo j hjp]; exact U4 j (by omega)
          · intro r h108 h130 hr
            rw [vfr r (by omega) (by omega), Sfr r h108 h130 (by omega) (by omega) (by omega)]
            exact U5 r h108 h130 hr)
  rw [show ((rM2P1 : Operand) : Nat) = 167 from rfl, t167] at hk1 I2 I3 I4
  have hsize : RMQ.Succinct.rankPrefix false shape.bpCode (shape.bpCode.length + 1) = shape.size :=
    bp_rank_end shape (by omega)
  rw [hsize] at I2 I3
  have e2 := addStore_pair hW rPOSB rCNT rM2 (by decide) s1 hr1
    (by show s1.regs 159 + s1.regs 168 < s1.extent
        rw [I5 159 (by decide) (by decide) (by decide), h159, I2, I6]; omega)
    (by rw [I6]; exact hextW)
    (by show s1.regs 38 < 2 ^ W; rw [I5 38 (by decide) (by decide) (by decide), h38]; exact hlenW)
  have fm : (addStoreState s1 rPOSB rCNT rM2).memory =
      put s1.memory (P0 + shape.size) (some shape.bpCode.length) := by
    show put s1.memory (s1.regs 159 + s1.regs 168) (some (s1.regs 38)) = _
    rw [I5 159 (by decide) (by decide) (by decide), h159, I2, I5 38 (by decide) (by decide) (by decide), h38]
  refine ⟨addStoreState s1 rPOSB rCNT rM2, jt + (k1 + 2), EvalG.seq et (EvalG.seq e1 e2), ?_, hr1,
    ?_, ?_, ?_, ?_, I6, I7⟩
  · simp at hjt
    have : (shape.bpCode.length + 1) * (16 + 4) + 3 ≤ (shape.bpCode.length + 1) * 20 + 3 := by omega
    omega
  · intro k hk
    rw [fm]
    by_cases hks : k = shape.size
    · rw [hks, put_same, bp_position_size]
    · rw [put_ne _ _ (by omega)]; exact I3 k (by omega)
  · intro j hj
    rw [fm, put_ne _ _ (by omega)]
    have hjws : j * ws ≤ Lq * ws := Nat.mul_le_mul_right ws hj
    exact I4 j (by omega)
  · intro a ha
    rw [fm, put_ne _ _ (by omega)]; exact I1 a ha
  · intro r h108 h130 hr
    show put s1.regs 108 _ r = _
    rw [put_ne _ _ h108]; exact I5 r h108 h130 hr

end RMQ.SuccinctFinal.PackedConstruction.Proof

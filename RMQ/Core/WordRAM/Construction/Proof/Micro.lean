import RMQ.Core.WordRAM.Construction.Proof.AccessHalf
import RMQ.Core.WordRAM.Construction.Builder.Micro
import RMQ.Core.WordRAM.Construction.Spec.Micro

/-! # PRE-1 builder proofs: the two microtables (stage S6)

Outside the builder firewall. A select-chunk row keeps, over the `c` pattern
bits, the remaining bits, the close count and the running position, which is
the reference position once the scan has passed the close of rank `k`
(`selectPos_step`, `selectPos_final`). A fringe row keeps, over the `c + 1`
offsets, the offset-encoded excess and the leftmost minimum over `[a, b)` in the
branch-free keep-left form (`fringeBest_step`); the packed value is
`bpFringeChunkPacked`. Both tables then follow from `emitTable_spec`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect SuccinctSpace

@[simp] theorem operand_val_200 : ((200 : Operand) : Nat) = 200 := rfl
@[simp] theorem operand_val_201 : ((201 : Operand) : Nat) = 201 := rfl
@[simp] theorem operand_val_202 : ((202 : Operand) : Nat) = 202 := rfl
@[simp] theorem operand_val_203 : ((203 : Operand) : Nat) = 203 := rfl
@[simp] theorem operand_val_204 : ((204 : Operand) : Nat) = 204 := rfl
@[simp] theorem operand_val_205 : ((205 : Operand) : Nat) = 205 := rfl
@[simp] theorem operand_val_206 : ((206 : Operand) : Nat) = 206 := rfl
@[simp] theorem operand_val_207 : ((207 : Operand) : Nat) = 207 := rfl
@[simp] theorem operand_val_208 : ((208 : Operand) : Nat) = 208 := rfl
@[simp] theorem operand_val_209 : ((209 : Operand) : Nat) = 209 := rfl
@[simp] theorem operand_val_210 : ((210 : Operand) : Nat) = 210 := rfl
@[simp] theorem operand_val_211 : ((211 : Operand) : Nat) = 211 := rfl
@[simp] theorem operand_val_212 : ((212 : Operand) : Nat) = 212 := rfl
@[simp] theorem operand_val_213 : ((213 : Operand) : Nat) = 213 := rfl
@[simp] theorem operand_val_214 : ((214 : Operand) : Nat) = 214 := rfl
@[simp] theorem operand_val_215 : ((215 : Operand) : Nat) = 215 := rfl
@[simp] theorem operand_val_216 : ((216 : Operand) : Nat) = 216 := rfl
@[simp] theorem operand_val_217 : ((217 : Operand) : Nat) = 217 := rfl
@[simp] theorem operand_val_218 : ((218 : Operand) : Nat) = 218 := rfl
@[simp] theorem operand_val_219 : ((219 : Operand) : Nat) = 219 := rfl

/-- `pre1_reg_simp` extended with the microtable registers 200-219. -/
syntax "pre1_micro_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_micro_simp [$hs,*]) =>
    `(tactic| pre1_reg_simp [operand_val_200, operand_val_201, operand_val_202, operand_val_203,
      operand_val_204, operand_val_205, operand_val_206, operand_val_207, operand_val_208,
      operand_val_209, operand_val_210, operand_val_211, operand_val_212, operand_val_213,
      operand_val_214, operand_val_215, operand_val_216, operand_val_217, operand_val_218,
      operand_val_219, $hs,*])

/-- Registers the microtable entry blocks may write. -/
abbrev MicroWrites (r : Nat) : Prop := 200 ≤ r ∧ r ≤ 219

theorem div_two_pow_succ (v t : Nat) : v / 2 ^ t / 2 = v / 2 ^ (t + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-! ## Select-chunk rows -/

/-- **One select step.** -/
theorem selectStep_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (c v k t : Nat) (ht : t < c) (hcW : c + 1 < 2 ^ W)
    (hvW : v < 2 ^ W) (h208 : u.regs 208 = t) (h214 : u.regs 214 = v / 2 ^ t) (h215 : u.regs 215 = k)
    (h216 : u.regs 216 = RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t)
    (h217 : u.regs 217 = if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t
      then bpChunkSelectPos c false v k else c) :
    ∃ u' j, SafeEval W selectStepBlock u u' j ∧ j ≤ 10 ∧ u'.status = .running ∧
      u'.regs 214 = v / 2 ^ (t + 1) ∧
      u'.regs 216 = RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1) ∧
      u'.regs 217 = (if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1)
        then bpChunkSelectPos c false v k else c) ∧
      (∀ r, ¬ (210 ≤ r ∧ r ≤ 214) → r ≠ 216 → r ≠ 217 → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hFle := RMQ.Succinct.rankPrefix_le_limit false (bpFringeChunkPattern c v) t
  have hsel := bpChunkSelectPos_le c false v k
  have hstep := selectPos_step (c := c) (t := t) (k := k) v ht _ rfl
  have hF := pattern_rank_false_succ (c := c) v ht
  have hxv : v / 2 ^ t ≤ v := Nat.div_le_self _ _
  rw [← div_two_pow_succ]
  generalize hFv : RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = F at *
  generalize hRv : RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1) = F' at *
  generalize hpv : (if k < F then bpChunkSelectPos c false v k else c) = pos at *
  generalize hQv : (if k < F' then bpChunkSelectPos c false v k else c) = pos' at *
  generalize hxd : v / 2 ^ t = x at *
  have hposle : pos ≤ c := by rw [← hpv]; split <;> omega
  have hQle : pos' ≤ c := by rw [← hQv]; split <;> omega
  have hb := Nat.mod_lt x (show 0 < 2 by decide)
  have hx2 : x / 2 ≤ x := Nat.div_le_self _ _
  have hA : (if F = k then 1 else 0) * (1 - x % 2) ≤ 1 := by split <;> omega
  have hB : (if F = k then 1 else 0) * (1 - x % 2) * t ≤ t :=
    Nat.le_trans (Nat.mul_le_mul_right t hA) (Nat.le_of_eq (Nat.one_mul _))
  have hC : (1 - (if F = k then 1 else 0) * (1 - x % 2)) * pos ≤ pos :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le 1 _)) (Nat.le_of_eq (Nat.one_mul _))
  obtain ⟨u', j, ev, hj, hr, hR, hm, he, hk, hkr⟩ := RegSpec.pure hW
    [.arithmetic .mod rF1 rSX rTWO, .arithmetic .div rSX rSX rTWO,
      .arithmetic .sub rF1 rONE rF1, .comparison .eq rF2 rSC rSK,
      .arithmetic .mul rF2 rF2 rF1, .arithmetic .sub rF3 rONE rF2,
      .arithmetic .mul rF4 rF2 rFT, .arithmetic .mul rF3 rF3 rSPOS,
      .arithmetic .add rSPOS rF4 rF3, .arithmetic .add rSC rSC rF1] u hrun (by
      pre1_micro_simp [h208, h214, h215, h216, h217, htwo, hone]
      repeat' apply And.intro
      all_goals first | omega | (split <;> omega))
  refine ⟨u', j, ev, by simpa using hj, hr, ?_, ?_, ?_, ?_, hm, he, hk, hkr⟩
  · rw [hR]; pre1_micro_simp [h208, h214, h215, h216, h217, htwo, hone]
  · rw [hR, hF]; pre1_micro_simp [h208, h214, h215, h216, h217, htwo, hone]
  · rw [hR, ← hstep]; pre1_micro_simp [h208, h214, h215, h216, h217, htwo, hone]
  · intro r h1 h2 h3
    have a1 : r ≠ 210 := by omega
    have a2 : r ≠ 211 := by omega
    have a3 : r ≠ 212 := by omega
    have a4 : r ≠ 213 := by omega
    have a5 : r ≠ 214 := by omega
    rw [hR]; pre1_micro_simp [a1, a2, a3, a4, a5, h2, h3]

/-- **Select-chunk row.** -/
theorem selectEntry_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (c slot : Nat) (h64 : u.regs 64 = c)
    (h14 : u.regs 14 = slot) (hslot : slot < bpChunkSelectRowCount c)
    (hcap : bpChunkSelectRowCount c + c + 1 < 2 ^ W) :
    EntryOK W selectEntryBlock MicroWrites u
      (bpChunkSelectPos c false (slot / (c + 1)) (slot % (c + 1))) (14 * c + 9) := by
  have hcW : c + 1 < 2 ^ W := by omega
  have hvle : slot / (c + 1) ≤ slot := Nat.div_le_self _ _
  have hkle : slot % (c + 1) < c + 1 := Nat.mod_lt _ (by omega)
  obtain ⟨u1, j1, e1, hj1, hr1, hR1, hm1, he1, hk1, hkr1⟩ := RegSpec.pure hW
    [.arithmetic .add rCP1 rCB rONE, .arithmetic .div rSX rSLOT rCP1,
      .arithmetic .mod rSK rSLOT rCP1, .constant rSC 0, .move rSPOS rCB] u hrun (by
      pre1_micro_simp [h64, h14, hone]
      repeat' apply And.intro
      all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
        (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega))
  have u1_214 : u1.regs 214 = slot / (c + 1) := by rw [hR1]; pre1_micro_simp [h64, h14, hone]
  have u1_215 : u1.regs 215 = slot % (c + 1) := by rw [hR1]; pre1_micro_simp [h64, h14, hone]
  have u1_216 : u1.regs 216 = 0 := by rw [hR1]; pre1_micro_simp [h64, h14, hone]
  have u1_217 : u1.regs 217 = c := by rw [hR1]; pre1_micro_simp [h64, h14, hone]
  have u1get : ∀ r, r ≠ 200 → ¬ (214 ≤ r ∧ r ≤ 217) → u1.regs r = u.regs r := fun r a b => by
    have b1 : r ≠ 214 := by omega
    have b2 : r ≠ 215 := by omega
    have b3 : r ≠ 216 := by omega
    have b4 : r ≠ 217 := by omega
    rw [hR1]; pre1_micro_simp [a, b1, b2, b3, b4]
  generalize hv : slot / (c + 1) = v at *
  generalize hk : slot % (c + 1) = k at *
  let Inv : Nat → State → Prop := fun t w =>
    w.regs 214 = v / 2 ^ t ∧
      w.regs 216 = RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t ∧
      w.regs 217 = (if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t
        then bpChunkSelectPos c false v k else c) ∧
      w.regs 215 = k ∧
      (∀ r, ¬ MicroWrites r → w.regs r = u.regs r) ∧
      w.memory = u.memory ∧ w.extent = u.extent ∧ w.keys = u.keys ∧ w.keyRegs = u.keyRegs
  obtain ⟨s1, j2, e2, hj2, hr2, ⟨I1, I2, I3, I4, I5, I6, I7, I8, I9⟩, _, _⟩ :=
    forSlots_spec hW rFT rFTGO rCB selectStepBlock 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv u1 hr1
      (by rw [u1get 2 (by decide) (by decide), hone])
      (by show u1.regs 64 < 2 ^ W; rw [u1get 64 (by decide) (by decide), h64]; omega)
      (by
        intro w _ hwr hwm hwe hwk hwkr
        have wget : ∀ r, r ≠ 208 → r ≠ 209 → w.regs r = u1.regs r := hwr
        refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hwm, hm1], by rw [hwe, he1], by rw [hwk, hk1],
          by rw [hwkr, hkr1]⟩
        · rw [wget 214 (by decide) (by decide), u1_214, Nat.pow_zero, Nat.div_one]
        · rw [wget 216 (by decide) (by decide), u1_216, RMQ.Succinct.rankPrefix_zero]
        · rw [wget 217 (by decide) (by decide), u1_217, RMQ.Succinct.rankPrefix_zero]
          simp
        · rw [wget 215 (by decide) (by decide), u1_215]
        · intro r hr
          rw [wget r (by omega) (by omega), u1get r (by omega) (by omega)])
      (by
        intro t w ht ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9⟩ hwr hwi hwcnt hwone
        have ht' : t < c := by
          have : t < u1.regs 64 := ht
          rwa [u1get 64 (by decide) (by decide), h64] at this
        obtain ⟨w', j, ev, hj, hr', R214, R216, R217, F, M, E, K, KR⟩ :=
          selectStep_spec hW w hwr hwone (by rw [W5 9 (by decide)]; exact htwo) c v k t ht' hcW
            (by omega) hwi W1 W4 W2 W3
        refine ⟨w', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show w'.regs 208 = t
          rw [F 208 (by decide) (by decide) (by decide)]; exact hwi
        · show w'.regs 64 = u1.regs 64
          rw [F 64 (by decide) (by decide) (by decide)]; exact hwcnt
        · rw [F 2 (by decide) (by decide) (by decide), hwone]
        · intro x _ hxr hxm hxe hxk hxkr
          have xget : ∀ r, r ≠ 208 → r ≠ 209 → x.regs r = w'.regs r := hxr
          refine ⟨?_, ?_, ?_, ?_, ?_, by rw [hxm, M, W6], by rw [hxe, E, W7], by rw [hxk, K, W8],
            by rw [hxkr, KR, W9]⟩
          · rw [xget 214 (by decide) (by decide), R214]
          · rw [xget 216 (by decide) (by decide), R216]
          · rw [xget 217 (by decide) (by decide), R217]
          · rw [xget 215 (by decide) (by decide), F 215 (by decide) (by decide) (by decide), W4]
          · intro r hr
            rw [xget r (by omega) (by omega), F r (by omega) (by omega) (by omega), W5 r hr])
  have hcnt : u1.regs rCB = c := by
    show u1.regs 64 = c; rw [u1get 64 (by decide) (by decide), h64]
  simp only [hcnt] at I1 I2 I3 hj2
  have hfin := selectPos_final c v k
  rw [hfin] at I3
  have hselle := bpChunkSelectPos_le c false v k
  obtain ⟨s2, j3, e3, hj3, hr3, hR3, hm3, he3, hk3, hkr3⟩ := RegSpec.pure hW [.move rENT rSPOS] s1 hr2
    (by pre1_micro_simp [])
  refine ⟨s2, j1 + (j2 + j3), EvalG.seq e1 (EvalG.seq e2 e3), ?_, hr3, ?_, ?_,
    by rw [hm3, I6], by rw [he3, I7], ?_, by rw [hkr3, I9], by rw [hk3, I8]⟩
  · simp at hj1 hj3
    omega
  · rw [hR3]; pre1_micro_simp [I3]
  · rw [hR3]; pre1_micro_simp [I3]; omega
  · intro r hr h16
    rw [hR3]; pre1_micro_simp [h16]
    exact I5 r hr

/-- **Select-chunk table.** -/
theorem selectTable_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (c : Nat) (h64 : s.regs 64 = c)
    (h67 : s.regs 67 = bpChunkSelectRowCount c) (h68 : s.regs 68 = bpChunkSelectEntryWidth c)
    (hcap : bpChunkSelectRowCount c + c + 1 < 2 ^ W)
    (hext : s.extent + bpChunkSelectRowCount c * bpChunkSelectEntryWidth c < 2 ^ W) :
    ∃ s' k, SafeEval W (emitTable rSROWS rSWID selectEntryBlock) s s' k ∧
      k ≤ bpChunkSelectRowCount c * (14 * c + 9 + 7 * bpChunkSelectEntryWidth c + 7) + 3 ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hwle : bpChunkSelectEntryWidth c ≤ c + 2 := by
    show Nat.log2 (c + 1) + 1 ≤ c + 2
    have := Nat.log2_le_self (c + 1)
    omega
  have hrows : 1 ≤ bpChunkSelectRowCount c := Nat.mul_pos (Nat.two_pow_pos c) (Nat.succ_pos c)
  obtain ⟨s', k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    emitTable_spec hW rSROWS rSWID selectEntryBlock
      (fun slot => bpChunkSelectPos c false (slot / (c + 1)) (slot % (c + 1))) (14 * c + 9) MicroWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo
      (by show s.regs 67 + 1 < 2 ^ W; rw [h67]; omega)
      (by show s.regs 68 < 2 ^ W; rw [h68]; omega)
      (by show s.extent + s.regs 67 * s.regs 68 < 2 ^ W; rw [h67, h68]; exact hext)
      (by
        intro x hxr hxfr _ _ _ _ hslot
        have xget : ∀ r, ¬ MicroWrites r → ¬ TableScratch r → x.regs r = s.regs r := hxfr
        exact selectEntry_spec hW x hxr
          (by rw [xget 2 (by decide) (by decide), hone]) (by rw [xget 9 (by decide) (by decide), htwo]) c
          (x.regs 14) (by rw [xget 64 (by decide) (by decide), h64]) rfl
          (by have : x.regs 14 < s.regs 67 := hslot; rwa [h67] at this) hcap)
  simp only [operand_val_67, operand_val_68, h67, h68] at hk hE
  exact ⟨s', k, ev, hk, hr, hE, hfr, hkr, hks⟩

/-! ## Fringe rows -/

theorem take_le_one (t a b E bv : Nat) :
    (if t = a then 1 else 0) + (if a < t then 1 else 0) * (if t < b then 1 else 0) *
      (if E < bv then 1 else 0) ≤ 1 := by
  by_cases h : t = a
  · subst h; simp
  · simp only [h, if_false, Nat.zero_add]
    split <;> split <;> split <;> simp

theorem mul_le_of_le_one {x y : Nat} (hx : x ≤ 1) : x * y ≤ y :=
  Nat.le_trans (Nat.mul_le_mul_right y hx) (Nat.le_of_eq (Nat.one_mul y))

/-- **One fringe scan offset.** -/
theorem fringeStep_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (c v a b t bp bv : Nat) (htc : t ≤ c)
    (hac : a ≤ c) (hbc : b ≤ c) (hcW : 4 * c + 4 < 2 ^ W) (hvW : v < 2 ^ W)
    (h64 : u.regs 64 = c) (h202 : u.regs 202 = v / 2 ^ t) (h203 : u.regs 203 = a)
    (h204 : u.regs 204 = b) (h205 : u.regs 205 = bpFringeChunkExcessOffsetAt c v t)
    (h206 : u.regs 206 = bp) (h207 : u.regs 207 = bv) (h208 : u.regs 208 = t)
    (hbp : bp ≤ c) (hbv : bv ≤ 2 * c)
    (hinv : a < t → bp = bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a (min t b - a) ∧
      bv = bpFringeChunkExcessOffsetAt c v bp) :
    ∃ u' j, SafeEval W fringeStepBlock u u' j ∧ j ≤ 21 ∧ u'.status = .running ∧
      u'.regs 202 = v / 2 ^ (t + 1) ∧
      u'.regs 205 = bpFringeChunkExcessOffsetAt c v (min (t + 1) c) ∧
      u'.regs 206 ≤ c ∧ u'.regs 207 ≤ 2 * c ∧
      (a < t + 1 → u'.regs 206 =
          bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a (min (t + 1) b - a) ∧
        u'.regs 207 = bpFringeChunkExcessOffsetAt c v (u'.regs 206)) ∧
      (∀ r, r ≠ 202 → ¬ (205 ≤ r ∧ r ≤ 207) → ¬ (210 ≤ r ∧ r ≤ 213) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hEle := bpFringeChunkExcessOffsetAt_le c v t
  have hstepE : t < c → bpFringeChunkExcessOffsetAt c v (t + 1) + 1 =
      bpFringeChunkExcessOffsetAt c v t + 2 * (v / 2 ^ t % 2) ∧ 1 ≤ bpFringeChunkExcessOffsetAt c v t :=
    fun h => excessOffset_succ (c := c) (t := t) v h
  have hbest := fringeBest_step (bpFringeChunkExcessOffsetAt c v) a b t bp bv hinv
  have hxv : v / 2 ^ t ≤ v := Nat.div_le_self _ _
  have hEnext : bpFringeChunkExcessOffsetAt c v (min (t + 1) c) =
      if t < c then bpFringeChunkExcessOffsetAt c v (t + 1) else bpFringeChunkExcessOffsetAt c v t := by
    split
    · rw [Nat.min_eq_left (by omega)]
    · rw [Nat.min_eq_right (by omega), show t = c by omega]
  have hscanle : ∀ m, a + m ≤ c + 1 → bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a m ≤ c :=
    fun m hm => bpFringeScanArgMin_le hac hm
  rw [← div_two_pow_succ, hEnext]
  generalize hEd : bpFringeChunkExcessOffsetAt c v t = E at *
  generalize hxd : v / 2 ^ t = x at *
  have hb2 := Nat.mod_lt x (show 0 < 2 by decide)
  have htake := take_le_one t a b E bv
  have hT1 := mul_le_of_le_one (y := E) htake
  have hT2 := mul_le_of_le_one (y := bv) (Nat.sub_le 1 ((if t = a then 1 else 0) +
    (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0)))
  have hT3 := mul_le_of_le_one (y := t) htake
  have hT4 := mul_le_of_le_one (y := bp) (Nat.sub_le 1 ((if t = a then 1 else 0) +
    (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0)))
  have hI1 : (if t = a then 1 else 0) ≤ 1 := by split <;> omega
  have hI2 : (if a < t then 1 else 0) * (if t < b then 1 else 0) ≤ 1 := by split <;> split <;> omega
  have hI3 : (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0) ≤ 1 :=
    Nat.le_trans (mul_le_of_le_one (y := if E < bv then 1 else 0) hI2) (by split <;> omega)
  have hnl : (if t < c then 1 else 0) ≤ 1 := by split <;> omega
  have hbit2 : x % 2 * 2 * (if t < c then 1 else 0) ≤ 2 :=
    Nat.le_trans (Nat.mul_le_mul_left _ hnl) (by omega)
  have hsub : (if t < c then 1 else 0) ≤ E + x % 2 * 2 * (if t < c then 1 else 0) := by
    split
    · have := (hstepE (by omega)).2; omega
    · omega
  obtain ⟨u', j, ev, hj, hr, hR, hm, he, hk, hkr⟩ := RegSpec.pure hW
    [.comparison .eq rF1 rFT rFA, .comparison .lt rF2 rFA rFT,
      .comparison .lt rF3 rFT rFB, .arithmetic .mul rF2 rF2 rF3,
      .comparison .lt rF3 rFE rFBV, .arithmetic .mul rF2 rF2 rF3,
      .arithmetic .add rF1 rF1 rF2, .arithmetic .sub rF2 rONE rF1,
      .arithmetic .mul rF3 rF1 rFE, .arithmetic .mul rF4 rF2 rFBV, .arithmetic .add rFBV rF3 rF4,
      .arithmetic .mul rF3 rF1 rFT, .arithmetic .mul rF4 rF2 rFBP, .arithmetic .add rFBP rF3 rF4,
      .comparison .lt rF1 rFT rCB, .arithmetic .mod rF2 rFV rTWO,
      .arithmetic .div rFV rFV rTWO, .arithmetic .mul rF2 rF2 rTWO,
      .arithmetic .mul rF2 rF2 rF1, .arithmetic .add rFE rFE rF2,
      .arithmetic .sub rFE rFE rF1] u hrun (by
      pre1_micro_simp [h64, h202, h203, h204, h205, h206, h207, h208, htwo, hone]
      repeat' apply And.intro
      all_goals first | omega | (split <;> omega) | (split <;> split <;> omega))
  have hR206 : u'.regs 206 = ((if t = a then 1 else 0) +
      (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0)) * t +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0))) * bp := by
    rw [hR]; pre1_micro_simp [h64, h202, h203, h204, h205, h206, h207, h208, htwo, hone]
  have hR207 : u'.regs 207 = ((if t = a then 1 else 0) +
      (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0)) * E +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if E < bv then 1 else 0))) * bv := by
    rw [hR]; pre1_micro_simp [h64, h202, h203, h204, h205, h206, h207, h208, htwo, hone]
  refine ⟨u', j, ev, by simpa using hj, hr, ?_, ?_, ?_, ?_, ?_, ?_, hm, he, hk, hkr⟩
  · rw [hR]; pre1_micro_simp [h64, h202, h203, h204, h205, h206, h207, h208, htwo, hone]
  · rw [hR]; pre1_micro_simp [h64, h202, h203, h204, h205, h206, h207, h208, htwo, hone]
    split
    · have := (hstepE (by omega)).1; omega
    · simp
  · rw [hR206]
    by_cases hta : a ≤ t
    · rw [(hbest hta).1]; exact hscanle _ (by omega)
    · rw [if_neg (by omega), if_neg (by omega)]; simp; exact hbp
  · rw [hR207]
    by_cases hta : a ≤ t
    · rw [(hbest hta).2]; exact bpFringeChunkExcessOffsetAt_le c v _
    · rw [if_neg (by omega), if_neg (by omega)]; simp; exact hbv
  · intro hat
    rw [hR206, hR207]
    exact ⟨(hbest (by omega)).1, by rw [(hbest (by omega)).2, (hbest (by omega)).1]⟩
  · intro r h1 h2 h3
    have a1 : r ≠ 205 := by omega
    have a2 : r ≠ 206 := by omega
    have a3 : r ≠ 207 := by omega
    have a4 : r ≠ 210 := by omega
    have a5 : r ≠ 211 := by omega
    have a6 : r ≠ 212 := by omega
    have a7 : r ≠ 213 := by omega
    rw [hR]; pre1_micro_simp [h1, a1, a2, a3, a4, a5, a6, a7]

/-- **Fringe row.** -/
theorem fringeEntry_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (c slot : Nat) (h64 : u.regs 64 = c)
    (h14 : u.regs 14 = slot) (hslot : slot < bpFringeChunkRowCount c)
    (hcap : bpFringeChunkRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) < 2 ^ W) :
    EntryOK W fringeEntryBlock MicroWrites u
      (bpFringeChunkPacked c (slot / ((c + 1) * (c + 1))) (slot / (c + 1) % (c + 1)) (slot % (c + 1)))
      (25 * c + 42) := by
  have hc1 : c + 1 ≤ (c + 1) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hc2 : (c + 1) * (c + 1) ≤ (c + 1) * (c + 1) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hcW : 4 * c + 4 < 2 ^ W := by omega
  have hvle : slot / ((c + 1) * (c + 1)) ≤ slot := Nat.div_le_self _ _
  have hqle : slot / (c + 1) ≤ slot := Nat.div_le_self _ _
  have hale : slot / (c + 1) % (c + 1) < c + 1 := Nat.mod_lt _ (by omega)
  have hble : slot % (c + 1) < c + 1 := Nat.mod_lt _ (by omega)
  obtain ⟨u1, j1, e1, hj1, hr1, hR1, hm1, he1, hk1, hkr1⟩ := RegSpec.pure hW fringeDecodeActs u hrun (by
      simp only [fringeDecodeActs]
      pre1_micro_simp [h64, h14, hone]
      repeat' apply And.intro
      all_goals first | omega | (apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega) |
        (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); omega) |
        (apply Nat.lt_of_le_of_lt (Nat.mod_le _ _); apply Nat.lt_of_le_of_lt (Nat.div_le_self _ _); omega))
  have u1v : ∀ r, u1.regs r = pureRegs fringeDecodeActs u.regs r := fun r => by rw [hR1]
  have u1_200 : u1.regs 200 = c + 1 := by rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_202 : u1.regs 202 = slot / ((c + 1) * (c + 1)) := by
    rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_203 : u1.regs 203 = slot / (c + 1) % (c + 1) := by
    rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_204 : u1.regs 204 = slot % (c + 1) := by
    rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_205 : u1.regs 205 = c := by rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_206 : u1.regs 206 = 0 := by rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1_207 : u1.regs 207 = 0 := by rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [h64, h14, hone]
  have u1get : ∀ r, ¬ (200 ≤ r ∧ r ≤ 207) → u1.regs r = u.regs r := fun r h => by
    have b0 : r ≠ 200 := by omega
    have b1 : r ≠ 201 := by omega
    have b2 : r ≠ 202 := by omega
    have b3 : r ≠ 203 := by omega
    have b4 : r ≠ 204 := by omega
    have b5 : r ≠ 205 := by omega
    have b6 : r ≠ 206 := by omega
    have b7 : r ≠ 207 := by omega
    rw [u1v]; simp only [fringeDecodeActs]; pre1_micro_simp [b0, b1, b2, b3, b4, b5, b6, b7]
  generalize hv : slot / ((c + 1) * (c + 1)) = v at *
  generalize ha : slot / (c + 1) % (c + 1) = a at *
  generalize hb : slot % (c + 1) = b at *
  let f := bpFringeChunkExcessOffsetAt c v
  let Inv : Nat → State → Prop := fun t w =>
    w.regs 202 = v / 2 ^ t ∧ w.regs 205 = f (min t c) ∧ w.regs 206 ≤ c ∧ w.regs 207 ≤ 2 * c ∧
      (a < t → w.regs 206 = bpFringeScanArgMin f a (min t b - a) ∧ w.regs 207 = f (w.regs 206)) ∧
      w.regs 200 = c + 1 ∧ w.regs 203 = a ∧ w.regs 204 = b ∧
      (∀ r, ¬ MicroWrites r → w.regs r = u.regs r) ∧
      w.memory = u.memory ∧ w.extent = u.extent ∧ w.keys = u.keys ∧ w.keyRegs = u.keyRegs
  obtain ⟨s1, j2, e2, hj2, hr2, ⟨I1, I2, I3, I4, I5, I6, I7, I8, I9, I10, I11, I12, I13⟩, _, _⟩ :=
    forSlots_spec hW rFT rFTGO rCP1 fringeStepBlock 21 (by decide) (by decide) (by decide) (by decide)
      (by decide) Inv u1 hr1
      (by rw [u1get 2 (by decide), hone])
      (by show u1.regs 200 < 2 ^ W; rw [u1_200]; omega)
      (by
        intro w _ hwr hwm hwe hwk hwkr
        have wget : ∀ r, r ≠ 208 → r ≠ 209 → w.regs r = u1.regs r := hwr
        refine ⟨?_, ?_, ?_, ?_, fun h => absurd h (Nat.not_lt_zero _), ?_, ?_, ?_, ?_,
          by rw [hwm, hm1], by rw [hwe, he1], by rw [hwk, hk1], by rw [hwkr, hkr1]⟩
        · rw [wget 202 (by decide) (by decide), u1_202, Nat.pow_zero, Nat.div_one]
        · rw [wget 205 (by decide) (by decide), u1_205, Nat.zero_min]
          exact (bpFringeChunkExcessOffsetAt_zero c v).symm
        · rw [wget 206 (by decide) (by decide), u1_206]; omega
        · rw [wget 207 (by decide) (by decide), u1_207]; omega
        · rw [wget 200 (by decide) (by decide), u1_200]
        · rw [wget 203 (by decide) (by decide), u1_203]
        · rw [wget 204 (by decide) (by decide), u1_204]
        · intro r hr
          rw [wget r (by omega) (by omega), u1get r (by omega)])
      (by
        intro t w ht ⟨W1, W2, W3, W4, W5, W6, W7, W8, W9, W10, W11, W12, W13⟩ hwr hwi hwcnt hwone
        have ht' : t ≤ c := by
          have : t < u1.regs 200 := ht
          rw [u1_200] at this; omega
        rw [Nat.min_eq_left ht'] at W2
        obtain ⟨w', j, ev, hj, hr', R202, R205, R206le, R207le, RI, F, M, E, K, KR⟩ :=
          fringeStep_spec hW w hwr hwone (by rw [W9 9 (by decide)]; exact htwo) c v a b t
            (w.regs 206) (w.regs 207) ht' (by omega) (by omega) hcW (by omega)
            (by rw [W9 64 (by decide)]; exact h64) W1 W7 W8 W2 rfl rfl hwi W3 W4 W5
        refine ⟨w', j, ev, hj, hr', ?_, ?_, ?_, ?_⟩
        · show w'.regs 208 = t
          rw [F 208 (by decide) (by decide) (by decide)]; exact hwi
        · show w'.regs 200 = u1.regs 200
          rw [F 200 (by decide) (by decide) (by decide)]; exact hwcnt
        · rw [F 2 (by decide) (by decide) (by decide), hwone]
        · intro x _ hxr hxm hxe hxk hxkr
          have xget : ∀ r, r ≠ 208 → r ≠ 209 → x.regs r = w'.regs r := hxr
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hxm, M, W10], by rw [hxe, E, W11],
            by rw [hxk, K, W12], by rw [hxkr, KR, W13]⟩
          · rw [xget 202 (by decide) (by decide), R202]
          · rw [xget 205 (by decide) (by decide), R205]
          · rw [xget 206 (by decide) (by decide)]; exact R206le
          · rw [xget 207 (by decide) (by decide)]; exact R207le
          · intro hat
            rw [xget 206 (by decide) (by decide), xget 207 (by decide) (by decide)]
            exact RI hat
          · rw [xget 200 (by decide) (by decide), F 200 (by decide) (by decide) (by decide), W6]
          · rw [xget 203 (by decide) (by decide), F 203 (by decide) (by decide) (by decide), W7]
          · rw [xget 204 (by decide) (by decide), F 204 (by decide) (by decide) (by decide), W8]
          · intro r hr
            rw [xget r (by omega) (by omega), F r (by omega) (by omega) (by omega), W9 r hr])
  have hcnt : u1.regs rCP1 = c + 1 := u1_200
  simp only [hcnt] at I1 I2 I3 I4 I5 hj2
  rw [Nat.min_eq_right (by omega)] at I2
  obtain ⟨I5a, I5b⟩ := I5 (by omega)
  rw [Nat.min_eq_right (show b ≤ c + 1 by omega)] at I5a
  have hdelta : f c = bpFringeChunkDeltaOffset c v := rfl
  have harg : bpFringeScanArgMin f a (b - a) = bpFringeChunkArgMin c v a b := rfl
  have hmin : f (bpFringeChunkArgMin c v a b) = bpFringeChunkMinOffset c v a b := rfl
  rw [harg] at I5a
  rw [I5a, hmin] at I5b
  rw [hdelta] at I2
  have hDle := bpFringeChunkDeltaOffset_le c v
  have hMle := bpFringeChunkMinOffset_le c v a b
  have hAle := bpFringeChunkArgMin_le c v (a := a) (b := b) (by omega) (by omega)
  have hpk := bpFringeChunkPacked_lt_entryBound c v (a := a) (b := b) (by omega) (by omega)
  have hbound : bpFringeChunkEntryBound c ≤ 16 * ((c + 1) * (c + 1) * (c + 1)) := by
    unfold bpFringeChunkEntryBound
    rw [← Nat.mul_assoc]
    have h1 : (2 * c + 1) * (2 * c + 2) ≤ 4 * ((c + 1) * (c + 1)) := by
      have := Nat.mul_le_mul (show 2 * c + 1 ≤ 2 * (c + 1) by omega) (show 2 * c + 2 ≤ 2 * (c + 1) by omega)
      rw [show 2 * (c + 1) * (2 * (c + 1)) = 4 * ((c + 1) * (c + 1)) by
        rw [Nat.mul_mul_mul_comm]] at this
      exact this
    have h2 := Nat.mul_le_mul_right (c + 1) h1
    rw [Nat.mul_assoc 4] at h2
    omega
  obtain ⟨s2, j3, e3, hj3, hr3, hR3, hm3, he3, hk3, hkr3⟩ := RegSpec.pure hW
    [.arithmetic .add rF1 rCP1 rCP1, .arithmetic .mul rF1 rFE rF1,
      .arithmetic .add rF1 rF1 rFBV, .arithmetic .mul rF1 rF1 rCP1,
      .arithmetic .add rENT rF1 rFBP] s1 hr2 (by
      pre1_micro_simp [I2, I5a, I5b, I6]
      have hpk' : (bpFringeChunkDeltaOffset c v * (c + 1 + (c + 1)) + bpFringeChunkMinOffset c v a b) *
          (c + 1) + bpFringeChunkArgMin c v a b < 2 ^ W := by
        rw [show c + 1 + (c + 1) = 2 * c + 2 by omega]
        unfold bpFringeChunkPacked at hpk
        omega
      have hm1 : bpFringeChunkDeltaOffset c v * (c + 1 + (c + 1)) ≤
          (bpFringeChunkDeltaOffset c v * (c + 1 + (c + 1)) + bpFringeChunkMinOffset c v a b) * (c + 1) :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (by omega))
      have hm2 : bpFringeChunkDeltaOffset c v * (c + 1 + (c + 1)) + bpFringeChunkMinOffset c v a b ≤
          (bpFringeChunkDeltaOffset c v * (c + 1 + (c + 1)) + bpFringeChunkMinOffset c v a b) * (c + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      repeat' apply And.intro
      all_goals omega)
  refine ⟨s2, j1 + (j2 + j3), EvalG.seq e1 (EvalG.seq e2 e3), ?_, hr3, ?_, ?_,
    by rw [hm3, I10], by rw [he3, I11], ?_, by rw [hkr3, I13], by rw [hk3, I12]⟩
  · simp [fringeDecodeActs] at hj1 hj3
    omega
  · rw [hR3]; pre1_micro_simp [I2, I5a, I5b, I6]
    unfold bpFringeChunkPacked
    rw [show c + 1 + (c + 1) = 2 * c + 2 by omega]
  · rw [hR3]; pre1_micro_simp [I2, I5a, I5b, I6]
    rw [show c + 1 + (c + 1) = 2 * c + 2 by omega]
    unfold bpFringeChunkPacked at hpk
    omega
  · intro r hr h16
    rw [hR3]; pre1_micro_simp [h16]
    have b1 : r ≠ 210 := by omega
    simp only [b1, if_false]
    exact I9 r hr

/-- **Fringe table.** -/
theorem fringeTable_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (c : Nat) (h64 : s.regs 64 = c)
    (h65 : s.regs 65 = bpFringeChunkRowCount c) (h66 : s.regs 66 = bpFringeChunkEntryWidth c)
    (hcap : bpFringeChunkRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) < 2 ^ W)
    (hext : s.extent + bpFringeChunkRowCount c * bpFringeChunkEntryWidth c < 2 ^ W) :
    ∃ s' k, SafeEval W (emitTable rFROWS rFWID fringeEntryBlock) s s' k ∧
      k ≤ bpFringeChunkRowCount c * (25 * c + 42 + 7 * bpFringeChunkEntryWidth c + 7) + 3 ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hrows : 1 ≤ bpFringeChunkRowCount c :=
    Nat.mul_pos (Nat.two_pow_pos c) (Nat.mul_pos (Nat.succ_pos c) (Nat.succ_pos c))
  have hg : 1 ≤ (c + 1) * (c + 1) * (c + 1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hwW : bpFringeChunkEntryWidth c < 2 ^ W := by
    have := Nat.le_mul_of_pos_left (bpFringeChunkEntryWidth c) hrows
    omega
  obtain ⟨s', k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    emitTable_spec hW rFROWS rFWID fringeEntryBlock
      (fun slot => bpFringeChunkPacked c (slot / ((c + 1) * (c + 1))) (slot / (c + 1) % (c + 1))
        (slot % (c + 1))) (25 * c + 42) MicroWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      s hrun hone htwo
      (by show s.regs 65 + 1 < 2 ^ W; rw [h65]; omega)
      (by show s.regs 66 < 2 ^ W; rw [h66]; exact hwW)
      (by show s.extent + s.regs 65 * s.regs 66 < 2 ^ W; rw [h65, h66]; exact hext)
      (by
        intro x hxr hxfr _ _ _ _ hslot
        have xget : ∀ r, ¬ MicroWrites r → ¬ TableScratch r → x.regs r = s.regs r := hxfr
        exact fringeEntry_spec hW x hxr
          (by rw [xget 2 (by decide) (by decide), hone]) (by rw [xget 9 (by decide) (by decide), htwo]) c
          (x.regs 14) (by rw [xget 64 (by decide) (by decide), h64]) rfl
          (by have : x.regs 14 < s.regs 65 := hslot; rwa [h65] at this) hcap)
  simp only [operand_val_65, operand_val_66, h65, h66] at hk hE
  exact ⟨s', k, ev, hk, hr, hE, hfr, hkr, hks⟩

/-! ## Both microtables -/

/-- **Microtables.** The fringe table then the select-chunk table, at chunk
width `c`. -/
theorem microtables_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (c : Nat) (h64 : s.regs 64 = c)
    (h65 : s.regs 65 = bpFringeChunkRowCount c) (h66 : s.regs 66 = bpFringeChunkEntryWidth c)
    (h67 : s.regs 67 = bpChunkSelectRowCount c) (h68 : s.regs 68 = bpChunkSelectEntryWidth c)
    (hcap : bpFringeChunkRowCount c + bpChunkSelectRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) <
      2 ^ W)
    (hext : s.extent + (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length +
      (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length < 2 ^ W) :
    ∃ s' k, SafeEval W microtablesBlock s s' k ∧
      k ≤ bpFringeChunkRowCount c * (25 * c + 42 + 7 * bpFringeChunkEntryWidth c + 7) + 3 +
        (bpChunkSelectRowCount c * (14 * c + 9 + 7 * bpChunkSelectEntryWidth c + 7) + 3) ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
        tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hc1 : c + 1 ≤ (c + 1) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hc2 : (c + 1) * (c + 1) ≤ (c + 1) * (c + 1) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [tableBits_length, tableBits_length, bpFringeChunkEntries_length, bpChunkSelectEntries_length] at hext
  obtain ⟨s1, k1, e1, hk1, hr1, E1, fr1, kr1, ks1⟩ :=
    fringeTable_spec hW s hrun hone htwo c h64 h65 h66 (by omega) (by omega)
  have x1 := E1.1
  rw [List.length_map, tableBits_length, bpFringeChunkEntries_length] at x1
  have g : ∀ r, ¬ MicroWrites r → ¬ TableScratch r → s1.regs r = s.regs r := fr1
  obtain ⟨s2, k2, e2, hk2, hr2, E2, fr2, kr2, ks2⟩ :=
    selectTable_spec hW s1 hr1 (by rw [g 2 (by decide) (by decide), hone])
      (by rw [g 9 (by decide) (by decide), htwo]) c (by rw [g 64 (by decide) (by decide), h64])
      (by rw [g 67 (by decide) (by decide), h67]) (by rw [g 68 (by decide) (by decide), h68])
      (by omega) (by rw [x1]; omega)
  refine ⟨s2, k1 + k2, EvalG.seq e1 e2, by omega, hr2, ?_, ?_, by rw [kr2, kr1], by rw [ks2, ks1]⟩
  · rw [List.map_append]; exact E1.trans E2
  · intro r h1 h2; rw [fr2 r h1 h2, fr1 r h1 h2]

end RMQ.SuccinctFinal.PackedConstruction.Proof

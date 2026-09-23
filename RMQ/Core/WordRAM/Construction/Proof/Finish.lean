import RMQ.Core.WordRAM.Construction.Proof.Micro
import RMQ.Core.WordRAM.Construction.Builder.Finish

/-! # PRE-1 builder proofs: header cells, header patch and paddings (stage S6)

Outside the builder firewall. `headerReserve_spec` appends the `oldW` header
cells and sets the BP base right after them; `headerPatch_spec` stores the
`oldW` little-endian bits of the long count into those cells; `pad_spec`
measures the serialized length `L` with one zero probe cell and appends zeros
up to the dense bit count `D` computed from `L` exactly as the reference does
(one probe cell remains when `L = D`).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect SuccinctSpace

@[simp] theorem operand_val_220 : ((220 : Operand) : Nat) = 220 := rfl
@[simp] theorem operand_val_221 : ((221 : Operand) : Nat) = 221 := rfl
@[simp] theorem operand_val_222 : ((222 : Operand) : Nat) = 222 := rfl
@[simp] theorem operand_val_223 : ((223 : Operand) : Nat) = 223 := rfl
@[simp] theorem operand_val_224 : ((224 : Operand) : Nat) = 224 := rfl
@[simp] theorem operand_val_225 : ((225 : Operand) : Nat) = 225 := rfl
@[simp] theorem operand_val_226 : ((226 : Operand) : Nat) = 226 := rfl
@[simp] theorem operand_val_227 : ((227 : Operand) : Nat) = 227 := rfl
@[simp] theorem operand_val_228 : ((228 : Operand) : Nat) = 228 := rfl

/-- `pre1_reg_simp` extended with the finish registers 220-228. -/
syntax "pre1_finish_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_finish_simp [$hs,*]) =>
    `(tactic| pre1_reg_simp [operand_val_220, operand_val_221, operand_val_222, operand_val_223,
      operand_val_224, operand_val_225, operand_val_226, operand_val_227, operand_val_228, $hs,*])

/-! ## Zero cells -/

/-- **Zero loop.** With `N` in register 12 the loop appends `N` zero cells. -/
theorem zeroLoop_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1) (N : Nat) (hN : s.regs 12 = N)
    (hext : s.extent + N + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W (.loop rECNT (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))))
        s s' k ∧ k ≤ 5 * N + 1 ∧ s'.status = .running ∧ Emits s s' (List.replicate N 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have hW2 : 2 < 2 ^ W := two_le_two_pow hW
  let Q : Nat → State → Prop := fun m u =>
    m ≤ N ∧ u.status = .running ∧ u.regs 12 = m ∧
      Emits s u (List.replicate (N - m) 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ : Q N s := by
    refine ⟨Nat.le_refl _, hrun, hN, ?_, fun r _ _ => rfl, rfl, rfl⟩
    rw [Nat.sub_self]
    exact Emits.refl s
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rECNT
    (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))) 3
    (fun m u hu => hu.2.1)
    (fun m u hu => by simp only [operand_val_12]; rw [hu.2.2.1]; omega)
    (fun u hu => by simp only [operand_val_12]; exact hu.2.2.1)
    (by
      intro m u hu
      obtain ⟨hm, hurun, hucnt, huemit, hufr, hukr, huk⟩ := hu
      have hu0 : u.regs 0 = 0 := by rw [hufr 0 (by decide) (by decide), hzero]
      have hu2 : u.regs 2 = 1 := by rw [hufr 2 (by decide) (by decide), hone]
      have huext : u.extent = s.extent + (N - (m + 1)) := by
        rw [huemit.1]; simp only [List.length_replicate]
      obtain ⟨u1, e1, hu1run, hu1emit, hu1fr, hu1kr, hu1k⟩ :=
        emitBit_spec hW rZERO (by decide) u hurun (by simp only [operand_val_0]; rw [hu0]; omega)
          (by rw [huext]; omega)
      have hu1cnt : u1.regs 12 = m + 1 := by rw [hu1fr 12 (by decide), hucnt]
      have hu1one : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide), hu2]
      let u2 := execPrim (Prim.arithmetic .sub rECNT rECNT rONE) u1
      have g2 := exec_arithmetic u1 .sub rECNT rECNT rONE
      have u2r : u2.regs = put u1.regs 12 m := by
        simp [u2, g2, Arithmetic.eval, hu1cnt, hu1one]
      have u2s : u2.status = .running := by simp [u2, g2, hu1run]
      have hsafe : Action.Safe W u1 (.arithmetic .sub rECNT rECNT rONE) :=
        safe_sub hW u1 _ _ _ (by simp only [operand_val_12, operand_val_2]; rw [hu1cnt, hu1one]; omega)
          (by simp only [operand_val_12]; rw [hu1cnt]; omega)
      refine ⟨u2, 2 + 1, EvalG.seq e1 (EvalG.action _ u1 hu1run hsafe), by omega,
        by omega, u2s, by rw [u2r, put_same], ?_, ?_, ?_, ?_⟩
      · have hm' : N - m = (N - (m + 1)) + 1 := by omega
        have hemit : Emits u u2 [0] := by
          have h0 : u.regs rZERO = 0 := hu0
          rw [h0] at hu1emit
          refine ⟨by simp [u2, g2, hu1emit.1], fun a => ?_⟩
          simp only [u2, g2]
          exact hu1emit.2 a
        rw [hm', List.replicate_succ']
        exact huemit.trans hemit
      · intro r h10 h12
        rw [u2r, put_ne _ _ h12, hu1fr r h10, hufr r h10 h12]
      · simp [u2, g2, hu1kr, hukr]
      · simp [u2, g2, hu1k, huk])
    N s hQ
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨_, hs'run, _, hs'emit, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', j, hl, ?_, hs'run, by simpa using hs'emit, hs'fr, hs'kr, hs'k⟩
  have : N * (3 + 2) = 5 * N := by rw [Nat.mul_comm]
  omega

/-- **Zero cells.** `zerosBlock cnt` appends `regs cnt` zero cells. -/
theorem zeros_spec {W : Nat} (hW : 32 ≤ W) (cnt : Operand)
    (s : State) (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (hext : s.extent + s.regs cnt + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W (zerosBlock cnt) s s' k ∧ k ≤ 5 * s.regs cnt + 2 ∧ s'.status = .running ∧
      Emits s s' (List.replicate (s.regs cnt) 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨t, k1, e1, hk1, ht, htr, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.move rECNT cnt] s hrun (by simp [pureOKs, pureOK])
  have t12 : t.regs 12 = s.regs cnt := by
    rw [htr]; simp only [pureRegs, pureReg, operand_val_12, put_same]
  have tfr : ∀ r : Nat, r ≠ 12 → t.regs r = s.regs r := by
    intro r hr; rw [htr]; simp only [pureRegs, pureReg, operand_val_12]; exact put_ne _ _ hr
  obtain ⟨s', k2, e2, hk2, hr', hem, hfr, hkr, hks⟩ :=
    zeroLoop_spec hW t ht (by rw [tfr 0 (by decide), hzero]) (by rw [tfr 2 (by decide), hone])
      (s.regs cnt) t12 (by rw [hte]; omega)
  have hem' : Emits s s' (List.replicate (s.regs cnt) 0) := by
    have h0 : Emits s t [] := Emits.of_eq hte htm
    simpa using h0.trans hem
  refine ⟨s', k1 + k2, EvalG.seq e1 e2, by simp at hk1; omega, hr', hem', ?_, by rw [hkr, htkr],
    by rw [hks, htk]⟩
  intro r h10 h12
  rw [hfr r h10 h12, tfr r h12]

/-! ## Header cells -/

/-- **Header reservation.** Appends `oldW` zero cells, records their base in
register 220 and the BP base `base + oldW` in register 119. -/
theorem headerReserve_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1) (oldW : Nat) (h75 : s.regs 75 = oldW)
    (hold : 1 ≤ oldW) (hext : s.extent + oldW + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W headerReserveBlock s s' k ∧ k ≤ 5 * oldW + 2 ∧ s'.status = .running ∧
      Emits s s' (List.replicate oldW 0) ∧ s'.regs 220 = s.extent ∧
      s'.regs 119 = s.extent + oldW ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → r ≠ 119 → r ≠ 220 → r ≠ 226 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨t, k1, e1, hk1, ht, htr, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.arithmetic .sub rH1 rOLDW rONE] s hrun (by
      pre1_finish_simp [h75, hone]; omega)
  have t226 : t.regs 226 = oldW - 1 := by rw [htr]; pre1_finish_simp [h75, hone]
  have tfr : ∀ r : Nat, r ≠ 226 → t.regs r = s.regs r := by
    intro r hr; rw [htr]; pre1_finish_simp [hr]
  obtain ⟨u, k2, e2, hk2, hu, hem, hu220, hufr, hukr, huk⟩ :=
    reserveArray_spec hW rBUF rH1 (by decide) (by decide) (by decide) (by decide) (by decide) t ht
      (by rw [tfr 0 (by decide), hzero]) (by rw [tfr 2 (by decide), hone])
      (by simp only [operand_val_226]; rw [t226, hte]; omega)
  simp only [operand_val_226, operand_val_220, t226] at hem hk2 hu220 hufr
  rw [show oldW - 1 + 1 = oldW by omega] at hem
  have hu75 : u.regs 75 = oldW := by
    rw [hufr 75 (by decide) (by decide) (by decide), tfr 75 (by decide), h75]
  have huext : u.extent = s.extent + oldW := by
    rw [hem.1, List.length_replicate, hte]
  obtain ⟨s', k3, e3, hk3, hs', hsr, hsm, hse, hsk, hskr⟩ :=
    RegSpec.pure hW [.arithmetic .add rBPB rBUF rOLDW] u hu (by
      pre1_finish_simp [hu75, hu220, hte]; omega)
  have hem' : Emits s s' (List.replicate oldW 0) := by
    have h0 : Emits s t [] := Emits.of_eq hte htm
    have h3 : Emits u s' [] := Emits.of_eq hse hsm
    simpa using (h0.trans hem).trans h3
  refine ⟨s', k1 + (k2 + k3), EvalG.seq e1 (EvalG.seq e2 e3), ?_, hs', hem', ?_, ?_, ?_,
    by rw [hskr, hukr, htkr], by rw [hsk, huk, htk]⟩
  · simp at hk1 hk3; omega
  · rw [hsr]; pre1_finish_simp [hu220, hte]
  · rw [hsr]; pre1_finish_simp [hu220, hu75, hte]
  · intro r h10 h12 h119 h220 h226
    rw [hsr]; pre1_finish_simp [h119]
    rw [hufr r h220 h10 h12, tfr r h226]

/-- **Header patch.** Stores bit `i` of the long count into header cell `i`,
for `i < oldW`, and changes no other memory. -/
theorem headerPatch_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2) (buf oldW lc : Nat) (h220 : u.regs 220 = buf)
    (h75 : u.regs 75 = oldW) (h177 : u.regs 177 = lc) (hlcW : lc < 2 ^ W)
    (hbuf : buf + oldW ≤ u.extent) (hextW : u.extent < 2 ^ W) :
    ∃ u' k, SafeEval W headerPatchBlock u u' k ∧ k ≤ 8 * oldW + 4 ∧ u'.status = .running ∧
      u'.extent = u.extent ∧
      (∀ a, u'.memory a =
        if buf ≤ a ∧ a < buf + oldW then some (lc / 2 ^ (a - buf) % 2) else u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (221 ≤ r ∧ r ≤ 223) → r ≠ 226 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  have hW2 : 2 < 2 ^ W := two_le_two_pow hW
  obtain ⟨t, k1, e1, hk1, ht, htr, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.move rHX rLCNT] u hrun (by simp [pureOKs, pureOK])
  have t221 : t.regs 221 = lc := by rw [htr]; pre1_finish_simp [h177]
  have tfr : ∀ r : Nat, r ≠ 221 → t.regs r = u.regs r := by
    intro r hr; rw [htr]; pre1_finish_simp [hr]
  let Inv : Nat → State → Prop := fun k v =>
    v.regs 221 = lc / 2 ^ k ∧ v.extent = u.extent ∧
      (∀ a, v.memory a =
        if buf ≤ a ∧ a < buf + k then some (lc / 2 ^ (a - buf) % 2) else u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (221 ≤ r ∧ r ≤ 223) → r ≠ 226 → v.regs r = u.regs r) ∧
      v.keyRegs = u.keyRegs ∧ v.keys = u.keys
  obtain ⟨u', k2, e2, hk2, hr', hinv, _, _⟩ :=
    forSlots_spec hW rHI rHIGO rOLDW headerPatchStepBlock 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) Inv t ht (by rw [tfr 2 (by decide), hone])
      (by simp only [operand_val_75]; rw [tfr 75 (by decide), h75]; omega)
      (by
        intro v _ hvr hvm hve hvk hvkr
        refine ⟨?_, by rw [hve, hte], ?_, ?_, by rw [hvkr, htkr], by rw [hvk, htk]⟩
        · rw [hvr 221 (by decide) (by decide), t221]; simp
        · intro a; rw [hvm, htm, if_neg (by omega)]
        · intro r h108 h2 h226
          rw [hvr r (by simp only [operand_val_222]; omega) (by simp only [operand_val_223]; omega),
            tfr r (by omega)])
      (by
        intro k v hk ⟨v221, vext, vmem, vfr, vkr, vk⟩ hvrun hvi hvcnt hvone
        simp only [operand_val_75, operand_val_222] at hk hvi hvcnt
        rw [tfr 75 (by decide), h75] at hk hvcnt
        have v220 : v.regs 220 = buf := by rw [vfr 220 (by decide) (by decide) (by decide), h220]
        have v9 : v.regs 9 = 2 := by rw [vfr 9 (by decide) (by decide) (by decide), htwo]
        have hq := Nat.div_le_self lc (2 ^ k)
        obtain ⟨w1, p1, r1, m1, x1, k1', kr1⟩ :=
          prefix_pure hW (.arithmetic .add rADDR rBUF rHI) v hvrun (by
            pre1_finish_simp [v220, hvi]; omega)
        have w1r : w1.regs = put v.regs 108 (buf + k) := by
          rw [r1]; pre1_finish_simp [v220, hvi]
        obtain ⟨w2, p2, r2, m2, x2, k2', kr2⟩ :=
          prefix_pure hW (.arithmetic .mod rH1 rHX rTWO) w1 p1.1 (by
            pre1_finish_simp [w1r, v221, v9]
            exact ⟨by have := Nat.mod_lt (lc / 2 ^ k) (show 0 < 2 by decide); omega, fun _ => by decide⟩)
        have w2r : w2.regs = put (put v.regs 108 (buf + k)) 226 (lc / 2 ^ k % 2) := by
          rw [r2, w1r]; pre1_finish_simp [v221, v9]
        obtain ⟨w3, p3, r3, m3, x3, k3', kr3⟩ :=
          prefix_store hW rADDR rH1 w2 p2.1
            (by simp only [operand_val_108]; rw [w2r, put_ne _ _ (by decide), put_same, x2, x1, vext]
                omega)
            (by simp only [operand_val_226]; rw [w2r, put_same]
                have := Nat.mod_lt (lc / 2 ^ k) (show 0 < 2 by decide); omega)
        obtain ⟨w4, p4, r4, m4, x4, k4', kr4⟩ :=
          prefix_pure hW (.arithmetic .div rHX rHX rTWO) w3 p3.1 (by
            pre1_finish_simp [r3, w2r, v221, v9]; omega)
        have w4r : w4.regs = put (put (put v.regs 108 (buf + k)) 226 (lc / 2 ^ k % 2)) 221
            (lc / 2 ^ k / 2) := by
          rw [r4, r3, w2r]; pre1_finish_simp [v221, v9]
        have w4m : w4.memory = put v.memory (buf + k) (some (lc / 2 ^ k % 2)) := by
          rw [m4, m3, w2r, m2, m1]; simp only [operand_val_108, operand_val_226]
          rw [put_ne _ _ (by decide), put_same, put_same]
        have w4e : w4.extent = v.extent := by rw [x4, x3, x2, x1]
        have pall := p1.append (p2.append (p3.append p4))
        refine ⟨w4, 1 + (1 + (1 + 1)), pall.close, by omega, pall.1, ?_, ?_, ?_, ?_⟩
        · rw [w4r]; pre1_finish_simp [hvi]
        · simp only [operand_val_75]; rw [w4r]; pre1_finish_simp [hvcnt, tfr 75 (by decide), h75]
        · rw [w4r]; pre1_finish_simp [hvone]
        · intro v' _ hv'r hv'm hv'e hv'k hv'kr
          refine ⟨?_, by rw [hv'e, w4e, vext], ?_, ?_, by rw [hv'kr, kr4, kr3, kr2, kr1, vkr],
            by rw [hv'k, k4', k3', k2', k1', vk]⟩
          · rw [hv'r 221 (by decide) (by decide), w4r, put_same, div_two_pow_succ]
          · intro a
            rw [hv'm, w4m]
            by_cases ha : a = buf + k
            · subst ha
              rw [put_same, if_pos (by omega), show buf + k - buf = k by omega]
            · rw [put_ne _ _ ha, vmem a]
              by_cases hin : buf ≤ a ∧ a < buf + k
              · rw [if_pos hin, if_pos (by omega)]
              · rw [if_neg hin, if_neg (by omega)]
          · intro r h108 h2 h226
            rw [hv'r r (by simp only [operand_val_222]; omega) (by simp only [operand_val_223]; omega), w4r, put_ne _ _ (by omega), put_ne _ _ h226,
              put_ne _ _ h108, vfr r h108 h2 h226])
  simp only [operand_val_75] at hinv hk2
  rw [tfr 75 (by decide), h75] at hinv hk2
  obtain ⟨_, hext', hmem', hfr', hkr', hk'⟩ := hinv
  refine ⟨u', k1 + k2, EvalG.seq e1 e2, ?_, hr', hext', hmem', hfr', hkr', hk'⟩
  simp at hk1
  have : oldW * (4 + 4) = 8 * oldW := by rw [Nat.mul_comm]
  omega

/-! ## Paddings -/

theorem prefix_reserve {W : Nat} (hW : 32 ≤ W) (d : Operand) (v : State)
    (hrun : v.status = .running) (h : v.extent + 1 < 2 ^ W) :
    ∃ v', ActsPrefix W [.reserve d] v v' 1 ∧ v'.regs = put v.regs d v.extent ∧
      v'.memory = v.memory ∧ v'.extent = v.extent + 1 ∧ v'.keys = v.keys ∧
      v'.keyRegs = v.keyRegs := by
  have e := EvalG.action (P := Action.Safe W) (.reserve d) v hrun (safe_reserve hW v d h)
  rw [show execPrim (Action.reserve d).prim v = _ from exec_reserve v d] at e
  exact ⟨{ v with regs := put v.regs d v.extent, extent := v.extent + 1, pc := v.pc + 1 },
    ⟨hrun, fun rest t' k' e' => acts_cons_safe rest e e'⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The dense bit count the pad block computes from the serialized length `L`:
the old cell bits `((L - 1) / oldW + 1) * oldW` rounded up to a multiple of `WW`. -/
def denseBitsOf (oldW WW L : Nat) : Nat :=
  (((L - 1) / oldW + 1) * oldW + WW - 1) / WW * WW

/-- **Paddings.** From a buffer of `L ≥ oldW` cells at `buf`, the pad block
appends one zero probe cell and then zeros, `D - L` cells in all when `L < D`
and just the probe when `L = D`, where `D` is the dense bit count of the
reference: the old cell bits `((L - 1) / oldW + 1) * oldW` rounded up to a
multiple of `WW`. -/
theorem pad_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hzero : u.regs 0 = 0) (hone : u.regs 2 = 1) (buf L oldW WW : Nat) (h220 : u.regs 220 = buf)
    (hext : u.extent = buf + L) (h75 : u.regs 75 = oldW) (h76 : u.regs 76 = WW)
    (hold : 1 ≤ oldW) (hWW : 1 ≤ WW) (hL : oldW ≤ L)
    (hcap : buf + L + oldW + WW + 2 < 2 ^ W) :
    ∃ s' k, SafeEval W padBlock u s' k ∧ k ≤ 5 * (denseBitsOf oldW WW L - L) + 18 ∧
      s'.status = .running ∧ L ≤ denseBitsOf oldW WW L ∧ denseBitsOf oldW WW L ≤ L + oldW + WW ∧
      Emits u s' (List.replicate (denseBitsOf oldW WW L - L -
        (if L < denseBitsOf oldW WW L then 1 else 0) + 1) 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → ¬ (224 ≤ r ∧ r ≤ 228) → s'.regs r = u.regs r) ∧
      s'.keyRegs = u.keyRegs ∧ s'.keys = u.keys := by
  have hDd : denseBitsOf oldW WW L = (((L - 1) / oldW + 1) * oldW + WW - 1) / WW * WW := rfl
  generalize denseBitsOf oldW WW L = D at hDd ⊢
  have hLo : L - oldW + oldW = L := by omega
  have hq1 : (L - 1) / oldW ≤ L - 1 := Nat.div_le_self _ _
  have hq2 : (L - 1) / oldW * oldW ≤ L - 1 := Nat.div_mul_le_self _ _
  have hq3 : L - 1 < (L - 1) / oldW * oldW + oldW := Nat.lt_div_mul_add (by omega)
  have hH2eq : ((L - 1) / oldW + 1) * oldW = (L - 1) / oldW * oldW + oldW := Nat.succ_mul _ _
  generalize hH2d : ((L - 1) / oldW + 1) * oldW = H2 at hH2eq hDd
  have hH2L : L ≤ H2 := by omega
  have hH2le : H2 ≤ L - 1 + oldW := by omega
  have hd1 : (H2 + WW - 1) / WW ≤ H2 + WW - 1 := Nat.div_le_self _ _
  have hd2 : (H2 + WW - 1) / WW * WW ≤ H2 + WW - 1 := Nat.div_mul_le_self _ _
  have hd3 : H2 ≤ (H2 + WW - 1) / WW * WW := selectCeilDiv_mul_ge_of_pos (n := H2) (by omega)
  generalize hDg : (H2 + WW - 1) / WW * WW = D at hd2 hd3 hDd
  subst hDd
  have hW2 : 2 < 2 ^ W := two_le_two_pow hW
  -- reserve PROBE; store PROBE ZERO
  obtain ⟨v1, p1, r1, m1, x1, k1, kr1⟩ := prefix_reserve hW rPROBE u hrun (by rw [hext]; omega)
  obtain ⟨v2, p2, r2, m2, x2, k2, kr2⟩ :=
    prefix_store hW rPROBE rZERO v1 p1.1
      (by rw [r1, x1]; simp only [operand_val_224, put_same]; omega)
      (by rw [r1]; simp only [operand_val_224, operand_val_0]; rw [put_ne _ _ (by decide), hzero]; omega)
  have v2r : v2.regs = put u.regs 224 (buf + L) := by rw [r2, r1, hext]; rfl
  have v2m : v2.memory = put u.memory (buf + L) (some 0) := by
    rw [m2, m1, r1]; simp only [operand_val_224, operand_val_0]
    rw [put_same, put_ne _ _ (by decide), hzero, hext]
  have v2e : v2.extent = buf + L + 1 := by rw [x2, x1, hext]
  obtain ⟨v3, p3, r3, m3, x3, k3, kr3⟩ := prefix_pureList hW
    [.arithmetic .sub rH1 rPROBE rBUF,
      .arithmetic .sub rH2 rH1 rOLDW, .arithmetic .add rH2 rH2 rOLDW,
      .arithmetic .sub rH2 rH2 rONE, .arithmetic .div rH2 rH2 rOLDW,
      .arithmetic .add rH2 rH2 rONE, .arithmetic .mul rH2 rH2 rOLDW,
      .arithmetic .add rDB rH2 rWW, .arithmetic .sub rDB rDB rONE,
      .arithmetic .div rDB rDB rWW, .arithmetic .mul rDB rDB rWW,
      .arithmetic .sub rPAD rDB rH1, .comparison .lt rH2 rH1 rDB,
      .arithmetic .sub rPAD rPAD rH2] v2 p2.1 (by
      pre1_finish_simp [v2r, h220, h75, h76, hone, Nat.add_sub_cancel_left, hLo, hH2d, hDg]
      repeat' apply And.intro
      all_goals first | omega | (split <;> omega))
  have v3_225 : v3.regs 225 = D - L - (if L < D then 1 else 0) := by
    rw [r3]; pre1_finish_simp [v2r, h220, h75, h76, hone, Nat.add_sub_cancel_left, hLo, hH2d, hDg]
  have v3fr : ∀ r : Nat, ¬ (224 ≤ r ∧ r ≤ 228) → v3.regs r = u.regs r := by
    intro r hr
    have a1 : r ≠ 224 := by omega
    have a2 : r ≠ 225 := by omega
    have a3 : r ≠ 226 := by omega
    have a4 : r ≠ 227 := by omega
    have a5 : r ≠ 228 := by omega
    rw [r3]; pre1_finish_simp [v2r, a1, a2, a3, a4, a5]
  have pall := p1.append (p2.append p3)
  have e1 : SafeEval W (acts [.reserve rPROBE, .store rPROBE rZERO,
      .arithmetic .sub rH1 rPROBE rBUF,
      .arithmetic .sub rH2 rH1 rOLDW, .arithmetic .add rH2 rH2 rOLDW,
      .arithmetic .sub rH2 rH2 rONE, .arithmetic .div rH2 rH2 rOLDW,
      .arithmetic .add rH2 rH2 rONE, .arithmetic .mul rH2 rH2 rOLDW,
      .arithmetic .add rDB rH2 rWW, .arithmetic .sub rDB rDB rONE,
      .arithmetic .div rDB rDB rWW, .arithmetic .mul rDB rDB rWW,
      .arithmetic .sub rPAD rDB rH1, .comparison .lt rH2 rH1 rDB,
      .arithmetic .sub rPAD rPAD rH2]) u v3 (1 + (1 + 14)) := pall.close
  obtain ⟨s', kz, ez, hkz, hs', hem, hfr, hkr, hks⟩ :=
    zeros_spec hW rPAD v3 pall.1
      (by rw [v3fr 0 (by decide), hzero]) (by rw [v3fr 2 (by decide), hone])
      (by simp only [operand_val_225]; rw [v3_225, x3, v2e]; split <;> omega)
  simp only [operand_val_225, v3_225] at hem hkz
  have hprobe : Emits u v3 [0] := by
    refine ⟨by rw [x3, v2e, hext]; rfl, fun a => ?_⟩
    rw [m3, v2m, hext]
    by_cases ha : a = buf + L
    · subst ha; simp
    · rw [put_ne _ _ ha, if_neg (by simp; omega)]
  refine ⟨s', 1 + (1 + 14) + kz, EvalG.seq e1 ez, ?_, hs', by omega, by omega, ?_, ?_,
    by rw [hkr, kr3, kr2, kr1], by rw [hks, k3, k2, k1]⟩
  · split at hkz <;> omega
  · rw [List.replicate_succ]
    exact hprobe.trans hem
  · intro r h10 h12 hr
    rw [hfr r h10 h12, v3fr r hr]

end RMQ.SuccinctFinal.PackedConstruction.Proof

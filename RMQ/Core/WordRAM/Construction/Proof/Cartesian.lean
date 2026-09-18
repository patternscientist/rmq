import RMQ.Core.WordRAM.Construction.Proof.Leaf
import RMQ.Core.WordRAM.Construction.Spec.Spine

/-! # PRE-1 builder proofs: Cartesian stack pass and BP emission (stage S3)

Outside the builder firewall. The three stack-pass arrays live in one region of
`3 * (n + 1)` cells starting at `e0`: the stack at offsets `[0, n]`, the
leftmost-descendant array at `[n + 1, 2 n + 1]`, the open-count array at
`[2 n + 2, 3 n + 2]`. `Region u e0 len M` says the region holds the values `M`.
The stack-pass invariant identifies, after `i` indices, the stack with the right
spine `spineFrom (buildTree (xs.take i)) 0`, the recorded leftmost descendants of
its nodes with the spine's leftmost indices, and the count array with
`openCounts (buildTree (xs.take i)).shape`. The only key hypothesis is
`KeySpec` of the leaf.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec Spec.StackCartesianTreeSpec RMQ.Cartesian

/-! ## Memory regions -/

/-- The region `[e0, e0 + len)` holds `M 0, …, M (len - 1)`. -/
def Region (u : State) (e0 len : Nat) (M : Nat → Nat) : Prop :=
  ∀ a, a < len → u.memory (e0 + a) = some (M a)

theorem store_region {u : State} {e0 len : Nat} {M : Nat → Nat} (hR : Region u e0 len M)
    (hext : e0 + len ≤ u.extent) (addr v : Operand) {a : Nat} (ha : a < len)
    (haddr : u.regs addr = e0 + a) :
    (execPrim (.store addr v) u).regs = u.regs ∧
    (execPrim (.store addr v) u).extent = u.extent ∧
    (execPrim (.store addr v) u).keys = u.keys ∧
    (execPrim (.store addr v) u).keyRegs = u.keyRegs ∧
    (execPrim (.store addr v) u).status = u.status ∧
    Region (execPrim (.store addr v) u) e0 len (put M a (u.regs v)) ∧
    (∀ b, (b < e0 ∨ e0 + len ≤ b) → (execPrim (.store addr v) u).memory b = u.memory b) := by
  have hlt : u.regs addr < u.extent := by omega
  rw [exec_store u addr v hlt]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun b hb => ?_, fun b hb => ?_⟩
  · simp only [haddr]
    by_cases hba : b = a
    · subst hba; simp [put]
    · rw [put_ne _ _ (by omega), hR b hb, put_ne _ _ hba]
  · simp only [haddr]
    rw [put_ne _ _ (by omega)]

theorem load_region {u : State} {e0 len : Nat} {M : Nat → Nat} (hR : Region u e0 len M)
    (hext : e0 + len ≤ u.extent) (d addr : Operand) {a : Nat} (ha : a < len)
    (haddr : u.regs addr = e0 + a) :
    execPrim (.load d addr) u = { u with regs := put u.regs d (M a), pc := u.pc + 1 } := by
  have hlt : u.regs addr < u.extent := by omega
  have hm : u.memory (u.regs addr) = some (M a) := by rw [haddr]; exact hR a ha
  exact exec_load u d addr hlt hm

theorem safe_load_region {W : Nat} (hW : 32 ≤ W) {u : State} {e0 len : Nat} {M : Nat → Nat}
    (hR : Region u e0 len M) (hext : e0 + len ≤ u.extent) (d addr : Operand) {a : Nat}
    (ha : a < len) (haddr : u.regs addr = e0 + a) (hv : M a < 2 ^ W) :
    Action.Safe W u (.load d addr) :=
  ⟨Prim.operandsFit_of_width _ hW, by omega, M a, by rw [haddr]; exact hR a ha, hv⟩

/-! ## The three arrays -/

/-- **Stack-pass arrays.** -/
theorem stackArrays_spec {W : Nat} (hW : 32 ≤ W) (n : Nat) (s : State)
    (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (hn : s.regs 1 = n) (hext : s.extent + 3 * (n + 1) < 2 ^ W) :
    ∃ s' k, SafeEval W stackArraysBlock s s' k ∧ k ≤ 15 * n + 12 ∧ s'.status = .running ∧
      Emits s s' (List.replicate (3 * (n + 1)) 0) ∧
      s'.regs 100 = s.extent ∧ s'.regs 101 = s.extent + (n + 1) ∧
      s'.regs 102 = s.extent + 2 * (n + 1) ∧
      (∀ r : Nat, r ≠ 100 → r ≠ 101 → r ≠ 102 → r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨u1, k1, e1, hk1, hr1, hem1, hb1, hfr1, hkr1, hks1⟩ :=
    reserveArray_spec hW rSTK rN (by decide) (by decide) (by decide) (by decide) (by decide)
      s hrun hzero hone (by simp only [operand_val_1]; rw [hn]; omega)
  simp only [operand_val_1, hn, operand_val_100] at hk1 hem1 hb1
  have hu1z : u1.regs 0 = 0 := by rw [hfr1 0 (by decide) (by decide) (by decide)]; exact hzero
  have hu1o : u1.regs 2 = 1 := by rw [hfr1 2 (by decide) (by decide) (by decide)]; exact hone
  have hu1n : u1.regs 1 = n := by rw [hfr1 1 (by decide) (by decide) (by decide)]; exact hn
  have hu1e : u1.extent = s.extent + (n + 1) := by rw [hem1.1]; simp
  obtain ⟨u2, k2, e2, hk2, hr2, hem2, hb2, hfr2, hkr2, hks2⟩ :=
    reserveArray_spec hW rLDB rN (by decide) (by decide) (by decide) (by decide) (by decide)
      u1 hr1 hu1z hu1o (by simp only [operand_val_1]; rw [hu1n, hu1e]; omega)
  simp only [operand_val_1, hu1n, operand_val_101] at hk2 hem2 hb2
  have hu2z : u2.regs 0 = 0 := by rw [hfr2 0 (by decide) (by decide) (by decide)]; exact hu1z
  have hu2o : u2.regs 2 = 1 := by rw [hfr2 2 (by decide) (by decide) (by decide)]; exact hu1o
  have hu2n : u2.regs 1 = n := by rw [hfr2 1 (by decide) (by decide) (by decide)]; exact hu1n
  have hu2e : u2.extent = s.extent + 2 * (n + 1) := by rw [hem2.1, hu1e]; simp; omega
  obtain ⟨u3, k3, e3, hk3, hr3, hem3, hb3, hfr3, hkr3, hks3⟩ :=
    reserveArray_spec hW rCNTB rN (by decide) (by decide) (by decide) (by decide) (by decide)
      u2 hr2 hu2z hu2o (by simp only [operand_val_1]; rw [hu2n, hu2e]; omega)
  simp only [operand_val_1, hu2n, operand_val_102] at hk3 hem3 hb3
  refine ⟨u3, k1 + (k2 + k3), EvalG.seq e1 (EvalG.seq e2 e3), by omega, hr3, ?_, ?_, ?_, ?_, ?_,
    by rw [hkr3, hkr2, hkr1], by rw [hks3, hks2, hks1]⟩
  · have := (hem1.trans hem2).trans hem3
    rw [List.replicate_append_replicate, List.replicate_append_replicate] at this
    have e : n + 1 + (n + 1) + (n + 1) = 3 * (n + 1) := by omega
    rwa [e] at this
  · rw [hfr3 100 (by decide) (by decide) (by decide), hfr2 100 (by decide) (by decide) (by decide),
      hb1]
  · rw [hfr3 101 (by decide) (by decide) (by decide), hb2, hu1e]
  · rw [hb3, hu2e]
  · intro r h100 h101 h102 h10 h12
    rw [hfr3 r h102 h10 h12, hfr2 r h101 h10 h12, hfr1 r h100 h10 h12]

theorem Emits.region_zero {s₀ s : State} {len : Nat} (h : Emits s₀ s (List.replicate len 0)) :
    Region s s₀.extent len (fun _ => 0) := by
  intro a ha
  have := h.memory_at (i := a) (by simpa using ha)
  simpa using this

theorem Region.mono {u : State} {e0 len len' : Nat} {M : Nat → Nat} (h : Region u e0 len M)
    (hle : len' ≤ len) : Region u e0 len' M := fun a ha => h a (by omega)

/-- An input predicate that only reads memory, extent and keys. -/
def InpStable (Inp : State → Prop) : Prop :=
  ∀ u v : State, Inp u → v.memory = u.memory → v.extent = u.extent → v.keys = u.keys → Inp v

/-! ## The pop guard -/

/-- **Pop guard.** From a state whose stack region holds `stk` with height
`regs 103` and index `i = regs 104`, `popGuardBlock leaf` sets register 110 to
`[sp ≠ 0 ∧ xs[i] < xs[stk (sp - 1)]]` and, if `sp ≠ 0`, register 109 to
`stk (sp - 1)`, in at most 13 steps. -/
theorem popGuard_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (hInp : InpStable Inp)
    (u : State) (hrun : u.status = .running) (hinp : Inp u) (hone : u.regs 2 = 1)
    (e0 : Nat) (stk : Nat → Nat) (hbase : u.regs 100 = e0)
    (hR : Region u e0 (xs.length + 1) stk) (hext : e0 + (xs.length + 1) ≤ u.extent)
    (hsp : u.regs 103 ≤ xs.length) (hi : u.regs 104 < xs.length)
    (hstk : ∀ k, k < u.regs 103 → stk k < xs.length)
    (hcap : e0 + xs.length + 1 < 2 ^ W) :
    ∃ u' j, SafeEval W (popGuardBlock leaf) u u' j ∧ j ≤ 13 ∧ u'.status = .running ∧
      u'.regs 110 = (if u.regs 103 = 0 then 0 else
        if xs.getD (u.regs 104) 0 < xs.getD (stk (u.regs 103 - 1)) 0 then 1 else 0) ∧
      (u.regs 103 ≠ 0 → u'.regs 109 = stk (u.regs 103 - 1)) ∧
      (∀ r : Nat, r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 108 → r ≠ 109 → r ≠ 110 →
        u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys := by
  by_cases h0 : u.regs 103 = 0
  · -- empty stack: rWG := 0
    let u1 := execPrim (Prim.constant rWG 0) u
    have f1 := exec_constant u rWG 0
    have hz : u.regs rSTKH = 0 := h0
    have ev : SafeEval W (acts [.constant rWG 0]) u u1 1 :=
      EvalG.action _ u hrun (safe_constant hW u _ _)
    refine ⟨u1, 1 + 1, EvalG.ifZeroTaken hrun hz ev, by omega, by simp [u1, f1, hrun], ?_, ?_,
      ?_, by simp [u1, f1], by simp [u1, f1], by simp [u1, f1]⟩
    · rw [if_pos h0]; simp [u1, f1]
    · intro h; exact absurd h0 h
    · intro r _ _ _ _ _ _ _ h110
      simp only [u1, f1]
      rw [put_ne _ _ (by simpa using h110)]
  · generalize hspv : u.regs 103 = sp at h0 hsp hstk ⊢
    generalize hiv : u.regs 104 = i at hi ⊢
    have hsp1 : 1 ≤ sp := by omega
    have hstop := hstk (sp - 1) (by omega)
    -- add rADDR rSTK rSTKH
    let u1 := execPrim (Prim.arithmetic .add rADDR rSTK rSTKH) u
    have f1 := exec_arithmetic u .add rADDR rSTK rSTKH
    have u1r : u1.regs = put u.regs 108 (e0 + sp) := by
      simp only [u1, f1, Arithmetic.eval]
      rw [show ((rSTK : Operand) : Nat) = 100 from rfl, show ((rSTKH : Operand) : Nat) = 103 from rfl,
        hbase, hspv]; rfl
    -- sub rADDR rADDR rONE
    let u2 := execPrim (Prim.arithmetic .sub rADDR rADDR rONE) u1
    have f2 := exec_arithmetic u1 .sub rADDR rADDR rONE
    have u1a : u1.regs 108 = e0 + sp := by rw [u1r, put_same]
    have u1o : u1.regs 2 = 1 := by rw [u1r, put_ne _ _ (by decide), hone]
    have u2r : u2.regs = put u.regs 108 (e0 + (sp - 1)) := by
      simp only [u2, f2, Arithmetic.eval]
      rw [show ((rADDR : Operand) : Nat) = 108 from rfl, show ((rONE : Operand) : Nat) = 2 from rfl,
        u1a, u1o, u1r]
      funext r; simp only [put]; split <;> omega
    have u2m : u2.memory = u.memory := by simp [u2, f2, u1, f1]
    have u2e : u2.extent = u.extent := by simp [u2, f2, u1, f1]
    have u2s : u2.status = .running := by simp [u2, f2, u1, f1, hrun]
    have u2k : u2.keys = u.keys := by simp [u2, f2, u1, f1]
    have hR2 : Region u2 e0 (xs.length + 1) stk := by
      intro a ha; rw [u2m]; exact hR a ha
    have u2a : u2.regs rADDR = e0 + (sp - 1) := by
      show u2.regs 108 = _; rw [u2r, put_same]
    -- load rTOP rADDR
    let u3 := execPrim (Prim.load rTOP rADDR) u2
    have f3 := load_region hR2 (by rw [u2e]; exact hext) rTOP rADDR (a := sp - 1) (by omega) u2a
    have u3r : u3.regs = put (put u.regs 108 (e0 + (sp - 1))) 109 (stk (sp - 1)) := by
      simp only [u3, f3, u2r]; rfl
    -- move rLEAF_I rI ; move rLEAF_J rTOP
    let u4 := execPrim (Prim.move rLEAF_I rI) u3
    have f4 := exec_move u3 rLEAF_I rI
    let u5 := execPrim (Prim.move rLEAF_J rTOP) u4
    have f5 := exec_move u4 rLEAF_J rTOP
    have u3i : u3.regs 104 = i := by rw [u3r, put_ne _ _ (by decide), put_ne _ _ (by decide), hiv]
    have u4r : u4.regs = put u3.regs 4 i := by
      simp only [u4, f4]; rw [show ((rI : Operand) : Nat) = 104 from rfl, u3i]; rfl
    have u4top : u4.regs 109 = stk (sp - 1) := by
      rw [u4r, put_ne _ _ (by decide), u3r, put_same]
    have u5r : u5.regs = put (put u3.regs 4 i) 5 (stk (sp - 1)) := by
      simp only [u5, f5]; rw [show ((rTOP : Operand) : Nat) = 109 from rfl, u4top, u4r]; rfl
    have u3s : u3.status = .running := by
      show (execPrim (Prim.load rTOP rADDR) u2).status = _; rw [f3]; exact u2s
    have u4s : u4.status = .running := by
      show (execPrim (Prim.move rLEAF_I rI) u3).status = _; rw [f4]; exact u3s
    have u5m : u5.memory = u.memory := by simp [u5, f5, u4, f4, u3, f3, u2m]
    have u5e : u5.extent = u.extent := by simp [u5, f5, u4, f4, u3, f3, u2e]
    have u5s : u5.status = .running := by simp [u5, f5, u4, f4, u3, f3, u2s]
    have u5k : u5.keys = u.keys := by simp [u5, f5, u4, f4, u3, f3, u2k]
    have hsafe1 : ActsOK (Action.Safe W) [.arithmetic .add rADDR rSTK rSTKH,
        .arithmetic .sub rADDR rADDR rONE, .load rTOP rADDR, .move rLEAF_I rI,
        .move rLEAF_J rTOP] u := by
      refine ⟨safe_add hW u _ _ _ ?_, by simp [Action.prim, f1, hrun], ?_⟩
      · show u.regs 100 + u.regs 103 < 2 ^ W
        rw [hbase, hspv]; omega
      refine ⟨safe_sub hW u1 _ _ _ ?_ ?_, u2s, ?_⟩
      · show u1.regs 2 ≤ u1.regs 108
        rw [u1o, u1a]; omega
      · show u1.regs 108 < 2 ^ W
        rw [u1a]; omega
      refine ⟨safe_load_region hW hR2 (by rw [u2e]; exact hext) _ _ (by omega) u2a (by omega),
        u3s, ?_⟩
      refine ⟨safe_move hW _ _ _, u4s, ?_⟩
      exact ⟨safe_move hW _ _ _, u5s, trivial⟩
    have ev1 := acts_evalG (P := Action.Safe W) _ u hrun hsafe1
    -- the leaf
    have hinp5 : Inp u5 := hInp u u5 hinp u5m u5e u5k
    have u5o : u5.regs 2 = 1 := by
      rw [u5r, put_ne _ _ (by decide), put_ne _ _ (by decide), u3r, put_ne _ _ (by decide),
        put_ne _ _ (by decide), hone]
    have u5_4 : u5.regs 4 = i := by rw [u5r, put_ne _ _ (by decide), put_same]
    have u5_5 : u5.regs 5 = stk (sp - 1) := by rw [u5r, put_same]
    obtain ⟨u6, e6, hu6s, hu6res, hu6fr, hu6m, hu6e, hu6k⟩ :=
      hleaf u5 u5s hinp5 u5o (by rw [u5_4]; exact hi) (by rw [u5_5]; exact hstop)
    rw [u5_4, u5_5] at hu6res
    -- move rWG rLEAF_RES
    let u7 := execPrim (Prim.move rWG rLEAF_RES) u6
    have f7 := exec_move u6 rWG rLEAF_RES
    have u7r : u7.regs =
        put u6.regs 110 (if xs.getD i 0 < xs.getD (stk (sp - 1)) 0 then 1 else 0) := by
      simp only [u7, f7]; rw [show ((rLEAF_RES : Operand) : Nat) = 6 from rfl, hu6res]; rfl
    have u7s : u7.status = .running := by simp [u7, f7, hu6s]
    have ev7 : SafeEval W (acts [.move rWG rLEAF_RES]) u6 u7 1 :=
      EvalG.action _ u6 hu6s (safe_move hW _ _ _)
    have evn := EvalG.seq ev1 (EvalG.seq e6 ev7)
    refine ⟨u7, 5 + (5 + 1) + 2, EvalG.ifZeroFallthrough hrun (by simpa [hspv] using h0) evn u7s,
      by omega, u7s, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u7r, put_same, if_neg h0]
    · intro _
      rw [u7r, put_ne _ _ (by decide), hu6fr 109 (by decide) (by decide) (by decide), u5r,
        put_ne _ _ (by decide), put_ne _ _ (by decide), u3r, put_same]
    · intro r h4 h5 h6 h7 h8 h108 h109 h110
      rw [u7r, put_ne _ _ h110, hu6fr r h6 h7 h8, u5r, put_ne _ _ h5, put_ne _ _ h4, u3r,
        put_ne _ _ h109, put_ne _ _ h108]
    · simp [u7, f7, hu6m, u5m]
    · simp [u7, f7, hu6e, u5e]
    · simp [u7, f7, hu6k, u5k]

/-! ## The pop loop -/

/-- The value of register 110 that the pop guard computes at stack height `sp`. -/
def guardVal (xs : List Int) (v : Int) (stk : Nat → Nat) (sp : Nat) : Nat :=
  if sp = 0 then 0 else if v < xs.getD (stk (sp - 1)) 0 then 1 else 0

/-- **Pop loop.** Pops while the new key is strictly smaller than the key at the
top: afterwards every popped entry had a strictly larger key, the new top (if
any) does not, register 107 records whether anything was popped and register
106 holds the last popped entry. The cost pays 18 per pop plus 1. -/
theorem popLoop_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (hInp : InpStable Inp)
    (u : State) (hrun : u.status = .running) (hinp : Inp u) (hone : u.regs 2 = 1)
    (e0 : Nat) (stk : Nat → Nat) (hbase : u.regs 100 = e0)
    (hR : Region u e0 (xs.length + 1) stk) (hext : e0 + (xs.length + 1) ≤ u.extent)
    (hsp : u.regs 103 ≤ xs.length) (hi : u.regs 104 < xs.length)
    (hstk : ∀ k, k < u.regs 103 → stk k < xs.length)
    (hcap : e0 + xs.length + 1 < 2 ^ W) (hpop : u.regs 107 = 0)
    (hguard : u.regs 110 = guardVal xs (xs.getD (u.regs 104) 0) stk (u.regs 103))
    (htop : u.regs 103 ≠ 0 → u.regs 109 = stk (u.regs 103 - 1)) :
    ∃ u' j, SafeEval W (.loop rWG (popBodyBlock leaf)) u u' j ∧
      j + u'.regs 103 * 18 ≤ u.regs 103 * 18 + 1 ∧ u'.status = .running ∧
      u'.regs 103 ≤ u.regs 103 ∧
      (∀ k, u'.regs 103 ≤ k → k < u.regs 103 → xs.getD (u.regs 104) 0 < xs.getD (stk k) 0) ∧
      (u'.regs 103 = 0 ∨ ¬ (xs.getD (u.regs 104) 0 < xs.getD (stk (u'.regs 103 - 1)) 0)) ∧
      u'.regs 107 = (if u'.regs 103 < u.regs 103 then 1 else 0) ∧
      (u'.regs 103 < u.regs 103 → u'.regs 106 = stk (u'.regs 103)) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 103 → ¬ (106 ≤ r ∧ r ≤ 110) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys := by
  generalize hsp0 : u.regs 103 = sp0 at hsp hstk hguard htop ⊢
  generalize hiv : u.regs 104 = i at hi hguard ⊢
  let v := xs.getD i 0
  let Q : State → Prop := fun w =>
    w.status = .running ∧ Inp w ∧ w.regs 2 = 1 ∧ w.regs 100 = e0 ∧ w.regs 104 = i ∧
      w.regs 103 ≤ sp0 ∧ w.memory = u.memory ∧ w.extent = u.extent ∧ w.keys = u.keys ∧
      (∀ k, w.regs 103 ≤ k → k < sp0 → v < xs.getD (stk k) 0) ∧
      w.regs 107 = (if w.regs 103 < sp0 then 1 else 0) ∧
      (w.regs 103 < sp0 → w.regs 106 = stk (w.regs 103)) ∧
      w.regs 110 = guardVal xs v stk (w.regs 103) ∧
      (w.regs 103 ≠ 0 → w.regs 109 = stk (w.regs 103 - 1)) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 103 → ¬ (106 ≤ r ∧ r ≤ 110) → w.regs r = u.regs r)
  have hQ : Q u := by
    refine ⟨hrun, hinp, hone, hbase, hiv, by omega, rfl, rfl, rfl, fun k h1 h2 => by omega, ?_,
      fun h => by omega, by rw [hsp0]; exact hguard, by rw [hsp0]; exact htop,
      fun _ _ _ _ => rfl⟩
    rw [hpop, if_neg (by omega)]
  have hloop := EvalG.loop_measure_pot (P := Action.Safe W) Q (fun w => w.regs 103) rWG
    (popBodyBlock leaf) 16 (fun w hw => hw.1)
    (by
      intro w hw hc
      obtain ⟨hwr, hwinp, hwo, hwb, hwi, hwsp, hwm, hwe, hwk, hwpops, _, _, hwg, hwt, hwfr⟩ := hw
      generalize hspw : w.regs 103 = sp at hwsp hwpops hwg hwt
      have hg : guardVal xs v stk sp ≠ 0 := by
        rw [← hwg]; exact hc
      have hsp1 : sp ≠ 0 := by intro h; simp [guardVal, h] at hg
      have hlt : v < xs.getD (stk (sp - 1)) 0 := by
        simp only [guardVal, if_neg hsp1] at hg
        by_cases h : v < xs.getD (stk (sp - 1)) 0
        · exact h
        · rw [if_neg h] at hg; exact absurd rfl hg
      have hwtop := hwt hsp1
      -- move rLAST rTOP; sub rSTKH rSTKH rONE; constant rPOP 1
      obtain ⟨w1, k1, e1, hk1, hw1r, hw1R, hw1m, hw1e, hw1k, hw1kr⟩ :=
        RegSpec.pure hW [.move rLAST rTOP, .arithmetic .sub rSTKH rSTKH rONE, .constant rPOP 1]
          w hwr (by
            refine ⟨trivial, ⟨?_, fun _ => ?_, by simp, by simp⟩, trivial, trivial⟩
            · show put w.regs 106 (w.regs 109) 103 - put w.regs 106 (w.regs 109) 2 < 2 ^ W
              rw [put_ne _ _ (by decide), put_ne _ _ (by decide), hspw]; omega
            · show put w.regs 106 (w.regs 109) 2 ≤ put w.regs 106 (w.regs 109) 103
              rw [put_ne _ _ (by decide), put_ne _ _ (by decide), hspw, hwo]; omega)
      have w1reg : w1.regs = put (put (put w.regs 106 (stk (sp - 1))) 103 (sp - 1)) 107 1 := by
        rw [hw1R]
        show put (put (put w.regs 106 (w.regs 109)) 103
          (put w.regs 106 (w.regs 109) 103 - put w.regs 106 (w.regs 109) 2)) 107 1 = _
        rw [put_ne _ _ (by decide), put_ne _ _ (by decide), hspw, hwo, hwtop]
      have w1_103 : w1.regs 103 = sp - 1 := by
        rw [w1reg, put_ne _ _ (by decide), put_same]
      have w1_2 : w1.regs 2 = 1 := by
        rw [w1reg, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), hwo]
      have w1_100 : w1.regs 100 = e0 := by
        rw [w1reg, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), hwb]
      have w1_104 : w1.regs 104 = i := by
        rw [w1reg, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), hwi]
      have hw1inp : Inp w1 := hInp w w1 hwinp hw1m hw1e hw1k
      have hR1 : Region w1 e0 (xs.length + 1) stk := by
        intro a ha; rw [hw1m, hwm]; exact hR a ha
      obtain ⟨w2, k2, e2, hk2, hw2r, hw2g, hw2t, hw2fr, hw2m, hw2e, hw2k⟩ :=
        popGuard_spec hW xs Inp leaf hleaf hInp w1 hw1r hw1inp w1_2 e0 stk w1_100 hR1
          (by rw [hw1e, hwe]; exact hext) (by rw [w1_103]; omega) (by rw [w1_104]; exact hi)
          (fun k hk => hstk k (by rw [w1_103] at hk; omega)) hcap
      simp only [w1_103, w1_104] at hw2g hw2t
      have w2_103 : w2.regs 103 = sp - 1 := by
        rw [hw2fr 103 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1_103]
      refine ⟨w2, k1 + k2, EvalG.seq e1 e2, by simp at hk1; omega, ?_, by simp; omega⟩
      refine ⟨hw2r, hInp w1 w2 hw1inp hw2m hw2e hw2k, ?_, ?_, ?_, by rw [w2_103]; omega,
        by rw [hw2m, hw1m, hwm], by rw [hw2e, hw1e, hwe], by rw [hw2k, hw1k, hwk], ?_, ?_, ?_,
        by rw [w2_103]; exact hw2g, by rw [w2_103]; exact hw2t, ?_⟩
      · rw [hw2fr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1_2]
      · rw [hw2fr 100 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1_100]
      · rw [hw2fr 104 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1_104]
      · intro k h1 h2
        rw [w2_103] at h1
        by_cases hk : k = sp - 1
        · subst hk; exact hlt
        · exact hwpops k (by omega) h2
      · rw [hw2fr 107 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1reg, put_same, w2_103, if_pos (by omega)]
      · intro _
        rw [hw2fr 106 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), w1reg, put_ne _ _ (by decide), put_ne _ _ (by decide),
          put_same, w2_103]
      · intro r h48 h103 h106
        have n4 : r ≠ 4 := fun h => h48 ⟨by omega, by omega⟩
        have n5 : r ≠ 5 := fun h => h48 ⟨by omega, by omega⟩
        have n6 : r ≠ 6 := fun h => h48 ⟨by omega, by omega⟩
        have n7 : r ≠ 7 := fun h => h48 ⟨by omega, by omega⟩
        have n8 : r ≠ 8 := fun h => h48 ⟨by omega, by omega⟩
        have n106 : r ≠ 106 := fun h => h106 ⟨by omega, by omega⟩
        have n107 : r ≠ 107 := fun h => h106 ⟨by omega, by omega⟩
        have n108 : r ≠ 108 := fun h => h106 ⟨by omega, by omega⟩
        have n109 : r ≠ 109 := fun h => h106 ⟨by omega, by omega⟩
        have n110 : r ≠ 110 := fun h => h106 ⟨by omega, by omega⟩
        rw [hw2fr r n4 n5 n6 n7 n8 n108 n109 n110, w1reg, put_ne _ _ n107, put_ne _ _ h103,
          put_ne _ _ n106, hwfr r h48 h103 h106])
    sp0 u (by show u.regs 103 ≤ sp0; omega) hQ
  obtain ⟨u', j, hl, hj, hq, hc⟩ := hloop
  obtain ⟨hr', _, _, _, _, hsp', hm', he', hk', hpops', h107', h106', hg', _, hfr'⟩ := hq
  simp only [hsp0] at hj
  refine ⟨u', j, hl, hj, hr', hsp', hpops', ?_, h107', h106', hfr', hm', he', hk'⟩
  have : guardVal xs v stk (u'.regs 103) = 0 := by rw [← hg']; exact hc
  simp only [guardVal] at this
  by_cases h0 : u'.regs 103 = 0
  · exact Or.inl h0
  · right
    intro hlt
    rw [if_neg h0, if_pos hlt] at this
    exact absurd this (by decide)

/-! ## Link and push -/

/-- The region contents after linking and pushing node `i`. -/
def linkPushM (n i sp ld : Nat) (popped : Bool) (M : Nat → Nat) : Nat → Nat :=
  if popped then
    put (put (put M (2 * (n + 1) + ld) (M (2 * (n + 1) + ld) + 1)) (n + 1 + i) ld) sp i
  else
    put (put (put M (n + 1 + i) i) (2 * (n + 1) + i) 1) sp i

/-- **Link and push.** -/
theorem linkPush_spec {W : Nat} (hW : 32 ≤ W) (n : Nat) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (e0 : Nat) (M : Nat → Nat)
    (h100 : u.regs 100 = e0) (h101 : u.regs 101 = e0 + (n + 1))
    (h102 : u.regs 102 = e0 + 2 * (n + 1))
    (hR : Region u e0 (3 * (n + 1)) M) (hext : e0 + 3 * (n + 1) ≤ u.extent)
    (hcap : e0 + 3 * (n + 1) + n + 2 < 2 ^ W)
    (i sp : Nat) (hi : u.regs 104 = i) (hin : i < n) (hsp : u.regs 103 = sp) (hspn : sp ≤ n)
    (popped : Bool) (hpop : u.regs 107 = if popped then 1 else 0)
    (hlast : popped = true → u.regs 106 < n ∧ M (n + 1 + u.regs 106) < n ∧
      M (2 * (n + 1) + M (n + 1 + u.regs 106)) ≤ n) :
    ∃ u' j, SafeEval W (.seq linkBlock pushBlock) u u' j ∧ j ≤ 13 ∧ u'.status = .running ∧
      Region u' e0 (3 * (n + 1))
        (linkPushM n i sp (if popped then M (n + 1 + u.regs 106) else 0) popped M) ∧
      u'.regs 103 = sp + 1 ∧
      (∀ r : Nat, r ≠ 103 → r ≠ 108 → r ≠ 111 → r ≠ 112 → u'.regs r = u.regs r) ∧
      (∀ b, (b < e0 ∨ e0 + 3 * (n + 1) ≤ b) → u'.memory b = u.memory b) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys := by
  have hW32 : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  -- the push, from any state with the bases, index and height in place
  have push : ∀ (w : State), w.status = .running → w.regs 2 = 1 → w.regs 100 = e0 →
      w.regs 104 = i → w.regs 103 = sp → ∀ (M' : Nat → Nat), Region w e0 (3 * (n + 1)) M' →
      e0 + 3 * (n + 1) ≤ w.extent →
      ∃ w' j, SafeEval W pushBlock w w' j ∧ j = 3 ∧ w'.status = .running ∧
        Region w' e0 (3 * (n + 1)) (put M' sp i) ∧ w'.regs 103 = sp + 1 ∧
        (∀ r : Nat, r ≠ 103 → r ≠ 108 → w'.regs r = w.regs r) ∧
        (∀ b, (b < e0 ∨ e0 + 3 * (n + 1) ≤ b) → w'.memory b = w.memory b) ∧
        w'.extent = w.extent ∧ w'.keys = w.keys := by
    intro w hwr hwo hw100 hwi hwsp M' hwR hwext
    let w1 := execPrim (Prim.arithmetic .add rADDR rSTK rSTKH) w
    have g1 := exec_arithmetic w .add rADDR rSTK rSTKH
    have w1r : w1.regs = put w.regs 108 (e0 + sp) := by
      simp only [w1, g1, Arithmetic.eval]
      rw [show ((rSTK : Operand) : Nat) = 100 from rfl, show ((rSTKH : Operand) : Nat) = 103 from rfl,
        hw100, hwsp]; rfl
    have hw1R : Region w1 e0 (3 * (n + 1)) M' := by intro a ha; simp only [w1, g1]; exact hwR a ha
    have hw1e : w1.extent = w.extent := by simp [w1, g1]
    have w1a : w1.regs rADDR = e0 + sp := by show w1.regs 108 = _; rw [w1r, put_same]
    obtain ⟨s2r, s2e, s2k, _, s2s, s2R, s2o⟩ :=
      store_region hw1R (by rw [hw1e]; exact hwext) rADDR rI (a := sp) (by omega) w1a
    let w2 := execPrim (Prim.store rADDR rI) w1
    have w1i : w1.regs rI = i := by show w1.regs 104 = i; rw [w1r, put_ne _ _ (by decide), hwi]
    rw [w1i] at s2R
    let w3 := execPrim (Prim.arithmetic .add rSTKH rSTKH rONE) w2
    have g3 := exec_arithmetic w2 .add rSTKH rSTKH rONE
    have w2reg : w2.regs = put w.regs 108 (e0 + sp) := by rw [s2r, w1r]
    have w3r : w3.regs = put (put w.regs 108 (e0 + sp)) 103 (sp + 1) := by
      simp only [w3, g3, Arithmetic.eval]
      rw [show ((rSTKH : Operand) : Nat) = 103 from rfl, show ((rONE : Operand) : Nat) = 2 from rfl,
        w2reg, put_ne _ _ (by decide), put_ne _ _ (by decide), hwsp, hwo]
    have w1s : w1.status = .running := by simp [w1, g1, hwr]
    have w2s : w2.status = .running := by rw [s2s]; exact w1s
    have w3s : w3.status = .running := by
      show (execPrim (Prim.arithmetic .add rSTKH rSTKH rONE) w2).status = _; rw [g3]; exact w2s
    have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rADDR rSTK rSTKH, .store rADDR rI,
        .arithmetic .add rSTKH rSTKH rONE] w := by
      refine ⟨safe_add hW w _ _ _ ?_, w1s, ?_⟩
      · show w.regs 100 + w.regs 103 < 2 ^ W
        rw [hw100, hwsp]; omega
      refine ⟨safe_store hW w1 _ _ (by rw [w1a, hw1e]; omega) (by rw [w1i]; omega), w2s, ?_⟩
      refine ⟨safe_add hW w2 _ _ _ ?_, w3s, trivial⟩
      show w2.regs 103 + w2.regs 2 < 2 ^ W
      rw [w2reg, put_ne _ _ (by decide), put_ne _ _ (by decide), hwsp, hwo]; omega
    refine ⟨w3, 3, acts_evalG (P := Action.Safe W) _ w hwr hsafe, rfl,
      w3s, ?_, by rw [w3r, put_same], ?_, ?_, ?_, ?_⟩
    · intro a ha; simp only [w3, g3]; exact s2R a ha
    · intro r h103 h108
      rw [w3r, put_ne _ _ h103, put_ne _ _ h108]
    · intro b hb; simp only [w3, g3]; rw [s2o b hb]; simp only [w1, g1]
    · simp only [w3, g3]; rw [s2e, hw1e]
    · simp only [w3, g3]; rw [s2k]; simp [w1, g1]
  cases popped with
  | false =>
    have h0 : u.regs rPOP = 0 := by simpa using hpop
    -- LD[i] := i ; CNT[i] := 1
    let u1 := execPrim (Prim.arithmetic .add rADDR rLDB rI) u
    have f1 := exec_arithmetic u .add rADDR rLDB rI
    have u1r : u1.regs = put u.regs 108 (e0 + (n + 1 + i)) := by
      simp only [u1, f1, Arithmetic.eval]
      rw [show ((rLDB : Operand) : Nat) = 101 from rfl, show ((rI : Operand) : Nat) = 104 from rfl,
        h101, hi, show e0 + (n + 1) + i = e0 + (n + 1 + i) by omega]; rfl
    have hR1 : Region u1 e0 (3 * (n + 1)) M := by intro a ha; simp only [u1, f1]; exact hR a ha
    have u1e : u1.extent = u.extent := by simp [u1, f1]
    have u1a : u1.regs rADDR = e0 + (n + 1 + i) := by show u1.regs 108 = _; rw [u1r, put_same]
    obtain ⟨s2r, s2e, s2k, _, s2s, s2R, s2o⟩ :=
      store_region hR1 (by rw [u1e]; exact hext) rADDR rI (a := n + 1 + i) (by omega) u1a
    have u1i : u1.regs rI = i := by show u1.regs 104 = i; rw [u1r, put_ne _ _ (by decide), hi]
    rw [u1i] at s2R
    let u2 := execPrim (Prim.store rADDR rI) u1
    let u3 := execPrim (Prim.arithmetic .add rADDR rCNTB rI) u2
    have f3 := exec_arithmetic u2 .add rADDR rCNTB rI
    have u2reg : u2.regs = put u.regs 108 (e0 + (n + 1 + i)) := by rw [s2r, u1r]
    have u3r : u3.regs = put u.regs 108 (e0 + (2 * (n + 1) + i)) := by
      simp only [u3, f3, Arithmetic.eval]
      rw [show ((rCNTB : Operand) : Nat) = 102 from rfl, show ((rI : Operand) : Nat) = 104 from rfl,
        u2reg, put_ne _ _ (by decide), put_ne _ _ (by decide), h102, hi,
        show e0 + 2 * (n + 1) + i = e0 + (2 * (n + 1) + i) by omega]
      funext r; simp only [put]; by_cases h : r = 108 <;> simp [h]
    have hR3 : Region u3 e0 (3 * (n + 1)) (put M (n + 1 + i) i) := by
      intro a ha; simp only [u3, f3]; exact s2R a ha
    have u3e : u3.extent = u.extent := by simp only [u3, f3]; rw [s2e, u1e]
    have u3a : u3.regs rADDR = e0 + (2 * (n + 1) + i) := by
      show u3.regs 108 = _; rw [u3r, put_same]
    obtain ⟨s4r, s4e, s4k, _, s4s, s4R, s4o⟩ :=
      store_region hR3 (by rw [u3e]; exact hext) rADDR rONE (a := 2 * (n + 1) + i) (by omega) u3a
    have u3o : u3.regs rONE = 1 := by show u3.regs 2 = 1; rw [u3r, put_ne _ _ (by decide), hone]
    rw [u3o] at s4R
    let u4 := execPrim (Prim.store rADDR rONE) u3
    have u1s : u1.status = .running := by simp [u1, f1, hrun]
    have u2s : u2.status = .running := by rw [s2s]; exact u1s
    have u3s : u3.status = .running := by simp [u3, f3, u2s]
    have u4s : u4.status = .running := by rw [s4s]; exact u3s
    have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rADDR rLDB rI, .store rADDR rI,
        .arithmetic .add rADDR rCNTB rI, .store rADDR rONE] u := by
      refine ⟨safe_add hW u _ _ _ ?_, u1s, ?_⟩
      · show u.regs 101 + u.regs 104 < 2 ^ W
        rw [h101, hi]; omega
      refine ⟨safe_store hW u1 _ _ (by rw [u1a, u1e]; omega) (by rw [u1i]; omega), u2s, ?_⟩
      refine ⟨safe_add hW u2 _ _ _ ?_, u3s, ?_⟩
      · show u2.regs 102 + u2.regs 104 < 2 ^ W
        rw [u2reg, put_ne _ _ (by decide), put_ne _ _ (by decide), h102, hi]; omega
      exact ⟨safe_store hW u3 _ _ (by rw [u3a, u3e]; omega) (by rw [u3o]; omega), u4s, trivial⟩
    have ev1 := acts_evalG (P := Action.Safe W) _ u hrun hsafe
    have u4reg : u4.regs = put u.regs 108 (e0 + (2 * (n + 1) + i)) := by rw [s4r, u3r]
    obtain ⟨u5, j5, e5, hj5, hu5s, hu5R, hu5sp, hu5fr, hu5o, hu5e, hu5k⟩ :=
      push u4 u4s (by rw [u4reg, put_ne _ _ (by decide), hone])
        (by rw [u4reg, put_ne _ _ (by decide), h100]) (by rw [u4reg, put_ne _ _ (by decide), hi])
        (by rw [u4reg, put_ne _ _ (by decide), hsp]) _ s4R (by rw [s4e, u3e]; exact hext)
    refine ⟨u5, (4 + 1) + j5, EvalG.seq (EvalG.ifZeroTaken hrun h0 ev1) e5, by omega, hu5s, ?_,
      hu5sp, ?_, ?_, ?_, ?_⟩
    · simp only [linkPushM]
      exact hu5R
    · intro r h103 h108 _ _
      rw [hu5fr r h103 h108, u4reg, put_ne _ _ h108]
    · intro b hb
      rw [hu5o b hb, s4o b hb]
      simp only [u3, f3]
      rw [s2o b hb]
      simp only [u1, f1]
    · rw [hu5e, s4e, u3e]
    · rw [hu5k, s4k]
      show (execPrim (Prim.arithmetic .add rADDR rCNTB rI) u2).keys = u.keys
      rw [f3]
      show (execPrim (Prim.store rADDR rI) u1).keys = u.keys
      rw [s2k]
      simp [u1, f1]
  | true =>
    obtain ⟨hlastn, hldn, hcntn⟩ := hlast rfl
    generalize hlv : u.regs 106 = last at hlastn hldn hcntn ⊢
    generalize hldv : M (n + 1 + last) = ld at hldn hcntn ⊢
    have h1 : u.regs rPOP ≠ 0 := by simp at hpop; simp [hpop]
    -- TMP := LD[last]
    let u1 := execPrim (Prim.arithmetic .add rADDR rLDB rLAST) u
    have f1 := exec_arithmetic u .add rADDR rLDB rLAST
    have u1r : u1.regs = put u.regs 108 (e0 + (n + 1 + last)) := by
      simp only [u1, f1, Arithmetic.eval]
      rw [show ((rLDB : Operand) : Nat) = 101 from rfl,
        show ((rLAST : Operand) : Nat) = 106 from rfl, h101, hlv,
        show e0 + (n + 1) + last = e0 + (n + 1 + last) by omega]; rfl
    have hR1 : Region u1 e0 (3 * (n + 1)) M := by intro a ha; simp only [u1, f1]; exact hR a ha
    have u1e : u1.extent = u.extent := by simp [u1, f1]
    have u1a : u1.regs rADDR = e0 + (n + 1 + last) := by show u1.regs 108 = _; rw [u1r, put_same]
    let u2 := execPrim (Prim.load rTMP rADDR) u1
    have f2 := load_region hR1 (by rw [u1e]; exact hext) rTMP rADDR (a := n + 1 + last) (by omega) u1a
    rw [hldv] at f2
    have u2r : u2.regs = put (put u.regs 108 (e0 + (n + 1 + last))) 111 ld := by
      simp only [u2, f2, u1r]; rfl
    have hR2 : Region u2 e0 (3 * (n + 1)) M := by intro a ha; simp only [u2, f2]; exact hR1 a ha
    have u2e : u2.extent = u.extent := by simp only [u2, f2]; exact u1e
    -- ADDR := CNT base + TMP; CC := CNT[ld] + 1; store
    let u3 := execPrim (Prim.arithmetic .add rADDR rCNTB rTMP) u2
    have f3 := exec_arithmetic u2 .add rADDR rCNTB rTMP
    have u3r : u3.regs = put (put (put u.regs 108 (e0 + (n + 1 + last))) 111 ld) 108
        (e0 + (2 * (n + 1) + ld)) := by
      simp only [u3, f3, Arithmetic.eval]
      rw [show ((rCNTB : Operand) : Nat) = 102 from rfl, show ((rTMP : Operand) : Nat) = 111 from rfl,
        u2r, put_same, put_ne _ _ (by decide), put_ne _ _ (by decide), h102,
        show e0 + 2 * (n + 1) + ld = e0 + (2 * (n + 1) + ld) by omega]; rfl
    have hR3 : Region u3 e0 (3 * (n + 1)) M := by intro a ha; simp only [u3, f3]; exact hR2 a ha
    have u3e : u3.extent = u.extent := by simp only [u3, f3]; exact u2e
    have u3a : u3.regs rADDR = e0 + (2 * (n + 1) + ld) := by
      show u3.regs 108 = _; rw [u3r, put_same]
    let u4 := execPrim (Prim.load rCC rADDR) u3
    have f4 := load_region hR3 (by rw [u3e]; exact hext) rCC rADDR (a := 2 * (n + 1) + ld)
      (by omega) u3a
    have u4r : u4.regs = put u3.regs 112 (M (2 * (n + 1) + ld)) := by simp only [u4, f4]; rfl
    have hR4 : Region u4 e0 (3 * (n + 1)) M := by intro a ha; simp only [u4, f4]; exact hR3 a ha
    have u4e : u4.extent = u.extent := by simp only [u4, f4]; exact u3e
    let u5 := execPrim (Prim.arithmetic .add rCC rCC rONE) u4
    have f5 := exec_arithmetic u4 .add rCC rCC rONE
    have u4one : u4.regs 2 = 1 := by
      rw [u4r, put_ne _ _ (by decide), u3r, put_ne _ _ (by decide), put_ne _ _ (by decide),
        put_ne _ _ (by decide), hone]
    have u5r : u5.regs = put u4.regs 112 (M (2 * (n + 1) + ld) + 1) := by
      simp only [u5, f5, Arithmetic.eval]
      rw [show ((rCC : Operand) : Nat) = 112 from rfl, show ((rONE : Operand) : Nat) = 2 from rfl,
        u4one, u4r, put_same]
    have hR5 : Region u5 e0 (3 * (n + 1)) M := by intro a ha; simp only [u5, f5]; exact hR4 a ha
    have u5e : u5.extent = u.extent := by simp only [u5, f5]; exact u4e
    have u5a : u5.regs rADDR = e0 + (2 * (n + 1) + ld) := by
      show u5.regs 108 = _
      rw [u5r, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide), u3r, put_same]
    obtain ⟨s6r, s6e, s6k, _, s6s, s6R, s6o⟩ :=
      store_region hR5 (by rw [u5e]; exact hext) rADDR rCC (a := 2 * (n + 1) + ld) (by omega) u5a
    have u5cc : u5.regs rCC = M (2 * (n + 1) + ld) + 1 := by
      show u5.regs 112 = _; rw [u5r, put_same]
    rw [u5cc] at s6R
    let u6 := execPrim (Prim.store rADDR rCC) u5
    -- LD[i] := TMP
    let u7 := execPrim (Prim.arithmetic .add rADDR rLDB rI) u6
    have f7 := exec_arithmetic u6 .add rADDR rLDB rI
    have u6reg : u6.regs = put u4.regs 112 (M (2 * (n + 1) + ld) + 1) := by rw [s6r, u5r]
    have u6_101 : u6.regs 101 = e0 + (n + 1) := by
      rw [u6reg, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide), u3r, put_ne _ _ (by decide),
        put_ne _ _ (by decide), put_ne _ _ (by decide), h101]
    have u6_104 : u6.regs 104 = i := by
      rw [u6reg, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide), u3r, put_ne _ _ (by decide),
        put_ne _ _ (by decide), put_ne _ _ (by decide), hi]
    have u7r : u7.regs = put u6.regs 108 (e0 + (n + 1 + i)) := by
      simp only [u7, f7, Arithmetic.eval]
      rw [show ((rLDB : Operand) : Nat) = 101 from rfl, show ((rI : Operand) : Nat) = 104 from rfl,
        u6_101, u6_104, show e0 + (n + 1) + i = e0 + (n + 1 + i) by omega]; rfl
    have hR7 : Region u7 e0 (3 * (n + 1)) (put M (2 * (n + 1) + ld) (M (2 * (n + 1) + ld) + 1)) := by
      intro a ha; simp only [u7, f7]; exact s6R a ha
    have u7e : u7.extent = u.extent := by simp only [u7, f7]; rw [s6e, u5e]
    have u7a : u7.regs rADDR = e0 + (n + 1 + i) := by show u7.regs 108 = _; rw [u7r, put_same]
    obtain ⟨s8r, s8e, s8k, _, s8s, s8R, s8o⟩ :=
      store_region hR7 (by rw [u7e]; exact hext) rADDR rTMP (a := n + 1 + i) (by omega) u7a
    have u7tmp : u7.regs rTMP = ld := by
      show u7.regs 111 = ld
      rw [u7r, put_ne _ _ (by decide), u6reg, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide),
        u3r, put_ne _ _ (by decide), put_same]
    rw [u7tmp] at s8R
    let u8 := execPrim (Prim.store rADDR rTMP) u7
    have u1s : u1.status = .running := by simp [u1, f1, hrun]
    have u2s : u2.status = .running := by simp only [u2, f2]; exact u1s
    have u3s : u3.status = .running := by simp [u3, f3, u2s]
    have u4s : u4.status = .running := by simp only [u4, f4]; exact u3s
    have u5s : u5.status = .running := by simp [u5, f5, u4s]
    have u6s : u6.status = .running := by rw [s6s]; exact u5s
    have u7s : u7.status = .running := by simp [u7, f7, u6s]
    have u8s : u8.status = .running := by rw [s8s]; exact u7s
    have hsafe : ActsOK (Action.Safe W) [.arithmetic .add rADDR rLDB rLAST, .load rTMP rADDR,
        .arithmetic .add rADDR rCNTB rTMP, .load rCC rADDR, .arithmetic .add rCC rCC rONE,
        .store rADDR rCC, .arithmetic .add rADDR rLDB rI, .store rADDR rTMP] u := by
      refine ⟨safe_add hW u _ _ _ ?_, u1s, ?_⟩
      · show u.regs 101 + u.regs 106 < 2 ^ W
        rw [h101, hlv]; omega
      refine ⟨safe_load_region hW hR1 (by rw [u1e]; exact hext) _ _ (by omega) u1a
        (by rw [hldv]; omega), u2s, ?_⟩
      refine ⟨safe_add hW u2 _ _ _ ?_, u3s, ?_⟩
      · show u2.regs 102 + u2.regs 111 < 2 ^ W
        rw [u2r, put_same, put_ne _ _ (by decide), put_ne _ _ (by decide), h102]; omega
      refine ⟨safe_load_region hW hR3 (by rw [u3e]; exact hext) _ _ (by omega) u3a
        (by omega), u4s, ?_⟩
      refine ⟨safe_add hW u4 _ _ _ ?_, u5s, ?_⟩
      · show u4.regs 112 + u4.regs 2 < 2 ^ W
        rw [u4one, u4r, put_same]; omega
      refine ⟨safe_store hW u5 _ _ (by rw [u5a, u5e]; omega) (by rw [u5cc]; omega), u6s, ?_⟩
      refine ⟨safe_add hW u6 _ _ _ ?_, u7s, ?_⟩
      · show u6.regs 101 + u6.regs 104 < 2 ^ W
        rw [u6_101, u6_104]; omega
      exact ⟨safe_store hW u7 _ _ (by rw [u7a, u7e]; omega) (by rw [u7tmp]; omega), u8s, trivial⟩
    have ev1 := acts_evalG (P := Action.Safe W) _ u hrun hsafe
    have u8reg : u8.regs = put u6.regs 108 (e0 + (n + 1 + i)) := by rw [s8r, u7r]
    have u8_2 : u8.regs 2 = 1 := by
      rw [u8reg, put_ne _ _ (by decide), u6reg, put_ne _ _ (by decide), u4one]
    have u8_100 : u8.regs 100 = e0 := by
      rw [u8reg, put_ne _ _ (by decide), u6reg, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide),
        u3r, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), h100]
    have u8_104 : u8.regs 104 = i := by rw [u8reg, put_ne _ _ (by decide), u6_104]
    have u8_103 : u8.regs 103 = sp := by
      rw [u8reg, put_ne _ _ (by decide), u6reg, put_ne _ _ (by decide), u4r, put_ne _ _ (by decide),
        u3r, put_ne _ _ (by decide), put_ne _ _ (by decide), put_ne _ _ (by decide), hsp]
    obtain ⟨u9, j9, e9, hj9, hu9s, hu9R, hu9sp, hu9fr, hu9o, hu9e, hu9k⟩ :=
      push u8 u8s u8_2 u8_100 u8_104 u8_103 _ s8R (by rw [s8e, u7e]; exact hext)
    refine ⟨u9, (8 + 2) + j9, EvalG.seq (EvalG.ifZeroFallthrough hrun h1 ev1 u8s) e9, by omega,
      hu9s, ?_, hu9sp, ?_, ?_, ?_, ?_⟩
    · simp only [linkPushM, if_true]
      exact hu9R
    · intro r h103 h108 h111 h112
      rw [hu9fr r h103 h108, u8reg, put_ne _ _ h108, u6reg, put_ne _ _ h112, u4r,
        put_ne _ _ h112, u3r, put_ne _ _ h108, put_ne _ _ h111, put_ne _ _ h108]
    · intro b hb
      rw [hu9o b hb, s8o b hb]
      simp only [u7, f7]
      rw [s6o b hb]
      simp only [u5, f5, u4, f4, u3, f3, u2, f2, u1, f1]
    · rw [hu9e, s8e, u7e]
    · rw [hu9k, s8k]
      simp only [u7, f7]
      rw [s6k]
      simp [u5, f5, u4, f4, u3, f3, u2, f2, u1, f1]

end RMQ.SuccinctFinal.PackedConstruction.Proof

import RMQ.Core.WordRAM.Construction.Proof.SummaryTables
import RMQ.Core.WordRAM.Construction.Spec.SparseMemo

/-! # PRE-1 builder proofs: the sparse memos (stage S4)

Outside the builder firewall. `localMemoBlock` fills the local memo row by row,
`A[l][b] = bpRangeArgMinBlock b (2 ^ l)`, and `globalMemoBlock` fills the
global memo at macro granularity, `G[l][m] = bpRangeArgMinBlock (m * M)
(2 ^ l * M)`, on every index whose range lies inside the covered blocks. Block
selection compares the stored block minima, which equal the reference keys by
`Spec.better_eq_min`.

Straight-line action lists with loads and stores are evaluated through
`ActsPrefix`, which composes single-action steps into the right-nested `acts`
of any concatenation.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose

/-! ## Prefix evaluation of action lists -/

/-- `ops` evaluates safely from `s` to the running state `t` in `k` steps, as a
prefix of any action list. -/
def ActsPrefix (W : Nat) (ops : List Action) (s t : State) (k : Nat) : Prop :=
  t.status = .running ∧ ∀ (rest : List Action) (t' : State) (k' : Nat),
    SafeEval W (acts rest) t t' k' → SafeEval W (acts (ops ++ rest)) s t' (k + k')

theorem acts_cons_safe {W : Nat} {a : Action} {s t t' : State} {k : Nat} (rest : List Action)
    (h1 : SafeEval W (.action a) s t 1) (h2 : SafeEval W (acts rest) t t' k) :
    SafeEval W (acts (a :: rest)) s t' (1 + k) := by
  cases rest with
  | nil =>
      change SafeEval W .skip t t' k at h2
      cases h2 with
      | stopped _ _ _ => exact h1
      | skip _ _ => exact h1
  | cons b rest => exact EvalG.seq h1 h2

theorem ActsPrefix.cons {W : Nat} {a : Action} {ops : List Action} {s t u : State} {k : Nat}
    (h1 : SafeEval W (.action a) s t 1) (h2 : ActsPrefix W ops t u k) :
    ActsPrefix W (a :: ops) s u (1 + k) :=
  ⟨h2.1, fun rest t' k' e => by
    rw [Nat.add_assoc]
    exact acts_cons_safe (ops ++ rest) h1 (h2.2 rest t' k' e)⟩

theorem ActsPrefix.append {W : Nat} {ops₁ ops₂ : List Action} {s t u : State} {k₁ k₂ : Nat}
    (h₁ : ActsPrefix W ops₁ s t k₁) (h₂ : ActsPrefix W ops₂ t u k₂) :
    ActsPrefix W (ops₁ ++ ops₂) s u (k₁ + k₂) :=
  ⟨h₂.1, fun rest t' k' e => by
    rw [List.append_assoc, Nat.add_assoc]
    exact h₁.2 (ops₂ ++ rest) t' (k₂ + k') (h₂.2 rest t' k' e)⟩

theorem ActsPrefix.close {W : Nat} {ops : List Action} {s t : State} {k : Nat}
    (h : ActsPrefix W ops s t k) : SafeEval W (acts ops) s t k := by
  have e := h.2 [] t 0 (EvalG.skip t h.1)
  rw [List.append_nil, Nat.add_zero] at e
  exact e

/-- One register-only action as a prefix step. -/
theorem prefix_pure {W : Nat} (hW : 32 ≤ W) (a : Action) (v : State) (hrun : v.status = .running)
    (h : pureOK W a v.regs) :
    ∃ v', ActsPrefix W [a] v v' 1 ∧ v'.regs = pureReg a v.regs ∧
      v'.memory = v.memory ∧ v'.extent = v.extent ∧ v'.keys = v.keys ∧
      v'.keyRegs = v.keyRegs := by
  obtain ⟨v', e, hr, hR, hm, he, hk, hkr⟩ := step_pure hW a v hrun h
  refine ⟨v', ⟨hr, fun rest t' k' e' => ?_⟩, hR, hm, he, hk, hkr⟩
  exact acts_cons_safe rest e e'

/-- One load as a prefix step. -/
theorem prefix_load {W : Nat} (hW : 32 ≤ W) (d addr : Operand) (v : State)
    (hrun : v.status = .running) {x : Nat} (ha : v.regs addr < v.extent)
    (hm : v.memory (v.regs addr) = some x) (hx : x < 2 ^ W) :
    ∃ v', ActsPrefix W [.load d addr] v v' 1 ∧ v'.regs = put v.regs d x ∧
      v'.memory = v.memory ∧ v'.extent = v.extent ∧ v'.keys = v.keys ∧
      v'.keyRegs = v.keyRegs := by
  obtain ⟨v', e, hr, hR, hm', he, hk, hkr⟩ := step_load hW d addr v hrun ha hm hx
  refine ⟨v', ⟨hr, fun rest t' k' e' => ?_⟩, hR, hm', he, hk, hkr⟩
  exact acts_cons_safe rest e e'

/-- One store below the extent as a prefix step. -/
theorem prefix_store {W : Nat} (hW : 32 ≤ W) (addr src : Operand) (v : State)
    (hrun : v.status = .running) (ha : v.regs addr < v.extent) (hv : v.regs src < 2 ^ W) :
    ∃ v', ActsPrefix W [.store addr src] v v' 1 ∧ v'.regs = v.regs ∧
      v'.memory = put v.memory (v.regs addr) (some (v.regs src)) ∧ v'.extent = v.extent ∧
      v'.keys = v.keys ∧ v'.keyRegs = v.keyRegs := by
  have e := EvalG.action (P := Action.Safe W) (.store addr src) v hrun (safe_store hW v _ _ ha hv)
  rw [show execPrim (Action.store addr src).prim v = _ from exec_store v addr src ha] at e
  exact ⟨{ v with memory := put v.memory (v.regs addr) (some (v.regs src)), pc := v.pc + 1 },
    ⟨hrun, fun rest t' k' e' => acts_cons_safe rest e e'⟩, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Block selection -/

theorem covered_block {bs bc b : Nat} (len : Nat) (hb : b < bc) (hcover : bc * bs ≤ len) :
    b * bs + bs ≤ len := by
  have := Nat.mul_le_mul_right bs (show b + 1 ≤ bc from hb)
  rw [Nat.succ_mul] at this
  omega

/-- **Leftmost-better selection by stored minima.** -/
theorem betterActs_prefix {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (dst x y : Operand)
    (hx108 : (x : Nat) ≠ 108) (hx144 : (x : Nat) ≠ 144) (hx145 : (x : Nat) ≠ 145)
    (hx146 : (x : Nat) ≠ 146) (hx147 : (x : Nat) ≠ 147)
    (hy108 : (y : Nat) ≠ 108) (hy144 : (y : Nat) ≠ 144) (hy145 : (y : Nat) ≠ 145)
    (hy146 : (y : Nat) ≠ 146) (hy147 : (y : Nat) ≠ 147)
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc X Y : Nat) (h116 : u.regs 116 = A1) (hX : u.regs x = X) (hY : u.regs y = Y)
    (hXbc : X < bc) (hYbc : Y < bc) (hA : A1 + bc ≤ u.extent) (hAW : A1 + bc < 2 ^ W)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) :
    ∃ u', ActsPrefix W (betterActs dst x y) u u' 9 ∧
      u'.regs dst = bpBetterArgMinBlock shape bs X Y ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 144 → r ≠ 145 → r ≠ 146 → r ≠ 147 → r ≠ dst →
        u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧
      u'.keyRegs = u.keyRegs := by
  have hmX := bpBlockMinExcess_le_length shape bs X
  have hmY := bpBlockMinExcess_le_length shape bs Y
  -- rADDR := MIN + x; KX := load
  obtain ⟨v1, p1, r1, m1, e1, k1, kr1⟩ :=
    prefix_pure hW (.arithmetic .add rADDR rMINB x) u hrun (by
      simp only [pureOK, Arithmetic.eval, operand_val_116, h116, hX, reduceCtorEq, false_implies,
        false_or, and_true]; omega)
  have v1r : v1.regs = put u.regs 108 (A1 + X) := by
    rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_116, h116, hX]
  obtain ⟨v2, p2, r2, m2, e2, k2, kr2⟩ :=
    prefix_load hW rKX rADDR v1 p1.1 (x := bpBlockMinExcess shape bs X)
      (by show v1.regs 108 < v1.extent; rw [v1r, put_same, e1]; omega)
      (by show v1.memory (v1.regs 108) = _; rw [v1r, put_same, m1]; exact hmin X hXbc)
      (by omega)
  have v2r : v2.regs = put (put u.regs 108 (A1 + X)) 144 (bpBlockMinExcess shape bs X) := by
    rw [r2, v1r]; rfl
  -- rADDR := MIN + y; KY := load
  obtain ⟨v3, p3, r3, m3, e3, k3, kr3⟩ :=
    prefix_pure hW (.arithmetic .add rADDR rMINB y) v2 p2.1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_116, v2r, put_ne _ _ (show (116 : Nat) ≠ 144 by decide),
        put_ne _ _ (show (116 : Nat) ≠ 108 by decide), put_ne _ _ hy144, put_ne _ _ hy108, h116, hY,
        reduceCtorEq, false_implies, false_or, and_true]; omega)
  have v3r : v3.regs = put (put (put u.regs 108 (A1 + X)) 144 (bpBlockMinExcess shape bs X))
      108 (A1 + Y) := by
    rw [r3, v2r]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_116,
      put_ne _ _ (show (116 : Nat) ≠ 144 by decide), put_ne _ _ (show (116 : Nat) ≠ 108 by decide),
      put_ne _ _ hy144, put_ne _ _ hy108, h116, hY]
  obtain ⟨v4, p4, r4, m4, e4, k4, kr4⟩ :=
    prefix_load hW rKY rADDR v3 p3.1 (x := bpBlockMinExcess shape bs Y)
      (by show v3.regs 108 < v3.extent; rw [v3r, put_same, e3, e2, e1]; omega)
      (by show v3.memory (v3.regs 108) = _; rw [v3r, put_same, m3, m2, m1]; exact hmin Y hYbc)
      (by omega)
  have v4_144 : v4.regs 144 = bpBlockMinExcess shape bs X := by
    rw [r4, operand_val_145, put_ne _ _ (by decide), v3r, put_ne _ _ (by decide), put_same]
  have v4_145 : v4.regs 145 = bpBlockMinExcess shape bs Y := by
    rw [r4, operand_val_145, put_same]
  have v4x : v4.regs x = X := by
    rw [r4, operand_val_145, put_ne _ _ hx145, v3r, put_ne _ _ hx108, put_ne _ _ hx144,
      put_ne _ _ hx108, hX]
  have v4y : v4.regs y = Y := by
    rw [r4, operand_val_145, put_ne _ _ hy145, v3r, put_ne _ _ hy108, put_ne _ _ hy144,
      put_ne _ _ hy108, hY]
  have v4_2 : v4.regs 2 = 1 := by
    rw [r4, operand_val_145, put_ne _ _ (by decide), v3r, put_ne _ _ (by decide),
      put_ne _ _ (by decide), put_ne _ _ (by decide), hone]
  -- c := [KY < KX]; T7 := 1 - c; T6 := c * y; T7 := T7 * x; dst := T6 + T7
  let c := if bpBlockMinExcess shape bs Y < bpBlockMinExcess shape bs X then 1 else 0
  have hc1 : c ≤ 1 := by show (if _ then 1 else 0) ≤ 1; split <;> omega
  obtain ⟨v5, p5, r5, m5, e5, k5, kr5⟩ :=
    prefix_pure hW (.comparison .lt rT6 rKY rKX) v4 p4.1 trivial
  have v5r : v5.regs = put v4.regs 146 c := by
    rw [r5]; simp only [pureReg, Comparison.eval, operand_val_146, operand_val_145, operand_val_144,
      v4_144, v4_145]; rfl
  have v5_146 : v5.regs 146 = c := by rw [v5r, put_same]
  have v5_2 : v5.regs 2 = 1 := by rw [v5r, put_ne _ _ (by decide), v4_2]
  obtain ⟨v6, p6, r6, m6, e6, k6, kr6⟩ :=
    prefix_pure hW (.arithmetic .sub rT7 rONE rT6) v5 p5.1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_2, operand_val_146, v5_146, v5_2,
        reduceCtorEq, false_implies, false_or, and_true, forall_const]
      omega)
  have v6r : v6.regs = put v5.regs 147 (1 - c) := by
    rw [r6]; simp only [pureReg, Arithmetic.eval, operand_val_147, operand_val_2, operand_val_146,
      v5_146, v5_2]
  have v6_146 : v6.regs 146 = c := by rw [v6r, put_ne _ _ (by decide), v5_146]
  have v6y : v6.regs y = Y := by
    rw [v6r, put_ne _ _ hy147, v5r, put_ne _ _ hy146, v4y]
  have hYW : Y < 2 ^ W := by omega
  have hXW : X < 2 ^ W := by omega
  obtain ⟨v7, p7, r7, m7, e7, k7, kr7⟩ :=
    prefix_pure hW (.arithmetic .mul rT6 rT6 y) v6 p6.1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_146, v6_146, v6y, reduceCtorEq,
        false_implies, false_or, and_true]
      have : c * Y ≤ Y := Nat.le_trans (Nat.mul_le_mul_right Y hc1) (by omega)
      omega)
  have v7r : v7.regs = put v6.regs 146 (c * Y) := by
    rw [r7]; simp only [pureReg, Arithmetic.eval, operand_val_146, v6_146, v6y]
  have v7_147 : v7.regs 147 = 1 - c := by
    rw [v7r, put_ne _ _ (by decide), v6r, put_same]
  have v7x : v7.regs x = X := by
    rw [v7r, put_ne _ _ hx146, v6r, put_ne _ _ hx147, v5r, put_ne _ _ hx146, v4x]
  obtain ⟨v8, p8, r8, m8, e8, k8, kr8⟩ :=
    prefix_pure hW (.arithmetic .mul rT7 rT7 x) v7 p7.1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_147, v7_147, v7x, reduceCtorEq,
        false_implies, false_or, and_true]
      have : (1 - c) * X ≤ X := Nat.le_trans (Nat.mul_le_mul_right X (Nat.sub_le 1 c)) (by omega)
      omega)
  have v8_146 : v8.regs 146 = c * Y := by
    rw [r8]; simp only [pureReg, Arithmetic.eval, operand_val_147, v7_147, v7x]
    rw [put_ne _ _ (by decide), v7r, put_same]
  have v8_147 : v8.regs 147 = (1 - c) * X := by
    rw [r8]; simp only [pureReg, Arithmetic.eval, operand_val_147, v7_147, v7x, put_same]
  have hsel : c * Y + (1 - c) * X = bpBetterArgMinBlock shape bs X Y := by
    rw [better_eq_min shape bs X Y (covered_block _ hXbc hcover) (covered_block _ hYbc hcover)]
    show (if _ then 1 else 0) * Y + (1 - if _ then 1 else 0) * X = _
    split <;> simp
  obtain ⟨v9, p9, r9, m9, e9, k9, kr9⟩ :=
    prefix_pure hW (.arithmetic .add dst rT6 rT7) v8 p8.1 (by
      simp only [pureOK, Arithmetic.eval, operand_val_146, operand_val_147, v8_146, v8_147,
        reduceCtorEq, false_implies, false_or, and_true]
      rw [hsel]
      have := (bpRangeArgMinBlock_mem shape bs X 1 (by decide)).2
      simp only [bpBetterArgMinBlock]; split <;> omega)
  have v9dst : v9.regs dst = c * Y + (1 - c) * X := by
    rw [r9]; simp only [pureReg, Arithmetic.eval, operand_val_146, operand_val_147, v8_146, v8_147,
      put_same]
  refine ⟨v9, p1.append (p2.append (p3.append (p4.append (p5.append (p6.append (p7.append
    (p8.append p9))))))), by rw [v9dst, hsel], ?_, ?_, ?_, ?_, ?_⟩
  · intro r h108 h144 h145 h146 h147 hdst
    rw [r9]; simp only [pureReg]
    rw [put_ne _ _ hdst, r8]; simp only [pureReg, operand_val_147]
    rw [put_ne _ _ h147, v7r, put_ne _ _ h146, v6r, put_ne _ _ h147, v5r, put_ne _ _ h146, r4,
      operand_val_145, put_ne _ _ h145, v3r, put_ne _ _ h108, put_ne _ _ h144, put_ne _ _ h108]
  · rw [m9, m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [e9, e8, e7, e6, e5, e4, e3, e2, e1]
  · rw [k9, k8, k7, k6, k5, k4, k3, k2, k1]
  · rw [kr9, kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1]

/-! ## One memo cell -/

/-- **One memo cell.** If the doubled range at index `i` lies inside the covered
blocks, the cell `C + i` of the current row receives the better of the two
previous-row cells `P + i` and `P + (i + h)`; otherwise memory is unchanged. -/
theorem memoCell_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (scale : Operand)
    (hs146 : (scale : Nat) ≠ 146)
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc S i h P C VX VY : Nat) (h116 : u.regs 116 = A1) (h32 : u.regs 32 = bc)
    (hS : u.regs scale = S) (hS1 : 1 ≤ S) (h139 : u.regs 139 = i) (h141 : u.regs 141 = h)
    (h149 : u.regs 149 = P) (h150 : u.regs 150 = C)
    (hcapG : (i + h + h) * S < 2 ^ W)
    (hA : A1 + bc ≤ u.extent) (hAW : A1 + bc < 2 ^ W)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (hcell : (i + h + h) * S ≤ bc →
      u.memory (P + i) = some VX ∧ u.memory (P + (i + h)) = some VY ∧ VX < bc ∧ VY < bc ∧
        P + (i + h) < u.extent ∧ C + i < u.extent ∧ C + i < 2 ^ W ∧ P + (i + h) < 2 ^ W) :
    ∃ u' j, SafeEval W (memoCellBlock scale) u u' j ∧ j ≤ 22 ∧ u'.status = .running ∧
      u'.memory = (if (i + h + h) * S ≤ bc then
        put u.memory (C + i) (some (bpBetterArgMinBlock shape bs VX VY)) else u.memory) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hh : i + h + h ≤ (i + h + h) * S := Nat.le_mul_of_pos_right _ hS1
  -- guard
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.arithmetic .add rT6 rMB rSPN, .arithmetic .add rT6 rT6 rSPN,
      .arithmetic .mul rT6 rT6 scale, .comparison .lt rT7 rBLOCKS rT6] u hrun (by
        simp only [pureOKs, pureOK, pureReg, Arithmetic.eval, put, operand_val_146,
          operand_val_139, operand_val_141, h139, h141,
          reduceCtorEq, false_implies, false_or, and_true,
          Nat.reduceEqDiff, ↓reduceIte, hs146, hS]
        refine ⟨?_, ?_, ?_⟩ <;> omega)
  have tR : ∀ r, t.regs r = if r = 147 then (if bc < (i + h + h) * S then 1 else 0) else
      if r = 146 then (i + h + h) * S else u.regs r := by
    intro r; rw [htR]
    simp only [pureRegs, pureReg, Arithmetic.eval, Comparison.eval, put, operand_val_146,
      operand_val_139, operand_val_141, operand_val_147, operand_val_32, h139, h141,
      Nat.reduceEqDiff, ↓reduceIte, hs146, hS, h32]
    by_cases h147 : r = 147
    · simp [h147]
    · by_cases h146 : r = 146
      · simp [h146]
      · simp [h147, h146]
  have tfr : ∀ r, r ≠ 146 → r ≠ 147 → t.regs r = u.regs r := fun r h1 h2 => by
    rw [tR, if_neg h2, if_neg h1]
  by_cases hv : (i + h + h) * S ≤ bc
  · obtain ⟨mX, mY, hVX, hVY, hPe, hCe, hCW, hPW⟩ := hcell hv
    have hc : t.regs rT7 = 0 := by
      show t.regs 147 = 0; rw [tR, if_pos rfl, if_neg (by omega)]
    have t2 : t.regs 2 = 1 := by rw [tfr 2 (by decide) (by decide), hone]
    have t139 : t.regs 139 = i := by rw [tfr 139 (by decide) (by decide), h139]
    have t141 : t.regs 141 = h := by rw [tfr 141 (by decide) (by decide), h141]
    have t149 : t.regs 149 = P := by rw [tfr 149 (by decide) (by decide), h149]
    -- rADDR := P + i; CX := load
    obtain ⟨w1, p1, r1, m1, e1, k1, kr1⟩ :=
      prefix_pure hW (.arithmetic .add rADDR rROWP rMB) t htr (by
        simp only [pureOK, Arithmetic.eval, operand_val_149, operand_val_139, t149, t139,
          reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w1r : w1.regs = put t.regs 108 (P + i) := by
      rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_149,
        operand_val_139, t149, t139]
    obtain ⟨w2, p2, r2, m2, e2, k2, kr2⟩ :=
      prefix_load hW rCX rADDR w1 p1.1 (x := VX)
        (by show w1.regs 108 < w1.extent; rw [w1r, put_same, e1, hte]; omega)
        (by show w1.memory (w1.regs 108) = _; rw [w1r, put_same, m1, htm]; exact mX)
        (by omega)
    have w2r : w2.regs = put (put t.regs 108 (P + i)) 142 VX := by rw [r2, w1r]; rfl
    -- T6 := i + h; rADDR := P + T6; CY := load
    obtain ⟨w3, p3, r3, m3, e3, k3, kr3⟩ :=
      prefix_pure hW (.arithmetic .add rT6 rMB rSPN) w2 p2.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_139, operand_val_141, w2r,
          put_ne _ _ (show (139 : Nat) ≠ 142 by decide), put_ne _ _ (show (139 : Nat) ≠ 108 by decide),
          put_ne _ _ (show (141 : Nat) ≠ 142 by decide), put_ne _ _ (show (141 : Nat) ≠ 108 by decide),
          t139, t141, reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w3r : w3.regs = put (put (put t.regs 108 (P + i)) 142 VX) 146 (i + h) := by
      rw [r3, w2r]; simp only [pureReg, Arithmetic.eval, operand_val_146, operand_val_139,
        operand_val_141, put_ne _ _ (show (139 : Nat) ≠ 142 by decide),
        put_ne _ _ (show (139 : Nat) ≠ 108 by decide), put_ne _ _ (show (141 : Nat) ≠ 142 by decide),
        put_ne _ _ (show (141 : Nat) ≠ 108 by decide), t139, t141]
    obtain ⟨w4, p4, r4, m4, e4, k4, kr4⟩ :=
      prefix_pure hW (.arithmetic .add rADDR rROWP rT6) w3 p3.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_149, operand_val_146, w3r, put_same,
          put_ne _ _ (show (149 : Nat) ≠ 146 by decide), put_ne _ _ (show (149 : Nat) ≠ 142 by decide),
          put_ne _ _ (show (149 : Nat) ≠ 108 by decide), t149, reduceCtorEq, false_implies,
          false_or, and_true]; omega)
    have w4r : w4.regs = put (put (put (put t.regs 108 (P + i)) 142 VX) 146 (i + h)) 108
        (P + (i + h)) := by
      rw [r4, w3r]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_149,
        operand_val_146, put_same, put_ne _ _ (show (149 : Nat) ≠ 146 by decide),
        put_ne _ _ (show (149 : Nat) ≠ 142 by decide), put_ne _ _ (show (149 : Nat) ≠ 108 by decide),
        t149]
    obtain ⟨w5, p5, r5, m5, e5, k5, kr5⟩ :=
      prefix_load hW rCY rADDR w4 p4.1 (x := VY)
        (by show w4.regs 108 < w4.extent; rw [w4r, put_same, e4, e3, e2, e1, hte]; omega)
        (by show w4.memory (w4.regs 108) = _; rw [w4r, put_same, m4, m3, m2, m1, htm]; exact mY)
        (by omega)
    have w5r : w5.regs = put w4.regs 143 VY := by rw [r5]; rfl
    have w5get : ∀ r, r ≠ 108 → r ≠ 142 → r ≠ 143 → r ≠ 146 → w5.regs r = t.regs r :=
      fun r a b c d => by
        rw [w5r, put_ne _ _ c, w4r, put_ne _ _ a, put_ne _ _ d, put_ne _ _ b, put_ne _ _ a]
    -- better
    obtain ⟨w6, p6, r6, fr6, m6, e6, k6, kr6⟩ :=
      betterActs_prefix hW shape rCX rCX rCY (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w5 p5.1
        (by rw [w5get 2 (by decide) (by decide) (by decide) (by decide), t2]) A1 bs bc VX VY
        (by rw [w5get 116 (by decide) (by decide) (by decide) (by decide),
          tfr 116 (by decide) (by decide), h116])
        (by show w5.regs 142 = VX
            rw [w5r, put_ne _ _ (by decide), w4r, put_ne _ _ (by decide), put_ne _ _ (by decide),
              put_same])
        (by show w5.regs 143 = VY; rw [w5r, put_same])
        hVX hVY (by rw [e5, e4, e3, e2, e1, hte]; exact hA) hAW hcover hlenW
        (fun b hb => by rw [m5, m4, m3, m2, m1, htm]; exact hmin b hb)
    have w6get : ∀ r, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → w6.regs r = t.regs r := fun r a b => by
      rw [fr6 r a (by omega) (by omega) (by omega) (by omega) (by simp; omega),
        w5get r a (by omega) (by omega) (by omega)]
    -- rADDR := C + i; store
    obtain ⟨w7, p7, r7, m7, e7, k7, kr7⟩ :=
      prefix_pure hW (.arithmetic .add rADDR rROWC rMB) w6 p6.1 (by
        simp only [pureOK, Arithmetic.eval, operand_val_150, operand_val_139,
          w6get 150 (by decide) (by decide), w6get 139 (by decide) (by decide),
          tfr 150 (by decide) (by decide), tfr 139 (by decide) (by decide), h150, h139,
          reduceCtorEq, false_implies, false_or, and_true]; omega)
    have w7r : w7.regs = put w6.regs 108 (C + i) := by
      rw [r7]; simp only [pureReg, Arithmetic.eval, operand_val_108, operand_val_150, operand_val_139,
        w6get 150 (by decide) (by decide), w6get 139 (by decide) (by decide),
        tfr 150 (by decide) (by decide), tfr 139 (by decide) (by decide), h150, h139]
    have w7_142 : w7.regs 142 = bpBetterArgMinBlock shape bs VX VY := by
      rw [w7r, put_ne _ _ (by decide)]; exact r6
    have hbW : bpBetterArgMinBlock shape bs VX VY < 2 ^ W := by
      unfold bpBetterArgMinBlock; split <;> omega
    obtain ⟨w8, p8, r8, m8, e8, k8, kr8⟩ :=
      prefix_store hW rADDR rCX w7 p7.1
        (by show w7.regs 108 < w7.extent; rw [w7r, put_same, e7, e6, e5, e4, e3, e2, e1, hte]; exact hCe)
        (by show w7.regs 142 < 2 ^ W; rw [w7_142]; exact hbW)
    have pre := p1.append (p2.append (p3.append (p4.append (p5.append (p6.append
      (p7.append p8))))))
    refine ⟨w8, jt + ((1 + (1 + (1 + (1 + (1 + (9 + (1 + 1))))))) + 1),
      EvalG.seq et (EvalG.ifZeroTaken htr hc pre.close), by simp at hjt; omega, p8.1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos hv, m8, m7, m6, m5, m4, m3, m2, m1, htm]
      show put u.memory (w7.regs 108) (some (w7.regs 142)) = _
      rw [w7_142, w7r, put_same]
    · intro r h108 hr
      rw [r8, w7r, put_ne _ _ h108, w6get r h108 hr, tfr r (by omega) (by omega)]
    · rw [e8, e7, e6, e5, e4, e3, e2, e1, hte]
    · rw [k8, k7, k6, k5, k4, k3, k2, k1, htk]
    · rw [kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1, htkr]
  · have hc : t.regs rT7 ≠ 0 := by
      show t.regs 147 ≠ 0; rw [tR, if_pos rfl, if_pos (by omega)]; decide
    refine ⟨t, jt + (0 + 2), EvalG.seq et (EvalG.ifZeroFallthrough htr hc (EvalG.skip t htr) htr),
      by simp at hjt; omega, htr, by rw [if_neg hv, htm], ?_, hte, htk, htkr⟩
    intro r h108 hr
    exact tfr r (by omega) (by omega)

/-! ## Memo rows -/

theorem row_addr_ne {N l l' i j : Nat} (hi : i < N) (hj : j < N) (hne : l ≠ l' ∨ i ≠ j) :
    l * N + i ≠ l' * N + j := by
  intro h
  have hN : 0 < N := by omega
  have hd : (l * N + i) / N = (l' * N + j) / N := by rw [h]
  have hm : (l * N + i) % N = (l' * N + j) % N := by rw [h]
  rw [Nat.add_comm (l * N), Nat.add_comm (l' * N), Nat.add_mul_div_right _ _ hN,
    Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj] at hd
  rw [Nat.add_comm (l * N), Nat.add_comm (l' * N), Nat.add_mul_mod_self_right,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  omega

theorem row_lt {N l L i : Nat} (hi : i < N) (hl : l < L) : l * N + i < L * N := by
  have := Nat.mul_le_mul_right N (show l + 1 ≤ L from hl)
  rw [Nat.succ_mul] at this
  omega

theorem row_ge {N l i : Nat} (hl : 1 ≤ l) : N ≤ l * N + i := by
  have := Nat.mul_le_mul_right N hl
  rw [Nat.one_mul] at this
  omega

/-- **Memo levels.** From row 0 of a memo with rows of `N` cells at `Bm`, the
level loop fills rows `1 .. Lv - 1` by the doubling law `hV` on every index
whose range lies inside the covered blocks. -/
theorem memoLevels_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape)
    (base count scale levels : Operand)
    (hbase : (base : Nat) ≠ 108 ∧ ¬ (137 ≤ (base : Nat) ∧ (base : Nat) ≤ 150))
    (hcount : (count : Nat) ≠ 108 ∧ ¬ (137 ≤ (count : Nat) ∧ (count : Nat) ≤ 150) ∧ (count : Nat) ≠ 2)
    (hscale : (scale : Nat) ≠ 108 ∧ ¬ (137 ≤ (scale : Nat) ∧ (scale : Nat) ≤ 150))
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc Bm N S Lv : Nat) (V : Nat → Nat → Nat)
    (h116 : u.regs 116 = A1) (h32 : u.regs 32 = bc) (hB : u.regs base = Bm)
    (hN : u.regs count = N) (hS : u.regs scale = S) (hL : u.regs levels = Lv)
    (hS1 : 1 ≤ S) (hL1 : 1 ≤ Lv) (hLW : Lv < W)
    (hcap : Bm + Lv * N + (N + 2 ^ Lv) * S < 2 ^ W)
    (hext : Bm + Lv * N ≤ u.extent) (hA : A1 + bc ≤ Bm)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (hV : ∀ l i, (i + 2 ^ (l + 1)) * S ≤ bc →
      V (l + 1) i = bpBetterArgMinBlock shape bs (V l i) (V l (i + 2 ^ l)))
    (hVlt : ∀ l i, (i + 2 ^ l) * S ≤ bc → V l i < bc)
    (hNi : ∀ l i, (i + 2 ^ l) * S ≤ bc → i < N)
    (hrow0 : ∀ i, (i + 1) * S ≤ bc → u.memory (Bm + i) = some (V 0 i)) :
    ∃ u' j, SafeEval W (memoLevelsBlock base count scale levels) u u' j ∧
      j ≤ Lv * (26 * N + 11) + 4 ∧ u'.status = .running ∧
      (∀ l i, l < Lv → (i + 2 ^ l) * S ≤ bc → u'.memory (Bm + l * N + i) = some (V l i)) ∧
      (∀ a, (a < Bm + N ∨ Bm + Lv * N ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 150) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have h2L : 2 ^ Lv < 2 ^ W := Nat.pow_lt_pow_right (by decide) hLW
  have hNS : N ≤ (N + 2 ^ Lv) * S := Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ hS1)
  have hAW : A1 + bc < 2 ^ W := by omega
  have hLp : Lv < 2 ^ Lv := Nat.lt_two_pow_self
  -- level count
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.arithmetic .sub rLVCNT levels rONE] u hrun (by
      simp only [pureOKs, pureOK, Arithmetic.eval, operand_val_2, hone, hL, and_true,
        reduceCtorEq, false_or, false_implies, forall_const]
      omega)
  have tfr : ∀ r, r ≠ 148 → t.regs r = u.regs r := fun r h => by
    rw [htR]; simp only [pureRegs, pureReg, operand_val_148, put, if_neg h]
  have t148 : t.regs 148 = Lv - 1 := by
    rw [htR]; simp [pureRegs, pureReg, Arithmetic.eval, put, hL, hone]
  let Inv : Nat → State → Prop := fun k v =>
    (∀ l i, l ≤ k → (i + 2 ^ l) * S ≤ bc → v.memory (Bm + l * N + i) = some (V l i)) ∧
      (∀ a, (a < Bm + N ∨ Bm + Lv * N ≤ a) → v.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 150) → v.regs r = u.regs r) ∧
      v.regs 148 = Lv - 1 ∧ v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs
  obtain ⟨s', k, e, hk, hr, hinv, _, _⟩ :=
    forSlots_spec hW rLVL rLVGO rLVCNT
      (.seq (acts [.arithmetic .shl rSPN rONE rLVL, .arithmetic .mul rT6 rLVL count,
          .arithmetic .add rROWP base rT6, .arithmetic .add rROWC rROWP count])
        (forSlots rMB rMBGO count (memoCellBlock scale)))
      (26 * N + 7) (by decide) (by decide) (by decide) (by decide) (by decide) Inv t htr
      (by rw [tfr 2 (by decide), hone])
      (by show t.regs 148 < 2 ^ W; rw [t148]; omega)
      (by
        intro v _ hvr hvm hve hvk hvkr
        have vfr : ∀ r, r ≠ 137 → r ≠ 138 → v.regs r = t.regs r := hvr
        refine ⟨?_, fun a _ => by rw [hvm, htm], fun r h1 h2 => ?_, ?_, by rw [hve, hte],
          by rw [hvk, htk], by rw [hvkr, htkr]⟩
        · intro l i hl hv
          have hl0 : l = 0 := by omega
          subst hl0
          rw [hvm, htm, Nat.zero_mul, Nat.add_zero]
          exact hrow0 i (by simpa using hv)
        · rw [vfr r (by omega) (by omega), tfr r (by omega)]
        · rw [vfr 148 (by decide) (by decide), t148])
      (by
        intro kk v hkk ⟨I1, I2, I3, I4, I5, I6, I7⟩ hvr hvi hvcnt hvone
        have hvi' : v.regs 137 = kk := hvi
        rw [show ((rLVCNT : Operand) : Nat) = 148 from rfl, t148] at hkk
        have hvB : v.regs base = Bm := by rw [I3 _ hbase.1 hbase.2, hB]
        have hvN : v.regs count = N := by rw [I3 _ hcount.1 hcount.2.1, hN]
        have hvS : v.regs scale = S := by rw [I3 _ hscale.1 hscale.2, hS]
        have hkW : kk < W := by omega
        have h2k : 2 ^ kk ≤ 2 ^ Lv := Nat.pow_le_pow_right (by decide) (by omega)
        have hkN : kk * N ≤ Lv * N := Nat.mul_le_mul_right N (by omega)
        have hk1N : (kk + 1) * N ≤ Lv * N := Nat.mul_le_mul_right N (by omega)
        have hk2N : (kk + 2) * N ≤ Lv * N := Nat.mul_le_mul_right N (by omega)
        -- row header
        obtain ⟨hd, jh, eh, hjh, hdr, hdR, hdm, hde, hdk, hdkr⟩ :=
          RegSpec.pure hW [.arithmetic .shl rSPN rONE rLVL, .arithmetic .mul rT6 rLVL count,
            .arithmetic .add rROWP base rT6, .arithmetic .add rROWC rROWP count] v hvr (by
              simp only [pureOKs, pureOK, pureReg, Arithmetic.eval, put, operand_val_2,
                operand_val_137, operand_val_141, operand_val_146, operand_val_149, hvone, hvi',
                reduceCtorEq, false_implies, false_or, and_true, true_and, ↓reduceIte,
                Nat.reduceEqDiff, hvB, hvN,
                show ¬ ((count : Nat) = 141) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
                show ¬ ((count : Nat) = 146) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
                show ¬ ((count : Nat) = 149) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
                show ¬ ((base : Nat) = 141) from fun h => hbase.2 ⟨by omega, by omega⟩,
                show ¬ ((base : Nat) = 146) from fun h => hbase.2 ⟨by omega, by omega⟩,
                shiftLeft_one]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
        have hdreg : ∀ r, hd.regs r =
            if r = 150 then Bm + kk * N + N else if r = 149 then Bm + kk * N else
            if r = 146 then kk * N else if r = 141 then 2 ^ kk else v.regs r := by
          intro r; rw [hdR]
          simp only [pureRegs, pureReg, Arithmetic.eval, put, operand_val_2, operand_val_137,
            operand_val_141, operand_val_146, operand_val_149, operand_val_150, hvone, hvi',
            ↓reduceIte, Nat.reduceEqDiff, hvB, hvN,
            show ¬ ((count : Nat) = 141) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
            show ¬ ((count : Nat) = 146) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
            show ¬ ((count : Nat) = 149) from fun h => hcount.2.1 ⟨by omega, by omega⟩,
            show ¬ ((base : Nat) = 141) from fun h => hbase.2 ⟨by omega, by omega⟩,
            show ¬ ((base : Nat) = 146) from fun h => hbase.2 ⟨by omega, by omega⟩,
            shiftLeft_one]
        have hdfr : ∀ r, r ≠ 141 → r ≠ 146 → r ≠ 149 → r ≠ 150 → hd.regs r = v.regs r :=
          fun r a b c d => by rw [hdreg, if_neg d, if_neg c, if_neg b, if_neg a]
        -- the cells of row kk + 1
        let J : Nat → State → Prop := fun i w =>
          (∀ l j, l ≤ kk → (j + 2 ^ l) * S ≤ bc → w.memory (Bm + l * N + j) = some (V l j)) ∧
            (∀ j, j < i → (j + 2 ^ (kk + 1)) * S ≤ bc →
              w.memory (Bm + (kk + 1) * N + j) = some (V (kk + 1) j)) ∧
            (∀ a, (a < Bm + N ∨ Bm + Lv * N ≤ a) → w.memory a = u.memory a) ∧
            (∀ r : Nat, r ≠ 108 → r ≠ 139 → r ≠ 140 → ¬ (142 ≤ r ∧ r ≤ 147) →
              w.regs r = hd.regs r) ∧
            w.extent = u.extent ∧ w.keys = u.keys ∧ w.keyRegs = u.keyRegs
        obtain ⟨w, kw, ew, hkw, hwr, hJ, _, _⟩ :=
          forSlots_spec hW rMB rMBGO count (memoCellBlock scale) 22
            (by decide)
            (by show (139 : Nat) ≠ (count : Nat); intro h; exact hcount.2.1 ⟨by omega, by omega⟩)
            (by show (140 : Nat) ≠ (count : Nat); intro h; exact hcount.2.1 ⟨by omega, by omega⟩)
            (by decide) (by decide)
            J hd hdr
            (by rw [hdfr 2 (by decide) (by decide) (by decide) (by decide), hvone])
            (by rw [hdfr count (fun h => hcount.2.1 ⟨by omega, by omega⟩)
                  (fun h => hcount.2.1 ⟨by omega, by omega⟩) (fun h => hcount.2.1 ⟨by omega, by omega⟩)
                  (fun h => hcount.2.1 ⟨by omega, by omega⟩), hvN]; omega)
            (by
              intro x _ hxr hxm hxe hxk hxkr
              have xfr : ∀ r, r ≠ 139 → r ≠ 140 → x.regs r = hd.regs r := hxr
              refine ⟨fun l j hl hj => by rw [hxm, hdm]; exact I1 l j hl hj,
                fun j hj => absurd hj (Nat.not_lt_zero _), fun a ha => by rw [hxm, hdm, I2 a ha],
                fun r h1 h2 h3 _ => xfr r h2 h3, by rw [hxe, hde, I5],
                by rw [hxk, hdk, I6], by rw [hxkr, hdkr, I7]⟩)
            (by
              intro i y hi ⟨J1, J2, J3, J4, J5, J6, J7⟩ hyr hyi hycnt hyone
              have hi' : i < N := by
                have : i < hd.regs count := hi
                rwa [hdfr count (fun h => hcount.2.1 ⟨by omega, by omega⟩)
                  (fun h => hcount.2.1 ⟨by omega, by omega⟩) (fun h => hcount.2.1 ⟨by omega, by omega⟩)
                  (fun h => hcount.2.1 ⟨by omega, by omega⟩), hvN] at this
              have yreg : ∀ r, r ≠ 108 → r ≠ 139 → r ≠ 140 → ¬ (142 ≤ r ∧ r ≤ 147) →
                  y.regs r = hd.regs r := J4
              have y116 : y.regs 116 = A1 := by
                rw [yreg 116 (by decide) (by decide) (by decide) (by decide), hdfr 116 (by decide) (by decide) (by decide)
                  (by decide), I3 116 (by decide) (by decide), h116]
              have y32 : y.regs 32 = bc := by
                rw [yreg 32 (by decide) (by decide) (by decide) (by decide), hdfr 32 (by decide) (by decide) (by decide)
                  (by decide), I3 32 (by decide) (by decide), h32]
              have yS : y.regs scale = S := by
                rw [yreg scale hscale.1 (fun h => hscale.2 ⟨by omega, by omega⟩)
                  (fun h => hscale.2 ⟨by omega, by omega⟩) (fun h => hscale.2 ⟨by omega, by omega⟩),
                  hdfr scale (fun h => hscale.2 ⟨by omega, by omega⟩)
                    (fun h => hscale.2 ⟨by omega, by omega⟩) (fun h => hscale.2 ⟨by omega, by omega⟩)
                    (fun h => hscale.2 ⟨by omega, by omega⟩), hvS]
              have y141 : y.regs 141 = 2 ^ kk := by
                rw [yreg 141 (by decide) (by decide) (by decide) (by decide), hdreg]; simp
              have y149 : y.regs 149 = Bm + kk * N := by
                rw [yreg 149 (by decide) (by decide) (by decide) (by decide), hdreg]; simp
              have y150 : y.regs 150 = Bm + (kk + 1) * N := by
                rw [yreg 150 (by decide) (by decide) (by decide) (by decide), hdreg, Nat.succ_mul]; simp; omega
              have hye : y.extent = u.extent := J5
              obtain ⟨y', j, ev, hj, hy'r, hy'm, hy'fr, hy'e, hy'k, hy'kr⟩ :=
                memoCell_spec hW shape scale (fun h => hscale.2 ⟨by omega, by omega⟩) y hyr hyone A1 bs bc S i (2 ^ kk)
                  (Bm + kk * N) (Bm + (kk + 1) * N) (V kk i) (V kk (i + 2 ^ kk))
                  y116 y32 yS hS1 hyi y141 y149 y150
                  (by
                    have : i + 2 ^ kk + 2 ^ kk ≤ N + 2 ^ Lv := by
                      have : 2 ^ kk + 2 ^ kk ≤ 2 ^ Lv := by
                        rw [← Nat.mul_two, ← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
                      omega
                    have := Nat.mul_le_mul_right S this
                    omega)
                  (by rw [hye]; omega) hAW hcover hlenW
                  (fun b hb => by rw [J3 _ (Or.inl (by omega))]; exact hmin b hb)
                  (by
                    intro hv
                    have hv1 : (i + 2 ^ kk) * S ≤ bc :=
                      Nat.le_trans (Nat.mul_le_mul_right S (by omega)) hv
                    have hv2 : (i + 2 ^ kk + 2 ^ kk) * S ≤ bc := hv
                    have hiN := hNi kk (i + 2 ^ kk) hv2
                    refine ⟨J1 kk i (Nat.le_refl _) hv1, ?_, hVlt kk i hv1, hVlt kk _ hv2, ?_, ?_, ?_, ?_⟩
                    · exact J1 kk (i + 2 ^ kk) (Nat.le_refl _) hv2
                    · rw [hye]; have := row_lt (L := kk + 1) hiN (Nat.lt_succ_self kk); omega
                    · rw [hye]; have := row_lt (L := kk + 2) hi' (show kk + 1 < kk + 2 by omega); omega
                    · have := row_lt (L := kk + 2) hi' (show kk + 1 < kk + 2 by omega); omega
                    · have := row_lt (L := kk + 1) hiN (Nat.lt_succ_self kk); omega)
              refine ⟨y', j, ev, hj, hy'r, ?_, ?_, ?_, ?_⟩
              · show y'.regs 139 = i
                rw [hy'fr 139 (by decide) (by decide)]; exact hyi
              · show y'.regs count = hd.regs count
                rw [hy'fr count hcount.1 (fun h => hcount.2.1 ⟨by omega, by omega⟩)]; exact hycnt
              · rw [hy'fr 2 (by decide) (by decide), hyone]
              · intro x _ hxr hxm hxe hxk hxkr
                have xfr : ∀ r, r ≠ 139 → r ≠ 140 → x.regs r = y'.regs r := hxr
                have hcell_ne : ∀ l j, l ≤ kk → (j + 2 ^ l) * S ≤ bc →
                    Bm + l * N + j ≠ Bm + (kk + 1) * N + i := by
                  intro l j hl hj h
                  exact row_addr_ne (N := N) (l := l) (l' := kk + 1) (i := j) (j := i) (hNi l j hj) hi' (Or.inl (by omega))
                    (by rw [Nat.add_assoc, Nat.add_assoc] at h; exact Nat.add_left_cancel h)
                refine ⟨?_, ?_, ?_, ?_, by rw [hxe, hy'e, J5], by rw [hxk, hy'k, J6],
                  by rw [hxkr, hy'kr, J7]⟩
                · intro l j hl hj
                  rw [hxm, hy'm]
                  split
                  · rw [put_ne _ _ (hcell_ne l j hl hj)]; exact J1 l j hl hj
                  · exact J1 l j hl hj
                · intro j hj hv
                  rw [hxm, hy'm]
                  by_cases hji : j = i
                  · subst hji
                    have hv' : (j + 2 ^ kk + 2 ^ kk) * S ≤ bc := by
                      rw [Nat.pow_succ, Nat.mul_two, ← Nat.add_assoc] at hv; exact hv
                    rw [if_pos hv', put_same, hV kk j hv]
                  · have hne : Bm + (kk + 1) * N + j ≠ Bm + (kk + 1) * N + i := by
                      intro h; exact hji (by omega)
                    split
                    · rw [put_ne _ _ hne]; exact J2 j (by omega) hv
                    · exact J2 j (by omega) hv
                · intro a ha
                  rw [hxm, hy'm]
                  split
                  · have hlo : Bm + N ≤ Bm + (kk + 1) * N + i := by
                      have := row_ge (N := N) (l := kk + 1) (i := i) (by omega); omega
                    have hhi : Bm + (kk + 1) * N + i < Bm + Lv * N := by
                      have := row_lt (L := Lv) hi' (show kk + 1 < Lv by omega); omega
                    rw [put_ne _ _ (by omega)]; exact J3 a ha
                  · exact J3 a ha
                · intro r h108 h139 h140 hr
                  rw [xfr r h139 h140, hy'fr r h108 hr]
                  exact J4 r h108 h139 h140 hr)
        rw [hdfr count (fun h => hcount.2.1 ⟨by omega, by omega⟩)
          (fun h => hcount.2.1 ⟨by omega, by omega⟩) (fun h => hcount.2.1 ⟨by omega, by omega⟩)
          (fun h => hcount.2.1 ⟨by omega, by omega⟩), hvN] at hkw hJ
        obtain ⟨K1, K2, K3, K4, K5, K6, K7⟩ := hJ
        refine ⟨w, jh + kw, EvalG.seq eh ew, by simp at hjh; omega, hwr, ?_, ?_, ?_, ?_⟩
        · show w.regs 137 = kk
          rw [K4 137 (by decide) (by decide) (by decide) (by decide), hdfr 137 (by decide) (by decide) (by decide)
            (by decide)]; exact hvi'
        · show w.regs 148 = t.regs 148
          rw [K4 148 (by decide) (by decide) (by decide) (by decide), hdfr 148 (by decide) (by decide)
            (by decide) (by decide), I4, t148]
        · rw [K4 2 (by decide) (by decide) (by decide) (by decide), hdfr 2 (by decide) (by decide) (by decide)
            (by decide), hvone]
        · intro x _ hxr hxm hxe hxk hxkr
          have xfr : ∀ r, r ≠ 137 → r ≠ 138 → x.regs r = w.regs r := hxr
          refine ⟨?_, fun a ha => by rw [hxm, K3 a ha], ?_, ?_, by rw [hxe, K5], by rw [hxk, K6],
            by rw [hxkr, K7]⟩
          · intro l j hl hj
            rw [hxm]
            by_cases hlk : l ≤ kk
            · exact K1 l j hlk hj
            · have hl' : l = kk + 1 := by omega
              subst hl'
              exact K2 j (hNi (kk + 1) j hj) hj
          · intro r h108 hr
            rw [xfr r (by omega) (by omega), K4 r h108 (by omega) (by omega) (by omega),
              hdfr r (by omega) (by omega) (by omega) (by omega), I3 r h108 hr]
          · rw [xfr 148 (by decide) (by decide), K4 148 (by decide) (by decide) (by decide) (by decide),
              hdfr 148 (by decide) (by decide) (by decide) (by decide), I4])
  rw [show ((rLVCNT : Operand) : Nat) = 148 from rfl, t148] at hk hinv
  obtain ⟨F1, F2, F3, _, F5, F6, F7⟩ := hinv
  refine ⟨s', jt + k, EvalG.seq et e, ?_, hr, fun l i hl hi => F1 l i (by omega) hi, F2, F3, F5, F6, F7⟩
  simp at hjt
  have : (Lv - 1) * (26 * N + 7 + 4) + 3 ≤ Lv * (26 * N + 11) + 3 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) 3
  omega

/-! ## The local memo -/

/-- **Local memo.** `A[l][b] = bpRangeArgMinBlock b (2 ^ l)` at `Bm + l * bc + b`
for every level `l < LC` and every `b` with `b + 2 ^ l ≤ bc`. -/
theorem localMemo_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc Bm LC : Nat) (h116 : u.regs 116 = A1) (h32 : u.regs 32 = bc)
    (h135 : u.regs 135 = Bm) (h58 : u.regs 58 = LC) (hLC1 : 1 ≤ LC) (hLCW : LC < W)
    (hcap : Bm + LC * bc + (bc + 2 ^ LC) * 1 < 2 ^ W)
    (hext : Bm + LC * bc ≤ u.extent) (hextW : u.extent < 2 ^ W) (hA : A1 + bc ≤ Bm)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) :
    ∃ u' j, SafeEval W localMemoBlock u u' j ∧ j ≤ bc * 6 + 3 + (LC * (26 * bc + 11) + 4) ∧
      u'.status = .running ∧
      (∀ l b, l < LC → b + 2 ^ l ≤ bc →
        u'.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))) ∧
      (∀ a, (a < Bm ∨ Bm + LC * bc ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 150) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hbcLC : bc ≤ LC * bc := Nat.le_mul_of_pos_left bc hLC1
  -- row 0
  let Inv : Nat → State → Prop := fun b v =>
    (∀ b', b' < b → v.memory (Bm + b') = some b') ∧
      (∀ a, (a < Bm ∨ Bm + bc ≤ a) → v.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 139 → r ≠ 140 → v.regs r = u.regs r) ∧
      v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs
  obtain ⟨t, k0, e0, hk0, ht, ⟨T1, T2, T3, T4, T5, T6⟩, _, _⟩ :=
    forSlots_spec hW rMB rMBGO rBLOCKS (acts [.arithmetic .add rADDR rAMB rMB, .store rADDR rMB]) 2
      (by decide) (by decide) (by decide) (by decide) (by decide) Inv u hrun hone
      (by show u.regs 32 < 2 ^ W; rw [h32]; omega)
      (by
        intro v _ hvr hvm hve hvk hvkr
        exact ⟨fun b' hb' => absurd hb' (Nat.not_lt_zero _), fun a _ => by rw [hvm],
          fun r _ h1 h2 => hvr r h1 h2, hve, hvk, hvkr⟩)
      (by
        intro b v hb ⟨V1, V2, V3, V4, V5, V6⟩ hvr hvi _ _
        have hb' : b < bc := by have : b < u.regs 32 := hb; rwa [h32] at this
        have hvi' : v.regs 139 = b := hvi
        have v135 : v.regs 135 = Bm := by rw [V3 135 (by decide) (by decide) (by decide), h135]
        have ev := addStore_pair hW rAMB rMB rMB (by decide) v hvr
          (by show v.regs 135 + v.regs 139 < v.extent; rw [v135, hvi', V4]; omega)
          (by rw [V4]; omega) (by show v.regs 139 < 2 ^ W; rw [hvi']; omega)
        refine ⟨_, 2, ev, Nat.le_refl _, hvr, hvi, ?_, ?_, ?_⟩
        · show v.regs 32 = u.regs 32
          exact V3 32 (by decide) (by decide) (by decide)
        · show v.regs 2 = 1
          rw [V3 2 (by decide) (by decide) (by decide), hone]
        · intro x _ hxr hxm hxe hxk hxkr
          have hm : (addStoreState v rAMB rMB rMB).memory = put v.memory (Bm + b) (some b) := by
            show put v.memory (v.regs 135 + v.regs 139) (some (v.regs 139)) = _
            rw [v135, hvi']
          refine ⟨?_, ?_, ?_, by rw [hxe, ← V4]; rfl, by rw [hxk, ← V5]; rfl, by rw [hxkr, ← V6]; rfl⟩
          · intro b' hb''
            rw [hxm, hm]
            by_cases hbb : b' = b
            · subst hbb; rw [put_same]
            · rw [put_ne _ _ (by omega)]; exact V1 b' (by omega)
          · intro a ha
            rw [hxm, hm, put_ne _ _ (by omega)]; exact V2 a ha
          · intro r h108 h139 h140
            have xfr : ∀ r, r ≠ 139 → r ≠ 140 → x.regs r = (addStoreState v rAMB rMB rMB).regs r := hxr
            rw [xfr r h139 h140]
            show put v.regs 108 _ r = _
            rw [put_ne _ _ h108]; exact V3 r h108 h139 h140)
  rw [show ((rBLOCKS : Operand) : Nat) = 32 from rfl, h32] at hk0 T1
  -- rows 1 .. LC - 1
  obtain ⟨u', j, e, hj, hr, M1, M2, M3, M4, M5, M6⟩ :=
    memoLevels_spec hW shape rAMB rBLOCKS rONE rOW (by decide) (by decide) (by decide)
      t ht (by rw [T3 2 (by decide) (by decide) (by decide), hone]) A1 bs bc Bm bc 1 LC
      (fun l b => bpRangeArgMinBlock shape bs b (2 ^ l))
      (by rw [T3 116 (by decide) (by decide) (by decide), h116])
      (by rw [T3 32 (by decide) (by decide) (by decide), h32])
      (by show t.regs 135 = Bm; rw [T3 135 (by decide) (by decide) (by decide), h135])
      (by show t.regs 32 = bc; rw [T3 32 (by decide) (by decide) (by decide), h32])
      (by show t.regs 2 = 1; rw [T3 2 (by decide) (by decide) (by decide), hone])
      (by show t.regs 58 = LC; rw [T3 58 (by decide) (by decide) (by decide), h58])
      (Nat.le_refl 1) hLC1 hLCW hcap (by rw [T4]; exact hext) hA hcover hlenW
      (fun b hb => by rw [T2 _ (Or.inl (by omega))]; exact hmin b hb)
      (fun l i _ => bpRangeArgMinBlock_pow_succ shape bs i l)
      (fun l i hi => by
        have := (bpRangeArgMinBlock_mem shape bs i (2 ^ l) (Nat.two_pow_pos l)).2
        show bpRangeArgMinBlock shape bs i (2 ^ l) < bc
        simp only [Nat.mul_one] at hi; omega)
      (fun l i hi => by
        have := Nat.two_pow_pos l
        simp only [Nat.mul_one] at hi; omega)
      (fun i hi => by
        simp only [Nat.mul_one] at hi
        rw [T1 i (by omega)]; simp)
  refine ⟨u', k0 + j, EvalG.seq e0 e, by omega, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l b hl hb
    exact M1 l b hl (by simpa using hb)
  · intro a ha
    rw [M2 a (by omega), T2 a (by omega)]
  · intro r h108 hr'
    rw [M3 r h108 hr', T3 r h108 (by omega) (by omega)]
  · rw [M4, T4]
  · rw [M5, T5]
  · rw [M6, T6]

/-! ## The global memo -/

/-- **Macro scan.** For a complete macro `m` (`(m + 1) * M ≤ bc`), cell `Gb + m`
receives the leftmost argmin block of its `M` blocks; otherwise memory is
unchanged. -/
theorem macroScan_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc M Gb m : Nat) (h116 : u.regs 116 = A1) (h32 : u.regs 32 = bc)
    (h31 : u.regs 31 = M) (h136 : u.regs 136 = Gb) (h139 : u.regs 139 = m)
    (hM1 : 1 ≤ M) (hcapM : (m + 1) * M < 2 ^ W) (hA : A1 + bc ≤ u.extent) (hAW : A1 + bc < 2 ^ W)
    (hextW : u.extent < 2 ^ W)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (hG : (m + 1) * M ≤ bc → Gb + m < u.extent ∧ Gb + m < 2 ^ W) :
    ∃ u' j, SafeEval W macroScanBlock u u' j ∧ j ≤ 15 * M + 12 ∧ u'.status = .running ∧
      u'.memory = (if (m + 1) * M ≤ bc then
        put u.memory (Gb + m) (some (bpRangeArgMinBlock shape bs (m * M) M)) else u.memory) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → ¬ (151 ≤ r ∧ r ≤ 154) →
        u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hmM : (m + 1) * M = m * M + M := Nat.succ_mul m M
  have hle1 : m + 1 ≤ (m + 1) * M := Nat.le_mul_of_pos_right (m + 1) hM1
  -- guard
  obtain ⟨t, jt, et, hjt, htr, htR, htm, hte, htk, htkr⟩ :=
    RegSpec.pure hW [.arithmetic .add rT6 rMB rONE, .arithmetic .mul rT6 rT6 rMACRO,
      .comparison .lt rT7 rBLOCKS rT6] u hrun (by
        simp only [pureOKs, pureOK, pureReg, Arithmetic.eval, put, operand_val_146, operand_val_139,
          operand_val_2, operand_val_31, h139, hone, h31, reduceCtorEq, false_implies, false_or,
          and_true, ↓reduceIte, Nat.reduceEqDiff]
        refine ⟨?_, ?_⟩ <;> omega)
  have tR : ∀ r, t.regs r = if r = 147 then (if bc < (m + 1) * M then 1 else 0) else
      if r = 146 then (m + 1) * M else u.regs r := by
    intro r; rw [htR]
    simp only [pureRegs, pureReg, Arithmetic.eval, Comparison.eval, put, operand_val_146,
      operand_val_139, operand_val_2, operand_val_31, operand_val_147, operand_val_32, h139, hone,
      h31, h32, ↓reduceIte, Nat.reduceEqDiff]
    by_cases h146 : r = 146 <;> simp [h146]
  have tfr : ∀ r, r ≠ 146 → r ≠ 147 → t.regs r = u.regs r := fun r a b => by
    rw [tR, if_neg b, if_neg a]
  by_cases hv : (m + 1) * M ≤ bc
  · obtain ⟨hGe, hGW⟩ := hG hv
    have hc : t.regs rT7 = 0 := by show t.regs 147 = 0; rw [tR, if_pos rfl, if_neg (by omega)]
    -- start, best, count
    obtain ⟨h1, j1, e1, hj1, h1r, h1R, h1m, h1e, h1k, h1kr⟩ :=
      RegSpec.pure hW [.arithmetic .mul rMST rMB rMACRO, .move rCX rMST,
        .arithmetic .sub rMM1 rMACRO rONE] t htr (by
          simp only [pureOKs, pureOK, pureReg, Arithmetic.eval, put, operand_val_151,
            operand_val_139, operand_val_31, operand_val_2, operand_val_142,
            tfr 139 (by decide) (by decide), tfr 31 (by decide) (by decide),
            tfr 2 (by decide) (by decide), h139, h31, hone, reduceCtorEq, false_implies, false_or,
            and_true, true_and, ↓reduceIte, Nat.reduceEqDiff]
          refine ⟨?_, ?_, ?_⟩ <;> omega)
    have h1reg : ∀ r, h1.regs r = if r = 152 then M - 1 else if r = 142 then m * M else
        if r = 151 then m * M else t.regs r := by
      intro r; rw [h1R]
      simp only [pureRegs, pureReg, Arithmetic.eval, put, operand_val_151, operand_val_139,
        operand_val_31, operand_val_2, operand_val_142, operand_val_152,
        tfr 139 (by decide) (by decide), tfr 31 (by decide) (by decide),
        tfr 2 (by decide) (by decide), h139, h31, hone, ↓reduceIte, Nat.reduceEqDiff]
    have h1fr : ∀ r, r ≠ 142 → r ≠ 151 → r ≠ 152 → h1.regs r = t.regs r := fun r a b c => by
      rw [h1reg, if_neg c, if_neg a, if_neg b]
    have hstart : ∀ jj, jj ≤ M - 1 → m * M + jj < bc := fun jj hjj => by omega
    -- scan
    let Inv : Nat → State → Prop := fun jj w =>
      w.regs 142 = bpRangeArgMinBlock shape bs (m * M) (jj + 1) ∧
        (∀ r : Nat, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → r ≠ 153 → r ≠ 154 → w.regs r = h1.regs r) ∧
        w.memory = u.memory ∧ w.extent = u.extent ∧ w.keys = u.keys ∧ w.keyRegs = u.keyRegs
    obtain ⟨h2, k2, e2, hk2, h2r, ⟨S1, S2, S3, S4, S5, S6⟩, _, _⟩ :=
      forSlots_spec hW rJS rJSGO rMM1
        (acts ([.arithmetic .add rCY rMST rJS, .arithmetic .add rCY rCY rONE] ++
          betterActs rCX rCX rCY)) 11
        (by decide) (by decide) (by decide) (by decide) (by decide) Inv h1 h1r
        (by rw [h1fr 2 (by decide) (by decide) (by decide), tfr 2 (by decide) (by decide), hone])
        (by show h1.regs 152 < 2 ^ W; rw [h1reg]; simp; omega)
        (by
          intro w _ hwr hwm hwe hwk hwkr
          have wfr : ∀ r, r ≠ 153 → r ≠ 154 → w.regs r = h1.regs r := hwr
          refine ⟨?_, fun r _ _ a b => wfr r a b, by rw [hwm, h1m, htm], by rw [hwe, h1e, hte],
            by rw [hwk, h1k, htk], by rw [hwkr, h1kr, htkr]⟩
          rw [wfr 142 (by decide) (by decide), h1reg]; simp)
        (by
          intro jj w hjj ⟨W1, W2, W3, W4, W5, W6⟩ hwr hwi hwcnt hwone
          have hjj' : jj < M - 1 := by
            have : jj < h1.regs 152 := hjj
            rwa [h1reg, if_pos rfl] at this
          have hwi' : w.regs 153 = jj := hwi
          have w151 : w.regs 151 = m * M := by
            rw [W2 151 (by decide) (by decide) (by decide) (by decide), h1reg]; simp
          have w2 : w.regs 2 = 1 := hwone
          have w116 : w.regs 116 = A1 := by
            rw [W2 116 (by decide) (by decide) (by decide) (by decide),
              h1fr 116 (by decide) (by decide) (by decide), tfr 116 (by decide) (by decide), h116]
          obtain ⟨x1, q1, r1, m1, e1', k1', kr1⟩ :=
            prefix_pure hW (.arithmetic .add rCY rMST rJS) w hwr (by
              simp only [pureOK, Arithmetic.eval, operand_val_151, operand_val_153, w151, hwi',
                reduceCtorEq, false_implies, false_or, and_true]; omega)
          have x1r : x1.regs = put w.regs 143 (m * M + jj) := by
            rw [r1]; simp only [pureReg, Arithmetic.eval, operand_val_143, operand_val_151,
              operand_val_153, w151, hwi']
          obtain ⟨x2, q2, r2, m2, e2', k2', kr2⟩ :=
            prefix_pure hW (.arithmetic .add rCY rCY rONE) x1 q1.1 (by
              simp only [pureOK, Arithmetic.eval, operand_val_143, operand_val_2, x1r, put_same,
                put_ne _ _ (show (2 : Nat) ≠ 143 by decide), w2, reduceCtorEq, false_implies,
                false_or, and_true]; omega)
          have x2r : x2.regs = put (put w.regs 143 (m * M + jj)) 143 (m * M + jj + 1) := by
            rw [r2, x1r]; simp only [pureReg, Arithmetic.eval, operand_val_143, operand_val_2, put_same,
              put_ne _ _ (show (2 : Nat) ≠ 143 by decide), w2]
          have hX := (bpRangeArgMinBlock_mem shape bs (m * M) (jj + 1) (by omega)).2
          obtain ⟨x3, q3, r3, fr3, m3, e3', k3', kr3⟩ :=
            betterActs_prefix hW shape rCX rCX rCY (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) x2 q2.1
              (by rw [x2r, put_ne _ _ (by decide), put_ne _ _ (by decide), w2]) A1 bs bc
              (bpRangeArgMinBlock shape bs (m * M) (jj + 1)) (m * M + jj + 1)
              (by rw [x2r, put_ne _ _ (by decide), put_ne _ _ (by decide), w116])
              (by show x2.regs 142 = _; rw [x2r, put_ne _ _ (by decide), put_ne _ _ (by decide), W1])
              (by show x2.regs 143 = _; rw [x2r, put_same])
              (by omega) (by omega) (by rw [e2', e1', W4]; exact hA) hAW hcover hlenW
              (fun b hb => by rw [m2, m1, W3]; exact hmin b hb)
          have pre := q1.append (q2.append q3)
          refine ⟨x3, 1 + (1 + 9), pre.close, by omega, q3.1, ?_, ?_, ?_, ?_⟩
          · show x3.regs 153 = jj
            rw [fr3 153 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x2r,
              put_ne _ _ (by decide), put_ne _ _ (by decide), hwi']
          · show x3.regs 152 = h1.regs 152
            rw [fr3 152 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x2r,
              put_ne _ _ (by decide), put_ne _ _ (by decide)]; exact hwcnt
          · rw [fr3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), x2r,
              put_ne _ _ (by decide), put_ne _ _ (by decide), w2]
          · intro y _ hyr hym hye hyk hykr
            have yfr : ∀ r, r ≠ 153 → r ≠ 154 → y.regs r = x3.regs r := hyr
            refine ⟨?_, ?_, by rw [hym, m3, m2, m1, W3], by rw [hye, e3', e2', e1', W4],
              by rw [hyk, k3', k2', k1', W5], by rw [hykr, kr3, kr2, kr1, W6]⟩
            · rw [yfr 142 (by decide) (by decide), show x3.regs 142 = _ from r3, rangeArgMin_snoc,
                show m * M + 1 + jj = m * M + jj + 1 by omega]
            · intro r h108 hr h153 h154
              rw [yfr r h153 h154, fr3 r h108 (by omega) (by omega) (by omega) (by omega)
                  (by show r ≠ 142; omega),
                x2r, put_ne _ _ (by omega), put_ne _ _ (by omega)]
              exact W2 r h108 hr h153 h154)
    rw [show ((rMM1 : Operand) : Nat) = 152 from rfl, h1reg, if_pos rfl] at hk2 S1
    rw [show M - 1 + 1 = M by omega] at S1
    -- store
    have h2_136 : h2.regs 136 = Gb := by
      rw [S2 136 (by decide) (by decide) (by decide) (by decide), h1fr 136 (by decide) (by decide)
        (by decide), tfr 136 (by decide) (by decide), h136]
    have h2_139 : h2.regs 139 = m := by
      rw [S2 139 (by decide) (by decide) (by decide) (by decide), h1fr 139 (by decide) (by decide)
        (by decide), tfr 139 (by decide) (by decide), h139]
    have hRW : bpRangeArgMinBlock shape bs (m * M) M < 2 ^ W := by
      have := (bpRangeArgMinBlock_mem shape bs (m * M) M hM1).2; omega
    have e3 := addStore_pair hW rGMB rMB rCX (by decide) h2 h2r
      (by show h2.regs 136 + h2.regs 139 < h2.extent; rw [h2_136, h2_139, S4]; exact hGe)
      (by rw [S4]; omega) (by show h2.regs 142 < 2 ^ W; rw [S1]; exact hRW)
    refine ⟨addStoreState h2 rGMB rMB rCX, jt + (j1 + (k2 + 2) + 1),
      EvalG.seq et (EvalG.ifZeroTaken htr hc (EvalG.seq e1 (EvalG.seq e2 e3))), ?_, h2r, ?_, ?_,
      S4, S5, S6⟩
    · simp at hjt hj1
      have : (M - 1) * (11 + 4) + 3 ≤ 15 * M + 3 := by
        have := Nat.mul_le_mul_right 15 (Nat.sub_le M 1); omega
      omega
    · rw [if_pos hv]
      show put h2.memory (h2.regs 136 + h2.regs 139) (some (h2.regs 142)) = _
      rw [h2_136, h2_139, S1, S3]
    · intro r h108 hr1 hr2
      show put h2.regs 108 _ r = _
      rw [put_ne _ _ h108, S2 r h108 hr1 (by omega) (by omega), h1fr r (by omega) (by omega) (by omega),
        tfr r (by omega) (by omega)]
  · have hc : t.regs rT7 ≠ 0 := by
      show t.regs 147 ≠ 0; rw [tR, if_pos rfl, if_pos (by omega)]; decide
    refine ⟨t, jt + (0 + 2), EvalG.seq et (EvalG.ifZeroFallthrough htr hc (EvalG.skip t htr) htr),
      by simp at hjt; omega, htr, by rw [if_neg hv, htm], ?_, hte, htk, htkr⟩
    intro r h108 hr1 hr2
    exact tfr r (by omega) (by omega)

/-- **Global memo.** `G[l][m] = bpRangeArgMinBlock (m * M) (2 ^ l * M)` at
`Gb + l * mc + m` for every level `l < GLC` and every `m` with
`(m + 2 ^ l) * M ≤ bc`. -/
theorem globalMemo_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (u : State)
    (hrun : u.status = .running) (hone : u.regs 2 = 1)
    (A1 bs bc Gb M mc GLC : Nat) (h116 : u.regs 116 = A1) (h32 : u.regs 32 = bc)
    (h31 : u.regs 31 = M) (h33 : u.regs 33 = mc) (h136 : u.regs 136 = Gb) (h59 : u.regs 59 = GLC)
    (hM1 : 1 ≤ M) (hmc : mc = bc / M + 1) (hGLC1 : 1 ≤ GLC) (hGLCW : GLC < W)
    (hcap : Gb + GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W)
    (hext : Gb + GLC * mc ≤ u.extent) (hextW : u.extent < 2 ^ W) (hA : A1 + bc ≤ Gb)
    (hcover : bc * bs ≤ shape.bpCode.length) (hlenW : shape.bpCode.length < 2 ^ W)
    (hmin : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) :
    ∃ u' j, SafeEval W globalMemoBlock u u' j ∧
      j ≤ mc * (15 * M + 16) + 3 + (GLC * (26 * mc + 11) + 4) ∧ u'.status = .running ∧
      (∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
        u'.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))) ∧
      (∀ a, (a < Gb ∨ Gb + GLC * mc ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 154) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hmcG : mc ≤ GLC * mc := Nat.le_mul_of_pos_left mc hGLC1
  have hmcM : mc * M < 2 ^ W := by
    have := Nat.mul_le_mul_right M (Nat.le_add_right mc (2 ^ GLC)); omega
  have hNi : ∀ l i, (i + 2 ^ l) * M ≤ bc → i < mc := by
    intro l i hi
    have h1 : (i + 1) * M ≤ bc :=
      Nat.le_trans (Nat.mul_le_mul_right M (by have := Nat.two_pow_pos l; omega)) hi
    have h2 : i + 1 ≤ bc / M := (Nat.le_div_iff_mul_le (by omega)).2 h1
    omega
  have hAW : A1 + bc < 2 ^ W := by omega
  -- row 0: macro scans
  let Inv : Nat → State → Prop := fun m v =>
    (∀ m', m' < m → (m' + 1) * M ≤ bc →
      v.memory (Gb + m') = some (bpRangeArgMinBlock shape bs (m' * M) M)) ∧
      (∀ a, (a < Gb ∨ Gb + mc ≤ a) → v.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 139 → r ≠ 140 → ¬ (142 ≤ r ∧ r ≤ 147) → ¬ (151 ≤ r ∧ r ≤ 154) →
        v.regs r = u.regs r) ∧
      v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs
  obtain ⟨t, k0, e0, hk0, ht, ⟨T1, T2, T3, T4, T5, T6⟩, _, _⟩ :=
    forSlots_spec hW rMB rMBGO rMACROS macroScanBlock (15 * M + 12)
      (by decide) (by decide) (by decide) (by decide) (by decide) Inv u hrun hone
      (by show u.regs 33 < 2 ^ W; rw [h33]; have := Nat.le_mul_of_pos_right mc hM1; omega)
      (by
        intro v _ hvr hvm hve hvk hvkr
        exact ⟨fun m' hm' => absurd hm' (Nat.not_lt_zero _), fun a _ => by rw [hvm],
          fun r _ h1 h2 _ _ => hvr r h1 h2, hve, hvk, hvkr⟩)
      (by
        intro m v hm ⟨V1, V2, V3, V4, V5, V6⟩ hvr hvi _ hvone
        have hm' : m < mc := by have : m < u.regs 33 := hm; rwa [h33] at this
        have hvi' : v.regs 139 = m := hvi
        have vget : ∀ r : Nat, r ≠ 108 → r ≠ 139 → r ≠ 140 → ¬ (142 ≤ r ∧ r ≤ 147) →
            ¬ (151 ≤ r ∧ r ≤ 154) → v.regs r = u.regs r := V3
        have hmM : (m + 1) * M ≤ mc * M := Nat.mul_le_mul_right M hm'
        obtain ⟨v', j, ev, hj, hv'r, hv'm, hv'fr, hv'e, hv'k, hv'kr⟩ :=
          macroScan_spec hW shape v hvr hvone A1 bs bc M Gb m
            (by rw [vget 116 (by decide) (by decide) (by decide) (by decide) (by decide), h116])
            (by rw [vget 32 (by decide) (by decide) (by decide) (by decide) (by decide), h32])
            (by rw [vget 31 (by decide) (by decide) (by decide) (by decide) (by decide), h31])
            (by rw [vget 136 (by decide) (by decide) (by decide) (by decide) (by decide), h136])
            hvi' hM1 (by omega) (by rw [V4]; omega) hAW (by rw [V4]; exact hextW) hcover hlenW
            (fun b hb => by rw [V2 _ (Or.inl (by omega))]; exact hmin b hb)
            (fun _ => ⟨by rw [V4]; omega, by omega⟩)
        refine ⟨v', j, ev, hj, hv'r, ?_, ?_, ?_, ?_⟩
        · show v'.regs 139 = m
          rw [hv'fr 139 (by decide) (by decide) (by decide)]; exact hvi'
        · show v'.regs 33 = u.regs 33
          rw [hv'fr 33 (by decide) (by decide) (by decide),
            vget 33 (by decide) (by decide) (by decide) (by decide) (by decide)]
        · rw [hv'fr 2 (by decide) (by decide) (by decide), hvone]
        · intro x _ hxr hxm hxe hxk hxkr
          have xfr : ∀ r, r ≠ 139 → r ≠ 140 → x.regs r = v'.regs r := hxr
          refine ⟨?_, ?_, ?_, by rw [hxe, hv'e, V4], by rw [hxk, hv'k, V5], by rw [hxkr, hv'kr, V6]⟩
          · intro m'' hm'' hv
            rw [hxm, hv'm]
            by_cases hmm : m'' = m
            · subst hmm; rw [if_pos hv, put_same]
            · split
              · rw [put_ne _ _ (by omega)]; exact V1 m'' (by omega) hv
              · exact V1 m'' (by omega) hv
          · intro a ha
            rw [hxm, hv'm]
            split
            · rw [put_ne _ _ (by omega)]; exact V2 a ha
            · exact V2 a ha
          · intro r h108 h139 h140 hr1 hr2
            rw [xfr r h139 h140, hv'fr r h108 hr1 hr2]
            exact V3 r h108 h139 h140 hr1 hr2)
  rw [show ((rMACROS : Operand) : Nat) = 33 from rfl, h33] at hk0 T1
  have tget : ∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 154) → t.regs r = u.regs r :=
    fun r h1 h2 => T3 r h1 (by omega) (by omega) (by omega) (by omega)
  obtain ⟨u', j, e, hj, hr, M1, M2, M3, M4, M5, M6⟩ :=
    memoLevels_spec hW shape rGMB rMACROS rMACRO rGLC (by decide) (by decide) (by decide)
      t ht (by rw [tget 2 (by decide) (by decide), hone]) A1 bs bc Gb mc M GLC
      (fun l m => bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))
      (by rw [tget 116 (by decide) (by decide), h116])
      (by rw [tget 32 (by decide) (by decide), h32])
      (by show t.regs 136 = Gb; rw [tget 136 (by decide) (by decide), h136])
      (by show t.regs 33 = mc; rw [tget 33 (by decide) (by decide), h33])
      (by show t.regs 31 = M; rw [tget 31 (by decide) (by decide), h31])
      (by show t.regs 59 = GLC; rw [tget 59 (by decide) (by decide), h59])
      hM1 hGLC1 hGLCW hcap (by rw [T4]; exact hext) hA hcover hlenW
      (fun b hb => by rw [T2 _ (Or.inl (by omega))]; exact hmin b hb)
      (fun l i _ => globalMemo_double shape bs M i l)
      (fun l i hi => by
        have hpos : 0 < 2 ^ l * M := Nat.mul_pos (Nat.two_pow_pos l) (by omega)
        have := (bpRangeArgMinBlock_mem shape bs (i * M) (2 ^ l * M) hpos).2
        show bpRangeArgMinBlock shape bs (i * M) (2 ^ l * M) < bc
        rw [Nat.add_mul] at hi; omega)
      hNi
      (fun i hi => by
        show t.memory (Gb + i) = some (bpRangeArgMinBlock shape bs (i * M) (2 ^ 0 * M))
        rw [Nat.pow_zero, Nat.one_mul]
        exact T1 i (hNi 0 i (by simpa using hi)) hi)
  rw [show 15 * M + 12 + 4 = 15 * M + 16 by omega] at hk0
  refine ⟨u', k0 + j, EvalG.seq e0 e, by omega, hr, M1, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [M2 a (by omega), T2 a (by omega)]
  · intro r h108 hr'
    rw [M3 r h108 (by omega), tget r h108 hr']
  · rw [M4, T4]
  · rw [M5, T5]
  · rw [M6, T6]

end RMQ.SuccinctFinal.PackedConstruction.Proof

import RMQ.Core.WordRAM.Construction.Proof.Emit

/-! # PRE-1 builder proofs: register-only block specifications

Outside the builder firewall. `RegSpec W b pre F cost` says that the block `b`
acts on registers only: from every running state whose registers satisfy
`pre`, it safely evaluates in at most `cost regs` steps to a running state
whose registers are exactly `F regs`, with memory, extent, keys and key
registers unchanged. Register-only specifications compose by sequencing
(`RegSpec.seq`), straight-line register actions have a computed specification
(`RegSpec.pure`: the register function `pureRegs` and the safety obligations
`pureOK` are evaluated by `simp` at literal registers), and the halving loop has
an exact one (`RegSpec.log2`). Size-only geometry blocks are specified through
these three rules, so their register values are computed rather than tracked
by hand.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-- Register-only block specification with an exact register function. -/
def RegSpec (W : Nat) (b : Block) (pre : Registers → Prop) (F : Registers → Registers)
    (cost : Registers → Nat) : Prop :=
  ∀ s : State, s.status = .running → pre s.regs →
    ∃ s' k, SafeEval W b s s' k ∧ k ≤ cost s.regs ∧ s'.status = .running ∧
      s'.regs = F s.regs ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧
      s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs

theorem RegSpec.seq {W : Nat} {a b : Block} {pa pb : Registers → Prop}
    {Fa Fb : Registers → Registers} {ca cb : Registers → Nat}
    (ha : RegSpec W a pa Fa ca) (hb : RegSpec W b pb Fb cb) :
    RegSpec W (.seq a b) (fun r => pa r ∧ pb (Fa r)) (fun r => Fb (Fa r))
      (fun r => ca r + cb (Fa r)) := by
  intro s hrun ⟨hpa, hpb⟩
  obtain ⟨s₁, k₁, ea, hk₁, hr₁, hreg₁, hm₁, he₁, hks₁, hkr₁⟩ := ha s hrun hpa
  obtain ⟨s₂, k₂, eb, hk₂, hr₂, hreg₂, hm₂, he₂, hks₂, hkr₂⟩ :=
    hb s₁ hr₁ (by rw [hreg₁]; exact hpb)
  refine ⟨s₂, k₁ + k₂, EvalG.seq ea eb, ?_, hr₂, by rw [hreg₂, hreg₁], by rw [hm₂, hm₁],
    by rw [he₂, he₁], by rw [hks₂, hks₁], by rw [hkr₂, hkr₁]⟩
  show k₁ + k₂ ≤ ca s.regs + cb (Fa s.regs)
  rw [hreg₁] at hk₂
  omega

theorem RegSpec.weaken {W : Nat} {b : Block} {pre pre' : Registers → Prop}
    {F F' : Registers → Registers} {cost cost' : Registers → Nat}
    (h : RegSpec W b pre F cost) (hpre : ∀ r, pre' r → pre r)
    (hF : ∀ r, pre' r → F r = F' r) (hcost : ∀ r, pre' r → cost r ≤ cost' r) :
    RegSpec W b pre' F' cost' := by
  intro s hrun hp
  obtain ⟨s', k, e, hk, hr, hreg, hm, he, hks, hkr⟩ := h s hrun (hpre _ hp)
  exact ⟨s', k, e, Nat.le_trans hk (hcost _ hp), hr, by rw [hreg, hF _ hp], hm, he, hks, hkr⟩

/-! ## Straight-line register actions -/

/-- Register effect of a register-only action (other actions are not register-only). -/
def pureReg : Action → Registers → Registers
  | .constant d v, r => put r d v.val
  | .move d src, r => put r d (r src)
  | .arithmetic op d l x, r => put r d (op.eval (r l) (r x))
  | .comparison op d l x, r => put r d (op.eval (r l) (r x))
  | _, r => r

/-- Safety obligations of a register-only action at a register valuation;
`False` for actions that touch memory, extent or keys. -/
def pureOK (W : Nat) : Action → Registers → Prop
  | .constant _ _, _ => True
  | .move _ _, _ => True
  | .arithmetic op _ l x, r =>
      op.eval (r l) (r x) < 2 ^ W ∧ (op = .sub → r x ≤ r l) ∧
        (op = .div ∨ op = .mod → 0 < r x) ∧ (op = .shl ∨ op = .shr → r x < W)
  | .comparison _ _ _ _, _ => True
  | _, _ => False

def pureRegs : List Action → Registers → Registers
  | [], r => r
  | a :: rest, r => pureRegs rest (pureReg a r)

def pureOKs (W : Nat) : List Action → Registers → Prop
  | [], _ => True
  | a :: rest, r => pureOK W a r ∧ pureOKs W rest (pureReg a r)

theorem pure_exec {W : Nat} (a : Action) (s : State) (h : pureOK W a s.regs) :
    execPrim a.prim s = { s with regs := pureReg a s.regs, pc := s.pc + 1 } := by
  cases a <;> simp only [pureOK] at h <;> rfl

theorem pure_safe {W : Nat} (hW : 32 ≤ W) (a : Action) (s : State) (h : pureOK W a s.regs) :
    Action.Safe W s a := by
  cases a <;> simp only [pureOK] at h
  · exact ⟨Prim.operandsFit_of_width _ hW, trivial⟩
  · exact ⟨Prim.operandsFit_of_width _ hW, trivial⟩
  · exact ⟨Prim.operandsFit_of_width _ hW, h⟩
  · exact ⟨Prim.operandsFit_of_width _ hW, trivial⟩

theorem pure_acts_exec {W : Nat} (hW : 32 ≤ W) :
    ∀ (ops : List Action) (s : State), s.status = .running → pureOKs W ops s.regs →
      ActsOK (Action.Safe W) ops s ∧
        execActs ops s = { s with regs := pureRegs ops s.regs, pc := s.pc + ops.length }
  | [], s, _, _ => ⟨trivial, rfl⟩
  | a :: rest, s, hrun, ⟨ha, hrest⟩ => by
      have hexec := pure_exec a s ha
      have hrun' : (execPrim a.prim s).status = .running := by rw [hexec]; exact hrun
      have hrest' : pureOKs W rest (execPrim a.prim s).regs := by rw [hexec]; exact hrest
      obtain ⟨hok, heq⟩ := pure_acts_exec hW rest (execPrim a.prim s) hrun' hrest'
      refine ⟨⟨pure_safe hW a s ha, hrun', hok⟩, ?_⟩
      show execActs rest (execPrim a.prim s) = _
      rw [heq, hexec]
      simp only [pureRegs, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- **Straight-line register actions.** -/
theorem RegSpec.pure {W : Nat} (hW : 32 ≤ W) (ops : List Action) :
    RegSpec W (acts ops) (pureOKs W ops) (pureRegs ops) (fun _ => ops.length) := by
  intro s hrun hok
  obtain ⟨hsafe, heq⟩ := pure_acts_exec hW ops s hrun hok
  have e := acts_evalG (P := Action.Safe W) ops s hrun hsafe
  rw [heq] at e
  exact ⟨_, _, e, Nat.le_refl _, hrun, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The halving loop, exactly -/

/-- **Halving loop, exact registers.** `log2Block dst src` sets `dst` to
`Nat.log2 x`, leaves `x / 2 ^ Nat.log2 x` in register 20 and `0` in register
21, and changes no other register (`x = regs src`). -/
theorem RegSpec.log2 {W : Nat} (hW : 32 ≤ W) (dst src : Operand)
    (hd2 : (dst : Nat) ≠ 2) (hd9 : (dst : Nat) ≠ 9) (hd20 : (dst : Nat) ≠ 20)
    (hd21 : (dst : Nat) ≠ 21) :
    RegSpec W (log2Block dst src) (fun r => r 2 = 1 ∧ r 9 = 2 ∧ r src < 2 ^ W)
      (fun r => put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst
        (Nat.log2 (r src)))
      (fun r => 5 * Nat.log2 (r src) + 4) := by
  intro s hrun ⟨hone, htwo, hxW⟩
  dsimp only
  have n2 : (2 : Nat) ≠ dst := fun h => hd2 h.symm
  have n9 : (9 : Nat) ≠ dst := fun h => hd9 h.symm
  have n20 : (20 : Nat) ≠ dst := fun h => hd20 h.symm
  have n21 : (21 : Nat) ≠ dst := fun h => hd21 h.symm
  generalize hx : s.regs src = x at hxW ⊢
  generalize hL : Nat.log2 x = L
  have hLx : L ≤ x := by rw [← hL]; exact Nat.log2_le_self x
  have hLW : L < 2 ^ W := Nat.lt_of_le_of_lt hLx hxW
  let t1 := execPrim (Prim.move rLX src) s
  have f1 := exec_move s rLX src
  let t2 := execPrim (Prim.constant dst 0) t1
  have f2 := exec_constant t1 dst 0
  let t3 := execPrim (Prim.comparison .lt rLC rONE rLX) t2
  have f3 := exec_comparison t2 .lt rLC rONE rLX
  have t1r : t1.regs = put s.regs 20 x := by simp [t1, f1, hx]
  have t2r : t2.regs = put t1.regs dst 0 := by simp [t2, f2]
  have t2one : t2.regs 2 = 1 := by
    rw [t2r, put_ne _ _ n2, t1r, put_ne _ _ (by decide), hone]
  have t2two : t2.regs 9 = 2 := by
    rw [t2r, put_ne _ _ n9, t1r, put_ne _ _ (by decide), htwo]
  have t2lx : t2.regs 20 = x := by rw [t2r, put_ne _ _ n20, t1r, put_same]
  have t2dst : t2.regs dst = 0 := by rw [t2r, put_same]
  have t3r : t3.regs = put t2.regs 21 (if 1 < x then 1 else 0) := by
    simp [t3, f3, Comparison.eval, t2one, t2lx]
  have t3m : t3.memory = s.memory := by simp [t3, f3, t2, f2, t1, f1]
  have t3e : t3.extent = s.extent := by simp [t3, f3, t2, f2, t1, f1]
  have t3s : t3.status = .running := by simp [t3, f3, t2, f2, t1, f1, hrun]
  have t3k : t3.keys = s.keys ∧ t3.keyRegs = s.keyRegs := by simp [t3, f3, t2, f2, t1, f1]
  have hinit : SafeEval W (acts [.move rLX src, .constant dst 0,
      .comparison .lt rLC rONE rLX]) s t3 3 :=
    acts_evalG (P := Action.Safe W) _ s hrun
      ⟨safe_move hW s _ _, by simp [Action.prim, exec_move, hrun],
        safe_constant hW t1 _ _, by simp [Action.prim, f1, exec_constant, hrun],
        safe_comparison hW t2 _ _ _ _, t3s, trivial⟩
  let Q : Nat → State → Prop := fun k u =>
    u.status = .running ∧ k ≤ L ∧ u.regs 2 = 1 ∧ u.regs 9 = 2 ∧
      u.regs 20 = x / 2 ^ (L - k) ∧ u.regs dst = L - k ∧
      u.regs 21 = (if 1 < x / 2 ^ (L - k) then 1 else 0) ∧
      u.memory = s.memory ∧ u.extent = s.extent ∧
      (∀ r : Nat, r ≠ (dst : Nat) → r ≠ 20 → r ≠ 21 → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ0 : Q L t3 := by
    refine ⟨t3s, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, t3m, t3e, ?_, t3k.2, t3k.1⟩
    · rw [t3r, put_ne _ _ (by decide), t2one]
    · rw [t3r, put_ne _ _ (by decide), t2two]
    · rw [t3r, put_ne _ _ (by decide), t2lx, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    · rw [t3r, put_ne _ _ (fun h => hd21 h), t2dst, Nat.sub_self]
    · rw [t3r, put_same, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    · intro r hd h20 h21
      rw [t3r, put_ne _ _ h21, t2r, put_ne _ _ hd, t1r, put_ne _ _ h20]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rLC (log2Body dst) 3
    (fun k u hu => hu.1)
    (fun k u hu => by
      obtain ⟨_, hkL, _, _, _, _, hlc, _⟩ := hu
      simp only [operand_val_21]
      rw [hlc]
      have hx0 : x ≠ 0 := by intro h; rw [h, Nat.log2_zero] at hL; omega
      have := div_pow_ge_two_of_log2 hx0 hL.symm hkL
      rw [if_pos (by omega)]; decide)
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, hlc, _⟩ := hu
      simp only [operand_val_21]
      rw [hlc, Nat.sub_zero, if_neg (by have := div_pow_log2_lt_two x; rw [hL] at this; omega)])
    (by
      intro k u hu
      obtain ⟨hurun, hkL, huone, hutwo, hulx, hudst, _, humem, huext, hufr, hukr, huk⟩ := hu
      let u1 := execPrim (Prim.arithmetic .div rLX rLX rTWO) u
      have g1 := exec_arithmetic u .div rLX rLX rTWO
      let u2 := execPrim (Prim.arithmetic .add dst dst rONE) u1
      have g2 := exec_arithmetic u1 .add dst dst rONE
      let u3 := execPrim (Prim.comparison .lt rLC rONE rLX) u2
      have g3 := exec_comparison u2 .lt rLC rONE rLX
      have hdiv : x / 2 ^ (L - (k + 1)) / 2 = x / 2 ^ (L - k) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; congr 2; omega
      have u1r : u1.regs = put u.regs 20 (x / 2 ^ (L - k)) := by
        simp [u1, g1, Arithmetic.eval, hulx, hutwo, hdiv]
      have u1dst : u1.regs dst = L - (k + 1) := by rw [u1r, put_ne _ _ hd20, hudst]
      have u1one : u1.regs 2 = 1 := by rw [u1r, put_ne _ _ (by decide), huone]
      have u2r : u2.regs = put u1.regs dst (L - k) := by
        show (execPrim (Prim.arithmetic .add dst dst rONE) u1).regs = _
        rw [g2]
        show put u1.regs dst (u1.regs dst + u1.regs 2) = _
        rw [u1dst, u1one, show L - (k + 1) + 1 = L - k by omega]
      have u2one : u2.regs 2 = 1 := by rw [u2r, put_ne _ _ n2, u1one]
      have u2two : u2.regs 9 = 2 := by
        rw [u2r, put_ne _ _ n9, u1r, put_ne _ _ (by decide), hutwo]
      have u2lx : u2.regs 20 = x / 2 ^ (L - k) := by rw [u2r, put_ne _ _ n20, u1r, put_same]
      have u3r : u3.regs = put u2.regs 21 (if 1 < x / 2 ^ (L - k) then 1 else 0) := by
        simp [u3, g3, Comparison.eval, u2one, u2lx]
      have u3s : u3.status = .running := by simp [u3, g3, u2, g2, u1, g1, hurun]
      have hsafe : ActsOK (Action.Safe W) [.arithmetic .div rLX rLX rTWO,
          .arithmetic .add dst dst rONE, .comparison .lt rLC rONE rLX] u := by
        refine ⟨safe_div hW u _ _ _ ?_ (by simp [hutwo]),
          by simp [Action.prim, exec_arithmetic, hurun], ?_⟩
        · simp only [operand_val_20]; rw [hulx]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxW
        refine ⟨safe_add hW u1 _ _ _ ?_, by simp [Action.prim, exec_arithmetic, hurun], ?_⟩
        · show u1.regs dst + u1.regs 2 < 2 ^ W
          rw [u1dst, u1one]; omega
        exact ⟨safe_comparison hW u2 _ _ _ _, u3s, trivial⟩
      refine ⟨u3, 3, acts_evalG (P := Action.Safe W) _ u hurun hsafe, Nat.le_refl _, u3s,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u3r, put_ne _ _ (by decide), u2one]
      · rw [u3r, put_ne _ _ (by decide), u2two]
      · rw [u3r, put_ne _ _ (by decide), u2lx]
      · rw [u3r, put_ne _ _ (fun h => hd21 h), u2r, put_same]
      · rw [u3r, put_same]
      · simp [u3, g3, u2, g2, u1, g1, humem]
      · simp [u3, g3, u2, g2, u1, g1, huext]
      · intro r hd h20 h21
        rw [u3r, put_ne _ _ h21, u2r, put_ne _ _ hd, u1r, put_ne _ _ h20, hufr r hd h20 h21]
      · simp [u3, g3, u2, g2, u1, g1, hukr]
      · simp [u3, g3, u2, g2, u1, g1, huk])
    L t3 hQ0
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨hs'run, _, _, _, hs'lx, hs'dst, hs'lc, hs'mem, hs'ext, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', 3 + j, EvalG.seq hinit hl, ?_, hs'run, ?_, hs'mem, hs'ext, hs'k, hs'kr⟩
  · have : L * (3 + 2) = 5 * L := by rw [Nat.mul_comm]
    omega
  · funext r
    rw [Nat.sub_zero] at hs'lx hs'dst hs'lc
    by_cases hrd : r = dst
    · subst hrd; rw [put_same, hs'dst]
    · rw [put_ne _ _ hrd]
      by_cases h21 : r = 21
      · subst h21; rw [put_same, hs'lc, if_neg (by have := div_pow_log2_lt_two x; rw [hL] at this; omega)]
      · rw [put_ne _ _ h21]
        by_cases h20 : r = 20
        · subst h20; rw [put_same, hs'lx]
        · rw [put_ne _ _ h20, hs'fr r hrd h20 h21]

/-! ## Register literals 41-199 -/

@[simp] theorem operand_val_41 : ((41 : Operand) : Nat) = 41 := rfl
@[simp] theorem operand_val_42 : ((42 : Operand) : Nat) = 42 := rfl
@[simp] theorem operand_val_43 : ((43 : Operand) : Nat) = 43 := rfl
@[simp] theorem operand_val_44 : ((44 : Operand) : Nat) = 44 := rfl
@[simp] theorem operand_val_45 : ((45 : Operand) : Nat) = 45 := rfl
@[simp] theorem operand_val_46 : ((46 : Operand) : Nat) = 46 := rfl
@[simp] theorem operand_val_47 : ((47 : Operand) : Nat) = 47 := rfl
@[simp] theorem operand_val_48 : ((48 : Operand) : Nat) = 48 := rfl
@[simp] theorem operand_val_49 : ((49 : Operand) : Nat) = 49 := rfl
@[simp] theorem operand_val_50 : ((50 : Operand) : Nat) = 50 := rfl
@[simp] theorem operand_val_51 : ((51 : Operand) : Nat) = 51 := rfl
@[simp] theorem operand_val_52 : ((52 : Operand) : Nat) = 52 := rfl
@[simp] theorem operand_val_53 : ((53 : Operand) : Nat) = 53 := rfl
@[simp] theorem operand_val_54 : ((54 : Operand) : Nat) = 54 := rfl
@[simp] theorem operand_val_55 : ((55 : Operand) : Nat) = 55 := rfl
@[simp] theorem operand_val_56 : ((56 : Operand) : Nat) = 56 := rfl
@[simp] theorem operand_val_57 : ((57 : Operand) : Nat) = 57 := rfl
@[simp] theorem operand_val_58 : ((58 : Operand) : Nat) = 58 := rfl
@[simp] theorem operand_val_59 : ((59 : Operand) : Nat) = 59 := rfl
@[simp] theorem operand_val_60 : ((60 : Operand) : Nat) = 60 := rfl
@[simp] theorem operand_val_61 : ((61 : Operand) : Nat) = 61 := rfl
@[simp] theorem operand_val_62 : ((62 : Operand) : Nat) = 62 := rfl
@[simp] theorem operand_val_63 : ((63 : Operand) : Nat) = 63 := rfl
@[simp] theorem operand_val_64 : ((64 : Operand) : Nat) = 64 := rfl
@[simp] theorem operand_val_65 : ((65 : Operand) : Nat) = 65 := rfl
@[simp] theorem operand_val_66 : ((66 : Operand) : Nat) = 66 := rfl
@[simp] theorem operand_val_67 : ((67 : Operand) : Nat) = 67 := rfl
@[simp] theorem operand_val_68 : ((68 : Operand) : Nat) = 68 := rfl
@[simp] theorem operand_val_69 : ((69 : Operand) : Nat) = 69 := rfl
@[simp] theorem operand_val_70 : ((70 : Operand) : Nat) = 70 := rfl
@[simp] theorem operand_val_71 : ((71 : Operand) : Nat) = 71 := rfl
@[simp] theorem operand_val_72 : ((72 : Operand) : Nat) = 72 := rfl
@[simp] theorem operand_val_73 : ((73 : Operand) : Nat) = 73 := rfl
@[simp] theorem operand_val_74 : ((74 : Operand) : Nat) = 74 := rfl
@[simp] theorem operand_val_75 : ((75 : Operand) : Nat) = 75 := rfl
@[simp] theorem operand_val_76 : ((76 : Operand) : Nat) = 76 := rfl
@[simp] theorem operand_val_77 : ((77 : Operand) : Nat) = 77 := rfl
@[simp] theorem operand_val_78 : ((78 : Operand) : Nat) = 78 := rfl
@[simp] theorem operand_val_79 : ((79 : Operand) : Nat) = 79 := rfl
@[simp] theorem operand_val_80 : ((80 : Operand) : Nat) = 80 := rfl
@[simp] theorem operand_val_81 : ((81 : Operand) : Nat) = 81 := rfl
@[simp] theorem operand_val_82 : ((82 : Operand) : Nat) = 82 := rfl
@[simp] theorem operand_val_83 : ((83 : Operand) : Nat) = 83 := rfl
@[simp] theorem operand_val_84 : ((84 : Operand) : Nat) = 84 := rfl
@[simp] theorem operand_val_85 : ((85 : Operand) : Nat) = 85 := rfl
@[simp] theorem operand_val_86 : ((86 : Operand) : Nat) = 86 := rfl
@[simp] theorem operand_val_87 : ((87 : Operand) : Nat) = 87 := rfl
@[simp] theorem operand_val_88 : ((88 : Operand) : Nat) = 88 := rfl
@[simp] theorem operand_val_89 : ((89 : Operand) : Nat) = 89 := rfl
@[simp] theorem operand_val_90 : ((90 : Operand) : Nat) = 90 := rfl
@[simp] theorem operand_val_91 : ((91 : Operand) : Nat) = 91 := rfl
@[simp] theorem operand_val_92 : ((92 : Operand) : Nat) = 92 := rfl
@[simp] theorem operand_val_93 : ((93 : Operand) : Nat) = 93 := rfl
@[simp] theorem operand_val_94 : ((94 : Operand) : Nat) = 94 := rfl
@[simp] theorem operand_val_95 : ((95 : Operand) : Nat) = 95 := rfl
@[simp] theorem operand_val_96 : ((96 : Operand) : Nat) = 96 := rfl
@[simp] theorem operand_val_97 : ((97 : Operand) : Nat) = 97 := rfl
@[simp] theorem operand_val_98 : ((98 : Operand) : Nat) = 98 := rfl
@[simp] theorem operand_val_99 : ((99 : Operand) : Nat) = 99 := rfl
@[simp] theorem operand_val_100 : ((100 : Operand) : Nat) = 100 := rfl
@[simp] theorem operand_val_101 : ((101 : Operand) : Nat) = 101 := rfl
@[simp] theorem operand_val_102 : ((102 : Operand) : Nat) = 102 := rfl
@[simp] theorem operand_val_103 : ((103 : Operand) : Nat) = 103 := rfl
@[simp] theorem operand_val_104 : ((104 : Operand) : Nat) = 104 := rfl
@[simp] theorem operand_val_105 : ((105 : Operand) : Nat) = 105 := rfl
@[simp] theorem operand_val_106 : ((106 : Operand) : Nat) = 106 := rfl
@[simp] theorem operand_val_107 : ((107 : Operand) : Nat) = 107 := rfl
@[simp] theorem operand_val_108 : ((108 : Operand) : Nat) = 108 := rfl
@[simp] theorem operand_val_109 : ((109 : Operand) : Nat) = 109 := rfl
@[simp] theorem operand_val_110 : ((110 : Operand) : Nat) = 110 := rfl
@[simp] theorem operand_val_111 : ((111 : Operand) : Nat) = 111 := rfl
@[simp] theorem operand_val_112 : ((112 : Operand) : Nat) = 112 := rfl
@[simp] theorem operand_val_113 : ((113 : Operand) : Nat) = 113 := rfl
@[simp] theorem operand_val_114 : ((114 : Operand) : Nat) = 114 := rfl
@[simp] theorem operand_val_115 : ((115 : Operand) : Nat) = 115 := rfl
@[simp] theorem operand_val_116 : ((116 : Operand) : Nat) = 116 := rfl
@[simp] theorem operand_val_117 : ((117 : Operand) : Nat) = 117 := rfl
@[simp] theorem operand_val_118 : ((118 : Operand) : Nat) = 118 := rfl
@[simp] theorem operand_val_119 : ((119 : Operand) : Nat) = 119 := rfl
@[simp] theorem operand_val_120 : ((120 : Operand) : Nat) = 120 := rfl
@[simp] theorem operand_val_121 : ((121 : Operand) : Nat) = 121 := rfl
@[simp] theorem operand_val_122 : ((122 : Operand) : Nat) = 122 := rfl
@[simp] theorem operand_val_123 : ((123 : Operand) : Nat) = 123 := rfl
@[simp] theorem operand_val_124 : ((124 : Operand) : Nat) = 124 := rfl
@[simp] theorem operand_val_125 : ((125 : Operand) : Nat) = 125 := rfl
@[simp] theorem operand_val_126 : ((126 : Operand) : Nat) = 126 := rfl
@[simp] theorem operand_val_127 : ((127 : Operand) : Nat) = 127 := rfl
@[simp] theorem operand_val_128 : ((128 : Operand) : Nat) = 128 := rfl
@[simp] theorem operand_val_129 : ((129 : Operand) : Nat) = 129 := rfl
@[simp] theorem operand_val_130 : ((130 : Operand) : Nat) = 130 := rfl
@[simp] theorem operand_val_131 : ((131 : Operand) : Nat) = 131 := rfl
@[simp] theorem operand_val_132 : ((132 : Operand) : Nat) = 132 := rfl
@[simp] theorem operand_val_133 : ((133 : Operand) : Nat) = 133 := rfl
@[simp] theorem operand_val_134 : ((134 : Operand) : Nat) = 134 := rfl
@[simp] theorem operand_val_135 : ((135 : Operand) : Nat) = 135 := rfl
@[simp] theorem operand_val_136 : ((136 : Operand) : Nat) = 136 := rfl
@[simp] theorem operand_val_137 : ((137 : Operand) : Nat) = 137 := rfl
@[simp] theorem operand_val_138 : ((138 : Operand) : Nat) = 138 := rfl
@[simp] theorem operand_val_139 : ((139 : Operand) : Nat) = 139 := rfl
@[simp] theorem operand_val_140 : ((140 : Operand) : Nat) = 140 := rfl
@[simp] theorem operand_val_141 : ((141 : Operand) : Nat) = 141 := rfl
@[simp] theorem operand_val_142 : ((142 : Operand) : Nat) = 142 := rfl
@[simp] theorem operand_val_143 : ((143 : Operand) : Nat) = 143 := rfl
@[simp] theorem operand_val_144 : ((144 : Operand) : Nat) = 144 := rfl
@[simp] theorem operand_val_145 : ((145 : Operand) : Nat) = 145 := rfl
@[simp] theorem operand_val_146 : ((146 : Operand) : Nat) = 146 := rfl
@[simp] theorem operand_val_147 : ((147 : Operand) : Nat) = 147 := rfl
@[simp] theorem operand_val_148 : ((148 : Operand) : Nat) = 148 := rfl
@[simp] theorem operand_val_149 : ((149 : Operand) : Nat) = 149 := rfl
@[simp] theorem operand_val_150 : ((150 : Operand) : Nat) = 150 := rfl
@[simp] theorem operand_val_151 : ((151 : Operand) : Nat) = 151 := rfl
@[simp] theorem operand_val_152 : ((152 : Operand) : Nat) = 152 := rfl
@[simp] theorem operand_val_153 : ((153 : Operand) : Nat) = 153 := rfl
@[simp] theorem operand_val_154 : ((154 : Operand) : Nat) = 154 := rfl
@[simp] theorem operand_val_155 : ((155 : Operand) : Nat) = 155 := rfl
@[simp] theorem operand_val_156 : ((156 : Operand) : Nat) = 156 := rfl
@[simp] theorem operand_val_157 : ((157 : Operand) : Nat) = 157 := rfl
@[simp] theorem operand_val_158 : ((158 : Operand) : Nat) = 158 := rfl
@[simp] theorem operand_val_159 : ((159 : Operand) : Nat) = 159 := rfl
@[simp] theorem operand_val_160 : ((160 : Operand) : Nat) = 160 := rfl
@[simp] theorem operand_val_161 : ((161 : Operand) : Nat) = 161 := rfl
@[simp] theorem operand_val_162 : ((162 : Operand) : Nat) = 162 := rfl
@[simp] theorem operand_val_163 : ((163 : Operand) : Nat) = 163 := rfl
@[simp] theorem operand_val_164 : ((164 : Operand) : Nat) = 164 := rfl
@[simp] theorem operand_val_165 : ((165 : Operand) : Nat) = 165 := rfl
@[simp] theorem operand_val_166 : ((166 : Operand) : Nat) = 166 := rfl
@[simp] theorem operand_val_167 : ((167 : Operand) : Nat) = 167 := rfl
@[simp] theorem operand_val_168 : ((168 : Operand) : Nat) = 168 := rfl
@[simp] theorem operand_val_169 : ((169 : Operand) : Nat) = 169 := rfl
@[simp] theorem operand_val_170 : ((170 : Operand) : Nat) = 170 := rfl
@[simp] theorem operand_val_171 : ((171 : Operand) : Nat) = 171 := rfl
@[simp] theorem operand_val_172 : ((172 : Operand) : Nat) = 172 := rfl
@[simp] theorem operand_val_173 : ((173 : Operand) : Nat) = 173 := rfl
@[simp] theorem operand_val_174 : ((174 : Operand) : Nat) = 174 := rfl
@[simp] theorem operand_val_175 : ((175 : Operand) : Nat) = 175 := rfl
@[simp] theorem operand_val_176 : ((176 : Operand) : Nat) = 176 := rfl
@[simp] theorem operand_val_177 : ((177 : Operand) : Nat) = 177 := rfl
@[simp] theorem operand_val_178 : ((178 : Operand) : Nat) = 178 := rfl
@[simp] theorem operand_val_179 : ((179 : Operand) : Nat) = 179 := rfl
@[simp] theorem operand_val_180 : ((180 : Operand) : Nat) = 180 := rfl
@[simp] theorem operand_val_181 : ((181 : Operand) : Nat) = 181 := rfl
@[simp] theorem operand_val_182 : ((182 : Operand) : Nat) = 182 := rfl
@[simp] theorem operand_val_183 : ((183 : Operand) : Nat) = 183 := rfl
@[simp] theorem operand_val_184 : ((184 : Operand) : Nat) = 184 := rfl
@[simp] theorem operand_val_185 : ((185 : Operand) : Nat) = 185 := rfl
@[simp] theorem operand_val_186 : ((186 : Operand) : Nat) = 186 := rfl
@[simp] theorem operand_val_187 : ((187 : Operand) : Nat) = 187 := rfl
@[simp] theorem operand_val_188 : ((188 : Operand) : Nat) = 188 := rfl
@[simp] theorem operand_val_189 : ((189 : Operand) : Nat) = 189 := rfl
@[simp] theorem operand_val_190 : ((190 : Operand) : Nat) = 190 := rfl
@[simp] theorem operand_val_191 : ((191 : Operand) : Nat) = 191 := rfl
@[simp] theorem operand_val_192 : ((192 : Operand) : Nat) = 192 := rfl
@[simp] theorem operand_val_193 : ((193 : Operand) : Nat) = 193 := rfl
@[simp] theorem operand_val_194 : ((194 : Operand) : Nat) = 194 := rfl
@[simp] theorem operand_val_195 : ((195 : Operand) : Nat) = 195 := rfl
@[simp] theorem operand_val_196 : ((196 : Operand) : Nat) = 196 := rfl
@[simp] theorem operand_val_197 : ((197 : Operand) : Nat) = 197 := rfl
@[simp] theorem operand_val_198 : ((198 : Operand) : Nat) = 198 := rfl
@[simp] theorem operand_val_199 : ((199 : Operand) : Nat) = 199 := rfl
@[simp] theorem operand_val_513 : ((513 : Operand) : Nat) = 513 := rfl
@[simp] theorem operand_val_561 : ((561 : Operand) : Nat) = 561 := rfl
@[simp] theorem operand_val_1180 : ((1180 : Operand) : Nat) = 1180 := rfl

end RMQ.SuccinctFinal.PackedConstruction.Proof

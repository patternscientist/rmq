import RMQ.Core.WordRAM.Construction.Builder.Emit

/-! # PRE-1 builder proofs: shared calculus for source blocks

Outside the builder firewall. Facts about `Structured.EvalG` evaluations of the
builder's source blocks that every stage specification uses:

* straight-line action lists (`acts`) evaluate to `execActs` at exactly their
  length when every intermediate state keeps running (`acts_evalG`);
* the register frame of any block from its syntactic `Block.WritesOnly` fact
  (`EvalG.regs_frame`), and the key bank is never changed (`EvalG.keys_eq`);
* `Emits s₀ s vals`: the state `s` is `s₀` with exactly the cells `vals`
  appended at the old extent, everything else in memory unchanged, and its
  composition law `Emits.trans`;
* safety of the individual actions at their pre-states (`Action.Safe`).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-! ## Register literals and single-step state equations -/

@[simp] theorem operand_val_0 : ((0 : Operand) : Nat) = 0 := rfl
@[simp] theorem operand_val_1 : ((1 : Operand) : Nat) = 1 := rfl
@[simp] theorem operand_val_2 : ((2 : Operand) : Nat) = 2 := rfl
@[simp] theorem operand_val_3 : ((3 : Operand) : Nat) = 3 := rfl
@[simp] theorem operand_val_4 : ((4 : Operand) : Nat) = 4 := rfl
@[simp] theorem operand_val_5 : ((5 : Operand) : Nat) = 5 := rfl
@[simp] theorem operand_val_6 : ((6 : Operand) : Nat) = 6 := rfl
@[simp] theorem operand_val_7 : ((7 : Operand) : Nat) = 7 := rfl
@[simp] theorem operand_val_8 : ((8 : Operand) : Nat) = 8 := rfl
@[simp] theorem operand_val_9 : ((9 : Operand) : Nat) = 9 := rfl
@[simp] theorem operand_val_10 : ((10 : Operand) : Nat) = 10 := rfl
@[simp] theorem operand_val_11 : ((11 : Operand) : Nat) = 11 := rfl
@[simp] theorem operand_val_12 : ((12 : Operand) : Nat) = 12 := rfl
@[simp] theorem operand_val_13 : ((13 : Operand) : Nat) = 13 := rfl
@[simp] theorem operand_val_14 : ((14 : Operand) : Nat) = 14 := rfl
@[simp] theorem operand_val_15 : ((15 : Operand) : Nat) = 15 := rfl
@[simp] theorem operand_val_16 : ((16 : Operand) : Nat) = 16 := rfl
@[simp] theorem operand_val_17 : ((17 : Operand) : Nat) = 17 := rfl
@[simp] theorem operand_val_18 : ((18 : Operand) : Nat) = 18 := rfl
@[simp] theorem operand_val_19 : ((19 : Operand) : Nat) = 19 := rfl
@[simp] theorem operand_val_20 : ((20 : Operand) : Nat) = 20 := rfl
@[simp] theorem operand_val_21 : ((21 : Operand) : Nat) = 21 := rfl
@[simp] theorem operand_val_22 : ((22 : Operand) : Nat) = 22 := rfl
@[simp] theorem operand_val_23 : ((23 : Operand) : Nat) = 23 := rfl
@[simp] theorem operand_val_24 : ((24 : Operand) : Nat) = 24 := rfl
@[simp] theorem operand_val_25 : ((25 : Operand) : Nat) = 25 := rfl
@[simp] theorem operand_val_26 : ((26 : Operand) : Nat) = 26 := rfl
@[simp] theorem operand_val_27 : ((27 : Operand) : Nat) = 27 := rfl
@[simp] theorem operand_val_28 : ((28 : Operand) : Nat) = 28 := rfl
@[simp] theorem operand_val_29 : ((29 : Operand) : Nat) = 29 := rfl
@[simp] theorem operand_val_30 : ((30 : Operand) : Nat) = 30 := rfl
@[simp] theorem operand_val_31 : ((31 : Operand) : Nat) = 31 := rfl
@[simp] theorem operand_val_32 : ((32 : Operand) : Nat) = 32 := rfl
@[simp] theorem operand_val_33 : ((33 : Operand) : Nat) = 33 := rfl
@[simp] theorem operand_val_34 : ((34 : Operand) : Nat) = 34 := rfl
@[simp] theorem operand_val_35 : ((35 : Operand) : Nat) = 35 := rfl
@[simp] theorem operand_val_36 : ((36 : Operand) : Nat) = 36 := rfl
@[simp] theorem operand_val_37 : ((37 : Operand) : Nat) = 37 := rfl
@[simp] theorem operand_val_38 : ((38 : Operand) : Nat) = 38 := rfl
@[simp] theorem operand_val_39 : ((39 : Operand) : Nat) = 39 := rfl
@[simp] theorem operand_val_40 : ((40 : Operand) : Nat) = 40 := rfl

@[simp] theorem put_same {α : Type} (f : Nat → α) (a : Nat) (v : α) : put f a v a = v := by
  simp [put]

theorem put_ne {α : Type} (f : Nat → α) {a b : Nat} (v : α) (h : b ≠ a) : put f a v b = f b := by
  simp [put, h]

theorem exec_constant (s : State) (d v : Operand) :
    execPrim (.constant d v) s = { s with regs := put s.regs d v.val, pc := s.pc + 1 } := rfl

theorem exec_move (s : State) (d src : Operand) :
    execPrim (.move d src) s = { s with regs := put s.regs d (s.regs src), pc := s.pc + 1 } := rfl

theorem exec_arithmetic (s : State) (op : Arithmetic) (d l r : Operand) :
    execPrim (.arithmetic op d l r) s =
      { s with regs := put s.regs d (op.eval (s.regs l) (s.regs r)), pc := s.pc + 1 } := rfl

theorem exec_comparison (s : State) (op : Comparison) (d l r : Operand) :
    execPrim (.comparison op d l r) s =
      { s with regs := put s.regs d (op.eval (s.regs l) (s.regs r)), pc := s.pc + 1 } := rfl

theorem exec_reserve (s : State) (d : Operand) :
    execPrim (.reserve d) s =
      { s with regs := put s.regs d s.extent, extent := s.extent + 1, pc := s.pc + 1 } := rfl

theorem exec_store (s : State) (a v : Operand) (h : s.regs a < s.extent) :
    execPrim (.store a v) s =
      { s with memory := put s.memory (s.regs a) (some (s.regs v)), pc := s.pc + 1 } := by
  simp [execPrim, h, State.next]

theorem exec_load (s : State) (d a : Operand) {v : Nat} (h : s.regs a < s.extent)
    (hm : s.memory (s.regs a) = some v) :
    execPrim (.load d a) s = { s with regs := put s.regs d v, pc := s.pc + 1 } := by
  simp [execPrim, h, hm, State.writeNext, State.next]

/-! ## Action lists -/

/-- Symbolic execution of an action list. -/
def execActs : List Action → State → State
  | [], s => s
  | a :: rest, s => execActs rest (execPrim a.prim s)

/-- Every action of the list satisfies `P` at its pre-state and leaves the state running. -/
def ActsOK (P : State → Action → Prop) : List Action → State → Prop
  | [], _ => True
  | a :: rest, s => P s a ∧ (execPrim a.prim s).status = .running ∧ ActsOK P rest (execPrim a.prim s)

theorem acts_evalG {P : State → Action → Prop} :
    ∀ (ops : List Action) (s : State), s.status = .running → ActsOK P ops s →
      EvalG P (acts ops) s (execActs ops s) ops.length
  | [], s, h, _ => EvalG.skip s h
  | [a], s, h, ⟨hp, _, _⟩ => EvalG.action a s h hp
  | a :: b :: rest, s, h, ⟨hp, hr, hok⟩ => by
      have hrest := acts_evalG (b :: rest) (execPrim a.prim s) hr hok
      have hseq := EvalG.seq (EvalG.action a s h hp) hrest
      have hlen : 1 + (b :: rest).length = (a :: b :: rest).length := by
        simp only [List.length_cons]; omega
      rw [hlen] at hseq
      exact hseq

theorem execActs_running {P : State → Action → Prop} :
    ∀ (ops : List Action) (s : State), s.status = .running → ActsOK P ops s →
      (execActs ops s).status = .running
  | [], _, h, _ => h
  | _ :: rest, _, _, ⟨_, hr, hok⟩ => execActs_running rest _ hr hok

theorem execActs_append (ops ops' : List Action) (s : State) :
    execActs (ops ++ ops') s = execActs ops' (execActs ops s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih _

/-! ## Frames -/

theorem EvalG.regs_frame {P : State → Action → Prop} {b : Block} {s s' : State} {k : Nat}
    (h : EvalG P b s s' k) (allowed : Nat → Prop) (hw : b.WritesOnly allowed)
    (r : Nat) (hr : ¬ allowed r) : s'.regs r = s.regs r := by
  induction h with
  | stopped => rfl
  | skip => rfl
  | action op s _ _ => exact execPrim_frame op.prim s allowed hw r hr
  | exit => rfl
  | seq _ _ iha ihb => rw [ihb hw.2, iha hw.1]
  | ifZeroTaken _ _ _ ih => exact ih hw.1
  | ifZeroFallthrough _ _ _ _ ih => exact ih hw.2
  | ifZeroFallthroughStopped _ _ _ _ ih => exact ih hw.2
  | loopExit => rfl
  | loopStep _ _ _ _ _ ihb ihr => rw [ihr hw, ihb hw]
  | loopStopped _ _ _ _ ih => exact ih hw

theorem EvalG.keys_eq {P : State → Action → Prop} {b : Block} {s s' : State} {k : Nat}
    (h : EvalG P b s s' k) : s'.keys = s.keys := by
  induction h with
  | stopped => rfl
  | skip => rfl
  | action op s _ _ => exact execPrim_keys op.prim s
  | exit => rfl
  | seq _ _ iha ihb => rw [ihb, iha]
  | ifZeroTaken _ _ _ ih => exact ih
  | ifZeroFallthrough _ _ _ _ ih => exact ih
  | ifZeroFallthroughStopped _ _ _ _ ih => exact ih
  | loopExit => rfl
  | loopStep _ _ _ _ _ ihb ihr => rw [ihr, ihb]
  | loopStopped _ _ _ _ ih => exact ih

/-! ## Emission -/

/-- `s` is `s₀` with exactly `vals` appended at the old extent. -/
def Emits (s₀ s : State) (vals : List Nat) : Prop :=
  s.extent = s₀.extent + vals.length ∧
    ∀ a, s.memory a =
      if s₀.extent ≤ a ∧ a < s₀.extent + vals.length then vals[a - s₀.extent]? else s₀.memory a

theorem Emits.refl (s : State) : Emits s s [] := by
  refine ⟨by simp, fun a => ?_⟩
  have hout : ¬ (s.extent ≤ a ∧ a < s.extent + ([] : List Nat).length) := by
    simp only [List.length_nil, Nat.add_zero]; omega
  rw [if_neg hout]

theorem Emits.trans {s₀ s₁ s₂ : State} {v w : List Nat} (h₁ : Emits s₀ s₁ v)
    (h₂ : Emits s₁ s₂ w) : Emits s₀ s₂ (v ++ w) := by
  obtain ⟨he₁, hm₁⟩ := h₁
  obtain ⟨he₂, hm₂⟩ := h₂
  refine ⟨by simp [he₂, he₁, Nat.add_assoc], fun a => ?_⟩
  rw [hm₂ a, hm₁ a, he₁]
  simp only [List.length_append]
  by_cases hlo : s₀.extent ≤ a
  · by_cases hv : a < s₀.extent + v.length
    · have hin : s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length) := ⟨hlo, by omega⟩
      have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
      rw [if_neg hout, if_pos ⟨hlo, hv⟩, if_pos hin, List.getElem?_append_left (by omega)]
    · by_cases hw : a < s₀.extent + v.length + w.length
      · have hin : s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length) := ⟨hlo, by omega⟩
        rw [if_pos ⟨by omega, hw⟩, if_pos hin, List.getElem?_append_right (by omega)]
        congr 1
        omega
      · have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
        have hout' : ¬ (s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length)) := by omega
        rw [if_neg hout, if_neg (by omega), if_neg hout']
  · have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
    rw [if_neg hout, if_neg (by omega), if_neg (by omega)]

/-- Memory below the old extent is unchanged by an emission. -/
theorem Emits.memory_below {s₀ s : State} {vals : List Nat} (h : Emits s₀ s vals)
    {a : Nat} (ha : a < s₀.extent) : s.memory a = s₀.memory a := by
  rw [h.2 a, if_neg (by omega)]

/-- The emitted cells hold exactly `vals`. -/
theorem Emits.memory_at {s₀ s : State} {vals : List Nat} (h : Emits s₀ s vals)
    {i : Nat} (hi : i < vals.length) : s.memory (s₀.extent + i) = some vals[i] := by
  rw [h.2, if_pos ⟨by omega, by omega⟩]
  simp [List.getElem?_eq_getElem hi]

/-! ## Safety of individual actions -/

theorem safe_move {W : Nat} (hW : 32 ≤ W) (s : State) (d src : Operand) :
    Action.Safe W s (.move d src) := ⟨Prim.operandsFit_of_width _ hW, trivial⟩

theorem safe_constant {W : Nat} (hW : 32 ≤ W) (s : State) (d v : Operand) :
    Action.Safe W s (.constant d v) := ⟨Prim.operandsFit_of_width _ hW, trivial⟩

theorem safe_comparison {W : Nat} (hW : 32 ≤ W) (s : State) (op : Comparison) (d l r : Operand) :
    Action.Safe W s (.comparison op d l r) := ⟨Prim.operandsFit_of_width _ hW, trivial⟩

theorem safe_reserve {W : Nat} (hW : 32 ≤ W) (s : State) (d : Operand)
    (h : s.extent + 1 < 2 ^ W) : Action.Safe W s (.reserve d) :=
  ⟨Prim.operandsFit_of_width _ hW, h⟩

theorem safe_store {W : Nat} (hW : 32 ≤ W) (s : State) (a v : Operand)
    (ha : s.regs a < s.extent) (hv : s.regs v < 2 ^ W) : Action.Safe W s (.store a v) :=
  ⟨Prim.operandsFit_of_width _ hW, ha, hv⟩

theorem safe_add {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (h : s.regs l + s.regs r < 2 ^ W) : Action.Safe W s (.arithmetic .add d l r) :=
  ⟨Prim.operandsFit_of_width _ hW, h, by simp, by simp, by simp⟩

theorem safe_sub {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (hle : s.regs r ≤ s.regs l) (hl : s.regs l < 2 ^ W) :
    Action.Safe W s (.arithmetic .sub d l r) :=
  ⟨Prim.operandsFit_of_width _ hW, by show s.regs l - s.regs r < 2 ^ W; omega,
    fun _ => hle, by simp, by simp⟩

theorem safe_mul {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (h : s.regs l * s.regs r < 2 ^ W) : Action.Safe W s (.arithmetic .mul d l r) :=
  ⟨Prim.operandsFit_of_width _ hW, h, by simp, by simp, by simp⟩

theorem safe_div {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (hl : s.regs l < 2 ^ W) (hr : 0 < s.regs r) : Action.Safe W s (.arithmetic .div d l r) :=
  ⟨Prim.operandsFit_of_width _ hW,
    by show s.regs l / s.regs r < 2 ^ W; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hl,
    by simp, fun _ => hr, by simp⟩

theorem safe_mod {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (hl : s.regs l < 2 ^ W) (hr : 0 < s.regs r) : Action.Safe W s (.arithmetic .mod d l r) :=
  ⟨Prim.operandsFit_of_width _ hW,
    by show s.regs l % s.regs r < 2 ^ W; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hl,
    by simp, fun _ => hr, by simp⟩

theorem safe_shl {W : Nat} (hW : 32 ≤ W) (s : State) (d l r : Operand)
    (hr : s.regs r < W) (h : Nat.shiftLeft (s.regs l) (s.regs r) < 2 ^ W) :
    Action.Safe W s (.arithmetic .shl d l r) :=
  ⟨Prim.operandsFit_of_width _ hW, h, by simp, by simp, fun _ => hr⟩

end RMQ.SuccinctFinal.PackedConstruction.Proof

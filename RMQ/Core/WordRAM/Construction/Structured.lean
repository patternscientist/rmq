import RMQ.Core.WordRAM.Construction.Calculus
import RMQ.Core.WordRAM.Construction.Safety

/-! # Finite structured source for the construction program

The source language has scalar actions (the nine non-control primitives), a
halt, sequencing, a zero test and a top-tested `while` loop. It compiles to a
fixed instruction list with resolved branch targets; the compiler theorem in
`Compiler.lean` relates the relational, cost-carrying big-step semantics
`EvalG` below to actual `run` segments transition for transition. The semantics
is parametrized by a per-action side condition so that plain evaluation and
safe evaluation (`Action.Safe`) are one relation. The program counter of a
result state of `EvalG` is not meaningful; the compiler theorem fixes it.
`evalF` is an executable, fuel-indexed evaluator sound for `Eval`, used only
to reduce straight-line source blocks by simplification; it is never the
charged interpreter.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Structured

inductive Action where
  | load (dst address : Operand)
  | constant (dst value : Operand)
  | move (dst src : Operand)
  | arithmetic (op : Arithmetic) (dst lhs rhs : Operand)
  | comparison (op : Comparison) (dst lhs rhs : Operand)
  | store (address value : Operand)
  | reserve (dst : Operand)
  | loadKey (dst address : Operand)
  | compareKey (dst lhs rhs : Operand)
deriving Repr, DecidableEq

def Action.prim : Action → Prim
  | .load dst address => .load dst address
  | .constant dst value => .constant dst value
  | .move dst src => .move dst src
  | .arithmetic op dst lhs rhs => .arithmetic op dst lhs rhs
  | .comparison op dst lhs rhs => .comparison op dst lhs rhs
  | .store address value => .store address value
  | .reserve dst => .reserve dst
  | .loadKey dst address => .loadKey dst address
  | .compareKey dst lhs rhs => .compareKey dst lhs rhs

/-- Source-level safety of one action at its pre-state: the `Prim.Safe`
obligations of its primitive, which for non-control primitives do not mention
the program length. -/
def Action.Safe (W : Nat) (s : State) (op : Action) : Prop := Prim.Safe W 0 s op.prim

theorem Action.safe_prim {W : Nat} {s : State} {op : Action} (h : op.Safe W s) (len : Nat) :
    Prim.Safe W len s op.prim := by
  obtain ⟨hops, hat⟩ := h
  refine ⟨hops, ?_⟩
  cases op <;> exact hat

/-- Actions never touch the program counter except by advancing it. -/
theorem Action.prim_not_control (op : Action) :
    (∀ target, op.prim ≠ .jump target) ∧ (∀ src, op.prim ≠ .jumpRegister src) ∧
      (∀ c target, op.prim ≠ .branchZero c target) ∧ (∀ src, op.prim ≠ .halt src) := by
  cases op <;> simp [Action.prim]

inductive Block where
  | skip
  | action (op : Action)
  | exit (src : Operand)
  | seq (first second : Block)
  | ifZero (condition : Operand) (zero nonzero : Block)
  | loop (condition : Operand) (body : Block)
deriving Repr, DecidableEq

/-- Compile-time size; independent of any input. -/
def Block.size : Block → Nat
  | .skip => 0
  | .action _ => 1
  | .exit _ => 1
  | .seq first second => first.size + second.size
  | .ifZero _ zero nonzero => 1 + nonzero.size + 1 + zero.size
  | .loop _ body => body.size + 2

/-- Resolved program counters are encoded as operands. -/
def fin (t : Nat) : Operand := ⟨t % 2 ^ 32, Nat.mod_lt _ (by decide)⟩

theorem fin_val_of_lt {t : Nat} (h : t < 2 ^ 32) : (fin t).val = t := Nat.mod_eq_of_lt h

/-- Every branch target is resolved from the fixed syntax and block position.
A loop is a forward exit branch, its body, and a backward jump. -/
def Block.compileAt : Block → Nat → List BInstr
  | .skip, _ => []
  | .action op, _ => [⟨op.prim⟩]
  | .exit src, _ => [⟨.halt src⟩]
  | .seq first second, base =>
      first.compileAt base ++ second.compileAt (base + first.size)
  | .ifZero condition zero nonzero, base =>
      [⟨.branchZero condition (fin (base + 1 + nonzero.size + 1))⟩] ++
      nonzero.compileAt (base + 1) ++
      [⟨.jump (fin (base + 1 + nonzero.size + 1 + zero.size))⟩] ++
      zero.compileAt (base + 1 + nonzero.size + 1)
  | .loop condition body, base =>
      [⟨.branchZero condition (fin (base + body.size + 2))⟩] ++
      body.compileAt (base + 1) ++
      [⟨.jump (fin base)⟩]

@[simp] theorem Block.compile_length (block : Block) (base : Nat) :
    (block.compileAt base).length = block.size := by
  induction block generalizing base with
  | skip => rfl
  | action op => rfl
  | exit src => rfl
  | seq a b iha ihb => simp [Block.compileAt, Block.size, iha, ihb]
  | ifZero c a b iha ihb => simp [Block.compileAt, Block.size, iha, ihb]; omega
  | loop c body ih => simp [Block.compileAt, Block.size, ih]

/-- Register frame of a block: every action writes an allowed register. -/
def Block.WritesOnly (allowed : Nat → Prop) : Block → Prop
  | .skip => True
  | .action op => ∀ d, op.prim.destination? = some d → allowed d.val
  | .exit _ => True
  | .seq a b => a.WritesOnly allowed ∧ b.WritesOnly allowed
  | .ifZero _ a b => a.WritesOnly allowed ∧ b.WritesOnly allowed
  | .loop _ body => body.WritesOnly allowed

/-! ## Relational cost-carrying big-step semantics -/

/-- `EvalG P b s s' k`: from `s`, block `b` evaluates to `s'` executing exactly
`k` compiled transitions, every executed action satisfying `P` at its pre-state.
Stopped states are identities of cost zero. Costs are exact: a zero test costs
one branch, a taken `nonzero` arm that keeps running pays the jump over the
zero arm, a loop iteration pays its exit test and its back jump, and a loop that
stops inside its body pays no back jump. -/
inductive EvalG (P : State → Action → Prop) : Block → State → State → Nat → Prop
  | stopped (b : Block) (s : State) (h : s.status ≠ .running) : EvalG P b s s 0
  | skip (s : State) (h : s.status = .running) : EvalG P .skip s s 0
  | action (op : Action) (s : State) (h : s.status = .running) (hp : P s op) :
      EvalG P (.action op) s (execPrim op.prim s) 1
  | exit (src : Operand) (s : State) (h : s.status = .running) :
      EvalG P (.exit src) s { s with status := .halted (s.regs src) } 1
  | seq {a b : Block} {s s₁ s₂ : State} {k₁ k₂ : Nat}
      (ha : EvalG P a s s₁ k₁) (hb : EvalG P b s₁ s₂ k₂) : EvalG P (.seq a b) s s₂ (k₁ + k₂)
  | ifZeroTaken {c : Operand} {zero nonzero : Block} {s s' : State} {k : Nat}
      (h : s.status = .running) (hc : s.regs c = 0) (hz : EvalG P zero s s' k) :
      EvalG P (.ifZero c zero nonzero) s s' (k + 1)
  | ifZeroFallthrough {c : Operand} {zero nonzero : Block} {s s' : State} {k : Nat}
      (h : s.status = .running) (hc : s.regs c ≠ 0) (hn : EvalG P nonzero s s' k)
      (hr : s'.status = .running) : EvalG P (.ifZero c zero nonzero) s s' (k + 2)
  | ifZeroFallthroughStopped {c : Operand} {zero nonzero : Block} {s s' : State} {k : Nat}
      (h : s.status = .running) (hc : s.regs c ≠ 0) (hn : EvalG P nonzero s s' k)
      (hr : s'.status ≠ .running) : EvalG P (.ifZero c zero nonzero) s s' (k + 1)
  | loopExit {c : Operand} {body : Block} {s : State}
      (h : s.status = .running) (hc : s.regs c = 0) : EvalG P (.loop c body) s s 1
  | loopStep {c : Operand} {body : Block} {s s₁ s₂ : State} {k₁ k₂ : Nat}
      (h : s.status = .running) (hc : s.regs c ≠ 0) (hbody : EvalG P body s s₁ k₁)
      (hr : s₁.status = .running) (hrest : EvalG P (.loop c body) s₁ s₂ k₂) :
      EvalG P (.loop c body) s s₂ (k₁ + k₂ + 2)
  | loopStopped {c : Operand} {body : Block} {s s₁ : State} {k₁ : Nat}
      (h : s.status = .running) (hc : s.regs c ≠ 0) (hbody : EvalG P body s s₁ k₁)
      (hr : s₁.status ≠ .running) : EvalG P (.loop c body) s s₁ (k₁ + 1)

/-- Plain evaluation: no side condition on actions. -/
abbrev Eval : Block → State → State → Nat → Prop := EvalG (fun _ _ => True)

/-- Safe evaluation: every executed action is `Prim.Safe` at its pre-state. -/
abbrev SafeEval (W : Nat) : Block → State → State → Nat → Prop := EvalG (Action.Safe W)

theorem EvalG.mono {P Q : State → Action → Prop} (hpq : ∀ s op, P s op → Q s op)
    {b : Block} {s s' : State} {k : Nat} (h : EvalG P b s s' k) : EvalG Q b s s' k := by
  induction h with
  | stopped b s h => exact EvalG.stopped b s h
  | skip s h => exact EvalG.skip s h
  | action op s h hp => exact EvalG.action op s h (hpq s op hp)
  | exit src s h => exact EvalG.exit src s h
  | seq _ _ iha ihb => exact EvalG.seq iha ihb
  | ifZeroTaken h hc _ ih => exact EvalG.ifZeroTaken h hc ih
  | ifZeroFallthrough h hc _ hr ih => exact EvalG.ifZeroFallthrough h hc ih hr
  | ifZeroFallthroughStopped h hc _ hr ih => exact EvalG.ifZeroFallthroughStopped h hc ih hr
  | loopExit h hc => exact EvalG.loopExit h hc
  | loopStep h hc _ hr _ ihb ihr => exact EvalG.loopStep h hc ihb hr ihr
  | loopStopped h hc _ hr ih => exact EvalG.loopStopped h hc ih hr

theorem SafeEval.toEval {W : Nat} {b : Block} {s s' : State} {k : Nat}
    (h : SafeEval W b s s' k) : Eval b s s' k :=
  h.mono (fun _ _ _ => trivial)

/-- Evaluation never resurrects a stopped state: the result is running only if
the start was running. -/
theorem EvalG.running_of_result {P : State → Action → Prop} {b : Block} {s s' : State} {k : Nat}
    (h : EvalG P b s s' k) (hr : s'.status = .running) : s.status = .running := by
  induction h with
  | stopped b s h => exact (h hr).elim
  | skip s h => exact h
  | action op s h hp => exact h
  | exit src s h => simp at hr
  | seq _ _ iha ihb => exact iha (ihb hr)
  | ifZeroTaken h hc _ ih => exact h
  | ifZeroFallthrough h hc _ _ ih => exact h
  | ifZeroFallthroughStopped h hc _ _ ih => exact h
  | loopExit h hc => exact h
  | loopStep h hc _ _ _ ihb ihr => exact h
  | loopStopped h hc _ _ ih => exact h

/-! ## Executable evaluator, sound for `Eval` -/

/-- Fuel-indexed executable evaluation of a source block. Fuel bounds nesting
depth plus loop iterations; it is not a cost. -/
def evalF : Nat → Block → State → Option (State × Nat)
  | 0, _, _ => none
  | fuel + 1, b, s =>
    if s.status ≠ .running then some (s, 0) else
    match b with
    | .skip => some (s, 0)
    | .action op => some (execPrim op.prim s, 1)
    | .exit src => some ({ s with status := .halted (s.regs src) }, 1)
    | .seq a b =>
        match evalF fuel a s with
        | none => none
        | some (s₁, k₁) =>
            match evalF fuel b s₁ with
            | none => none
            | some (s₂, k₂) => some (s₂, k₁ + k₂)
    | .ifZero c zero nonzero =>
        if s.regs c = 0 then
          match evalF fuel zero s with
          | none => none
          | some (s', k) => some (s', k + 1)
        else
          match evalF fuel nonzero s with
          | none => none
          | some (s', k) => some (s', if s'.status = .running then k + 2 else k + 1)
    | .loop c body =>
        if s.regs c = 0 then some (s, 1) else
        match evalF fuel body s with
        | none => none
        | some (s₁, k₁) =>
            if s₁.status = .running then
              match evalF fuel (.loop c body) s₁ with
              | none => none
              | some (s₂, k₂) => some (s₂, k₁ + k₂ + 2)
            else some (s₁, k₁ + 1)

theorem evalF_sound : ∀ (fuel : Nat) (b : Block) (s s' : State) (k : Nat),
    evalF fuel b s = some (s', k) → Eval b s s' k := by
  intro fuel
  induction fuel with
  | zero => intro b s s' k h; simp [evalF] at h
  | succ fuel ih =>
      intro b s s' k h
      by_cases hs : s.status = .running
      · cases b with
        | skip =>
            simp [evalF, hs] at h
            obtain ⟨rfl, rfl⟩ := h
            exact EvalG.skip s hs
        | action op =>
            simp [evalF, hs] at h
            obtain ⟨rfl, rfl⟩ := h
            exact EvalG.action op s hs trivial
        | exit src =>
            simp [evalF, hs] at h
            obtain ⟨rfl, rfl⟩ := h
            exact EvalG.exit src s hs
        | seq a b =>
            simp only [evalF, hs, ne_eq, not_true_eq_false, if_false] at h
            cases h₁ : evalF fuel a s with
            | none => simp [h₁] at h
            | some r₁ =>
                obtain ⟨s₁, k₁⟩ := r₁
                cases h₂ : evalF fuel b s₁ with
                | none => simp [h₁, h₂] at h
                | some r₂ =>
                    obtain ⟨s₂, k₂⟩ := r₂
                    simp [h₁, h₂] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact EvalG.seq (ih a s s₁ k₁ h₁) (ih b s₁ s₂ k₂ h₂)
        | ifZero c zero nonzero =>
            simp only [evalF, hs, ne_eq, not_true_eq_false, if_false] at h
            by_cases hc : s.regs c = 0
            · simp only [hc, if_true] at h
              cases h₁ : evalF fuel zero s with
              | none => simp [h₁] at h
              | some r₁ =>
                  obtain ⟨s₁, k₁⟩ := r₁
                  simp [h₁] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact EvalG.ifZeroTaken hs hc (ih zero s s₁ k₁ h₁)
            · simp only [hc, if_false] at h
              cases h₁ : evalF fuel nonzero s with
              | none => simp [h₁] at h
              | some r₁ =>
                  obtain ⟨s₁, k₁⟩ := r₁
                  simp [h₁] at h
                  obtain ⟨rfl, rfl⟩ := h
                  by_cases hr : s₁.status = .running
                  · rw [if_pos hr]
                    exact EvalG.ifZeroFallthrough hs hc (ih nonzero s s₁ k₁ h₁) hr
                  · rw [if_neg hr]
                    exact EvalG.ifZeroFallthroughStopped hs hc (ih nonzero s s₁ k₁ h₁) hr
        | loop c body =>
            simp only [evalF, hs, ne_eq, not_true_eq_false, if_false] at h
            by_cases hc : s.regs c = 0
            · simp only [hc, if_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact EvalG.loopExit hs hc
            · simp only [hc, if_false] at h
              cases h₁ : evalF fuel body s with
              | none => simp [h₁] at h
              | some r₁ =>
                  obtain ⟨s₁, k₁⟩ := r₁
                  simp only [h₁] at h
                  by_cases hr : s₁.status = .running
                  · simp only [hr, if_true] at h
                    cases h₂ : evalF fuel (.loop c body) s₁ with
                    | none => simp [h₂] at h
                    | some r₂ =>
                        obtain ⟨s₂, k₂⟩ := r₂
                        simp [h₂] at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact EvalG.loopStep hs hc (ih body s s₁ k₁ h₁) hr
                          (ih (.loop c body) s₁ s₂ k₂ h₂)
                  · simp only [hr, if_false, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact EvalG.loopStopped hs hc (ih body s s₁ k₁ h₁) hr
      · simp [evalF, hs] at h
        obtain ⟨rfl, rfl⟩ := h
        exact EvalG.stopped _ _ hs

/-! ## Register frame of a compiled block -/

theorem Block.compile_writesOnly (block : Block) (allowed : Nat → Prop)
    (h : block.WritesOnly allowed) (base : Nat) :
    ∀ i ∈ block.compileAt base, _root_.RMQ.SuccinctFinal.PackedConstruction.WritesOnly allowed i := by
  induction block generalizing base with
  | skip => simp [Block.compileAt]
  | action op =>
      intro i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      exact h
  | exit src =>
      intro i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      intro d hd
      simp [Prim.destination?] at hd
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact iha h.1 _ i hi
      · exact ihb h.2 _ i hi
  | ifZero c zero nonzero ihz ihn =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · intro d hd; simp [Prim.destination?] at hd
      · exact ihn h.2 _ i hi
      · intro d hd; simp [Prim.destination?] at hd
      · exact ihz h.1 _ i hi
  | loop c body ih =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with (rfl | hi) | rfl
      · intro d hd; simp [Prim.destination?] at hd
      · exact ih h _ i hi
      · intro d hd; simp [Prim.destination?] at hd

end Structured

end RMQ.SuccinctFinal.PackedConstruction

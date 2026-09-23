import RMQ.Core.WordRAM.Construction.Structured

/-! # Correctness of structured compilation against the interpreter

`EvalG.compile_realizes`: every source evaluation is realized by an actual run
segment of the hosting program, with exactly the evaluation's cost as its
transition count, ending in the evaluation's result state up to the program
counter, and with every executed transition classified as an executed action
(satisfying the side condition at its own pre-state) or as a control
instruction whose target stays inside the hosted code. `SafeEval.compile_safe`
turns the safe-evaluation judgment into `Run.Safe` of that same segment.
The run-level consequences of `Prim.Safe` are proved here because they need
both the execution calculus and the safety judgment.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-! ## Run-level consequences of per-transition safety -/

/-- Along a run whose transitions are all safe, every pre- and post-state fits. -/
theorem run_trace_fits (program : List BInstr) (W : Nat) (hlen : program.length < 2 ^ W)
    (fuel : Nat) (s : State) (hfit : s.Fits W)
    (hsafe : ∀ t ∈ (run program fuel s).transitions,
      Prim.Safe W program.length t.before t.instruction.primitive) :
    (∀ t ∈ (run program fuel s).transitions, t.before.Fits W ∧ t.after.Fits W) ∧
      (run program fuel s).final.Fits W := by
  induction fuel generalizing s with
  | zero => exact ⟨fun _ h => (List.not_mem_nil h).elim, hfit⟩
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none =>
          rw [run_of_step_none program s _ hs]
          exact ⟨fun _ h => (List.not_mem_nil h).elim, hfit⟩
      | some t =>
          obtain ⟨hb, _, hf, he⟩ := step_spec hs
          subst hb
          have hhead : Prim.Safe W program.length t.before t.instruction.primitive := by
            apply hsafe t
            simp [run, hs]
          have hpc : t.before.pc < program.length := (List.getElem?_eq_some_iff.mp hf).1
          have hafter : t.after.Fits W := by
            rw [he]
            exact Prim.safe_fits hfit hhead hpc hlen
          have hrest := ih t.after hafter (fun u hu => hsafe u (by simp [run, hs, hu]))
          refine ⟨?_, by simpa [run, hs] using hrest.2⟩
          intro u hu
          simp only [run, hs, List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact ⟨hfit, hafter⟩
          · exact hrest.1 u hu

/-- Safety of every transition, from a fitting start under a fitting program
length, is the `Run.Safe` judgment. -/
theorem Run.Safe.of_transitions (program : List BInstr) (W : Nat)
    (hlen : program.length < 2 ^ W) (fuel : Nat) (s : State) (hfit : s.Fits W)
    (hsafe : ∀ t ∈ (run program fuel s).transitions,
      Prim.Safe W program.length t.before t.instruction.primitive) :
    Run.Safe W program (run program fuel s) := by
  intro t ht
  exact ⟨hsafe t ht, ((run_trace_fits program W hlen fuel s hfit hsafe).1 t ht).2⟩

/-- A safe run from a non-faulted state never faults. -/
theorem Run.Safe.not_fault {W : Nat} {program : List BInstr} {fuel : Nat} {s : State}
    (hsafe : Run.Safe W program (run program fuel s)) (hs : s.status ≠ .fault) :
    (run program fuel s).final.status ≠ .fault := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
      cases hstep : stepProgram program s with
      | none => rw [run_of_step_none program s _ hstep]; exact hs
      | some t =>
          obtain ⟨hb, _, _, he⟩ := step_spec hstep
          subst hb
          have hhead := hsafe t (by simp [run, hstep])
          have hafter : t.after.status ≠ .fault := by
            rw [he]
            exact Prim.safe_not_fault hhead.1 hs
          have hrest : Run.Safe W program (run program fuel t.after) := by
            intro u hu
            exact hsafe u (by simp [run, hstep, hu])
          simpa [run, hstep] using ih hrest hafter

theorem Run.Safe.final_fits {W : Nat} {program : List BInstr} {fuel : Nat} {s : State}
    (hsafe : Run.Safe W program (run program fuel s)) (hfit : s.Fits W) :
    (run program fuel s).final.Fits W := by
  induction fuel generalizing s with
  | zero => exact hfit
  | succ fuel ih =>
      cases hstep : stepProgram program s with
      | none => rw [run_of_step_none program s _ hstep]; exact hfit
      | some t =>
          have hhead := hsafe t (by simp [run, hstep])
          have hrest : Run.Safe W program (run program fuel t.after) := by
            intro u hu
            exact hsafe u (by simp [run, hstep, hu])
          simpa [run, hstep] using ih hrest hhead.2

namespace Structured

/-! ## Hosting -/

def HostedAt (program : List BInstr) (base : Nat) (code : List BInstr) : Prop :=
  ∀ i, i < code.length → program[base + i]? = code[i]?

theorem HostedAt.self (program : List BInstr) : HostedAt program 0 program := by
  intro i hi
  simp

theorem HostedAt.head {program : List BInstr} {base : Nat} {i : BInstr} {rest : List BInstr}
    (h : HostedAt program base (i :: rest)) : program[base]? = some i := by
  simpa using h 0 (by simp)

theorem HostedAt.append_left {program : List BInstr} {base : Nat} {a b : List BInstr}
    (h : HostedAt program base (a ++ b)) : HostedAt program base a := by
  intro i hi
  have hx := h i (by simp only [List.length_append]; omega)
  simpa [List.getElem?_append_left hi] using hx

theorem HostedAt.append_right {program : List BInstr} {base : Nat} {a b : List BInstr}
    (h : HostedAt program base (a ++ b)) : HostedAt program (base + a.length) b := by
  intro i hi
  have hx := h (a.length + i) (by simp only [List.length_append]; omega)
  simpa [Nat.add_assoc, List.getElem?_append_right (by omega : a.length ≤ a.length + i)]
    using hx

theorem HostedAt.append (a b : List BInstr) (base : Nat) (program : List BInstr)
    (ha : HostedAt program base a) (hb : HostedAt program (base + a.length) b) :
    HostedAt program base (a ++ b) := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getElem?_append_left hia]
    exact ha i hia
  · rw [List.getElem?_append_right (by omega)]
    have hrest := hb (i - a.length) (by simp only [List.length_append] at hi; omega)
    simpa only [Nat.add_assoc, Nat.add_sub_of_le (by omega : a.length ≤ i)] using hrest

/-! ## Program-counter bookkeeping -/

/-- Two states agree everywhere except the program counter. -/
def PcAgree (a b : State) : Prop :=
  a.regs = b.regs ∧ a.memory = b.memory ∧ a.extent = b.extent ∧ a.keys = b.keys ∧
    a.keyRegs = b.keyRegs ∧ a.status = b.status

theorem PcAgree.refl (a : State) : PcAgree a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PcAgree.of_set (a : State) (q : Nat) : PcAgree { a with pc := q } a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PcAgree.trans {a b c : State} (h₁ : PcAgree a b) (h₂ : PcAgree b c) : PcAgree a c := by
  obtain ⟨r₁, m₁, e₁, k₁, kr₁, s₁⟩ := h₁
  obtain ⟨r₂, m₂, e₂, k₂, kr₂, s₂⟩ := h₂
  exact ⟨r₁.trans r₂, m₁.trans m₂, e₁.trans e₂, k₁.trans k₂, kr₁.trans kr₂, s₁.trans s₂⟩

theorem PcAgree.set_pc {a b : State} (h : PcAgree a b) (q : Nat) : PcAgree { a with pc := q } b := h

theorem PcAgree.status {a b : State} (h : PcAgree a b) : a.status = b.status := h.2.2.2.2.2

theorem PcAgree.eq_set {a b : State} (h : PcAgree a b) : a = { b with pc := a.pc } := by
  obtain ⟨r, m, e, k, kr, s⟩ := h
  cases a; cases b
  simp only at r m e k kr s
  subst r m e k kr s
  rfl

theorem PcAgree.set_eq {a b : State} (h : PcAgree a b) (q : Nat) :
    { a with pc := q } = { b with pc := q } := by
  obtain ⟨r, m, e, k, kr, s⟩ := h
  cases a; cases b
  simp only at r m e k kr s
  subst r m e k kr s
  rfl

/-- No primitive's effect outside the program counter depends on the program
counter. -/
theorem execPrim_pcAgree (p : Prim) (s : State) (q : Nat) :
    PcAgree (execPrim p { s with pc := q }) (execPrim p s) := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  all_goals first
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | (split
       · first
          | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          | (split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
       · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- A running action lands one past its program counter. -/
theorem Action.exec_pc_of_running (op : Action) (s : State) (q : Nat)
    (hr : (execPrim op.prim { s with pc := q }).status = .running) :
    (execPrim op.prim { s with pc := q }).pc = q + 1 := by
  cases op with
  | load dst address =>
      simp only [Action.prim, execPrim, State.writeNext, State.next] at hr ⊢
      by_cases ha : s.regs address < s.extent
      · simp only [ha, if_true] at hr ⊢
        cases hm : s.memory (s.regs address) with
        | none => simp [hm] at hr
        | some v => simp
      · simp [ha] at hr
  | store address value =>
      simp only [Action.prim, execPrim, State.next] at hr ⊢
      by_cases ha : s.regs address < s.extent
      · simp [ha]
      · simp [ha] at hr
  | loadKey dst address =>
      simp only [Action.prim, execPrim, State.next] at hr ⊢
      cases hk : s.keys (s.regs address) with
      | none => simp [hk] at hr
      | some k => simp
  | constant dst value => simp [Action.prim, execPrim, State.writeNext, State.next]
  | move dst src => simp [Action.prim, execPrim, State.writeNext, State.next]
  | arithmetic op dst lhs rhs => simp [Action.prim, execPrim, State.writeNext, State.next]
  | comparison op dst lhs rhs => simp [Action.prim, execPrim, State.writeNext, State.next]
  | reserve dst => simp [Action.prim, execPrim, State.writeNext, State.next]
  | compareKey dst lhs rhs => simp [Action.prim, execPrim, State.writeNext, State.next]

/-! ## Transition classification -/

/-- Every transition realized from a hosted block at `base` of size `size` is
an executed action satisfying the side condition at its own pre-state, a
branch or jump whose target lies inside `[base, base + size]`, or a halt. -/
def TransitionShape (P : State → Action → Prop) (base size : Nat) (t : Transition) : Prop :=
  (∃ op : Action, t.instruction = ⟨op.prim⟩ ∧ P t.before op) ∨
  (∃ c target, t.instruction = ⟨.branchZero c target⟩ ∧ target.val ≤ base + size) ∨
  (∃ target, t.instruction = ⟨.jump target⟩ ∧ target.val ≤ base + size) ∨
  (∃ src, t.instruction = ⟨.halt src⟩)

theorem TransitionShape.mono {P : State → Action → Prop} {base size base' size' : Nat}
    {t : Transition} (h : TransitionShape P base' size' t) (hle : base' + size' ≤ base + size) :
    TransitionShape P base size t := by
  rcases h with h | ⟨c, target, hi, ht⟩ | ⟨target, hi, ht⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, target, hi, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨target, hi, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr h))

theorem shapes_append {P : State → Action → Prop} {base size : Nat} {ts₁ ts₂ : List Transition}
    (h₁ : ∀ t ∈ ts₁, TransitionShape P base size t)
    (h₂ : ∀ t ∈ ts₂, TransitionShape P base size t) :
    ∀ t ∈ ts₁ ++ ts₂, TransitionShape P base size t := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact h₁ t ht
  · exact h₂ t ht

/-- Evaluation from a stopped state does nothing. -/
theorem EvalG.stopped_eq {P : State → Action → Prop} {b : Block} {s s' : State} {k : Nat}
    (h : EvalG P b s s' k) (hs : s.status ≠ .running) : s' = s ∧ k = 0 := by
  induction h with
  | stopped b s h => exact ⟨rfl, rfl⟩
  | skip s h => exact (hs h).elim
  | action op s h hp => exact (hs h).elim
  | exit src s h => exact (hs h).elim
  | seq _ _ iha ihb =>
      obtain ⟨rfl, rfl⟩ := iha hs
      obtain ⟨rfl, rfl⟩ := ihb hs
      exact ⟨rfl, rfl⟩
  | ifZeroTaken h hc _ ih => exact (hs h).elim
  | ifZeroFallthrough h hc _ _ ih => exact (hs h).elim
  | ifZeroFallthroughStopped h hc _ _ ih => exact (hs h).elim
  | loopExit h hc => exact (hs h).elim
  | loopStep h hc _ _ _ ihb ihr => exact (hs h).elim
  | loopStopped h hc _ _ ih => exact (hs h).elim

/-! ## The compiler theorem -/

/-- Every structured evaluation is realized by an actual hosted run segment of
exactly its cost, ending in its result state up to the program counter, at the
end of the hosted code when still running, and consisting only of executed
actions (each satisfying `P` at its own pre-state) and in-range control
instructions. The side condition `P` must not depend on the program counter. -/
theorem EvalG.compile_realizes {P : State → Action → Prop}
    (hP : ∀ (s : State) (q : Nat) (op : Action), P s op → P { s with pc := q } op)
    (program : List BInstr) {b : Block} {s s' : State} {k : Nat} (h : EvalG P b s s' k) :
    ∀ base : Nat, HostedAt program base (b.compileAt base) → base + b.size < 2 ^ 32 →
      ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧
        PcAgree s'' s' ∧ (s''.status = .running → s''.pc = base + b.size) ∧
        ∀ t ∈ ts, TransitionShape P base b.size t := by
  induction h with
  | stopped b s hs =>
      intro base _ _
      refine ⟨{ s with pc := base }, [], RunsTo.refl _ _, rfl, PcAgree.of_set s base, ?_, ?_⟩
      · intro hr; exact (hs hr).elim
      · intro t ht; exact (List.not_mem_nil ht).elim
  | skip s hs =>
      intro base _ _
      refine ⟨{ s with pc := base }, [], RunsTo.refl _ _, rfl, PcAgree.of_set s base, ?_, ?_⟩
      · intro _; simp [Block.size]
      · intro t ht; exact (List.not_mem_nil ht).elim
  | action op s hs hp =>
      intro base host _
      have hf : program[({ s with pc := base } : State).pc]? = some ⟨op.prim⟩ := by
        simpa [Block.compileAt] using host.head
      refine ⟨execPrim op.prim { s with pc := base }, _,
        RunsTo.instruction (by simpa using hs) hf, rfl, execPrim_pcAgree _ _ _, ?_, ?_⟩
      · intro hr
        simp only [Block.size]
        exact Action.exec_pc_of_running op s base hr
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact Or.inl ⟨op, rfl, hP s base op hp⟩
  | exit src s hs =>
      intro base host _
      have hf : program[({ s with pc := base } : State).pc]? = some ⟨.halt src⟩ := by
        simpa [Block.compileAt] using host.head
      refine ⟨_, _, RunsTo.instruction (by simpa using hs) hf, rfl,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
      · intro hr; simp [execPrim] at hr
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact Or.inr (Or.inr (Or.inr ⟨src, rfl⟩))
  | seq ha hb iha ihb =>
      rename_i a b s s₁ s₂ k₁ k₂
      intro base host bound
      have hsizes : base + a.size ≤ base + (Block.seq a b).size := by
        simp only [Block.size]; omega
      obtain ⟨s₁'', ts₁, hrun₁, hlen₁, hagree₁, hpc₁, hshape₁⟩ :=
        iha base host.append_left (by simp only [Block.size] at bound; omega)
      by_cases hr : s₁''.status = .running
      · have hpc := hpc₁ hr
        have hs₁'' : s₁'' = { s₁ with pc := base + a.size } := by
          rw [hagree₁.eq_set, hpc]
        have hostb : HostedAt program (base + a.size) (b.compileAt (base + a.size)) := by
          simpa [Block.compileAt] using host.append_right
        obtain ⟨s₂'', ts₂, hrun₂, hlen₂, hagree₂, hpc₂, hshape₂⟩ :=
          ihb (base + a.size) hostb (by simp only [Block.size] at bound; omega)
        rw [← hs₁''] at hrun₂
        refine ⟨s₂'', ts₁ ++ ts₂, hrun₁.trans hrun₂,
          by simp only [List.length_append, hlen₁, hlen₂], hagree₂, ?_, ?_⟩
        · intro hr₂
          rw [hpc₂ hr₂]
          simp only [Block.size] <;> omega
        · exact shapes_append (fun t ht => (hshape₁ t ht).mono hsizes)
            (fun t ht => (hshape₂ t ht).mono (by simp only [Block.size] <;> omega))
      · have hstopped : s₁.status ≠ .running := by
          rw [← hagree₁.status]; exact hr
        obtain ⟨rfl, rfl⟩ := hb.stopped_eq hstopped
        refine ⟨s₁'', ts₁, hrun₁, by simp only [hlen₁, Nat.add_zero], hagree₁,
          fun h => (hr h).elim, fun t ht => (hshape₁ t ht).mono hsizes⟩
  | ifZeroTaken hs hc hz ih =>
      rename_i c zero nonzero s s' k
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + 1 + nonzero.size + 1))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + 1 + nonzero.size + 1)))
          { s with pc := base } = { s with pc := base + 1 + nonzero.size + 1 } := by
        simp [execPrim, hc, fin_val_of_lt (by omega : base + 1 + nonzero.size + 1 < 2 ^ 32)]
      have hostz : HostedAt program (base + 1 + nonzero.size + 1)
          (zero.compileAt (base + 1 + nonzero.size + 1)) := by
        simpa [Block.compileAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using host.append_right
      obtain ⟨s'', ts, hrun, hlen, hagree, hpc, hshape⟩ :=
        ih (base + 1 + nonzero.size + 1) hostz (by omega)
      have hstep := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep
      refine ⟨s'', _ :: ts, hstep.trans hrun, by simp only [List.length_cons, hlen], hagree, ?_, ?_⟩
      · intro hr
        rw [hpc hr]
        simp only [Block.size] <;> omega
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact Or.inr (Or.inl ⟨c, _, rfl, by
            rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
        · exact (hshape t ht).mono (by simp only [Block.size] <;> omega)
  | ifZeroFallthrough hs hc hn hr ih =>
      rename_i c zero nonzero s s' k
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + 1 + nonzero.size + 1))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + 1 + nonzero.size + 1)))
          { s with pc := base } = { s with pc := base + 1 } := by
        simp [execPrim, hc]
      have hostn : HostedAt program (base + 1) (nonzero.compileAt (base + 1)) := by
        simpa [Block.compileAt] using host.append_left.append_left.append_right
      obtain ⟨s₁'', ts₁, hrun₁, hlen₁, hagree₁, hpc₁, hshape₁⟩ := ih (base + 1) hostn (by omega)
      have hr₁ : s₁''.status = .running := by rw [hagree₁.status]; exact hr
      have hpc := hpc₁ hr₁
      have hj' : HostedAt program (base + 1 + nonzero.size)
          [⟨.jump (fin (base + 1 + nonzero.size + 1 + zero.size))⟩] := by
        simpa [Block.compileAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using host.append_left.append_right
      have hj : program[s₁''.pc]? = some ⟨.jump (fin (base + 1 + nonzero.size + 1 + zero.size))⟩ := by
        rw [hpc]; exact hj'.head
      have hjump : execPrim (Prim.jump (fin (base + 1 + nonzero.size + 1 + zero.size))) s₁'' =
          { s₁'' with pc := base + 1 + nonzero.size + 1 + zero.size } := by
        simp [execPrim, fin_val_of_lt (by omega : base + 1 + nonzero.size + 1 + zero.size < 2 ^ 32)]
      have hstep₀ := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep₀
      have hstep₂ := RunsTo.instruction (program := program) (s := s₁'') hr₁ hj
      rw [hjump] at hstep₂
      refine ⟨_, _ :: (ts₁ ++ [_]), hstep₀.trans (hrun₁.trans hstep₂),
        by simp only [List.length_cons, List.length_append, List.length_nil, hlen₁] <;> omega,
        hagree₁.set_pc _, ?_, ?_⟩
      · intro _; simp only [Block.size] <;> omega
      · intro t ht
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | ht | rfl
        · exact Or.inr (Or.inl ⟨c, _, rfl, by
            rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
        · exact (hshape₁ t ht).mono (by simp only [Block.size] <;> omega)
        · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, by
            rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩))
  | ifZeroFallthroughStopped hs hc hn hr ih =>
      rename_i c zero nonzero s s' k
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + 1 + nonzero.size + 1))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + 1 + nonzero.size + 1)))
          { s with pc := base } = { s with pc := base + 1 } := by
        simp [execPrim, hc]
      have hostn : HostedAt program (base + 1) (nonzero.compileAt (base + 1)) := by
        simpa [Block.compileAt] using host.append_left.append_left.append_right
      obtain ⟨s₁'', ts₁, hrun₁, hlen₁, hagree₁, hpc₁, hshape₁⟩ := ih (base + 1) hostn (by omega)
      have hr₁ : s₁''.status ≠ .running := by rw [hagree₁.status]; exact hr
      have hstep₀ := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep₀
      refine ⟨s₁'', _ :: ts₁, hstep₀.trans hrun₁, by simp only [List.length_cons, hlen₁], hagree₁,
        fun h => (hr₁ h).elim, ?_⟩
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inr (Or.inl ⟨c, _, rfl, by
          rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
      · exact (hshape₁ t ht).mono (by simp only [Block.size] <;> omega)
  | loopExit hs hc =>
      rename_i c body s
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + body.size + 2))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + body.size + 2))) { s with pc := base } =
          { s with pc := base + body.size + 2 } := by
        simp [execPrim, hc, fin_val_of_lt (by omega : base + body.size + 2 < 2 ^ 32)]
      have hstep := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep
      refine ⟨_, _, hstep, rfl, PcAgree.of_set s _, ?_, ?_⟩
      · intro _; simp only [Block.size] <;> omega
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact Or.inr (Or.inl ⟨c, _, rfl, by
          rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
  | loopStep hs hc hbody hr hrest ihb ihr =>
      rename_i c body s s₁ s₂ k₁ k₂
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + body.size + 2))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + body.size + 2))) { s with pc := base } =
          { s with pc := base + 1 } := by
        simp [execPrim, hc]
      have hostb : HostedAt program (base + 1) (body.compileAt (base + 1)) := by
        simpa [Block.compileAt] using host.append_left.append_right
      obtain ⟨s₁'', ts₁, hrun₁, hlen₁, hagree₁, hpc₁, hshape₁⟩ := ihb (base + 1) hostb (by omega)
      have hr₁ : s₁''.status = .running := by rw [hagree₁.status]; exact hr
      have hpc := hpc₁ hr₁
      have hj' : HostedAt program (base + 1 + body.size) [⟨.jump (fin base)⟩] := by
        simpa [Block.compileAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using host.append_right
      have hj : program[s₁''.pc]? = some ⟨.jump (fin base)⟩ := by
        rw [hpc]; exact hj'.head
      have hjump : execPrim (Prim.jump (fin base)) s₁'' = { s₁ with pc := base } := by
        rw [hagree₁.eq_set]
        simp [execPrim, fin_val_of_lt (by omega : base < 2 ^ 32)]
      obtain ⟨s₂'', ts₂, hrun₂, hlen₂, hagree₂, hpc₂, hshape₂⟩ :=
        ihr base host (by simp only [Block.size]; omega)
      have hstep₀ := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep₀
      have hstep₂ := RunsTo.instruction (program := program) (s := s₁'') hr₁ hj
      rw [hjump] at hstep₂
      refine ⟨s₂'', _ :: (ts₁ ++ _ :: ts₂), hstep₀.trans (hrun₁.trans (hstep₂.trans hrun₂)),
        by simp only [List.length_cons, List.length_append, hlen₁, hlen₂] <;> omega, hagree₂, ?_, ?_⟩
      · intro hr₂; exact hpc₂ hr₂
      · intro t ht
        simp only [List.mem_cons, List.mem_append] at ht
        rcases ht with rfl | ht | rfl | ht
        · exact Or.inr (Or.inl ⟨c, _, rfl, by
            rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
        · exact (hshape₁ t ht).mono (by simp only [Block.size] <;> omega)
        · exact Or.inr (Or.inr (Or.inl ⟨_, rfl, by rw [fin_val_of_lt (by omega)]; omega⟩))
        · exact hshape₂ t ht
  | loopStopped hs hc hbody hr ih =>
      rename_i c body s s₁ k₁
      intro base host bound
      simp only [Block.size] at bound
      have hf : program[({ s with pc := base } : State).pc]? =
          some ⟨.branchZero c (fin (base + body.size + 2))⟩ := by
        simpa [Block.compileAt] using host.append_left.append_left.head
      have hbranch : execPrim (Prim.branchZero c (fin (base + body.size + 2))) { s with pc := base } =
          { s with pc := base + 1 } := by
        simp [execPrim, hc]
      have hostb : HostedAt program (base + 1) (body.compileAt (base + 1)) := by
        simpa [Block.compileAt] using host.append_left.append_right
      obtain ⟨s₁'', ts₁, hrun₁, hlen₁, hagree₁, hpc₁, hshape₁⟩ := ih (base + 1) hostb (by omega)
      have hr₁ : s₁''.status ≠ .running := by rw [hagree₁.status]; exact hr
      have hstep₀ := RunsTo.instruction (program := program) (s := { s with pc := base })
        (by simpa using hs) hf
      rw [hbranch] at hstep₀
      refine ⟨s₁'', _ :: ts₁, hstep₀.trans hrun₁, by simp only [List.length_cons, hlen₁], hagree₁,
        fun h => (hr₁ h).elim, ?_⟩
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact Or.inr (Or.inl ⟨c, _, rfl, by
          rw [fin_val_of_lt (by omega)]; simp only [Block.size] <;> omega⟩)
      · exact (hshape₁ t ht).mono (by simp only [Block.size] <;> omega)

/-- The compiler theorem in the record form: the final machine state is the
evaluation's result with only its program counter replaced. -/
theorem EvalG.compile_realizes' {P : State → Action → Prop}
    (hP : ∀ (s : State) (q : Nat) (op : Action), P s op → P { s with pc := q } op)
    (program : List BInstr) {b : Block} {s s' : State} {k : Nat} (h : EvalG P b s s' k)
    (base : Nat) (host : HostedAt program base (b.compileAt base)) (bound : base + b.size < 2 ^ 32) :
    ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧
      s'' = { s' with pc := s''.pc } ∧ (s''.status = .running → s''.pc = base + b.size) := by
  obtain ⟨s'', ts, hrun, hlen, hagree, hpc, _⟩ := h.compile_realizes hP program base host bound
  exact ⟨s'', ts, hrun, hlen, hagree.eq_set, hpc⟩

/-! ## Safety of the realized segment -/

theorem Action.Safe.pc_set {W : Nat} {s : State} {op : Action} (h : op.Safe W s) (q : Nat) :
    op.Safe W { s with pc := q } := by
  obtain ⟨hops, hat⟩ := h
  refine ⟨hops, ?_⟩
  cases op <;> exact hat

theorem one_lt_two_pow {W : Nat} (hW : 32 ≤ W) : 1 < 2 ^ W :=
  Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 32) (Nat.pow_le_pow_right (by decide) hW)

/-- A classified transition of a hosted block is `Prim.Safe` when the block
lies strictly inside the program and the width is at least 32. -/
theorem TransitionShape.safe {W : Nat} (hW : 32 ≤ W) {program : List BInstr} {base size : Nat}
    (hin : base + size < program.length) {t : Transition}
    (h : TransitionShape (Action.Safe W) base size t) :
    Prim.Safe W program.length t.before t.instruction.primitive := by
  rcases h with ⟨op, hi, hp⟩ | ⟨c, target, hi, ht⟩ | ⟨target, hi, ht⟩ | ⟨src, hi⟩
  · rw [hi]; exact Action.safe_prim hp _
  · rw [hi]; exact ⟨Prim.operandsFit_of_width _ hW, by show target.val < program.length; omega⟩
  · rw [hi]; exact ⟨Prim.operandsFit_of_width _ hW, by show target.val < program.length; omega⟩
  · rw [hi]; exact ⟨Prim.operandsFit_of_width _ hW, trivial⟩

/-- Safe evaluation compiles to a `Run.Safe` segment of exactly its cost. -/
theorem SafeEval.compile_safe {W : Nat} (hW : 32 ≤ W) (program : List BInstr)
    (hprog : program.length < 2 ^ W) {b : Block} {s s' : State} {k : Nat}
    (h : SafeEval W b s s' k) (base : Nat) (host : HostedAt program base (b.compileAt base))
    (hbound : base + b.size < 2 ^ 32) (hin : base + b.size < program.length)
    (hfit : ({ s with pc := base } : State).Fits W) :
    ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧
      s'' = { s' with pc := s''.pc } ∧ (s''.status = .running → s''.pc = base + b.size) ∧
      Run.Safe W program (run program ts.length { s with pc := base }) ∧ s''.Fits W := by
  obtain ⟨s'', ts, hrun, hlen, hagree, hpc, hshape⟩ :=
    h.compile_realizes (fun s q op hp => hp.pc_set q) program base host hbound
  have hsafe : ∀ t ∈ (run program ts.length { s with pc := base }).transitions,
      Prim.Safe W program.length t.before t.instruction.primitive := by
    intro t ht
    unfold RunsTo at hrun
    rw [hrun] at ht
    exact (hshape t ht).safe hW hin
  have hrs := Run.Safe.of_transitions program W hprog ts.length _ hfit hsafe
  refine ⟨s'', ts, hrun, hlen, hagree.eq_set, hpc, hrs, ?_⟩
  have hfin := hrs.final_fits hfit
  unfold RunsTo at hrun
  rw [hrun] at hfin
  exact hfin

end Structured

end RMQ.SuccinctFinal.PackedConstruction

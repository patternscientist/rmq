import RMQ.Core.WordRAM.Lifecycle.Machine

/-! # Ordered lifecycle execution

Composition preserves actual pre-states and occurrence indices. The old-prefix
adapter lifts completed transition segments without restarting the old machine.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

theorem step_spec {program : List Instruction} {s : State} {t : Transition}
    (h : step program s = some t) :
    t.before = s ∧ s.core.status = .running ∧
      ∃ i, program[s.core.pc]? = some i ∧ t.action = .instruction i ∧
        t.after = execute i s := by
  simp only [step] at h
  split at h
  next hs =>
    cases hf : program[s.core.pc]? with
    | none => simp [hf] at h
    | some i =>
      simp [hf] at h
      subst t
      exact ⟨rfl, hs, i, rfl, rfl, rfl⟩
  next => simp at h

theorem step_of_running {program : List Instruction} {s : State} {i : Instruction}
    (hs : s.core.status = .running) (hf : program[s.core.pc]? = some i) :
    step program s = some ⟨s, .instruction i, execute i s⟩ := by
  simp [step, hs, hf]

theorem step_none_of_stopped (program : List Instruction) (s : State)
    (hs : s.core.status ≠ .running) : step program s = none := by
  simp [step, hs]

theorem run_of_step_none (program : List Instruction) (fuel : Nat) (s : State)
    (h : step program s = none) : run program fuel s = ⟨s, []⟩ := by
  cases fuel <;> simp [run, h]

theorem run_of_stopped (program : List Instruction) (fuel : Nat) (s : State)
    (hs : s.core.status ≠ .running) : run program fuel s = ⟨s, []⟩ :=
  run_of_step_none program fuel s (step_none_of_stopped program s hs)

theorem run_add (program : List Instruction) (a b : Nat) (s : State) :
    run program (a + b) s =
      let first := run program a s
      let second := run program b first.final
      ⟨second.final, first.transitions ++ second.transitions⟩ := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    cases h : step program s with
    | none => simp [Nat.succ_add, run, h, run_of_step_none program b s h]
    | some t =>
      simpa [Nat.succ_add, run, h, List.cons_append] using
        congrArg (fun r : Run => Run.mk r.final (t :: r.transitions)) (ih t.after)

def RunsTo (program : List Instruction) (s s' : State) (ts : List Transition) : Prop :=
  run program ts.length s = ⟨s', ts⟩

theorem RunsTo.refl (program : List Instruction) (s : State) : RunsTo program s s [] := rfl

theorem RunsTo.trans {program : List Instruction} {s₁ s₂ s₃ : State}
    {ts₁ ts₂ : List Transition} (h₁ : RunsTo program s₁ s₂ ts₁)
    (h₂ : RunsTo program s₂ s₃ ts₂) : RunsTo program s₁ s₃ (ts₁ ++ ts₂) := by
  unfold RunsTo at h₁ h₂ ⊢
  rw [List.length_append, run_add, h₁]
  simp [h₂]

theorem RunsTo.instruction {program : List Instruction} {s : State} {i : Instruction}
    (hs : s.core.status = .running) (hf : program[s.core.pc]? = some i) :
    RunsTo program s (execute i s) [⟨s, .instruction i, execute i s⟩] := by
  simp [RunsTo, run, step_of_running hs hf]

theorem RunsTo.fuel_extension {program : List Instruction} {s s' : State}
    {ts : List Transition} (h : RunsTo program s s' ts)
    (stopped : s'.core.status ≠ .running) (extra : Nat) :
    run program (ts.length + extra) s = ⟨s', ts⟩ := by
  unfold RunsTo at h
  rw [run_add, h]
  dsimp only
  rw [run_of_stopped program extra s' stopped]
  simp

theorem run_transition_at {program : List Instruction} {fuel : Nat} {s : State}
    {k : Nat} {t : Transition} (h : (run program fuel s).transitions[k]? = some t) :
    t.before = (run program k s).final ∧ step program t.before = some t := by
  induction fuel generalizing s k with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step program s with
    | none => simp [run, hs] at h
    | some first =>
      cases k with
      | zero =>
        simp only [run, hs, List.getElem?_cons_zero, Option.some.injEq] at h
        subst t
        have hb := (step_spec hs).1
        exact ⟨hb, by simpa [hb] using hs⟩
      | succ k =>
        simp only [run, hs, List.getElem?_cons_succ] at h
        obtain ⟨hb, ht⟩ := ih h
        exact ⟨by simpa [run, hs] using hb, ht⟩

theorem run_exact_steps (program : List Instruction) (fuel : Nat) (s : State) :
    run program (run program fuel s).steps s = run program fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases h : step program s with
    | none => simp [run, h, Run.steps]
    | some t =>
      simpa [run, h, Run.steps] using
        congrArg (fun r : Run => Run.mk r.final (t :: r.transitions)) (ih t.after)

def ofCore (s : PackedConstruction.State) (keys keyRegs : Nat) : State := ⟨s, keys, keyRegs⟩

def oldInstruction (i : PackedConstruction.BInstr) : Instruction := .old i.primitive

def oldTransition (keys keyRegs : Nat) (t : PackedConstruction.Transition) : Transition :=
  ⟨ofCore t.before keys keyRegs, .instruction (oldInstruction t.instruction),
    ofCore t.after keys keyRegs⟩

def oldRun (keys keyRegs : Nat) (r : PackedConstruction.Run) : Run :=
  ⟨ofCore r.final keys keyRegs, r.transitions.map (oldTransition keys keyRegs)⟩

theorem old_step {program : List PackedConstruction.BInstr} {s : PackedConstruction.State}
    {t : PackedConstruction.Transition} (h : PackedConstruction.stepProgram program s = some t)
    (tail : List Instruction) (keys keyRegs : Nat) :
    step (program.map oldInstruction ++ tail) (ofCore s keys keyRegs) =
      some (oldTransition keys keyRegs t) := by
  obtain ⟨hb, hs, hf, he⟩ := PackedConstruction.step_spec h
  have hi : s.pc < program.length := (List.getElem?_eq_some_iff.mp hf).1
  have fetch : (program.map oldInstruction ++ tail)[s.pc]? =
      some (oldInstruction t.instruction) := by
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hf]
  cases t
  simp_all [step, ofCore, oldTransition, oldInstruction, execute]

theorem old_run_full (program : List PackedConstruction.BInstr) (tail : List Instruction)
    (fuel : Nat) (s : PackedConstruction.State) (keys keyRegs : Nat)
    (hfull : (PackedConstruction.run program fuel s).transitions.length = fuel) :
    run (program.map oldInstruction ++ tail) fuel (ofCore s keys keyRegs) =
      oldRun keys keyRegs (PackedConstruction.run program fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : PackedConstruction.stepProgram program s with
    | none => simp [PackedConstruction.run, hs] at hfull
    | some t =>
      have ht : (PackedConstruction.run program fuel t.after).transitions.length = fuel := by
        simpa [PackedConstruction.run, hs] using hfull
      have hstep := old_step hs tail keys keyRegs
      simp only [run, hstep, PackedConstruction.run, hs]
      change _ = oldRun keys keyRegs _
      rw [show (oldTransition keys keyRegs t).after = ofCore t.after keys keyRegs from rfl,
        ih t.after ht]
      rfl

/-- Every old transition remains the same transition, including its position
and full projected states, inside an old prefix followed by new instructions. -/
theorem lift_old_prefix {program : List PackedConstruction.BInstr}
    {s s' : PackedConstruction.State} {ts : List PackedConstruction.Transition}
    (h : PackedConstruction.RunsTo program s s' ts)
    (tail : List Instruction) (keys keyRegs : Nat) :
    RunsTo (program.map oldInstruction ++ tail) (ofCore s keys keyRegs)
      (ofCore s' keys keyRegs) (ts.map (oldTransition keys keyRegs)) := by
  unfold RunsTo
  rw [List.length_map]
  have hh : PackedConstruction.run program ts.length s = ⟨s', ts⟩ := h
  rw [old_run_full program tail ts.length s keys keyRegs (by rw [hh]), hh]
  rfl

/-- A stopped old run cannot accidentally fall through into an appended new
instruction. The equality preserves the complete ordered run, not just result. -/
theorem old_run_of_stopped (program : List PackedConstruction.BInstr)
    (tail : List Instruction) (fuel : Nat) (s : PackedConstruction.State)
    (keys keyRegs : Nat)
    (stopped : (PackedConstruction.run program fuel s).final.status ≠ .running) :
    run (program.map oldInstruction ++ tail) fuel (ofCore s keys keyRegs) =
      oldRun keys keyRegs (PackedConstruction.run program fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : PackedConstruction.stepProgram program s with
    | none =>
      have hstop : s.status ≠ .running := by
        simpa [PackedConstruction.run, hs] using stopped
      have hnew := step_none_of_stopped (program.map oldInstruction ++ tail)
        (ofCore s keys keyRegs) hstop
      simp [run, hnew, PackedConstruction.run, hs, oldRun]
    | some t =>
      have hrest : (PackedConstruction.run program fuel t.after).final.status ≠ .running := by
        simpa [PackedConstruction.run, hs] using stopped
      have hstep := old_step hs tail keys keyRegs
      simp only [run, hstep, PackedConstruction.run, hs]
      rw [show (oldTransition keys keyRegs t).after = ofCore t.after keys keyRegs from rfl,
        ih t.after hrest]
      rfl

theorem requestProtocol_exact (entry : PackedConstruction.Operand) (left right answer : Nat)
    (s : State) (hs : s.core.status = .halted answer) :
    (requestProtocol entry left right s).final =
      { s with core := { s.core with
        regs := PackedConstruction.put (PackedConstruction.put s.core.regs
          requestLeftRegister left) requestRightRegister right,
        pc := entry, status := .running } } ∧
    (requestProtocol entry left right s).steps = 4 ∧
    (requestProtocol entry left right s).categories =
      [.requestAdmission, .requestAdmission, .controlEntry, .controlEntry] := by
  simp [requestProtocol, runBoundary, boundaryStep, executeBoundary, hs,
    Run.steps, Run.categories, Action.category]

end RMQ.SuccinctFinal.PackedLifecycle

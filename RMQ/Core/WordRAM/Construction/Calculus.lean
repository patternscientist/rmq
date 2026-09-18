import RMQ.Core.WordRAM.Construction.Program

/-! # Exact execution calculus for the construction interpreter

Every statement below is an observation of `run` itself. Segments compose with
their complete transition lists, so equal repeated events remain positionally
distinct. Work is the transition count, partitioned exactly over the ten
primitive categories. Store provenance, frame discipline, clean-tail
preservation, extent monotonicity, write replay and supplied-store agreement
are all proved against the actual dynamic execution, never against a static
footprint or a separately supplied log. The header lemmas at the end are the
generic run-level facts behind the `HeaderUse` certificate field.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-! ## Single steps -/

theorem stepProgram_of_running {program : List BInstr} {s : State} {i : BInstr}
    (hs : s.status = .running) (hf : program[s.pc]? = some i) :
    stepProgram program s = some ⟨s, i, execPrim i.primitive s⟩ := by
  simp [stepProgram, fetch, hf, checkedStep, hs, bstep]

theorem stepProgram_none_of_stopped {program : List BInstr} {s : State}
    (hs : s.status ≠ .running) : stepProgram program s = none := by
  unfold stepProgram fetch
  cases program[s.pc]? with
  | none => rfl
  | some i =>
      cases h : s.status with
      | running => exact (hs h).elim
      | halted v => simp [checkedStep, h]
      | fault => simp [checkedStep, h]

theorem stepProgram_none_of_fetch {program : List BInstr} {s : State}
    (hf : program[s.pc]? = none) : stepProgram program s = none := by
  simp [stepProgram, fetch, hf]

/-- A successful step records exactly the producing state, the fetched
instruction and the scalar evaluator's result. -/
theorem step_spec {program : List BInstr} {s : State} {t : Transition}
    (h : stepProgram program s = some t) :
    t.before = s ∧ s.status = .running ∧ program[s.pc]? = some t.instruction ∧
      t.after = execPrim t.instruction.primitive s := by
  unfold stepProgram fetch at h
  cases hf : program[s.pc]? with
  | none => simp [hf] at h
  | some i =>
      simp only [hf] at h
      cases hs : s.status with
      | running =>
          simp only [checkedStep, hs, bstep, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl, rfl⟩
      | halted v => simp [checkedStep, hs] at h
      | fault => simp [checkedStep, hs] at h

/-! ## Fuel and composition -/

@[simp] theorem run_zero (program : List BInstr) (s : State) : run program 0 s = ⟨s, []⟩ := rfl

theorem run_of_step_none (program : List BInstr) (s : State) (fuel : Nat)
    (h : stepProgram program s = none) : run program fuel s = ⟨s, []⟩ := by
  cases fuel <;> simp [run, h]

theorem run_of_stopped (program : List BInstr) (fuel : Nat) (s : State)
    (h : s.status ≠ .running) : run program fuel s = ⟨s, []⟩ :=
  run_of_step_none program s fuel (stepProgram_none_of_stopped h)

theorem run_succ_of_step {program : List BInstr} {s : State} {t : Transition} (fuel : Nat)
    (h : stepProgram program s = some t) :
    run program (fuel + 1) s =
      ⟨(run program fuel t.after).final, t :: (run program fuel t.after).transitions⟩ := by
  simp [run, h]

/-- Split an actual run at any fuel boundary, retaining every transition. -/
theorem run_add (program : List BInstr) (a b : Nat) (s : State) :
    run program (a + b) s =
      let first := run program a s
      let second := run program b first.final
      ⟨second.final, first.transitions ++ second.transitions⟩ := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
      cases h : stepProgram program s with
      | none => simp [Nat.succ_add, run, h, run_of_step_none program s b h]
      | some t =>
          simpa [Nat.succ_add, run, h, List.cons_append] using
            congrArg (fun r : Run => Run.mk r.final (t :: r.transitions)) (ih t.after)

/-- An exact transition segment consumes precisely its own length in fuel. -/
def RunsTo (program : List BInstr) (s s' : State) (transitions : List Transition) : Prop :=
  run program transitions.length s = ⟨s', transitions⟩

theorem RunsTo.refl (program : List BInstr) (s : State) : RunsTo program s s [] := rfl

theorem RunsTo.trans {program : List BInstr} {s₁ s₂ s₃ : State} {ts₁ ts₂ : List Transition}
    (h₁ : RunsTo program s₁ s₂ ts₁) (h₂ : RunsTo program s₂ s₃ ts₂) :
    RunsTo program s₁ s₃ (ts₁ ++ ts₂) := by
  unfold RunsTo at h₁ h₂ ⊢
  rw [List.length_append, run_add, h₁]
  simp [h₂]

theorem RunsTo.of_step {program : List BInstr} {s : State} {t : Transition}
    (h : stepProgram program s = some t) : RunsTo program s t.after [t] := by
  simp [RunsTo, run, h]

/-- The fetched instruction's own result, never a supplied answer. -/
theorem RunsTo.instruction {program : List BInstr} {s : State} {i : BInstr}
    (hs : s.status = .running) (hf : program[s.pc]? = some i) :
    RunsTo program s (execPrim i.primitive s) [⟨s, i, execPrim i.primitive s⟩] :=
  RunsTo.of_step (stepProgram_of_running hs hf)

theorem RunsTo.steps {program : List BInstr} {s s' : State} {ts : List Transition}
    (h : RunsTo program s s' ts) : (run program ts.length s).steps = ts.length := by
  unfold RunsTo at h
  rw [h]
  rfl

theorem run_add_of_stopped (program : List BInstr) (a b : Nat) (s : State)
    (h : (run program a s).final.status ≠ .running) :
    run program (a + b) s = run program a s := by
  rw [run_add]
  dsimp only
  rw [run_of_stopped program b _ h]
  simp

/-- A halted or faulted segment is fuel-insensitive. -/
theorem RunsTo.fuel_extension {program : List BInstr} {s s' : State} {ts : List Transition}
    (h : RunsTo program s s' ts) (stopped : s'.status ≠ .running) (extra : Nat) :
    run program (ts.length + extra) s = ⟨s', ts⟩ := by
  unfold RunsTo at h
  rw [run_add, h]
  dsimp only
  rw [run_of_stopped program extra s' stopped]
  simp

theorem run_steps_le_fuel (program : List BInstr) (fuel : Nat) (s : State) :
    (run program fuel s).steps ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [run, Run.steps]
  | succ fuel ih =>
      cases h : stepProgram program s with
      | none => simp [run, h, Run.steps]
      | some t => simpa [run, h, Run.steps] using Nat.succ_le_succ (ih t.after)

/-! ## Category partition -/

theorem Run.steps_eq_categories_length (r : Run) : r.steps = r.categories.length := by
  simp [Run.steps, Run.categories]

private theorem categories_partition (cs : List Category) :
    cs.length = cs.count .read + cs.count .register + cs.count .arithmetic +
      cs.count .comparison + cs.count .branch + cs.count .control + cs.count .write +
      cs.count .allocation + cs.count .keyRead + cs.count .oracleComparison := by
  induction cs with
  | nil => simp
  | cons c cs ih => cases c <;> simp_all <;> omega

/-- The ten disjoint primitive categories partition the executed transitions exactly. -/
theorem Run.steps_partition (r : Run) :
    r.steps = r.categoryCount .read + r.categoryCount .register + r.categoryCount .arithmetic +
      r.categoryCount .comparison + r.categoryCount .branch + r.categoryCount .control +
      r.categoryCount .write + r.categoryCount .allocation + r.categoryCount .keyRead +
      r.categoryCount .oracleComparison := by
  rw [r.steps_eq_categories_length]
  exact categories_partition r.categories

/-! ## Positional provenance -/

/-- Index `k` identifies the actual occurrence and its executed prefix. -/
theorem run_transition_at {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} (h : (run program fuel s).transitions[k]? = some t) :
    t.before = (run program k s).final ∧ stepProgram program t.before = some t := by
  induction fuel generalizing s k with
  | zero => simp [run] at h
  | succ fuel ih =>
      cases hs : stepProgram program s with
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

theorem run_transition_spec {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} (h : (run program fuel s).transitions[k]? = some t) :
    t.before = (run program k s).final ∧ t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      t.after = execPrim t.instruction.primitive t.before := by
  obtain ⟨hb, hs⟩ := run_transition_at h
  exact ⟨hb, (step_spec hs).2⟩

/-- Membership yields a position; every transition of a run is a genuine step. -/
theorem run_mem_spec {program : List BInstr} {fuel : Nat} {s : State} {t : Transition}
    (h : t ∈ (run program fuel s).transitions) :
    t.before.status = .running ∧ program[t.before.pc]? = some t.instruction ∧
      t.after = execPrim t.instruction.primitive t.before := by
  obtain ⟨k, hk⟩ := List.getElem?_of_mem h
  exact (run_transition_spec hk).2

/-- Positional store provenance: the store occurrence at index `k` writes the
value register of its own pre-state to the address register of its own
pre-state, exactly when that address is inside the pre-state extent; otherwise
it faults and writes nothing. -/
theorem run_write_at {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} {address value : Operand}
    (h : (run program fuel s).transitions[k]? = some t)
    (hstore : t.instruction.primitive = .store address value) :
    t.before = (run program k s).final ∧ t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      (t.before.regs address < t.before.extent →
        t.after.memory (t.before.regs address) = some (t.before.regs value) ∧
        t.after.status = .running ∧ t.after.extent = t.before.extent ∧
        t.write? = some (t.before.regs address, t.before.regs value)) ∧
      (¬ t.before.regs address < t.before.extent →
        t.after.status = .fault ∧ t.after.memory = t.before.memory ∧ t.write? = none) := by
  obtain ⟨hb, hs, hf, he⟩ := run_transition_spec h
  refine ⟨hb, hs, hf, ?_, ?_⟩
  · intro ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [he, hstore]; simp [execPrim, ha, State.next, put]
    · rw [he, hstore]; simp [execPrim, ha, State.next, hs]
    · rw [he, hstore]; simp [execPrim, ha, State.next]
    · simp [Transition.write?, hstore, ha]
  · intro ha
    refine ⟨?_, ?_, ?_⟩
    · rw [he, hstore]; simp [execPrim, ha]
    · rw [he, hstore]; simp [execPrim, ha]
    · simp [Transition.write?, hstore, ha]

/-- Positional read backing: a successful load occurrence returns exactly the
present cell of its own pre-state memory at the address its own register holds. -/
theorem run_load_at {program : List BInstr} {fuel : Nat} {s : State} {k : Nat}
    {t : Transition} {dst address : Operand}
    (h : (run program fuel s).transitions[k]? = some t)
    (hload : t.instruction.primitive = .load dst address) :
    t.before = (run program k s).final ∧ t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      t.load? = some (t.before.regs address) ∧
      (∀ v, t.before.regs address < t.before.extent →
        t.before.memory (t.before.regs address) = some v →
        t.after.regs dst = v ∧ t.after.status = .running ∧ t.after.memory = t.before.memory) ∧
      (t.after.status = .running →
        t.before.regs address < t.before.extent ∧
        ∃ v, t.before.memory (t.before.regs address) = some v ∧ t.after.regs dst = v) := by
  obtain ⟨hb, hs, hf, he⟩ := run_transition_spec h
  refine ⟨hb, hs, hf, by simp [Transition.load?, hload], ?_, ?_⟩
  · intro v ha hv
    rw [he, hload]
    simp [execPrim, ha, hv, State.writeNext, State.next, put, hs]
  · intro hrun
    rw [he, hload] at hrun
    by_cases ha : t.before.regs address < t.before.extent
    · refine ⟨ha, ?_⟩
      cases hv : t.before.memory (t.before.regs address) with
      | none => simp [execPrim, ha, hv] at hrun
      | some v =>
          refine ⟨v, rfl, ?_⟩
          rw [he, hload]
          simp [execPrim, ha, hv, State.writeNext, State.next, put]
    · simp [execPrim, ha] at hrun

/-! ## Memory and extent equations of one primitive -/

theorem execPrim_memory_replay (p : Prim) (s : State) :
    (execPrim p s).memory =
      (match p with
        | .store address value =>
            if s.regs address < s.extent then
              put s.memory (s.regs address) (some (s.regs value))
            else s.memory
        | _ => s.memory) := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  all_goals first
    | rfl
    | (split
       · first | rfl | (split <;> rfl)
       · rfl)

theorem execPrim_extent_eq (p : Prim) (s : State) :
    (execPrim p s).extent = (match p with | .reserve _ => s.extent + 1 | _ => s.extent) := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  all_goals first
    | rfl
    | (split
       · first | rfl | (split <;> rfl)
       · rfl)

/-- Keys are an input channel: no primitive changes the key bank. -/
theorem execPrim_keys (p : Prim) (s : State) : (execPrim p s).keys = s.keys := by
  cases p <;> simp only [execPrim, State.writeNext, State.next]
  all_goals first | rfl | (split <;> first | rfl | (split <;> rfl))

/-! ## Extent monotonicity and clean tails -/

theorem execPrim_extent_le (p : Prim) (s : State) : s.extent ≤ (execPrim p s).extent := by
  rw [execPrim_extent_eq]
  cases p <;> dsimp only <;> omega

theorem run_extent_mono (program : List BInstr) (fuel : Nat) (s : State) :
    s.extent ≤ (run program fuel s).final.extent := by
  induction fuel generalizing s with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      cases h : stepProgram program s with
      | none => simp [run, h]
      | some t =>
          obtain ⟨_, _, _, he⟩ := step_spec h
          have h1 : s.extent ≤ t.after.extent := by
            rw [he]; exact execPrim_extent_le _ _
          simpa [run, h] using Nat.le_trans h1 (ih t.after)

theorem execPrim_cleanTail (p : Prim) (s : State) (h : CleanTail s) :
    CleanTail (execPrim p s) := by
  intro a ha
  rw [execPrim_extent_eq] at ha
  rw [execPrim_memory_replay]
  cases p
  case store address value =>
    dsimp only at ha ⊢
    by_cases hlt : s.regs address < s.extent
    · rw [if_pos hlt]
      have hne : a ≠ s.regs address := by omega
      simp only [put, hne, if_false]
      exact h a ha
    · rw [if_neg hlt]
      exact h a ha
  case reserve dst =>
    dsimp only at ha ⊢
    exact h a (by omega)
  all_goals
    dsimp only at ha ⊢
    exact h a ha

theorem run_cleanTail (program : List BInstr) (fuel : Nat) (s : State) (h : CleanTail s) :
    CleanTail (run program fuel s).final := by
  induction fuel generalizing s with
  | zero => exact h
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none => simpa [run, hs] using h
      | some t =>
          obtain ⟨_, _, _, he⟩ := step_spec hs
          have ht : CleanTail t.after := by rw [he]; exact execPrim_cleanTail _ _ h
          simpa [run, hs] using ih t.after ht

theorem run_keys (program : List BInstr) (fuel : Nat) (s : State) :
    (run program fuel s).final.keys = s.keys := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none => simp [run, hs]
      | some t =>
          obtain ⟨_, _, _, he⟩ := step_spec hs
          have ht : t.after.keys = s.keys := by rw [he]; exact execPrim_keys _ _
          simpa [run, hs] using (ih t.after).trans ht

/-! ## Register frames -/

theorem step_frame {program : List BInstr} {s : State} (allowed : Nat → Prop)
    (hwrites : ∀ i ∈ program, WritesOnly allowed i) (r : Nat) (hout : ¬ allowed r)
    {t : Transition} (hstep : stepProgram program s = some t) : t.after.regs r = s.regs r := by
  obtain ⟨_, _, hf, he⟩ := step_spec hstep
  rw [he]
  exact execPrim_frame _ _ allowed (hwrites t.instruction (List.mem_of_getElem? hf)) r hout

/-- Registers outside the program's write inventory are unchanged at every fuel
prefix, including faulted and early-halted runs. -/
theorem run_frame (program : List BInstr) (fuel : Nat) (s : State) (allowed : Nat → Prop)
    (hwrites : ∀ i ∈ program, WritesOnly allowed i) (r : Nat) (hout : ¬ allowed r) :
    (run program fuel s).final.regs r = s.regs r := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases ht : stepProgram program s with
      | none => simp [run, ht]
      | some t =>
          simpa only [run, ht] using
            (ih t.after).trans (step_frame allowed hwrites r hout ht)

/-! ## Write replay -/

/-- One transition's memory effect is exactly its own write event, if any. -/
theorem Transition.memory_of_step {program : List BInstr} {s : State} {t : Transition}
    (hs : stepProgram program s = some t) :
    t.after.memory =
      match t.write? with
      | some e => put s.memory e.1 (some e.2)
      | none => s.memory := by
  obtain ⟨hb, _, _, he⟩ := step_spec hs
  subst hb
  rw [he, execPrim_memory_replay]
  unfold Transition.write?
  cases t.instruction.primitive
  case store address value =>
    dsimp only
    by_cases hlt : t.before.regs address < t.before.extent
    · simp [hlt]
    · simp [hlt]
  all_goals rfl

/-- The final memory of a run is exactly the initial memory with the run's own
successful write events folded in, in execution order. Plain-data replay is a
consequence of the execution, never a substitute for it. -/
theorem writes_replay (program : List BInstr) (fuel : Nat) (s : State) :
    (run program fuel s).final.memory =
      (run program fuel s).writes.foldl (fun m e => put m e.1 (some e.2)) s.memory := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none => simp [run, hs, Run.writes]
      | some t =>
          have hrest := ih t.after
          have hmem := Transition.memory_of_step hs
          simp only [run, hs, Run.writes, List.filterMap_cons] at hrest ⊢
          rw [hrest, hmem]
          cases t.write? with
          | none => rfl
          | some e => rfl

/-! ## Supplied-store agreement -/

/-- Two states agree on everything except memory and the key bank. -/
def State.Agree (s s' : State) : Prop :=
  s.regs = s'.regs ∧ s.extent = s'.extent ∧ s.keyRegs = s'.keyRegs ∧
    s.pc = s'.pc ∧ s.status = s'.status

theorem State.Agree.refl (s : State) : State.Agree s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem State.Agree.eq {s s' : State} (h : State.Agree s s') :
    s' = { s with memory := s'.memory, keys := s'.keys } := by
  obtain ⟨hr, he, hk, hp, hs⟩ := h
  cases s; cases s'
  simp only at hr he hk hp hs
  subst hr he hk hp hs
  rfl

theorem State.agree_of_eq {s : State} {m : Memory} {k : Nat → Option Int} :
    State.Agree s { s with memory := m, keys := k } := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One primitive on two states that agree outside memory and keys: agreement
on the one numeric cell a load reads and on the one key a key read consults
is enough, and the two post-memories either agree at an address or are both
unchanged there. -/
theorem execPrim_agree (p : Prim) (s : State) (m' : Memory) (k' : Nat → Option Int)
    (hmem : ∀ dst address, p = .load dst address → m' (s.regs address) = s.memory (s.regs address))
    (hkey : ∀ dst address, p = .loadKey dst address → k' (s.regs address) = s.keys (s.regs address)) :
    State.Agree (execPrim p s) (execPrim p { s with memory := m', keys := k' }) ∧
      (∀ b, (execPrim p { s with memory := m', keys := k' }).memory b = (execPrim p s).memory b ∨
        ((execPrim p { s with memory := m', keys := k' }).memory b = m' b ∧
          (execPrim p s).memory b = s.memory b)) := by
  cases p with
  | load dst address =>
      have hm := hmem dst address rfl
      simp only [execPrim, State.writeNext, State.next]
      by_cases ha : s.regs address < s.extent
      · rw [if_pos ha, if_pos ha, hm]
        cases s.memory (s.regs address) with
        | none => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
        | some v => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
      · rw [if_neg ha, if_neg ha]
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | store address value =>
      simp only [execPrim, State.next]
      by_cases ha : s.regs address < s.extent
      · rw [if_pos ha, if_pos ha]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => ?_⟩
        by_cases hb : b = s.regs address
        · left; simp [put, hb]
        · right; simp [put, hb]
      · rw [if_neg ha, if_neg ha]
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | loadKey dst address =>
      have hk := hkey dst address rfl
      simp only [execPrim, State.next]
      rw [hk]
      cases s.keys (s.regs address) with
      | none => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
      | some v => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | constant dst value =>
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | move dst src => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | arithmetic op dst lhs rhs => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | comparison op dst lhs rhs => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | jump target => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | jumpRegister src => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | branchZero condition target => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | halt src => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | reserve dst => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩
  | compareKey dst lhs rhs => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun b => Or.inr ⟨rfl, rfl⟩⟩

theorem execPrim_agree_of_agree (p : Prim) (s s' : State) (h : State.Agree s s')
    (hmem : ∀ dst address, p = .load dst address →
      s'.memory (s.regs address) = s.memory (s.regs address))
    (hkey : ∀ dst address, p = .loadKey dst address →
      s'.keys (s.regs address) = s.keys (s.regs address)) :
    State.Agree (execPrim p s) (execPrim p s') ∧
      (∀ b, (execPrim p s').memory b = (execPrim p s).memory b ∨
        ((execPrim p s').memory b = s'.memory b ∧ (execPrim p s).memory b = s.memory b)) := by
  rw [h.eq]
  exact execPrim_agree p s s'.memory s'.keys hmem hkey

theorem stepProgram_none_agree {program : List BInstr} {s s' : State} (h : State.Agree s s')
    (hs : stepProgram program s = none) : stepProgram program s' = none := by
  obtain ⟨_, _, _, hp, hst⟩ := h
  cases hf : program[s.pc]? with
  | none => exact stepProgram_none_of_fetch (by rw [← hp]; exact hf)
  | some i =>
      cases hst' : s.status with
      | running => rw [stepProgram_of_running hst' hf] at hs; cases hs
      | halted v => exact stepProgram_none_of_stopped (by rw [← hst, hst']; simp)
      | fault => exact stepProgram_none_of_stopped (by rw [← hst, hst']; simp)

/-- Transition-wise agreement of two transition lists: same instructions and
agreeing pre- and post-states outside memory and keys. -/
def TransitionsAgree : List Transition → List Transition → Prop
  | [], [] => True
  | t :: ts, t' :: ts' =>
      (t.instruction = t'.instruction ∧ State.Agree t.before t'.before ∧
        State.Agree t.after t'.after) ∧ TransitionsAgree ts ts'
  | _, _ => False

/-- Run agreement: transition-wise agreement plus agreeing finals. -/
def Run.Agree (r r' : Run) : Prop :=
  TransitionsAgree r.transitions r'.transitions ∧ State.Agree r.final r'.final

theorem TransitionsAgree.length_eq {ts ts' : List Transition} (h : TransitionsAgree ts ts') :
    ts.length = ts'.length := by
  induction ts generalizing ts' with
  | nil =>
      cases ts' with
      | nil => rfl
      | cons t' ts' => exact absurd h (by simp [TransitionsAgree])
  | cons t ts ih =>
      cases ts' with
      | nil => exact absurd h (by simp [TransitionsAgree])
      | cons t' ts' => simp only [List.length_cons, ih h.2]

theorem TransitionsAgree.map_eq {ts ts' : List Transition} (h : TransitionsAgree ts ts')
    {β : Type} (f : Transition → β)
    (hf : ∀ t t' : Transition, t.instruction = t'.instruction → State.Agree t.before t'.before →
      State.Agree t.after t'.after → f t = f t') :
    ts.map f = ts'.map f := by
  induction ts generalizing ts' with
  | nil =>
      cases ts' with
      | nil => rfl
      | cons t' ts' => exact absurd h (by simp [TransitionsAgree])
  | cons t ts ih =>
      cases ts' with
      | nil => exact absurd h (by simp [TransitionsAgree])
      | cons t' ts' =>
          obtain ⟨⟨hi, hb, ha⟩, hrest⟩ := h
          simp only [List.map_cons, hf t t' hi hb ha, ih hrest]

theorem TransitionsAgree.filterMap_eq {ts ts' : List Transition} (h : TransitionsAgree ts ts')
    {β : Type} (f : Transition → Option β)
    (hf : ∀ t t' : Transition, t.instruction = t'.instruction → State.Agree t.before t'.before →
      State.Agree t.after t'.after → f t = f t') :
    ts.filterMap f = ts'.filterMap f := by
  induction ts generalizing ts' with
  | nil =>
      cases ts' with
      | nil => rfl
      | cons t' ts' => exact absurd h (by simp [TransitionsAgree])
  | cons t ts ih =>
      cases ts' with
      | nil => exact absurd h (by simp [TransitionsAgree])
      | cons t' ts' =>
          obtain ⟨⟨hi, hb, ha⟩, hrest⟩ := h
          simp only [List.filterMap_cons, hf t t' hi hb ha, ih hrest]

/-- Fine supplied-store agreement: agreement on every numeric address the first
run actually loads and on every key address it actually reads determines the
whole run up to memory and keys. The hypothesis is over the first run's own
dynamic read footprint, including reads that fault. -/
theorem run_agree_of_reads (program : List BInstr) (fuel : Nat) (s s' : State)
    (hagree : State.Agree s s')
    (hmem : ∀ a ∈ (run program fuel s).loads, s'.memory a = s.memory a)
    (hkey : ∀ i ∈ (run program fuel s).keyReads, s'.keys i = s.keys i) :
    Run.Agree (run program fuel s) (run program fuel s') := by
  induction fuel generalizing s s' with
  | zero => exact ⟨trivial, hagree⟩
  | succ fuel ih =>
      cases hs : stepProgram program s with
      | none =>
          rw [run_of_step_none program s _ hs,
            run_of_step_none program s' _ (stepProgram_none_agree hagree hs)]
          exact ⟨trivial, hagree⟩
      | some t =>
          obtain ⟨hb, hst, hf, he⟩ := step_spec hs
          subst hb
          have hs' : stepProgram program s' =
              some ⟨s', t.instruction, execPrim t.instruction.primitive s'⟩ :=
            stepProgram_of_running (by rw [← hagree.2.2.2.2]; exact hst)
              (by rw [← hagree.2.2.2.1]; exact hf)
          have hone := execPrim_agree_of_agree t.instruction.primitive t.before s' hagree
            (fun dst address hp => hmem _ (by
              simp [run, hs, Run.loads, Transition.load?, hp]))
            (fun dst address hp => hkey _ (by
              simp [run, hs, Run.keyReads, Transition.keyRead?, hp]))
          obtain ⟨hagree', hcells⟩ := hone
          rw [← he] at hagree' hcells
          have hloads : ∀ a ∈ (run program fuel t.after).loads,
              (execPrim t.instruction.primitive s').memory a = t.after.memory a := by
            intro a ha
            rcases hcells a with h | ⟨h1, h2⟩
            · exact h
            · rw [h1, h2]
              apply hmem
              simp only [run, hs, Run.loads, List.filterMap_cons]
              cases t.load? <;> simp_all [Run.loads]
          have hkeys : ∀ i ∈ (run program fuel t.after).keyReads,
              (execPrim t.instruction.primitive s').keys i = t.after.keys i := by
            intro i hi
            rw [execPrim_keys, he, execPrim_keys]
            apply hkey
            simp only [run, hs, Run.keyReads, List.filterMap_cons]
            cases t.keyRead? <;> simp_all [Run.keyReads]
          have hrest := ih t.after (execPrim t.instruction.primitive s') hagree' hloads hkeys
          rw [run_succ_of_step fuel hs, run_succ_of_step fuel hs']
          exact ⟨⟨⟨rfl, hagree, hagree'⟩, hrest.1⟩, hrest.2⟩

theorem Run.Agree.steps {r r' : Run} (h : Run.Agree r r') : r.steps = r'.steps :=
  h.1.length_eq

theorem Run.Agree.categories {r r' : Run} (h : Run.Agree r r') : r.categories = r'.categories :=
  h.1.map_eq _ (fun _ _ hi _ _ => by simp [hi])

theorem Run.Agree.writes {r r' : Run} (h : Run.Agree r r') : r.writes = r'.writes :=
  h.1.filterMap_eq _ (fun t t' hi hb _ => by
    obtain ⟨hr, he, _, _, _⟩ := hb
    simp only [Transition.write?, hi, hr, he])

theorem Run.Agree.reserves {r r' : Run} (h : Run.Agree r r') : r.reserves = r'.reserves :=
  h.1.filterMap_eq _ (fun t t' hi hb _ => by
    obtain ⟨_, he, _, _, _⟩ := hb
    simp only [Transition.reserve?, hi, he])

theorem Run.Agree.result {r r' : Run} (h : Run.Agree r r') : r.result = r'.result := by
  unfold Run.result
  rw [h.2.2.2.2.2]

/-- Coarse supplied-store agreement: two clean-tailed agreeing states whose
memories agree on every cell below the extent have equal memories, so the
fine hypothesis is automatic and the runs agree on every projection. -/
theorem run_agree_of_supplied (program : List BInstr) (fuel : Nat) (s s' : State)
    (hagree : State.Agree s s') (hclean : CleanTail s) (hclean' : CleanTail s')
    (hbelow : ∀ a, a < s.extent → s'.memory a = s.memory a)
    (hkey : ∀ i ∈ (run program fuel s).keyReads, s'.keys i = s.keys i) :
    s'.memory = s.memory ∧ Run.Agree (run program fuel s) (run program fuel s') := by
  have hm : s'.memory = s.memory := by
    funext a
    by_cases ha : a < s.extent
    · exact hbelow a ha
    · rw [hclean a (by omega), hclean' a (by rw [← hagree.2.1]; omega)]
  exact ⟨hm, run_agree_of_reads program fuel s s' hagree (fun a _ => by rw [hm]) hkey⟩

/-! ## Header lemmas behind the `HeaderUse` certificate -/

/-- Generic missing-header fault: any program whose first instruction is the
header load, started at pc 0 in a running state whose address register is
zero and whose cell 0 is absent, faults on its first transition and does
nothing else: one step, no writes, no reservations, unchanged extent. -/
theorem run_missing_header (program : List BInstr)
    (hhead : program[0]? = some headerInstruction) (s : State) (hpc : s.pc = 0)
    (hst : s.status = .running) (hreg : s.regs 0 = 0) (hmem : s.memory 0 = none)
    (fuel : Nat) (hfuel : 1 ≤ fuel) :
    (run program fuel s).final.status = .fault ∧ (run program fuel s).steps = 1 ∧
      (run program fuel s).writes = [] ∧ (run program fuel s).reserves = [] ∧
      (run program fuel s).final.extent = s.extent := by
  obtain ⟨rest, hrest⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
  subst hrest
  have hf : program[s.pc]? = some headerInstruction := by rw [hpc]; exact hhead
  have hstep := stepProgram_of_running hst hf
  have hafter : execPrim headerInstruction.primitive s = { s with status := .fault } := by
    simp only [headerInstruction, execPrim]
    have h0 : s.regs ((0 : Operand).val) = 0 := by simpa using hreg
    by_cases ha : s.regs ((0 : Operand).val) < s.extent
    · rw [if_pos ha, h0, hmem]
    · rw [if_neg ha]
  rw [run_succ_of_step rest hstep]
  simp only [hafter]
  rw [run_of_stopped program rest _ (by simp)]
  simp [Run.steps, Run.writes, Run.reserves, Transition.write?, Transition.reserve?,
    headerInstruction]

/-- Generic header receipt: with the header load first, a present cell 0 and a
zero address register, the first transition of the intact run is that load and
it moves the header word into register 1. -/
theorem run_header_first (program : List BInstr)
    (hhead : program[0]? = some headerInstruction) (s : State) (hpc : s.pc = 0)
    (hst : s.status = .running) (hreg : s.regs 0 = 0) (n : Nat) (hmem : s.memory 0 = some n)
    (hext : 0 < s.extent) (fuel : Nat) (hfuel : 1 ≤ fuel) :
    ∃ t, (run program fuel s).transitions[0]? = some t ∧ t.instruction = headerInstruction ∧
      t.before = s ∧ t.after.regs 1 = n ∧ t.after.status = .running ∧
      t.after.memory = s.memory ∧ t.after.extent = s.extent := by
  obtain ⟨rest, hrest⟩ : ∃ rest, fuel = rest + 1 := ⟨fuel - 1, by omega⟩
  subst hrest
  have hf : program[s.pc]? = some headerInstruction := by rw [hpc]; exact hhead
  have hstep := stepProgram_of_running hst hf
  have hafter : execPrim headerInstruction.primitive s = s.writeNext ((1 : Operand).val) n := by
    simp only [headerInstruction, execPrim]
    have h0 : s.regs ((0 : Operand).val) = 0 := by simpa using hreg
    have ha : s.regs ((0 : Operand).val) < s.extent := by rw [h0]; exact hext
    rw [if_pos ha, h0, hmem]
  refine ⟨⟨s, headerInstruction, execPrim headerInstruction.primitive s⟩, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [run_succ_of_step rest hstep]; rfl
  · simp [hafter, State.writeNext, State.next, put]
  · simp [hafter, State.writeNext, State.next, hst]
  · rw [hafter]; rfl
  · rw [hafter]; rfl

theorem comparisonInputState_extent (xs : List Int) : (comparisonInputState xs).extent = 1 := rfl

theorem wordInputState_extent (width : Nat) (xs : List Int) :
    (wordInputState width xs).extent = xs.length + 1 := rfl

end RMQ.SuccinctFinal.PackedConstruction

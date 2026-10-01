import RMQ.Core.WordRAM.Lifecycle.Calculus
import RMQ.Core.WordRAM.Construction.Calculus

/-! # Supplied-store agreement for evolving lifecycle stores

Read agreement is about the replies at the producing states of paired actual
steps. It includes missing replies and repeated attempts. Memory and input-key
functions may differ elsewhere; registers, owned extents and control agree.
Neither a final answer nor a separately manufactured read log is an assumption.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open PackedConstruction (Operand Prim execPrim put)

def State.Agree (s t : State) : Prop :=
  PackedConstruction.State.Agree s.core t.core ∧
    s.keyExtent = t.keyExtent ∧ s.keyRegExtent = t.keyRegExtent

theorem State.Agree.refl (s : State) : s.Agree s :=
  ⟨PackedConstruction.State.Agree.refl _, rfl, rfl⟩

theorem State.Agree.regs {s t : State} (h : s.Agree t) : s.core.regs = t.core.regs := h.1.1
theorem State.Agree.extent {s t : State} (h : s.Agree t) : s.core.extent = t.core.extent := h.1.2.1
theorem State.Agree.keyRegs {s t : State} (h : s.Agree t) : s.core.keyRegs = t.core.keyRegs := h.1.2.2.1
theorem State.Agree.pc {s t : State} (h : s.Agree t) : s.core.pc = t.core.pc := h.1.2.2.2.1
theorem State.Agree.status {s t : State} (h : s.Agree t) : s.core.status = t.core.status := h.1.2.2.2.2

theorem State.Agree.eq {s t : State} (h : s.Agree t) :
    t = { s with core := { s.core with memory := t.core.memory, keys := t.core.keys } } := by
  rcases s with ⟨sc, sk, sr⟩
  rcases t with ⟨tc, tk, tr⟩
  rcases h with ⟨hc, hk, hr⟩
  dsimp only at hc hk hr ⊢
  cases hk
  cases hr
  exact congrArg (fun c => State.mk c sk sr) hc.eq

/-- Only the executed numeric guard demands a memory reply. A missing cell
inside the extent is a reply `none`; an out-of-extent attempt needs no equality
of inaccessible cells. `loadKey` has the existing unguarded key-oracle lookup. -/
def Instruction.ReadAgree (i : Instruction) (s t : State) : Prop :=
  (∀ dst address, i = .old (.load dst address) →
    s.core.regs address < s.core.extent →
    t.core.memory (s.core.regs address) = s.core.memory (s.core.regs address)) ∧
  (∀ dst address, i = .old (.loadKey dst address) →
    t.core.keys (s.core.regs address) = s.core.keys (s.core.regs address))

theorem Instruction.ReadAgree.refl (i : Instruction) (s : State) : i.ReadAgree s s :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

private theorem old_guarded_agree (p : Prim) (s t : PackedConstruction.State)
    (h : PackedConstruction.State.Agree s t)
    (hm : ∀ dst address, p = .load dst address → s.regs address < s.extent →
      t.memory (s.regs address) = s.memory (s.regs address))
    (hk : ∀ dst address, p = .loadKey dst address →
      t.keys (s.regs address) = s.keys (s.regs address)) :
    PackedConstruction.State.Agree (execPrim p s) (execPrim p t) := by
  classical
  by_cases bad : ∃ dst address, p = .load dst address ∧ ¬s.regs address < s.extent
  · obtain ⟨dst, address, rfl, ha⟩ := bad
    have ht : ¬t.regs address < t.extent := by simpa [← h.1, ← h.2.1] using ha
    simp only [execPrim, if_neg ha, if_neg ht]
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩
  · refine (PackedConstruction.execPrim_agree_of_agree p s t h ?_ hk).1
    intro dst address hp
    apply hm dst address hp
    apply Classical.byContradiction
    intro hn
    exact bad ⟨dst, address, hp, hn⟩

theorem execute_agree (i : Instruction) (s t : State) (h : s.Agree t)
    (hr : i.ReadAgree s t) : (execute i s).Agree (execute i t) := by
  cases i with
  | old p =>
      exact ⟨old_guarded_agree p s.core t.core h.1
        (fun d a he ha => hr.1 d a (congrArg Instruction.old he) ha)
        (fun d a he => hr.2 d a (congrArg Instruction.old he)), h.2⟩
  | releaseCell =>
      rw [h.eq]
      simp only [execute]
      split <;> simp [State.Agree, PackedConstruction.State.Agree, PackedConstruction.State.next]
  | releaseKey =>
      rw [h.eq]
      simp only [execute]
      split <;> simp [State.Agree, PackedConstruction.State.Agree, PackedConstruction.State.next]
  | releaseKeyRegister =>
      rw [h.eq]
      simp only [execute]
      split <;> simp [State.Agree, PackedConstruction.State.Agree, PackedConstruction.State.next]

/-- A scalar write either makes the two replies equal or leaves each old cell
unchanged. This states store/release coherence without equating unrelated cells. -/
def CellsCoherent {α : Type} (before₁ before₂ after₁ after₂ : Nat → α) : Prop :=
  ∀ a, after₁ a = after₂ a ∨ (after₁ a = before₁ a ∧ after₂ a = before₂ a)

private theorem put_coherent {α : Type} (f g : Nat → α) (a : Nat) (v : α) :
    CellsCoherent f g (put f a v) (put g a v) := by
  intro b
  by_cases hb : b = a
  · left; simp [put, hb]
  · right; simp [put, hb]

theorem execute_memory_coherent (i : Instruction) (s t : State) (h : s.Agree t) :
    CellsCoherent s.core.memory t.core.memory (execute i s).core.memory (execute i t).core.memory := by
  cases i with
  | old p =>
      change CellsCoherent _ _ (execPrim p s.core).memory (execPrim p t.core).memory
      rw [PackedConstruction.execPrim_memory_replay, PackedConstruction.execPrim_memory_replay]
      cases p <;> try exact fun _ => Or.inr ⟨rfl, rfl⟩
      case store address value =>
        rw [← h.regs, ← h.extent]
        by_cases ha : s.core.regs address < s.core.extent
        · simp only [if_pos ha]
          exact put_coherent _ _ _ _
        · simp only [if_neg ha]
          exact fun _ => Or.inr ⟨rfl, rfl⟩
  | releaseCell =>
      simp only [execute]
      rw [← h.extent]
      split
      · exact fun _ => Or.inr ⟨rfl, rfl⟩
      · exact put_coherent _ _ _ _
  | releaseKey =>
      simp only [execute]
      split <;> split <;> exact fun _ => Or.inr ⟨rfl, rfl⟩
  | releaseKeyRegister =>
      simp only [execute]
      split <;> split <;> exact fun _ => Or.inr ⟨rfl, rfl⟩

theorem execute_keys_coherent (i : Instruction) (s t : State) (h : s.Agree t) :
    CellsCoherent s.core.keys t.core.keys (execute i s).core.keys (execute i t).core.keys := by
  cases i with
  | old p =>
      change CellsCoherent _ _ (execPrim p s.core).keys (execPrim p t.core).keys
      rw [PackedConstruction.execPrim_keys, PackedConstruction.execPrim_keys]
      exact fun _ => Or.inr ⟨rfl, rfl⟩
  | releaseKey =>
      simp only [execute]
      rw [← h.2.1]
      split
      · exact fun _ => Or.inr ⟨rfl, rfl⟩
      · exact put_coherent _ _ _ _
  | releaseCell =>
      simp only [execute]
      split <;> split <;> exact fun _ => Or.inr ⟨rfl, rfl⟩
  | releaseKeyRegister =>
      simp only [execute]
      split <;> split <;> exact fun _ => Or.inr ⟨rfl, rfl⟩

def Transition.keyRead? (t : Transition) : Option (Nat × Option Int) :=
  match t.action with
  | .instruction (.old (.loadKey _ address)) =>
      some (t.before.core.regs address, t.before.core.keys (t.before.core.regs address))
  | _ => none

def Run.keyReads (r : Run) : List (Nat × Option Int) := r.transitions.filterMap Transition.keyRead?

theorem instruction_read_agree (i : Instruction) (s t : State) (h : s.Agree t)
    (hr : i.ReadAgree s t) :
    (Transition.mk s (.instruction i) (execute i s)).read? =
      (Transition.mk t (.instruction i) (execute i t)).read? := by
  cases i with
  | old p =>
      cases p <;> try rfl
      case load dst address =>
        simp only [Transition.read?]
        rw [← h.regs, ← h.extent]
        by_cases ha : s.core.regs address < s.core.extent
        · simp [ha, hr.1 dst address rfl ha]
        · simp [ha]
  | releaseCell | releaseKey | releaseKeyRegister => rfl

theorem instruction_keyRead_agree (i : Instruction) (s t : State) (h : s.Agree t)
    (hr : i.ReadAgree s t) :
    (Transition.mk s (.instruction i) (execute i s)).keyRead? =
      (Transition.mk t (.instruction i) (execute i t)).keyRead? := by
  cases i with
  | old p =>
      cases p <;> try rfl
      case loadKey dst address =>
        simp only [Transition.keyRead?]
        rw [← h.regs, hr.2 dst address rfl]
  | releaseCell | releaseKey | releaseKeyRegister => rfl

def Transition.Agree (a b : Transition) : Prop :=
  a.action = b.action ∧ a.before.Agree b.before ∧ a.after.Agree b.after ∧
    a.read? = b.read? ∧ a.keyRead? = b.keyRead?

theorem step_none_agree (program : List Instruction) (s t : State) (h : s.Agree t)
    (hs : step program s = none) : step program t = none := by
  by_cases hrun : s.core.status = .running
  · cases hf : program[s.core.pc]? with
    | none => simp [step, ← h.pc, ← h.status, hrun, hf]
    | some i => simp [step, hrun, hf] at hs
  · simp [step, ← h.status, hrun]

theorem step_agree_of_reads {program : List Instruction} {s t : State} {a : Transition}
    (hs : step program s = some a) (h : s.Agree t)
    (hr : ∀ i, a.action = .instruction i → i.ReadAgree s t) :
    ∃ b, step program t = some b ∧ a.Agree b := by
  obtain ⟨hb, hrun, i, hfetch, haction, hafter⟩ := step_spec hs
  have ht : step program t = some ⟨t, .instruction i, execute i t⟩ :=
    step_of_running (by rw [← h.status]; exact hrun) (by rw [← h.pc]; exact hfetch)
  refine ⟨_, ht, haction, ?_, ?_, ?_, ?_⟩
  · simpa [hb] using h
  · simpa [hafter] using execute_agree i s t h (hr i haction)
  · simpa [Transition.read?, hb, haction] using instruction_read_agree i s t h (hr i haction)
  · simpa [Transition.keyRead?, hb, haction] using instruction_keyRead_agree i s t h (hr i haction)

/-- The condition is recursively attached to the two actual producing prefixes.
No endpoint agreement is a field. Initial state agreement forces the two fetches
to succeed or stop together; each subsequent agreement is derived from replies. -/
def DynamicReadsAgree (program : List Instruction) : Nat → State → State → Prop
  | 0, _, _ => True
  | fuel + 1, s, t =>
      match step program s, step program t with
      | some a, some b =>
          (∀ i, a.action = .instruction i → i.ReadAgree s t) ∧
            DynamicReadsAgree program fuel a.after b.after
      | _, _ => True

theorem DynamicReadsAgree.refl (program : List Instruction) (fuel : Nat) (s : State) :
    DynamicReadsAgree program fuel s s := by
  induction fuel generalizing s with
  | zero => trivial
  | succ fuel ih =>
      cases h : step program s with
      | none => simp [DynamicReadsAgree, h]
      | some t =>
          simp only [DynamicReadsAgree, h]
          exact ⟨fun i _ => Instruction.ReadAgree.refl i s, ih t.after⟩

/-- Pairing is positional: equal repeated event values remain distinct entries. -/
def TransitionsAgree : List Transition → List Transition → Prop
  | [], [] => True
  | a :: as, b :: bs => a.Agree b ∧ TransitionsAgree as bs
  | _, _ => False

def Run.Agree (r q : Run) : Prop :=
  TransitionsAgree r.transitions q.transitions ∧ r.final.Agree q.final

theorem run_agree_of_dynamic_reads (program : List Instruction) (fuel : Nat) (s t : State)
    (h : s.Agree t) (hr : DynamicReadsAgree program fuel s t) :
    (run program fuel s).Agree (run program fuel t) := by
  induction fuel generalizing s t with
  | zero => exact ⟨trivial, h⟩
  | succ fuel ih =>
      cases hs : step program s with
      | none =>
          have ht := step_none_agree program s t h hs
          simp only [run, hs, ht, Run.Agree, TransitionsAgree]
          exact ⟨trivial, h⟩
      | some a =>
          obtain ⟨_, hrun, i, hfetch, haction, _⟩ := step_spec hs
          let b : Transition := ⟨t, .instruction i, execute i t⟩
          have ht : step program t = some b := step_of_running
            (by rw [← h.status]; exact hrun) (by rw [← h.pc]; exact hfetch)
          have hcurrent : (∀ j, a.action = .instruction j → j.ReadAgree s t) ∧
              DynamicReadsAgree program fuel a.after b.after := by
            simpa [DynamicReadsAgree, hs, ht] using hr
          obtain ⟨b', ht', hab⟩ := step_agree_of_reads hs h hcurrent.1
          have heq : b' = b := Option.some.inj (ht'.symm.trans ht)
          subst b'
          have hrest := ih a.after b.after hab.2.2.1 hcurrent.2
          simp only [run, hs, ht, Run.Agree, TransitionsAgree]
          exact ⟨⟨hab, hrest.1⟩, hrest.2⟩

theorem TransitionsAgree.map_eq {ts us : List Transition} (h : TransitionsAgree ts us)
    {α : Type} (f : Transition → α) (hf : ∀ a b, a.Agree b → f a = f b) :
    ts.map f = us.map f := by
  induction ts generalizing us with
  | nil => cases us <;> simp_all [TransitionsAgree]
  | cons a ts ih =>
      cases us with
      | nil => simp [TransitionsAgree] at h
      | cons b us =>
          simp only [List.map_cons, hf a b h.1, ih h.2]

theorem TransitionsAgree.filterMap_eq {ts us : List Transition} (h : TransitionsAgree ts us)
    {α : Type} (f : Transition → Option α) (hf : ∀ a b, a.Agree b → f a = f b) :
    ts.filterMap f = us.filterMap f := by
  induction ts generalizing us with
  | nil => cases us <;> simp_all [TransitionsAgree]
  | cons a ts ih =>
      cases us with
      | nil => simp [TransitionsAgree] at h
      | cons b us =>
          simp only [List.filterMap_cons, hf a b h.1, ih h.2]

theorem Run.Agree.steps {r q : Run} (h : r.Agree q) : r.steps = q.steps := by
  have hm := h.1.map_eq (fun _ : Transition => ()) (fun _ _ _ => rfl)
  simpa [Run.steps] using congrArg List.length hm

theorem Run.Agree.actions {r q : Run} (h : r.Agree q) :
    r.transitions.map (·.action) = q.transitions.map (·.action) :=
  h.1.map_eq _ (fun _ _ hab => hab.1)

theorem Run.Agree.categories {r q : Run} (h : r.Agree q) : r.categories = q.categories :=
  h.1.map_eq _ (fun _ _ hab => congrArg Action.category hab.1)

theorem Run.Agree.categoryCount {r q : Run} (h : r.Agree q) (c : Category) :
    r.categoryCount c = q.categoryCount c := by
  simp only [Run.categoryCount, h.categories]

theorem Run.Agree.reads {r q : Run} (h : r.Agree q) : r.reads = q.reads :=
  h.1.filterMap_eq _ (fun _ _ hab => hab.2.2.2.1)

theorem Run.Agree.keyReads {r q : Run} (h : r.Agree q) : r.keyReads = q.keyReads :=
  h.1.filterMap_eq _ (fun _ _ hab => hab.2.2.2.2)

theorem Run.Agree.writes {r q : Run} (h : r.Agree q) : r.writes = q.writes := by
  apply h.1.filterMap_eq
  intro a b hab
  simp only [Transition.write?, hab.1, hab.2.1.regs, hab.2.1.extent]

theorem Run.Agree.final_regs {r q : Run} (h : r.Agree q) :
    r.final.core.regs = q.final.core.regs := h.2.regs

theorem Run.Agree.final_status {r q : Run} (h : r.Agree q) :
    r.final.core.status = q.final.core.status := h.2.status

theorem Run.Agree.result {r q : Run} (h : r.Agree q) :
    (match r.final.core.status with | .halted v => some v | _ => none) =
    (match q.final.core.status with | .halted v => some v | _ => none) := by
  rw [h.final_status]

theorem executeBoundary_agree (b : Boundary) (s t : State) (h : s.Agree t) :
    (executeBoundary b s).Agree (executeBoundary b t) := by
  rw [h.eq]
  cases b <;> simp [executeBoundary, State.Agree, PackedConstruction.State.Agree]

theorem runBoundary_agree (bs : List Boundary) (s t : State) (h : s.Agree t) :
    (runBoundary bs s).Agree (runBoundary bs t) := by
  induction bs generalizing s t with
  | nil => exact ⟨trivial, h⟩
  | cons b bs ih =>
      have hafter := executeBoundary_agree b s t h
      cases hs : s.core.status with
      | running =>
          simp only [runBoundary, boundaryStep, hs, ← h.status, Run.Agree, TransitionsAgree]
          exact ⟨trivial, h⟩
      | fault =>
          simp only [runBoundary, boundaryStep, hs, ← h.status, Run.Agree, TransitionsAgree]
          exact ⟨trivial, h⟩
      | halted value =>
          have hr := ih (executeBoundary b s) (executeBoundary b t) hafter
          simp only [runBoundary, boundaryStep, hs, ← h.status, Run.Agree, TransitionsAgree]
          exact ⟨⟨⟨rfl, h, hafter, rfl, rfl⟩, hr.1⟩, hr.2⟩

theorem requestProtocol_agree (entry : Operand) (left right : Nat) (s t : State)
    (h : s.Agree t) :
    (requestProtocol entry left right s).Agree (requestProtocol entry left right t) :=
  runBoundary_agree _ s t h

theorem TransitionsAgree.occurrence {ts us : List Transition} (h : TransitionsAgree ts us)
    {k : Nat} {a : Transition} (ha : ts[k]? = some a) :
    ∃ b, us[k]? = some b ∧ a.Agree b := by
  induction ts generalizing us k with
  | nil => simp at ha
  | cons first ts ih =>
      cases us with
      | nil => simp [TransitionsAgree] at h
      | cons second us =>
          cases k with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
              subst a
              exact ⟨second, rfl, h.1⟩
          | succ k =>
              simp only [List.getElem?_cons_succ] at ha ⊢
              exact ih h.2 ha

theorem Run.Agree.occurrence {r q : Run} (h : r.Agree q)
    {k : Nat} {a : Transition} (ha : r.transitions[k]? = some a) :
    ∃ b, q.transitions[k]? = some b ∧ a.Agree b := h.1.occurrence ha

/-- The instruction and its producing state come from this exact occurrence of
the actual run. The conclusion constrains the loaded numeric register itself. -/
theorem load_occurrence_value {program : List Instruction} {fuel k : Nat}
    {s : State} {t : Transition} {dst address : Operand} {value : Nat}
    (hpos : (run program fuel s).transitions[k]? = some t)
    (hi : t.action = .instruction (.old (.load dst address)))
    (ha : t.before.core.regs address < t.before.core.extent)
    (hv : t.before.core.memory (t.before.core.regs address) = some value) :
    t.after.core.regs dst = value ∧
    t.read? = some (t.before.core.regs address, some value) ∧
    t.after.core.status = .running := by
  obtain ⟨_, hstep⟩ := run_transition_at hpos
  obtain ⟨_, hrun, i, _, haction, hafter⟩ := step_spec hstep
  have he : i = .old (.load dst address) := Action.instruction.inj (haction.symm.trans hi)
  rw [he] at hafter
  refine ⟨?_, ?_, ?_⟩
  · rw [hafter]
    simp [execute, execPrim, ha, hv, PackedConstruction.State.writeNext,
      PackedConstruction.State.next, put]
  · simp [Transition.read?, hi, ha, hv]
  · rw [hafter]
    simp [execute, execPrim, ha, hv, PackedConstruction.State.writeNext,
      PackedConstruction.State.next, hrun]

/-- Different successful replies at one shared address force different loaded
register values at matched actual occurrences, not merely unequal log records. -/
theorem load_occurrence_value_dependency {program : List Instruction} {fuel k : Nat}
    {s u : State} {t v : Transition} {dst address : Operand} {x y : Nat}
    (ht : (run program fuel s).transitions[k]? = some t)
    (hv : (run program fuel u).transitions[k]? = some v)
    (hit : t.action = .instruction (.old (.load dst address)))
    (hiv : v.action = .instruction (.old (.load dst address)))
    (haddress : t.before.core.regs address = v.before.core.regs address)
    (hat : t.before.core.regs address < t.before.core.extent)
    (hav : v.before.core.regs address < v.before.core.extent)
    (hxt : t.before.core.memory (t.before.core.regs address) = some x)
    (hyv : v.before.core.memory (v.before.core.regs address) = some y)
    (hne : x ≠ y) :
    t.read? = some (t.before.core.regs address, some x) ∧
    v.read? = some (t.before.core.regs address, some y) ∧
    t.after.core.regs dst ≠ v.after.core.regs dst := by
  obtain ⟨hx, hrt, _⟩ := load_occurrence_value ht hit hat hxt
  obtain ⟨hy, hrv, _⟩ := load_occurrence_value hv hiv hav hyv
  exact ⟨hrt, by simpa [haddress] using hrv, by simpa [hx, hy] using hne⟩

/-- This negative control challenges exactly the positive guarded reply
predicate. Removing the source cell cannot satisfy the successful-read guard. -/
theorem absent_source_rejects_read_agreement (s : State) (dst address : Operand) (v : Nat)
    (ha : s.core.regs address < s.core.extent)
    (hv : s.core.memory (s.core.regs address) = some v) :
    ¬Instruction.ReadAgree (.old (.load dst address)) s
      { s with core := { s.core with memory := put s.core.memory (s.core.regs address) none } } := by
  intro h
  have he := h.1 dst address rfl ha
  simp [put, hv] at he

end RMQ.SuccinctFinal.PackedLifecycle

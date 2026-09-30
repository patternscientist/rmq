import RMQ.Core.WordRAM.Lifecycle.Input

/-! # Charged descriptor and request transfer

The base is transferred from output register 3. Size and output length are
loaded from its produced metadata; the current request is read from the input
arena before copying or retirement can overwrite its two cells.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Descriptor

open PackedConstruction (Operand Prim execPrim put Arithmetic)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def requestBase : InputModel → Nat → Nat
  | .word, n => n + 1
  | .comparison, _ => 1

def code (model : InputModel) : List Instruction := [
  .old (.move 0 3),
  .old (.load 302 0),
  .old (.constant 4 7),
  .old (.arithmetic .add 4 0 4),
  .old (.load 2 4),
  .old (match model with | .word => .move 4 302 | .comparison => .constant 4 0),
  .old (.constant 5 1),
  .old (.arithmetic .add 4 4 5),
  .old (.load 300 4),
  .old (.arithmetic .add 4 4 5),
  .old (.load 301 4)]

def Hosted (program : List Instruction) (base : Nat) (model : InputModel) : Prop :=
  ∀ i, i < 11 → program[base + i]? = (code model)[i]?

def Entry (model : InputModel) (base B n M left right : Nat) (s : State) : Prop :=
  s.core.status = .running ∧ s.core.pc = base ∧ s.core.regs 3 = B ∧
    B + 7 < s.core.extent ∧ s.core.memory B = some n ∧
    s.core.memory (B + 7) = some M ∧
    requestBase model n + 1 < s.core.extent ∧
    s.core.memory (requestBase model n) = some left ∧
    s.core.memory (requestBase model n + 1) = some right

def Result (base B n M left right : Nat) (s t : State) : Prop :=
  t.core.status = .running ∧ t.core.pc = base + 11 ∧
    t.core.regs 0 = B ∧ t.core.regs 2 = M ∧ t.core.regs 302 = n ∧
    t.core.regs 300 = left ∧ t.core.regs 301 = right ∧
    t.core.memory = s.core.memory ∧ t.core.extent = s.core.extent ∧
    t.core.keys = s.core.keys ∧ t.core.keyRegs = s.core.keyRegs ∧
    t.keyExtent = s.keyExtent ∧ t.keyRegExtent = s.keyRegExtent ∧
    (∀ r, 400 ≤ r → t.core.regs r = s.core.regs r)

theorem transfer {program : List Instruction} {model : InputModel} {base B n M left right : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s) :
    Result base B n M left right s (run program 11 s).final ∧
      (run program 11 s).steps = 11 := by
  obtain ⟨hr, hpc, hB, hbound, hn, hM, hreq, hl, hright⟩ := entry
  have h0 := host 0 (by decide)
  have h1 := host 1 (by decide)
  have h2 := host 2 (by decide)
  have h3 := host 3 (by decide)
  have h4 := host 4 (by decide)
  have h5 := host 5 (by decide)
  have h6 := host 6 (by decide)
  have h7 := host 7 (by decide)
  have h8 := host 8 (by decide)
  have h9 := host 9 (by decide)
  have h10 := host 10 (by decide)
  have hBlt : B < s.core.extent := by omega
  have hreqlt : requestBase model n < s.core.extent := by omega
  cases model <;>
    simp only [code, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;>
    simp only [requestBase] at hreq hreqlt hl hright <;>
    simp [run, step, hpc, hr, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next,
      put, Arithmetic.eval, hB, hBlt, hbound, hn, hM, hl, hright, hreq, hreqlt,
      Nat.add_assoc, Result, Run.steps] <;>
    intro r h400 <;> simp [put, show r ≠ 0 by omega, show r ≠ 2 by omega,
      show r ≠ 4 by omega, show r ≠ 5 by omega, show r ≠ 300 by omega,
      show r ≠ 301 by omega, show r ≠ 302 by omega]

@[simp] theorem code_length (model : InputModel) : (code model).length = 11 := rfl

/-- Proof-erased old instruction view of this same static code list. -/
def coreCode (model : InputModel) : List PackedConstruction.BInstr :=
  (code model).filterMap (fun i => match i with | .old p => some ⟨p⟩ | _ => none)

theorem code_eq (model : InputModel) : code model = (coreCode model).map oldInstruction := by
  cases model <;> rfl

@[simp] theorem coreCode_length (model : InputModel) : (coreCode model).length = 11 := by
  cases model <;> rfl

theorem code_fields (model : InputModel) :
    (code model)[0]? = some (.old (.move 0 3)) ∧
      (code model)[1]? = some (.old (.load 302 0)) ∧
      (code model)[4]? = some (.old (.load 2 4)) ∧
      (code model)[8]? = some (.old (.load 300 4)) ∧
      (code model)[10]? = some (.old (.load 301 4)) := by simp [code]

theorem code_encoding (model : InputModel) :
    (code model).map Instruction.encoding =
      [[2,0,3], [0,302,0], [1,4,7], [3,0,4,0,4], [0,2,4],
       (match model with | .word => [2,4,302] | .comparison => [1,4,0]),
       [1,5,1], [3,0,4,4,5], [0,300,4], [3,0,4,4,5], [0,301,4]] := by
  cases model <;> rfl

theorem code_fits {model : InputModel} {W : Nat} (hw : 32 ≤ W)
    {i : Instruction} (_hi : i ∈ code model) : i.Fits W := by
  have hw32 : 2^32 ≤ 2^W := Nat.pow_le_pow_right (by decide) hw
  cases i with
  | old p =>
      intro word hword
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hword
      exact Nat.lt_of_lt_of_le v.isLt hw32
  | releaseCell => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKey => simp [Instruction.Fits, Instruction.encoding]; omega
  | releaseKeyRegister => simp [Instruction.Fits, Instruction.encoding]; omega

def Frame (s t : State) : Prop :=
  t.core.memory = s.core.memory ∧ t.core.extent = s.core.extent ∧
    t.core.keys = s.core.keys ∧ t.core.keyRegs = s.core.keyRegs ∧
    t.keyExtent = s.keyExtent ∧ t.keyRegExtent = s.keyRegExtent ∧
    ∀ r, 400 ≤ r → t.core.regs r = s.core.regs r

theorem Frame.refl (s : State) : Frame s s := ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

theorem Frame.trans {s t u : State} (h : Frame s t) (g : Frame t u) : Frame s u :=
  ⟨g.1.trans h.1, g.2.1.trans h.2.1, g.2.2.1.trans h.2.2.1,
    g.2.2.2.1.trans h.2.2.2.1, g.2.2.2.2.1.trans h.2.2.2.2.1,
    g.2.2.2.2.2.1.trans h.2.2.2.2.2.1,
    fun r hr => (g.2.2.2.2.2.2 r hr).trans (h.2.2.2.2.2.2 r hr)⟩

theorem Frame.closed {s t : State} (frame : Frame s t) (hc : s.Closed) : t.Closed := by
  simpa [State.Closed, PackedConstruction.CleanTail, frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2.1] using hc

theorem instruction_frame {model : InputModel} {i : Instruction}
    (hi : i ∈ code model) (s : State) : Frame s (execute i s) := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases model
  all_goals simp [Frame, execute, execPrim, PackedConstruction.State.next,
    PackedConstruction.State.writeNext, put]
  all_goals
    repeat' split
    all_goals simp_all [put]
    all_goals omega

def UsesCode (model : InputModel) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, ∃ i ∈ code model, t.action = .instruction i

theorem run_frame_of_uses {program : List Instruction} {model : InputModel}
    {fuel : Nat} {s : State} (uses : UsesCode model (run program fuel s)) :
    Frame s (run program fuel s).final := by
  induction fuel generalizing s with
  | zero => exact Frame.refl s
  | succ fuel ih =>
      cases hs : step program s with
      | none => simpa [run, hs] using Frame.refl s
      | some t =>
          obtain ⟨_, _, i, _, hi, ha⟩ := step_spec hs
          obtain ⟨j, hj, hjt⟩ := uses t (by simp [run, hs])
          have heq : j=i := Action.instruction.inj (hjt.symm.trans hi)
          subst j
          have first : Frame s t.after := by rw [ha]; exact instruction_frame hj s
          have rest := ih (s := t.after) (fun u hu => uses u (by simp [run, hs, hu]))
          simpa [run, hs] using first.trans rest

theorem uses_prefix {program : List Instruction} {model : InputModel}
    {fuel count : Nat} {s : State} (uses : UsesCode model (run program fuel s))
    (hc : count ≤ fuel) : UsesCode model (run program count s) := by
  intro t ht
  apply uses t
  rw [show fuel=count+(fuel-count) by omega, run_add]
  exact List.mem_append_left _ ht

def categories : List Category :=
  [.old .register, .old .read, .old .register, .old .arithmetic, .old .read,
    .old .register, .old .register, .old .arithmetic, .old .read, .old .arithmetic, .old .read]

theorem execution_shape {program : List Instruction} {model : InputModel} {base B n M left right : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s) :
    UsesCode model (run program 11 s) ∧ (run program 11 s).categories = categories := by
  obtain ⟨hr, hpc, hB, hbound, hn, hM, hreq, hl, hright⟩ := entry
  have get : ∀ i, i < 11 → program[base+i]? = (code model)[i]? := host
  have h0 : program[base]? = some (.old (.move 0 3)) := by simpa [code] using host 0 (by decide)
  have hBlt : B < s.core.extent := by omega
  have hreqlt : requestBase model n < s.core.extent := by omega
  cases model <;> simp only [requestBase] at hreq hreqlt hl hright <;>
    simp [UsesCode, categories, Run.categories, Action.category, Prim.category,
      run, step, hpc, hr, h0, get, code,
      execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next,
      put, Arithmetic.eval, hB, hBlt, hbound, hn, hM, hl, hright, hreq, hreqlt, Nat.add_assoc]

theorem transfer_prefix_frame {program : List Instruction} {model : InputModel} {base B n M left right : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s)
    {fuel : Nat} (hf : fuel ≤ 11) : Frame s (run program fuel s).final :=
  run_frame_of_uses (uses_prefix (execution_shape host entry).1 hf)

def Good (W : Nat) (program : List Instruction) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, t.Safe W program.length

theorem transfer_good {program : List Instruction} {model : InputModel} {base B n M left right W : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s)
    (hw : 32 ≤ W) (fit : s.Fits W) : Good W program (run program 11 s) := by
  obtain ⟨hr, hpc, hB, hbound, hn, hM, hreq, hl, hright⟩ := entry
  have get : ∀ i, i < 11 → program[base+i]? = (code model)[i]? := host
  have h0 : program[base]? = some (.old (.move 0 3)) := by simpa [code] using host 0 (by decide)
  have hBlt : B < s.core.extent := by omega
  have hreqlt : requestBase model n < s.core.extent := by omega
  have he := fit.1.2.2.1
  have hnfit := fit.1.2.2.2.1 B n hn
  have hMfit := fit.1.2.2.2.1 (B+7) M hM
  have hlfit := fit.1.2.2.2.1 (requestBase model n) left hl
  have hrfit := fit.1.2.2.2.1 (requestBase model n+1) right hright
  cases model <;> simp only [requestBase] at hreq hreqlt hl hright <;>
    simp [Good, run, step, hpc, hr, h0, get, code,
      execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next,
      put, Arithmetic.eval, hB, hBlt, hbound, hn, hM, hl, hright, hreq, hreqlt, Nat.add_assoc,
      Transition.Safe, Instruction.Safe, Prim.Safe, Prim.SafeAt, Prim.operandsFit_of_width _ hw,
      hnfit, hMfit, hlfit, hrfit] <;> omega

theorem transfer_safe {program : List Instruction} {model : InputModel} {base B n M left right W : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s)
    (hw : 32 ≤ W) (fit : s.Fits W) (plen : program.length < 2^W) :
    Good W program (run program 11 s) ∧ (run program 11 s).final.Fits W ∧
      ∀ t ∈ (run program 11 s).transitions, t.before.Fits W ∧ t.after.Fits W := by
  have hg := transfer_good host entry hw fit
  exact ⟨hg, run_fits fit plen hg⟩

def OutputReceipt (t : Transition) : Prop :=
  t.action = .instruction (.old (.move 0 3)) ∧
    t.after = execute (.old (.move 0 3)) t.before ∧
    t.after.core.regs 0 = t.before.core.regs 3

theorem output_projection (s : State) :
    (execute (.old (.move 0 3)) s).core.regs 0 = s.core.regs 3 := by
  simp [execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next, put]

/-- A distinct source value distinguishes the charged transfer from a wrong
source-register move, even if both movements have the same category and cost. -/
theorem output_wrong_source (s : State) (source : Operand)
    (different : s.core.regs source ≠ s.core.regs 3) :
    (execute (.old (.move 0 source)) s).core.regs 0 ≠
      (execute (.old (.move 0 3)) s).core.regs 0 := by
  simpa [execute, execPrim, PackedConstruction.State.writeNext,
    PackedConstruction.State.next, put] using different

theorem output_transfer_at {program : List Instruction} {model : InputModel} {base B n M left right : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s) :
    ∃ t, (run program 11 s).transitions[0]? = some t ∧ t.before = s ∧
      OutputReceipt t ∧ t.after.core.regs 0 = B := by
  have fetch : program[s.core.pc]? = some (.old (.move 0 3)) := by
    rw [entry.2.1]
    simpa [code] using host 0 (by decide)
  have hs := step_of_running entry.1 fetch
  refine ⟨⟨s, .instruction (.old (.move 0 3)), execute (.old (.move 0 3)) s⟩,
    by simp [run, hs], rfl, ?_, ?_⟩
  · exact ⟨rfl, rfl, output_projection s⟩
  · exact (output_projection s).trans entry.2.2.1

def ReadReceipt (dst addr : Operand) (address value : Nat) (t : Transition) : Prop :=
  t.action = .instruction (.old (.load dst addr)) ∧
    t.before.core.regs addr = address ∧ address < t.before.core.extent ∧
    t.before.core.memory address = some value ∧
    t.after = execute (.old (.load dst addr)) t.before ∧ t.after.core.regs dst = value

/-- The metadata and request values are read at these four actual occurrences.
The fetched load operands, resolved addresses and pre-state cells are retained. -/
theorem read_occurrences {program : List Instruction} {model : InputModel} {base B n M left right : Nat}
    {s : State} (host : Hosted program base model) (entry : Entry model base B n M left right s) :
    (∃ t, (run program 11 s).transitions[1]? = some t ∧ ReadReceipt 302 0 B n t) ∧
      (∃ t, (run program 11 s).transitions[4]? = some t ∧ ReadReceipt 2 4 (B+7) M t) ∧
      (∃ t, (run program 11 s).transitions[8]? = some t ∧
        ReadReceipt 300 4 (requestBase model n) left t) ∧
      (∃ t, (run program 11 s).transitions[10]? = some t ∧
        ReadReceipt 301 4 (requestBase model n+1) right t) := by
  obtain ⟨hr, hpc, hB, hbound, hn, hM, hreq, hl, hright⟩ := entry
  have get : ∀ i, i < 11 → program[base+i]? = (code model)[i]? := host
  have h0 : program[base]? = some (.old (.move 0 3)) := by simpa [code] using host 0 (by decide)
  have hBlt : B < s.core.extent := by omega
  have hreqlt : requestBase model n < s.core.extent := by omega
  cases model <;> simp only [requestBase] at hreq hreqlt hl hright ⊢ <;>
    simp [ReadReceipt, run, step, hpc, hr, h0, get, code,
      execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next,
      put, Arithmetic.eval, hB, hBlt, hbound, hn, hM, hl, hright, hreq, hreqlt, Nat.add_assoc]

theorem occurrence_prestate {program : List Instruction} {s : State} {k : Nat} {t : Transition}
    (ht : (run program 11 s).transitions[k]? = some t) :
    t.before = (run program k s).final ∧ step program t.before = some t := run_transition_at ht

end RMQ.SuccinctFinal.PackedLifecycle.Descriptor

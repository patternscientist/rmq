import RMQ.Core.WordRAM.Packed.Primitive

/-!
# Exact execution calculus for the physical packed-query machine

All logs below are observations of `Primitive.run` itself. Composition retains
complete transitions, including pre-states and failed loads. The positional
theorems use transition indices, so equal repeated receipts remain distinct.
The memory-agreement proof follows the actual dynamic execution; it does not
assume a static footprint or an independent semantic evaluator.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

@[simp] theorem run_zero (memory : Memory) (program : Program) (s : State) :
    run memory program 0 s = ⟨s, []⟩ := rfl

theorem run_of_step_none (memory : Memory) (program : Program) (s : State)
    (fuel : Nat) (h : step memory program s = none) :
    run memory program fuel s = ⟨s, []⟩ := by
  cases fuel <;> simp [run, h]

/-- Split an actual run at any fuel boundary, retaining every transition. -/
theorem run_add (memory : Memory) (program : Program) (a b : Nat) (s : State) :
    run memory program (a + b) s =
      let first := run memory program a s
      let second := run memory program b first.final
      ⟨second.final, first.transitions ++ second.transitions⟩ := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
      cases h : step memory program s with
      | none => simp [Nat.succ_add, run, h, run_of_step_none memory program s b h]
      | some t =>
          simpa [Nat.succ_add, run, h, List.cons_append] using
            congrArg (fun r : Run => Run.mk r.final (t :: r.transitions))
              (ih t.after)

/-- An exact transition segment consumes precisely its own length in fuel. -/
def RunsTo (memory : Memory) (program : Program) (s s' : State)
    (transitions : List Transition) : Prop :=
  run memory program transitions.length s = ⟨s', transitions⟩

theorem RunsTo.refl (memory : Memory) (program : Program) (s : State) :
    RunsTo memory program s s [] := rfl

theorem RunsTo.trans {memory : Memory} {program : Program}
    {s₁ s₂ s₃ : State} {ts₁ ts₂ : List Transition}
    (h₁ : RunsTo memory program s₁ s₂ ts₁)
    (h₂ : RunsTo memory program s₂ s₃ ts₂) :
    RunsTo memory program s₁ s₃ (ts₁ ++ ts₂) := by
  unfold RunsTo at h₁ h₂ ⊢
  rw [List.length_append, run_add, h₁]
  simp [h₂]

theorem RunsTo.of_step {memory : Memory} {program : Program} {s : State}
    {t : Transition} (h : step memory program s = some t) :
    RunsTo memory program s t.after [t] := by
  simp [RunsTo, run, h]

/-- The fetched instruction's result, rather than a supplied answer, is used. -/
theorem RunsTo.instruction {memory : Memory} {program : Program} {s : State}
    {i : Instruction} (hrunning : s.status = .running)
    (hfetch : program[s.pc]? = some i) :
    RunsTo memory program s (execute memory i s).1
      [⟨s, i, (execute memory i s).1, (execute memory i s).2⟩] := by
  apply RunsTo.of_step
  simp [step, hrunning, hfetch]

theorem run_of_halted (memory : Memory) (program : Program) (fuel : Nat)
    (s : State) (value : Nat) (h : s.status = .halted value) :
    run memory program fuel s = ⟨s, []⟩ :=
  run_of_step_none memory program s fuel (by simp [step, h])

theorem run_add_of_halted (memory : Memory) (program : Program) (a b : Nat)
    (s : State) (value : Nat)
    (h : (run memory program a s).final.status = .halted value) :
    run memory program (a + b) s = run memory program a s := by
  rw [run_add]
  dsimp only
  rw [run_of_halted memory program b _ value h]
  simp

theorem RunsTo.fuel_extension {memory : Memory} {program : Program}
    {s s' : State} {ts : List Transition} {value : Nat}
    (h : RunsTo memory program s s' ts) (halted : s'.status = .halted value)
    (extra : Nat) :
    run memory program (ts.length + extra) s = ⟨s', ts⟩ := by
  unfold RunsTo at h
  rw [run_add, h]
  dsimp only
  rw [run_of_halted memory program extra s' value halted]
  simp

def Run.categoryCount (r : Run) (c : Category) : Nat := r.categories.count c

theorem Run.steps_eq_categories_length (r : Run) :
    r.steps = r.categories.length := by simp [Run.steps, Run.categories]

private theorem categories_partition (cs : List Category) :
    cs.length = cs.count .memoryRead + cs.count .registerWrite +
      cs.count .arithmetic + cs.count .comparison + cs.count .branch +
      cs.count .control := by
  induction cs with
  | nil => simp
  | cons c cs ih => cases c <;> simp_all <;> omega

/-- The six disjoint categories partition the executed primitive steps exactly. -/
theorem Run.steps_partition (r : Run) :
    r.steps = r.categoryCount .memoryRead + r.categoryCount .registerWrite +
      r.categoryCount .arithmetic + r.categoryCount .comparison +
      r.categoryCount .branch + r.categoryCount .control := by
  rw [r.steps_eq_categories_length]
  exact categories_partition r.categories

theorem run_steps_le_fuel (memory : Memory) (program : Program) (fuel : Nat)
    (s : State) : (run memory program fuel s).steps ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [run, Run.steps]
  | succ fuel ih =>
      cases h : step memory program s with
      | none => simp [run, h, Run.steps]
      | some t => simpa [run, h, Run.steps] using Nat.succ_le_succ (ih t.after)

/-- A successful fetch records exactly the producing state and execution. -/
theorem step_spec {memory : Memory} {program : Program} {s : State}
    {t : Transition} (h : step memory program s = some t) :
    t.before = s ∧ s.status = .running ∧
      program[s.pc]? = some t.instruction ∧
      execute memory t.instruction s = (t.after, t.receipt) := by
  cases hs : s.status with
  | halted value => simp [step, hs] at h
  | fault => simp [step, hs] at h
  | running =>
      cases hf : program[s.pc]? with
      | none => simp [step, hs, hf] at h
      | some i =>
          simp only [step, hs, hf, Option.some.injEq] at h
          subst t
          simp

/-- Index `k` identifies the actual occurrence and its executed prefix. -/
theorem run_transition_at {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition}
    (h : (run memory program fuel s).transitions[k]? = some t) :
    t.before = (run memory program k s).final ∧
      step memory program t.before = some t := by
  induction fuel generalizing s k with
  | zero => simp [run] at h
  | succ fuel ih =>
      cases hs : step memory program s with
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

theorem run_transition_spec {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition}
    (h : (run memory program fuel s).transitions[k]? = some t) :
    t.before = (run memory program k s).final ∧
      t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      execute memory t.instruction t.before = (t.after, t.receipt) := by
  obtain ⟨hb, hs⟩ := run_transition_at h
  exact ⟨hb, (step_spec hs).2⟩

/-- Only a raw load creates a receipt, including when the physical lookup fails. -/
theorem execute_receipt {memory : Memory} {i : Instruction} {s : State}
    {receipt : Receipt} (h : (execute memory i s).2 = some receipt) :
    ∃ dst addrReg, i = .load dst addrReg ∧
      receipt.address = s.regs addrReg ∧ receipt.reply = memory[receipt.address]? := by
  cases i <;> simp [execute] at h
  case load dst addrReg =>
    cases h
    exact ⟨dst, addrReg, rfl, rfl, rfl⟩

/-- The same occurrence supplies prefix, instruction, operands and numeric backing. -/
theorem run_read_at {memory : Memory} {program : Program} {fuel : Nat}
    {s : State} {k : Nat} {t : Transition} {receipt : Receipt}
    (h : (run memory program fuel s).transitions[k]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run memory program k s).final ∧
      t.before.status = .running ∧
      program[t.before.pc]? = some t.instruction ∧
      execute memory t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧
        receipt.reply = memory[receipt.address]? := by
  obtain ⟨hb, hs, hf, he⟩ := run_transition_spec h
  exact ⟨hb, hs, hf, he, execute_receipt (by rw [he]; exact hr)⟩

private theorem execute_eq_of_agree (memory memory' : Memory) (i : Instruction)
    (s : State)
    (h : ∀ receipt, (execute memory i s).2 = some receipt →
      memory'[receipt.address]? = memory[receipt.address]?) :
    execute memory' i s = execute memory i s := by
  cases i <;> try rfl
  case load dst address =>
      have ha := h ⟨s.regs address, memory[s.regs address]?⟩ rfl
      simpa only [execute] using
        congrArg (fun reply : Option Nat =>
          ((match reply with
            | some value => s.writeNext dst value
            | none => { s with status := .fault }),
            some (Receipt.mk (s.regs address) reply))) ha

private theorem step_none_memory {memory : Memory} (memory' : Memory)
    {program : Program} {s : State} (h : step memory program s = none) :
    step memory' program s = none := by
  cases hs : s.status <;> simp_all [step]
  cases hf : program[s.pc]? <;> simp_all

theorem step_eq_of_agree {memory : Memory} (memory' : Memory)
    {program : Program} {s : State} {t : Transition}
    (hs : step memory program s = some t)
    (h : ∀ receipt, t.receipt = some receipt →
      memory'[receipt.address]? = memory[receipt.address]?) :
    step memory' program s = some t := by
  obtain ⟨hb, hr, hf, he⟩ := step_spec hs
  have hx : execute memory' t.instruction s = (t.after, t.receipt) := by
    rw [execute_eq_of_agree memory memory' t.instruction s, he]
    intro receipt hreceipt
    apply h receipt
    simpa [he] using hreceipt
  simp only [step, hr, hf, hx]
  cases t
  simp_all

/-- Agreement on the first execution's attempted reads determines the whole run.
The hypothesis includes `none` replies, so adding a cell at a failed address
cannot silently satisfy it. The second execution need not supply a footprint. -/
theorem run_eq_of_agree (memory memory' : Memory) (program : Program) (fuel : Nat)
    (s : State)
    (h : ∀ receipt ∈ (run memory program fuel s).reads,
      memory'[receipt.address]? = memory[receipt.address]?) :
    run memory' program fuel s = run memory program fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : step memory program s with
      | none => simp [run, hs, step_none_memory memory' hs]
      | some t =>
          have hs' : step memory' program s = some t := by
            apply step_eq_of_agree memory' hs
            intro receipt hr
            apply h receipt
            simp [run, hs, Run.reads, hr]
          have ht : ∀ receipt ∈ (run memory program fuel t.after).reads,
              memory'[receipt.address]? = memory[receipt.address]? := by
            intro receipt hr
            apply h receipt
            simp only [run, hs, Run.reads, List.filterMap_cons]
            cases t.receipt <;> simp_all [Run.reads]
          simp [run, hs, hs', ih t.after ht]

/-- Projection consumer pins result, step count, categories and read receipts. -/
theorem run_observations_eq_of_agree (memory memory' : Memory) (program : Program)
    (fuel : Nat) (s : State)
    (h : ∀ receipt ∈ (run memory program fuel s).reads,
      memory'[receipt.address]? = memory[receipt.address]?) :
    (run memory' program fuel s).result = (run memory program fuel s).result ∧
      (run memory' program fuel s).steps = (run memory program fuel s).steps ∧
      (run memory' program fuel s).categories = (run memory program fuel s).categories ∧
      (run memory' program fuel s).reads = (run memory program fuel s).reads := by
  rw [run_eq_of_agree memory memory' program fuel s h]
  exact ⟨rfl, rfl, rfl, rfl⟩

namespace CalculusExamples

def initial : State := ⟨fun _ => 0, 0, .running⟩
def loadAndHalt : Program := [.load 1 0, .halt 1]
def repeatedLoadAndHalt : Program := [.load 1 0, .load 1 0, .halt 1]

/-- Expected scalar answers are literal data, independent of the evaluator. -/
theorem successfulLoad :
    (run [7] loadAndHalt 2 initial).result = some 7 ∧
      (run [7] loadAndHalt 2 initial).reads = [⟨0, some 7⟩] ∧
      (run [7] loadAndHalt 2 initial).steps = 2 ∧
      (run [7] loadAndHalt 2 initial).categories = [.memoryRead, .control] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem failedLoad :
    (run [] loadAndHalt 2 initial).result = none ∧
      (run [] loadAndHalt 2 initial).final.status = .fault ∧
      (run [] loadAndHalt 2 initial).reads = [⟨0, none⟩] ∧
      (run [] loadAndHalt 2 initial).steps = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A failed attempt retains the same positional producer evidence as a success. -/
theorem failedLoad_positional :
    ∃ t : Transition,
      (run [] loadAndHalt 2 initial).transitions[0]? = some t ∧
      t.receipt = some ⟨0, none⟩ ∧
      t.before = (run [] loadAndHalt 0 initial).final ∧
      t.before.status = .running ∧
      loadAndHalt[t.before.pc]? = some t.instruction ∧
      execute [] t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        0 = t.before.regs addrReg ∧ (none : Option Nat) = ([] : Memory)[0]? := by
  let t : Transition := ⟨initial, .load 1 0, { initial with status := .fault },
    some ⟨0, none⟩⟩
  have ht : (run [] loadAndHalt 2 initial).transitions[0]? = some t := rfl
  exact ⟨t, ht, rfl, run_read_at ht rfl⟩

theorem repeatedLoads :
    (run [7] repeatedLoadAndHalt 3 initial).result = some 7 ∧
      (run [7] repeatedLoadAndHalt 3 initial).reads = [⟨0, some 7⟩, ⟨0, some 7⟩] :=
  ⟨rfl, rfl⟩

/-- Equal event values are produced at two different positions and pre-states. -/
theorem repeatedLoad_positions :
    ∃ first second : Transition,
      (run [7] repeatedLoadAndHalt 3 initial).transitions[0]? = some first ∧
      (run [7] repeatedLoadAndHalt 3 initial).transitions[1]? = some second ∧
      first.receipt = some ⟨0, some 7⟩ ∧ second.receipt = some ⟨0, some 7⟩ ∧
      first.before = (run [7] repeatedLoadAndHalt 0 initial).final ∧
      second.before = (run [7] repeatedLoadAndHalt 1 initial).final ∧
      first.before.pc = 0 ∧ second.before.pc = 1 := by
  let first : Transition := ⟨initial, .load 1 0, initial.writeNext 1 7,
    some ⟨0, some 7⟩⟩
  let second : Transition := ⟨initial.writeNext 1 7, .load 1 0,
    (initial.writeNext 1 7).writeNext 1 7, some ⟨0, some 7⟩⟩
  have hf : (run [7] repeatedLoadAndHalt 3 initial).transitions[0]? = some first := rfl
  have hs : (run [7] repeatedLoadAndHalt 3 initial).transitions[1]? = some second := rfl
  exact ⟨first, second, hf, hs, rfl, rfl,
    (run_read_at hf rfl).1, (run_read_at hs rfl).1, rfl, rfl⟩

theorem suppliedMemoryAgreement :
    run [7, 99] loadAndHalt 2 initial = run [7] loadAndHalt 2 initial := by
  apply run_eq_of_agree
  intro receipt hr
  have he : receipt = ⟨0, some 7⟩ := by simpa [successfulLoad.2.1] using hr
  subst receipt
  rfl

/-- A changed loaded cell changes the answer projection itself. -/
theorem loadedValue_changes_result :
    (run [7] loadAndHalt 2 initial).result ≠
      (run [8] loadAndHalt 2 initial).result := by decide

/-- Adding a cell at the actual failed-read address violates the same agreement
hypothesis used by `run_eq_of_agree`, rather than a stronger proxy predicate. -/
theorem failedAddress_not_agreement :
    ¬ (∀ receipt ∈ (run [] loadAndHalt 2 initial).reads,
      ([7] : Memory)[receipt.address]? = ([] : Memory)[receipt.address]?) := by
  intro h
  have bad := h ⟨0, none⟩ (by rw [failedLoad.2.2.1]; simp)
  contradiction

/-- Composition, halted extension, and the partition are directly consumed. -/
theorem composedLoadAndHalt (extra : Nat) :
    (run [7] loadAndHalt (2 + extra) initial).result = some 7 ∧
      (run [7] loadAndHalt (2 + extra) initial).steps =
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .memoryRead +
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .registerWrite +
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .arithmetic +
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .comparison +
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .branch +
        (run [7] loadAndHalt (2 + extra) initial).categoryCount .control := by
  have load := RunsTo.instruction (memory := [7]) (program := loadAndHalt)
    (s := initial) (i := .load 1 0) rfl rfl
  have halt := RunsTo.instruction (memory := [7]) (program := loadAndHalt)
    (s := initial.writeNext 1 7) (i := .halt 1) rfl rfl
  have both := load.trans halt
  have extended := both.fuel_extension (value := 7) rfl extra
  constructor
  · exact congrArg Run.result extended
  · exact Run.steps_partition _

end CalculusExamples

end RMQ.SuccinctFinal.PackedWordRAM

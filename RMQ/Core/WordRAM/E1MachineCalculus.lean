import RMQ.Core.WordRAM.E1Machine

/-!
# E1 amended machine: program-composition calculus

Compositional reasoning layer over `RMQ.WordRAM.E1Machine` for the
concrete whole-query program proofs (frozen matrix REQ-E1-03/04/05/06):

* `HostedAt program base code` - the instruction block `code` sits at
  absolute address `base` inside `program`.  Generators emit blocks at
  explicit bases (branch targets are absolute, resolved by the
  generator), and per-block lemmas are stated against any hosting
  program, so blocks compose by concatenation.
* `RunsTo store program s s' reads cats` - exact-fuel big-step
  execution: running with fuel `cats.length` consumes it exactly,
  reaching `s'` with receipt log `reads` and category log `cats`.
  Reflexivity, transitivity (via `run_add`), one lemma per instruction
  constructor, and fuel-insensitivity after halt make whole-program
  correctness a chain of mechanical steps.

Everything here is machine-generic; nothing mentions the RMQ route.
-/

namespace RMQ
namespace WordRAM
namespace E1Machine

/-! ## Hosted code blocks -/

/-- `code` is hosted at absolute base `base` in `program`: fetching
`base + i` yields instruction `i` of the block. -/
def HostedAt (program : Program) (base : Nat) (code : List Instr) : Prop :=
  ∀ i, i < code.length → program[base + i]? = code[i]?

theorem hostedAt_nil (program : Program) (base : Nat) :
    HostedAt program base [] := by
  intro i hi
  cases hi

/-- A program hosts itself at base `0`. -/
theorem hostedAt_self (program : Program) : HostedAt program 0 program := by
  intro i hi
  simp

theorem HostedAt.head {program : Program} {base : Nat} {instr : Instr}
    {rest : List Instr} (h : HostedAt program base (instr :: rest)) :
    program[base]? = some instr := by
  have := h 0 (Nat.succ_le_succ (Nat.zero_le _))
  simpa using this

theorem HostedAt.tail {program : Program} {base : Nat} {instr : Instr}
    {rest : List Instr} (h : HostedAt program base (instr :: rest)) :
    HostedAt program (base + 1) rest := by
  intro i hi
  have := h (i + 1) (Nat.succ_le_succ hi)
  have harith : base + 1 + i = base + (i + 1) := by omega
  rw [harith]
  simpa using this

theorem HostedAt.append_left {program : Program} {base : Nat}
    {code₁ code₂ : List Instr}
    (h : HostedAt program base (code₁ ++ code₂)) :
    HostedAt program base code₁ := by
  intro i hi
  have hlt : i < (code₁ ++ code₂).length := by
    simp [List.length_append]
    omega
  have := h i hlt
  rwa [List.getElem?_append_left hi] at this

theorem HostedAt.append_right {program : Program} {base : Nat}
    {code₁ code₂ : List Instr}
    (h : HostedAt program base (code₁ ++ code₂)) :
    HostedAt program (base + code₁.length) code₂ := by
  intro i hi
  have hlt : code₁.length + i < (code₁ ++ code₂).length := by
    simp [List.length_append]
    omega
  have harith : base + code₁.length + i = base + (code₁.length + i) := by
    omega
  rw [harith]
  have := h (code₁.length + i) hlt
  rw [this]
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

/-! ## Exact-fuel big-step execution -/

/--
Exact-fuel big-step relation: from `s`, running with fuel `cats.length`
consumes every unit (one instruction per category tick), reaching `s'`
with receipt log `reads`.  Because the fuel equals the step count, two
`RunsTo` segments compose exactly.
-/
def RunsTo (store : ReadStore) (program : Program) (s s' : State)
    (reads : List TraceEvent) (cats : List Category) : Prop :=
  run store program cats.length s = ⟨s', reads, cats, cats.length⟩

theorem RunsTo.refl (store : ReadStore) (program : Program) (s : State) :
    RunsTo store program s s [] [] := rfl

theorem RunsTo.trans {store : ReadStore} {program : Program}
    {s₁ s₂ s₃ : State} {r₁ r₂ : List TraceEvent}
    {c₁ c₂ : List Category}
    (h₁ : RunsTo store program s₁ s₂ r₁ c₁)
    (h₂ : RunsTo store program s₂ s₃ r₂ c₂) :
    RunsTo store program s₁ s₃ (r₁ ++ r₂) (c₁ ++ c₂) := by
  unfold RunsTo at h₁ h₂ ⊢
  have hadd := run_add store program c₁.length c₂.length s₁
  rw [h₁] at hadd
  simp only at hadd
  rw [h₂] at hadd
  simp only [List.length_append]
  simpa using hadd

/-- One executed instruction, in relational form. -/
theorem RunsTo.step {store : ReadStore} {program : Program} {s s' : State}
    {instr : Instr} {cat : Category} {event? : Option TraceEvent}
    (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some instr)
    (hexec : execInstr store instr s = (s', cat, event?)) :
    RunsTo store program s s' event?.toList [cat] := by
  unfold RunsTo
  have hstep : E1Machine.step store program s = some (s', cat, event?) := by
    unfold E1Machine.step
    rw [if_neg (by simp [hhalt]), hfetch]
    simp [hexec]
  show run store program (0 + 1) s = _
  rw [run_succ, hstep]
  simp

/-! ### Per-constructor step rules

Each rule needs only "not halted" and the fetch fact; the successor
state, receipt, and category are computed by the semantics.  These are
the mechanical bricks for the concrete program proofs.
-/

theorem RunsTo.readMem {store : ReadStore} {program : Program} {s : State}
    {dst segment addrReg : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.readMem dst segment addrReg)) :
    RunsTo store program s
      ⟨s.regs.write dst
          (decodeRead (store.readWord? segment (s.regs addrReg))),
        s.pc + 1, false⟩
      [.readWord segment (s.regs addrReg)
          (store.readWord? segment (s.regs addrReg))]
      [.memoryRead] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.const {store : ReadStore} {program : Program} {s : State}
    {dst value : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.const dst value)) :
    RunsTo store program s
      ⟨s.regs.write dst value, s.pc + 1, false⟩ [] [.registerWrite] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.move {store : ReadStore} {program : Program} {s : State}
    {dst src : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.move dst src)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src), s.pc + 1, false⟩ []
      [.registerWrite] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.add {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.add dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src₁ + s.regs src₂), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.sub {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.sub dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src₁ - s.regs src₂), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.mulConst {store : ReadStore} {program : Program} {s : State}
    {dst src k : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.mulConst dst src k)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src * k), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.divConst {store : ReadStore} {program : Program} {s : State}
    {dst src k : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.divConst dst src k)) :
    RunsTo store program s
      ⟨s.regs.write dst (s.regs src / k), s.pc + 1, false⟩ []
      [.arithmetic] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natLt {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natLt dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ < s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natLe {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natLe dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ ≤ s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.natEq {store : ReadStore} {program : Program} {s : State}
    {dst src₁ src₂ : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.natEq dst src₁ src₂)) :
    RunsTo store program s
      ⟨s.regs.write dst (if s.regs src₁ = s.regs src₂ then 1 else 0),
        s.pc + 1, false⟩ [] [.comparison] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.brNZ {store : ReadStore} {program : Program} {s : State}
    {cond target : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.brNZ cond target)) :
    RunsTo store program s
      ⟨s.regs, if s.regs cond = 0 then s.pc + 1 else target, false⟩ []
      [.branch] :=
  RunsTo.step hhalt hfetch rfl

theorem RunsTo.halt {store : ReadStore} {program : Program} {s : State}
    (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some .halt) :
    RunsTo store program s ⟨s.regs, s.pc, true⟩ [] [.control] :=
  RunsTo.step hhalt hfetch rfl

/-! ## Fuel insensitivity after halt -/

/-- Once a `RunsTo` segment ends halted, any surplus fuel changes
nothing: the run packet is determined.  This makes "the machine outcome"
well defined by any fuel budget at least the step count. -/
theorem RunsTo.run_fuel_ge {store : ReadStore} {program : Program}
    {s s' : State} {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats)
    (hhalted : s'.halted = true) (extra : Nat) :
    run store program (cats.length + extra) s = ⟨s', reads, cats,
      cats.length⟩ := by
  have hadd := run_add store program cats.length extra s
  unfold RunsTo at h
  rw [h] at hadd
  simp only at hadd
  have hstuck : E1Machine.step store program s' = none := by
    unfold E1Machine.step
    rw [if_pos hhalted]
  rw [run_stuck store program hstuck extra] at hadd
  simpa using hadd

/-- Restated with an arbitrary sufficient fuel budget. -/
theorem RunsTo.run_of_le_fuel {store : ReadStore} {program : Program}
    {s s' : State} {reads : List TraceEvent} {cats : List Category}
    (h : RunsTo store program s s' reads cats)
    (hhalted : s'.halted = true) {fuel : Nat} (hfuel : cats.length ≤ fuel) :
    run store program fuel s = ⟨s', reads, cats, cats.length⟩ := by
  obtain ⟨extra, rfl⟩ : ∃ extra, fuel = cats.length + extra :=
    ⟨fuel - cats.length, by omega⟩
  exact h.run_fuel_ge hhalted extra

end E1Machine
end WordRAM
end RMQ

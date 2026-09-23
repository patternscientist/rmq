import RMQ.Core.WordRAM.Packed.Scratch

/-!
# Finite indexed storage for the packed primitive executor

Program, memory, and registers are arrays. Cells are still natural-number
representatives here; this module does not establish a finite limb encoding,
machine-word safety, or a native hardware cost. The simulation preserves the
entire primitive run, including failed loads and positional transitions.
-/

namespace RMQ.SuccinctFinal.PackedNative

open PackedWordRAM

structure FiniteState where
  regs : Array Nat
  pc : Nat
  status : Status
deriving Repr

def FiniteState.read (s : FiniteState) (r : Nat) : Nat := s.regs[r]?.getD 0

def FiniteState.decode (s : FiniteState) : State :=
  ⟨s.read, s.pc, s.status⟩

@[simp] theorem FiniteState.decode_regs (s : FiniteState) : s.decode.regs = s.read := rfl
@[simp] theorem FiniteState.decode_pc (s : FiniteState) : s.decode.pc = s.pc := rfl
@[simp] theorem FiniteState.decode_status (s : FiniteState) :
    s.decode.status = s.status := rfl

/-- Allocate exactly `capacity` indexed registers from a reference state. -/
def FiniteState.ofState (capacity : Nat) (s : State) : FiniteState :=
  ⟨Array.ofFn (fun r : Fin capacity => s.regs r.val), s.pc, s.status⟩

@[simp] theorem FiniteState.ofState_size (capacity : Nat) (s : State) :
    (FiniteState.ofState capacity s).regs.size = capacity := by
  simp [FiniteState.ofState]

/-- Finite initialization represents exactly a reference state with a zero
tail. The hypothesis concerns all omitted registers, not just source operands. -/
theorem FiniteState.decode_ofState (capacity : Nat) (s : State)
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    (FiniteState.ofState capacity s).decode = s := by
  cases s with
  | mk regs pc status =>
      unfold FiniteState.ofState FiniteState.decode
      congr 1
      funext r
      by_cases hr : r < capacity
      · simp [FiniteState.read, hr]
      · have hz : regs r = 0 := hzero r (by omega)
        simp [FiniteState.read, hr, hz]

def FiniteState.writeNext (s : FiniteState) (dst value : Nat) : FiniteState :=
  ⟨s.regs.setIfInBounds dst value, s.pc + 1, .running⟩

@[simp] theorem FiniteState.writeNext_size (s : FiniteState) (dst value : Nat) :
    (s.writeNext dst value).regs.size = s.regs.size := by
  simp [FiniteState.writeNext]

theorem FiniteState.writeNext_decode (s : FiniteState) (dst value : Nat)
    (h : dst < s.regs.size) :
    (s.writeNext dst value).decode = s.decode.writeNext dst value := by
  unfold FiniteState.decode FiniteState.writeNext State.writeNext
  congr 1
  funext r
  by_cases hr : r = dst
  · subst r
    simp [FiniteState.read, Registers.write, h]
  · simp [FiniteState.read, Registers.write, hr, Ne.symm hr]

/-- Out-of-bank source registers have the reference machine's zero value. -/
theorem FiniteState.read_above (s : FiniteState) (r : Nat) (h : s.regs.size ≤ r) :
    s.read r = 0 := by
  simp [FiniteState.read, Array.getElem?_eq_none (by omega)]

/-- One actual indexed-container instruction. Destination capacity is the
simulation guard; array writes outside capacity otherwise leave the bank alone.
Missing memory produces the same fault and failed receipt as the reference. -/
def executeFinite (memory : Array Nat) (i : Instruction) (s : FiniteState) :
    FiniteState × Option Receipt :=
  match i with
  | .load dst address =>
      let a := s.read address
      let reply := memory[a]?
      let next := match reply with
        | some value => s.writeNext dst value
        | none => { s with status := .fault }
      (next, some ⟨a, reply⟩)
  | .constant dst value => (s.writeNext dst value, none)
  | .move dst src => (s.writeNext dst (s.read src), none)
  | .arithmetic op dst lhs rhs =>
      (s.writeNext dst (op.eval (s.read lhs) (s.read rhs)), none)
  | .comparison op dst lhs rhs =>
      (s.writeNext dst (op.eval (s.read lhs) (s.read rhs)), none)
  | .jump target => ({ s with pc := target }, none)
  | .jumpRegister src => ({ s with pc := s.read src }, none)
  | .branchZero condition target =>
      ({ s with pc := if s.read condition = 0 then target else s.pc + 1 }, none)
  | .halt src => ({ s with status := .halted (s.read src) }, none)

/-- Every constructor preserves the actual register allocation. -/
theorem executeFinite_size (memory : Array Nat) (i : Instruction) (s : FiniteState) :
    (executeFinite memory i s).1.regs.size = s.regs.size := by
  cases i <;> simp [executeFinite]
  split <;> simp_all

/-- Constructor-exhaustive simulation, including all arithmetic operations:
both the complete state and the optional load receipt agree. -/
theorem executeFinite_decode (memory : Array Nat) (i : Instruction) (s : FiniteState)
    (hwrites : i.WritesOnly (fun r => r < s.regs.size)) :
    ((executeFinite memory i s).1.decode, (executeFinite memory i s).2) =
      execute memory.toList i s.decode := by
  cases i with
  | load dst address =>
      simp only [executeFinite, execute, FiniteState.decode_regs,
        Array.getElem?_toList]
      cases hreply : memory[s.read address]? with
      | none => rfl
      | some value =>
          exact congrArg (fun next : State =>
            (next, some (Receipt.mk (s.read address) (some value))))
              (s.writeNext_decode dst value hwrites)
  | constant dst value =>
      exact congrArg (fun next : State => (next, (none : Option Receipt)))
        (s.writeNext_decode dst value hwrites)
  | move dst src =>
      exact congrArg (fun next : State => (next, (none : Option Receipt)))
        (s.writeNext_decode dst (s.read src) hwrites)
  | arithmetic op dst lhs rhs | comparison op dst lhs rhs =>
      exact congrArg (fun next : State => (next, (none : Option Receipt)))
        (s.writeNext_decode dst (op.eval (s.read lhs) (s.read rhs)) hwrites)
  | jump target => rfl
  | jumpRegister src => rfl
  | branchZero condition target => rfl
  | halt src => rfl

structure FiniteTransition where
  before : FiniteState
  instruction : Instruction
  after : FiniteState
  receipt : Option Receipt
deriving Repr

def FiniteTransition.decode (t : FiniteTransition) : Transition :=
  ⟨t.before.decode, t.instruction, t.after.decode, t.receipt⟩

def stepFinite (memory : Array Nat) (program : Array Instruction) (s : FiniteState) :
    Option FiniteTransition :=
  match s.status with
  | .running =>
      match program[s.pc]? with
      | none => none
      | some i =>
          let result := executeFinite memory i s
          some ⟨s, i, result.1, result.2⟩
  | _ => none

theorem stepFinite_size (memory : Array Nat) (program : Array Instruction)
    (s : FiniteState) (t : FiniteTransition) (ht : stepFinite memory program s = some t) :
    t.after.regs.size = s.regs.size := by
  cases hs : s.status with
  | halted value => simp [stepFinite, hs] at ht
  | fault => simp [stepFinite, hs] at ht
  | running =>
      cases hi : program[s.pc]? with
      | none => simp [stepFinite, hs, hi] at ht
      | some i =>
          simp only [stepFinite, hs, hi, Option.some.injEq] at ht
          subst t
          exact executeFinite_size memory i s

theorem stepFinite_decode (memory : Array Nat) (program : Array Instruction)
    (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    (stepFinite memory program s).map FiniteTransition.decode =
      step memory.toList program.toList s.decode := by
  cases hs : s.status with
  | halted value => simp [stepFinite, step, FiniteState.decode, hs]
  | fault => simp [stepFinite, step, FiniteState.decode, hs]
  | running =>
      cases hi : program[s.pc]? with
      | none => simp [stepFinite, step, FiniteState.decode, hs, hi]
      | some i =>
          have himem : i ∈ program.toList :=
            List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hi)
          have hex := executeFinite_decode memory i s (hwrites i himem)
          simp only [stepFinite, step, FiniteState.decode_status, FiniteState.decode_pc,
            hs, Array.getElem?_toList, hi, Option.map_some]
          exact congrArg (fun p : State × Option Receipt =>
            some (Transition.mk s.decode i p.1 p.2)) hex

structure FiniteRun where
  final : FiniteState
  transitions : List FiniteTransition
deriving Repr

def FiniteRun.decode (r : FiniteRun) : Run :=
  ⟨r.final.decode, r.transitions.map FiniteTransition.decode⟩

/-- The observational executor retains transitions. A production executor can
erase these observations by a separately proved projection. -/
def runFinite (memory : Array Nat) (program : Array Instruction) :
    Nat → FiniteState → FiniteRun
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match stepFinite memory program s with
      | none => ⟨s, []⟩
      | some t =>
          let rest := runFinite memory program fuel t.after
          ⟨rest.final, t :: rest.transitions⟩

/-- Full fuel simulation as equality of complete primitive runs. No hypothesis
on memory contents, load success, starting status, source register identifiers,
or fuel adequacy is needed. Only every destination must fit the finite bank. -/
theorem runFinite_decode (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    (runFinite memory program fuel s).decode =
      run memory.toList program.toList fuel s.decode := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      simp only [runFinite, run, ← stepFinite_decode memory program s hwrites]
      cases ht : stepFinite memory program s with
      | none => rfl
      | some t =>
          have hsize := stepFinite_size memory program s t ht
          have hwrites' : ∀ i ∈ program.toList,
              i.WritesOnly (fun r => r < t.after.regs.size) := by
            simpa only [hsize] using hwrites
          have heq := ih t.after hwrites'
          have hf := congrArg Run.final heq
          have ht' := congrArg Run.transitions heq
          simp only [Option.map_some, FiniteTransition.decode, FiniteRun.decode,
            List.map_cons] at *
          rw [hf, ht']

/-- Register allocation remains fixed for every fuel prefix. -/
theorem runFinite_size (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState) :
    (runFinite memory program fuel s).final.regs.size = s.regs.size := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases ht : stepFinite memory program s with
      | none => simp [runFinite, ht]
      | some t =>
          simpa only [runFinite, ht] using
            (ih t.after).trans (stepFinite_size memory program s t ht)

/-- Direct consumer for a list-based PQ1 allocation/program and any initial
reference state whose finite bank is exact. This preserves the same memory and
program, with no substitute store or instruction stream. -/
theorem runFinite_ofState (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    (runFinite memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)).decode = run memory program fuel s := by
  simpa only [List.toList_toArray, FiniteState.decode_ofState capacity s hzero] using
    runFinite_decode memory.toArray program.toArray fuel (FiniteState.ofState capacity s)
      (by simpa only [List.toList_toArray, FiniteState.ofState_size] using hwrites)

end RMQ.SuccinctFinal.PackedNative

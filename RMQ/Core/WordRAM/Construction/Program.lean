import RMQ.Core.WordRAM.Construction.Model

/-! # Fetch-and-step interpretation of a fixed construction program

The interpreter fetches one `BInstr` from the fixed program at the current
program counter and applies `checkedStep`, so a halted or faulted state never
executes again. Every recorded transition keeps its actual pre-state, the
fetched instruction and its post-state. Work is the number of transitions;
category counts, write events, reservations and key reads are projections of
the same transition list, never separately supplied data. This module operates
on `List BInstr` literally and imports only the frozen primitive model.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- One executed primitive transition with positional provenance. -/
structure Transition where
  before : State
  instruction : BInstr
  after : State

def fetch (program : List BInstr) (s : State) : Option BInstr := program[s.pc]?

/-- A transition exists only for a running state with an instruction at its
program counter. Fetch happens before the terminal-state guard is consulted,
and both are required. -/
def stepProgram (program : List BInstr) (s : State) : Option Transition :=
  match fetch program s with
  | none => none
  | some i =>
      match checkedStep i s with
      | none => none
      | some s' => some ⟨s, i, s'⟩

structure Run where
  final : State
  transitions : List Transition

/-- Fuel-indexed execution. Fuel is a termination instrument only; the actual
work is `Run.steps`, the number of transitions actually taken. -/
def run (program : List BInstr) : Nat → State → Run
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match stepProgram program s with
      | none => ⟨s, []⟩
      | some t =>
          let rest := run program fuel t.after
          ⟨rest.final, t :: rest.transitions⟩

def Run.steps (r : Run) : Nat := r.transitions.length

def Run.categories (r : Run) : List Category :=
  r.transitions.map (fun t => t.instruction.primitive.category)

def Run.categoryCount (r : Run) (c : Category) : Nat := r.categories.count c

/-- A successful store transition's address and value, both read from its own
pre-state. A store whose address is outside the extent faults and writes
nothing, so it is not a write event. -/
def Transition.write? (t : Transition) : Option (Nat × Nat) :=
  match t.instruction.primitive with
  | .store address value =>
      if t.before.regs address < t.before.extent then
        some (t.before.regs address, t.before.regs value)
      else none
  | _ => none

/-- A reservation returns the pre-state extent as the fresh address. -/
def Transition.reserve? (t : Transition) : Option Nat :=
  match t.instruction.primitive with
  | .reserve _ => some t.before.extent
  | _ => none

/-- The numeric address a load transition reads, from its own pre-state. -/
def Transition.load? (t : Transition) : Option Nat :=
  match t.instruction.primitive with
  | .load _ address => some (t.before.regs address)
  | _ => none

/-- The key-bank address a key read transition consults. -/
def Transition.keyRead? (t : Transition) : Option Nat :=
  match t.instruction.primitive with
  | .loadKey _ address => some (t.before.regs address)
  | _ => none

def Run.writes (r : Run) : List (Nat × Nat) := r.transitions.filterMap Transition.write?
def Run.reserves (r : Run) : List Nat := r.transitions.filterMap Transition.reserve?
def Run.loads (r : Run) : List Nat := r.transitions.filterMap Transition.load?
def Run.keyReads (r : Run) : List Nat := r.transitions.filterMap Transition.keyRead?

def Run.result (r : Run) : Option Nat :=
  match r.final.status with
  | .halted value => some value
  | _ => none

/-- Positional projection of a contiguous address range of a state's memory.
Absent cells read as zero; exactness theorems must separately show the cells
are present. This is the only extraction the builder may use for its output. -/
def emitted (s : State) (base len : Nat) : List Nat :=
  (List.range len).map fun i => (s.memory (base + i)).getD 0

/-- The numeric register a primitive writes, if any. Stores write memory only,
key reads write a key register only, and control instructions write nothing. -/
def Prim.destination? : Prim → Option Operand
  | .load dst _ => some dst
  | .constant dst _ => some dst
  | .move dst _ => some dst
  | .arithmetic _ dst _ _ => some dst
  | .comparison _ dst _ _ => some dst
  | .jump _ => none
  | .jumpRegister _ => none
  | .branchZero _ _ => none
  | .halt _ => none
  | .store _ _ => none
  | .reserve dst => some dst
  | .loadKey _ _ => none
  | .compareKey dst _ _ => some dst

/-- Register frame discipline of one instruction. -/
def WritesOnly (allowed : Nat → Prop) (i : BInstr) : Prop :=
  ∀ d, i.primitive.destination? = some d → allowed d.val

instance WritesOnly.decidable (allowed : Nat → Prop) [DecidablePred allowed] (i : BInstr) :
    Decidable (WritesOnly allowed i) :=
  match h : i.primitive.destination? with
  | none => isTrue (fun d hd => by rw [h] at hd; cases hd)
  | some d =>
      if hd : allowed d.val then
        isTrue (fun e he => by rw [h] at he; cases he; exact hd)
      else
        isFalse (fun hall => hd (hall d h))

theorem execPrim_frame (p : Prim) (s : State) (allowed : Nat → Prop)
    (hwrites : ∀ d, p.destination? = some d → allowed d.val) (r : Nat) (hout : ¬ allowed r) :
    (execPrim p s).regs r = s.regs r := by
  have hne : ∀ d : Operand, p.destination? = some d → r ≠ d.val := by
    intro d hd heq
    exact hout (heq ▸ hwrites d hd)
  cases p with
  | load dst address =>
      have h := hne dst rfl
      simp only [execPrim]
      split
      · split
        · simp [State.writeNext, State.next, put, h]
        · rfl
      · rfl
  | constant dst value => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]
  | move dst src => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]
  | arithmetic op dst lhs rhs => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]
  | comparison op dst lhs rhs => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]
  | jump target => rfl
  | jumpRegister src => rfl
  | branchZero condition target => rfl
  | halt src => rfl
  | store address value =>
      simp only [execPrim]
      split <;> rfl
  | reserve dst => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]
  | loadKey dst address =>
      simp only [execPrim]
      split <;> rfl
  | compareKey dst lhs rhs => simp [execPrim, State.writeNext, State.next, put, hne dst rfl]

end RMQ.SuccinctFinal.PackedConstruction

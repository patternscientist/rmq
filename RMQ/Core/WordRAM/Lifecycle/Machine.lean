import RMQ.Core.WordRAM.Construction.Compiler

/-! # Scalar lifecycle machine

The old numeric machine is an exact projection. The two additional extents
account for separately owned comparison resources; they are not bounds on Int
values. Every release retires one tail cell. External request admission is a
separate charged protocol on a halted state, with one scalar update per event.
No request tape or observation history is stored in the machine state.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open PackedConstruction (Operand Prim execPrim put)

structure State where
  core : PackedConstruction.State
  keyExtent : Nat
  keyRegExtent : Nat

inductive Instruction where
  | old (primitive : Prim)
  | releaseCell
  | releaseKey
  | releaseKeyRegister
deriving DecidableEq, Repr

def execute : Instruction → State → State
  | .old p, s => { s with core := execPrim p s.core }
  | .releaseCell, s =>
      if s.core.extent = 0 then { s with core := { s.core with status := .fault } }
      else { s with core := { s.core.next with extent := s.core.extent - 1, memory := put s.core.memory (s.core.extent - 1) none } }
  | .releaseKey, s =>
      if s.keyExtent = 0 then { s with core := { s.core with status := .fault } }
      else { s with keyExtent := s.keyExtent - 1, core := { s.core.next with keys := put s.core.keys (s.keyExtent - 1) none } }
  | .releaseKeyRegister, s =>
      if s.keyRegExtent = 0 then { s with core := { s.core with status := .fault } }
      else { s with keyRegExtent := s.keyRegExtent - 1, core := { s.core.next with keyRegs := put s.core.keyRegs (s.keyRegExtent - 1) 0 } }

@[simp] theorem execute_old (p : Prim) (s : State) :
    execute (.old p) s = { s with core := execPrim p s.core } := rfl

theorem releaseCell_zero (s : State) (h : s.core.extent = 0) :
    execute .releaseCell s = { s with core := { s.core with status := .fault } } := by
  simp [execute, h]

theorem releaseKey_zero (s : State) (h : s.keyExtent = 0) :
    execute .releaseKey s = { s with core := { s.core with status := .fault } } := by
  simp [execute, h]

theorem releaseKeyRegister_zero (s : State) (h : s.keyRegExtent = 0) :
    execute .releaseKeyRegister s = { s with core := { s.core with status := .fault } } := by
  simp [execute, h]

def requestLeftRegister : Nat := 300
def requestRightRegister : Nat := 301

/-- The environment supplies only the current two request words. Entry and
activation are separately charged scalar control changes. -/
inductive Boundary where
  | left (value : Nat)
  | right (value : Nat)
  | entry (target : Operand)
  | activate
deriving DecidableEq, Repr

def executeBoundary : Boundary → State → State
  | .left v, s => { s with core := { s.core with regs := put s.core.regs requestLeftRegister v } }
  | .right v, s => { s with core := { s.core with regs := put s.core.regs requestRightRegister v } }
  | .entry target, s => { s with core := { s.core with pc := target } }
  | .activate, s => { s with core := { s.core with status := .running } }

inductive Action where
  | instruction (i : Instruction)
  | boundary (b : Boundary)
deriving DecidableEq, Repr

inductive Category where
  | old (category : PackedConstruction.Category)
  | numericRelease | keyRelease | keyRegisterRelease | requestAdmission | controlEntry
deriving DecidableEq, Repr

def Action.category : Action → Category
  | .instruction (.old p) => .old p.category
  | .instruction .releaseCell => .numericRelease
  | .instruction .releaseKey => .keyRelease
  | .instruction .releaseKeyRegister => .keyRegisterRelease
  | .boundary (.left _) | .boundary (.right _) => .requestAdmission
  | .boundary (.entry _) | .boundary .activate => .controlEntry

structure Transition where
  before : State
  action : Action
  after : State

def step (program : List Instruction) (s : State) : Option Transition :=
  if s.core.status = .running then
    (program[s.core.pc]?).map fun i => ⟨s, .instruction i, execute i s⟩
  else none

/-- Old instruction execution stays stopped. Only this named external boundary
can accept a new request after a query has halted. Faulted states do not re-enter. -/
def boundaryStep (b : Boundary) (s : State) : Option Transition :=
  match s.core.status with
  | .halted _ => some ⟨s, .boundary b, executeBoundary b s⟩
  | _ => none

structure Run where
  final : State
  transitions : List Transition

def run (program : List Instruction) : Nat → State → Run
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match step program s with
      | none => ⟨s, []⟩
      | some t => let rest := run program fuel t.after
                  ⟨rest.final, t :: rest.transitions⟩

def runBoundary : List Boundary → State → Run
  | [], s => ⟨s, []⟩
  | b :: bs, s =>
      match boundaryStep b s with
      | none => ⟨s, []⟩
      | some t => let rest := runBoundary bs t.after
                  ⟨rest.final, t :: rest.transitions⟩

def requestProtocol (entry : Operand) (left right : Nat) (s : State) : Run :=
  runBoundary [.left left, .right right, .entry entry, .activate] s

def Run.steps (r : Run) : Nat := r.transitions.length
def Run.categories (r : Run) : List Category := r.transitions.map (·.action.category)
def Run.categoryCount (r : Run) (c : Category) : Nat := r.categories.count c

/-- Attempted numeric reads include absent replies and preserve repetitions. -/
def Transition.read? (t : Transition) : Option (Nat × Option Nat) :=
  match t.action with
  | .instruction (.old (.load _ address)) =>
      let a := t.before.core.regs address
      some (a, if a < t.before.core.extent then t.before.core.memory a else none)
  | _ => none

def Transition.write? (t : Transition) : Option (Nat × Nat) :=
  match t.action with
  | .instruction (.old (.store address value)) =>
      if t.before.core.regs address < t.before.core.extent then
        some (t.before.core.regs address, t.before.core.regs value) else none
  | _ => none

def Run.reads (r : Run) : List (Nat × Option Nat) := r.transitions.filterMap Transition.read?
def Run.writes (r : Run) : List (Nat × Nat) := r.transitions.filterMap Transition.write?

/-- Logical ownership includes absence outside each separately counted bank. -/
def State.Closed (s : State) : Prop :=
  PackedConstruction.CleanTail s.core ∧
  (∀ a, s.keyExtent ≤ a → s.core.keys a = none) ∧
  (∀ r, s.keyRegExtent ≤ r → s.core.keyRegs r = 0)

def State.Fits (W : Nat) (s : State) : Prop :=
  s.core.Fits W ∧ s.keyExtent < 2 ^ W ∧ s.keyRegExtent < 2 ^ W

def Instruction.encoding : Instruction → List Nat
  | .old p => p.constants.map Fin.val
  | .releaseCell => [13]
  | .releaseKey => [14]
  | .releaseKeyRegister => [15]

def Instruction.Fits (W : Nat) (i : Instruction) : Prop :=
  ∀ word ∈ i.encoding, word < 2 ^ W

/-- Old safety is reused verbatim; new operations have scalar nonempty-bank
preconditions. External admission has its own represented-input boundary. -/
def Instruction.Safe (W len : Nat) (s : State) : Instruction → Prop
  | .old p => p.Safe W len s.core
  | .releaseCell => 13 < 2 ^ W ∧ 0 < s.core.extent
  | .releaseKey => 14 < 2 ^ W ∧ 0 < s.keyExtent
  | .releaseKeyRegister => 15 < 2 ^ W ∧ 0 < s.keyRegExtent

end RMQ.SuccinctFinal.PackedLifecycle

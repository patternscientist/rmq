import Std

/-!
# Physical register instruction semantics for the packed query

One instruction performs one scalar arithmetic, comparison, transfer, or raw
physical load operation. Memory and register values are natural representatives
of words; separate reachability theorems must establish the declared width for
every state and operand. This definition alone asserts no query adequacy or
word-width bound. Arithmetic subtraction is used only under non-underflow
invariants by the compiled program.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

abbrev Registers := Nat → Nat

def Registers.write (regs : Registers) (dst value : Nat) : Registers :=
  fun r => if r = dst then value else regs r

@[simp] theorem Registers.write_same (regs : Registers) (dst value : Nat) :
    regs.write dst value dst = value := by simp [Registers.write]

theorem Registers.write_other (regs : Registers) (dst value r : Nat)
    (h : r ≠ dst) : regs.write dst value r = regs r := by
  simp [Registers.write, h]

inductive Arithmetic where
  | add | sub | mul | div | mod | shl | shr | band | bor | bxor
deriving Repr, DecidableEq

def Arithmetic.eval : Arithmetic → Nat → Nat → Nat
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .mod, x, y => x % y
  | .shl, x, y => Nat.shiftLeft x y
  | .shr, x, y => Nat.shiftRight x y
  | .band, x, y => Nat.land x y
  | .bor, x, y => Nat.lor x y
  | .bxor, x, y => Nat.xor x y

inductive Comparison where
  | lt | le | eq
deriving Repr, DecidableEq

def Comparison.eval : Comparison → Nat → Nat → Nat
  | .lt, x, y => if x < y then 1 else 0
  | .le, x, y => if x ≤ y then 1 else 0
  | .eq, x, y => if x = y then 1 else 0

inductive Instruction where
  | load (dst address : Nat)
  | constant (dst value : Nat)
  | move (dst src : Nat)
  | arithmetic (op : Arithmetic) (dst lhs rhs : Nat)
  | comparison (op : Comparison) (dst lhs rhs : Nat)
  | jump (target : Nat)
  | jumpRegister (src : Nat)
  | branchZero (condition target : Nat)
  | halt (src : Nat)
deriving Repr, DecidableEq

inductive Category where
  | memoryRead | registerWrite | arithmetic | comparison | branch | control
deriving Repr, DecidableEq

def Instruction.category : Instruction → Category
  | .load .. => .memoryRead
  | .constant .. | .move .. => .registerWrite
  | .arithmetic .. => .arithmetic
  | .comparison .. => .comparison
  | .jump .. | .jumpRegister .. | .branchZero .. => .branch
  | .halt .. => .control

/-- Every numeric operand is enumerated, even in dormant instructions. -/
def Instruction.operands : Instruction → List Nat
  | .load dst address => [dst, address]
  | .constant dst value => [dst, value]
  | .move dst src => [dst, src]
  | .arithmetic _ dst lhs rhs | .comparison _ dst lhs rhs => [dst, lhs, rhs]
  | .jump target => [target]
  | .jumpRegister src | .halt src => [src]
  | .branchZero condition target => [condition, target]

def Arithmetic.code : Arithmetic → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .shl => 5 | .shr => 6 | .band => 7 | .bor => 8 | .bxor => 9

def Comparison.code : Comparison → Nat
  | .lt => 0 | .le => 1 | .eq => 2

/-- Explicit finite instruction serialization also counts operation tags. -/
def Instruction.encoding (i : Instruction) : List Nat :=
  (match i with
   | .load .. => [0]
   | .constant .. => [1]
   | .move .. => [2]
   | .arithmetic op .. => [3, op.code]
   | .comparison op .. => [4, op.code]
   | .jump .. => [5]
   | .jumpRegister .. => [6]
   | .branchZero .. => [7]
   | .halt .. => [8]) ++ i.operands

def Instruction.Fits (width : Nat) (i : Instruction) : Prop :=
  ∀ operand ∈ i.encoding, operand < 2 ^ width

abbrev Program := List Instruction
abbrev Memory := List Nat

inductive Status where
  | running
  | halted (value : Nat)
  | fault
deriving Repr, DecidableEq

structure State where
  regs : Registers
  pc : Nat
  status : Status

def State.writeNext (s : State) (dst value : Nat) : State :=
  { regs := s.regs.write dst value, pc := s.pc + 1, status := .running }

structure Receipt where
  address : Nat
  reply : Option Nat
deriving Repr, DecidableEq

/-- Raw loads preserve the whole physical cell, without an option tag. -/
def execute (memory : Memory) (i : Instruction) (s : State) :
    State × Option Receipt :=
  match i with
  | .load dst address =>
      let a := s.regs address
      let reply := memory[a]?
      let next := match reply with
        | some value => s.writeNext dst value
        | none => { s with status := .fault }
      (next, some ⟨a, reply⟩)
  | .constant dst value => (s.writeNext dst value, none)
  | .move dst src => (s.writeNext dst (s.regs src), none)
  | .arithmetic op dst lhs rhs =>
      (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs)), none)
  | .comparison op dst lhs rhs =>
      (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs)), none)
  | .jump target => ({ s with pc := target }, none)
  | .jumpRegister src => ({ s with pc := s.regs src }, none)
  | .branchZero condition target =>
      ({ s with pc := if s.regs condition = 0 then target else s.pc + 1 }, none)
  | .halt src => ({ s with status := .halted (s.regs src) }, none)

/-- A fetched instruction and its actual pre-state are retained for positional
provenance. These are proof observations, not additional machine registers. -/
structure Transition where
  before : State
  instruction : Instruction
  after : State
  receipt : Option Receipt

def step (memory : Memory) (program : Program) (s : State) : Option Transition :=
  match s.status with
  | .running =>
      match program[s.pc]? with
      | none => none
      | some i =>
          let result := execute memory i s
          some ⟨s, i, result.1, result.2⟩
  | _ => none

structure Run where
  final : State
  transitions : List Transition

def run (memory : Memory) (program : Program) : Nat → State → Run
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match step memory program s with
      | none => ⟨s, []⟩
      | some t =>
          let rest := run memory program fuel t.after
          ⟨rest.final, t :: rest.transitions⟩

def Run.reads (r : Run) : List Receipt :=
  r.transitions.filterMap (·.receipt)

def Run.categories (r : Run) : List Category :=
  r.transitions.map (·.instruction.category)

def Run.steps (r : Run) : Nat := r.transitions.length

def Run.result (r : Run) : Option Nat :=
  match r.final.status with
  | .halted value => some value
  | _ => none

def State.Fits (width : Nat) (s : State) : Prop :=
  s.pc < 2 ^ width ∧ (∀ r, s.regs r < 2 ^ width) ∧
  (∀ value, s.status = .halted value → value < 2 ^ width)

/-- No underflow, zero divisor, oversized shift operand, or unrepresentable
arithmetic result is licensed by the natural-number reference evaluator. -/
def Instruction.Safe (width : Nat) (s : State) (i : Instruction) : Prop :=
  i.Fits width ∧ s.Fits width ∧
  match i with
  | .arithmetic op _ lhs rhs =>
      op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width ∧
      (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
      (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
      (op = .shl ∨ op = .shr → s.regs rhs < width)
  | _ => True

end RMQ.SuccinctFinal.PackedWordRAM

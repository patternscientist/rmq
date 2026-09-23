import Std

/-! # PRE construction contract: primitive data and interpretation

This is a model definition and contract test surface, not an RMQ builder.
Memory/register access is indexed access in the declared RAM model. Functional
updates implement the mathematical store; no Lean-runtime bound is asserted.
Only `loadKey` and `compareKey` use the separately named comparison-oracle
input model. Finite-key refinement must discharge their word implementation.
Reservation claims one uninitialized cell; initialization is a separate store.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

abbrev Operand := Fin (2 ^ 32)
abbrev Memory := Nat → Option Nat
abbrev Registers := Nat → Nat

def put (f : Nat → α) (address : Nat) (value : α) : Nat → α :=
  fun i => if i = address then value else f i

inductive Arithmetic where
  | add | sub | mul | div | mod | shl | shr | band | bor | bxor
deriving DecidableEq, Repr

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
deriving DecidableEq, Repr

def Comparison.eval : Comparison → Nat → Nat → Nat
  | .lt, x, y => if x < y then 1 else 0
  | .le, x, y => if x ≤ y then 1 else 0
  | .eq, x, y => if x = y then 1 else 0

inductive Prim where
  | load (dst address : Operand)
  | constant (dst value : Operand)
  | move (dst src : Operand)
  | arithmetic (op : Arithmetic) (dst lhs rhs : Operand)
  | comparison (op : Comparison) (dst lhs rhs : Operand)
  | jump (target : Operand)
  | jumpRegister (src : Operand)
  | branchZero (condition target : Operand)
  | halt (src : Operand)
  | store (address value : Operand)
  | reserve (dst : Operand)
  | loadKey (dst address : Operand)
  | compareKey (dst lhs rhs : Operand)
deriving DecidableEq, Repr

/-- Every encoded literal, register identifier and branch target is bounded by
construction, including dormant instructions. Opcode tags are charged too. -/
def Prim.constants : Prim → List Operand
  | .load dst address => [0, dst, address]
  | .constant dst value => [1, dst, value]
  | .move dst src => [2, dst, src]
  | .arithmetic op dst lhs rhs =>
      [3, match op with
        | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
        | .shl => 5 | .shr => 6 | .band => 7 | .bor => 8 | .bxor => 9,
       dst, lhs, rhs]
  | .comparison op dst lhs rhs =>
      [4, match op with | .lt => 0 | .le => 1 | .eq => 2, dst, lhs, rhs]
  | .jump target => [5, target]
  | .jumpRegister src => [6, src]
  | .branchZero condition target => [7, condition, target]
  | .halt src => [8, src]
  | .store address value => [9, address, value]
  | .reserve dst => [10, dst]
  | .loadKey dst address => [11, dst, address]
  | .compareKey dst lhs rhs => [12, dst, lhs, rhs]

inductive Category where
  | read | register | arithmetic | comparison | branch | control | write | allocation
  | keyRead | oracleComparison
deriving DecidableEq, Repr

def Prim.category : Prim → Category
  | .load .. => .read
  | .constant .. => .register
  | .move .. => .register
  | .arithmetic .. => .arithmetic
  | .comparison .. => .comparison
  | .jump .. => .branch
  | .jumpRegister .. => .branch
  | .branchZero .. => .branch
  | .halt .. => .control
  | .store .. => .write
  | .reserve .. => .allocation
  | .loadKey .. => .keyRead
  | .compareKey .. => .oracleComparison

inductive Status where
  | running | halted (value : Nat) | fault
deriving DecidableEq, Repr

structure State where
  regs : Registers
  memory : Memory
  extent : Nat
  keys : Nat → Option Int
  keyRegs : Nat → Int
  pc : Nat
  status : Status

def State.next (s : State) : State := { s with pc := s.pc + 1 }

def State.writeNext (s : State) (dst value : Nat) : State :=
  { s.next with regs := put s.regs dst value }

/-- Exhaustive scalar interpretation. No host-list traversal or RMQ semantic
function occurs in any arm. Bounds and non-faulting reachability are separate
obligations of the future construction run. -/
def execPrim (p : Prim) (s : State) : State :=
  match p with
  | .load dst address =>
      if s.regs address < s.extent then
        match s.memory (s.regs address) with
        | some value => s.writeNext dst value
        | none => { s with status := .fault }
      else { s with status := .fault }
  | .constant dst value => s.writeNext dst value
  | .move dst src => s.writeNext dst (s.regs src)
  | .arithmetic op dst lhs rhs => s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs))
  | .comparison op dst lhs rhs => s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs))
  | .jump target => { s with pc := target }
  | .jumpRegister src => { s with pc := s.regs src }
  | .branchZero condition target =>
      { s with pc := if s.regs condition = 0 then target.val else s.pc + 1 }
  | .halt src => { s with status := .halted (s.regs src) }
  | .store address value =>
      if s.regs address < s.extent then
        { s.next with memory := put s.memory (s.regs address) (some (s.regs value)) }
      else { s with status := .fault }
  | .reserve dst => { s.writeNext dst s.extent with extent := s.extent + 1 }
  | .loadKey dst address =>
      match s.keys (s.regs address) with
      | some value => { s.next with keyRegs := put s.keyRegs dst value }
      | none => { s with status := .fault }
  | .compareKey dst lhs rhs =>
      s.writeNext dst (if s.keyRegs lhs < s.keyRegs rhs then 1 else 0)

/-- Reflected instruction data cannot carry an evaluator function. -/
structure BInstr where
  primitive : Prim
deriving DecidableEq, Repr

def BInstr.semantics (i : BInstr) : List Prim := [i.primitive]
def primCap : Nat := 1

/-- This list is a reflected sequence of charged operations, never a memory
representation or an uncharged semantic subroutine. -/
def interpretPrims : List Prim → State → State
  | [], s => s
  | p :: ps, s => interpretPrims ps (execPrim p s)

def bstep (i : BInstr) (s : State) : State := execPrim i.primitive s

theorem bstep_reflects (i : BInstr) (s : State) :
    bstep i s = interpretPrims i.semantics s := rfl

theorem semantics_cap (i : BInstr) : i.semantics.length ≤ primCap := by
  simp [BInstr.semantics, primCap]

theorem prim_const_cap (i : BInstr) (p : Prim) (_hp : p ∈ i.semantics)
    (c : Operand) (_hc : c ∈ p.constants) : c.val < 2 ^ 32 := c.isLt

theorem reserve_does_not_initialize (dst : Operand) (s : State) :
    (execPrim (.reserve dst) s).memory = s.memory := rfl

theorem store_value_from_prestate (address value : Operand) (s : State)
    (ha : s.regs address < s.extent) :
    (execPrim (.store address value) s).memory (s.regs address) = some (s.regs value) := by
  simp [execPrim, ha, put]

theorem store_other_unchanged (address value : Operand) (s : State) (location : Nat)
    (hne : location ≠ s.regs address) :
    (execPrim (.store address value) s).memory location = s.memory location := by
  by_cases h : s.regs address < s.extent
  · simp [execPrim, h, put, hne]
  · simp [execPrim, h]

end RMQ.SuccinctFinal.PackedConstruction

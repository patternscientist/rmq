import RMQ.Core.WordRAM.Construction.Primitive
import RMQ.Core.WordRAM.Packed.Primitive

/-! # Conservative scalar extension

Every old packed-query scalar instruction whose operand fields fit the fixed
construction-code field width has a constructor-by-constructor translation.
On a running prestate, its numeric execution agrees with the old interpreter.
The added mutable memory and key channels do not change these scalar steps.
This is an interpreter bridge, not a construction program or a cost bound.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Conservative

abbrev OldInstruction := PackedWordRAM.Instruction
abbrev OldState := PackedWordRAM.State

/-- Only instruction fields are restricted here; all numeric register values
are preserved. Reachable machine-word bounds are a separate obligation. -/
def OperandsFit32 (i : OldInstruction) : Prop :=
  ∀ operand ∈ i.operands, operand < 2 ^ 32

def arithmetic : PackedWordRAM.Arithmetic → Arithmetic
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .shl => .shl
  | .shr => .shr
  | .band => .band
  | .bor => .bor
  | .bxor => .bxor

def comparison : PackedWordRAM.Comparison → Comparison
  | .lt => .lt
  | .le => .le
  | .eq => .eq

theorem arithmetic_eval (op : PackedWordRAM.Arithmetic) (x y : Nat) :
    (arithmetic op).eval x y = op.eval x y := by
  cases op <;> rfl

theorem comparison_eval (op : PackedWordRAM.Comparison) (x y : Nat) :
    (comparison op).eval x y = op.eval x y := by
  cases op <;> rfl

/-- One old constructor maps to one new scalar primitive. The proofs are
erased bounds on data fields, and carry no execution result. -/
def instruction (i : OldInstruction) (h : OperandsFit32 i) : Prim :=
  match i with
  | .load dst address =>
      .load ⟨dst, h dst (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨address, h address (by simp [PackedWordRAM.Instruction.operands])⟩
  | .constant dst value =>
      .constant ⟨dst, h dst (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨value, h value (by simp [PackedWordRAM.Instruction.operands])⟩
  | .move dst src =>
      .move ⟨dst, h dst (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨src, h src (by simp [PackedWordRAM.Instruction.operands])⟩
  | .arithmetic op dst lhs rhs =>
      .arithmetic (arithmetic op)
        ⟨dst, h dst (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨lhs, h lhs (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨rhs, h rhs (by simp [PackedWordRAM.Instruction.operands])⟩
  | .comparison op dst lhs rhs =>
      .comparison (comparison op)
        ⟨dst, h dst (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨lhs, h lhs (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨rhs, h rhs (by simp [PackedWordRAM.Instruction.operands])⟩
  | .jump target =>
      .jump ⟨target, h target (by simp [PackedWordRAM.Instruction.operands])⟩
  | .jumpRegister src =>
      .jumpRegister ⟨src, h src (by simp [PackedWordRAM.Instruction.operands])⟩
  | .branchZero condition target =>
      .branchZero ⟨condition, h condition (by simp [PackedWordRAM.Instruction.operands])⟩
        ⟨target, h target (by simp [PackedWordRAM.Instruction.operands])⟩
  | .halt src =>
      .halt ⟨src, h src (by simp [PackedWordRAM.Instruction.operands])⟩

theorem operandsFit32_of_fits (i : OldInstruction) (h : i.Fits 32) :
    OperandsFit32 i := by
  intro operand hmem
  apply h operand
  cases i <;> simp_all [PackedWordRAM.Instruction.encoding,
    PackedWordRAM.Instruction.operands]

def status : PackedWordRAM.Status → Status
  | .running => .running
  | .halted value => .halted value
  | .fault => .fault

/-- Embed every register without imposing a finite register-array convention.
Old immutable list memory becomes indexed memory with its exact extent. -/
def state (memory : PackedWordRAM.Memory) (s : OldState) : State where
  regs := s.regs
  memory := fun address => memory[address]?
  extent := memory.length
  keys := fun _ => none
  keyRegs := fun _ => 0
  pc := s.pc
  status := status s.status

/-- Exact state equality covers successful and failing loads, both branch
outcomes and all arithmetic/comparison constructors. The running premise is
needed because the old `writeNext` explicitly resets status to running. -/
theorem execute_eq (memory : PackedWordRAM.Memory) (i : OldInstruction)
    (hfit : OperandsFit32 i) (s : OldState) (hrun : s.status = .running) :
    execPrim (instruction i hfit) (state memory s) =
      state memory (PackedWordRAM.execute memory i s).1 := by
  cases i with
  | load dst address =>
      cases hread : memory[s.regs address]? with
      | none =>
          have hbound := List.getElem?_eq_none_iff.mp hread
          have ha : ¬ s.regs address < memory.length := by omega
          simp [instruction, execPrim, state, PackedWordRAM.execute, ha, status]
      | some value =>
          have ha : s.regs address < memory.length :=
            (List.getElem?_eq_some_iff.mp hread).1
          simp [instruction, execPrim, state, PackedWordRAM.execute, ha,
            State.writeNext, State.next, PackedWordRAM.State.writeNext,
            hrun, status] <;> rfl
  | constant dst value =>
      simp [instruction, execPrim, state, PackedWordRAM.execute,
        State.writeNext, State.next, PackedWordRAM.State.writeNext,
        hrun, status] <;> rfl
  | move dst src =>
      simp [instruction, execPrim, state, PackedWordRAM.execute,
        State.writeNext, State.next, PackedWordRAM.State.writeNext,
        hrun, status] <;> rfl
  | arithmetic op dst lhs rhs =>
      simp [instruction, execPrim, state, PackedWordRAM.execute, arithmetic_eval,
        State.writeNext, State.next, PackedWordRAM.State.writeNext,
        hrun, status] <;> rfl
  | comparison op dst lhs rhs =>
      simp [instruction, execPrim, state, PackedWordRAM.execute, comparison_eval,
        State.writeNext, State.next, PackedWordRAM.State.writeNext,
        hrun, status] <;> rfl
  | jump target => rfl
  | jumpRegister src => rfl
  | branchZero condition target => rfl
  | halt src => rfl

/-- Explicit public projections of the same exact state equality. All added
storage is unchanged, and no key-oracle state is introduced by translation. -/
theorem execute_projections (memory : PackedWordRAM.Memory) (i : OldInstruction)
    (hfit : OperandsFit32 i) (s : OldState) (hrun : s.status = .running) :
    let actual := execPrim (instruction i hfit) (state memory s)
    let expected := (PackedWordRAM.execute memory i s).1
    actual.regs = expected.regs ∧ actual.pc = expected.pc ∧
      actual.status = status expected.status ∧
      actual.memory = (fun address => memory[address]?) ∧
      actual.extent = memory.length ∧ actual.keys = (fun _ => none) ∧
      actual.keyRegs = (fun _ => 0) := by
  dsimp only
  rw [execute_eq memory i hfit s hrun]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The accepted old encoded-field width premise supplies the translation's
operand bounds; operation tags remain accounted by the respective encodings. -/
theorem execute_eq_of_fits (memory : PackedWordRAM.Memory) (i : OldInstruction)
    (hfit : i.Fits 32) (s : OldState) (hrun : s.status = .running) :
    execPrim (instruction i (operandsFit32_of_fits i hfit)) (state memory s) =
      state memory (PackedWordRAM.execute memory i s).1 :=
  execute_eq memory i (operandsFit32_of_fits i hfit) s hrun

end Conservative

end RMQ.SuccinctFinal.PackedConstruction

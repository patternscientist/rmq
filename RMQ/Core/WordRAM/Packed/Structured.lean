import RMQ.Core.WordRAM.Packed.Calculus

/-!
# Finite structured assembly for the physical machine

The source language contains only scalar actions, scalar branches, and fixed
finite repetition. Repetition is expanded into ordinary instructions, so it
does not introduce a primitive scan or an input-dependent code generator.
The source evaluator is an independent compositional specification; no cost
claim about it is made. A compiler theorem must relate it to `Primitive.run`.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

namespace Structured

inductive Action where
  | load (dst address : Nat)
  | constant (dst value : Nat)
  | move (dst src : Nat)
  | arithmetic (op : Arithmetic) (dst lhs rhs : Nat)
  | comparison (op : Comparison) (dst lhs rhs : Nat)
deriving Repr, DecidableEq

def Action.instruction : Action → Instruction
  | .load dst address => .load dst address
  | .constant dst value => .constant dst value
  | .move dst src => .move dst src
  | .arithmetic op dst lhs rhs => .arithmetic op dst lhs rhs
  | .comparison op dst lhs rhs => .comparison op dst lhs rhs

inductive Block where
  | skip
  | action (op : Action)
  | exit (src : Nat)
  | seq (first second : Block)
  | ifZero (condition : Nat) (zero nonzero : Block)
  | repeat (count : Nat) (body : Block)
deriving Repr, DecidableEq

/-- Compile-time size; it is independent of memory and query endpoints. -/
def Block.size : Block → Nat
  | .skip => 0
  | .action _ | .exit _ => 1
  | .seq first second => first.size + second.size
  | .ifZero _ zero nonzero => 1 + nonzero.size + 1 + zero.size
  | .repeat count body => count * body.size

/-- Every branch target is resolved from the fixed syntax and block position.
Calls are inlined by source construction; no hidden call stack is introduced. -/
def Block.compileAt : Block → Nat → Program
  | .skip, _ => []
  | .action op, _ => [op.instruction]
  | .exit src, _ => [.halt src]
  | .seq first second, base =>
      first.compileAt base ++ second.compileAt (base + first.size)
  | .ifZero condition zero nonzero, base =>
      [.branchZero condition (base + 1 + nonzero.size + 1)] ++
      nonzero.compileAt (base + 1) ++
      [.jump (base + 1 + nonzero.size + 1 + zero.size)] ++
      zero.compileAt (base + 1 + nonzero.size + 1)
  | .repeat count body, base =>
      ((List.range count).map fun index => body.compileAt (base + index * body.size)).flatten

structure Data where
  regs : Registers
  status : Status

def Data.ofState (s : State) : Data := ⟨s.regs, s.status⟩

structure Evaluation where
  final : Data
  reads : List Receipt

def Action.eval (memory : Memory) (op : Action) (s : Data) : Evaluation :=
  let out := execute memory op.instruction ⟨s.regs, 0, s.status⟩
  ⟨Data.ofState out.1, out.2.toList⟩

def iterate (body : Data → Evaluation) : Nat → Data → Evaluation
  | 0, s => ⟨s, []⟩
  | count + 1, s =>
      let first := body s
      let rest := iterate body count first.final
      ⟨rest.final, first.reads ++ rest.reads⟩

/-- Source semantics has no program counter and computes no RMQ answer except
through its explicit scalar actions and reads. It is not a unit-cost machine. -/
def Block.eval (memory : Memory) (block : Block) (s : Data) : Evaluation :=
  match s.status with
  | .running =>
      match block with
      | .skip => ⟨s, []⟩
      | .action op => op.eval memory s
      | .exit src => ⟨⟨s.regs, .halted (s.regs src)⟩, []⟩
      | .seq first second =>
          let a := first.eval memory s
          let b := second.eval memory a.final
          ⟨b.final, a.reads ++ b.reads⟩
      | .ifZero condition zero nonzero =>
          if s.regs condition = 0 then zero.eval memory s else nonzero.eval memory s
      | .repeat count body => iterate (body.eval memory) count s
  | _ => ⟨s, []⟩

def Block.sequence (blocks : List Block) : Block := blocks.foldr .seq .skip

end Structured
end RMQ.SuccinctFinal.PackedWordRAM

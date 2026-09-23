import RMQ.Core.WordRAM.Packed.Structured

/-!
# Scalar blocks for total natural-number source operations

Truncated subtraction is implemented by a comparison and branch. The actual
subtraction instruction is executed only when its operands do not underflow.
These blocks expand into fixed primitive instructions and contain no reads.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def natSubBlock (dst lhs rhs tmp : Nat) : Block :=
  .seq (.action (.comparison .le tmp rhs lhs))
    (.ifZero tmp (.action (.constant dst 0))
      (.action (.arithmetic .sub dst lhs rhs)))

def minBlock (dst lhs rhs tmp : Nat) : Block :=
  .seq (.action (.comparison .le tmp lhs rhs))
    (.ifZero tmp (.action (.move dst rhs)) (.action (.move dst lhs)))

@[simp] theorem natSubBlock_size (dst lhs rhs tmp : Nat) :
    (natSubBlock dst lhs rhs tmp).size = 5 := rfl

@[simp] theorem minBlock_size (dst lhs rhs tmp : Nat) :
    (minBlock dst lhs rhs tmp).size = 5 := rfl

theorem natSubBlock_source (dst lhs rhs tmp : Nat) (memory : Memory)
    (regs : Registers) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp) :
    (natSubBlock dst lhs rhs tmp).eval memory ⟨regs, .running⟩ =
      ⟨⟨(regs.write tmp (Comparison.le.eval (regs rhs) (regs lhs))).write dst
        (regs lhs - regs rhs), .running⟩, []⟩ := by
  by_cases h : regs rhs ≤ regs lhs
  · simp [natSubBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, Comparison.eval, Arithmetic.eval,
      Registers.write, hl, hr, h]
  · have hz : regs lhs - regs rhs = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [natSubBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, Comparison.eval, Registers.write, h, hz]

theorem minBlock_source (dst lhs rhs tmp : Nat) (memory : Memory)
    (regs : Registers) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp) :
    (minBlock dst lhs rhs tmp).eval memory ⟨regs, .running⟩ =
      ⟨⟨(regs.write tmp (Comparison.le.eval (regs lhs) (regs rhs))).write dst
        (min (regs lhs) (regs rhs)), .running⟩, []⟩ := by
  by_cases h : regs lhs ≤ regs rhs
  · simp [minBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, Comparison.eval, Registers.write, hl, h,
      Nat.min_eq_left h]
  · simp [minBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, Comparison.eval, Registers.write, hr, h,
      Nat.min_eq_right (by omega : regs rhs ≤ regs lhs)]

/-- The two scalar blocks preserve all registers apart from destination and
comparison scratch. The conclusion covers arbitrary numeric source values. -/
theorem natSubBlock_frame (dst lhs rhs tmp : Nat) (memory : Memory)
    (regs : Registers) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp)
    (r : Nat) (hd : r ≠ dst) (ht : r ≠ tmp) :
    ((natSubBlock dst lhs rhs tmp).eval memory ⟨regs, .running⟩).final.regs r = regs r := by
  rw [natSubBlock_source dst lhs rhs tmp memory regs hl hr]
  simp [Registers.write, hd, ht]

theorem minBlock_frame (dst lhs rhs tmp : Nat) (memory : Memory)
    (regs : Registers) (hl : lhs ≠ tmp) (hr : rhs ≠ tmp)
    (r : Nat) (hd : r ≠ dst) (ht : r ≠ tmp) :
    ((minBlock dst lhs rhs tmp).eval memory ⟨regs, .running⟩).final.regs r = regs r := by
  rw [minBlock_source dst lhs rhs tmp memory regs hl hr]
  simp [Registers.write, hd, ht]

end RMQ.SuccinctFinal.PackedWordRAM

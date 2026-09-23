import RMQ.Core.WordRAM.Packed.Scalar

/-!
# Regular logical-word location from stored descriptor fields

Inputs are the logical index, payload bit base, bit length, stride and logical
word count. In particular, word count is not inferred from bit length: empty
sentinel words retain presence while their span length is zero. The query
loads these fields from the counted metadata bank before this block.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

structure NumericSpan where
  position : Nat
  length : Nat
deriving DecidableEq, Repr

def regularSpan (index bitBase bitLength stride count : Nat) : Option NumericSpan :=
  if index < count then
    some ⟨bitBase + index * stride, min stride (bitLength - index * stride)⟩
  else none

/-- Inputs base..base+4; outputs presence, position, length at base+5..base+7;
scratch base+8..base+10. No memory operation occurs during location. -/
def regularLocateBlock (base : Nat) : Block :=
  Block.sequence [
    .action (.constant (base + 5) 0),
    .action (.constant (base + 6) 0),
    .action (.constant (base + 7) 0),
    .action (.comparison .lt (base + 10) base (base + 4)),
    .ifZero (base + 10) .skip (Block.sequence [
      .action (.constant (base + 5) 1),
      .action (.arithmetic .mul (base + 8) base (base + 3)),
      .action (.arithmetic .add (base + 6) (base + 1) (base + 8)),
      natSubBlock (base + 9) (base + 2) (base + 8) (base + 10),
      minBlock (base + 7) (base + 3) (base + 9) (base + 10)])]

def LocatedSpan (base : Nat) (span : Option NumericSpan) (data : Data) : Prop :=
  data.status = .running ∧
    match span with
    | none => data.regs (base + 5) = 0 ∧ data.regs (base + 6) = 0 ∧
        data.regs (base + 7) = 0
    | some s => data.regs (base + 5) = 1 ∧ data.regs (base + 6) = s.position ∧
        data.regs (base + 7) = s.length

@[simp] theorem regularLocateBlock_size (base : Nat) :
    (regularLocateBlock base).size = 19 := by
  simp [regularLocateBlock, Block.sequence, Block.size, natSubBlock_size, minBlock_size]

theorem regularLocateBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    LocatedSpan base
      (regularSpan (regs base) (regs (base + 1)) (regs (base + 2))
        (regs (base + 3)) (regs (base + 4)))
      ((regularLocateBlock base).eval memory ⟨regs, .running⟩).final ∧
    ((regularLocateBlock base).eval memory ⟨regs, .running⟩).reads = [] := by
  by_cases hp : regs base < regs (base + 4)
  · by_cases hle : regs base * regs (base + 3) ≤ regs (base + 2)
    ·
      by_cases hm : regs (base + 3) ≤ regs (base + 2) - regs base * regs (base + 3)
      · simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, regularSpan,
          LocatedSpan, hp, hle, hm, Nat.min_eq_left hm]
      · simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, regularSpan,
          LocatedSpan, hp, hle, hm, Nat.min_eq_right (by omega :
            regs (base + 2) - regs base * regs (base + 3) ≤ regs (base + 3))]
    · have hs : regs (base + 2) - regs base * regs (base + 3) = 0 :=
        Nat.sub_eq_zero_of_le (by omega)
      by_cases hz : regs (base + 3) = 0
      all_goals simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, regularSpan,
          LocatedSpan, hp, hle, hs, hz]
  · simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
      Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
      Comparison.eval, regularSpan, LocatedSpan, hp]

/-- Location leaves the inputs and all registers outside its six destinations unchanged. -/
theorem regularLocateBlock_frame (base : Nat) (memory : Memory) (regs : Registers)
    (r : Nat) (hr : r < base + 5 ∨ base + 11 ≤ r) :
    ((regularLocateBlock base).eval memory ⟨regs, .running⟩).final.regs r = regs r := by
  have h5 : r ≠ base + 5 := by omega
  have h6 : r ≠ base + 6 := by omega
  have h7 : r ≠ base + 7 := by omega
  have h8 : r ≠ base + 8 := by omega
  have h9 : r ≠ base + 9 := by omega
  have h10 : r ≠ base + 10 := by omega
  by_cases hp : regs base < regs (base + 4)
  · by_cases hsub : regs base * regs (base + 3) ≤ regs (base + 2)
    · by_cases hm : regs (base + 3) ≤ regs (base + 2) - regs base * regs (base + 3)
      all_goals simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
        Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
        Comparison.eval, Arithmetic.eval, natSubBlock, minBlock,
        hp, hsub, hm, h5, h6, h7, h8, h9, h10]
    · by_cases hz : regs (base + 3) = 0
      all_goals simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
        Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
        Comparison.eval, Arithmetic.eval, natSubBlock, minBlock,
        hp, hsub, hz, h5, h6, h7, h8, h9, h10]
  · simp [regularLocateBlock, Block.sequence, Block.eval, Action.eval,
      Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
      Comparison.eval, hp, h5, h6, h7, h10]

end RMQ.SuccinctFinal.PackedWordRAM

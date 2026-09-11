import RMQ.Core.WordRAM.Packed.RegularLocate

/-!
# Interior component location by scalar descriptor arithmetic

Each component has its own word prefix and entry/chunk geometry. This source
does not concatenate the logical tables or assume entries occupy one word.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def interiorSpan (index wordPrefix count bitBase entryWidth chunks bpWidth : Nat) :
    Option NumericSpan :=
  let localIndex := index - wordPrefix
  if wordPrefix ≤ index ∧ localIndex < count then
    let entryIndex := localIndex / chunks
    let chunkOffset := (localIndex % chunks) * bpWidth
    some ⟨bitBase + chunkOffset + entryIndex * entryWidth,
      min (entryWidth - chunkOffset) bpWidth⟩
  else none

/-- Inputs base..base+6 in the order of interiorSpan. Outputs at base+7..9
are presence, absolute old bit position and length; scratch base+10..16. -/
def interiorLocateBlock (base : Nat) : Block :=
  Block.sequence [
    .action (.constant (base + 7) 0),
    .action (.constant (base + 8) 0),
    .action (.constant (base + 9) 0),
    .action (.comparison .le (base + 16) (base + 1) base),
    .ifZero (base + 16) .skip (Block.sequence [
      .action (.arithmetic .sub (base + 10) base (base + 1)),
      .action (.comparison .lt (base + 16) (base + 10) (base + 2)),
      .ifZero (base + 16) .skip (Block.sequence [
        .action (.constant (base + 7) 1),
        .action (.arithmetic .div (base + 11) (base + 10) (base + 5)),
        .action (.arithmetic .mod (base + 12) (base + 10) (base + 5)),
        .action (.arithmetic .mul (base + 12) (base + 12) (base + 6)),
        .action (.arithmetic .mul (base + 13) (base + 11) (base + 4)),
        .action (.arithmetic .add (base + 8) (base + 3) (base + 12)),
        .action (.arithmetic .add (base + 8) (base + 8) (base + 13)),
        natSubBlock (base + 14) (base + 4) (base + 12) (base + 16),
        minBlock (base + 9) (base + 14) (base + 6) (base + 16)])])]

def InteriorLocatedSpan (base : Nat) (span : Option NumericSpan) (data : Data) : Prop :=
  data.status = .running ∧
    match span with
    | none => data.regs (base + 7) = 0 ∧ data.regs (base + 8) = 0 ∧
        data.regs (base + 9) = 0
    | some s => data.regs (base + 7) = 1 ∧ data.regs (base + 8) = s.position ∧
        data.regs (base + 9) = s.length

@[simp] theorem interiorLocateBlock_size (base : Nat) :
    (interiorLocateBlock base).size = 27 := by
  simp [interiorLocateBlock, Block.sequence, Block.size, natSubBlock_size, minBlock_size]

theorem interiorLocateBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    InteriorLocatedSpan base
      (interiorSpan (regs base) (regs (base + 1)) (regs (base + 2))
        (regs (base + 3)) (regs (base + 4)) (regs (base + 5)) (regs (base + 6)))
      ((interiorLocateBlock base).eval memory ⟨regs, .running⟩).final ∧
    ((interiorLocateBlock base).eval memory ⟨regs, .running⟩).reads = [] := by
  by_cases hp : regs (base + 1) ≤ regs base
  · by_cases hc : regs base - regs (base + 1) < regs (base + 2)
    · by_cases hsub : ((regs base - regs (base + 1)) % regs (base + 5)) *
          regs (base + 6) ≤ regs (base + 4)
      · by_cases hm : regs (base + 4) - ((regs base - regs (base + 1)) %
              regs (base + 5)) * regs (base + 6) ≤ regs (base + 6)
        · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
            Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
            Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, interiorSpan,
            InteriorLocatedSpan, hp, hc, hsub, hm, Nat.min_eq_left hm]
        · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
            Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
            Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, interiorSpan,
            InteriorLocatedSpan, hp, hc, hsub, hm, Nat.min_eq_right (by omega :
              regs (base + 6) ≤ regs (base + 4) - ((regs base - regs (base + 1)) %
                regs (base + 5)) * regs (base + 6))]
      · have hs : regs (base + 4) - ((regs base - regs (base + 1)) % regs (base + 5)) *
            regs (base + 6) = 0 := Nat.sub_eq_zero_of_le (by omega)
        simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock, interiorSpan,
          InteriorLocatedSpan, hp, hc, hsub, hs]
    · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
        Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
        Comparison.eval, Arithmetic.eval, interiorSpan, InteriorLocatedSpan, hp, hc]
  · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
      Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
      Comparison.eval, interiorSpan, InteriorLocatedSpan, hp]

/-- Every input and every register outside the declared output/scratch interval is preserved. -/
theorem interiorLocateBlock_frame (base : Nat) (memory : Memory) (regs : Registers)
    (r : Nat) (hr : r < base + 7 ∨ base + 17 ≤ r) :
    ((interiorLocateBlock base).eval memory ⟨regs, .running⟩).final.regs r = regs r := by
  have h7 : r ≠ base + 7 := by omega
  have h8 : r ≠ base + 8 := by omega
  have h9 : r ≠ base + 9 := by omega
  have h10 : r ≠ base + 10 := by omega
  have h11 : r ≠ base + 11 := by omega
  have h12 : r ≠ base + 12 := by omega
  have h13 : r ≠ base + 13 := by omega
  have h14 : r ≠ base + 14 := by omega
  have h16 : r ≠ base + 16 := by omega
  by_cases hp : regs (base + 1) ≤ regs base
  · by_cases hc : regs base - regs (base + 1) < regs (base + 2)
    · by_cases hsub : ((regs base - regs (base + 1)) % regs (base + 5)) *
          regs (base + 6) ≤ regs (base + 4)
      · by_cases hm : regs (base + 4) - ((regs base - regs (base + 1)) %
            regs (base + 5)) * regs (base + 6) ≤ regs (base + 6)
        all_goals simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock,
          hp, hc, hsub, hm, h7, h8, h9, h10, h11, h12, h13, h14, h16]
      · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
          Comparison.eval, Arithmetic.eval, natSubBlock, minBlock,
          hp, hc, hsub, h7, h8, h9, h10, h11, h12, h13, h14, h16]
    · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
        Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
        Comparison.eval, Arithmetic.eval, hp, hc, h7, h8, h9, h10, h16]
  · simp [interiorLocateBlock, Block.sequence, Block.eval, Action.eval,
      Action.instruction, execute, State.writeNext, Data.ofState, Registers.write,
      Comparison.eval, hp, h7, h8, h9, h16]

end RMQ.SuccinctFinal.PackedWordRAM

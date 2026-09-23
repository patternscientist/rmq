import RMQ.Core.WordRAM.Packed.Scalar
import RMQ.Core.WordRAM.Packed.Compiler
import RMQ.Core.WordRAM.E1RankBridge
import RMQ.Core.WordRAM.Packed.Frame

/-!
# Scalar arithmetic around charged chunk-table reads

These fixed blocks compute the rank-table address and decode a returned entry.
The intervening table read belongs to the physical logical-read block. There
is no rank/popcount operation in the primitive vocabulary.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured SuccinctSpace

def chunkSlot (word chunkBits chunkIndex effective : Nat) : Nat :=
  let length := min chunkBits (effective - chunkIndex * chunkBits)
  let value := word / 2 ^ (chunkIndex * chunkBits) % 2 ^ chunkBits
  (value * (chunkBits + 1) + length) * (chunkBits + 1) + length

/-- Inputs word,c,j,e at base..base+3; outputs length,value,slot at base+4..6;
scratch base+7..11. -/
def chunkSlotBlock (base : Nat) : Block :=
  Block.sequence [
    .action (.constant (base + 7) 1),
    .action (.arithmetic .mul (base + 8) (base + 2) (base + 1)),
    natSubBlock (base + 9) (base + 3) (base + 8) (base + 11),
    minBlock (base + 4) (base + 1) (base + 9) (base + 11),
    .action (.arithmetic .shl (base + 9) (base + 7) (base + 1)),
    .action (.arithmetic .shr (base + 5) base (base + 8)),
    .action (.arithmetic .mod (base + 5) (base + 5) (base + 9)),
    .action (.arithmetic .add (base + 10) (base + 1) (base + 7)),
    .action (.arithmetic .mul (base + 6) (base + 5) (base + 10)),
    .action (.arithmetic .add (base + 6) (base + 6) (base + 4)),
    .action (.arithmetic .mul (base + 6) (base + 6) (base + 10)),
    .action (.arithmetic .add (base + 6) (base + 6) (base + 4))]

@[simp] theorem chunkSlotBlock_size (base : Nat) :
    (chunkSlotBlock base).size = 20 := by
  simp [chunkSlotBlock, Block.sequence, Block.size, natSubBlock_size, minBlock_size]

theorem chunkSlotBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := (chunkSlotBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs (base + 4) = min (regs (base + 1))
      (regs (base + 3) - regs (base + 2) * regs (base + 1)) ∧
    actual.final.regs (base + 5) = regs base /
      2 ^ (regs (base + 2) * regs (base + 1)) % 2 ^ regs (base + 1) ∧
    actual.final.regs (base + 6) = chunkSlot (regs base) (regs (base + 1))
      (regs (base + 2)) (regs (base + 3)) := by
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
  have shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
  by_cases hsub : regs (base + 2) * regs (base + 1) ≤ regs (base + 3)
  · by_cases hmin : regs (base + 1) ≤ regs (base + 3) - regs (base + 2) * regs (base + 1)
    · simp [chunkSlotBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
        execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
        Comparison.eval, natSubBlock, minBlock, chunkSlot, shiftLeft_numeric,
        shiftRight_numeric, hsub, hmin, Nat.min_eq_left hmin]
    · simp [chunkSlotBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
        execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
        Comparison.eval, natSubBlock, minBlock, chunkSlot, shiftLeft_numeric,
        shiftRight_numeric, hsub, hmin, Nat.min_eq_right (by omega :
          regs (base + 3) - regs (base + 2) * regs (base + 1) ≤ regs (base + 1))]
  · have hs : regs (base + 3) - regs (base + 2) * regs (base + 1) = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    by_cases hz : regs (base + 1) = 0
    all_goals simp [chunkSlotBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
      Comparison.eval, natSubBlock, minBlock, chunkSlot, shiftLeft_numeric,
      shiftRight_numeric, hsub, hs, hz]

theorem chunkSlot_eq_reference (word : List Bool) (c e j : Nat) :
    chunkSlot (bitsToNatLE word) c j e =
      SuccinctClose.bpWordRankChunkSlotAt c word e j := by
  simp [chunkSlot, SuccinctClose.bpWordRankChunkSlotAt,
    SuccinctClose.bpFringeChunkSlot, SuccinctClose.bpWordChunkSliceLen,
    SuccinctClose.bpFringeWindowChunkValue_eq_div_mod]

def chunkRank (c length entry target : Nat) : Nat :=
  let ones := (entry / (c + 1) % (2 * (c + 1)) + length - c) / 2
  if target = 0 then length - ones else ones

/-- Inputs c,length,entry,target at base..base+3; output base+4; scratch5..10. -/
def chunkRankBlock (base : Nat) : Block :=
  Block.sequence [
    .action (.constant (base + 5) 1),
    .action (.constant (base + 6) 2),
    .action (.arithmetic .add (base + 7) base (base + 5)),
    .action (.arithmetic .mul (base + 8) (base + 6) (base + 7)),
    .action (.arithmetic .div (base + 9) (base + 2) (base + 7)),
    .action (.arithmetic .mod (base + 9) (base + 9) (base + 8)),
    .action (.arithmetic .add (base + 9) (base + 9) (base + 1)),
    natSubBlock (base + 9) (base + 9) base (base + 10),
    .action (.arithmetic .div (base + 9) (base + 9) (base + 6)),
    .ifZero (base + 3)
      (natSubBlock (base + 4) (base + 1) (base + 9) (base + 10))
      (.action (.move (base + 4) (base + 9)))]

@[simp] theorem chunkRankBlock_size (base : Nat) :
    (chunkRankBlock base).size = 21 := by
  simp [chunkRankBlock, Block.sequence, Block.size, natSubBlock_size]

theorem chunkRankBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := (chunkRankBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs (base + 4) = chunkRank (regs base) (regs (base + 1))
      (regs (base + 2)) (regs (base + 3)) := by
  by_cases hsub : regs base ≤ regs (base + 2) / (regs base + 1) %
      (2 * (regs base + 1)) + regs (base + 1)
  · by_cases ht : regs (base + 3) = 0
    · by_cases hn : (regs (base + 2) / (regs base + 1) % (2 * (regs base + 1)) +
          regs (base + 1) - regs base) / 2 ≤ regs (base + 1)
      · simp [chunkRankBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
          execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
          Comparison.eval, natSubBlock, chunkRank, hsub, ht, hn]
      · have hz : regs (base + 1) - (regs (base + 2) / (regs base + 1) %
            (2 * (regs base + 1)) + regs (base + 1) - regs base) / 2 = 0 :=
          Nat.sub_eq_zero_of_le (by omega)
        simp [chunkRankBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
          execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
          Comparison.eval, natSubBlock, chunkRank, hsub, ht, hn, hz]
    · simp [chunkRankBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
        execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
        Comparison.eval, natSubBlock, chunkRank, hsub, ht]
  · have hz : regs (base + 2) / (regs base + 1) % (2 * (regs base + 1)) +
        regs (base + 1) - regs base = 0 := Nat.sub_eq_zero_of_le (by omega)
    by_cases ht : regs (base + 3) = 0
    all_goals simp [chunkRankBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
      Comparison.eval, natSubBlock, chunkRank, hsub, ht, hz]

theorem chunkSlotBlock_machine (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := run memory ((chunkSlotBlock base).compileAt 0 ++ [.halt (base + 6)])
      21 ⟨regs, 0, .running⟩
    actual.result = some (chunkSlot (regs base) (regs (base + 1))
      (regs (base + 2)) (regs (base + 3))) ∧ actual.reads = [] ∧ actual.steps ≤ 21 := by
  have hs := chunkSlotBlock_source base memory regs
  have hm := (chunkSlotBlock base).compile_with_halt memory (base + 6)
    ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hm ⊢
  rw [hs.1] at hm
  exact ⟨by simpa [hs.2.2.2.2, chunkSlotBlock_size] using hm.2.1,
    by simpa [hs.2.1, chunkSlotBlock_size] using hm.2.2.1,
    by simpa [chunkSlotBlock_size] using hm.2.2.2⟩

theorem chunkRankBlock_machine (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := run memory ((chunkRankBlock base).compileAt 0 ++ [.halt (base + 4)])
      22 ⟨regs, 0, .running⟩
    actual.result = some (chunkRank (regs base) (regs (base + 1))
      (regs (base + 2)) (regs (base + 3))) ∧ actual.reads = [] ∧ actual.steps ≤ 22 := by
  have hs := chunkRankBlock_source base memory regs
  have hm := (chunkRankBlock base).compile_with_halt memory (base + 4)
    ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hm ⊢
  rw [hs.1] at hm
  exact ⟨by simpa [hs.2.2, chunkRankBlock_size] using hm.2.1,
    by simpa [hs.2.1, chunkRankBlock_size] using hm.2.2.1,
    by simpa [chunkRankBlock_size] using hm.2.2.2⟩

theorem chunkRank_eq_reference (c length entry : Nat) (target : Bool) :
    chunkRank c length entry (if target then 1 else 0) =
      SuccinctClose.bpChunkRankOfEntry c target length entry := by
  cases target <;> simp [chunkRank, SuccinctClose.bpChunkRankOfEntry,
    Nat.mul_add]

theorem chunkSlotBlock_writes (base : Nat) :
    (chunkSlotBlock base).WritesOnly (fun r => base + 4 ≤ r ∧ r < base + 12) := by
  simp [chunkSlotBlock, Block.sequence, Block.WritesOnly, Action.destination,
    natSubBlock, minBlock]

theorem chunkRankBlock_writes (base : Nat) :
    (chunkRankBlock base).WritesOnly (fun r => base + 4 ≤ r ∧ r < base + 11) := by
  simp [chunkRankBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem chunkSlotBlock_frame (base : Nat) (memory : Memory) (s : Data)
    (r : Nat) (outside : r < base + 4 ∨ base + 12 ≤ r) :
    ((chunkSlotBlock base).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (chunkSlotBlock_writes base) r (by omega) s

theorem chunkRankBlock_frame (base : Nat) (memory : Memory) (s : Data)
    (r : Nat) (outside : r < base + 4 ∨ base + 11 ≤ r) :
    ((chunkRankBlock base).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (chunkRankBlock_writes base) r (by omega) s

end RMQ.SuccinctFinal.PackedWordRAM

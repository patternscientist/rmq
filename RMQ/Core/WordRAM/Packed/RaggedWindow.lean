import RMQ.Core.WordRAM.Packed.Compiler
import RMQ.Core.WordRAM.Packed.Width
import RMQ.Core.WordRAM.E1FringeBridge

/-!
# Four logical words in one larger physical word

The new word width exceeds four old word widths. Four logical replies can
therefore be concatenated in a register using their actual lengths, including
zero-length absent replies. This never concatenates two full physical cells.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured SuccinctSpace

def raggedWindowValue (w0 w1 w2 w3 l0 l1 l2 : Nat) : Nat :=
  w0 + 2 ^ l0 * (w1 + 2 ^ l1 * (w2 + 2 ^ l2 * w3))

theorem raggedWindowValue_eq_bits (a b c d : List Bool) :
    raggedWindowValue (bitsToNatLE a) (bitsToNatLE b) (bitsToNatLE c)
      (bitsToNatLE d) a.length b.length c.length =
    bitsToNatLE (a ++ b ++ c ++ d) := by
  simp [raggedWindowValue, SuccinctClose.bitsToNatLE_append, Nat.mul_add]

private theorem concat_lt_pow (a b la lb : Nat)
    (ha : a < 2 ^ la) (hb : b < 2 ^ lb) :
    a + 2 ^ la * b < 2 ^ (la + lb) := by
  have hm := Nat.mul_le_mul_left (2 ^ la) (Nat.succ_le_of_lt hb)
  rw [Nat.mul_succ] at hm
  rw [Nat.pow_add]
  omega

theorem raggedWindowValue_lt_pow (w0 w1 w2 w3 l0 l1 l2 l3 : Nat)
    (h0 : w0 < 2 ^ l0) (h1 : w1 < 2 ^ l1)
    (h2 : w2 < 2 ^ l2) (h3 : w3 < 2 ^ l3) :
    raggedWindowValue w0 w1 w2 w3 l0 l1 l2 < 2 ^ (l0 + l1 + l2 + l3) := by
  have h23 := concat_lt_pow w2 w3 l2 l3 h2 h3
  have h123 := concat_lt_pow w1 _ l1 (l2 + l3) h1 h23
  have h0123 := concat_lt_pow w0 _ l0 (l1 + (l2 + l3)) h0 h123
  simpa [raggedWindowValue, Nat.add_assoc] using h0123

theorem fourOldWidths_lt_wordWidth (n : Nat) :
    4 * PackedCellProbe.packedReviewerCellWidth n < wordWidth n := by
  unfold wordWidth
  omega

theorem raggedWindowValue_fits (n w0 w1 w2 w3 l0 l1 l2 l3 : Nat)
    (h0 : w0 < 2 ^ l0) (h1 : w1 < 2 ^ l1)
    (h2 : w2 < 2 ^ l2) (h3 : w3 < 2 ^ l3)
    (hl0 : l0 ≤ PackedCellProbe.packedReviewerCellWidth n)
    (hl1 : l1 ≤ PackedCellProbe.packedReviewerCellWidth n)
    (hl2 : l2 ≤ PackedCellProbe.packedReviewerCellWidth n)
    (hl3 : l3 ≤ PackedCellProbe.packedReviewerCellWidth n) :
    raggedWindowValue w0 w1 w2 w3 l0 l1 l2 < 2 ^ wordWidth n := by
  have hval := raggedWindowValue_lt_pow w0 w1 w2 w3 l0 l1 l2 l3 h0 h1 h2 h3
  have hs := fourOldWidths_lt_wordWidth n
  have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
    (show l0 + l1 + l2 + l3 ≤ wordWidth n by omega)
  exact Nat.lt_of_lt_of_le hval hpow

/-- Inputs base..base+3 are values and base+4..base+7 are actual lengths.
Only base+8 is written. The final length is needed for bounds, not shifts. -/
def raggedWindowBlock (base : Nat) : Block :=
  Block.sequence [
    .action (.arithmetic .shl (base + 8) (base + 3) (base + 6)),
    .action (.arithmetic .add (base + 8) (base + 2) (base + 8)),
    .action (.arithmetic .shl (base + 8) (base + 8) (base + 5)),
    .action (.arithmetic .add (base + 8) (base + 1) (base + 8)),
    .action (.arithmetic .shl (base + 8) (base + 8) (base + 4)),
    .action (.arithmetic .add (base + 8) base (base + 8))]

@[simp] theorem raggedWindowBlock_size (base : Nat) :
    (raggedWindowBlock base).size = 6 := by
  simp [raggedWindowBlock, Block.sequence, Block.size]

theorem raggedWindowBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := (raggedWindowBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
    actual.final.regs (base + 8) =
      raggedWindowValue (regs base) (regs (base + 1)) (regs (base + 2))
        (regs (base + 3)) (regs (base + 4)) (regs (base + 5)) (regs (base + 6)) ∧
    (∀ r, r ≠ base + 8 → actual.final.regs r = regs r) := by
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b :=
    Nat.shiftLeft_eq a b
  simp [raggedWindowBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, Registers.write, Arithmetic.eval,
    shiftLeft_numeric, raggedWindowValue, Nat.mul_comm]
  intro r hr
  simp [hr]

theorem raggedWindowBlock_bits (base : Nat) (memory : Memory) (regs : Registers)
    (a b c d : List Bool)
    (h0 : regs base = bitsToNatLE a) (h1 : regs (base + 1) = bitsToNatLE b)
    (h2 : regs (base + 2) = bitsToNatLE c) (h3 : regs (base + 3) = bitsToNatLE d)
    (hl0 : regs (base + 4) = a.length) (hl1 : regs (base + 5) = b.length)
    (hl2 : regs (base + 6) = c.length) :
    ((raggedWindowBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 8) =
      bitsToNatLE (a ++ b ++ c ++ d) := by
  rw [(raggedWindowBlock_source base memory regs).2.2.1,
    h0, h1, h2, h3, hl0, hl1, hl2, raggedWindowValue_eq_bits]

theorem raggedWindowBlock_machine (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := run memory ((raggedWindowBlock base).compileAt 0 ++ [.halt (base + 8)])
      7 ⟨regs, 0, .running⟩
    actual.result = some (raggedWindowValue (regs base) (regs (base + 1))
      (regs (base + 2)) (regs (base + 3)) (regs (base + 4)) (regs (base + 5))
      (regs (base + 6))) ∧ actual.reads = [] ∧ actual.steps ≤ 7 ∧
    (∀ r, r ≠ base + 8 → actual.final.regs r = regs r) := by
  have hs := raggedWindowBlock_source base memory regs
  have hm := (raggedWindowBlock base).compile_with_halt memory (base + 8)
    ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hm ⊢
  rw [hs.1] at hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [raggedWindowBlock_size, Data.ofState, hs.2.2.1] using hm.2.1
  · simpa [raggedWindowBlock_size, Data.ofState, hs.2.1] using hm.2.2.1
  · simpa [raggedWindowBlock_size] using hm.2.2.2
  · intro r hr
    have hd := hm.1
    simp only [raggedWindowBlock_size] at hd
    have hstatus := hs.1
    simp only [Block.eval, hstatus] at hd
    exact (congrArg (fun data : Data => data.regs r) hd).trans (hs.2.2.2 r hr)

end RMQ.SuccinctFinal.PackedWordRAM

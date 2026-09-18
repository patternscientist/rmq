import RMQ.Core.WordRAM.Bitvector.SafetyInterface
import RMQ.Core.WordRAM.Bitvector.CompleteLayout
import RMQ.Core.WordRAM.Bitvector.Width

/-! # Concrete logarithmic-width limits for the shared controllers

These are numerical consequences of the declared width and the stored word
lengths. They do not change the executable programs or their allocation.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

theorem chunkBits_le_machine (n : Nat) :
    SuccinctClose.bpFringeChunkBits (2*n) ≤ machineWordBits n := by
  have h := log2_double_le n
  have hm := machineWordBits_pos n
  unfold SuccinctClose.bpFringeChunkBits machineWordBits at *
  omega

theorem chunkTable_width_le (n : Nat) :
    SuccinctClose.bpFringeChunkEntryWidth (SuccinctClose.bpFringeChunkBits (2*n)) ≤
      machineWordBits n + 8 := by
  have hb := SuccinctClose.bpFringeChunkEntryWidth_le (SuccinctClose.bpFringeChunkBits (2*n))
  have hl := log2_double_le n
  unfold SuccinctClose.bpFringeChunkBits machineWordBits at *
  omega

def canonicalEnvelope (n : Nat) : Nat := 2 ^ (9 + 2 * machineWordBits n)

private theorem canonical_output (m : Nat) (hm : 0 < m) :
    8*m + 2 * max (2^(2*m+3)) (2^(m+8)) ≤ 2^(9+2*m) := by
  have hd : 2^(2*m+3) ≤ 2^(7+2*m) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht : 2^(m+8) ≤ 2^(7+2*m) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmax : max (2^(2*m+3)) (2^(m+8)) ≤ 2^(7+2*m) := Nat.max_le.mpr ⟨hd, ht⟩
  have hlin : 8*m ≤ 2^(8+2*m) := by
    have hmul := Nat.mul_le_mul_left 8 (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))
    have hp : 2^(3+m) ≤ 2^(8+2*m) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_add] at hp
    change 8 * 2^m ≤ 2^(8+2*m) at hp
    omega
  have he1 : 2^(8+2*m) = 2 * 2^(7+2*m) := by
    rw [show 8+2*m = (7+2*m)+1 by omega, Nat.pow_succ, Nat.mul_comm]
  have he2 : 2^(9+2*m) = 2 * 2^(8+2*m) := by
    rw [show 9+2*m = (8+2*m)+1 by omega, Nat.pow_succ, Nat.mul_comm]
  omega

/-- All controller bounds use this one width, with no small-input dispatch. -/
def canonicalLimits (n : Nat) : Controller.SafetyLimits where
  width := Experiment.width n
  rawWidth := machineWordBits n
  directoryBound := 2 ^ (2 * machineWordBits n + 3)
  tableBound := 2 ^ (machineWordBits n + 8)
  envelope := canonicalEnvelope n
  width32 := width_floor n
  rawShift := by unfold Experiment.width; omega
  rawCapacity := Nat.pow_le_pow_right (by decide) (by omega)
  output := canonical_output _ (machineWordBits_pos n)
  cubic := by
    have hm := machineWordBits_pos n
    have hp : 2^(32+6*machineWordBits n) < 2^(32+16*machineWordBits n) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    change 32 * (2^(9+2*machineWordBits n) * 2^(9+2*machineWordBits n) *
      2^(9+2*machineWordBits n)) < 2^(32+16*machineWordBits n)
    rw [← Nat.pow_add, ← Nat.pow_add]
    change 2^5 * 2^((9+2*machineWordBits n)+(9+2*machineWordBits n)+(9+2*machineWordBits n)) < _
    rw [← Nat.pow_add]
    simpa only [show 5+((9+2*machineWordBits n)+(9+2*machineWordBits n)+
      (9+2*machineWordBits n)) = 32+6*machineWordBits n by omega] using hp
  square := by
    have hp : 2^(26+4*machineWordBits n) < 2^(32+16*machineWordBits n) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    change 256 * (2^(9+2*machineWordBits n) * 2^(9+2*machineWordBits n)) <
      2^(32+16*machineWordBits n)
    rw [← Nat.pow_add]
    change 2^8 * 2^((9+2*machineWordBits n)+(9+2*machineWordBits n)) < _
    rw [← Nat.pow_add]
    simpa only [show 8+((9+2*machineWordBits n)+(9+2*machineWordBits n)) =
      26+4*machineWordBits n by omega] using hp

theorem optional_length_le (words : Array (List Bool)) (cap index : Nat)
    (bound : ∀ word ∈ words.toList, word.length ≤ cap) :
    logicalLength words[index]? ≤ cap := by
  cases hg : words[index]? with
  | none => simp [logicalLength]
  | some word =>
    have hw : word ∈ words.toList := List.mem_of_getElem? (by simpa using hg)
    simpa [logicalLength, hg] using bound word hw

theorem logicalPacket_le_of_length (word : Option (List Bool)) (cap : Nat)
    (bound : logicalLength word ≤ cap) : logicalPacket word ≤ 2^cap := by
  cases word with
  | none => simp
  | some bits =>
    have hn := bitsToNatLE_lt_two_pow_length bits
    have hp : 2^bits.length ≤ 2^cap := Nat.pow_le_pow_right (by decide) bound
    simp only [logicalPacket_some]
    omega

theorem normalizedSegmentWord_length (target : Bool) (segment : Nat)
    (word : Option (List Bool)) :
    logicalLength (normalizedSegmentWord target segment word) = logicalLength word := by
  unfold normalizedSegmentWord
  split
  · exact normalize_optional_length target word
  · rfl

end RMQ.PackedBitvector

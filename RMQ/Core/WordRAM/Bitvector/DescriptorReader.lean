import RMQ.Core.WordRAM.Bitvector.NumericReader
import RMQ.Core.WordRAM.Bitvector.RegularLayout

/-! # Physical-reader refinement from actual descriptors and decoded spans

The hypotheses describe the supplied numerical memory. They do not specialize
the reader source and do not supply it with an executable semantic store.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace Experiment
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def normalizedSegmentWord (target : Bool) (segment : Nat)
    (word : Option (List Bool)) : Option (List Bool) :=
  if segment = 0 then word.map (normalize target) else word

theorem physicalReader_regular_words (mem : Memory) (regs : Registers)
    (target : Bool) (words : Array (List Bool)) (base : Nat)
    (htarget : regs 3 = target.toNat) (hs : regs 8192 < 23)
    (hregular : RegularWords words)
    (hbase : mem[numericDescriptorAddress regs]? = some base)
    (hlen : mem[numericDescriptorAddress regs + 1]? = some (segmentBits words).length)
    (hstride : mem[numericDescriptorAddress regs + 2]? = some (firstLength words))
    (hcount : mem[numericDescriptorAddress regs + 3]? = some words.size)
    (hdecode : ∀ hi : regs 8193 < words.size,
      decodeSpanNat (regs 22) (base + regs 8193 * firstLength words)
        (min (firstLength words) ((segmentBits words).length - regs 8193 * firstLength words))
        mem = some (bitsToNatLE words[regs 8193])) :
    let actual := physicalReader.eval mem ⟨regs, .running⟩
    let expected := normalizedSegmentWord target (regs 8192) words[regs 8193]?
    actual.final.status = .running ∧
    actual.final.regs 8194 = readerPacket expected ∧
    actual.final.regs 8195 = readerLength expected ∧
    actual.reads = (if regs 8193 < words.size then
      numericDescriptorReceipts mem regs ++
        spanAttemptReceipts (regs 22) (base + regs 8193 * firstLength words)
          (min (firstLength words) ((segmentBits words).length - regs 8193 * firstLength words)) mem
      else numericDescriptorReceipts mem regs) ∧
    GenericReaderFrame regs actual.final.regs := by
  dsimp only
  by_cases hi : regs 8193 < words.size
  · have h := physicalReader_present mem regs base (segmentBits words).length
      (firstLength words) words.size (bitsToNatLE words[regs 8193]) hs
      hbase hlen hstride hcount hi (hdecode hi)
    have hl := hregular.length_eq (regs 8193) hi
    have he : normalizedSegmentWord target (regs 8192) words[regs 8193]? =
        if regs 8192 = 0 then some (normalize target words[regs 8193])
        else some words[regs 8193] := by
      simp only [normalizedSegmentWord, Array.getElem?_eq_getElem hi, Option.map_some]
    have hp : (if regs 8192 = 0 ∧ regs 3 ≠ 0 then
        2 ^ words[regs 8193].length - bitsToNatLE words[regs 8193]
        else bitsToNatLE words[regs 8193] + 1) =
          readerPacket (normalizedSegmentWord target (regs 8192) words[regs 8193]?) := by
      rw [he]
      by_cases hz : regs 8192 = 0 <;> cases target <;>
        simp [hz, readerPacket, htarget]
      simpa using (normalize_numeric_packet true words[regs 8193]).symm
    refine ⟨h.1, ?_, ?_, ?_, h.2.2.2.2⟩
    · rw [h.2.1, ← hl]
      exact hp
    · rw [h.2.2.1, ← hl, he]
      by_cases hz : regs 8192 = 0 <;> simp [readerLength, hz]
    · rw [h.2.2.2.1, if_pos hi]
  · have h := physicalReader_absent mem regs base (segmentBits words).length
      (firstLength words) words.size hs hbase hlen hstride hcount (Nat.le_of_not_gt hi)
    have he : normalizedSegmentWord target (regs 8192) words[regs 8193]? = none := by
      simp [normalizedSegmentWord, Array.getElem?_eq_none (Nat.le_of_not_gt hi)]
    simpa only [he, readerPacket, readerLength, Option.map_none, Option.getD_none,
      if_neg hi] using h

end RMQ.PackedBitvector

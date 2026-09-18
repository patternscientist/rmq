import RMQ.Core.WordRAM.Bitvector.CompleteLayout
import RMQ.Core.WordRAM.Bitvector.ControllerInterface

/-! # Charged physical reading from the complete allocation

The receipt specification reads the same numerical descriptor fields used by
the program. All hypotheses connecting that memory to logical words are proved
from the single allocation, for both targets and every request.
-/

namespace RMQ.PackedBitvector.Allocation

open SuccinctSpace
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

private theorem readerPacket_eq_logicalPacket (word : Option (List Bool)) :
    readerPacket word = logicalPacket word := by cases word <;> rfl

def readerReceipts (bits : List Bool) (target : Bool) (segment index : Nat) : List Receipt :=
  if segment < 23 then
    let address := 23 + target.toNat * 92 + segment * 4
    let mem := memory bits
    let prefixReads := (List.range 4).map fun i => ⟨address + i, mem[address + i]?⟩
    let count := mem[address + 3]?.getD 0
    if index < count then
      let base := mem[address]?.getD 0
      let bitLength := mem[address + 1]?.getD 0
      let stride := mem[address + 2]?.getD 0
      prefixReads ++ spanAttemptReceipts (Experiment.width bits.length)
        (base + index * stride) (min stride (bitLength - index * stride)) mem
    else prefixReads
  else []

theorem descriptor_reads (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) (hs : regs 8192 < 23)
    (field : Nat) (hf : field < 4) :
    (memory bits)[numericDescriptorAddress regs + field]? =
      some ((bankDescriptor bits target (regs 8192))[field]?.getD 0) := by
  have h := memory_descriptor_present bits target (regs 8192) field hs hf
  simpa only [numericDescriptorAddress, hm.1] using h

theorem readerReceipts_eq (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) (hs : regs 8192 < 23) :
    readerReceipts bits target (regs 8192) (regs 8193) =
      let desc := bankDescriptor bits target (regs 8192)
      if regs 8193 < desc[3]?.getD 0 then numericDescriptorReceipts (memory bits) regs ++
        spanAttemptReceipts (regs 22) (desc[0]?.getD 0 + regs 8193 * (desc[2]?.getD 0))
          (min (desc[2]?.getD 0) (desc[1]?.getD 0 - regs 8193 * (desc[2]?.getD 0))) (memory bits)
      else numericDescriptorReceipts (memory bits) regs := by
  have h0 := descriptor_reads bits target regs hm hs 0 (by decide)
  have h1 := descriptor_reads bits target regs hm hs 1 (by decide)
  have h2 := descriptor_reads bits target regs hm hs 2 (by decide)
  have h3 := descriptor_reads bits target regs hm hs 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [numericDescriptorAddress, hm.1] at h0 h1 h2 h3
  simp only [readerReceipts, if_pos hs, h0, h1, h2, h3, Option.getD_some,
    numericDescriptorReceipts, numericDescriptorAddress, hm.1, hm.2]

theorem physicalReader_correct (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) :
    let actual := Experiment.physicalReader.eval (memory bits) ⟨regs, .running⟩
    let expected := (readStore bits target).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts bits target (regs 8192) (regs 8193) ∧
    ReaderFrame regs actual.final.regs := by
  dsimp only
  by_cases hs : regs 8192 < 23
  · have h0 := descriptor_reads bits target regs hm hs 0 (by decide)
    have h1 := descriptor_reads bits target regs hm hs 1 (by decide)
    have h2 := descriptor_reads bits target regs hm hs 2 (by decide)
    have h3 := descriptor_reads bits target regs hm hs 3 (by decide)
    simp only [Nat.add_zero] at h0
    have hr := readerReceipts_eq bits target regs hm hs
    by_cases hp : activeSegment (regs 8192)
    · let words := logicalWords bits target (regs 8192)
      let base := 207 * Experiment.width bits.length +
        Experiment.componentOffset (allSegments bits) (physicalComponent target (regs 8192))
      have hd := bankDescriptor_active bits target (regs 8192) hp
      change bankDescriptor bits target (regs 8192) = Experiment.descriptor base words at hd
      simp only [hd, Experiment.descriptor, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at h0 h1 h2 h3 hr
      have h := physicalReader_regular_words (memory bits) regs target words base hm.1 hs
        (logicalWords_regular bits target (regs 8192) hp) h0 h1 h2 h3 (by
          intro hi
          simpa only [words, base, hm.2] using
            decode_logicalWords bits target (regs 8192) (regs 8193) hp hi)
      change _ ∧ _ = readerPacket _ ∧ _ = readerLength _ ∧ _ = _ ∧ _ at h
      simpa only [readStore, logicalWord, words, readerPacket_eq_logicalPacket,
        readerLength, logicalLength, hr, firstLength] using h
    · have he : regs 8192 = 20 := by unfold activeSegment at hp; omega
      have hd : bankDescriptor bits target (regs 8192) = [0, 0, 0, 0] := by
        rw [bankDescriptor_eq_selected bits target (regs 8192) hs, he]
        simp [selectedDescriptor]
      simp only [hd, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
        at h0 h1 h2 h3 hr
      have h := physicalReader_absent (memory bits) regs 0 0 0 0 hs h0 h1 h2 h3 (Nat.zero_le _)
      have hw : (readStore bits target).readWord? (regs 8192) (regs 8193) = none := by
        simp [readStore, logicalWord, logicalWords_inactive bits target (regs 8192) hp,
          normalizedSegmentWord]
      simpa only [hw, logicalPacket, logicalLength, hr, Nat.not_lt_zero, if_false] using h
  · have h := physicalReader_outside (memory bits) regs (Nat.le_of_not_gt hs)
    have hp : ¬activeSegment (regs 8192) := by unfold activeSegment; omega
    have hw : (readStore bits target).readWord? (regs 8192) (regs 8193) = none := by
      simp [readStore, logicalWord, logicalWords_inactive bits target (regs 8192) hp,
        normalizedSegmentWord]
    simpa only [hw, logicalPacket, logicalLength, readerReceipts, if_neg hs] using h

/-- Arbitrary proof metadata can consume the reader once its two actual input
fields agree. The source still receives only numerical memory and registers. -/
def controllerModel (bits : List Bool) (target : Bool) (metadata : Registers) :
    Controller.ControllerModel :=
  ⟨metadata, readStore bits target, readerReceipts bits target⟩

theorem readerSimulation (bits : List Bool) (target : Bool) (metadata : Registers)
    (ht : metadata 3 = target.toNat) (hw : metadata 22 = Experiment.width bits.length) :
    Controller.ReaderSimulation (controllerModel bits target metadata)
      (memory bits) Experiment.physicalReader := by
  intro regs hm
  apply physicalReader_correct bits target regs
  exact ⟨(hm 3 (by decide)).trans ht, (hm 22 (by decide)).trans hw⟩

end RMQ.PackedBitvector.Allocation

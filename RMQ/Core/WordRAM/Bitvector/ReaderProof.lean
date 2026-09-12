import RMQ.Core.WordRAM.Bitvector.ReaderGeometry
import RMQ.Core.WordRAM.Bitvector.SegmentMap
import RMQ.Core.WordRAM.Bitvector.DescriptorReader

/-! # Canonical generic reader: charged loads recover the exact logical word

The canonical store hypotheses below are proved from the allocation. The
numeric source proof remains parameterized by actual replies and therefore
also describes faults without inventing a successful descriptor prefix.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect Experiment
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

theorem canonical_descriptor_reads (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) (hs : regs 8192 < 23)
    (field : Nat) (hf : field < 4) :
    (memory bits)[numericDescriptorAddress regs + field]? =
      some ((bankDescriptor bits target (regs 8192))[field]?.getD 0) := by
  have h := memory_descriptor_present bits target (regs 8192) field hs hf
  simpa only [numericDescriptorAddress, hm.1] using h

theorem canonical_expected_receipts (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) (hs : regs 8192 < 23) :
    genericReaderReceipts bits target (memory bits) (regs 8192) (regs 8193) =
      let desc := bankDescriptor bits target (regs 8192)
      let count := desc[3]?.getD 0
      if regs 8193 < count then numericDescriptorReceipts (memory bits) regs ++
        spanAttemptReceipts (regs 22) (desc[0]?.getD 0 + regs 8193 * (desc[2]?.getD 0))
          (min (desc[2]?.getD 0) (desc[1]?.getD 0 - regs 8193 * (desc[2]?.getD 0))) (memory bits)
      else numericDescriptorReceipts (memory bits) regs := by
  have h0 := canonical_descriptor_reads bits target regs hm hs 0 (by decide)
  have h1 := canonical_descriptor_reads bits target regs hm hs 1 (by decide)
  have h2 := canonical_descriptor_reads bits target regs hm hs 2 (by decide)
  have h3 := canonical_descriptor_reads bits target regs hm hs 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [numericDescriptorAddress, hm.1] at h0 h1 h2 h3
  simp only [genericReaderReceipts, if_pos hs, h0, h1, h2, h3,
    Option.getD_some, numericDescriptorReceipts, numericDescriptorAddress, hm.1, hm.2]

theorem canonicalGenericReaderCorrect_holds : CanonicalGenericReaderCorrect := by
  intro bits target regs hm
  change GenericReaderMetadata bits target regs at hm
  dsimp only
  by_cases hs : regs 8192 < 23
  · have h0 := canonical_descriptor_reads bits target regs hm hs 0 (by decide)
    have h1 := canonical_descriptor_reads bits target regs hm hs 1 (by decide)
    have h2 := canonical_descriptor_reads bits target regs hm hs 2 (by decide)
    have h3 := canonical_descriptor_reads bits target regs hm hs 3 (by decide)
    simp only [Nat.add_zero] at h0
    have hr := canonical_expected_receipts bits target regs hm hs
    by_cases hp : presentSegment (regs 8192)
    · let words := selectedWords bits target (regs 8192)
      let base := 207 * width bits.length +
        componentOffset (allSegments bits) (componentIndex target (regs 8192))
      let stride := firstLength words
      have hd := bankDescriptor_present bits target (regs 8192) hp
      change bankDescriptor bits target (regs 8192) = descriptor base words at hd
      simp only [hd, descriptor, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at h0 h1 h2 h3 hr
      change (memory bits)[numericDescriptorAddress regs + 2]? = some stride at h2
      have hmember := selectedWords_mem bits target (regs 8192) hp
      have hregular := allSegments_regular bits words hmember
      have h := physicalReader_regular_words (memory bits) regs target words base hm.1 hs
        hregular h0 h1 h2 h3 (by
          intro hi
          have hdecode := decode_component_word bits (componentIndex target (regs 8192)) (regs 8193)
            (componentIndex_lt target (regs 8192) hp)
            (by simpa only [words, selectedWords_present bits target (regs 8192) hp] using hi)
          simpa only [words, selectedWords_present bits target (regs 8192) hp, base, hm.2]
            using hdecode)
      have hw : normalizedSegmentWord target (regs 8192) words[regs 8193]? =
          genericLogicalWord bits target (regs 8192) (regs 8193) := by
        rw [genericLogicalWord_selected]
        rfl
      simpa only [hw, hr] using h
    · have hd := bankDescriptor_absent bits target (regs 8192) hs hp
      simp only [hd, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at h0 h1 h2 h3 hr
      have h := physicalReader_absent (memory bits) regs 0 0 0 0 hs h0 h1 h2 h3 (Nat.zero_le _)
      have hw : genericLogicalWord bits target (regs 8192) (regs 8193) = none := by
        rw [genericLogicalWord_selected]
        simp [selectedWords, hp]
      simpa only [hw, readerPacket, readerLength, Option.map_none, Option.getD_none,
        hr, Nat.not_lt_zero, if_false] using h
  · have h := physicalReader_outside (memory bits) regs (Nat.le_of_not_gt hs)
    have hp : ¬presentSegment (regs 8192) := by unfold presentSegment; omega
    have hw : genericLogicalWord bits target (regs 8192) (regs 8193) = none := by
      rw [genericLogicalWord_selected]
      simp [selectedWords, hp]
    simpa only [hw, readerPacket, readerLength, Option.map_none, Option.getD_none,
      genericReaderReceipts, if_neg hs] using h

end RMQ.PackedBitvector

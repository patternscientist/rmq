import RMQ.Core.WordRAM.Bitvector.AccessProof

namespace RMQ.PackedBitvector.AccessConsumer

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured AccessProof

theorem actual_access_required (bits : List Bool) (regs : Registers)
    (hm : AccessMetadata bits regs)
    (fit : (⟨regs, .running⟩ : Data).Fits (Experiment.width bits.length))
    (readerSafe : Controller.ReaderSafe
      (Allocation.controllerModel bits false regs) (Experiment.width bits.length)
      (Allocation.memory bits) Experiment.physicalReader) :
    let actual := accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 705 = ((bits[regs 704]?).map fun bit => bit.toNat + 1).getD 0 ∧
    actual.reads = (if regs 704 < bits.length then
      Allocation.readerReceipts bits false 19 (regs 704 / SuccinctRank.machineWordBits bits.length)
      else []) ∧
    (∀ r, r < 705 ∨ (710 ≤ r ∧ r < 8192) ∨ 8271 ≤ r →
      actual.final.regs r = regs r) ∧
    accessQuery.Safe (Allocation.memory bits) (Experiment.width bits.length) ⟨regs, .running⟩ := by
  have h := accessQuery_source bits regs hm
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, accessQuery_safe bits regs hm fit readerSafe⟩

#print axioms actual_access_required

end RMQ.PackedBitvector.AccessConsumer

import RMQ.Core.WordRAM.Bitvector.ChargedSetup

namespace RMQ.PackedBitvector.ChargedSetupConsumer

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured ChargedSetup

example (bits : List Bool) (regs : Registers) :
    Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨setupMetadata bits regs, .running⟩, setupReceipts bits⟩ :=
  setup_source bits regs

example (bits : List Bool) (regs : Registers) :
    Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨targetMetadata bits regs, .running⟩, targetReceipts bits regs⟩ :=
  targetSetup_source bits regs

theorem charged_setup_required (bits : List Bool) (width : Nat) (regs : Registers)
    (hw : 32 ≤ width) (memoryFit : MemoryWordsFit (Allocation.memory bits) width)
    (fit : (⟨regs, .running⟩ : Data).Fits width) :
    (Block.seq Experiment.setup Experiment.targetSetup).eval
      (Allocation.memory bits) ⟨regs, .running⟩ =
      ⟨⟨targetMetadata bits (setupMetadata bits regs), .running⟩,
        setupReceipts bits ++ targetReceipts bits (setupMetadata bits regs)⟩ ∧
    Experiment.setup.Safe (Allocation.memory bits) width ⟨regs, .running⟩ ∧
    Experiment.targetSetup.Safe (Allocation.memory bits) width ⟨regs, .running⟩ ∧
    (Block.seq Experiment.setup Experiment.targetSetup).Safe
      (Allocation.memory bits) width ⟨regs, .running⟩ :=
  ⟨setup_then_target_source bits regs, setup_safe bits width regs hw memoryFit fit,
    targetSetup_safe bits width regs hw memoryFit fit,
    setup_then_target_safe bits width regs hw memoryFit fit⟩

example (bits : List Bool) (regs : Registers) :
    (Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 3 = regs 3 ∧
    (Experiment.setup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 352 = regs 352 ∧
    (Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 512 = regs 512 ∧
    (Experiment.targetSetup.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 704 = regs 704 :=
  ⟨setup_frame bits regs 3 (by decide) (by decide),
    setup_frame bits regs 352 (by decide) (by decide),
    targetSetup_frame bits regs 512 (by decide) (by decide),
    targetSetup_frame bits regs 704 (by decide) (by decide)⟩

#print axioms charged_setup_required

end RMQ.PackedBitvector.ChargedSetupConsumer

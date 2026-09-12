import RMQ.Core.WordRAM.Bitvector.Source
import RMQ.Core.WordRAM.Bitvector.Space
import RMQ.Core.WordRAM.Bitvector.NumericReader
import RMQ.Core.WordRAM.Packed.SelectProof
import RMQ.Core.WordRAM.Packed.Scratch

/-! # The actual programs use only the counted finite register bank -/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

private theorem setup_writes_registerBank :
    Experiment.setup.WritesOnly (fun r => r < registerCount) := by
  simp [Experiment.setup, List.range_succ, Block.sequence, Block.WritesOnly, Action.destination, registerCount]

private theorem targetSetup_writes_registerBank :
    Experiment.targetSetup.WritesOnly (fun r => r < registerCount) := by
  simp [Experiment.targetSetup, Block.sequence, Block.WritesOnly, Action.destination, registerCount]

private theorem physicalReader_writes_registerBank :
    Experiment.physicalReader.WritesOnly (fun r => r < registerCount) :=
  Block.WritesOnly.mono _ physicalReader_writes (by intro r h; exact h.2)

private theorem accessQuery_writes_registerBank :
    accessQuery.WritesOnly (fun r => r < registerCount) := by
  simpa [accessQuery, Block.sequence, Block.WritesOnly, Action.destination, registerCount]
    using physicalReader_writes_registerBank

private theorem rankQuery_writes_registerBank :
    rankQuery.WritesOnly (fun r => r < registerCount) := by
  have hr : (rankBlock Experiment.physicalReader).WritesOnly (fun r => r < registerCount) :=
    Block.WritesOnly.mono _ (rankBlock_writes _ physicalReader_writes)
      (by intro r h; unfold RankWrites at h; unfold registerCount; omega)
  simpa [rankQuery, rankPrepare, Block.sequence, Block.WritesOnly, Action.destination, registerCount]
    using hr

theorem source_writes_registerBank (operation : Operation) :
    (source operation).WritesOnly (fun r => r < registerCount) := by
  have hs : (selectCloseBlock Experiment.physicalReader).WritesOnly (fun r => r < registerCount) :=
    Block.WritesOnly.mono _ (selectCloseBlock_writes _ physicalReader_writes)
      (by intro r h; unfold SelectWrites at h; unfold registerCount; omega)
  cases operation
  · exact ⟨setup_writes_registerBank, accessQuery_writes_registerBank⟩
  · exact ⟨setup_writes_registerBank, rankQuery_writes_registerBank⟩
  · exact ⟨setup_writes_registerBank, targetSetup_writes_registerBank, hs⟩

theorem program_writes_registerBank (operation : Operation) :
    ∀ instruction ∈ program operation,
      instruction.WritesOnly (fun r => r < registerCount) := by
  intro instruction hi
  rcases List.mem_append.mp hi with hi | hi
  · exact (source operation).compile_writesOnly _ (source_writes_registerBank operation) 0 instruction hi
  · simp only [List.mem_singleton] at hi
    subst instruction
    trivial

/-- Every fuel prefix preserves the zero contents outside the exact counted
bank. Arbitrary memory includes both successful execution and faulty loads. -/
theorem run_finite_registers (memory : Memory) (operation : Operation) (target : Bool)
    (argument fuel r : Nat) (hr : registerCount ≤ r) :
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 := by
  rw [run_frame memory (program operation) fuel (initial operation target argument)
    (fun r => r < registerCount) (program_writes_registerBank operation) r (by omega)]
  have h3 : r ≠ 3 := by unfold registerCount at hr; omega
  have ha : r ≠ argumentRegister operation := by
    cases operation <;> simp only [argumentRegister] <;> unfold registerCount at hr <;> omega
  simp [initial, h3, ha]

theorem execute_finite_registers (bits : List Bool) (operation : Operation) (target : Bool)
    (argument r : Nat) (hr : registerCount ≤ r) :
    (execute bits operation target argument).final.regs r = 0 :=
  run_finite_registers (Allocation.memory bits) operation target argument _ r hr

/-- The same universal support predicate used by the positive frame theorem. -/
def PreservesScratchBank (programs : Operation → Program) : Prop :=
  ∀ memory operation target argument fuel r, registerCount ≤ r →
    (run memory (programs operation) fuel (initial operation target argument)).final.regs r = 0

theorem program_preservesScratchBank : PreservesScratchBank program := run_finite_registers

theorem outOfBankWrite_rejected :
    ¬ PreservesScratchBank (fun _ => [.constant registerCount 1]) := by
  intro h
  have bad := h [] .access false 0 1 registerCount (Nat.le_refl _)
  simp [run, step, SuccinctFinal.PackedWordRAM.execute, initial, registerCount,
    State.writeNext, Registers.write] at bad

end RMQ.PackedBitvector

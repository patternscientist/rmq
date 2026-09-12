import RMQ.Core.WordRAM.Bitvector.SelectExecution
import RMQ.Core.WordRAM.Bitvector.AccessProof

/-! # Charged setup and actual compiled access to the original input -/

namespace RMQ.PackedBitvector

open SuccinctRank
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

theorem loadedMetadata_access_geometry (bits : List Bool) (argument : Nat) :
    AccessProof.AccessMetadata bits (loadedMetadata bits .access false argument) := by
  refine ⟨loadedMetadata_target bits .access false argument,
    loadedMetadata_size bits .access false argument, ?_,
    loadedMetadata_width bits .access false argument⟩
  change (jacobsonRankData bits).wordSize = machineWordBits bits.length
  exact jacobson_wordSize_eq bits

def accessExecutionReceipts (bits : List Bool) (argument : Nat) : List Receipt :=
  ChargedSetup.setupReceipts bits ++ AccessProof.accessReceipts bits argument

theorem access_source (bits : List Bool) (argument : Nat) :
    let actual := (source .access).eval (Allocation.memory bits)
      ⟨(initial .access false argument).regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 705 = AccessProof.accessPacket bits argument ∧
    actual.reads = accessExecutionReceipts bits argument := by
  have hs := ChargedSetup.setup_source bits (initial .access false argument).regs
  have ha := AccessProof.accessQuery_source bits (loadedMetadata bits .access false argument)
    (loadedMetadata_access_geometry bits argument)
  have hi : loadedMetadata bits .access false argument 704 = argument :=
    loadedMetadata_argument bits .access false argument
  simp only [hi] at ha
  simp only [source, operationBody, Block.eval_seq, hs, Evaluation.bind]
  exact ⟨ha.1, ha.2.1, congrArg (ChargedSetup.setupReceipts bits ++ ·) ha.2.2.1⟩

theorem execute_access (bits : List Bool) (argument : Nat) :
    let actual := execute bits .access false argument
    let packet := AccessProof.accessPacket bits argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 705 = packet ∧ actual.reads = accessExecutionReceipts bits argument ∧
    actual.steps ≤ (source .access).size + 1 := by
  have hs := access_source bits argument
  exact execute_source_result bits .access 705 rfl false argument _ _ hs.1 hs.2.1 hs.2.2

end RMQ.PackedBitvector

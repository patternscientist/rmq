import RMQ.Core.WordRAM.Bitvector.ChargedSetup
import RMQ.Core.WordRAM.Bitvector.CompleteReader
import RMQ.Core.WordRAM.Bitvector.GenericSelectProof

/-! # The actual loaded scalars instantiate the generic controller model -/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def loadedMetadata (bits : List Bool) (operation : Operation) (target : Bool)
    (argument : Nat) : Registers :=
  let loaded := ChargedSetup.setupMetadata bits (initial operation target argument).regs
  match operation with
  | .select => ChargedSetup.targetMetadata bits loaded
  | _ => loaded

theorem loadedMetadata_target (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    loadedMetadata bits operation target argument 3 = target.toNat := by
  cases operation <;> cases target <;> rfl

theorem loadedMetadata_width (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    loadedMetadata bits operation target argument 22 = Experiment.width bits.length := by
  cases operation <;> cases target <;> rfl

theorem loadedMetadata_argument (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    loadedMetadata bits operation target argument (argumentRegister operation) = argument := by
  cases operation <;> cases target <;> rfl

theorem loadedMetadata_size (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    loadedMetadata bits operation target argument 18 = bits.length := by
  cases operation <;> cases target <;> rfl

theorem loadedMetadata_chunk (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) :
    loadedMetadata bits operation target argument 34 =
      SuccinctClose.bpFringeChunkBits (2*bits.length) := by
  cases operation <;> cases target <;> rfl

theorem loadedMetadata_rank_geometry (bits : List Bool) (target : Bool) (argument : Nat) :
    loadedMetadata bits .rank target argument 19 = (jacobsonRankData bits).wordSize ∧
    loadedMetadata bits .rank target argument 20 = (jacobsonRankData bits).blocksPerSuper := by
  cases target <;> exact ⟨rfl, rfl⟩

theorem loadedMetadata_select_geometry (bits : List Bool) (target : Bool) (argument : Nat) :
    let regs := loadedMetadata bits .select target argument
    let d := sparseExceptionSelectData bits target
    regs 16 = occurrenceCount bits target ∧
    regs 25 = d.superStride ∧ regs 26 = d.localStride ∧ regs 27 = d.localSlotsPerSuper ∧
    regs 28 = d.longFlagBits.length ∧ regs 29 = d.sparseDirectory.flagBits.length ∧
    regs 30 = d.longFlagRankData.wordSize ∧ regs 31 = d.sparseDirectory.rankData.wordSize ∧
    regs 32 = d.wordSize := by
  cases target <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def loadedModel (bits : List Bool) (operation : Operation) (target : Bool)
    (argument : Nat) : Controller.ControllerModel :=
  Allocation.controllerModel bits target (loadedMetadata bits operation target argument)

theorem loadedModel_reader (bits : List Bool) (operation : Operation) (target : Bool)
    (argument : Nat) :
    Controller.ReaderSimulation (loadedModel bits operation target argument)
      (Allocation.memory bits) Experiment.physicalReader :=
  Allocation.readerSimulation bits target _
    (loadedMetadata_target bits operation target argument)
    (loadedMetadata_width bits operation target argument)

theorem selectReference_value (bits : List Bool) (target : Bool) (argument : Nat) :
    (Controller.selectReference (Allocation.readStore bits target)
      (loadedMetadata bits .select target argument) argument).value =
        Succinct.select target bits argument := by
  have hg := loadedMetadata_select_geometry bits target argument
  dsimp only at hg
  simp only [Controller.selectReference, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1,
    hg.2.2.2.2.1, hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1,
    hg.2.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.2, loadedMetadata_chunk]
  exact Allocation.readStore_select_value bits target argument

end RMQ.PackedBitvector

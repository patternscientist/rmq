import RMQ.Core.WordRAM.Bitvector.Metadata

/-! # Actual setup, select controller and shared primitive run

Every receipt below belongs to the compiled program's execution over the same
complete allocation. No proof-side store is supplied to the program.
-/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def selectExecutionReceipts (bits : List Bool) (target : Bool) (argument : Nat) : List Receipt :=
  ChargedSetup.setupReceipts bits ++
    ChargedSetup.targetReceipts bits
      (ChargedSetup.setupMetadata bits (initial .select target argument).regs) ++
    Controller.traceReads (Allocation.readerReceipts bits target)
      (Controller.selectReference (Allocation.readStore bits target)
        (loadedMetadata bits .select target argument) argument).trace

theorem select_source (bits : List Bool) (target : Bool) (argument : Nat) :
    let actual := (source .select).eval (Allocation.memory bits)
      ⟨(initial .select target argument).regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 513 = optionNatPacket (Succinct.select target bits argument) ∧
    actual.reads = selectExecutionReceipts bits target argument := by
  let regs := loadedMetadata bits .select target argument
  have hm : Controller.MetadataMatches (loadedModel bits .select target argument) regs :=
    fun _ _ => rfl
  have h := Controller.selectCloseBlock_source (loadedModel bits .select target argument)
    (Allocation.memory bits) Experiment.physicalReader
    (loadedModel_reader bits .select target argument) physicalReader_writes regs hm
  have harg : regs 512 = argument := loadedMetadata_argument bits .select target argument
  simp only [loadedModel, Allocation.controllerModel, harg, selectReference_value] at h
  generalize he : (selectCloseBlock Experiment.physicalReader).eval
    (Allocation.memory bits) ⟨regs, .running⟩ = selected at h
  rcases selected with ⟨⟨final, status⟩, receipts⟩
  dsimp only at h
  obtain ⟨hstatus, hvalue, hreads, _⟩ := h
  subst status
  have hs := ChargedSetup.setup_source bits (initial .select target argument).regs
  have ht := ChargedSetup.targetSetup_source bits
    (ChargedSetup.setupMetadata bits (initial .select target argument).regs)
  dsimp only [regs, loadedMetadata] at he
  simp only [source, operationBody, Block.eval_seq, hs, ht, Evaluation.bind, he]
  exact ⟨True.intro, hvalue, by
    simpa only [selectExecutionReceipts, Controller.logicalTraceReads, List.append_assoc]
      using congrArg (fun rs => ChargedSetup.setupReceipts bits ++
        ChargedSetup.targetReceipts bits
          (ChargedSetup.setupMetadata bits (initial .select target argument).regs) ++ rs) hreads⟩

private theorem data_eq_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by
  cases s with
  | mk regs status => cases hs; rfl

/-- Direct compiler consequence, including the numeric output register used by
the public packet interface. No writes/frame premise is needed for this join. -/
theorem compile_source_result (block : Block) (output : Nat) (memory : Memory)
    (regs : Registers) (value : Nat) (receipts : List Receipt)
    (hs : (block.eval memory ⟨regs, .running⟩).final.status = .running)
    (hv : (block.eval memory ⟨regs, .running⟩).final.regs output = value)
    (ht : (block.eval memory ⟨regs, .running⟩).reads = receipts) :
    let actual := run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
      ⟨regs, 0, .running⟩
    actual.result = some value ∧ actual.final.status = .halted value ∧
    actual.final.regs output = value ∧ actual.reads = receipts ∧ actual.steps ≤ block.size + 1 := by
  have hm := block.compile_with_halt memory output ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hm
  have hdata := hm.1
  rw [data_eq_running _ hs] at hdata
  have hregs := congrArg Data.regs hdata
  have hstatus := congrArg Data.status hdata
  change (run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
    ⟨regs, 0, .running⟩).final.regs = (block.eval memory ⟨regs, .running⟩).final.regs at hregs
  change (run memory (block.compileAt 0 ++ [.halt output]) (block.size + 1)
    ⟨regs, 0, .running⟩).final.status =
      .halted ((block.eval memory ⟨regs, .running⟩).final.regs output) at hstatus
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs, hv] using hm.2.1
  · simpa only [hv] using hstatus
  · exact (congrFun hregs output).trans hv
  · exact hm.2.2.1.trans ht
  · simpa only [List.length_append, Block.compile_length, List.length_cons,
      List.length_nil] using hm.2.2.2

/-- Keep the operation abstract during the compiler conversion. This avoids
normalizing a concrete fixed program while checking the state representation. -/
theorem execute_source_result (bits : List Bool) (operation : Operation)
    (output : Nat) (houtput : resultRegister operation = output)
    (target : Bool) (argument value : Nat) (receipts : List Receipt)
    (hs : ((source operation).eval (Allocation.memory bits)
      ⟨(initial operation target argument).regs, .running⟩).final.status = .running)
    (hv : ((source operation).eval (Allocation.memory bits)
      ⟨(initial operation target argument).regs, .running⟩).final.regs
        output = value)
    (ht : ((source operation).eval (Allocation.memory bits)
      ⟨(initial operation target argument).regs, .running⟩).reads = receipts) :
    let actual := execute bits operation target argument
    actual.result = some value ∧ actual.final.status = .halted value ∧
    actual.final.regs output = value ∧ actual.reads = receipts ∧
    actual.steps ≤ (source operation).size + 1 := by
  subst output
  exact compile_source_result (source operation) (resultRegister operation) (Allocation.memory bits)
    (initial operation target argument).regs value receipts hs hv ht

theorem execute_select (bits : List Bool) (target : Bool) (argument : Nat) :
    let actual := execute bits .select target argument
    let packet := optionNatPacket (Succinct.select target bits argument)
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 513 = packet ∧
    actual.reads = selectExecutionReceipts bits target argument ∧
    actual.steps ≤ (source .select).size + 1 := by
  have hs := select_source bits target argument
  exact execute_source_result bits .select 513 rfl target argument _ _ hs.1 hs.2.1 hs.2.2

end RMQ.PackedBitvector

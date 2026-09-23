import RMQ.Core.WordRAM.Bitvector.GenericSelectSafety
open RMQ RMQ.PackedBitvector RMQ.PackedBitvector.Controller
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1SelectSafetyConsumer
variable (model : ControllerModel) (limits : SafetyLimits)
  (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
  (readerSafe : Controller.ReaderSafe model limits.width memory reader)
  (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
  (s : Data) (fit : s.Fits limits.width) (hm : Controller.MetadataMatches model s.regs)
example : (selectCloseBlock reader).Safe memory limits.width s :=
  Controller.selectCloseBlock_safe model limits bounds memory reader readerSafe readerCorrect readerWrites s fit hm
example (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    ((selectCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 513 < 2 ^ limits.width :=
  Controller.selectCloseBlock_output_bound model limits bounds memory reader readerSafe readerCorrect readerWrites regs fr mr
example (fields : reader.FieldsFit limits.width) (budget : 3667 + 82 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    RankExecutionSafety memory limits.width ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩ :=
  Controller.selectCloseBlock_execution_safe model limits bounds memory reader readerSafe readerCorrect readerWrites fields budget regs fr mr
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader) :
    (selectCloseBlock Experiment.physicalReader).Safe memory limits.width s :=
  physicalSelect_safe model limits bounds memory rs rc s fit hm
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    let program := (selectCloseBlock Experiment.physicalReader).compileAt 0 ++ [.halt 513]
    let actual := run memory program 9981 ⟨regs, 0, .running⟩
    (∀ instruction ∈ program, instruction.Fits limits.width) ∧
    actual.final.Fits limits.width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe limits.width t.before t.instruction ∧ t.after.Fits limits.width) ∧
    (∀ index, index ≤ 9981 → (run memory program index ⟨regs, 0, .running⟩).final.Fits limits.width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt), actual.transitions[index]? = some t →
      t.receipt = some receipt → receipt.address < 2 ^ limits.width ∧
      receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ limits.width)) :=
  physicalSelect_execution_safe_expectedType model limits bounds memory rs rc regs fr mr
example : ¬ ReaderSimulation model memory .skip := readerSimulation_rejects_skip model memory
example : Experiment.physicalReader.FieldsFit limits.width := physicalReader_fieldsFit limits
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    ((selectCloseBlock Experiment.physicalReader).eval memory ⟨regs, .running⟩).final.regs 513 <
      2 ^ limits.width :=
  Controller.selectCloseBlock_output_bound model limits bounds memory Experiment.physicalReader
    rs rc physicalReader_writes regs fr mr
#print axioms Controller.selectCloseBlock_safe
#print axioms Controller.selectCloseBlock_output_bound
#print axioms Controller.selectCloseBlock_execution_safe
#print axioms physicalReader_fieldsFit
#print axioms physicalSelect_safe
#print axioms physicalSelect_execution_safe
#print axioms physicalSelect_execution_safe_expectedType
#print axioms readerSimulation_rejects_skip
end BV1SelectSafetyConsumer

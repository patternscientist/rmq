import RMQ.Core.WordRAM.Bitvector.GenericSelectProof
import RMQ.Core.WordRAM.Bitvector.GenericRankSafety
import RMQ.Core.WordRAM.Bitvector.CanonicalMemoryBounds

/-! Independent expected-type consumers for the generic controller interface.
The expected propositions spell out the model objects and read projection.
-/

namespace RMQ.PackedBitvector.ControllerChecks

open SuccinctFinal SuccinctFinal.PackedWordRAM Structured PackedCellProbe
open Controller

example (snapshot : Registers) (store : WordRAM.ReadStore)
    (receipts : Nat → Nat → List Receipt) (memory : Memory) (reader : Block)
    (h : ReaderSimulation ⟨snapshot, store, receipts⟩ memory reader) :
    ∀ regs, (∀ r < 190, regs r = snapshot r) →
      let actual := reader.eval memory ⟨regs, .running⟩
      let expected := store.readWord? (regs 8192) (regs 8193)
      actual.final.status = .running ∧
      actual.final.regs 8194 = logicalPacket expected ∧
      actual.final.regs 8195 = logicalLength expected ∧
      actual.reads = receipts (regs 8192) (regs 8193) ∧
      (∀ r, r < 8194 ∨ 8271 ≤ r → actual.final.regs r = regs r) := h

example (snapshot : Registers) (store : WordRAM.ReadStore)
    (receipts : Nat → Nat → List Receipt) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation ⟨snapshot, store, receipts⟩ memory reader)
    (hwrites : ReaderWrites reader) (target : Bool) (regs : Registers)
    (hm : ∀ r < 190, regs r = snapshot r)
    (htarget : regs 359 = if target then 1 else 0) :
    let actual := (rankBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedRankRead (regs 356) (regs 357) (regs 358) 21 (snapshot 34) target store
      (regs 353) (regs 354) (regs 355) (regs 352)
    actual.final.status = .running ∧ actual.final.regs 360 = expected.value ∧
      actual.reads = expected.trace.flatMap (fun event => match event with
        | .readWord segment index _ => receipts segment index
        | _ => []) ∧ (∀ event ∈ expected.trace, event.isReadWord) :=
  Controller.rankBlock_source_expectedType snapshot store receipts memory reader
    hreader hwrites target regs hm htarget

example (snapshot : Registers) (store : WordRAM.ReadStore)
    (receipts : Nat → Nat → List Receipt) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation ⟨snapshot, store, receipts⟩ memory reader)
    (hwrites : ReaderWrites reader) (regs : Registers)
    (hm : ∀ r < 190, regs r = snapshot r) :
    let actual := (selectCloseBlock reader).eval memory ⟨regs, .running⟩
    let expected := packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout 21 22 store
      (snapshot 34) false (snapshot 16) (snapshot 25) (snapshot 32) (snapshot 27) (snapshot 26)
      (snapshot 28) (snapshot 30) 1 (snapshot 29) (snapshot 31) 1 (snapshot 26) (regs 512)
    actual.final.status = .running ∧ actual.final.regs 513 = optionNatPacket expected.value ∧
      actual.reads = expected.trace.flatMap (fun event => match event with
        | .readWord segment index _ => receipts segment index
        | _ => []) ∧ (∀ event ∈ expected.trace, event.isReadWord) :=
  Controller.selectCloseBlock_source_expectedType snapshot store receipts memory reader
    hreader hwrites regs hm

example (model : ControllerModel) (memory : Memory) (reader : Block)
    (hreader : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : Controller.MetadataMatches model regs) :
    let expected := packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout 21 22 model.store
      (model.metadata 34) false (model.metadata 16) (model.metadata 25) (model.metadata 32)
      (model.metadata 27) (model.metadata 26) (model.metadata 28) (model.metadata 30) 1
      (model.metadata 29) (model.metadata 31) 1 (model.metadata 26) (regs 512)
    let actual := run memory ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some (optionNatPacket expected.value) ∧
      actual.final.status = .halted (optionNatPacket expected.value) ∧
      actual.reads = expected.trace.flatMap (fun event => match event with
        | .readWord segment index _ => model.receipts segment index
        | _ => []) ∧
      actual.steps ≤ 3667 + 82 * reader.size ∧
      (∀ r, ¬ SelectWrites r → actual.final.regs r = regs r) ∧
      (∀ event ∈ expected.trace, event.isReadWord) :=
  Controller.selectCloseBlock_machine model memory reader hreader hwrites regs hm

example (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (hsafe : ∀ s, s.Fits limits.width → (∀ r < 190, s.regs r = model.metadata r) →
      reader.Safe memory limits.width s)
    (hsim : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : ∀ r < 190, regs r = model.metadata r) (hw : 0 < regs 354) (hb : 0 < regs 355)
    (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    (rankBlock reader).Safe memory limits.width ⟨regs, .running⟩ ∧
      ((rankBlock reader).eval memory ⟨regs, .running⟩).final.regs 360 ≤ limits.envelope :=
  Controller.rankBlock_safe_bound model limits bounds memory reader hsafe hsim hwrites
    regs fit hm hw hb length rawLength

example (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
    (hsafe : ∀ s, s.Fits limits.width → (∀ r < 190, s.regs r = model.metadata r) →
      reader.Safe memory limits.width s)
    (hsim : ReaderSimulation model memory reader) (hwrites : ReaderWrites reader)
    (readerFields : reader.FieldsFit limits.width)
    (budget : 552 + 11 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits limits.width)
    (hm : ∀ r < 190, regs r = model.metadata r) (hw : 0 < regs 354) (hb : 0 < regs 355)
    (length : regs 353 ≤ limits.envelope)
    (rawLength : ∀ index, logicalLength (model.store.readWord? (regs 358) index) ≤ limits.rawWidth) :
    let program := (rankBlock reader).compileAt 0 ++ [.halt 360]
    let actual := run memory program (552 + 11 * reader.size) ⟨regs, 0, .running⟩
    (∀ instruction ∈ program, instruction.Fits limits.width) ∧
    actual.final.Fits limits.width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe limits.width t.before t.instruction ∧ t.after.Fits limits.width) ∧
    (∀ index, index ≤ 552 + 11 * reader.size →
      (run memory program index ⟨regs, 0, .running⟩).final.Fits limits.width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ limits.width ∧ receipt.reply = memory[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ limits.width)) :=
  Controller.rankBlock_execution_safe model limits bounds memory reader hsafe hsim hwrites
    readerFields budget regs fit hm hw hb length rawLength

example (bits : List Bool) :
    ∀ value ∈ Allocation.memory bits, value < 2 ^ Experiment.width bits.length :=
  canonical_memoryWordsFit bits

example (bits : List Bool) (target : Bool) (regs : Registers)
    (htarget : regs 3 = target.toNat) (hwidth : regs 22 = Experiment.width bits.length) :
    (regs 8192 < 23 → 23 + regs 3 * 92 + regs 8192 * 4 + 3 <
      2 ^ Experiment.width bits.length) ∧
    (regs 8192 < 23 → ∀ bitBase bitLength stride count,
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4]? = some bitBase →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 1]? = some bitLength →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 2]? = some stride →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 3]? = some count →
      regs 8193 < count →
      bitBase + regs 8193 * stride < 2 ^ Experiment.width bits.length ∧
      stride < Experiment.width bits.length) :=
  canonical_numericReaderGeometry bits target regs ⟨htarget, hwidth⟩

example (bits : List Bool) : ∀ value ∈ Allocation.scalarHeader bits,
    value ≤ 2 ^ (9 + 2 * SuccinctRank.machineWordBits bits.length) :=
  canonical_scalarHeader_bound bits

example (target : Bool) :
    (Allocation.logicalWords [] target 19).size = 1 ∧
    (Allocation.logicalWords [] target 19)[0]? = some [] :=
  canonical_empty_raw_sentinel target

#print axioms canonical_allSegments_count
#print axioms canonical_body_length
#print axioms canonicalAddressBound_lt_capacity
#print axioms canonical_scalarHeader_bound
#print axioms canonical_memoryWordsFit
#print axioms canonical_numericReaderGeometry
#print axioms canonical_empty_raw_sentinel

#print axioms Controller.readerSimulation_rejects_skip
#print axioms Controller.rankWordBlock_source
#print axioms Controller.rankBlock_source
#print axioms Controller.rankBlock_machine
#print axioms Controller.rankBlock_source_expectedType
#print axioms Controller.selectReference_normalForm
#print axioms Controller.selectCloseBlock_source
#print axioms Controller.selectCloseBlock_machine
#print axioms Controller.selectCloseBlock_source_expectedType
#print axioms Controller.SafetyLimits.chunk_slot_fit
#print axioms Controller.rankWordBlock_safe_invariant
#print axioms Controller.rankBlock_safe_bound
#print axioms Controller.rankLongBlock_safe_bound
#print axioms Controller.rankSparseBlock_safe_bound
#print axioms Controller.rankBlock_execution_safe
#print axioms Controller.rankBlock_execution_safe_expectedType

end RMQ.PackedBitvector.ControllerChecks

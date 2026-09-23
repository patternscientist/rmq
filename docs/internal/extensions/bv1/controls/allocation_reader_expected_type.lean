import RMQ.Core.WordRAM.Bitvector.Space
import RMQ.Core.WordRAM.Bitvector.Metadata
import RMQ.Core.WordRAM.Bitvector.CanonicalStoreBounds

open RMQ RMQ.PackedBitvector RMQ.SuccinctSpace RMQ.SuccinctRank
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured

example (bits : List Bool) :
    ((Allocation.memory bits).length +
      ((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length +
      (8271 + 3)) * Experiment.width bits.length ≤
        bits.length + completeRho bits.length := complete_capacity bits

example : LittleOLinear completeRho := completeRho_littleO

example (n : Nat) : Nat.log2 (n+2)+1 ≤ Experiment.width n ∧
    Experiment.width n ≤ 48*(Nat.log2 (n+2)+1) :=
  ⟨log_le_width n, width_le_log n⟩

example (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : segment < 23 ∧ segment ≠ 20) :
    Allocation.bankDescriptor bits target segment =
      Experiment.descriptor (207 * Experiment.width bits.length +
        Experiment.componentOffset (Allocation.allSegments bits)
          (Allocation.physicalComponent target segment))
        (Allocation.logicalWords bits target segment) :=
  Allocation.bankDescriptor_active bits target segment hs

example (bits : List Bool) (target : Bool) (regs : Registers)
    (ht : regs 3 = target.toNat) (hw : regs 22 = Experiment.width bits.length) :
    let actual := Experiment.physicalReader.eval (Allocation.memory bits) ⟨regs, .running⟩
    let word := Allocation.logicalWord bits target (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = (match word with | none => 0 | some xs => bitsToNatLE xs + 1) ∧
    actual.final.regs 8195 = (word.map List.length).getD 0 ∧
    actual.reads = Allocation.readerReceipts bits target (regs 8192) (regs 8193) ∧
    (∀ r, r < 8194 ∨ 8271 ≤ r → actual.final.regs r = regs r) :=
  Allocation.physicalReader_correct bits target regs ⟨ht, hw⟩

example (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    ∀ regs, (∀ r < 190, regs r = loadedMetadata bits operation target argument r) →
    let actual := Experiment.physicalReader.eval (Allocation.memory bits) ⟨regs, .running⟩
    let word := Allocation.logicalWord bits target (regs 8192) (regs 8193)
    actual.final.status = .running ∧ actual.final.regs 8194 = logicalPacket word ∧
    actual.final.regs 8195 = logicalLength word ∧
    actual.reads = Allocation.readerReceipts bits target (regs 8192) (regs 8193) ∧
    (∀ r, r < 8194 ∨ 8271 ≤ r → actual.final.regs r = regs r) :=
  loadedModel_reader bits operation target argument

example (bits : List Bool) (target : Bool) (argument : Nat) :
    (Controller.selectReference (Allocation.readStore bits target)
      (ChargedSetup.targetMetadata bits (ChargedSetup.setupMetadata bits
        (initial .select target argument).regs)) argument).value =
          Succinct.select target bits argument :=
  selectReference_value bits target argument

example (bits : List Bool) (target : Bool) (segment index : Nat)
    (h21 : segment ≠ 21) (h22 : segment ≠ 22) :
    logicalPacket ((Allocation.readStore bits target).readWord? segment index) ≤
      2 ^ (2 * machineWordBits bits.length + 3) :=
  canonical_directory_packet bits target segment index h21 h22

example (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : segment = 21 ∨ segment = 22) :
    logicalPacket ((Allocation.readStore bits target).readWord? segment index) ≤
      2 ^ (machineWordBits bits.length + 8) :=
  canonical_table_packet bits target segment index hs

#print axioms complete_capacity
#print axioms completeRho_littleO
#print axioms width_bounds
#print axioms Allocation.bankDescriptor_active
#print axioms Allocation.logicalWords_view
#print axioms Allocation.decode_logicalWords
#print axioms Allocation.physicalReader_correct
#print axioms Allocation.readerSimulation
#print axioms loadedModel_reader
#print axioms selectReference_value
#print axioms canonicalLimits
#print axioms canonical_directory_packet
#print axioms canonical_table_packet
#print axioms canonical_raw_length

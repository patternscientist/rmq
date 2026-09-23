import RMQ.Core.WordRAM.Native.Machine.CodeFacts

namespace RMQ.SuccinctFinal.PackedNative.LimbMachine.CodeFactsChecks

open PackedWordRAM LimbWord

example (width : Nat) (fields : Array Word) (i : Instruction)
    (h : decodeInstruction width fields = .ok i) :
    fields = (i.encoding.map (LimbWord.encode width)).toArray ∧
      ∀ value ∈ i.encoding, value < 2 ^ width :=
  decodeInstruction_success width fields i h

example (width : Nat) (fields : Array Word) (i : Instruction)
    (hs : fields.size ≤ 5)
    (hc : ∀ word ∈ fields.toList, LimbWord.Canonical width word)
    (hp : parseInstruction (fields.toList.map LimbWord.decode) = .ok i) :
    decodeInstruction width fields = .ok i :=
  decodeInstruction_of_canonical width fields i hs hc hp

example (width : Nat) (code : Code)
    (hc : ∀ fields ∈ code.toList, ∃ i, decodeInstruction width fields = .ok i) :
    ∃ program : Program, code = (program.map (encodeInstruction width)).toArray ∧
      ∀ i ∈ program, ∀ value ∈ i.encoding, value < 2 ^ width :=
  code_exists_program width code hc

example (i : Instruction) (fields : List Nat)
    (hp : parseInstruction fields = .ok i) : i.encoding = fields :=
  parseInstruction_success_encoding fields i hp

#print axioms parseInstruction_success_encoding
#print axioms decodeInstruction_success
#print axioms code_exists_program

end RMQ.SuccinctFinal.PackedNative.LimbMachine.CodeFactsChecks

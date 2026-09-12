import RMQ.Core.WordRAM.Bitvector.SelectExperiment
import RMQ.Core.WordRAM.Bitvector.Normalization

/-! # Proposed generic physical reader contract

This module fixes proof-side propositions for the select route experiment.
It does not assert that the experiment inhabits them. The executable source
receives only numeric memory and machine registers; logical words, descriptors
and metadata identities below are specifications to be proved from that run.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace GenericSelect
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def readerPacket (word : Option (List Bool)) : Nat :=
  (word.map (fun bits => bitsToNatLE bits + 1)).getD 0

def readerLength (word : Option (List Bool)) : Nat :=
  (word.map List.length).getD 0

def genericLogicalWord (bits : List Bool) (target : Bool)
    (segment index : Nat) : Option (List Bool) :=
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  if segment = 0 then (d.bitWords.store.words[index]?).map (normalize target)
  else if segment < 17 then
    ((Experiment.directorySegments d)[segment - 1]?.getD #[])[index]?
  else if segment = 21 then (SuccinctClose.bpFringeChunkTable c).store.words[index]?
  else if segment = 22 then (SuccinctClose.bpChunkSelectTable c false).store.words[index]?
  else none

def genericReadStore (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? := genericLogicalWord bits target

/-- Only the target input and already charged physical width are read by this
reader outside its request and scratch bank. Whole-controller metadata has a
larger independent setup obligation. -/
def GenericReaderMetadata (bits : List Bool) (target : Bool) (regs : Registers) : Prop :=
  regs 3 = target.toNat ∧ regs 22 = Experiment.width bits.length

def GenericReaderFrame (before after : Registers) : Prop :=
  ∀ r, r < 8194 ∨ 8271 ≤ r → after r = before r

/-- Canonical descriptor-read prefix, followed by physical span attempts.
Using canonical metadata here is a specification obligation: the reader must
derive the same span from its actual four charged descriptor replies. -/
def genericReaderReceipts (bits : List Bool) (target : Bool) (mem : Memory)
    (segment index : Nat) : List Receipt :=
  if segment < 23 then
    let address := 23 + target.toNat * 92 + segment * 4
    let canonical := Experiment.memory bits
    let descriptor := (List.range 4).map fun i => ⟨address + i, mem[address + i]?⟩
    let count := canonical[address + 3]?.getD 0
    if index < count then
      let base := canonical[address]?.getD 0
      let bitLength := canonical[address + 1]?.getD 0
      let stride := canonical[address + 2]?.getD 0
      descriptor ++ spanAttemptReceipts (Experiment.width bits.length)
        (base + index * stride) (min stride (bitLength - index * stride)) mem
    else descriptor
  else []

/-- Generic correctness interface with exact packet, length, ordered attempts
and frame on one evaluation. Its canonical instance remains a BV-1 obligation. -/
def GenericReaderCorrect (bits : List Bool) (target : Bool)
    (mem : Memory) (reader : Block) : Prop :=
  ∀ regs, GenericReaderMetadata bits target regs →
    let actual := reader.eval mem ⟨regs, .running⟩
    let expected := genericLogicalWord bits target (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = readerPacket expected ∧
    actual.final.regs 8195 = readerLength expected ∧
    actual.reads = genericReaderReceipts bits target mem (regs 8192) (regs 8193) ∧
    GenericReaderFrame regs actual.final.regs

/-- The exact canonical reader target to discharge, with no shape witness. -/
def CanonicalGenericReaderCorrect : Prop :=
  ∀ (bits : List Bool) (target : Bool),
    GenericReaderCorrect bits target (Experiment.memory bits) Experiment.physicalReader

theorem readerPacket_normalize (target : Bool) (word : Option (List Bool)) :
    readerPacket (word.map (normalize target)) =
      let packet := readerPacket word
      let len := readerLength word
      if packet = 0 then 0 else if target then 2 ^ len + 1 - packet else packet :=
  normalize_optional_numeric_packet target word

theorem readerLength_normalize (target : Bool) (word : Option (List Bool)) :
    readerLength (word.map (normalize target)) = readerLength word :=
  normalize_optional_length target word

end RMQ.PackedBitvector

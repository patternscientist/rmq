import RMQ.Core.WordRAM.Bitvector.ReaderInterface
import RMQ.Core.WordRAM.Bitvector.AllocationFacts

open RMQ RMQ.PackedBitvector RMQ.SuccinctSpace

#print axioms readerPacket_normalize
#print axioms readerLength_normalize

example (target : Bool) (word : Option (List Bool)) :
    readerPacket (word.map (normalize target)) =
      let packet := readerPacket word
      let len := readerLength word
      if packet = 0 then 0 else if target then 2 ^ len + 1 - packet else packet :=
  readerPacket_normalize target word

example (target : Bool) (word : Option (List Bool)) :
    readerLength (word.map (normalize target)) = readerLength word :=
  readerLength_normalize target word

-- Pin the generic reader target's actual data quantifiers without claiming its proof.
example : CanonicalGenericReaderCorrect =
    (∀ (bits : List Bool) (target : Bool),
      GenericReaderCorrect bits target (Experiment.memory bits) Experiment.physicalReader) := rfl

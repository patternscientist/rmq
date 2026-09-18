import RMQ.Core.WordRAM.Bitvector.MemoryLayout
import RMQ.Core.GenericSelect.Family

/-! # One numerical allocation for access, rank and both select targets

The select components retain their order and bit positions. Four rank sample
tables follow them. Logical segment 19 gives rank/access a sentinel-bearing
view of the single raw bit range; it contributes no second raw payload.
All routing information is retained as numerical header words.
-/

namespace RMQ.PackedBitvector.Allocation

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

def rankSegments (bits : List Bool) : List (Array (List Bool)) :=
  let d := jacobsonRankData bits
  [d.superTables.falseTable.store.words, d.superTables.trueTable.store.words,
   d.blockTables.falseTable.store.words, d.blockTables.trueTable.store.words]

def allSegments (bits : List Bool) : List (Array (List Bool)) :=
  Experiment.allSegments bits ++ rankSegments bits

def allDescriptors (bits : List Bool) : List (List Nat) :=
  Experiment.descriptorsFrom (207 * Experiment.width bits.length) (allSegments bits)

def descriptorBank (bits : List Bool) (target : Bool) : List (List Nat) :=
  let desc := allDescriptors bits
  [desc[0]!] ++ (desc.drop (if target then 17 else 1)).take 16 ++
    [desc[if target then 36 else 35]!, desc[if target then 38 else 37]!,
     Experiment.descriptor (207 * Experiment.width bits.length)
       (jacobsonRankData bits).bitWords.store.words,
     [0, 0, 0, 0]] ++ [desc[33]!, desc[34]!]

def scalarHeader (bits : List Bool) : List Nat :=
  let df := sparseExceptionSelectData bits false
  let dt := sparseExceptionSelectData bits true
  let rank := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  [occurrenceCount bits false, occurrenceCount bits true, bits.length,
    rank.wordSize, rank.blocksPerSuper, 0, Experiment.width bits.length, 0,
    df.wordSize, df.superStride, df.localStride, df.localSlotsPerSuper] ++
      Experiment.flagScalars df ++ [df.wordSize, 0, c] ++ Experiment.flagScalars dt

def header (bits : List Bool) : List Nat :=
  scalarHeader bits ++ (descriptorBank bits false).flatten ++
    (descriptorBank bits true).flatten

def body (bits : List Bool) : List Bool :=
  (allSegments bits).flatMap Experiment.segmentBits

def memory (bits : List Bool) : Memory :=
  header bits ++ denseWords (Experiment.width bits.length) (body bits)

@[simp] theorem rankSegments_length (bits : List Bool) :
    (rankSegments bits).length = 4 := by rfl

@[simp] theorem allSegments_length (bits : List Bool) :
    (allSegments bits).length = 39 := by simp [allSegments]

@[simp] theorem allDescriptors_length (bits : List Bool) :
    (allDescriptors bits).length = 39 := by simp [allDescriptors]

@[simp] theorem descriptorBank_length (bits : List Bool) (target : Bool) :
    (descriptorBank bits target).length = 23 := by
  cases target <;> simp [descriptorBank]

@[simp] theorem scalarHeader_length (bits : List Bool) :
    (scalarHeader bits).length = 23 := by simp [scalarHeader, Experiment.flagScalars]

end RMQ.PackedBitvector.Allocation

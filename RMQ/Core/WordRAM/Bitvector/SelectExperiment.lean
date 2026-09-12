import RMQ.Core.WordRAM.Packed.SelectSource
import RMQ.Core.WordRAM.Packed.SpanAssembly
import RMQ.Core.WordRAM.Packed.RegularLocate
import RMQ.Core.WordRAM.Packed.DensePacking
import RMQ.Core.WordRAM.Packed.ArrayRun
import RMQ.Core.GenericSelect.Source
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedWordChunks

/-! # Generic select feasibility construction

This experiment runs the existing select controller with a new physical reader.
It is a route experiment, with no all-size correctness, safety or space theorem
yet. The reader receives only numeric memory and registers. All semantic data
below is used during allocation; no source block receives a logical store.
-/

namespace RMQ.PackedBitvector.Experiment

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def width (n : Nat) : Nat := 32 + 16 * machineWordBits n

def directorySegments {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) : List (Array (List Bool)) :=
  [d.superTable.baseOccurrenceTable.store.words,
   d.superTable.baseWordIndexTable.store.words,
   d.superTable.rankBeforeTable.store.words,
   d.superTable.firstOffsetTable.store.words,
   d.localTable.baseOccurrenceTable.store.words,
   d.localTable.baseWordIndexTable.store.words,
   d.localTable.rankBeforeTable.store.words,
   d.localTable.firstOffsetTable.store.words,
   d.longFlagRankData.superTables.trueTable.store.words,
   d.longFlagRankData.blockTables.trueTable.store.words,
   d.longFlagRankData.bitWords.store.words,
   d.longSuperRelativeTable.store.words,
   d.sparseDirectory.rankData.superTables.trueTable.store.words,
   d.sparseDirectory.rankData.blockTables.trueTable.store.words,
   d.sparseDirectory.rankData.bitWords.store.words,
   d.sparseDirectory.relativeTable.store.words]

def flagScalars {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) : List Nat :=
  [d.longFlagBits.length, d.sparseDirectory.flagBits.length,
   d.longFlagRankData.wordSize, d.sparseDirectory.rankData.wordSize]

def segmentBits (words : Array (List Bool)) : List Bool := words.toList.flatten

def descriptor (position : Nat) (words : Array (List Bool)) : List Nat :=
  [position, (segmentBits words).length, (words[0]?.getD []).length, words.size]

def descriptorsFrom : Nat → List (Array (List Bool)) → List (List Nat)
  | _, [] => []
  | position, words :: rest =>
      descriptor position words :: descriptorsFrom
        (position + (segmentBits words).length) rest

/-- Twenty-three scalar words, followed by two banks of 23 four-word descriptors.
The raw bitvector and the two universal chunk tables each occur once in the body.
The unused select segments have explicit absent descriptors. -/
def memory (bits : List Bool) : Memory := Id.run do
  let df := sparseExceptionSelectData bits false
  let dt := sparseExceptionSelectData bits true
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  let all := [df.bitWords.store.words] ++ directorySegments df ++ directorySegments dt ++
    [(SuccinctClose.bpFringeChunkTable c).store.words,
     (SuccinctClose.bpChunkSelectTable c false).store.words]
  let desc := descriptorsFrom (207 * width bits.length) all
  let bank (target : Bool) :=
    [desc[0]!] ++ (desc.drop (if target then 17 else 1)).take 16 ++
      List.replicate 4 [0, 0, 0, 0] ++ [desc[33]!, desc[34]!]
  let scalars :=
    [occurrenceCount bits false, occurrenceCount bits true, bits.length,
      0, 0, 0, width bits.length, 0, df.wordSize, df.superStride,
      df.localStride, df.localSlotsPerSuper] ++ flagScalars df ++
      [df.wordSize, 0, c] ++ flagScalars dt
  return scalars ++ (bank false).flatten ++ (bank true).flatten ++
    denseWords (width bits.length) (all.flatMap segmentBits)

def descriptorLoads : Block := Block.sequence [
  .action (.constant 8208 4),
  .action (.arithmetic .mul 8209 8192 8208),
  .action (.constant 8210 92),
  .action (.arithmetic .mul 8211 3 8210),
  .action (.arithmetic .add 8209 8209 8211),
  .action (.constant 8210 23),
  .action (.arithmetic .add 8209 8209 8210),
  .action (.constant 8210 1),
  .action (.load 8201 8209),
  .action (.arithmetic .add 8209 8209 8210), .action (.load 8202 8209),
  .action (.arithmetic .add 8209 8209 8210), .action (.load 8203 8209),
  .action (.arithmetic .add 8209 8209 8210), .action (.load 8204 8209),
  .action (.move 8200 8193), regularLocateBlock 8200]

/-- Only the raw data segment is complemented, and only within its logical length.
Flag-rank words and table replies retain their stored values. -/
def finishPacket : Block := Block.sequence [
  .action (.move 8195 8207), .action (.constant 8210 1),
  .action (.arithmetic .add 8194 8259 8210),
  .ifZero 8192
    (.ifZero 3 .skip (Block.sequence [
      .action (.arithmetic .shl 8211 8210 8195),
      .action (.arithmetic .sub 8194 8211 8259)])) .skip]

def physicalReader : Block := Block.sequence [
  .action (.constant 8194 0), .action (.constant 8195 0),
  .action (.constant 8208 23), .action (.comparison .lt 8209 8192 8208),
  .ifZero 8209 .skip (Block.sequence [descriptorLoads,
    .ifZero 8205 .skip (Block.sequence [
      .action (.move 8256 22), .action (.move 8257 8206),
      .action (.move 8258 8207), spanBlock 8256, finishPacket])])]

def targetSetup : Block := .ifZero 3 .skip (Block.sequence [
  .action (.move 16 17),
  .action (.constant 6 19), .action (.load 28 6),
  .action (.constant 6 20), .action (.load 29 6),
  .action (.constant 6 21), .action (.load 30 6),
  .action (.constant 6 22), .action (.load 31 6)])

def setup : Block := Block.sequence ((List.range 19).map fun index =>
  .seq (.action (.constant 6 index)) (.action (.load (16 + index) 6)))

def source : Block := Block.sequence [setup,
  targetSetup, selectCloseBlock physicalReader]

def program : Program := source.compileAt 0 ++ [.halt 513]

def initial (target : Bool) (occurrence : Nat) : State :=
  ⟨fun r => if r = 3 then target.toNat else if r = 512 then occurrence else 0,
   0, .running⟩

def executeSelect (bits : List Bool) (target : Bool) (occurrence : Nat) : Run :=
  runArray (memory bits) program.toArray (source.size + 1) (initial target occurrence)

end RMQ.PackedBitvector.Experiment

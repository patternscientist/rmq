import RMQ.Core.WordRAM.Packed.ChunkArithmetic
import RMQ.Core.WordRAM.Packed.Frame

/-!
# Fixed rank source assembled from scalar blocks

The reader argument is a fixed source block inlined at construction time. It
uses registers8192,8193 for segment/index and returns the logical value packet
and length at8194,8195. It is not a runtime function or semantic store. The
final query supplies the concrete physical reader proved against its allocation.

Chunk width comes from counted metadata register34. The fixed eight-copy fold
still tests its runtime chunk count before each copy; short folds perform no
additional table reads. Whole rank performs all three seed reads before testing
their presence, matching the existing logical rank protocol.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def rankWordAddress : Block :=
    Block.sequence [
      .action (.move 280 256),
      .action (.move 281 34),
      .action (.move 282 261),
      .action (.move 283 262),
      chunkSlotBlock 280,
      .action (.constant 8192 21),
      .action (.move 8193 286)]

def rankWordDecode : Block :=
    Block.sequence [
      .action (.move 300 34),
      .action (.move 301 284),
      natSubBlock 302 8194 265 303,
      .action (.move 303 259),
      chunkRankBlock 300,
      .action (.arithmetic .add 260 260 304),
      .action (.arithmetic .add 261 261 265)]

def rankWordBody (reader : Block) : Block :=
  .seq (.action (.comparison .lt 264 261 263))
    (.ifZero 264 .skip (.seq rankWordAddress (.seq reader rankWordDecode)))

/-- Inputs word,length,limit,target at256..259; output260; local scratch261..310. -/
def rankWordInit : Block :=
  Block.sequence [
    .action (.constant 265 1),
    minBlock 262 258 257 264,
    natSubBlock 263 262 265 264,
    .action (.arithmetic .div 263 263 34),
    .action (.arithmetic .add 263 263 265),
    .action (.constant 266 8),
    minBlock 263 263 266 264,
    .action (.constant 261 0),
    .action (.constant 260 0)]

def rankWordBlock (reader : Block) : Block :=
  .seq rankWordInit (.repeat 8 (rankWordBody reader))

@[simp] theorem rankWordBody_size (reader : Block) :
    (rankWordBody reader).size = 60 + reader.size := by
  simp [rankWordBody, rankWordAddress, rankWordDecode, Block.sequence, Block.size, chunkSlotBlock_size,
    chunkRankBlock_size, natSubBlock_size]
  omega

@[simp] theorem rankWordBlock_size (reader : Block) :
    (rankWordBlock reader).size = 501 + 8 * reader.size := by
  simp [rankWordBlock, rankWordInit, Block.sequence, Block.size, minBlock_size, natSubBlock_size,
    rankWordBody_size, Nat.mul_add]
  omega

def rankSeedRead (reader : Block) (segment index output : Nat) : Block :=
  Block.sequence [
    .action (.move 8192 segment), .action (.move 8193 index), reader,
    .action (.move output 8194)]

def rankInit : Block :=
  Block.sequence [
    .action (.constant 370 1),
    .action (.constant 360 0),
    minBlock 361 352 353 369,
    .action (.arithmetic .div 362 361 354),
    .action (.arithmetic .div 363 362 355)]

def rankSeeds (reader : Block) : Block :=
  Block.sequence [rankInit, rankSeedRead reader 356 363 364,
    rankSeedRead reader 357 362 365, rankSeedRead reader 358 362 366,
    .action (.move 367 8195)]

def rankPrepareWord : Block :=
  Block.sequence [
          natSubBlock 256 366 370 369,
          .action (.move 257 367),
          .action (.arithmetic .mul 368 362 354),
          natSubBlock 258 361 368 369,
          .action (.move 259 359)]

def rankCombine : Block :=
  Block.sequence [
          natSubBlock 364 364 370 369,
          natSubBlock 365 365 370 369,
          .action (.arithmetic .add 360 364 365),
          .action (.arithmetic .add 360 360 260)]

def rankFinish (reader : Block) : Block :=
  .ifZero 364 .skip (.ifZero 365 .skip (.ifZero 366 .skip
    (.seq rankPrepareWord (.seq (rankWordBlock reader) rankCombine))))

/-- Whole rank inputs: pos,bitLength,wordSize,blocksPerSuper,superSegment,
blockSegment,wordSegment,target at352..359; output360; seeds/scratch361..370.
The in-word fold and the reader use their fixed disjoint banks. -/
def rankBlock (reader : Block) : Block :=
  .seq (rankSeeds reader) (rankFinish reader)

@[simp] theorem rankBlock_size (reader : Block) :
    (rankBlock reader).size = 551 + 11 * reader.size := by
  simp [rankBlock, rankSeeds, rankInit, rankSeedRead, rankFinish, rankPrepareWord,
    rankCombine, Block.sequence, Block.size, minBlock_size, natSubBlock_size,
    rankWordBlock_size]
  omega

/-- Fixed metadata-to-parameter setup for close rank; input position is352. -/
def rankCloseBlock (reader : Block) : Block :=
  Block.sequence [
    .action (.constant 369 2),
    .action (.arithmetic .mul 353 16 369),
    .action (.move 354 32),
    .action (.move 355 32),
    .action (.constant 356 17),
    .action (.constant 357 18),
    .action (.constant 358 19),
    .action (.constant 359 0),
    rankBlock reader]

/-- Long/sparse rank parameter setup, with no source generated from runtime n. -/
def rankLongBlock (reader : Block) : Block :=
  Block.sequence [
    .action (.move 353 28),
    .action (.move 354 30),
    .action (.constant 355 1),
    .action (.constant 356 9),
    .action (.constant 357 10),
    .action (.constant 358 11),
    .action (.constant 359 1),
    rankBlock reader]

def rankSparseBlock (reader : Block) : Block :=
  Block.sequence [
    .action (.move 353 29),
    .action (.move 354 31),
    .action (.constant 355 1),
    .action (.constant 356 13),
    .action (.constant 357 14),
    .action (.constant 358 15),
    .action (.constant 359 1),
    rankBlock reader]

end RMQ.SuccinctFinal.PackedWordRAM

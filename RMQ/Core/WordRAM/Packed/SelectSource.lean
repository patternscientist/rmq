import RMQ.Core.WordRAM.Packed.RankSource

/-!
# Fixed scalar source for close select

Every source argument is a compile-time block or register number. All varying
geometry is read from the charged metadata bank. Rank, select and physical-read
subroutines use disjoint caller banks, and bounded repeats compile to ordinary
primitive instructions. Result packets encode none as0 and some position as
position+1; no branch exits the enclosing query.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def selectWordAddress : Block := Block.sequence [
  .action (.move 280 400), .action (.move 281 34),
  .action (.move 282 404), .action (.move 283 401), chunkSlotBlock 280,
  .action (.constant 8192 21), .action (.move 8193 286)]

def selectWordDecode : Block := Block.sequence [
  .action (.move 300 34), .action (.move 301 284),
  natSubBlock 302 8194 407 409, .action (.constant 303 0), chunkRankBlock 300]

def selectWordMiss : Block := Block.sequence [
  natSubBlock 406 406 304 409, .action (.arithmetic .add 404 404 407)]

def selectWordSelectAddress : Block := Block.sequence [
  .action (.arithmetic .add 410 34 407),
  .action (.arithmetic .mul 410 285 410),
  .action (.arithmetic .add 8193 410 406),
  .action (.constant 8192 22)]

def selectWordFinish : Block := Block.sequence [
  natSubBlock 411 8194 407 409,
  .action (.arithmetic .mul 403 404 34),
  .action (.arithmetic .add 403 403 411),
  .action (.arithmetic .add 403 403 407)]

def selectWordSelected (reader : Block) : Block :=
  Block.sequence [selectWordSelectAddress, reader, selectWordFinish]

def selectWordActive (reader : Block) : Block := Block.sequence [
  selectWordAddress, reader, selectWordDecode,
  .action (.comparison .lt 408 406 304),
  .ifZero 408 selectWordMiss (selectWordSelected reader)]

/-- Guard the remaining copies once the select result has been found. -/
def selectWordBody (reader : Block) : Block :=
  .ifZero 403
    (.seq (.action (.comparison .lt 408 404 405))
      (.ifZero 408 .skip (selectWordActive reader))) .skip

/-- Inputs word,length,occurrence400..402; output403; local scratch404..411.
Chunk arithmetic and the physical reader use their existing separate banks. -/
def selectWordInit : Block := Block.sequence [
  .action (.constant 407 1), .action (.constant 403 0),
  .action (.constant 404 0), .action (.move 406 402),
  natSubBlock 405 401 407 409,
  .action (.arithmetic .div 405 405 34),
  .action (.arithmetic .add 405 405 407),
  .action (.constant 408 8), minBlock 405 405 408 409]

def selectWordBlock (reader : Block) : Block := .seq selectWordInit (.repeat 8 (selectWordBody reader))

/-- One statically placed logical read followed by a copy of its packet. -/
def selectFieldRead (reader : Block) (segment indexReg destination : Nat) : Block :=
  Block.sequence [
    .action (.constant 8192 segment), .action (.move 8193 indexReg), reader,
    .action (.move destination 8194)]

def selectFieldsFrom (reader : Block) (segment indexReg destination : Nat) : Nat → Block
  | 0 => .skip
  | count + 1 => .seq (selectFieldRead reader segment indexReg destination)
      (selectFieldsFrom reader (segment + 1) indexReg (destination + 1) count)

def selectEntryFields (reader : Block) (segment indexReg base : Nat) : Block :=
  selectFieldsFrom reader segment indexReg (base + 5) 4

def selectEntryDecode (base : Nat) : Block :=
  .ifZero (base + 5) .skip (.ifZero (base + 6) .skip
      (.ifZero (base + 7) .skip (.ifZero (base + 8) .skip
        (Block.sequence [
          natSubBlock (base + 1) (base + 5) (base + 9) (base + 10),
          natSubBlock (base + 2) (base + 6) (base + 9) (base + 10),
          natSubBlock (base + 3) (base + 7) (base + 9) (base + 10),
          natSubBlock (base + 4) (base + 8) (base + 9) (base + 10),
          .action (.constant base 1)]))))

/-- Four reads precede all presence checks. At base: presence, four decoded
fields, four raw packets, constant one and scratch. Parameters are static. -/
def selectEntryBlock (reader : Block) (segment indexReg base : Nat) : Block :=
  Block.sequence [
    .action (.constant base 0), .action (.constant (base + 9) 1),
    selectEntryFields reader segment indexReg base, selectEntryDecode base]

def denseFirstPrepare : Block := Block.sequence [
  natSubBlock 400 645 659 658, .action (.move 401 646),
  .action (.arithmetic .add 402 648 650)]

def denseWordFinish : Block :=
  .ifZero 403 .skip (Block.sequence [
    .action (.arithmetic .mul 643 644 32),
    .action (.arithmetic .add 643 643 403)])

def denseFirstSelected (reader : Block) : Block := Block.sequence [
  denseFirstPrepare, selectWordBlock reader, denseWordFinish]

def denseSecondAddress : Block := Block.sequence [
  .action (.arithmetic .add 644 644 659),
  .action (.constant 8192 0), .action (.move 8193 644)]

def denseSecondPrepare : Block := Block.sequence [
  natSubBlock 400 8194 659 658, .action (.move 401 8195),
  natSubBlock 402 650 651 658]

def denseSecondSelected (reader : Block) : Block := Block.sequence [
  denseSecondAddress, reader,
  .ifZero 8194 .skip (Block.sequence [
    denseSecondPrepare, selectWordBlock reader, denseWordFinish])]

def denseReadAddress : Block := Block.sequence [
  .action (.constant 643 0), .action (.constant 659 1),
  .action (.arithmetic .div 644 640 32),
  .action (.constant 8192 0), .action (.move 8193 644)]

def denseReadSave : Block := Block.sequence [
  .action (.move 645 8194), .action (.move 646 8195)]

def denseRankBeforePrepare : Block := Block.sequence [
  .action (.arithmetic .mul 647 644 32), natSubBlock 647 640 647 658,
  natSubBlock 256 645 659 658, .action (.move 257 646),
  .action (.move 258 647), .action (.constant 259 0)]

def denseRankWholePrepare : Block := Block.sequence [
  .action (.move 648 260),
  natSubBlock 256 645 659 658, .action (.move 257 646),
  .action (.move 258 646), .action (.constant 259 0)]

def denseChoosePrepare : Block := Block.sequence [
  .action (.move 649 260), natSubBlock 650 642 641 658,
  natSubBlock 651 649 648 658,
  .action (.comparison .lt 652 650 651)]

def denseRankBefore (reader : Block) : Block := .seq denseRankBeforePrepare (rankWordBlock reader)

def denseRankWhole (reader : Block) : Block := .seq denseRankWholePrepare (rankWordBlock reader)

def denseSelectBranch (reader : Block) : Block :=
  .ifZero 652 (denseSecondSelected reader) (denseFirstSelected reader)

def densePresent (reader : Block) : Block := Block.sequence [
  denseRankBefore reader, denseRankWhole reader, denseChoosePrepare,
  denseSelectBranch reader]

/-- Inputs basePosition,baseOccurrence,occurrence640..642; output643;
scratch644..659. Both rank calls use the same first logical word and length. -/
def denseSelectBlock (reader : Block) : Block := Block.sequence [
  denseReadAddress, reader, denseReadSave,
  .ifZero 645 .skip (densePresent reader)]

def selectLongAddress : Block := Block.sequence [
  .action (.arithmetic .mul 534 360 25), natSubBlock 535 512 561 550,
  .action (.arithmetic .add 8193 534 535), .action (.constant 8192 12)]

def selectLongFinish : Block :=
  .ifZero 8194 .skip (Block.sequence [
    .action (.arithmetic .mul 513 562 32),
    .action (.arithmetic .add 513 513 564),
    .action (.arithmetic .add 513 513 8194)])

def selectLongBlock (reader : Block) : Block := Block.sequence [
  .action (.move 352 514), rankLongBlock reader,
  selectLongAddress, reader, selectLongFinish]

def selectSparseAddress : Block := Block.sequence [
  .action (.arithmetic .mul 534 360 26), natSubBlock 535 512 521 550,
  .action (.arithmetic .add 8193 534 535), .action (.constant 8192 16)]

def selectSparseFinish : Block :=
  .ifZero 8194 .skip (.action (.arithmetic .add 513 520 8194))

def selectSparseBlock (reader : Block) : Block := Block.sequence [
  .action (.move 352 515), rankSparseBlock reader,
  selectSparseAddress, reader, selectSparseFinish]

def selectLocalAddress : Block := Block.sequence [
  natSubBlock 515 512 561 550,
  .action (.arithmetic .div 515 515 26),
  .action (.arithmetic .mul 534 514 27),
  .action (.arithmetic .add 515 534 515)]

def selectLocalPrepare : Block := Block.sequence [
  .action (.arithmetic .add 520 562 592),
  .action (.arithmetic .mul 520 520 32),
  .action (.arithmetic .add 520 520 594),
  .action (.arithmetic .add 521 561 591)]

def selectLocalDense (reader : Block) : Block := Block.sequence [
  .action (.move 640 520), .action (.move 641 521),
  .action (.move 642 512), denseSelectBlock reader,
  .action (.move 513 643)]

def selectLocalPresent (reader : Block) : Block := Block.sequence [
  selectLocalPrepare,
  .ifZero 593 (selectLocalDense reader) (selectSparseBlock reader)]

def selectLocalBlock (reader : Block) : Block := Block.sequence [
  selectLocalAddress,
  selectEntryBlock reader 5 515 590,
  .ifZero 590 .skip (selectLocalPresent reader)]

/-- Input occurrence512; output position packet513; controller scratch514..550,
super-entry560..570, local-entry590..600, dense/select/rank/reader banks. -/
def selectSuperPresent (reader : Block) : Block :=
  .ifZero 563 (selectLocalBlock reader) (selectLongBlock reader)

def selectEligible (reader : Block) : Block := Block.sequence [
  .action (.arithmetic .div 514 512 25), selectEntryBlock reader 1 514 560,
  .ifZero 560 .skip (selectSuperPresent reader)]

def selectCloseBlock (reader : Block) : Block := Block.sequence [
  .action (.constant 513 0), .action (.comparison .lt 550 512 16),
  .ifZero 550 .skip (selectEligible reader)]

end RMQ.SuccinctFinal.PackedWordRAM

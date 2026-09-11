import RMQ.Core.WordRAM.Packed.Scalar

/-!
# Fixed scalar source for interior candidates

All logical entry components are read through the supplied fixed reader block.
The seven-copy entry fold matches the canonical maximum entry width; its
semantic and word-safety proofs must discharge that bound. Candidates occupy
three distinct registers, avoiding a packed pair with an unproved width.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def candidateNoneBlock : Block := Block.sequence [
  .action (.constant 7000 0), .action (.constant 7001 0), .action (.constant 7002 0)]

def candidateSaveBlock (base : Nat) : Block := Block.sequence [
  .action (.move base 7000), .action (.move (base + 1) 7001),
  .action (.move (base + 2) 7002)]

def candidateRestoreBlock (base : Nat) : Block := Block.sequence [
  .action (.move 7000 base), .action (.move 7001 (base + 1)),
  .action (.move 7002 (base + 2))]

/-- The right candidate wins only for a strictly smaller score. -/
def candidateMergeLeftBlock (base : Nat) : Block :=
  .ifZero base .skip (.ifZero 7000 (candidateRestoreBlock base)
    (.seq (.action (.comparison .lt 7003 7001 (base + 1)))
      (.ifZero 7003 (candidateRestoreBlock base) .skip)))

def interiorReadAddress : Block := Block.sequence [
    .action (.arithmetic .mul 715 707 709),
    .action (.arithmetic .add 715 706 715),
    .action (.arithmetic .add 8193 715 710),
    .action (.constant 8192 20)]

def interiorReadDecode : Block := Block.sequence [
    .ifZero 8194 (.action (.constant 713 0)) (Block.sequence [
      natSubBlock 716 8194 714 718,
      .action (.arithmetic .shl 716 716 712),
      .action (.arithmetic .add 711 711 716),
      .action (.arithmetic .add 712 712 8195)]),
    .action (.arithmetic .add 710 710 714)]

def interiorReadBody (reader : Block) : Block :=
  .seq (.action (.comparison .lt 717 710 709)) (.ifZero 717 .skip
    (.seq interiorReadAddress (.seq reader interiorReadDecode)))

def interiorReadInit : Block := Block.sequence [
    .action (.arithmetic .div 709 705 32),
    .action (.arithmetic .mod 715 705 32),
    .ifZero 715 .skip (.action (.arithmetic .add 709 709 714)),
    .action (.constant 710 0), .action (.constant 711 0),
    .action (.constant 712 0), .action (.constant 713 1)]

def interiorReadHead : Block := Block.sequence [
  .action (.constant 708 0), .action (.constant 714 1),
  .action (.comparison .lt 717 707 704)]

def interiorReadInvalid (reader : Block) : Block := Block.sequence [
    .action (.constant 8192 20), .action (.move 8193 57), reader,
    .action (.move 708 8194)]

def interiorReadFinish : Block :=
  .ifZero 713 .skip (.action (.arithmetic .add 708 711 714))

def interiorReadValid (reader : Block) : Block :=
  .seq interiorReadInit (.seq (.repeat 7 (interiorReadBody reader)) interiorReadFinish)

/-- Inputs entryCount,width,base,index704..707; output packet708; scratch709..718.
The out-of-range arm preserves the actual dead logical request. -/
def interiorReadBlock (reader : Block) : Block :=
  .seq interiorReadHead (.ifZero 717 (interiorReadInvalid reader) (interiorReadValid reader))

def interiorMinBaselinePrefix : Block := Block.sequence [
  .action (.constant 774 1),
  .action (.move 704 37), .action (.move 705 32), .action (.move 706 49),
  .action (.arithmetic .div 707 768 35)]

def interiorMinBaselineProgram (entry : Block) : Block :=
  .seq interiorMinBaselinePrefix (.seq entry (.action (.move 769 708)))

def interiorMinRelativePrefix (base : Nat) : Block := Block.sequence [
  .action (.move 704 36), .action (.move 705 42), .action (.move 706 base),
  .action (.move 707 768)]

def interiorMinFieldProgram (entry : Block) (base output : Nat) : Block :=
  .seq (interiorMinRelativePrefix base) (.seq entry (.action (.move output 708)))

def interiorMinFinish : Block := .seq candidateNoneBlock
  (.ifZero 769 .skip (.ifZero 770 .skip (.ifZero 771 .skip (.ifZero 772 .skip
    (Block.sequence [
      .action (.constant 7000 1), natSubBlock 769 769 774 773,
      natSubBlock 770 770 774 773, .action (.arithmetic .add 7001 769 770),
      .action (.arithmetic .mul 773 33 35), natSubBlock 7001 7001 773 769,
      .action (.arithmetic .mul 7002 768 33),
      .action (.arithmetic .add 7002 7002 772), natSubBlock 7002 7002 774 773])))))

/-- Input block768; writes the global candidate and local scratch769..774. -/
def interiorMinProgram (entry : Block) : Block :=
  .seq (interiorMinBaselineProgram entry)
    (.seq (interiorMinFieldProgram entry 50 770)
      (.seq (interiorMinFieldProgram entry 51 771)
        (.seq (interiorMinFieldProgram entry 52 772) interiorMinFinish)))
def interiorMinBlock (reader : Block) : Block :=
  interiorMinProgram (interiorReadBlock reader)

def interiorLocalSpanPrefix : Block := Block.sequence [
  .action (.arithmetic .mul 704 40 38),
  .action (.arithmetic .mul 707 800 704),
  .action (.arithmetic .mul 803 802 38),
  .action (.arithmetic .add 707 707 803), .action (.arithmetic .add 707 707 801),
  .action (.arithmetic .mul 704 39 704),
  .action (.move 705 43), .action (.move 706 53)]

def interiorLocalSpanSelectedPrefix : Block := Block.sequence [
  .action (.constant 804 1), .action (.arithmetic .mul 768 800 38),
  .action (.arithmetic .add 768 768 708), natSubBlock 768 768 804 803]

/-- Inputs macro,localStart,level800..802. -/
def interiorLocalSpanProgram (entry minimum : Block) : Block :=
  .seq interiorLocalSpanPrefix (.seq entry
    (.ifZero 708 candidateNoneBlock (.seq interiorLocalSpanSelectedPrefix minimum)))
def interiorLocalSpanBlock (reader : Block) : Block :=
  interiorLocalSpanProgram (interiorReadBlock reader) (interiorMinBlock reader)

def interiorGlobalSpanPrefix : Block := Block.sequence [
  .action (.arithmetic .mul 704 41 39),
  .action (.move 705 44), .action (.move 706 54),
  .action (.arithmetic .mul 707 817 39), .action (.arithmetic .add 707 707 816)]

def interiorGlobalSpanSelectedPrefix : Block := Block.sequence [
  .action (.constant 818 1), natSubBlock 768 708 818 819]

/-- Inputs macroStart,level816..817. -/
def interiorGlobalSpanProgram (entry minimum : Block) : Block :=
  .seq interiorGlobalSpanPrefix (.seq entry
    (.ifZero 708 candidateNoneBlock (.seq interiorGlobalSpanSelectedPrefix minimum)))
def interiorGlobalSpanBlock (reader : Block) : Block :=
  interiorGlobalSpanProgram (interiorReadBlock reader) (interiorMinBlock reader)

def interiorLocalTwoPrefix : Block := Block.sequence [
  .action (.move 704 45), .action (.move 705 47), .action (.move 706 55),
  .action (.move 707 834)]

def interiorLocalTwoFirstPrefix : Block := Block.sequence [
  .action (.constant 843 1), natSubBlock 835 708 843 844,
  .action (.arithmetic .div 836 835 45), .action (.arithmetic .mod 837 835 45),
  .action (.move 800 832), .action (.move 801 833), .action (.move 802 836)]

def interiorLocalTwoSecondPrefix : Block := Block.sequence [
  .action (.move 800 832), .action (.arithmetic .add 801 833 834),
  natSubBlock 801 801 837 844, .action (.move 802 836)]

def interiorLocalTwoSelectedProgram (span : Block) : Block :=
  .seq interiorLocalTwoFirstPrefix (.seq span (.seq (candidateSaveBlock 840)
    (.seq interiorLocalTwoSecondPrefix (.seq span (candidateMergeLeftBlock 840)))))

/-- Inputs macro,localStart,count832..834; saved first candidate840..842. -/
def interiorLocalTwoProgram (entry span : Block) : Block :=
  .seq interiorLocalTwoPrefix (.seq entry
    (.ifZero 708 candidateNoneBlock (interiorLocalTwoSelectedProgram span)))
def interiorLocalTwoBlock (reader : Block) : Block :=
  interiorLocalTwoProgram (interiorReadBlock reader) (interiorLocalSpanBlock reader)

def interiorGlobalTwoPrefix : Block := Block.sequence [
  .action (.move 704 46), .action (.move 705 48), .action (.move 706 56),
  .action (.move 707 865)]

def interiorGlobalTwoFirstPrefix : Block := Block.sequence [
  .action (.constant 875 1), natSubBlock 866 708 875 876,
  .action (.arithmetic .div 867 866 46), .action (.arithmetic .mod 868 866 46),
  .action (.move 816 864), .action (.move 817 867)]

def interiorGlobalTwoSecondPrefix : Block := Block.sequence [
  .action (.arithmetic .add 816 864 865), natSubBlock 816 816 868 876,
  .action (.move 817 867)]

def interiorGlobalTwoSelectedProgram (span : Block) : Block :=
  .seq interiorGlobalTwoFirstPrefix (.seq span (.seq (candidateSaveBlock 872)
    (.seq interiorGlobalTwoSecondPrefix (.seq span (candidateMergeLeftBlock 872)))))

/-- Inputs macroStart,count864..865; saved first candidate872..874. -/
def interiorGlobalTwoProgram (entry span : Block) : Block :=
  .seq interiorGlobalTwoPrefix (.seq entry
    (.ifZero 708 candidateNoneBlock (interiorGlobalTwoSelectedProgram span)))
def interiorGlobalTwoBlock (reader : Block) : Block :=
  interiorGlobalTwoProgram (interiorReadBlock reader) (interiorGlobalSpanBlock reader)

def interiorRangeCrossPrefix : Block := Block.sequence [
  natSubBlock 901 897 900 910,
  .action (.arithmetic .div 902 901 38), .action (.arithmetic .mod 903 901 38),
  .action (.move 832 898), .action (.move 833 899), .action (.move 834 900)]

def interiorRangeAdjacentPrefix : Block := Block.sequence [
  .action (.arithmetic .add 832 898 911), .action (.constant 833 0),
  .action (.move 834 903)]

def interiorRangeMiddlePrefix : Block := Block.sequence [
  .action (.arithmetic .add 864 898 911), .action (.move 865 902)]

def interiorRangeTrailingPrefix : Block := Block.sequence [
  .action (.arithmetic .add 832 898 911), .action (.arithmetic .add 832 832 902),
  .action (.constant 833 0), .action (.move 834 903)]

def interiorRangeTrailingProgram (localTwo : Block) : Block :=
  .seq (candidateSaveBlock 907) (.seq interiorRangeTrailingPrefix
    (.seq localTwo (candidateMergeLeftBlock 907)))

def interiorRangeMiddleStageProgram (globalTwo : Block) : Block :=
  .seq interiorRangeMiddlePrefix (.seq globalTwo (candidateMergeLeftBlock 904))

def interiorRangeMiddleProgram (localTwo globalTwo : Block) : Block :=
  .seq (interiorRangeMiddleStageProgram globalTwo)
    (.ifZero 903 .skip (interiorRangeTrailingProgram localTwo))

def interiorRangeBranchProgram (localTwo globalTwo : Block) : Block :=
  .ifZero 902 (.seq interiorRangeAdjacentPrefix (.seq localTwo (candidateMergeLeftBlock 904)))
    (interiorRangeMiddleProgram localTwo globalTwo)

def interiorRangeCrossProgram (localTwo globalTwo : Block) : Block :=
  .seq interiorRangeCrossPrefix (.seq localTwo (.seq (candidateSaveBlock 904)
    (interiorRangeBranchProgram localTwo globalTwo)))
def interiorRangeCrossBlock (reader : Block) : Block :=
  interiorRangeCrossProgram (interiorLocalTwoBlock reader) (interiorGlobalTwoBlock reader)

def interiorRangePrefix : Block := Block.sequence [
  .action (.constant 911 1),
  .action (.arithmetic .div 898 896 38), .action (.arithmetic .mod 899 896 38),
  natSubBlock 900 38 899 910, .action (.comparison .le 910 897 900)]

def interiorRangeSinglePrefix : Block := Block.sequence [
  .action (.move 832 898), .action (.move 833 899), .action (.move 834 897)]

/-- Inputs startBlock,count896..897; output global candidate. -/
def interiorRangeProgram (localTwo cross : Block) : Block :=
  .ifZero 897 candidateNoneBlock (.seq interiorRangePrefix
    (.ifZero 910 cross (.seq interiorRangeSinglePrefix localTwo)))
def interiorRangeBlock (reader : Block) : Block :=
  interiorRangeProgram (interiorLocalTwoBlock reader) (interiorRangeCrossBlock reader)

end RMQ.SuccinctFinal.PackedWordRAM

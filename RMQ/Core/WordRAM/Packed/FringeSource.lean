import RMQ.Core.WordRAM.Packed.RankSource
import RMQ.Core.WordRAM.Packed.RaggedWindow
import RMQ.Core.WordRAM.Packed.InteriorSource

/-!
# Fixed source for fringe candidates and close LCA

The four-word window is concatenated using actual reply lengths. Its numeric
width bound is proved in RaggedWindow; no premise that early words are full is
needed. The fringe fold contains33 guarded copies. All candidate comparisons
use the same left-biased merge as the reference layer.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

/-- Compile-time four-way unrolling, preserving each returned logical length. -/
def loadWindowPart (reader : Block) (part : Nat) : Block := Block.sequence [
  .action (.constant 1028 part), .action (.arithmetic .add 8193 1025 1028),
  .action (.constant 8192 0), reader,
  natSubBlock (1056 + part) 8194 1026 1027,
  .action (.move (1060 + part) 8195)]

def loadWindowParts (reader : Block) (part : Nat) : Nat → Block
  | 0 => .skip
  | count + 1 => .seq (loadWindowPart reader part) (loadWindowParts reader (part + 1) count)

def loadWindowInit : Block := Block.sequence [
  .action (.constant 1026 1), .action (.arithmetic .div 1025 1024 33),
  .action (.arithmetic .mul 1025 1025 33), .action (.arithmetic .div 1025 1025 32)]

/-- Input close1024; exact ragged numeric window1064; words/lengths1056..1063. -/
def loadWindowBlock (reader : Block) : Block := Block.sequence [
  loadWindowInit, loadWindowParts reader 0 4, raggedWindowBlock 1056]

def fringeKeepBestBlock : Block := Block.sequence [
  .action (.move 1114 1124), .action (.move 1115 1125)]

def fringeConsiderBlock : Block := Block.sequence [
  .action (.arithmetic .div 1124 1123 1128),
  .action (.arithmetic .mod 1124 1124 1129),
  .action (.arithmetic .add 1124 1112 1124), natSubBlock 1124 1124 34 1132,
  .action (.arithmetic .mod 1125 1123 1128),
  .action (.arithmetic .add 1125 1117 1125),
  .ifZero 1113 (Block.sequence [
    .action (.constant 1113 1), fringeKeepBestBlock])
    (.seq (.action (.comparison .lt 1130 1124 1114))
      (.ifZero 1130 .skip fringeKeepBestBlock))]

def fringeAddressRangeBlock : Block := Block.sequence [
      .action (.arithmetic .mul 1117 1116 34),
      natSubBlock 1118 1109 1117 1132, minBlock 1118 1118 34 1132,
      .action (.arithmetic .add 1119 1110 1127),
      .action (.arithmetic .add 1126 1116 1127),
      .action (.arithmetic .mul 1126 1126 34), minBlock 1119 1119 1126 1132,
      natSubBlock 1120 1119 1117 1132]

def fringeAddressSlotBlock : Block := Block.sequence [
      .action (.arithmetic .shr 1121 1064 1117),
      .action (.arithmetic .shl 1126 1127 34),
      .action (.arithmetic .mod 1121 1121 1126),
      .action (.arithmetic .mul 1122 1121 1128),
      .action (.arithmetic .add 1122 1122 1118),
      .action (.arithmetic .mul 1122 1122 1128),
      .action (.arithmetic .add 8193 1122 1120),
      .action (.constant 8192 21)]

def fringeAddressBlock : Block := .seq fringeAddressRangeBlock fringeAddressSlotBlock

def fringeDecodeBlock : Block := Block.sequence [
      natSubBlock 1123 8194 1127 1132,
      .action (.comparison .lt 1130 1118 1120),
      .ifZero 1130 .skip fringeConsiderBlock]

def fringeAdvanceBlock : Block := Block.sequence [
      .action (.arithmetic .mul 1126 1128 1129),
      .action (.arithmetic .div 1126 1123 1126),
      .action (.arithmetic .add 1112 1112 1126), natSubBlock 1112 1112 34 1132,
      .action (.arithmetic .add 1116 1116 1127)]

def fringeBody (reader : Block) : Block :=
  .seq (.action (.comparison .lt 1130 1116 1111)) (.ifZero 1130 .skip
    (.seq fringeAddressBlock (.seq reader (.seq fringeDecodeBlock fringeAdvanceBlock))))

def fringeSeedAddressBlock : Block := Block.sequence [
  .action (.constant 1127 1), .action (.constant 1131 2),
  .action (.arithmetic .div 1107 1104 33), .action (.arithmetic .mul 1107 1107 33),
  .action (.arithmetic .div 1107 1107 32), .action (.arithmetic .mul 1107 1107 32),
  .action (.move 352 1107)]

def fringeSeedDecodeBlock : Block := Block.sequence [
  .action (.arithmetic .mul 1108 360 1131), natSubBlock 1108 1107 1108 1132,
  .action (.move 1024 1104)]

def fringeFoldRangeInit : Block := Block.sequence [
  natSubBlock 1109 1105 1107 1132,
  .action (.arithmetic .add 1110 1105 1106), natSubBlock 1110 1110 1127 1132,
  natSubBlock 1110 1110 1107 1132,
  .action (.arithmetic .div 1111 1110 34), .action (.arithmetic .add 1111 1111 1127),
  .action (.constant 1130 33), minBlock 1111 1111 1130 1132]

def fringeFoldStateInit : Block := Block.sequence [
  .action (.move 1112 1108), .action (.constant 1113 0),
  .action (.constant 1114 0), .action (.constant 1115 0), .action (.constant 1116 0),
  .action (.arithmetic .add 1128 34 1127), .action (.arithmetic .mul 1129 1131 1128)]

def fringeFoldInit : Block := .seq fringeFoldRangeInit fringeFoldStateInit

def fringeFinishBlock : Block := Block.sequence [
  .action (.constant 7000 1),
  .ifZero 1113 (Block.sequence [
    .action (.move 7001 1108), .action (.move 7002 1105)])
    (Block.sequence [
      .action (.move 7001 1114), .action (.arithmetic .add 7002 1107 1115)])]

def fringeFoldBlock (reader : Block) : Block :=
  .seq fringeFoldInit (.seq (.repeat 33 (fringeBody reader)) fringeFinishBlock)

def fringeSeedBlock (reader : Block) : Block := .seq fringeSeedAddressBlock
  (.seq (rankCloseBlock reader) fringeSeedDecodeBlock)

def fringeWindowFoldBlock (reader : Block) : Block :=
  .seq (loadWindowBlock reader) (fringeFoldBlock reader)

/-- Inputs close,start,span1104..1106; local scratch1107..1132; global candidate. -/
def fringeBlock (reader : Block) : Block :=
  .seq (fringeSeedBlock reader) (fringeWindowFoldBlock reader)

def lcaSamePrepareBlock : Block := Block.sequence [
  .action (.move 1104 1200), .action (.arithmetic .add 1105 1200 1214),
  natSubBlock 1106 1201 1200 1215, .action (.arithmetic .add 1106 1106 1214)]

def lcaSameBlock (reader : Block) : Block := .seq lcaSamePrepareBlock (fringeBlock reader)

def lcaCrossLeftPrepareBlock : Block := Block.sequence [
  .action (.move 1104 1200), .action (.arithmetic .add 1105 1200 1214),
  .action (.arithmetic .mul 1106 1203 33), .action (.arithmetic .add 1106 1106 33),
  natSubBlock 1106 1106 1200 1215]

def lcaCrossLeftBlock (reader : Block) : Block :=
  .seq lcaCrossLeftPrepareBlock (.seq (fringeBlock reader) (candidateSaveBlock 1205))

def lcaCrossMiddleInitBlock : Block := Block.sequence [
  .action (.arithmetic .add 896 1203 1214),
  .action (.comparison .lt 1215 896 1204)]

def lcaCrossMiddleCountBlock : Block :=
  .seq (natSubBlock 897 1204 1203 1215) (natSubBlock 897 897 1214 1215)

def lcaCrossMiddleProgram (interior : Block) : Block := .seq lcaCrossMiddleInitBlock
  (.ifZero 1215 candidateNoneBlock (.seq lcaCrossMiddleCountBlock interior))

def lcaCrossMiddleBlock (reader : Block) : Block := lcaCrossMiddleProgram (interiorRangeBlock reader)

def lcaCrossRightPrepareBlock : Block := Block.sequence [
  .action (.move 1104 1201), .action (.arithmetic .mul 1105 1204 33),
  natSubBlock 1106 1201 1105 1215, .action (.constant 1215 2),
  .action (.arithmetic .add 1106 1106 1215)]

def lcaCrossRightBlock (reader : Block) : Block :=
  .seq lcaCrossRightPrepareBlock (.seq (fringeBlock reader) (candidateMergeLeftBlock 1208))

def lcaCrossMergeSaveBlock : Block := .seq (candidateMergeLeftBlock 1205) (candidateSaveBlock 1208)

def lcaCrossProgram (left middle right : Block) : Block :=
  .seq left (.seq middle (.seq lcaCrossMergeSaveBlock right))

def lcaCrossBlock (reader : Block) : Block :=
  lcaCrossProgram (lcaCrossLeftBlock reader) (lcaCrossMiddleBlock reader) (lcaCrossRightBlock reader)

def lcaInitBlock : Block := Block.sequence [
  .action (.constant 1202 0), .action (.constant 1214 1),
  .action (.arithmetic .div 1203 1200 33), .action (.arithmetic .div 1204 1201 33),
  .action (.comparison .eq 1215 1203 1204)]

def lcaFinishBlock : Block :=
  .ifZero 7000 .skip (Block.sequence [
    natSubBlock 1202 7002 1214 1215, .action (.arithmetic .add 1202 1202 1214)])

def lcaChooseProgram (reader interior : Block) : Block :=
  .ifZero 1215
    (lcaCrossProgram (lcaCrossLeftBlock reader) (lcaCrossMiddleProgram interior) (lcaCrossRightBlock reader))
    (lcaSameBlock reader)

def lcaCloseProgram (reader interior : Block) : Block :=
  .seq lcaInitBlock (.seq (lcaChooseProgram reader interior) lcaFinishBlock)

/-- Input close pair1200..1201; output close packet1202. -/
def lcaCloseBlock (reader : Block) : Block := lcaCloseProgram reader (interiorRangeBlock reader)

end RMQ.SuccinctFinal.PackedWordRAM

import RMQ.Core.WordRAM.Construction.Builder.Emit

/-! # PRE-1 builder: size-only geometry prelude

Program text only (inside the builder firewall). The geometry prelude computes
size-only quantities from the input length in register 1 by charged
arithmetic; no quantity is supplied from outside the run. This module holds the
interior-layout subset (base, macro size, block count, macro sample count and
the two sparse-level domains and widths); later stages append further blocks.
Their equalities with the reference size-only definitions are proved outside
the firewall.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-- The two constants every later block assumes: `r2 = 1`, `r9 = 2`. -/
def constantsBlock : Block := acts [.constant rONE 1, .constant rTWO 2]

/-- `regs dst := Nat.log2 (d * (Nat.log2 d + 1)) + 1` for `d = regs dom`. -/
def levelWidthBlock (dst dom : Operand) : Block :=
  .seq (log2Block rLL dom)
    (.seq (acts [.arithmetic .add rLL rLL rONE, .arithmetic .mul rT0 dom rLL])
      (.seq (log2Block dst rT0) (acts [.arithmetic .add dst dst rONE])))

/-- Interior layout subset: base, macro size, block count, macro sample count,
local and global level domains and widths. -/
def interiorGeometryBlock : Block :=
  .seq (log2Block rBASE rN)
    (.seq (acts [.arithmetic .add rBASE rBASE rONE, .arithmetic .mul rMACRO rBASE rBASE,
        .arithmetic .div rBLOCKS rN rBASE, .arithmetic .div rMACROS rBLOCKS rMACRO,
        .arithmetic .add rMACROS rMACROS rONE, .arithmetic .add rLDOM rMACRO rTWO,
        .arithmetic .add rGDOM rMACROS rTWO])
      (.seq (levelWidthBlock rLWID rLDOM) (levelWidthBlock rGWID rGDOM)))

/-- `regs dst := Nat.log2 (regs src) + 1` (`machineWordBits`). -/
def wordBitsBlock (dst src : Operand) : Block :=
  .seq (log2Block dst src) (acts [.arithmetic .add dst dst rONE])

/-- Branch-free `dst := min a b` over the scratch registers 26-28. -/
def minActs (dst a b : Operand) : List Action :=
  [.comparison .lt rT1 a b, .arithmetic .sub rT2 rONE rT1, .arithmetic .mul rT3 rT1 a,
    .arithmetic .mul rT2 rT2 b, .arithmetic .add dst rT3 rT2]

/-- Step `i` of the geometry bank: it computes register `38 + i` from the input
length, the constants, the interior subset (registers 30-37) and the bank
registers below `38 + i`, using only the scratch registers 20-28. -/
def geoStepBlock : Nat → Block
  | 0 => acts [.arithmetic .mul rM2 rTWO rN]
  | 1 => wordBitsBlock rWS rM2
  | 2 => acts [.arithmetic .mul rSS rWS rWS]
  | 3 => wordBitsBlock rEL rWS
  | 4 => acts [.arithmetic .mul rT1 rEL rEL, .arithmetic .div rT1 rWS rT1,
      .comparison .lt rT2 rT1 rONE, .arithmetic .add rLSTR rT1 rT2]
  | 5 => acts [.arithmetic .add rT1 rSS rLSTR, .arithmetic .sub rT1 rT1 rONE,
      .arithmetic .div rLPS rT1 rLSTR]
  | 6 => acts [.arithmetic .mul rT1 rSS rWS, .arithmetic .mul rLSPAN rT1 rEL]
  | 7 => acts [.arithmetic .add rT1 rN rSS, .arithmetic .sub rT1 rT1 rONE,
      .arithmetic .div rSUP rT1 rSS]
  | 8 => acts [.arithmetic .mul rLOC rSUP rLPS]
  | 9 => acts (minActs rSP rLOC rN)
  | 10 => wordBitsBlock rRBW rSS
  | 11 => .seq (acts (minActs rT0 rM2 rLSPAN)) (wordBitsBlock rLW rT0)
  | 12 => wordBitsBlock rLFW rSUP
  | 13 => wordBitsBlock rSFW rSP
  | 14 => acts [.arithmetic .div rT1 rM2 rWS, .arithmetic .div rT1 rT1 rWS,
      .arithmetic .add rRSUP rT1 rONE]
  | 15 => acts [.arithmetic .div rT1 rM2 rWS, .arithmetic .add rRBLK rT1 rONE]
  | 16 => acts [.arithmetic .div rT1 rSUP rLFW, .arithmetic .add rLFR rT1 rONE]
  | 17 => acts [.arithmetic .div rT1 rSP rSFW, .arithmetic .add rSFR rT1 rONE]
  | 18 => acts [.arithmetic .mul rBS2 rTWO rBASE]
  | 19 => acts [.arithmetic .div rT1 rBLOCKS rBASE, .arithmetic .add rSSC rT1 rONE]
  | 20 => wordBitsBlock rOW rMACRO
  | 21 => wordBitsBlock rGLC rMACROS
  | 22 => wordBitsBlock rBAW rBLOCKS
  | 23 => .seq (wordBitsBlock rT1 rBASE)
      (acts [.constant rT2 3, .arithmetic .mul rT1 rTWO rT1, .arithmetic .add rRW rT1 rT2])
  | 24 => acts [.arithmetic .mul rT1 rOW rMACRO, .arithmetic .mul rLSCNT rMACROS rT1]
  | 25 => acts [.arithmetic .mul rGSCNT rGLC rMACROS]
  | 26 => .seq (log2Block rT1 rM2)
      (acts [.constant rT2 8, .arithmetic .div rT1 rT1 rT2, .arithmetic .add rCB rT1 rONE])
  | 27 => acts [.arithmetic .shl rT1 rONE rCB, .arithmetic .add rT2 rCB rONE,
      .arithmetic .mul rT3 rT2 rT2, .arithmetic .mul rFROWS rT1 rT3]
  | 28 => .seq (acts [.arithmetic .mul rT1 rTWO rCB, .arithmetic .add rT1 rT1 rONE,
        .arithmetic .mul rT3 rTWO rCB, .arithmetic .add rT3 rT3 rTWO,
        .arithmetic .add rT2 rCB rONE, .arithmetic .mul rT3 rT3 rT2,
        .arithmetic .mul rT1 rT1 rT3])
      (wordBitsBlock rFWID rT1)
  | 29 => acts [.arithmetic .shl rT1 rONE rCB, .arithmetic .add rT2 rCB rONE,
      .arithmetic .mul rSROWS rT1 rT2]
  | 30 => .seq (acts [.arithmetic .add rT1 rCB rONE]) (wordBitsBlock rSWID rT1)
  | 31 => acts [.arithmetic .mul rT1 rSSC rWS, .arithmetic .mul rT2 rBLOCKS rRW,
      .constant rT3 3, .arithmetic .mul rT2 rT3 rT2, .arithmetic .add rT1 rT1 rT2,
      .arithmetic .mul rT2 rLSCNT rOW, .arithmetic .add rT1 rT1 rT2,
      .arithmetic .mul rT2 rGSCNT rBAW, .arithmetic .add rT1 rT1 rT2,
      .arithmetic .mul rT2 rLDOM rLWID, .arithmetic .add rT1 rT1 rT2,
      .arithmetic .mul rT2 rGDOM rGWID, .arithmetic .add rIBITS rT1 rT2]
  | 32 => acts [.arithmetic .mul rFBITS rFROWS rFWID]
  | 33 => acts [.arithmetic .mul rCBITS rSROWS rSWID]
  | 34 => acts [.arithmetic .div rT1 rM2 rWS, .arithmetic .mul rT2 rEL rEL,
      .arithmetic .mul rT2 rEL rT2, .arithmetic .mul rQ rT1 rT2]
  | 35 => acts [.arithmetic .div rR rM2 rEL]
  | 36 => acts [.constant rT1 1180, .arithmetic .mul rT1 rT1 rQ, .constant rT2 513,
      .arithmetic .mul rT2 rT2 rR, .arithmetic .add rT1 rT1 rT2, .constant rT2 561,
      .arithmetic .add rAO rT1 rT2]
  | 37 => .seq (acts [.arithmetic .add rT1 rM2 rAO, .arithmetic .add rT1 rT1 rIBITS,
        .arithmetic .add rT1 rT1 rFBITS, .arithmetic .add rT1 rT1 rCBITS,
        .arithmetic .add rT1 rT1 rTWO])
      (wordBitsBlock rOLDW rT1)
  | 38 => acts [.constant rT1 8, .arithmetic .mul rT1 rT1 rOLDW, .constant rT2 32,
      .arithmetic .add rWW rT2 rT1]
  | _ => .skip

/-- The first `k` bank steps in order. -/
def geoChain : Nat → Block
  | 0 => .skip
  | k + 1 => .seq (geoChain k) (geoStepBlock k)

/-- The whole size-only geometry prelude after the constants: the interior
subset, then the 39 bank steps (registers 38-76). -/
def geometryPrelude : Block := .seq interiorGeometryBlock (geoChain 39)

end Builder

end RMQ.SuccinctFinal.PackedConstruction

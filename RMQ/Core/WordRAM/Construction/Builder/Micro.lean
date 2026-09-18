import RMQ.Core.WordRAM.Construction.Builder.Access

/-! # PRE-1 builder: the two microtables

Program text only (inside the builder firewall). Both tables are indexed by
chunk patterns of `c = regs 64` bits. A fringe row decodes its slot into the
pattern `v`, the range start `a` and the range end `b`, scans the `c + 1`
prefix offsets of the pattern once keeping the offset-encoded excess, the
leftmost minimum over `[a, b)` (the start `a` when the range is empty) and the
final excess, and packs `(delta * (2c + 2) + min) * (c + 1) + arg`. A
select-chunk row decodes its slot into `v` and a rank `k` and scans the `c`
pattern bits for the close of rank `k`, defaulting to `c`. Every update is
branch-free arithmetic on comparison results.

The registers of this phase (200-219) are declared here.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-! ## Phase registers: microtables -/

/-- `c + 1`. -/
abbrev rCP1 : Operand := 200
/-- `(c + 1) * (c + 1)`. -/
abbrev rSQ : Operand := 201
/-- Remaining pattern bits of a fringe row. -/
abbrev rFV : Operand := 202
/-- Fringe range start `a`. -/
abbrev rFA : Operand := 203
/-- Fringe range end `b`. -/
abbrev rFB : Operand := 204
/-- Offset-encoded prefix excess. -/
abbrev rFE : Operand := 205
/-- Best (leftmost minimum) offset. -/
abbrev rFBP : Operand := 206
/-- Excess at the best offset. -/
abbrev rFBV : Operand := 207
/-- Scan offset. -/
abbrev rFT : Operand := 208
/-- Scan guard. -/
abbrev rFTGO : Operand := 209
/-- Scratch. -/
abbrev rF1 : Operand := 210
/-- Scratch. -/
abbrev rF2 : Operand := 211
/-- Scratch. -/
abbrev rF3 : Operand := 212
/-- Scratch. -/
abbrev rF4 : Operand := 213
/-- Remaining pattern bits of a select-chunk row. -/
abbrev rSX : Operand := 214
/-- Select rank `k`. -/
abbrev rSK : Operand := 215
/-- Closes seen so far. -/
abbrev rSC : Operand := 216
/-- Selected position (default `c`). -/
abbrev rSPOS : Operand := 217

/-! ## Fringe rows -/

/-- Decode a fringe slot: `v = slot / (c + 1)²`, `a = slot / (c + 1) % (c + 1)`,
`b = slot % (c + 1)`; start the excess at the offset `c`. -/
def fringeDecodeActs : List Action :=
  [.arithmetic .add rCP1 rCB rONE, .arithmetic .mul rSQ rCP1 rCP1,
    .arithmetic .div rFV rSLOT rSQ, .arithmetic .div rFA rSLOT rCP1,
    .arithmetic .mod rFA rFA rCP1, .arithmetic .mod rFB rSLOT rCP1,
    .move rFE rCB, .constant rFBP 0, .constant rFBV 0]

/-- One scan offset `t`: take `t` as the best when `t = a`, or when `a < t < b`
and its excess is strictly smaller; then, below `c`, consume one pattern bit. -/
def fringeStepBlock : Block :=
  acts [.comparison .eq rF1 rFT rFA, .comparison .lt rF2 rFA rFT,
    .comparison .lt rF3 rFT rFB, .arithmetic .mul rF2 rF2 rF3,
    .comparison .lt rF3 rFE rFBV, .arithmetic .mul rF2 rF2 rF3,
    .arithmetic .add rF1 rF1 rF2, .arithmetic .sub rF2 rONE rF1,
    .arithmetic .mul rF3 rF1 rFE, .arithmetic .mul rF4 rF2 rFBV, .arithmetic .add rFBV rF3 rF4,
    .arithmetic .mul rF3 rF1 rFT, .arithmetic .mul rF4 rF2 rFBP, .arithmetic .add rFBP rF3 rF4,
    .comparison .lt rF1 rFT rCB, .arithmetic .mod rF2 rFV rTWO,
    .arithmetic .div rFV rFV rTWO, .arithmetic .mul rF2 rF2 rTWO,
    .arithmetic .mul rF2 rF2 rF1, .arithmetic .add rFE rFE rF2,
    .arithmetic .sub rFE rFE rF1]

/-- A fringe row: decode, scan the `c + 1` offsets, pack. -/
def fringeEntryBlock : Block :=
  .seq (acts fringeDecodeActs)
  (.seq (forSlots rFT rFTGO rCP1 fringeStepBlock)
    (acts [.arithmetic .add rF1 rCP1 rCP1, .arithmetic .mul rF1 rFE rF1,
      .arithmetic .add rF1 rF1 rFBV, .arithmetic .mul rF1 rF1 rCP1,
      .arithmetic .add rENT rF1 rFBP]))

/-! ## Select-chunk rows -/

/-- Decode a select slot: `v = slot / (c + 1)`, `k = slot % (c + 1)`; no close
seen, position `c`. -/
def selectDecodeActs : List Action :=
  [.arithmetic .add rCP1 rCB rONE, .arithmetic .div rSX rSLOT rCP1,
    .arithmetic .mod rSK rSLOT rCP1, .constant rSC 0, .move rSPOS rCB]

/-- One pattern bit at offset `t`: a close whose rank is `k` sets the position;
every close advances the count. -/
def selectStepBlock : Block :=
  acts [.arithmetic .mod rF1 rSX rTWO, .arithmetic .div rSX rSX rTWO,
    .arithmetic .sub rF1 rONE rF1, .comparison .eq rF2 rSC rSK,
    .arithmetic .mul rF2 rF2 rF1, .arithmetic .sub rF3 rONE rF2,
    .arithmetic .mul rF4 rF2 rFT, .arithmetic .mul rF3 rF3 rSPOS,
    .arithmetic .add rSPOS rF4 rF3, .arithmetic .add rSC rSC rF1]

/-- A select-chunk row: decode, scan the `c` pattern bits, return the position. -/
def selectEntryBlock : Block :=
  .seq (acts selectDecodeActs)
  (.seq (forSlots rFT rFTGO rCB selectStepBlock)
    (acts [.move rENT rSPOS]))

/-! ## Both tables -/

/-- The fringe table, then the select-chunk table, in payload order. -/
def microtablesBlock : Block :=
  .seq (emitTable rFROWS rFWID fringeEntryBlock) (emitTable rSROWS rSWID selectEntryBlock)

end Builder

end RMQ.SuccinctFinal.PackedConstruction

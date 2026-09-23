import RMQ.Core.WordRAM.Construction.Builder.Micro
import RMQ.Core.WordRAM.Construction.Builder.Cartesian

/-! # PRE-1 builder: the bit buffer, header patch and paddings

Program text only (inside the builder firewall). The buffer starts with `oldW`
zero cells reserved for the old header (`headerReserveBlock`, base in register
220). After the BP code, the access half, the interior close and the two
microtables, `headerPatchBlock` stores the `oldW` little-endian bits of the long
count (register 177) into those cells. `padBlock` measures the serialized
length by reserving one zero probe cell, computes the old cell bits
`(1 + ceilDiv (L - oldW) oldW) * oldW` and the dense bits
`ceilDiv oldBits W * W`, and appends the zeros that remain after the probe.

The registers of this phase (220-228) are declared here.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-! ## Phase registers: buffer finish -/

/-- Buffer base: the first header cell. -/
abbrev rBUF : Operand := 220
/-- Remaining header value bits. -/
abbrev rHX : Operand := 221
/-- Header bit index. -/
abbrev rHI : Operand := 222
/-- Header loop guard. -/
abbrev rHIGO : Operand := 223
/-- The probe cell (serialized length measure). -/
abbrev rPROBE : Operand := 224
/-- Zeros still to append. -/
abbrev rPAD : Operand := 225
/-- Scratch. -/
abbrev rH1 : Operand := 226
/-- Scratch. -/
abbrev rH2 : Operand := 227
/-- Dense bits `denseCount * W`. -/
abbrev rDB : Operand := 228

/-! ## Blocks -/

/-- Reserve `oldW` zero cells for the header; their base goes to `rBUF`, and the
BP base `rBPB` is the cell right after them. -/
def headerReserveBlock : Block :=
  .seq (acts [.arithmetic .sub rH1 rOLDW rONE])
    (.seq (reserveArray rBUF rH1) (acts [.arithmetic .add rBPB rBUF rOLDW]))

/-- Header bit `i`: `HDR[i] := x % 2`, `x := x / 2`. -/
def headerPatchStepBlock : Block :=
  acts [.arithmetic .add rADDR rBUF rHI, .arithmetic .mod rH1 rHX rTWO, .store rADDR rH1,
    .arithmetic .div rHX rHX rTWO]

/-- Store `natToBitsLE oldW lc` into the header cells. -/
def headerPatchBlock : Block :=
  .seq (acts [.move rHX rLCNT]) (forSlots rHI rHIGO rOLDW headerPatchStepBlock)

/-- Append `regs cnt` zero cells. -/
def zerosBlock (cnt : Operand) : Block :=
  .seq (acts [.move rECNT cnt])
    (.loop rECNT (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))))

/-- Measure the serialized length with a zero probe cell and pad to the dense
bits: `L = probe - buf`, `oldBits = (1 + ceilDiv (L - oldW) oldW) * oldW`,
`denseBits = ceilDiv oldBits W * W`, then `denseBits - L - [L < denseBits]`
further zeros. -/
def padBlock : Block :=
  .seq (acts [.reserve rPROBE, .store rPROBE rZERO,
    .arithmetic .sub rH1 rPROBE rBUF,
    .arithmetic .sub rH2 rH1 rOLDW, .arithmetic .add rH2 rH2 rOLDW,
    .arithmetic .sub rH2 rH2 rONE, .arithmetic .div rH2 rH2 rOLDW,
    .arithmetic .add rH2 rH2 rONE, .arithmetic .mul rH2 rH2 rOLDW,
    .arithmetic .add rDB rH2 rWW, .arithmetic .sub rDB rDB rONE,
    .arithmetic .div rDB rDB rWW, .arithmetic .mul rDB rDB rWW,
    .arithmetic .sub rPAD rDB rH1, .comparison .lt rH2 rH1 rDB,
    .arithmetic .sub rPAD rPAD rH2])
    (zerosBlock rPAD)

/-- The buffer after the Cartesian pass: header cells, BP code, access half,
interior close, microtables, header patch, paddings. -/
def bufferBlock : Block :=
  .seq headerReserveBlock (.seq bpEmitBlock (.seq accessHalfBlock (.seq interiorCloseBlock
    (.seq microtablesBlock (.seq headerPatchBlock padBlock)))))

end Builder

end RMQ.SuccinctFinal.PackedConstruction

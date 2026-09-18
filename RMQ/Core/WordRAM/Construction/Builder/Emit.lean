import RMQ.Core.WordRAM.Construction.Builder.Registers

/-! # PRE-1 builder: reusable emission and arithmetic source blocks

Program text only (inside the builder firewall). The bit buffer holds one
numeric cell per emitted bit: `emitBit src` reserves a fresh cell and stores the
0/1 value of register `src` into it (`reserve` does not initialize). `emitBits`
emits the `w`-bit little-endian encoding of a register by repeated `mod 2` and
`div 2`, least significant bit first. `emitTable count width entry` runs
`entry` for every slot `0 ≤ slot < count` (the entry block reads `rSLOT` and
leaves its value in `rENT`) and emits each value at `width` bits. `log2Block`
is the halving loop. Their specifications are proved outside the firewall.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-- A right-nested sequence of actions. -/
def acts : List Action → Block
  | [] => .skip
  | [a] => .action a
  | a :: b :: rest => .seq (.action a) (acts (b :: rest))

/-- Reserve one fresh cell and store register `src` into it. -/
def emitBit (src : Operand) : Block :=
  .seq (.action (.reserve rCUR)) (.action (.store rCUR src))

/-- One round of `emitBits`: emit the low bit of `rEVAL`, halve it, count down. -/
def emitBitsBody : Block :=
  acts [.arithmetic .mod rBIT rEVAL rTWO, .reserve rCUR, .store rCUR rBIT,
    .arithmetic .div rEVAL rEVAL rTWO, .arithmetic .sub rECNT rECNT rONE]

/-- Emit the `regs w`-bit little-endian encoding of `regs v`. -/
def emitBits (w v : Operand) : Block :=
  .seq (acts [.move rECNT w, .move rEVAL v]) (.loop rECNT emitBitsBody)

/-- The per-slot body of `emitTable`: entry, emission, advance, retest. -/
def emitTableBody (count w : Operand) (entry : Block) : Block :=
  .seq entry (.seq (emitBits w rENT)
    (acts [.arithmetic .add rSLOT rSLOT rONE, .comparison .lt rGO rSLOT count]))

/-- Emit `regs count` entries, slot by slot, each at `regs w` bits. -/
def emitTable (count w : Operand) (entry : Block) : Block :=
  .seq (acts [.constant rSLOT 0, .comparison .lt rGO rSLOT count])
    (.loop rGO (emitTableBody count w entry))

/-- One round of the halving loop. -/
def log2Body (dst : Operand) : Block :=
  acts [.arithmetic .div rLX rLX rTWO, .arithmetic .add dst dst rONE,
    .comparison .lt rLC rONE rLX]

/-- `regs dst := Nat.log2 (regs src)` by repeated halving. -/
def log2Block (dst src : Operand) : Block :=
  .seq (acts [.move rLX src, .constant dst 0, .comparison .lt rLC rONE rLX])
    (.loop rLC (log2Body dst))

/-- `for i := 0 while i < regs cnt do (body; i := i + 1)`, with guard register `go`. -/
def forSlots (i go cnt : Operand) (body : Block) : Block :=
  .seq (acts [.constant i 0, .comparison .lt go i cnt])
    (.loop go (.seq body (acts [.arithmetic .add i i rONE, .comparison .lt go i cnt])))

/-- Append `regs cnt + 1` zero cells and leave the address of the first in `base`. -/
def reserveArray (base cnt : Operand) : Block :=
  .seq (acts [.reserve base, .store base rZERO, .move rECNT cnt])
    (.loop rECNT (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))))

end Builder

end RMQ.SuccinctFinal.PackedConstruction

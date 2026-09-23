import RMQ.Core.WordRAM.Construction.Builder.Interior

/-! # PRE-1 builder: Cartesian stack pass and BP emission

Program text only (inside the builder firewall). The stack pass keeps the
right spine of the Cartesian tree of the processed prefix as a stack of input
indices, and for every spine node the inorder index of its leftmost
descendant. For input index `i` it pops while `xs[i] < xs[top]` (strictly, so
equal keys stay on the stack and ties resolve leftmost), asking the leaf block
for every comparison (index `i` in register 4, the top index in register 5,
result in register 6). If something was popped, the open count of the last
popped node's leftmost descendant grows by one and that descendant becomes the
leftmost descendant of `i`; otherwise `i` gets count 1 and is its own leftmost
descendant. The BP emission then writes, for every index, its open count many
1-cells followed by one 0-cell into the bit buffer. Specifications are proved
outside the firewall.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-- The three stack-pass arrays, `n + 1` zero cells each. -/
def stackArraysBlock : Block :=
  .seq (reserveArray rSTK rN) (.seq (reserveArray rLDB rN) (reserveArray rCNTB rN))

/-- `rWG := [sp ≠ 0 ∧ xs[i] < xs[stack top]]`, leaving the top index in `rTOP`. -/
def popGuardBlock (leaf : Block) : Block :=
  .ifZero rSTKH (acts [.constant rWG 0])
    (.seq (acts [.arithmetic .add rADDR rSTK rSTKH, .arithmetic .sub rADDR rADDR rONE,
        .load rTOP rADDR, .move rLEAF_I rI, .move rLEAF_J rTOP])
      (.seq leaf (acts [.move rWG rLEAF_RES])))

/-- One pop, then the next guard. -/
def popBodyBlock (leaf : Block) : Block :=
  .seq (acts [.move rLAST rTOP, .arithmetic .sub rSTKH rSTKH rONE, .constant rPOP 1])
    (popGuardBlock leaf)

/-- Record the open count and the leftmost descendant of the new node `i`. -/
def linkBlock : Block :=
  .ifZero rPOP
    (acts [.arithmetic .add rADDR rLDB rI, .store rADDR rI,
      .arithmetic .add rADDR rCNTB rI, .store rADDR rONE])
    (acts [.arithmetic .add rADDR rLDB rLAST, .load rTMP rADDR,
      .arithmetic .add rADDR rCNTB rTMP, .load rCC rADDR, .arithmetic .add rCC rCC rONE,
      .store rADDR rCC, .arithmetic .add rADDR rLDB rI, .store rADDR rTMP])

/-- Push `i`. -/
def pushBlock : Block :=
  acts [.arithmetic .add rADDR rSTK rSTKH, .store rADDR rI, .arithmetic .add rSTKH rSTKH rONE]

/-- Insert input index `i`. -/
def stackStepBlock (leaf : Block) : Block :=
  .seq (acts [.constant rPOP 0])
    (.seq (popGuardBlock leaf)
      (.seq (.loop rWG (popBodyBlock leaf))
        (.seq linkBlock pushBlock)))

/-- Pass 1: the monotone stack over all `n` input indices. -/
def stackPassBlock (leaf : Block) : Block :=
  .seq (acts [.constant rSTKH 0]) (forSlots rI rIGO rN (stackStepBlock leaf))

/-- The BP unit of index `j`: `count[j]` many 1-cells, then one 0-cell. -/
def bpUnitBlock : Block :=
  .seq (acts [.arithmetic .add rADDR rCNTB rJ, .load rCC rADDR])
    (.seq (.loop rCC (.seq (emitBit rONE) (acts [.arithmetic .sub rCC rCC rONE])))
      (emitBit rZERO))

/-- Pass 2: the BP code from the open counts. -/
def bpEmitBlock : Block := forSlots rJ rJGO rN bpUnitBlock

end Builder

end RMQ.SuccinctFinal.PackedConstruction

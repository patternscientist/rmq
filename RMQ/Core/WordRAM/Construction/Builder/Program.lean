import RMQ.Core.WordRAM.Construction.Builder.Output

/-! # PRE-1 builder: program host module

Program text only (inside the builder firewall). Contract clause V3-1 places the
builder's public constants in this module; clause V3-3 fixes both leaves as
literal five-action sequences and both constants as the compiled template
followed by `halt 3`. `builderBody leaf` runs the constants, the geometry
prelude, the arrays, the Cartesian stack pass with the bit buffer, and the
output phase; `builderSource leaf` prefixes the header load. The fuel function
has the body fixed by clause V3-6 as amended by V3-6a (`D + C * n`), and the two
extraction functions have exactly the V3-6 bodies.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

open Structured

/-- Comparison-oracle leaf: `regs 6 := [keys (regs 4) < keys (regs 5)]`, padded
to five actions with two charged no-op moves (V2-2, V3-3). -/
def keyLeaf : Block :=
  .seq (.action (.loadKey 0 4)) (.seq (.action (.loadKey 1 5))
    (.seq (.action (.compareKey 6 0 1)) (.seq (.action (.move 6 6))
      (.action (.move 6 6)))))

/-- Word-model leaf: `regs 6 := [memory (regs 4 + 1) < memory (regs 5 + 1)]`. -/
def wordLeaf : Block :=
  .seq (.action (.arithmetic .add 7 4 2)) (.seq (.action (.load 7 7))
    (.seq (.action (.arithmetic .add 8 5 2)) (.seq (.action (.load 8 8))
      (.action (.comparison .lt 6 7 8)))))

/-- The builder after the header load: constants, geometry prelude, arrays,
stack pass and bit buffer, output. -/
def builderBody (leaf : Block) : Block :=
  .seq Builder.constantsBlock (.seq Builder.geometryPrelude (.seq Builder.arraysBlock
    (.seq (.seq Builder.stackArraysBlock (.seq (Builder.stackPassBlock leaf) Builder.bufferBlock))
      Builder.outputBlock)))

/-- The whole builder source: the header load, then the body (V3-3). -/
def builderSource (leaf : Block) : Block := .seq (.action (.load 1 0)) (builderBody leaf)

/-- The comparison-oracle program constant (V2-2, V3-3). -/
def builderProgram : List BInstr := (builderSource keyLeaf).compileAt 0 ++ [⟨.halt 3⟩]

/-- The word-model program constant (V2-2, V3-3). -/
def builderProgramWord : List BInstr := (builderSource wordLeaf).compileAt 0 ++ [⟨.halt 3⟩]

/-- The fuel function (V3-6 as amended by V3-6a): `D + C * n`. -/
def builderBudget (n : Nat) : Nat := 1000000000 + 1000000000 * n

/-- The emitted output of the comparison-oracle run (V3-6). -/
def efficientBuild (xs : List Int) : List Nat :=
  match (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status with
  | .halted outBase =>
      emitted (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final outBase
        ((run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.extent - outBase)
  | _ => []

/-- The emitted output of the word-model run at encoding width `width` (V3-6). -/
def efficientBuildWord (width : Nat) (xs : List Int) : List Nat :=
  match (run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final.status with
  | .halted outBase =>
      emitted (run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final outBase
        ((run builderProgramWord (builderBudget xs.length) (wordInputState width xs)).final.extent - outBase)
  | _ => []

end RMQ.SuccinctFinal.PackedConstruction

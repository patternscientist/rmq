import RMQ.Core.WordRAM.Construction.Controls
import RMQ.Core.WordRAM.Construction.Conservative

/-! # C1-C4 construction contract prerequisites

The theorem in this file certifies primitive and input prerequisites only.
It neither supplies a construction program nor proves an efficient builder.
Default proofs are proof-only; independent exact-type consumers project every
field so deleting or weakening one cannot silently retain certification.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- The eventual literal-pinned program must inhabit this schema. Its family
quantifies over every ordinary input, not only inputs passing readiness tests.
No inhabitant is claimed to construct an RMQ allocation in this phase. -/
structure ProgramContract (program : Program) (family : List Int → Program)
    (instructionLiteral encodedWordLiteral : Nat) : Prop where
  uniform : Uniform program family
  lengthPinned : program.length = instructionLiteral
  encodedPinned : programWords program = encodedWordLiteral
  codeBits : ∀ width, CodeAccounting program width (encodedWordLiteral * width)

/-- Obligations that are established before any builder construction. -/
structure ContractPrerequisites : Prop where
  reflection : ∀ i s, bstep i s = interpretPrims i.semantics s := bstep_reflects
  workCap : ∀ i : BInstr, i.semantics.length ≤ 1 := semantics_cap
  constantCap : ∀ (i : BInstr) (p : Prim), p ∈ i.semantics → ∀ c ∈ p.constants,
    ∀ width, 32 ≤ width → c.val < 2 ^ width := constants_fit_width
  headerRead : ∀ width xs,
    ((bstep headerInstruction (wordInputState width xs)).regs 1 = xs.length ∧
      (bstep headerInstruction (wordInputState width xs)).status = .running) ∧
    (bstep headerInstruction
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).status = .fault :=
    fun width xs => ⟨header_read width xs, missing_header_fault width xs⟩
  pointwise : ∀ width xs i,
    encodeInput width xs (i + 1) = (xs[i]?).map (encodeInt width) := encodeInput_succ
  oracleControl : ¬ ∃ ps : List Prim,
    ps.length ≤ primCap ∧ ∀ s, interpretPrims ps s = oracleSemantics s := oracle_not_reflected
  uniformControl : ¬ ∃ program, Uniform program bakedProgram := baked_not_uniform
  writeValue : ∀ address value s, s.regs address < s.extent →
    (execPrim (.store address value) s).memory (s.regs address) = some (s.regs value) :=
    store_value_from_prestate
  freshReserve : ∀ s, CleanTail s → ∀ dst,
    (execPrim (.reserve dst) s).memory s.extent = none := reserve_fresh
  codeAccounting : ∀ program width,
    CodeAccounting program width (programWords program * width) := code_accounting_exact

theorem contractPrerequisites_holds : ContractPrerequisites := {}

end RMQ.SuccinctFinal.PackedConstruction

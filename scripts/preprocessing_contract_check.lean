import RMQ.Core.WordRAM.Construction.Contract
import RMQ.Core.WordRAM.Construction.Conservative import Lean

/-! Independent exact-type consumers of the C1-C4 certificate and its input
and terminal-state interfaces. These types do not adapt to certificate edits. -/

namespace PRE1ContractConsumer
open RMQ.SuccinctFinal.PackedConstruction

theorem reflection : ∀ i s, bstep i s = interpretPrims i.semantics s :=
  contractPrerequisites_holds.reflection
theorem workCap : ∀ i : BInstr, i.semantics.length ≤ 1 :=
  contractPrerequisites_holds.workCap
theorem constantCap : ∀ (i : BInstr) (p : Prim), p ∈ i.semantics → ∀ c ∈ p.constants,
    ∀ width, 32 ≤ width → c.val < 2 ^ width := contractPrerequisites_holds.constantCap
theorem headerRead : ∀ width xs,
    ((bstep headerInstruction (wordInputState width xs)).regs 1 = xs.length ∧
      (bstep headerInstruction (wordInputState width xs)).status = .running) ∧
    (bstep headerInstruction
      { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).status = .fault :=
  contractPrerequisites_holds.headerRead
theorem pointwise : ∀ width xs i,
    encodeInput width xs (i + 1) = (xs[i]?).map (encodeInt width) :=
  contractPrerequisites_holds.pointwise
theorem oracleControl : ¬ ∃ ps : List Prim,
    ps.length ≤ primCap ∧ ∀ s, interpretPrims ps s = oracleSemantics s :=
  contractPrerequisites_holds.oracleControl
theorem uniformControl : ¬ ∃ program, Uniform program bakedProgram :=
  contractPrerequisites_holds.uniformControl
theorem writeValue : ∀ address value s, s.regs address < s.extent →
    (execPrim (.store address value) s).memory (s.regs address) = some (s.regs value) :=
  contractPrerequisites_holds.writeValue
theorem freshReserve : ∀ s, CleanTail s → ∀ dst,
    (execPrim (.reserve dst) s).memory s.extent = none :=
  contractPrerequisites_holds.freshReserve
theorem codeAccounting : ∀ program width,
    CodeAccounting program width (programWords program * width) :=
  contractPrerequisites_holds.codeAccounting

theorem accounting_definition (program : Program) (width bits : Nat)
    (h : CodeAccounting program width bits) :
    bits = ((program.map (fun i => i.primitive.constants)).flatten).length * width := h
theorem encoded_length_definition (program : Program) :
    programWords program = ((program.map (fun i => i.primitive.constants)).flatten).length := rfl

theorem program_uniform (program : Program) (family : List Int → Program) (k b : Nat)
    (h : ProgramContract program family k b) : ∀ xs, family xs = program := h.uniform
theorem program_length (program : Program) (family : List Int → Program) (k b : Nat)
    (h : ProgramContract program family k b) : program.length = k := h.lengthPinned
theorem program_encoding (program : Program) (family : List Int → Program) (k b : Nat)
    (h : ProgramContract program family k b) : programWords program = b := h.encodedPinned
theorem program_accounting (program : Program) (family : List Int → Program) (k b : Nat)
    (h : ProgramContract program family k b) :
    ∀ width, CodeAccounting program width (b * width) := h.codeBits

theorem signed_order : ∀ {width : Nat} {x y : Int}, SignedFits width x → SignedFits width y →
    (encodeInt width x < encodeInt width y ↔ x < y) := encodeInt_lt_iff
theorem signed_width : ∀ {width : Nat} {x : Int}, SignedFits width x →
    encodeInt width x < 2 ^ width := encodeInt_lt_capacity
theorem input_all_sizes : ∀ n, InputFits (n + 2) (List.replicate n (0 : Int)) := inputFits_all_sizes
theorem oracle_header : ∀ xs,
    (bstep headerInstruction (comparisonInputState xs)).regs 1 = xs.length ∧
    (bstep headerInstruction (comparisonInputState xs)).status = .running := comparison_header_read
theorem oracle_missing_header : ∀ xs,
    (bstep headerInstruction
      { comparisonInputState xs with memory := put (comparisonInputState xs).memory 0 none }).status =
      .fault := comparison_missing_header_fault
theorem terminal_fault : ∀ i s, s.status = .fault → checkedStep i s = none := checkedStep_fault
theorem terminal_halted : ∀ i s v, s.status = .halted v → checkedStep i s = none := checkedStep_halted
theorem replay_fake :
    ¬ Replays (fun _ => none) [(0, 0)] (put (fun _ => none) 1 (some 7)) := fabricated_replay_rejected

example : oracleBPWord (comparisonInputState [0, 1]) = 5 := oracle_increasing
example : oracleBPWord (comparisonInputState [1, 0]) = 3 := oracle_decreasing
example : oracleBPWord (comparisonInputState [1, 1]) = 5 := oracle_equal
example : encodeInput 8 [] 0 = some 0 := encodeInput_header 8 []
example : encodeInput 8 [-128] 1 = some 0 := by decide
example : encodeInput 8 [127] 1 = some 255 := by decide
example : ¬ SignedFits 8 128 := by unfold SignedFits; decide

theorem conservative_step (memory : RMQ.SuccinctFinal.PackedWordRAM.Memory)
    (i : Conservative.OldInstruction) (hfit : i.Fits 32) (s : Conservative.OldState)
    (hrun : s.status = .running) :
    execPrim (Conservative.instruction i (Conservative.operandsFit32_of_fits i hfit))
      (Conservative.state memory s) =
        Conservative.state memory (RMQ.SuccinctFinal.PackedWordRAM.execute memory i s).1 :=
  Conservative.execute_eq_of_fits memory i hfit s hrun

#print axioms contractPrerequisites_holds
#print axioms oracle_not_reflected
#print axioms baked_not_uniform
#print axioms header_read
#print axioms encodeInt_lt_iff
#print axioms inputFits_all_sizes
#print axioms reserve_fresh
#print axioms comparison_missing_header_fault
#print axioms Conservative.execute_eq_of_fits
/-! ## Verdict marker (audit PRE-1-A1C P3-1; repair PRE-1-R2 of audit PRE-1-A2 P2-1, contract amendment)

The exit code is the verdict. The marker is printed if and only if (1) the whole
file elaborates with no error-severity message and (2) `consumerWitness`, which
refers to each declaration above and restates each example, exists and collects
no `sorryAx`; otherwise nothing is printed and no diagnostic is added, so the
failing line set of a rejected mutation stays exactly the lines above. Lean 4.22
resets the command state's message log before every command
(`Lean.Language.Lean.process.doElab` sets `messages := .empty`), so this command
cannot read an earlier command's errors from its own state. For the whole-file
condition it elaborates the file a second time in this process from the source
text of its own input context, with only this command blanked (line breaks
kept), through `Lean.Parser.parseHeader`, `Lean.Elab.processHeader` and
`Lean.Elab.IO.processCommands`, which collects the message logs of every command
snapshot, and requires `MessageLog.hasErrors` to be false for the header and for
those messages: the predicate by which the frontend decides the exit code. An
error in any command kind (a declaration, an anonymous example, a `#guard` or
`run_cmd` check, a missing declaration after a maximum-recursion-depth failure,
or a command after this one) therefore suppresses the marker. -/

def consumerWitness : Unit :=
  let _ := @reflection
  let _ := @workCap
  let _ := @constantCap
  let _ := @headerRead
  let _ := @pointwise
  let _ := @oracleControl
  let _ := @uniformControl
  let _ := @writeValue
  let _ := @freshReserve
  let _ := @codeAccounting
  let _ := @accounting_definition
  let _ := @encoded_length_definition
  let _ := @program_uniform
  let _ := @program_length
  let _ := @program_encoding
  let _ := @program_accounting
  let _ := @signed_order
  let _ := @signed_width
  let _ := @input_all_sizes
  let _ := @oracle_header
  let _ := @oracle_missing_header
  let _ := @terminal_fault
  let _ := @terminal_halted
  let _ := @replay_fake
  let _ := @conservative_step
  let _ : oracleBPWord (comparisonInputState [0, 1]) = 5 := oracle_increasing
  let _ : oracleBPWord (comparisonInputState [1, 0]) = 3 := oracle_decreasing
  let _ : oracleBPWord (comparisonInputState [1, 1]) = 5 := oracle_equal
  let _ : encodeInput 8 [] 0 = some 0 := encodeInput_header 8 []
  let _ : encodeInput 8 [-128] 1 = some 0 := by decide
  let _ : encodeInput 8 [127] 1 = some 255 := by decide
  let _ : ¬ SignedFits 8 128 := by unfold SignedFits; decide
  ()

open Lean Elab Command in
#eval show CommandElabM Unit from do
  -- (1) Whole file: elaborate this file again in this process from its own
  -- source text, with only this command blanked (line breaks kept), and read
  -- the message log of the header and of every command.
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)
    context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)
    (mainModule := (← getEnv).mainModule)
  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors
  -- (2) The witness exists and collects no `sorryAx`.
  let witness := `PRE1ContractConsumer.consumerWitness
  let witnessClean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if fileClean && witnessClean then IO.println "PRE1-CONTRACT-TYPED-CONSUMERS PASS"
end PRE1ContractConsumer

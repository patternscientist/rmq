"""Apply the PRE-1-R2 verdict-marker edits to LF drafts of the five consumers."""
import re
import sys
import textwrap

sys.path.insert(0, '.')
from marker_block import marker_command

I = sys.argv[1].rstrip('/') + '/'
HYGIENE = re.compile(r'\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib')


def rewrite(path, pairs):
    text = open(I + path, encoding='utf-8', newline='').read()
    assert '\r' not in text
    for old, new in pairs:
        assert text.count(old) == 1, (path, old[:80])
        text = text.replace(old, new)
    open(I + path, 'w', encoding='utf-8', newline='\n').write(text)
    return text


def doc(header, conditions, otherwise):
    body = ("The exit code is the verdict. The marker is printed if and only if " + conditions + "; " + otherwise +
            " Lean 4.22 resets the command state's message log before every command "
            "(`Lean.Language.Lean.process.doElab` sets `messages := .empty`), so this command cannot read an "
            "earlier command's errors from its own state. For the whole-file condition it elaborates the file a "
            "second time in this process from the source text of its own input context, with only this command "
            "blanked (line breaks kept), through `Lean.Parser.parseHeader`, `Lean.Elab.processHeader` and "
            "`Lean.Elab.IO.processCommands`, which collects the message logs of every command snapshot, and "
            "requires `MessageLog.hasErrors` to be false for the header and for those messages: the predicate by "
            "which the frontend decides the exit code. An error in any command kind (a declaration, an anonymous "
            "example, a `#guard` or `run_cmd` check, a missing declaration after a maximum-recursion-depth "
            "failure, or a command after this one) therefore suppresses the marker.")
    return "/-! ## " + header + "\n\n" + textwrap.fill(body, width=80, break_long_words=False, break_on_hyphens=False) + " -/\n"


QUIET = ("otherwise nothing is printed and no diagnostic is added, so the failing line set of a rejected mutation "
         "stays exactly the lines above.")

# 1. Builder consumer.
old_builder_doc = """/-! ## Verdict marker (audit PRE-1-A1C P3-1)

The exit code is the verdict. The marker is printed only when every
declaration above elaborated without `sorry` (`consumerWitness` refers to each
of them) and the `#guard` checks above still hold (`consumerGuards` repeats
them). Otherwise nothing is printed and no diagnostic is added, so the failing
line set of a rejected mutation stays exactly the lines above. -/
"""
new_builder_doc = doc("Verdict marker (audit PRE-1-A1C P3-1; repair PRE-1-R2 of audit PRE-1-A2 P2-1)",
                      "(1) the whole file elaborates with no error-severity message, (2) `consumerWitness`, which "
                      "refers to each declaration above, exists and collects no `sorryAx`, and (3) `consumerGuards`, "
                      "which repeats the `#guard` checks above, holds", QUIET)
old_builder_eval = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let witness := `PRE1BuilderConsumer.consumerWitness
  let clean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if clean && consumerGuards then IO.println "PRE1-BUILDER-TYPED-CONSUMERS PASS"
"""
new_builder_eval = marker_command('PRE1BuilderConsumer.consumerWitness', 'consumerGuards', 'PRE1-BUILDER-TYPED-CONSUMERS PASS')
rewrite('scripts/preprocessing_builder_check.lean', [(old_builder_doc, new_builder_doc), (old_builder_eval, new_builder_eval)])

# 2. Capstone consumer: docstring lines 11-12 (same line count) and the marker command.
old_cap_doc = """here. The marker is printed only when every declaration elaborated without
`sorry`. This file is not imported by `RMQ.lean` (coordinator integration step).
"""
new_cap_doc = """here. The marker is printed only when the whole file elaborates without an error
and the witness is free of `sorryAx`. This file is not imported by `RMQ.lean` (coordinator integration step).
"""
old_cap_head = "/-! ## Verdict marker -/\n"
new_cap_head = doc("Verdict marker (repair PRE-1-R2 of audit PRE-1-A2 P2-1)",
                   "(1) the whole file elaborates with no error-severity message and (2) `consumerWitness`, which "
                   "refers to each declaration above, exists and collects no `sorryAx`", QUIET)
old_cap_eval = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let witness := `RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.consumerWitness
  let clean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if clean then IO.println "PRE1-CAPSTONE-TYPED-CONSUMERS PASS"
"""
new_cap_eval = marker_command('RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.consumerWitness', None, 'PRE1-CAPSTONE-TYPED-CONSUMERS PASS')
cap = rewrite('RMQ/Validation/PreprocessingContract.lean', [(old_cap_doc, new_cap_doc), (old_cap_head, new_cap_head), (old_cap_eval, new_cap_eval)])
for n, line in enumerate(cap.split('\n'), 1):
    if HYGIENE.search(line):
        raise SystemExit('hygiene word in PreprocessingContract.lean line %d: %s' % (n, line))

# 3. Contract consumer.
old_contract_doc = """/-! ## Verdict marker (audit PRE-1-A1C P3-1)

The exit code is the verdict. The marker is printed only when every
declaration above elaborated without `sorry` and the anonymous examples still
check: `consumerWitness` refers to each declaration and restates each example.
Otherwise nothing is printed and no diagnostic is added, so the failing line set
of a rejected mutation stays exactly the lines above. -/
"""
new_contract_doc = doc("Verdict marker (audit PRE-1-A1C P3-1; repair PRE-1-R2 of audit PRE-1-A2 P2-1, contract amendment)",
                       "(1) the whole file elaborates with no error-severity message and (2) `consumerWitness`, which "
                       "refers to each declaration above and restates each example, exists and collects no `sorryAx`",
                       QUIET)
old_contract_eval = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let witness := `PRE1ContractConsumer.consumerWitness
  let clean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if clean then IO.println "PRE1-CONTRACT-TYPED-CONSUMERS PASS"
"""
new_contract_eval = marker_command('PRE1ContractConsumer.consumerWitness', None, 'PRE1-CONTRACT-TYPED-CONSUMERS PASS')
rewrite('scripts/preprocessing_contract_check.lean', [(old_contract_doc, new_contract_doc), (old_contract_eval, new_contract_eval)])

# 4. Spec consumer: `import Lean` appended to the last import line; the marker command.
old_spec_import = "import RMQ.Core.WordRAM.Construction.Spec.Envelope\n"
new_spec_import = "import RMQ.Core.WordRAM.Construction.Spec.Envelope import Lean\n"
old_spec_eval = '#eval IO.println "PRE1-SPEC-TYPED-CONSUMERS PASS"\n'
new_spec_eval = ("\n" + doc("Verdict marker (repair PRE-1-R2 of audit PRE-1-A2 P2-1)",
                            "the whole file elaborates with no error-severity message (this consumer has no witness or "
                            "guard condition; its `#guard` lines are commands of the file)",
                            "otherwise nothing is printed and no diagnostic is added.") + "\n" +
                 marker_command(None, None, 'PRE1-SPEC-TYPED-CONSUMERS PASS'))
rewrite('scripts/preprocessing_spec_check.lean', [(old_spec_import, new_spec_import), (old_spec_eval, new_spec_eval)])

# 5. Stage consumer.
old_stage_doc = """/-! ## Verdict marker (coordinator item before the S8 freeze; same design as the builder
and contract consumers, DD-20260913-PRE1-013)

The exit code is the verdict. The marker is printed only when every
declaration above elaborated without `sorry` (`consumerWitness` refers to each
of them) and every fixture check holds (`stageGuards`, evaluated here once).
A missing or `sorry`-dependent declaration or a failing fixture logs one error
here instead of the marker. -/
"""
new_stage_doc = doc("Verdict marker (coordinator item before the S8 freeze, DD-20260913-PRE1-013; repair PRE-1-R2 of audit PRE-1-A2 P2-1)",
                    "(1) the whole file elaborates with no error-severity message, (2) `consumerWitness`, which refers "
                    "to each declaration above, exists and collects no `sorryAx`, and (3) every fixture check holds "
                    "(`stageGuards`, evaluated here once)",
                    "a missing or `sorryAx`-dependent witnessed declaration or a failing fixture check logs one error "
                    "here instead of the marker, as before, and a failure of (1) alone prints nothing.")
old_stage_eval = """open Lean Elab Command in
#eval show CommandElabM Unit from do
  let witness := `PRE1StageConsumer.consumerWitness
  let clean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if !clean then
    logError "PRE1-STAGE-TYPED-CONSUMERS FAIL: a declaration is missing or depends on sorry"
  else if stageGuards then
    IO.println "PRE1-STAGE-TYPED-CONSUMERS PASS"
  else
    logError "PRE1-STAGE-TYPED-CONSUMERS FAIL: an executable fixture check is false"
"""
new_stage_eval = marker_command('PRE1StageConsumer.consumerWitness', None, 'PRE1-STAGE-TYPED-CONSUMERS PASS', stage_style=True)
rewrite('scripts/preprocessing_stage_check.lean', [(old_stage_doc, new_stage_doc), (old_stage_eval, new_stage_eval)])
print('ok')

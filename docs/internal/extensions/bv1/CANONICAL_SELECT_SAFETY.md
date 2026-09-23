# BV-1 canonical full select safety

Status: CANDIDATE_COMPLETE for this leaf only. Contract frozen before source edits. This worker owns only
`CanonicalSelectSafety.lean`, this evidence file, and its exact temporary
consumer. Governance `0e6a00f654abc64f8b68988fa9675b9a839dca2f` and continuation
checkpoint `645a0502b9da9ad6444edbe44759e1c2c5661f25` remain fixed. Applicable
canonical proof-sprint preflight and completion gate were already applied.
The parent owns all commits, public claims, ledgers and full BV-1 acceptance.

## Frozen theorem and consumer

For every `bits : List Bool`, `target : Bool`, `argument : Nat`, with the sole
premise `argument < 2 ^ Experiment.width bits.length`, prove
`(source .select).Safe (Allocation.memory bits) (Experiment.width bits.length)
  ⟨(initial .select target argument).regs, .running⟩` and
`Controller.SelectExecutionSafety (Allocation.memory bits)
  (Experiment.width bits.length) (program .select)
  ((source .select).size + 1) (initial .select target argument)`.
The direct consumer expands instruction fit, final fit, every indexed
transition's primitive safety and successor fit, every fuel prefix's fit, and
every indexed receipt's address, exact same-memory reply and successful value
fit. It refers to `execute bits .select target argument` and actual
`program .select`, never a controller-only or sibling run.

Composition is actual canonical allocation → memory words/descriptor geometry
→ actual loaded metadata → ControllerSafetyBounds and ReaderSafe plus checked
ReaderSimulation → shared select controller safety → charged setup and target
setup intermediate states → actual complete source → existing compiler safety.
The final theorem has no reader, metadata, geometry, shape or readiness premise.

## Frozen leaf matrix

| ID | Verbatim assigned requirement | Exact evidence and consumer | Boundary challenge | Status |
| --- | --- | --- | --- | --- |
| CSS-FULL | Close actual full (source .select) compiled program safety for all bits,target and representable argument<2^Experiment.width n, including ChargedSetup.setup + targetSetup. | Exact source and compiled propositions above; same source/program/initial/allocation; checked consumer below | Both target branches, empty bits and invalid fitting argument covered universally | CANDIDATE_COMPLETE |
| CSS-BOUNDS | You must derive actual ControllerSafetyBounds for loadedModel from these builders, instantiate physicalReader_safe/ReaderSafe, then source Safe and full compiled all-prefix/positional/backing safety using actual program .select/initial. | loadedModel_safetyBounds and loadedModel_readerSafe consume exact checked canonical exports and actual setup source equalities, for every Operation | Raw0/11/15 lengths, both packet bounds and actual low metadata all retained | CANDIDATE_COMPLETE |
| CSS-NO-PREMISE | No extra uncharged metadata or geometry premises in final endpoint. | Final exact-type consumer has only representability premise | Consumer pins builders and includes full setup, so conditional helper alone cannot typecheck endpoint | CANDIDATE_COMPLETE |
| CSS-CHECK | No Lean without slot | Unique owned narrow build and expected-type/axiom consumer after grant; hygiene and whitespace scans | No shared build overlap; no aggregate; no peer edits | CANDIDATE_COMPLETE |

The inherited BV-1 matrix remains byte-for-byte untouched and OPEN. Applicable
store identity, word/address/operand bounds, primitive execution, same-memory
backing, proof separation and public composition obligations are preserved at
this leaf's exact execution. Canonical semantic values and final capstone
composition remain the parent's separate joins.

## Frozen verification plan

CanonicalMemoryBounds was developed in parallel under disjoint ownership;
its frozen exports are `canonical_memoryWordsFit`,
`canonical_numericReaderGeometry`, and `canonical_scalarHeader_bound`.
CanonicalStoreBounds and CanonicalLimits passed. Source was prepared offline;
checks ran only after explicit shared slot grant using pinned direct v4.22.0 Lake and
`run_command.ps1`, unique stages, one process. Initial warm deadline 180 seconds,
adjust only on observed prerequisite evidence. Check exact expanded consumer
and axiom outputs; run RMQ hygiene scans and whitespace checks. No full build or
aggregate gate for this internal leaf.

## Evidence and digestion

The checked source is 12,395 bytes, SHA-256
`FCBC3B363E47BC16298DEDBDE693921EC4CA45672753AD564161807D6CE7D753`.
The source was unchanged between its clean build and the final consumer.

| Owned stage | Result | Evidence |
| --- | --- | --- |
| canonical-select-safety-1 | FAIL, 24.513 s | First ordinary diagnostic: expand setup's literal List.range19 in size/fields/write proofs, expose canonical width in the FieldsFit hypothesis, and avoid simplifying a Boolean fit power bound prematurely. No timeout. |
| canonical-select-safety-2 | PASS, 21.295 s | Joint narrow build of CanonicalSelectSafety and ScratchFrame; all local warnings repaired. |
| canonical-select-safety-consumer-1 | FAIL, 14.019 s | Only the explicit empty maximum-input control needed its goal changed from [].length to 0 before omega; source and all theorem axiom reports already passed. |
| canonical-select-safety-consumer-2 | PASS, 10.876 s | Eight expected-type propositions and nine axiom diagnostics; no errors or warnings. |

Each stage has its replayable invocation and owned result under
`commands/<stage>.json`. The direct v4.22.0 binary avoids the previously observed
elan shim network attempt. Every stage used the granted build slot, a 180-second
deadline and a single owned process. Slot release followed the last consumer;
documentation and hygiene continued without Lean. No aggregate was appropriate
for these disjoint internal leaves. Both required repository trust scans had no
matches; `git diff --check` and explicit untracked-source whitespace checks passed.

The source consumer preserves the entire charged source and proves its literal
budget is 10030. The expanded execution consumer preserves actual program,
initial state, memory and indexed transitions, with each indexed receipt backed
by that same allocation. Its prefix clause is every fuel at most the source
budget, as required by SelectExecutionSafety. The separate ScratchFrame theorem
covers register support for every natural fuel without this budget restriction.
All nine axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`;
the literal source-budget theorem uses only `propext`, `Quot.sound`.

Conceptually, the former generic safety hypotheses are now derived from the
actual stored headers, actual descriptor geometry and actual payload bounds.
The proof carries the evaluated setup and target-setup states into the shared
controller and then into the compiler theorem. In plain English, every fitting
input runs this complete canonical select program with fitting instructions,
register values, addresses and replies; invalid occurrences still satisfy
machine safety. The only live final assumption is input representability.
The internal all-operation helpers have no assumptions and are direct consumers
for the parallel rank/access safety join.

A skeptical reader should next inspect the independent semantic, termination,
capacity and full-public-interface joins: safety alone does not prove their
answers correct or close the whole BV-1 milestone. Those remain coordinator
scope. No executable construction or new design/process decision was introduced
here; this implements the approved interface, so no parent-owned design ledger
was edited. No commit or global acceptance claim was made.

## Exact checked external consumer

The following is the complete successful temporary consumer, imported against
the built module, reproduced here so the evidence can be reconstructed.

```lean
import RMQ.Core.WordRAM.Bitvector.CanonicalSelectSafety
open RMQ RMQ.PackedBitvector RMQ.PackedBitvector.Controller
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1CanonicalSelectSafetyConsumer
example (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    ControllerSafetyBounds (loadedModel bits operation target argument) (canonicalLimits bits.length) :=
  loadedModel_safetyBounds bits operation target argument
example (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    Controller.ReaderSafe (loadedModel bits operation target argument)
      (Experiment.width bits.length) (Allocation.memory bits) Experiment.physicalReader :=
  loadedModel_readerSafe bits operation target argument
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    (source .select).Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨(initial .select target argument).regs, .running⟩ :=
  canonical_select_source_safe bits target argument ha
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .select) ((source .select).size + 1) (initial .select target argument) :=
  canonical_select_execution_safe bits target argument ha
example (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .select target argument
    (∀ instruction ∈ program .select, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .select).size + 1 →
      (run (Allocation.memory bits) (program .select) index (initial .select target argument)).final.Fits
        (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt), actual.transitions[index]? = some t →
      t.receipt = some receipt → receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  canonical_select_execution_safe_expectedType bits target argument ha
example : (source .select).size + 1 = 10030 := canonical_select_source_budget
example (target : Bool) : RankExecutionSafety (Allocation.memory []) (Experiment.width 0)
    (program .select) ((source .select).size + 1) (initial .select target 0) :=
  canonical_select_execution_safe [] target 0 (Nat.two_pow_pos _)
example (target : Bool) : RankExecutionSafety (Allocation.memory []) (Experiment.width 0)
    (program .select) ((source .select).size + 1)
    (initial .select target (2 ^ Experiment.width 0 - 1)) := by
  exact canonical_select_execution_safe [] target _ (by change 2 ^ Experiment.width 0 - 1 < 2 ^ Experiment.width 0; have := Nat.two_pow_pos (Experiment.width 0); omega)
#print axioms loadedMetadata_envelope
#print axioms loadedModel_safetyBounds
#print axioms loadedModel_readerSafe
#print axioms initial_data_fits
#print axioms canonical_select_source_safe
#print axioms canonical_select_source_fieldsFit
#print axioms canonical_select_source_budget
#print axioms canonical_select_execution_safe
#print axioms canonical_select_execution_safe_expectedType
end BV1CanonicalSelectSafetyConsumer
```

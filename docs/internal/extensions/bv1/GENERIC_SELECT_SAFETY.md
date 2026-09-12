# BV-1 generic select safety leaf

Status: CANDIDATE_COMPLETE for this assigned leaf; coordinator acceptance is
separate. Contract frozen before source edits. Worker owns only
`GenericSelectSafety.lean`, this evidence file, and its temporary exact consumer.
Governance is `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; continuation checkpoint is
`645a0502b9da9ad6444edbe44759e1c2c5661f25`. Canonical proof-sprint preflight and
completion gate apply. No commit or aggregate gate is authorized to this worker.
All inherited BV-1 acceptance rows remain unchanged and OPEN.

## Frozen target and composition

For arbitrary `model : ControllerModel`, `limits : SafetyLimits`,
`bounds : ControllerSafetyBounds model limits`, `memory : Memory`, and reader,
assume `ReaderSafe model limits.width memory reader`,
`ReaderSimulation model memory reader`, and `ReaderWrites reader`.
For every `s : Data` with `s.Fits limits.width` and
`MetadataMatches model s.regs`, the required source conclusion is exactly
`(selectCloseBlock reader).Safe memory limits.width s`.
For running entry registers, the same evaluation's register 513 must be
strictly below `2 ^ limits.width`.

No additional occurrence bound is needed: the actual controller first checks
register 512 against metadata register 16, whose envelope bound is part of
`ControllerSafetyBounds`. The generic output bound is machine capacity; a
stronger output bound by input length comes from the separately checked
canonical semantic refinement, not from numerical conditions on arbitrary
possibly malformed logical stores.

Compilation additionally assumes `reader.FieldsFit limits.width` and
`3667 + 82 * reader.size < 2 ^ limits.width`. The exact target is
`RankExecutionSafety memory limits.width
  ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
  (3667 + 82 * reader.size) ⟨regs, 0, .running⟩`.
`SelectExecutionSafety` may be a transparent alias of that existing predicate.
The physical corollary substitutes exactly `Experiment.physicalReader` (size
77, budget 9981), with its actual writes derived from `physicalReader_writes`.
The consumer expands instruction fit, final fit, every indexed transition's
safety, every fuel prefix's fit, and every indexed receipt's address, same
memory lookup and successful reply fit.

No BP shape, readiness, canonical-store semantic lookup, or additional
unaccounted metadata hypothesis is permitted. Reader simulation constrains the
actual supplied reader and is discharged by the root's physical allocation
bridge. The source proof consumes the compiled generic flag rank wrappers and
chunk rank helper; executable blocks and compilation remain the existing
Packed definitions.

## Frozen leaf evidence matrix

| ID | Exact assigned requirement | Exact evidence / consumer | Boundary challenge | Status |
| --- | --- | --- | --- | --- |
| GSS-SOURCE | actual shared selectCloseBlock Experiment.physicalReader full source safety/output bound under compiled Controller.SafetyLimits, ControllerSafetyBounds, ReaderSafe, MetadataMatches, entry Fits, and request argument bound as mathematically necessary | Generic source safety above, specialized to the actual physical reader; register 513 of the same evaluation fits | Stopped entry and invalid large occurrence use actual guards; arbitrary fitting scratch inputs | CHECKED: source and exact consumer |
| GSS-COMPILE | Then obtain shared SelectExecutionSafety/all-prefix/transition/backing corollary through existing compiler safety | Exact compiled program, budget and expanded positional consumer above | Consumer retains transition index and receipt equality to the same memory | CHECKED: physicalSelect_execution_safe_expectedType |
| GSS-RANK | consume GenericRankSafety rank helper for flags | rankLongBlock_safe_bound, rankSparseBlock_safe_bound and rankWordBlock_safe_invariant at the same model/memory/reader | Raw length remains rawWidth, distinct from packet bound | CHECKED: both actual flag paths and both dense rank calls |
| GSS-NO-SHORTCUT | No BP shape, readiness, logical-store oracle, or uncharged metadata premises beyond these explicit generic numerical interfaces | Full theorem signature and source/axiom scan; actual source evaluator | Replacing reader by skip fails existing ReaderSimulation_rejects_skip | CHECKED: no shape/readiness premise; skip rejection imported and rechecked at exact type |
| GSS-CHECK | Continue through proof loop/exact consumer/digestion; no aggregate | Unique owned narrow runner stages, explicit import/typed consumer, trust and whitespace scans | No broader build and no overlap with shared build owner | CHECKED: stages and scans below |

## Verification plan

Narrow build only after explicit shared slot grant; initial deadline 180 seconds
with warm dependencies. Existing Packed SelectSafety may require separate cold
prerequisite warmup, in which case inspect the diagnostic and coordinate before
retrying. Use the pinned v4.22.0 lake binary and the owned `run_command.ps1`
runner, one process at a time. At closure run a fresh exact consumer and axiom
inspection, repository hygiene scans, and `git diff --check`. No full Lake or
aggregate gate because this is an additive internal proof leaf.

## Checked evidence

`GenericSelectSafety.lean` is 105343 bytes, SHA-256
`DE8C9B1CD5C13C0B4D630839872DE55542116046EBDB4CC9B823C53B59C5B678`.
Every endpoint below is in `RMQ.PackedBitvector.Controller`.

The source conclusion is exactly the frozen proposition. `selectCloseBlock_safe`
(line 1733) has the explicit eight model/reader numerical parameters followed
by `s`, `fit`, and `hm`, and concludes
`(selectCloseBlock reader).Safe memory limits.width s`.
`physicalSelect_safe` (line 1785) substitutes the actual
`Experiment.physicalReader` and proves its writes premise with the checked
`physicalReader_writes`; it retains only numerical model bounds, reader safety,
reader simulation, entry fit and metadata equality as live hypotheses.

`selectCloseBlock_output_bound` (line 1742) concludes exactly
`((selectCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 513
  < 2 ^ limits.width` from the same source safety. The fresh consumer explicitly
specializes this proposition to `Experiment.physicalReader`, the same memory,
and the same entry registers.

`selectCloseBlock_execution_safe` (line 1756) concludes the frozen compiled
safety proposition with `3667 + 82 * reader.size`. Its object chain is
`selectCloseBlock_safe` → actual `Block.Safe` → existing
`rank_compiled_safety` → actual `Block.compileAt 0 ++ [.halt 513]` → existing
`RankExecutionSafety` observations of `run`.
`SelectExecutionSafety` is only a transparent alias for that existing
predicate. `physicalReader_fieldsFit` derives the actual reader's dormant
operand fit from `regularLocateBlock_fieldsFit` and `spanBlock_fieldsFit` plus
the literal surrounding operations. `physicalSelect_execution_safe` (line
1794) fixes the same program to the reader of size 77 and budget 9981; the code
capacity inequality is derived from `limits.width32`, not assumed separately.
`physicalSelect_execution_safe_expectedType` (line 1811) expands all five
conjuncts verbatim as recorded in the consumer below.

Both long-superblock and sparse-local branches consume the checked generic
`rankLongBlock_safe_bound` / `rankSparseBlock_safe_bound` at the identical
model, limits, bounds, memory and reader. Both dense rank calls consume
`rankWordBlock_safe_invariant` and `rankWordBlock_output_bound` at those same
arguments. The local `reader_output_bounds` theorem says packet ≤ packetBound
for every request; its length conclusion has the explicit guard
`segment = 0 ∨ segment = 11 ∨ segment = 15`. The two dense raw reads discharge
that guard from the actual address block's output `segment = 0`. Table word
lengths are never substituted for rawWidth.

Read-only review by the controller worker before the first build confirmed
the numerical interface is sufficient at the top join, the actual invalid
occurrence guard discharges the eligible request bound, all five compiled
observations retain their objects and indexes, and `3667 + 82 * 77 = 9981`.
This review was source inspection, followed by independent kernel elaboration
recorded below.

## Verification results

All stages used `run_command.ps1` with the direct pinned
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe`.
The direct binary avoids the earlier elan-shim network attempt. Every stage
ran in its owned one-thread, kill-on-close Windows job while this worker held
the explicitly granted shared build slot. No timeout or surviving child was
reported. The slot was released immediately after the consumer process exited.

| Stage | Exact argument vector | Result |
| --- | --- | --- |
| generic-select-safety-1 | `build RMQ.Core.WordRAM.Bitvector.GenericSelectSafety` | FAIL, 51.984 s, 300 s deadline; cold Packed.SelectSafety prerequisite built; exactly one local arithmetic obligation needed packetBound positivity rather than an unrelated power positivity fact |
| generic-select-safety-2 | `build RMQ.Core.WordRAM.Bitvector.GenericSelectSafety` | PASS, 35.773 s, 180 s deadline; no local warnings |
| generic-select-safety-consumer-1 | `env lean <TEMP>/bv1-generic-select-safety-consumer.lean` | PASS, 8.419 s, 180 s deadline; eight independent expected-type propositions and eight axiom inspections |

Replayable command/result records are
`commands/generic-select-safety-1.json`,
`commands/generic-select-safety-2.json`, and
`commands/generic-select-safety-consumer-1.json`.
All seven new endpoint axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.
The imported skip-reader rejection contains only `propext` and `Quot.sound`.
No new axiom, native decision, external dependency, or Mathlib import was added.
The RMQ-wide prohibited trust-footprint scan and native-decision scan returned
no matches. `git diff --check` and separate untracked-file whitespace checks
passed; only Git's usual LF/CRLF notices appeared. No broad build or aggregate
gate was run because this internal leaf has narrow source and direct consumers.

## Proof digestion and completion gate

Conceptually, the safety proof now uses the generic numerical envelopes and
actual supplied-reader contract throughout the existing select source. It
retains the old primitive source and compiler and derives every bound on the
same evaluation. In plain English, once the physical reader and loaded
metadata meet their stated numerical contracts, every select branch fits the
declared machine word and every observed load is a safe access to that same
memory. The invalid-occurrence branch is included and needs no extra caller
validity assumption.

The live assumptions are exactly the frozen numerical interfaces, reader
safety/simulation/writes, entry fit and metadata equality. Generic compilation
also needs reader operand fit and program capacity; the physical instantiation
derives those last two from the actual reader literals and width32. No shape
witness, readiness proof, query-answer oracle or independent replay store is
introduced. The local `SelectSafety.Context` merely packages the proof
parameters; executable definitions do not read it.

A skeptical reviewer should next ask whether the canonical final allocation
really discharges these reader, metadata and numerical bounds simultaneously
and whether all setup/code/scratch charges concern that same allocation. Those
are the root's remaining integration obligations, already explicit in the
inherited OPEN BV-1 matrix. This leaf does not declare them complete. Its
anti-vacuity check concerns precisely the live reader-simulation premise:
`¬ ReaderSimulation model memory .skip`; no stronger negative predicate is
misreported as refuting source safety alone, since skipping can be safe.

No new representation or process decision was made: the proof instantiates the
already approved generic numerical interface and existing compiler. Root owns
global design/public ledgers and integration. The assigned leaf has no remaining
proof obligation, but whole BV-1 remains OPEN. Worker status is
`CANDIDATE_COMPLETE`, never coordinator acceptance.

## Exact fresh consumer

The following file was checked by the final consumer stage, with no source
changes afterward.

```lean
import RMQ.Core.WordRAM.Bitvector.GenericSelectSafety
open RMQ RMQ.PackedBitvector RMQ.PackedBitvector.Controller
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1SelectSafetyConsumer
variable (model : ControllerModel) (limits : SafetyLimits)
  (bounds : ControllerSafetyBounds model limits) (memory : Memory) (reader : Block)
  (readerSafe : Controller.ReaderSafe model limits.width memory reader)
  (readerCorrect : ReaderSimulation model memory reader) (readerWrites : ReaderWrites reader)
  (s : Data) (fit : s.Fits limits.width) (hm : Controller.MetadataMatches model s.regs)
example : (selectCloseBlock reader).Safe memory limits.width s :=
  Controller.selectCloseBlock_safe model limits bounds memory reader readerSafe readerCorrect readerWrites s fit hm
example (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    ((selectCloseBlock reader).eval memory ⟨regs, .running⟩).final.regs 513 < 2 ^ limits.width :=
  Controller.selectCloseBlock_output_bound model limits bounds memory reader readerSafe readerCorrect readerWrites regs fr mr
example (fields : reader.FieldsFit limits.width) (budget : 3667 + 82 * reader.size < 2 ^ limits.width)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    RankExecutionSafety memory limits.width ((selectCloseBlock reader).compileAt 0 ++ [.halt 513])
      (3667 + 82 * reader.size) ⟨regs, 0, .running⟩ :=
  Controller.selectCloseBlock_execution_safe model limits bounds memory reader readerSafe readerCorrect readerWrites fields budget regs fr mr
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader) :
    (selectCloseBlock Experiment.physicalReader).Safe memory limits.width s :=
  physicalSelect_safe model limits bounds memory rs rc s fit hm
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    let program := (selectCloseBlock Experiment.physicalReader).compileAt 0 ++ [.halt 513]
    let actual := run memory program 9981 ⟨regs, 0, .running⟩
    (∀ instruction ∈ program, instruction.Fits limits.width) ∧
    actual.final.Fits limits.width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe limits.width t.before t.instruction ∧ t.after.Fits limits.width) ∧
    (∀ index, index ≤ 9981 → (run memory program index ⟨regs, 0, .running⟩).final.Fits limits.width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt), actual.transitions[index]? = some t →
      t.receipt = some receipt → receipt.address < 2 ^ limits.width ∧
      receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ limits.width)) :=
  physicalSelect_execution_safe_expectedType model limits bounds memory rs rc regs fr mr
example : ¬ ReaderSimulation model memory .skip := readerSimulation_rejects_skip model memory
example : Experiment.physicalReader.FieldsFit limits.width := physicalReader_fieldsFit limits
example (rs : Controller.ReaderSafe model limits.width memory Experiment.physicalReader)
    (rc : ReaderSimulation model memory Experiment.physicalReader)
    (regs : Registers) (fr : (⟨regs, .running⟩ : Data).Fits limits.width)
    (mr : Controller.MetadataMatches model regs) :
    ((selectCloseBlock Experiment.physicalReader).eval memory ⟨regs, .running⟩).final.regs 513 <
      2 ^ limits.width :=
  Controller.selectCloseBlock_output_bound model limits bounds memory Experiment.physicalReader
    rs rc physicalReader_writes regs fr mr
#print axioms Controller.selectCloseBlock_safe
#print axioms Controller.selectCloseBlock_output_bound
#print axioms Controller.selectCloseBlock_execution_safe
#print axioms physicalReader_fieldsFit
#print axioms physicalSelect_safe
#print axioms physicalSelect_execution_safe
#print axioms physicalSelect_execution_safe_expectedType
#print axioms readerSimulation_rejects_skip
end BV1SelectSafetyConsumer

```

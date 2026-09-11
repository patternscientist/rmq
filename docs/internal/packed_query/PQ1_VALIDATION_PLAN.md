# PQ1 final validation contract

Frozen against checkpoint c8696087200a4e6cca26ac28ac2d8f972ddd44dd; revised
against HEAD bfffa95fdcbdea7df4b9c78f5bf8271dabfb5f0f plus the uncommitted
certificate, consumer, runtime and runner changes described below (three new
certificate fields, definitional pins, the array evaluator, new runtime
fixtures and the definition-collapse, projection and runtime negative cases).
This is a plan and registry contract, not a completed replay report. The
candidate is not accepted until the checks below run on its exact committed
tree, the aggregate gate passes on that tree and a fresh blind exact-commit
audit is complete.

## Public type and consumer

Core theorem: RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds.
Public proof alias: RMQ.Headlines.succinctRMQFullyChargedPackedQuery.
Public proposition alias: RMQ.Headlines.SuccinctRMQFullyChargedPackedQuery.
Public import: RMQPaper, through RMQ.Headlines.RMQ.
Independent consumer: RMQ/Validation/PackedQueryContract.lean.

The consumer must ascribe the actual public alias to the complete core
proposition and separately project every field at an independently written
expected type. It must spell the builder, width, program, initial state, fuel,
endpoint domain and observed run arguments; merely printing the current
theorem type or inferring projection types is insufficient. The final consumer
has no certificate parameter or supplied correctness/safety hypothesis.

Three fields were added to the certificate at the end of its field list:
specResult states that for every valid range the actual run returns
some (scanWindow xs left (right - left) + 1), with no reference to queryNat or
the RC6 reference value; noFailedLoads states that for every valid range every
receipt of the run has a reply; invalidGuardSteps states that every invalid
range is rejected within six executed instructions. The supporting theorems
are in RMQ/Core/WordRAM/Packed/QueryCertificate.lean. The proof of
noFailedLoads does not use its validity premise (the canonical run halts for
every endpoint pair), and the guard takes exactly four steps when left is at
least right and exactly six otherwise (queryRun_invalid_steps).

RMQ.lean imports the consumer and RMQ.Core.WordRAM.Packed.ArrayRun, so the
default lake build elaborates every field check, pin and negative control, and
scripts/headline_axiom_check.lean runs after lake build and lake build
RMQPaper on a fresh clone without the replay's direct compilation.

## Frozen certificate mutation registry

Each field case weakens exactly the named proposition to True and replaces
its composition initializer by True.intro. The core composition and public
export must still compile; the independent consumer must then fail on its
corresponding expected proposition. A failure in the mutation setup or core
producer is not the expected consumer verdict. All other field types and
initializers remain byte-identical.

| Case ID | Exact field | Expected verdict/surface |
| --- | --- | --- |
| C01-ALLOCATION-RESIDUAL | allocationResidualLittleO | REJECT / PackedQueryContract.lean |
| C02-COMPLETE-RESIDUAL | completeResidualLittleO | REJECT / PackedQueryContract.lean |
| C03-WIDTH-SCALING | widthBounds | REJECT / PackedQueryContract.lean |
| C04-DATA-CAPACITY | dataCapacity | REJECT / PackedQueryContract.lean |
| C05-COMPLETE-CAPACITY | completeCapacity | REJECT / PackedQueryContract.lean |
| C06-MEMORY-WORDS | memoryWordsFit | REJECT / PackedQueryContract.lean |
| C07-ALLOCATION-ADDRESSES | allocationAddressesFit | REJECT / PackedQueryContract.lean |
| C08-DORMANT-FIELDS | programFieldsFit | REJECT / PackedQueryContract.lean |
| C09-FIXED-BUDGET | budgetExact | REJECT / PackedQueryContract.lean |
| C10-PROGRAM-LENGTH | programLength | REJECT / PackedQueryContract.lean |
| C11-ENCODED-PROGRAM | encodedProgramBound | REJECT / PackedQueryContract.lean |
| C12-REGISTER-COUNT | registerCount | REJECT / PackedQueryContract.lean |
| C13-SCRATCH-COUNT | scratchCount | REJECT / PackedQueryContract.lean |
| C14-UNUSED-REGISTERS | unusedRegisters | REJECT / PackedQueryContract.lean |
| C15-VALID-INPUTS | validInputs | REJECT / PackedQueryContract.lean |
| C16-TOTAL-NAT-CONTRACT | natContract | REJECT / PackedQueryContract.lean |
| C17-LEFTMOST | leftmost | REJECT / PackedQueryContract.lean |
| C18-ACTUAL-RESULT | result | REJECT / PackedQueryContract.lean |
| C19-ACTUAL-HALT | halt | REJECT / PackedQueryContract.lean |
| C20-INVALID-GUARD | invalidGuard | REJECT / PackedQueryContract.lean |
| C21-EXECUTED-STEPS | stepBound | REJECT / PackedQueryContract.lean |
| C22-CATEGORY-PARTITION | categoryPartition | REJECT / PackedQueryContract.lean |
| C23-FINAL-STATE | finalStateFit | REJECT / PackedQueryContract.lean |
| C24-TRANSITION-SAFETY | transitionSafety | REJECT / PackedQueryContract.lean |
| C25-EVERY-PREFIX | prefixSafety | REJECT / PackedQueryContract.lean |
| C26-READ-WIDTH | readWidth | REJECT / PackedQueryContract.lean |
| C27-POSITIONAL-BACKING | positionalReadBacking | REJECT / PackedQueryContract.lean |
| C28-ORDERED-REFINEMENT | orderedLogicalRefinement | REJECT / PackedQueryContract.lean |
| C29-READ-ONLY | logicalReadOnly | REJECT / PackedQueryContract.lean |
| C30-MEMORY-AGREEMENT | suppliedMemoryAgreement | REJECT / PackedQueryContract.lean |
| C31-SPEC-RESULT | specResult | REJECT / PackedQueryContract.lean |
| C32-NO-FAILED-LOADS | noFailedLoads | REJECT / PackedQueryContract.lean |
| C33-INVALID-GUARD-STEPS | invalidGuardSteps | REJECT / PackedQueryContract.lean |
| P01-PUBLIC-ALIAS-TRUE | replace public proof alias by True.intro | REJECT / PackedQueryContract.lean |
| A01-UNCHANGED-CONTRACT | unchanged core/export/consumer | ACCEPT / PackedQueryContract.lean |
| D01-CATEGORY-COLLAPSE | Instruction.category non-load arms collapsed to control | REJECT / PackedQueryContract.lean |
| R01-SPEC-PROJECTION | specResult packet changed from answer plus one to plus two | REJECT / Capstone.lean |
| N01-WRONG-EXPECTED | runtime fixture with a wrong literal answer | REJECT / PackedQueryRuntime.lean |

The committed runner must compare this exact ID/target/verdict/surface mapping
with its own fixed registry, with the complete source inventory of every
certificate field and initializer between the PQ1-REPLAY markers, with the
consumer's checkCNN inventory and with the pin inventory below. Reject
missing, duplicate, extra, reordered or resurfaced mappings. Full mode runs
every case; one explicit selector runs exactly that case and no other. Unknown,
empty or whitespace selectors fail before a Lean child starts. Include
deterministic registry/selector self-tests that inject missing/duplicate cases
and keep a known-success control. Do not infer a registry from the
implementation and compare it with itself.

The last three cases are not field weakenings:

- D01 replaces the body of Instruction.category in
  RMQ/Core/WordRAM/Packed/Primitive.lean so that load keeps memoryRead and
  every other constructor returns control. The producer and RMQPaper still
  build (the certificate's partition field holds for any category map), so the
  producer is rebuilt through lake build RMQPaper and the consumer must then
  fail only at pinInstructionCategory. Collapsing every constructor to one
  category is not a usable case: the producer's own example
  CalculusExamples.successfulLoad in Calculus.lean already rejects it.
- R01 changes the specResult field statement from + 1 to + 2. The producer,
  not the consumer, must reject it, and every error must lie in the specResult
  initializer of fullyChargedPackedQueryCapstone_of_runtime_safety.
- N01 runs the runtime negative control by explicit selector; the fixture
  checker must reject it with its result-mismatch message.

Development evidence on the uncommitted tree (not replay evidence): with the
D01 collapse applied, lake build RMQPaper passed in 268 seconds and the
consumer failed only at pinInstructionCategory, with a "Not a definitional
equality" error at the theorem and a "type mismatch" at its rfl; after
byte-exact restoration lake build RMQPaper passed in 254 seconds and the
consumer passed. Collapsing every constructor to control, or mapping every
transition of Run.categories to control, failed the producer at Calculus.lean
line 288, and replacing the shift-width condition of Instruction.Safe by True
failed it at Safety.lean line 203; these are therefore not definition-collapse
cases. No other pin was collapse-tested by a build. With the R01 change,
Capstone.lean failed with one type mismatch on the specResult initializer line
and was restored byte-exactly. The N01 selector failed with
"N01-WRONG-EXPECTED: result mismatch".

Script-boundary controls launch the runner itself in a bounded child of the
same shell with -SelectorProbeOnly: an explicitly bound empty, whitespace or
unknown -OnlyCase (and an empty -OnlyCase with -RuntimeOnly) must fail with the
PQ1-SELECTOR diagnostic before any stage; a valid ID must select exactly that
case; omission must select every case. These controls, the registry self-test,
the probe, the deadline self-test and the provenance self-test are Lean-free
and must pass under both Windows PowerShell 5.1 and PowerShell 7.
Every boundary child starts with a stale runtime selector and must prove the
environment entry is absent after startup, including when selection rejects.
An empty environment value is not absence: Lean rejects it as malformed.

## Definitional pins

Each field check restates its field in the producer's vocabulary, so a
changed definition would change producer and consumer together. The consumer
therefore restates, by definitional unfolding, the complete body of every small
semantic definition reachable from the field types: machine state and
semantics, run observations, encoded-field fit and arithmetic safety, the input
encoding and total wrapper, and the specification predicates. A pin is added
whether or not a weakening would also break a producer proof; the D01 build
above shows that at least one weakening does not. The pins are, in order: pinMemory, pinRegisters, pinProgram,
pinStateShape, pinReceiptShape, pinTransitionShape, pinRunShape,
pinRegistersWrite, pinArithmeticEval, pinComparisonEval, pinArithmeticCode,
pinComparisonCode, pinInstructionCategory, pinInstructionOperands,
pinInstructionEncoding, pinInstructionFits, pinStateWriteNext, pinExecute,
pinStep, pinRunZero, pinRunSucc, pinRunReads, pinRunCategories, pinRunSteps,
pinRunResult, pinRunCategoryCount, pinStateFits, pinInstructionSafe,
pinInputRegisters, pinInitialState, pinEncodeInputs, pinQueryNat,
pinValidRange, pinLeftmostArgMin, pinOptionNatPacket, pinLittleOLinear,
pinReadOnlyTrace, pinIsReadWord.

Every pin is proved by rfl except the two operator evaluators and the operand
list, which are proved by case analysis on the constructor followed by rfl in
each case; a pin whose right side matches on a constructor also fixes the
constructor set. The remaining definitions in the field types are fixed by the
fields themselves. queryBudget, queryRegisterCount and queryScratchWords are
pinned to numerals by budgetExact, registerCount and scratchCount. wordWidth,
allocationRho and queryCompleteRho are constrained by the width bounds, the
capacity inequalities and the little-o fields that the claim itself states.
buildMemory, metadata, queryProgram, SuccinctClassic.cartesianShape,
SuccinctClassic.queryTraceResult and logicalTraceReads occur on one side of an
equation whose other side is the pinned machine's own observation (result,
halt, orderedLogicalRefinement), so a changed body must produce the same values
or break the producer. scanWindow is fixed on every valid range by natContract
and specResult together with leftmost and the uniqueness of the leftmost
minimum.

The consumer also contains negative controls showing that Instruction.Fits at
wordWidth 0 rejects an operand equal to the word capacity in a register field,
a jump target and an immediate, and a positive control accepting the largest
representable immediate.

## Runtime registry

RMQ/Validation/PackedQueryRuntime.lean runs the actual numeric-memory program.
Its independent literal expected fixture indices and separately pinned IDs are:

S01-EMPTY, S02-SINGLE, S03-LEFTMOST-TIE, S04-SLICE, S05-REVERSED,
S06-OUT-OF-RANGE, S07-WORD-MAX, S08-OUTER-CAPACITY, S09-LONG-INTERVAL,
S10-CORRUPT-METADATA, S11-UNREAD-REPLACEMENT, S12-EMPTY-INTERVAL,
S13-CROSS-BLOCK, S14-SAME-BLOCK, S15-ADJACENT-BLOCKS.

All expect ACCEPT by the fixture checker. S08 checks only the total outer API
and makes no machine-cost claim for unbounded input parsing. S10 changes the
actual loaded size metadata of the singleton allocation and requires the
returned packet to change to rejection. S11 changes a genuinely unread
allocated cell and requires the same result, steps, ordered categories and
receipts. Each machine case checks halt, literal expected answer, agreement of
that literal with scanWindow, instruction budget, category partition, raw
allocation replies and that no receipt lacks a reply. Invalid cases require
zero reads and exactly four guard steps when left is at least right, six
otherwise. Small fixtures do not replace the universal fringe/interior proofs.

S12 is the empty interval [2,2) on a four-element list. S13, S14 and S15 use the
list [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9], whose element closes span three
summary blocks and whose minimum value 2 occurs at indices 5 and 9: S13 is
[1,11) with expected index 5 (the interior-block candidate beats the equal
right-fringe value at index 9), S14 is [6,10) with expected index 9 and S15 is
[4,8) with expected index 5, each derived by hand. Their routes are asserted
from the input's Cartesian shape and the RC6 reference trace, never from the
machine: S13 has endpoint closes in non-adjacent summary blocks and 18
segment-20 interior reads in the reference trace, S14 has both closes in one
block and no interior read, S15 has closes in adjacent blocks and no interior
read, and S12 has an empty reference trace.

Fixtures execute runArray on queryProgram.toArray, which runArray_toArray
proves equal to run on the list program. S02 and S05 are also executed by run
itself and must agree on result, final status, steps, categories and receipts.

The negative runtime control, runnable only by explicit selector and required
to be rejected with its result-mismatch message, is N01-WRONG-EXPECTED: the
query [0,4) on [4, -3, -3, 8] with expected index 2, where the leftmost minimum
is index 1.

A runtime selector reaches the Lean program either as its only argument or
through the PQ1_RUNTIME_SELECTOR environment variable spelled id:<ID>. The
runner uses only the environment channel, because Windows PowerShell 5.1 drops
an empty native argument and would turn the empty-selector control into a full
run. The runner removes the environment entry for itself before any child
starts. It uses the environment provider's removal operation because a .NET
string argument can coerce null to an empty value under PowerShell 7.

Three fixture families are out of reach of the Lean interpreter, where
buildMemory alone took 60 to 169 seconds for one 24-element list. A cross-macro
interior needs more summary blocks than one macro holds (blocksPerSuper
squared); in the canonical layout this first happens at n = 1000, and a whole
middle macro, the only case that reads the global interior tables, first fits
at n = 3456. A nonzero sparse exception count is impossible below n = 2^96,
because the local stride max 1 (w / (ell * ell)) is 1 whenever the select word
parameter w = log2(2n) + 1 is below 98, and a local block of one occurrence
never spans more than w bits. A nonzero long count needs a superblock of w
squared closes spanning more than w cubed times ell bits, which needs more than
13,000 elements. These routes rest on the universal theorems.

Timing evidence on this host (Windows, one Lean process at a time, other
applications using about half of the processors): the full runtime registry at
HEAD bfffa95 (eleven fixtures, list evaluator, one preprocessing per fixture)
took 520 seconds; the revised registry (fifteen fixtures, array evaluator, one
preprocessing per distinct list) took 294 seconds and passed all fifteen.
Preprocessing dominates: in isolated measurements one 16,358-step run took 42
seconds through run and 5 seconds through runArray, while buildMemory for a
24-element list took between 60 and 169 seconds in different runs. The
runner's runtime-stage deadline (RuntimeDeadlineSeconds) is therefore 1200
seconds, about four times the measured registry.

## Process and restoration contract

The early textual certificate inventory uses a frozen layout: known members start at
two spaces, continuation lines at four or more, and member-level comments use
`--`. Every member-leading token is inventoried, including unfamiliar Lean
identifier spelling; unsupported layout is rejected rather than ignored.
Registry self-tests inject underscore, apostrophe, Unicode and escaped names
inside and outside both marker regions, as well as unsupported indentation.
This text check is a lower bound: Lean admits more-indented and defaulted fields.
After rebuilding the baseline producer, `scripts/packed_query_inventory_check.lean`
compares Lean's actual structure metadata with an independent literal 33-field
inventory. Its parsed extra-field controls include a defaulted, more-indented
field, apostrophe, Unicode and escaped names; unchanged and absent-structure
controls exercise the same predicate. Every replay mode that mutates the
certificate must pass this authoritative inventory check first.

Reuse scripts/owned_process_tree.ps1 to bound owned root and descendant
processes; retain each stage's diagnostic output under .lake/pq1-replay.
Use observed narrow runtimes with cold-cache margin. Missing targets,
timeouts, output-limit failures and setup failures never count as expected
type rejection. No simultaneous Lean process uses this build tree.

Certificate mutations run only from a clean committed candidate. Save exact
bytes and hashes of every touched tracked file; apply one case; check the
expected producer and consumer surfaces; restore in finally; verify exact
hashes and tracked/index cleanliness. Rebuild restored producer/public/consumer
artifacts before proceeding or reporting success; a definition-collapse case is
rebuilt and restored through lake build RMQPaper under its own deadline
(ProducerRebuildDeadlineSeconds, default 2400), and the runtime control
touches no file. Final report records the exact source commit, complete case
registry, stage outcomes, restoration and clean-tree checks. This file alone is
not replay evidence.

The shared Git observer checks exit status, deadline and output limits before
using stdout for repository state. Stderr diagnostics remain visible warnings;
they are not parsed as changed paths. Its clean-baseline fixture includes LF
restoration under `core.autocrlf=true` with a required real conversion warning,
plus actual tracked, staged and untracked changes and a failed Git command.

The provenance self-test reads every file listed in
docs/internal/packed_query/experiment-rc6/manifest.json from the committed
blobs of HEAD (git cat-file, raw bytes), requires the committed directory to
contain exactly the listed files plus manifest.json and .gitattributes, and
checks each byte count and SHA-256 against the committed manifest; a flipped
byte and an appended byte must fail the same comparison.

## Claim-surface inventory and final verification

The currentFactSurfacePathRegex in docs/internal/CLAIM_DRIFT_POLICY.json
matches these 18 tracked paths at c869608: README.md; artifact/CLAIMS.md;
artifact/README.md; docs/FAMILY_SUMMARY.md;
docs/PAPER_CLAIM_CORRESPONDENCE.md; docs/PAPER_MAIN_THEOREM.md;
docs/PAPER_MODEL_ADEQUACY.md; docs/PAPER_RELATED_WORK.md;
docs/PAPER_THEOREM_MAP.md; docs/PUBLICATION_STRATEGY.md;
docs/RELATED_WORK_AND_LIMITATIONS.md; docs/ROADMAP.md;
docs/TRUST_AUDIT_PACKET.md; docs/WHAT_IS_PROVED.md;
docs/WORD_RAM_REVIEW_PACKET.md; docs/digests/PROJECT_DIGESTION_CURRENT.md;
docs/internal/CLAIM_DRIFT_POLICY.md; docs/internal/RMQ_FINAL_ROADMAP.md.

Root searched all 18 for fully-charged/small-step/word-RAM wording. Final
synchronization must inspect each relevant passage, distinguish the old 210
trace and 427 probe models from the new 837,572 instruction budget, update
affected current-frontier statements and add a focused digestion entry. This
inventory is a lower bound; inspect RMQPaper and the declaration-adjacent Lean
comments too.

After canonical closure and replay: required builds/trust/hygiene/design and
paper/correspondence gates, then one aggregate gate on the unchanged final tree
and a fresh blind exact-commit audit. Prior RC6 aggregate runtime was about 82
minutes; the frozen acceptance matrix requires at least a 150-minute ownership
deadline with short polling. Diagnose any late failure by its smallest
component before another full final certification. No checkpoint or successful
local leaf substitutes for these final obligations.

# PQ1 final validation contract

Frozen against checkpoint c8696087200a4e6cca26ac28ac2d8f972ddd44dd.
This is a plan and registry contract, not a completed replay report. No public
milestone is accepted until the canonical safety premise is discharged,
the unconditional theorem is exported and the checks below run on its exact
committed candidate.

## Public type and consumer

Core theorem: RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds.
Planned public proof alias: RMQ.Headlines.succinctRMQFullyChargedPackedQuery.
Planned public proposition alias: RMQ.Headlines.SuccinctRMQFullyChargedPackedQuery.
Public import: RMQPaper, through RMQ.Headlines.RMQ.
Independent consumer: RMQ/Validation/PackedQueryContract.lean.

The consumer must ascribe the actual public alias to the complete core
proposition and separately project every field at an independently written
expected type. It must spell the builder, width, program, initial state, fuel,
endpoint domain and observed run arguments; merely printing the current
theorem type or inferring projection types is insufficient. The final consumer
has no certificate parameter or supplied correctness/safety hypothesis.

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
| P01-PUBLIC-ALIAS-TRUE | replace public proof alias by True.intro | REJECT / PackedQueryContract.lean |
| A01-UNCHANGED-CONTRACT | unchanged core/export/consumer | ACCEPT / PackedQueryContract.lean |

The committed runner must compare this exact ID/field/verdict mapping with its
own fixed registry and with the complete 30-field source inventory. Reject
missing, duplicate, extra or reordered mappings. Full mode runs every case;
one explicit selector runs exactly that case and no other. Unknown, empty or
whitespace selectors fail before a Lean child starts. Include deterministic
registry/selector self-tests that inject missing/duplicate cases and keep a
known-success control. Do not infer a registry from the implementation and
compare it with itself.

## Runtime registry

RMQ/Validation/PackedQueryRuntime.lean runs the actual numeric-memory program.
Its independent literal expected fixture indices and separately pinned IDs are:

S01-EMPTY, S02-SINGLE, S03-LEFTMOST-TIE, S04-SLICE, S05-REVERSED,
S06-OUT-OF-RANGE, S07-WORD-MAX, S08-OUTER-CAPACITY, S09-LONG-INTERVAL,
S10-CORRUPT-METADATA, S11-UNREAD-REPLACEMENT.

All expect ACCEPT by the fixture checker. S08 checks only the total outer API
and makes no machine-cost claim for unbounded input parsing. S10 changes the
actual loaded size metadata of the singleton allocation and requires the
returned packet to change to rejection. S11 changes a genuinely unread
allocated cell and requires the same result, steps, ordered categories and
receipts. Each machine case checks halt, literal expected answer, instruction
budget, category partition and raw allocation replies. Invalid cases require
zero reads. Small fixtures do not replace the universal fringe/interior proofs.

Development evidence: the first full attempt passed S01 through S10, including
the actual metadata-corruption control, in 171.989 seconds. S11 correctly
rejected its original singleton fixture because every allocated cell was read.
Its repaired 24-element increasing input and one-element query passed a focused
actual unread-cell replacement in 123.506 seconds: 7641 instructions, 228
receipts, answer some0, and identical result/steps/categories/receipts after
replacement. The final full runtime and unknown/empty-selector controls remain
required on the completed public candidate. The runtime stage deadline is now
600 seconds, allowing the measured replacement test plus the preceding cases
and cold-cache margin; the earlier development attempts used 300 seconds.

## Process and restoration contract

Reuse scripts/owned_process_tree.ps1 to bound owned root and descendant
processes; retain each stage's diagnostic output under .lake/pq1-replay.
Use observed narrow runtimes with cold-cache margin. Missing targets,
timeouts, output-limit failures and setup failures never count as expected
type rejection. No simultaneous Lean process uses this build tree.

Certificate mutations run only from a clean committed candidate. Save exact
bytes and hashes of every touched tracked file; apply one case; check the
expected producer and consumer surfaces; restore in finally; verify exact
hashes and tracked/index cleanliness. Rebuild restored producer/public/consumer
artifacts before proceeding or reporting success. Final report records the
exact source commit, complete case registry, stage outcomes, restoration and
clean-tree checks. This file alone is not replay evidence.

## Claim-surface inventory and final verification

The currentFactSurfacePathRegex in docs/internal/CLAIM_DRIFT_POLICY.json
matches these18 tracked paths at c869608: README.md; artifact/CLAIMS.md;
artifact/README.md; docs/FAMILY_SUMMARY.md;
docs/PAPER_CLAIM_CORRESPONDENCE.md; docs/PAPER_MAIN_THEOREM.md;
docs/PAPER_MODEL_ADEQUACY.md; docs/PAPER_RELATED_WORK.md;
docs/PAPER_THEOREM_MAP.md; docs/PUBLICATION_STRATEGY.md;
docs/RELATED_WORK_AND_LIMITATIONS.md; docs/ROADMAP.md;
docs/TRUST_AUDIT_PACKET.md; docs/WHAT_IS_PROVED.md;
docs/WORD_RAM_REVIEW_PACKET.md; docs/digests/PROJECT_DIGESTION_CURRENT.md;
docs/internal/CLAIM_DRIFT_POLICY.md; docs/internal/RMQ_FINAL_ROADMAP.md.

Root searched all18 for fully-charged/small-step/word-RAM wording. Final
synchronization must inspect each relevant passage, distinguish the old210
trace and427 probe models from the new837572 instruction budget, update
affected current-frontier statements and add a focused digestion entry. This
inventory is a lower bound; inspect RMQPaper and the declaration-adjacent Lean
comments too. No public acceptance wording has changed yet.

After canonical closure and replay: required builds/trust/hygiene/design and
paper/correspondence gates, then one aggregate gate on the unchanged final tree
and a fresh blind exact-commit audit. Prior RC6 aggregate runtime was about82
minutes; the frozen acceptance matrix requires at least a150-minute ownership
deadline with short polling. Diagnose any late failure by its smallest
component before another full final certification. No checkpoint or successful
local leaf substitutes for these final obligations.

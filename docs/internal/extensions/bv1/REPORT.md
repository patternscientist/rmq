Status: INCOMPLETE
Phase: CONTRACT/FEASIBILITY — pending mandatory coordinator route review.

All 30 rows in ACCEPTANCE_MATRIX.md remain open at the composed target.
This is the authorized phase checkpoint, not candidate completion or an
obstruction. The task's explicit completion contract permits an INCOMPLETE
phase return for mandatory contract/route review. Resume the same branch after
the coordinator's disposition; no acceptance criterion is amended.

- Handle/title: BV-1 / `(BV-1) Prove fully charged generic rank select`.
- Branch: `codex/bv-1-fully-charged-rank-select`.
- Worktree: `C:/Users/poin/.codex/worktrees/c974/RMQ`.
- Base/governance and initial preflight HEAD: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Local phase commit is being prepared. Assigned edits are preserved; no push or integration.
- Durable frozen matrix: `docs/internal/extensions/bv1/ACCEPTANCE_MATRIX.md`.
- Exact command evidence: `COMMANDS.md`, `commands/*.json`.
- Route contract/source facts: `CONTRACT.md`, `SOURCE_FACTS.md`.

## Implemented and checked so far

`Normalization.lean` proves position-preserving normalization for both Boolean
values, all prefix ranks, all select occurrences, access/slices and finite-word
numeric/optional packet identities. No shape/readiness premise occurs. Exact
types and axiom/build evidence are in NORMALIZATION.md. The clean source build
and typed/axiom consumer passed. These are mathematical identities, not a
physical machine theorem.

`SelectExperiment.lean` builds one numeric select allocation with both
directories, one raw input, shared chunk tables and a charged descriptor/span
reader. It compiles the existing selectCloseBlock with the new reader using
the existing Structured compiler. Its source and `ReaderInterface.lean` compile.
The latter defines the exact generic reader proposition; its canonical instance
has not been proved. No access/rank program or full allocation/safety theorem
exists yet, and Capstone.lean is not present.

The version1 feasibility validator has18 exact named cases and uses independent
Succinct.select expected results. Startup, a known case and all18 cases passed.
All eight production selector controls also passed, including omitted and
empty parameters. The threshold query's attempted crossing assertion failed:
its answer was correct but it made no second span load. A separate version2
reader-component crossing control passed at n127,segment2,index0, with one
actual second span load and correct packet1. It addresses component coverage
without claiming whole-select crossing reachability. The failed earlier source
is retained byte-for-byte as a replayable expected-fail control. No full
controls row is closed; long/sparse parameterized cases remain unexecuted.

`AllocationFacts.lean` now proves the exact retained-bit serialization and
count for all valid generic directory objects, reconciling the four omitted
false rank sample tables. It derives the canonical overhead bound for each
target and sums the two bounds. Its clean build, five typed consumers and
eight axiom inventories passed. These are component-capacity facts: final
padding, metadata, rank/access data, code and scratch accounting remain open.

An independent read-only contract review is in ROUTE_REVIEW.md. It identifies
canonical layout regularity and arbitrary-memory fault-specification boundaries;
the lead incorporated both into CONTRACT.md. No canonical counterexample or
formal obstruction was found. The coordinator's evidence-dependent route
disposition, full generic reader proof and final blind candidate audit are
separate pending stages.

## Exact checked propositions

For every target,bits,k,p, with no additional premise:

```text
Succinct.rankPrefix false (normalize target bits) p =
  Succinct.rankPrefix target bits p
Succinct.select false (normalize target bits) k = Succinct.select target bits k
readerPacket (word.map (normalize target)) =
  let packet := readerPacket word
  let len := readerLength word
  if packet = 0 then 0 else if target then 2^len + 1 - packet else packet
```

For every valid `d : SparseExceptionSelectData bits target rs rb`, the length
of the actual selected sixteen component arrays plus the lengths of the four
omitted false sample tables equals `d.payload.length`. Consequently those
selected bits are at most `canonicalSparseExceptionSelectOverhead bits.length`.
The independent false/true pair is at most the sum of two such overheads. The
directory object's validity proofs remain hypotheses of this generic leaf;
canonical instantiation is checked. No packet/trace/safety fact is inferred
from this length theorem. Exact full types appear in ALLOCATION_FACTS.md and
the committed typed consumers under scripts/packed_bitvector_*_consumers.lean.

`CanonicalGenericReaderCorrect` is an elaborated proposition, not a theorem:
it universally requests GenericReaderCorrect for Experiment.memory bits and
Experiment.physicalReader at the same bits and target. The actual decoder,
descriptor loads and same-memory receipt equations must still establish it.

## Verification, scope and decisions

Narrow builds, exact-type/axiom consumers, startup, all18 select fixtures and
eight production selector controls passed. The crossing candidate failed and
the repaired component fixture passed, as recorded above. The proof leaves and
reader packet facts use only propext and Quot.sound in their explicit axiom
inventories. Trust-token/native-decision scans returned no matches.

DD-20260912-BV1-001 and WDD-20260912-BV1-001 record source and process decisions,
alternatives, evidence and consequences. Shared ledgers were appended only.
Changed source is confined to four Bitvector modules, the new validator and
lane scripts; lakefile adds only rmq_packed_bitvector_validate. The remaining
changed files are the task evidence folder and the two appended ledgers.
No shared Packed module, canonical skill, public root alias or gate.ps1 changed.

The full lake build, full capstone import/axiom inventory, mutation campaign,
long/sparse controls, final public family/digestion entry and blind exact-commit
candidate audit are not run or claimed. They remain requirements after the
route review; no capstone exists to certify now. No host-wide aggregate slot
was requested or consumed. Windows process ownership is recorded; unexecuted
Linux/escape controls are uncovered. Detailed phase policy checks are in
COMMANDS.md and commands/phase-*.json(.gz).

The corrected archived phase check passed all six checks and preserved the
exact frozen matrix hash. Its claim scan reported1601 hits and zero strict
failures. The preceding self-scanning failure remains archived with the
process repair described in WDD-20260912-BV1-001. This certifies the phase's
checked hygiene/prose surfaces, not the still-missing capstone or its final
aggregate. The postcommit source identity and range check are recorded in the
following report amendment.

## Unmet rows

REQ-BV-ALLOC, REQ-BV-OPS, REQ-BV-RUN, REQ-BV-REUSE, REQ-BV-JOIN,
CHK-BV-CONTROLS; INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY,
INV-SEMANTIC-NONVACUITY, INV-TRACE-EXECUTION, INV-STORE-AGREEMENT,
INV-READ-BACKING, INV-WORD-WIDTH, INV-ADDRESS-WIDTH,
INV-INSTRUCTION-ATOMICITY, INV-PROGRAM-ACCOUNTING,
INV-ORACLE-INDEPENDENCE, INV-VALIDATION-REACH, INV-ALL-SIZE,
INV-PROOF-SEPARATION, INV-NO-SYNTHETIC, INV-CATEGORY-SEPARATION,
INV-PUBLIC-COMPOSITION, INV-CERTIFICATE-ANTI-BYPASS,
INV-MUTATION-REPRODUCIBILITY, INV-GLOBAL-PHYSICAL-MACHINE,
INV-WIDTH-SCALING; REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY,
REPLAY-SUBPROCESS-DEADLINE. No row is narrowed or marked inapplicable.

## Proof digestion and next consumer

Both-bit select can share the existing false-select source: complement only a
loaded raw data word when selecting true, preserving its actual length and
positions. Store both target-specific exception directories; their flags keep
their original values. The normalization theorem now proves the semantic
identity needed by that route.

The next checked consumer is the generic physical reader, followed by a full
generic select refinement and the all-size safety/allocation join. Its live
obligations include descriptor erasure, same-store reply dependence, all
intermediate width bounds, both directory capacities, and final code/scratch
accounting. A skeptical graduate student should ask whether those metadata
loads and normalized replies actually determine each returned position on
every exceptional route. The existing helper theorem does not answer that yet.

Two independent source inventories found an additive path without shared
Packed edits. Contract review and executable feasibility evidence are being
prepared; no formal obstruction was found. Final full-target independent audit,
coordinator acceptance and integration remain separate stages.

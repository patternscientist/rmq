# BV-1 parameterized exceptional-route controls

Status: CANDIDATE_COMPLETE for this bounded leaf. Frozen before implementation under governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f` and continuation checkpoint
`645a0502b9da9ad6444edbe44759e1c2c5661f25`. The inherited canonical proof-sprint
preflight and completion gate apply. This worker owns only
scripts/packed_bitvector_exceptions.lean, scripts/packed_bitvector_exceptions.ps1,
this document and uniquely named command records. Other workers' files remain
untouched. Root owns commits, ledgers and whole BV-1 acceptance.

## Frozen assignment and assertions

Implement and close an exact version1 nonempty registry, in this order:
long-super-false, long-super-true, sparse-local-false, sparse-local-true.
Each fixture builds kernel-inhabited GenericSelect.SparseExceptionSelectData
records for both Boolean banks, with shared wordSize1, superStride2,
localStride2 and localSlotsPerSuper1. Input is [target,!target,target]; queried
occurrence is1, with independent Succinct.select result some2 / packet3.
The opposite target has its own valid record and occurrence count.

The actual run is runArray suppliedMemory (PackedBitvector.program .select).toArray
((PackedBitvector.source .select).size+1) (PackedBitvector.initial .select target 1).
The program and initial state are the existing full Source definitions. Charged
setup, targetSetup, physical reader and compiler are unchanged. The supplied
numeric memory serializes these valid parameterized components with the existing
descriptor and dense-word constructors, both banks, and shared chunk tables.
It is a valid parameterized component allocation, not `Allocation.memory` from
the canonical global builder.
No logical reader callback or metadata-only initial-state substitution is used.

The production verdict requires the independent List packet in result, halted
status and output register513; all receipts successful and backed by the same
supplied memory; steps at most the actual source budget; a transition executing
the first physical span load `.load 8259 8261` with before.regs8192=12 for long
or16 for sparse, with exact addressed successful receipt; and absence of the
opposite exceptional segment. The observed route comes from returned transitions.

The same production verdict accepts the expected route and rejects a replay
which changes only its expected segment to the opposite route. Wrong-route
failure must preserve the correct answer and identify route failure, with an
expected-accept replay before and after. Source files are never mutated by this
control. Exact literal case registry and observed PASS-name order/count are
checked independently; silent omissions or duplicates reject.

The wrapper exercises eight exact production selector replays: omitted, valid
(long-super-false), empty, whitespace, malformed(long super), unknown(no-such-case),
padded( long-super-false ), incompatible(Case plus ListRegistry). Expected exits
are0,0,2,2,2,2,2,2 with exact output surfaces. PSBoundParameters distinguishes
omitted and explicitly empty. Each run has a fresh versioned timestamped evidence
tag, bounded owned process tree, pinned direct v4.22.0 toolchain, one thread,
exact source import-closure hashes and scoped tracked-status restoration checks.

| ID | Required result | Exact consumer/control | Status |
| --- | --- | --- | --- |
| EX-VALID | Both banks inhabit SparseExceptionSelectData with shared geometry | Explicit record type, all-q semantic fields, bounded tables/rank/raw stores and capacity fields; startup-v3 | CANDIDATE_COMPLETE |
| EX-RUN | All four actual full programs return the independent List answer and observe the assigned physical exceptional route | Same run supplies packet, transitions, receipts and source budget; replay-v1-omitted | CANDIDATE_COMPLETE |
| EX-NEGATIVE | Same verdict rejects wrong expected route and accepts restored route | Expected-accept / wrong-route expected-fail / expected-accept production replays; replay-v1 | CANDIDATE_COMPLETE |
| EX-SELECTOR | Exact four registry and eight strict selectors | Actual wrapper and complete observed-name sequence; replay-v1 | CANDIDATE_COMPLETE |
| EX-REPLAY | Bounded replay and restoration | Unique owned stages, hashes/status/whitespace and exact durable results; replay-v1 | CANDIDATE_COMPLETE |

These are valid alternative parameterized directories. They do not claim that
the canonical global builder marks a length3 span exceptional. Canonical-global
long/sparse cases remain covered by the universal correctness and safety proofs;
finite exceptional controls establish branch execution on valid parameterized
components only. Existing small canonical main fixtures cannot reach these
routes. No full BV-1 control or capstone row is closed by a draft or startup.

Verification: prepare offline, then after explicit build-slot grant check Lean
startup before a known fixture and the complete registry; repair ordinary errors
narrowly. Run exact record/run bridge consumer and axiom diagnostics, all selector
and wrong-route controls, then trust and whitespace scans. No aggregate gate.

## Exact record and evaluator consumers

The fixture source contains the following all-input propositions. A startup
check must elaborate the constructors and these consumers without proof holes;
the runtime checks then use those exact constructors.

```lean
data (long target bank : Bool) :
  SparseExceptionSelectData (bits target) bank 4 4

data_geometry (long target bank : Bool) :
  (data long target bank).wordSize = 1 ∧
  (data long target bank).superStride = 2 ∧
  (data long target bank).localStride = 2 ∧
  (data long target bank).localSlotsPerSuper = 1

data_select_exact (long target bank : Bool) (occurrence : Nat) :
  ((data long target bank).selectCosted occurrence).erase =
    Succinct.select bank (bits target) occurrence

fixture_run_eq (long target : Bool) :
  runArray (memory long target) (PackedBitvector.program .select).toArray
    ((PackedBitvector.source .select).size + 1)
    (PackedBitvector.initial .select target 1) =
  run (memory long target) (PackedBitvector.program .select)
    ((PackedBitvector.source .select).size + 1)
    (PackedBitvector.initial .select target 1)
```

For each long/sparse choice, `memory` uses `data long target false` and
`data long target true`, the common raw words from the false bank (their input
bits and word size are identical), all16 directory arrays from each bank,
and the production rank/select chunk tables. `Experiment.descriptorsFrom`
assigns bit offsets into their common flattened payload; `denseWords` packs
that payload. Both descriptor banks and23 scalar headers occupy the charged
207-word prefix. The initial state carries the ordinary request and target;
the production setup loads the headers and chooses the target bank.

The record proofs are stronger than the four queried occurrences: each bank's
directory semantic fields cover every occurrence, including saturation and
absent selects. For the fixture input, at most two occurrences exist in either
bank, so each valid occurrence uses super slot0. A marked super selects the
long offsets; an unmarked super uses the singleton marked local entry and the
sparse offsets. No valid occurrence reaches an invented dense witness.

The replay campaign has exactly11 entries: the eight frozen selector controls
plus the expected-accept, wrong-route expected-fail, expected-accept sequence.
The omitted selector executes all four fixture names in the frozen order.

## Development diagnostics

The first startup diagnostic (`exception-controls-startup-v1.json`) rejected
ordinary constructor elaboration: singleton rank parameters, computable
logarithm simplification, raw list membership, and a large closed payload-bound
calculation. The revision uses explicit singleton rank parameters and proves
the existing canonical overhead is at least512 symbolically, then proves the
small concrete payload bound. This preserves the original record capacity
predicate.

The second startup diagnostic (`exception-controls-startup-v2.json`) reduced
the remaining errors to raw `List.Mem` presentation in two table constructors
and unsupported named arguments on `Nat.le_trans`. All occurrence/route
semantic field proofs elaborated. The next revision exposes list membership
explicitly and uses the inferred middle bound512. No failed startup is runtime
evidence or acceptance.

## Proof digestion

Conceptually, these fixtures retain the valid generic select records while
choosing small exceptional directories deliberately. Thus the real machine can
exercise both exceptional branches without allocating the astronomical input
needed to make the canonical global classifier choose them. Both banks remain
valid and share the geometry loaded by charged setup.

There are no extra semantic hypotheses on the record consumers. The finite
machine controls instantiate the fixed three-bit inputs and occurrence1;
their answer comes independently from the list semantics. The live limitation
is classifier reach: these controls establish execution on valid parameterized
components, while the separate universal canonical proofs carry the all-size
canonical result. A skeptical reader should check that the observed route is
taken from actual machine transitions, that the supplied memory is the one
backing every receipt, and that the wrong-route replay fails that very verdict
while preserving the correct answer.

## Checked results and replay

All records below are under `docs/internal/extensions/bv1/commands/` and were
produced on checkpoint `645a0502b9da9ad6444edbe44759e1c2c5661f25` with the
documented shared working-tree changes. They do not claim a globally clean tree.

| Record | Result | Owned Lean duration / campaign wall time |
| --- | --- | --- |
| exception-controls-startup-v1.json | FAIL, ordinary constructor diagnostic | 7.387s |
| exception-controls-startup-v2.json | FAIL, remaining membership/transitivity diagnostic | 9.956s |
| exception-controls-startup-v3.json | PASS, complete record and all5 axiom consumers, no local warnings | 7.108s |
| exception-controls-known-v1.json | PASS, first actual long-super-false run | 9.076s |
| exception-controls-replay-v1-omitted.json | PASS, exact4 actual runs in order | 12.461s |
| exception-controls-replay-v1.json | PASS, exact11/11 selector/route controls | 105.413s wall |

The four returned traces had the following observations. Every row had packet3
in result, halted status and register513, every receipt successful and backed
by that run's supplied memory, and the actual source budget was10030.

| Fixture | Segment12 loads | Segment16 loads | Steps |
| --- | --- | --- | --- |
| long-super-false | 1 | 0 | 792 |
| long-super-true | 1 | 0 | 802 |
| sparse-local-false | 0 | 1 | 1091 |
| sparse-local-true | 0 | 1 | 1101 |

The expected rejection record is
`exception-controls-replay-v1-route-reject.json`. The child exits1 and reports
`packetOK=true expected=3 actual=some 3 expected-segment=16 long-loads=1
sparse-loads=0 routeOK=false backed=true steps=792 budget=10030 wrong-route=true`.
The wrapper campaign requires exactly that failure class and exit, with accepted
controls before and after. The other selectors returned exactly0,0,2,2,2,2,2,2.
No timeout or output-limit result counted as a verdict.

The startup prints dependency sets for `data`, `data_geometry`,
`data_select_exact`, `offsets_exact` and `fixture_run_eq`. They use only the
standard `propext`, `Classical.choice`, `Quot.sound` axioms (the offset lemma
does not require choice). There are no holes or new axioms. Repository trust
and native-reduction scans returned no matches; tracked and owned-untracked
whitespace checks were clean. The PowerShell parser reported no errors.
Broad gates were skipped because this leaf changes only the bounded fixture
registry and runner; root retains final certification.

Source and wrapper frozen for these passing runs:

| File | Bytes | SHA256 |
| --- | --- | --- |
| scripts/packed_bitvector_exceptions.lean | 14618 | DC3A964CDE6DE9AC1222761BFFB89B3D6D783708D3661DE20EF9EF77134E136F |
| scripts/packed_bitvector_exceptions.ps1 | 11128 | F16EDBFC6578043DBAD17BEE9F97FD2B1A569E2BBBBA622958F1F65195A7BD64 |

Every passing record hashes134 files in the exact local source import closure
and runner/toolchain configuration, before and after. The final campaign records
`exactRestoration=true`, `scopedStatusRestored=true`, `whitespaceCheck=true` and
the explicit pre-existing dirty-tree baseline. Source is never patched during
the wrong-route control. Child records and owned process receipts make each
invocation replayable; the owned helper uses the direct pinned v4.22.0 toolchain,
one Lean thread, a180-second child deadline and bounded process-tree cleanup.

From the repository root, these production commands replay the decisive checks
with fresh automatically generated evidence tags:

```powershell
pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -ReplaySelectors
pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -Case long-super-false -WrongRoute
```

The final standalone command is expected to exit1. `-ReplaySelectors` includes
the complete registry through its omitted-selector child, so a separate full
registry invocation is unnecessary for the same unchanged source.

No shared production definitions, acceptance matrix, public API, ledger or
commit were changed by this leaf. No new architectural or workflow decision was
needed: this implements the already-frozen parameterized exceptional control
row. Whole BV-1 acceptance remains with the coordinator.

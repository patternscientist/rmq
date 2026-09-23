# PQ1 coordinator acceptance and integration record

Status: **ACCEPTED** for the PQ1 primitive packed query milestone and the
revised E1/PQ1 roadmap node. This records coordinator acceptance, not a new
mathematical theorem, a release-wide audit closure, or novelty priority.

## Exact identities and ownership

- Governance/base: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Worker: PQ-1; branch `codex/fully-charged-packed-query-v1`.
- Fresh blind auditor: PQ1-A1; original target
  `4c89378f0c70aee272a56a12b7e70fb61e687e61`.
- Repaired and fully gated source:
  `6562ff62d14b17e918e7149f896bd0657ffd5aa0`.
- Immutable audit report commit:
  `d21b190139fa810291ae271974ec00cde58af965`;
  [full propositions, object chains and falsification evidence](../audit_reports/PQ1_FRESH_BLIND_4c89378.md).
- The original target failed its mandatory gate and is not certified by the
  later results. P1 denotes that failed required gate, not a Lean trust defect.
- This follow-up changes current wording, status, one public docstring and
  dated internal audit-report classification with six regression controls;
  all theorem definitions, statements, proof bodies, primitive semantics,
  consumers, Lean mutation registry cases, cost constants and toolchain are preserved.
- Integration destination: local `main`, by fast-forward to this accepted
  branch after the final follow-up checks. The branch tip and `main`
  reachability identify the integration commit without a self-referential SHA.
  The user explicitly requested fixes followed by merge; no remote push is
  inferred. The active coordinator worktree and milestone branch are retained
  for the audit evidence and continued work, rather than marked retired.

## Findings and coordinator decisions

| Finding | Decision and evidence |
| --- | --- |
| P1: inherited runtime selector remained present but empty under PowerShell 7 | Closed by 6562ff6: actual environment-entry removal, a stale-selector boundary regression and unchanged fail-closed parsing. Both-host focused runtime and full replay passed. |
| P3: “straight-line” prose hid the existence of forward conditional branches | Closed in this follow-up: current public descriptions and the declaration-adjacent docstring say “loop-free”; the review packet explains forward jumps and the fixed program. Historical audit/design records retain their original wording. |
| Missing coordinator disposition and stale pending-verification prose | Closed here after reconstructing the audited 34-row matrix and checking the completed evidence. Current publication surfaces and manuscript now distinguish accepted PQ1 from open release-wide, preprocessing and serialized-payload work. |
| Per-commit CI rejects report-only commit 3c8097e as a missing workflow decision | Correct the bounded dated internal audit-report classification; both-host regression and all incoming historical commits are checked. The eight historical certification exceptions and audited commits are unchanged. |

The fresh source audit plus one same-session tooling correction review is
accepted under the existing audit protocol. The correction was nonmaterial
to the mathematical/public/trust surface: it repaired startup environment
removal and added its boundary regression. P1 severity does not make that a
new theorem or model. The original source audit remains the independent
audit; the correction review is not mislabeled a fresh repaired-target audit.
This final wording/status and report-classification pass changes no theorem or acceptance requirement.

## Requirement closure

The coordinator closes every frozen ID below. E1–E9 refer to the exact
propositions and composition chains in the immutable audit report above,
including the identical `buildMemory xs`, program, initial state, actual run,
capacity expression, width and validity guards. The audit was reviewed with
the source and completed execution records; a theorem-name inventory or a
legacy worker status cell is not the acceptance basis. Original requirement
and invariant bytes are preserved in `PQ1_ACCEPTANCE_MATRIX.md`.

| ID | Coordinator disposition and evidence |
| --- | --- |
| REQ-PQ1-CONSTRUCTION | ACCEPTED. Source satisfied: E1, numeric builder and closed primitive run; E2 actual returned register chain. |
| REQ-PQ2-EXECUTION | ACCEPTED. Source satisfied: E2/E5, complete result and ordered-read refinement through both selects, LCA/fringes/interior and final rank; canonical interface discharge. |
| REQ-PQ3-SPACE | ACCEPTED. Source satisfied: E3, exact complete allocation/program/register expression and both checked residuals; identical E1 execution memory. |
| REQ-PQ4-WIDTH | ACCEPTED. Source satisfied: E3/E4, logarithmic width, dormant constructor-complete encoded fields and actual prefix/transition/read arithmetic safety. |
| REQ-PQ5-COST | ACCEPTED. Source satisfied: E4, fixed finite program, halting within its fuel, actual transition/category partition; scalar arithmetic model explicit. |
| REQ-PQ6-COVERAGE | ACCEPTED. Source satisfied: E2/E4/E5/E6, no readiness premise, source branches include rare/global paths, ordered repeats and empty/dead semantics preserved. |
| REQ-PQ7-INPUTS | ACCEPTED. Source satisfied: E2/E6, total Nat wrapper and leftmost half-open contract; all valid endpoints representable; charged invalid guard. |
| REQ-PQ8-UNIFORMITY | ACCEPTED. Source satisfied: E1/E4, closed code, metadata prefix charged, no n-specialized query constants. |
| REQ-PQ9-PUBLIC | ACCEPTED. Source satisfied with optional P3 terminology follow-up: E7/E9, identical alias/import, typed consumers and digestion, properly separated costs. |
| CHK-PQ10-VERIFICATION | ACCEPTED. Satisfied at repaired target 6562ff6: both required host aggregates, exact full PQ1 replay, supplemental probes, preflight, source identity and hygiene pass. Persisted report-tree strict claim-drift, applicable strict design and whitespace checks pass; `.lake/pq1-report-checks-final.json` binds these results to the report SHA256. Original-target failure and environment-limited attempts are retained below. |
| REPLAY-EXACT-REGISTRY | ACCEPTED. Satisfied at repair target: E7/E8 and both-host full replay, exact 38-case registry/selection, inventory and all diagnostic/expected-accept controls. |
| REPLAY-SELECTOR-NONVACUITY | ACCEPTED. Satisfied at repair target: E8 and both-host full replay; explicit empty/invalid selectors reject, omitted selection runs all cases, valid selection is exact, and stale runtime-channel removal is checked at the real host boundary. |
| REPLAY-SUBPROCESS-DEADLINE | ACCEPTED. Satisfied at repair target: E8 and both-host full replay; intentional deadline control kills its live descendant, actual stages finish without resource failure, restoration and clean-tree checks pass. |
| INV-STORE-IDENTITY | ACCEPTED. Source satisfied: E1/E3/E5 same `buildMemory xs` in counted expression, actual run, receipts and agreement. |
| INV-VALUE-DEPENDENCY | ACCEPTED. Source satisfied: E2 actual read-to-return chain, E5 physical value refinement; committed `SpanAssembly.lean:499-503` changes each crossing input reply and compares `.result`; supplemental whole-query data mutation changes the returned packet at physical data addresses 174 and 177 (continuation). |
| INV-SEMANTIC-NONVACUITY | ACCEPTED. Source satisfied: E2/E4/E5 derived operational reader/source/safety predicates, not True or membership-only labels. |
| INV-TRACE-EXECUTION | ACCEPTED. Source satisfied: E5 `Run.reads = transitions.filterMap receipt` and indexed actual prefix proof. |
| INV-STORE-AGREEMENT | ACCEPTED. Source satisfied: E5 actual consumed lookup agreement determines the entire same-program run, including none replies. |
| INV-READ-BACKING | ACCEPTED. Source satisfied: E5 indexed transition/instruction/operand/lookup conjunction. |
| INV-WORD-WIDTH | ACCEPTED. Source satisfied: E3/E4 stored cells, registers, status result and transitions fit one width. |
| INV-ADDRESS-WIDTH | ACCEPTED. Source satisfied: E3/E4 constructor-complete static encoding plus every actual load operand, sentinel/dead/failed address checks. |
| INV-INSTRUCTION-ATOMICITY | ACCEPTED. Source satisfied: E4 scalar execute cases; all iterative high-level work expands into charged code. |
| INV-PROGRAM-ACCOUNTING | ACCEPTED. Source satisfied: E1/E3 fixed program encoding and scratch counted; varying metadata serialized and loaded. |
| INV-ORACLE-INDEPENDENCE | ACCEPTED. Source satisfied: E8 independent literal answers/scanWindow and reference-route assertions. |
| INV-VALIDATION-REACH | ACCEPTED. Source satisfied: E8 actual numeric-memory primitive evaluator and checked array equivalence, plus two list-run controls. |
| INV-ALL-SIZE | ACCEPTED. Source satisfied: E2/E4/E6 universal canonical list theorem without readiness or geometry exclusions. |
| INV-PROOF-SEPARATION | ACCEPTED. Source satisfied: E1/E2 proof predicates and observations never enter primitive state or instruction data. |
| INV-NO-SYNTHETIC | ACCEPTED. Source satisfied: E4/E5 actual transition-derived reads/categories; read-only logical trace excludes synthetic projected events. |
| INV-CATEGORY-SEPARATION | ACCEPTED. Source satisfied: E3/E4/E6/E9 separate bits, proof observations, scalar steps, mathematical input checking, preprocessing and Lean runtime. |
| INV-PUBLIC-COMPOSITION | ACCEPTED. Source satisfied: E2/E3/E4/E5/E6/E7 all advertised fields use identical allocation, execution and validity domain; representability guards are explicit. |
| INV-CERTIFICATE-ANTI-BYPASS | ACCEPTED. Satisfied at repair target: E7 exact-type projections and E8 full replay on both hosts reject every field/public collapse at its expected surface. |
| INV-MUTATION-REPRODUCIBILITY | ACCEPTED. Satisfied at repair target: E8 committed cases replay on both hosts with expected surfaces, restored acceptance and clean-tree checks; supplemental sources and precise verdicts appear below. |
| INV-GLOBAL-PHYSICAL-MACHINE | ACCEPTED. Source satisfied: E1/E5 one complete pre-execution numeric store, charged metadata and physical span reads; no suffix-only embedding. |
| INV-WIDTH-SCALING | ACCEPTED. Source satisfied: E3/E4 one query-independent logarithmic width bounds stored, dynamic and dormant static quantities together. |

All optional-P3 references in the frozen audit table above describe the audit
at its exact source target; the wording follow-up is closed by this record.

## Verification and scope of reuse

Both full `scripts/gate.ps1` runs passed at 6562ff6 with all 18 advertised
checkers invoked, no timeout and no output overflow: PowerShell 7 in 5654.834s,
Windows PowerShell 5.1 in 7415.157s. Each includes all 38 PQ1 mutation cases,
15 runtime fixtures, exact selector/registry/deadline/restoration controls,
41 M1 cases, 21 and 16 EG-CP cases, eight standard-only axiom inventories,
claim/paper checks and all 16 paper topology cases. Exact local artifacts:
`.lake/pq1-aggregate-pwsh-6562ff6.json` and
`.lake/pq1-aggregate-powershell-6562ff6.json`.

The full PQ1 replay reports are
`run-874f9ebfe40043e5b45fd72b4663141d/report.json` and
`run-ab42523e17a64ec9ac6ba6d81d8e3a46/report.json` under `.lake/pq1-replay/`.
Supplemental probes are reproduced verbatim in the durable audit report;
they include returned-value dependency, removed/unread-added allocation and
exact-type sibling-memory/forged-prefix rejection with positive controls.
The auditor independently verified both aggregates, both full replay records,
all 34 frozen IDs and the final report SHA256
`F22B7DDC84C576545C5B815547D6FAAFF21F90B37E7E2918862B6B94D83F3E72`.

Follow-up verification is recorded in `.lake/pq1-merge/verification.json`:
the affected public import and exact-type consumer, strict production claim
drift, strict design/workflow checks, paper/citation and paper topology checks,
trust/hygiene, frozen-matrix byte integrity and whitespace. Per-commit history
checking found that the dated internal report in 3c8097e was incorrectly
classified as a new workflow decision. The follow-up recognizes that bounded
Markdown report convention, preserves executable/public/plan/prompt controls,
and checks the production classifier regression on both PowerShell hosts and
every incoming non-merge commit. See WDD-20260912-PQ1-016. The already-passed
Lean mutation campaigns are not repeated for wording/status and report-path
classification edits; neither their code nor the mathematical source changed.
The merge is a fast-forward,
so it introduces no combined source tree beyond the checked branch.

The current-surface inventory is the 18 paths matched by
`CLAIM_DRIFT_POLICY.json.currentFactSurfacePathRegex`, plus the PQ1 public
docstring, current digestion, manuscript and its editing-rule-5 companions.
All were inspected for this status/terminology scope. No bibliography,
novelty claim, model operation, numeric bound or frozen requirement is changed.

## Digestion and next work

Conceptually, one fixed loop-free program now obtains RMQ answers from a
counted numeric allocation, charging metadata reads and every primitive
transition. For an ordinary list and valid half-open range, it returns the
leftmost answer with one uniform instruction bound and succinct asymptotic
data/code/scratch space. Live assumptions remain unit-cost scalar arithmetic,
the pinned Lean/Std trust base, unbounded preprocessing and the outer uncharged
Nat encoding check. A skeptical reader should ask about useful finite-size
bounds and preprocessing in the same model, not infer practical compactness
from asymptotic absorption.

This closes PQ1 and the revised E1 route; S1 serialized-payload querying,
preprocessing, tighter path-sensitive cost, extraction and V1 release-wide
verification remain separate. No successor proof worker is launched during
this merge-only request. The branch/worktree are intentionally retained as
the active coordinator workspace; unrelated accumulated worktrees are outside
this integration's cleanup scope.

# LIFE-1 verification coverage plan

This plan freezes check ownership and coverage before implementation. It records
planned work, not successful verification or candidate completion. Completed
commands must be appended with exact source identities, command lines, UTC times,
durations, exit statuses, deadlines, artifact hashes and platform limitations.

- Worker: LIFE-1; task title: `(LIFE-1) Implement continuous succinct construction and queries`.
- Worktree: `C:/Users/poin/.codex/worktrees/8941/RMQ`.
- Branch: `codex/life-1-continuous-packed-lifecycle`.
- Base and initial HEAD: `bf31f983205175481fcb659caa4dfb70ef43e361`.
- Workflow governance: `7b227c49ef2ec044b702126cc41c9add847eed01`.
- Applicable role: `rmq-proof-sprint`; runtime catalog:
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.
- Skill preflight: PASS on this exact base with the actual runtime catalog.
- Source contract: exact UTF-8 prompt bytes embedded in `CONTRACT_REQUIREMENTS.json`;
  SHA-256 `f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18`.
- Frozen matrix: 43 IDs, eight columns, complete row byte preservation.

## Roles, coverage and unique failure modes

All commands run with the explicit worktree above. Initial dirty-diff state is
only the new lifecycle contract/identity artifacts; implementation receipts must
replace that description with the actual tree or source hashes they consumed.
“Pending” is uncovered evidence, never a pass. A checked theorem type and its
object/guard chain are required in addition to command success.

| Role | Check / exact command or required future invocation | Changed paths and rows | Unique failure mode | Scheduling/deadline and initial outcome |
| --- | --- | --- | --- | --- |
| Development-loop and final-required | `powershell -ExecutionPolicy Bypass -File scripts/lifecycle_contract_integrity.ps1 -RepositoryRoot C:/Users/poin/.codex/worktrees/8941/RMQ` | Contract artifacts; L1-20, CHK-SCOPE | Missing/duplicate/unknown/reordered IDs, wrong column count, strict UTF-8 failure, late-clause requirement drift, changed complete row or prefix. Full embedded source is pinned independently. | In-process reads only; use 60 seconds wrapper margin. Initial independent freeze check PASS; dedicated checker result is recorded in `contract_integrity.json`. Rerun before expensive final verification and after appended evidence. |
| Development-loop | `lake build <narrowest changed lifecycle module>`, then its direct consumer | New `RMQ/Core/WordRAM/Lifecycle/` modules and their actual consumers; relevant L1-01 through L1-16 and inherited invariants | Local elaboration/type failure or adapter consumer mismatch | Heavy mutex required. Warm comparable experimental leaves: 2–28 seconds; use 180 seconds only after verifying prerequisite artifacts. Cold closure may need about 3600 seconds; allow 7200 seconds pending measured evidence. No Lean builds are assigned to the contract-freeze helper. |
| Development-loop | Direct kernel fixtures and focused production operational controls, with exact invocation recorded once their owned paths exist | New lifecycle semantics, `RMQ/Validation/LifecycleContract.lean`, `RMQ/Validation/PackedLifecycle.lean`, dedicated `scripts/lifecycle_*`; L1-01, L1-04 through L1-11, L1-14 through L1-18 and matching INV rows | Wrong producing source, skipped initialization, stale tail, absent source word, omitted release, backward overlap, retained keys, wrong entry, overflow or second-query dirty bank | Expected predicates/guards/objects must be written before verdict classification. Run small known cases first. Deadline derives from the actual target's measured startup and execution, not a cold build inside a short fixture budget. Pending. |
| Final-required | `lake build` | Entire final candidate; L1-20, CHK-FINAL | Default build integration failure | Shared heavy mutex; exact unchanged default build reference is 30.677 seconds warm. Cold predecessor closures may take about 3600 seconds; budget 7200 seconds for a cold build, revise only from evidence. Pending. |
| Final-required | `lake build RMQ.Core.WordRAM.Lifecycle.Capstone RMQ.Validation.LifecycleContract rmq_lifecycle_validate` | Final public source, independent expected-type consumer and new executable target; L1-08 through L1-18, L1-20, INV-PUBLIC-COMPOSITION, INV-CERTIFICATE-ANTI-BYPASS, INV-VALIDATION-REACH | Named capstone/consumer/validator targets missing or failing despite default build | Heavy mutex; run after prerequisite/default-build scheduling is understood. Warm budget 300 seconds, cold budget 7200 seconds until measured. This separately named target check is explicitly required by the task. Pending. |
| Final-required | Bounded startup/shape probe, one exact known selector, then full new validator and exact lifecycle dependency checks; commit exact production registry and invocation before final use | Executable layer and dedicated control runner; L1-15, L1-17, L1-18, INV-ORACLE-INDEPENDENCE, INV-VALIDATION-REACH, INV-MUTATION-REPRODUCIBILITY | Validator bypass of new layer; vacuous registry/selector; mixed diagnostics; leaked subprocesses or unrestored mutations | Heavy mutex for full replay. Separate build prerequisites from runtime deadlines. Record actual startup/known-case timing before setting full replay budget. A provisional 120-second startup limit is diagnostic only; investigate initialization before increasing it. Pending. |
| Final-required | Exact public type inventory and axiom inventory under the final narrow lifecycle import, including the independently typed consumer | New capstone/headline/validation surfaces; L1-16, L1-20, INV-PROOF-SEPARATION, INV-CERTIFICATE-ANTI-BYPASS | Unexpected hypotheses/axioms or consumer that merely adapts to current declaration type | Record exact committed inventory command/file once definitions exist. `#check` and `#print axioms` alone cannot establish expected-type dependency. Narrow warm budget 300 seconds; observe cold prerequisite guidance. Pending. |
| Development-loop and final-required | `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml`; `rg -n "native_decide|Lean\.ofReduceBool" RMQ` | Owned proof/trust surfaces and inherited repository hygiene; L1-20, INV-PROOF-SEPARATION, CHK-FINAL | Forbidden trust changes or hidden native decision bridge | 60 seconds margin; retain and classify exact matches, with unchanged inherited matches separated from new owned source. `rg` exit 1 means no matches, not a tool failure. Pending final-tree scan. |
| Final-required | `git diff --check`; after final commit, `git diff --check bf31f983205175481fcb659caa4dfb70ef43e361..HEAD` | All scoped candidate edits; L1-20, CHK-FINAL, CHK-SCOPE | Working-tree or committed-range whitespace defects | 60 seconds margin. Both are required; a clean worktree does not certify commit bytes. Pending final range. |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base bf31f983205175481fcb659caa4dfb70ef43e361`; for each actual new commit, `-Strict -Base <exact parent> -Head <exact commit>` | Owned Lean/native model paths require design ledger; owned checker/contract/report/process paths require workflow ledger; L1-19, L1-20, CHK-FINAL | Missing decision rationale masked by another commit or an implicit empty diff | 120 seconds margin. Inspect existing production classifier; no broad allowances or retrospective exceptions. Contract checker and plan require a workflow decision before their commit. Pending root-owned ledgers and commits. |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` after complete report creation | Exact narrow candidate prose, report and new docstrings; L1-19, L1-20, INV-CATEGORY-SEPARATION, CHK-FINAL | Unsupported candidate claim, stale report or scope/campaign conflation | 120 seconds margin; rerun after relevant prose/report changes. No predecessor public-surface migration is assigned. Pending. |
| Final-required | Exact final source/receipt hashes, frozen rows, permitted changed paths, final report, exact branch/base/commit and clean tracked/untracked state verification | All owned paths and `REPORT.md`; L1-20, CHK-FINAL, CHK-SCOPE | Stale source receipts, newline-serialization confusion, uncommitted or out-of-scope files, omitted row dispositions | Read/check only; 120 seconds margin. Distinguish workspace bytes, exact Git blobs and historical newline bytes. Avoid self-referential report/commit hashes by stating the precise hashed object and later receipt. Pending. |
| Conditional, coordinator-owned | Complete repository `scripts/gate.ps1`, final certification after formal source/native-boundary scheduling, and independent fresh-blind exact-candidate audit | Whole campaign frontier, not only local formal work | Aggregate/native/publication/independence failures beyond this local check set | Do not run independently or duplicate predecessor campaigns. Aggregate reference is several hours. Pending campaign phases remain mandatory and do not excuse missing local checks. |

## Execution and restoration policy

Serialize expensive Lean/Lake/default-build/full-replay work with
`Local\RMQLifecycleImplementationHeavy20260920`. Use the existing
`scripts/owned_process_tree.ps1` helpers for owned subprocess deadlines/cleanup.
Allow only one heavy compiler per build tree and one host-wide aggregate slot;
do not share mutable caches across worktrees. Read-only research and bounded C
measurement probes may overlap. Record exact provenance for reused warm artifacts.

Before each replay, freeze the exact ordered case registry and source-to-case
mapping. Check missing, duplicate, unknown and explicitly empty selectors at the
actual command boundary; omission may mean all only when explicitly documented.
Expected-accept controls must distinguish genuine dependency changes from
irrelevant edits. Reject mixed expected/unrelated diagnostics, missing gates,
timeouts and nonzero unexpected exits. Prove owned descendants are cleaned up on
each required host and restore exact source hashes after mutations. No success
marker may follow an error. This policy governs lifecycle mutation/executable
runners; the contract-integrity checker itself has no selectors, subprocesses or
source mutations and always checks all rows.

Retain complete external command outputs and exits before compact summaries.
Keep bulky output outside staged source and identify its absolute local path and
SHA-256. For direct Lean negative fixtures, record the accepted predicate P,
challenged predicate Q, objects, guards and quantifiers and either identical
relations or a checked P-to-Q bridge. Never force an untrue proposed negative
control to fail simply to satisfy a registry.

On timeout or unexplained silence, inspect the identified child tree, CPU use,
artifact progress, missing direct imports and accidental full-build fallback.
Do not restart a healthy quiet process or rerun an unchanged ended timeout.
Record the material source, dependency, scheduling or evidence-based deadline
change authorizing any retry. An incomplete timed-out run supplies no successful
semantic verdict.

Checks are invalidated by changes to their consumed source/consumer/checker
closure. A docs-only edit invalidates relevant claim/design/contract checks, not
unrelated Lean compilation; state that dependency judgment in the final report.
The coordinator owns one complete aggregate after the candidate freezes. A final
report must distinguish completed checks, scheduling-only reused timings and
checks omitted by this explicit ownership division.

## Scope and downstream completion boundary

Only the task's listed lifecycle modules, additive headline, validation targets,
dedicated scripts, lifecycle target additions, extension artifacts, new proof
guide and narrow documentation/ledger updates may change. The contract-freeze
helper owns only the five assigned contract/plan/receipt files and dedicated
integrity checker, performs no Lean builds, creates no commits and writes no
final candidate report. Root owns source interfaces, ledgers and completion.

The completed local capstone must close every assigned implementation row.
Production native allocator ownership/capacity, publication-wide synchronization,
the complete aggregate and fresh-blind coordinator acceptance are separate
mandatory consumers. Nothing in this plan converts a local missing proof,
resource invariant, handoff, cost fact or executable check into deferred work.

## Append-only command evidence

The initial strict freeze compared all 43 complete requirement cells against the
exact external source prompt and its embedded byte-preserving copy, parsed all
eight nonempty columns, rejected ID differences/duplicates and confirmed that
the full active and frozen matrix bytes were identical. Source and artifact
hashes, checker controls and exact helper command outcomes are recorded in
`contract_integrity.json`. All proof/implementation rows remain Open until their
own operational and theorem evidence is appended to `ACCEPTANCE_MATRIX.md`.


## Final candidate-local reconciliation

This appended section records actual final evidence; the initial planning
table and historical freeze results above remain unchanged. The 43-ID current
dispositions and complete object chains are in ACCEPTANCE_EVIDENCE.md and the
append-only suffix of ACCEPTANCE_MATRIX.md. Candidate-local closure is worker
evidence, not coordinator acceptance, and is gated on S below.

- B: final default lake build passed in5.732s; the explicitly named Capstone,
  LifecycleContract, rmq_lifecycle_validate, Lifecycle headline and Provenance
  build passed in57.584s. Actual commands/times/outputs are
  .lake/lifecycle-final/default.result.json and named.result.json.
- T: lake env lean scripts/lifecycle_inventory.lean passed in135.302s;
  only subsets of propext, Classical.choice and Quot.sound occur; constant
  pins use no axioms. Both required repository trust-hygiene scans have zero
  matches. Receipt: .lake/lifecycle-final/inventory.result.json.
- N: corrected final validator source compiled in13.122s, native03 rebuilt
  in12.593s, and all16 cases passed in81.505s. The9-process replay includes
  startup, one exact focused case and5 exact selector negatives, with clean
  owned process receipts and matching before/after source/binary hashes.
  L14/L16 explicitly exercise comparison keys outside the same size-dependent
  signed word-input domain; both actual dirty-entry cases reject the skipped
  register400 clear through a checked full-entry-to-register bridge.
  See NATIVE_VERIFICATION.md and
  .lake/lifecycle-validator/da0d7bf710d148dfa5e439022fca3ede.
- D: actual final summary at
  .lake/lifecycle-dependency/20260921T021035666-83fc2827/summary.json reports
  passed=true,26 selected cases,23 expected rejections and3 expected accepts,
  matching exits, every original/private restoration=true and shadowRemoved=true.
  Summary SHA-256 is17d5798eb4a91699c2b938fa9f82e393652c43de9a28654976649c8c5ae29ed7.
  DEPENDENCY_VERIFICATION.md records all source edits, unchanged independent
  clients, exact diagnostic surfaces, final parser/selector/timeout-cleanup
  self-tests, and preserved rejected development campaigns.
- S: SOURCE_MANIFEST.json, FINAL_RECEIPTS.json and REPORT.md reconcile exact
  source identities, receipt hashes and static claim/design/path/whitespace/
  contract checks. Implementation commit is
  299ec6527ca2fbcf73cfc34e9de75f4a1f34140c; root reports its actual strict
  per-commit design check passed in3.854s. The evidence-only closing commit,
  its per-commit/range checks and clean-delivery verification are an invariant
  of submission. Actual post-closing-commit outcomes are recorded in external
  .lake/lifecycle-final/delivery.json and the submission message, without a
  self-referential claim about the report's enclosing commit.

The interrupted native01 build is not certified. Native02 and its72.571s
development replay used an earlier large-Int fixture; the actual word-width
inspection justified correcting that fixture and rerunning the changed binary.
Dependency development failures remain failures, not accepted case verdicts.
The final D summary above, rather than a case prefix or registered expectation,
is the complete campaign verdict.

Windows is the verified native host. Logical array size is distinct from native
backing capacity and alias freedom; comparison Int resources and model ticks
remain separate from numeric words and elapsed runtime. Warm build evidence is
not independent cold reproduction. No old validator or full repository aggregate
was independently run. Native consuming ownership/capacity, the scheduled
aggregate, blind exact-candidate audit and coordinator acceptance remain separate
campaign consumers; they do not excuse a missing local requirement.

Frozen historical files retain strict UTF-8/LF bytes. Reproduction must use an
LF-preserving checkout, such as git -c core.autocrlf=false worktree add at the
exact submitted commit, and preserve those bytes in later checkout operations.
The precondition covers CONTRACT_REQUIREMENTS.json as well as both matrices.
Default CRLF serialization is not claimed to pass raw-byte hashes; no silent
normalization, attribute change or global Git-config change is used.

LIFE-1-R1 successor verification is recorded in [repair-r1/VERIFICATION_PLAN.md](repair-r1/VERIFICATION_PLAN.md) and [repair-r1/REPORT.md](repair-r1/REPORT.md); original evidence and requirements above remain historical and unchanged.

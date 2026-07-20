# P1 RMQ Policy Hardening Worklog

Status: contract frozen before production edits. The original matrix preserves
that freeze snapshot; the closure table and observed ledger below are the
authoritative evidence/status updates.

## Worker And Contract

- Handle/title: P1 / (P1) Harden RMQ claim and decision policy.
- Exact base: 0b8490cb1dee4f02e7c72a5e097c1fa78361c588.
- Workflow governance: 7e0e6089251147b02365bc5603ebd2347902018f.
- Branch: codex/p1-rmq-policy-hardening.
- Worktree:
  C:\Users\poin\.codex\visualizations\2026\07\19\019f7ccf-62d2-7841-b02a-506c37d2e167\p1-rmq-policy-hardening.
- Named target: make retired cost 207 impossible to present as current on a
  governed surface, and replace enumerated design-sensitive coverage with a
  default-sensitive classifier whose narrow opt-outs are durable evidence and
  decision records.
- Downstream join: the aggregate gate and emitted worker contracts must consume
  the production claim scanner, the production design classifier, and their
  replayable regressions before later public-claim migrations are certified.
- Hard obligation: close the category boundaries through the production final
  verdict, not copied regexes, remembered path lists, or count-only fixtures.
- Forbidden shortcuts: no copied detector, catch-all history allowance,
  current-surface hand list, prose-only evidence, Lean/public theorem change,
  live document migration, E1 overlap, or transcript/scratch artifact.
- Stop conditions: every frozen row closes; or a precise policy-architecture
  obstruction requires coordinator choice; or a named external dependency
  blocks further work; or the user redirects.

## Base-Derived Inventories

The exact-base registry was reconstructed from
docs/internal/CLAIM_DRIFT_POLICY.json currentFactSurfacePathRegex and git
ls-files. It contains exactly 18 paths:

1. artifact/CLAIMS.md
2. artifact/README.md
3. docs/digests/PROJECT_DIGESTION_CURRENT.md
4. docs/FAMILY_SUMMARY.md
5. docs/internal/CLAIM_DRIFT_POLICY.md
6. docs/internal/RMQ_FINAL_ROADMAP.md
7. docs/PAPER_CLAIM_CORRESPONDENCE.md
8. docs/PAPER_MAIN_THEOREM.md
9. docs/PAPER_MODEL_ADEQUACY.md
10. docs/PAPER_RELATED_WORK.md
11. docs/PAPER_THEOREM_MAP.md
12. docs/PUBLICATION_STRATEGY.md
13. docs/RELATED_WORK_AND_LIMITATIONS.md
14. docs/ROADMAP.md
15. docs/TRUST_AUDIT_PACKET.md
16. docs/WHAT_IS_PROVED.md
17. docs/WORD_RAM_REVIEW_PACKET.md
18. README.md

README.md and docs/FAMILY_SUMMARY.md already state 210. The only expected
current-surface repair is policy explanation in
docs/internal/CLAIM_DRIFT_POLICY.md; no public document migration is allowed.

## Frozen Requirement-To-Evidence Matrix

| ID | Exact frozen requirement | Intended production behavior and evidence needed | Direct consumer / composition chain | Anti-vacuity mutation | Evidence / status |
| --- | --- | --- | --- | --- | --- |
| REQ-P1-CURRENT-COST-210-ENFORCEMENT | "on every registered current-fact surface, strict production scanning must reject prose that presents 207 as current/canonical/principled/uniform/modeled/query/charged-trace/trace-length/Costed.cost. The existing regression fixture r1r1-current-cost-207-control currently accepts this exact defect; replace that false control with a named rejection. Keep 210 accepted as the current bound." | The strict forbidden-retired-current-cost-bound policy includes 207 in the complete named role category; the real claim_drift_scan.ps1 -Strict returns nonzero and labels the term fail for every category representative, while a current 210 control exits zero. | CLAIM_DRIFT_POLICY.json -> claim_drift_scan.ps1 final allowance/strict verdict -> claim_drift_policy_regression.ps1 -> gate.ps1 and blocking CI strict scan. | Replace the false 207 control with a reject; add held-out role/order variants and current 210 accept control. | Open. |
| REQ-P1-HISTORICAL-COST-ALLOWANCE | "truthful, explicitly marked historical mentions of 207 remain accepted, as do frozen historical 76, 142, 328, and distinctly named live compatibility 352 roles. CLAIM-HISTORY-A07-COST or a more precise documented marker may carry the allowance, but an allowance word in an unrelated clause must not bypass a stale-current statement." | The existing production line allowance becomes an anchored controlled grammar: a marked historical-only clause, or the exact current-210-plus-retired-comparison shape already used by current surfaces, accepts; a marker or history word in a separate clause cannot authorize current 207. Advisory 328 and compatibility 352 remain non-strict and truthfully labeled. | Policy JSON allowance -> production scanner final verdict -> regression accept/reject controls -> gate strict scan. | Accept marked historical 207/76/142 and current-210-plus-history; reject "Historical context ...; current bound is 207" with the same marker; accept historical 328 and named compatibility 352. | Open. |
| REQ-P1-POLICY-TERM-TRUTH | "policy IDs, status strings, prose, and fixtures must not call 76 or 207 current. Preserve compatibility if renaming an internal term would break consumers; do not rename or delete any frozen public Lean identity." | Keep stable consumed policy IDs, change their status/pattern prose to call 76/142/207 retired or historical, document 210 as current, and rename the misleading 207 expected-accept fixture into a rejection without touching Lean. | Policy files and regression names -> scanner output/audit interpretation -> gate and worker evidence. | Static config checks fail if retired advisory/status text starts with or asserts current; repository search classifies every current-sounding 76/207 policy occurrence. | Open. |
| REQ-P1-DESIGN-COVERAGE-OPT-OUT | "replace the current proof/code-sensitive enumeration boundary with a documented opt-out/default-sensitive classifier. Newly invented Lean, public artifact/docs, validation, script, workflow, and repository paths outside an explicit neutral exclusion must require the appropriate DESIGN_DECISIONS.md and/or WORKFLOW_DESIGN_DECISIONS.md. Exclusions must be narrow semantic categories, not an expanding remembered list of sensitive names. The two decision-log files themselves and durable evidence-only/history/report classes need nonrecursive treatment." | design_decision_check.ps1 normalizes changed paths, classifies narrow neutral decision/evidence/history/report classes first, classifies workflow infrastructure by semantic roots, classifies Lean code as code even under tool roots, and defaults every other new repository path to code-sensitive. Correct changed decision logs satisfy the respective requirement without recursion. | Git base/worktree inventory -> production classifier -> strict exit -> CI and isolated-Git regression; template emits exact invocation. | Held-out unenumerated RMQ Lean, validation Lean, workflow script, public doc, and unknown repository path reject; worklog/audit/historical digest and decision-log-only controls accept. | Open. |
| REQ-P1-STRICT-BASE-NONVACUITY | "strict branch certification must not silently examine zero committed changes because -Base was omitted. Choose and document one compatible production behavior: require -Base in strict certification mode, or add an equally strong explicit mode that fails closed without a base. Update the worker template and completion gate so emitted prompts require -Strict -Base with the task's exact 40-character base commit. Preserve a deliberate non-strict local-worktree mode if useful." | Strict mode requires a syntactically exact, resolvable 40-character commit and never falls back; non-strict mode without Base inspects worktree/index/untracked paths as an advisory local mode. Template and completion gate require the exact-base command. | Worker prompt -> production design checker -> CI/event certification; completion gate audits emitted commands. | Strict without Base and strict invalid/short Base reject; non-strict without Base detects a held-out path and exits advisory zero rather than examining an implicit committed range. | Open. |
| REQ-P1-PRODUCTION-CLASSIFIER-REGRESSION | "add a named regression that executes the actual production scripts/design_decision_check.ps1 against isolated Git fixtures. Include category-level holdouts for an unenumerated RMQ Lean path, a new validation path, a new workflow script, an ordinary public doc, an explicitly neutral evidence/history path, missing code decision, missing workflow decision, present correct decisions, strict missing-base failure, absolute Windows paths if supported, and clean restoration. Do not validate a copied detector." | New design_decision_check_regression.ps1 creates isolated Git repositories, invokes the production checker in bounded child processes, asserts exit plus exact production diagnostic, verifies drive-qualified repository roots on Windows, and preserves the caller tracked tree. | Production checker -> new regression -> gate.ps1 exactly-once consumer. | Every listed category is a named case; missing decisions reject, correct decisions accept, and deleting or copying around the production invocation breaks expected diagnostics. | Open. |
| REQ-P1-GATE-WIRING | "wire the new regression into the aggregate gate exactly once with faithful exit propagation. The existing claim policy regression remains wired exactly once." | gate.ps1 invokes each regression once and immediately fails on its nonzero LASTEXITCODE; no second classifier or overwritten status. | Aggregate gate -> CI blocking repository gate. | Static invocation count equals one for each regression; design regression nonzero is propagated by its immediate Fail branch. | Open. |
| INV-P1-NO-PUBLIC-SEMANTIC-CHANGE | "do not edit README, FAMILY_SUMMARY, any other current fact surface, Lean code, theorem statements, frozen public identities, E1 matrices/worklogs, audit reports, roadmaps, legacy naming, or the M1 registry. Current main already states 210 consistently; do not manufacture a document migration." | Exact changed-path inventory contains only authorized policy/workflow files; no Lean or current public surface other than the authorized policy explanation changes. | Base..HEAD inventory -> coordinator integration review. | Compare changed paths to the frozen allowlist and rerun current-surface inventory. | Open. |
| INV-P1-E1-NONOVERLAP | "This task closes: the P1 workflow-policy rung only; it does not close E1, merge the campaign, change Lean semantics, or refresh legacy/M1 surfaces." | No E1, Lean, legacy, M1, campaign, merge, or public theorem path changes; worklog and report say candidate only. | Base..HEAD inventory and candidate declaration. | Search changed paths and report for unauthorized E1 closure/merge claims. | Open. |
| REPLAY-EXACT-REGISTRY | "REPLAY-EXACT-REGISTRY applies to the named policy mutation fixture inventory: duplicate IDs, missing required IDs, and verdict-count drift must fail." | claim_drift_policy_regression.ps1 carries an independent exact ordered ID sequence and pinned verdict totals, validates before execution, and runs cheap self-mutations proving duplicate, missing-middle, and verdict-flip rejection. | Frozen registry -> actual fixture objects -> production scanner executions -> final pinned totals. | duplicate-fixture-id, missing-required-fixture-id, and verdict-count-drift controls must each be rejected by the registry validator. | Open. |
| REPLAY-SELECTOR-NONVACUITY | "REPLAY-SELECTOR-NONVACUITY is NOT_APPLICABLE because no focused selector is part of this script contract." | No selector interface is introduced. | Not applicable. | Confirm both regressions run their full frozen/default case sets. | N/A by frozen contract. |
| REPLAY-SUBPROCESS-DEADLINE | "REPLAY-SUBPROCESS-DEADLINE applies only if the regression launches external Git/PowerShell children; every such stage needs a positive deadline, timeout failure, owned-process cleanup, and a cheap sleeper control." | Both regressions route external Git/PowerShell stages through bounded process helpers, classify timeout nonzero, terminate and wait for the owned process tree, and run a cheap sleeper timeout/cleanup control before semantic cases. | Bounded helper -> production child verdict -> regression exit -> gate. | sleeper-timeout-owned-cleanup must time out quickly, terminate, and leave no live owned child; semantic child timeout must fail. | Open. |
| INV-P1-INHERITED-CLAIM-CHECKS | "Preserve all inherited claim-policy attribution checks, 2^128 role checks, source/freshness/position checks, readWord-only checks, and tracked-tree restoration controls." | Existing fixtures and production paths remain in the exact registry; new validation is additive. | Claim regression exact registry -> production scanner -> aggregate gate. | Missing inherited middle fixture and changed final totals are rejected; existing path/context/restoration cases still execute. | Open. |
| CHK-P1-CLAIM-STRICT | "powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict"; "powershell -ExecutionPolicy Bypass -File scripts\claim_drift_policy_regression.ps1" | Both final production commands exit zero; the first reports zero strict failures and the second reports exact full-registry verdict totals plus controls. | Final candidate policy surfaces and aggregate consumer. | Regression must still reject stale-current 207 even when the repository itself is clean. | Not run on candidate. |
| CHK-P1-DESIGN-STRICT | "powershell -ExecutionPolicy Bypass -File scripts\design_decision_check_regression.ps1"; "powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 0b8490cb1dee4f02e7c72a5e097c1fa78361c588"; "powershell -ExecutionPolicy Bypass -File scripts\worker_prompt_preflight_regression.ps1 if the template changed" | All required final production/regression commands exit zero on the unchanged final tree. | Design classifier, template, completion gate, gate wiring. | Missing-base regression rejects while exact-base final branch certification inspects the committed range. | Not run on candidate. |
| CHK-P1-HYGIENE | "git diff --check"; "after committing git diff --check 0b8490cb1dee4f02e7c72a5e097c1fa78361c588..HEAD"; "exact changed-path inventory; clean status." | Working and committed ranges are whitespace-clean; only authorized files changed; post-commit worktree is clean. | Candidate commit and coordinator review. | Compare exact paths to write scope; no transcript/temp/cache staged. | Not run on candidate. |
| COMPLETE-P1-COMMITTED-EVIDENCE | "Stage only authorized files and commit the final unchanged candidate tree." | One final candidate commit contains the completed worklog, production changes, regressions, gate/template consumers, and workflow decision; no later content edit invalidates checks. | Candidate SHA -> coordinator reconstruction. | Post-commit diff check, exact inventory, and clean status. | Open. |

## Explicit Deferrals

Merging main into claude/b1-b2-charged-fringe-tables; REQ-E1-07/09 notes;
claude/e1-cost-algebra; ProgramFits; legacy naming; M1 refresh; Lean semantics;
and public-document migration remain owner/dependency blocked and are not
required for this workflow-policy target.

## Verification Command Ledger

| Command | Role / covered rows | Unique failure mode | Planned tree / timeout basis | Final duration and result |
| --- | --- | --- | --- | --- |
| JSON parse plus exact policy ID/status checks | Development; current-cost, history, term truth | malformed policy or missing/duplicated term | Dirty development tree; 30 s | Pending. |
| Focused production claim fixtures for current 207/current 210/historical costs | Development; current-cost/history | allowance-bypass or role-category miss | Dirty development tree; 60 s per production child through bounded runner | Pending. |
| design_decision_check_regression.ps1 | Development then final; design opt-out, strict base, production regression, subprocess deadline | copied/enumerated detector, base vacuity, path-category miss, child leak | Frozen candidate; closest scripts are sub-minute to a few minutes; outer timeout 10 min, internal positive stage deadlines | Pending. |
| claim_drift_policy_regression.ps1 | Final; claim rows, exact registry, inherited checks, deadline | policy category/allowance/path/final-exit regression | Frozen candidate; base regression is roughly two minutes; outer timeout 10 min, internal positive stage deadlines | Pending. |
| claim_drift_scan.ps1 -Strict | Final; repository current-surface verdict | live strict violation absent from fixtures | Frozen candidate; observed base scan 22 s; timeout 2 min | Pending. |
| design_decision_check.ps1 -Strict -Base exact SHA | Final; committed-range design coverage | zero-range fallback or missing workflow entry | Frozen candidate; timeout 1 min | Pending. |
| worker_prompt_preflight_regression.ps1 | Final because template changes | emitted prompt omits exact strict base | Frozen candidate; timeout 5 min | Pending. |
| git diff --check and hygiene rg | Final hygiene | whitespace or forbidden source/trust token | Frozen candidate; timeout 1 min each | Pending. |
| scripts/gate.ps1 | Conditional only if focused regression cannot prove exact aggregate invocation/exit propagation | aggregate wiring/status overwrite | Unchanged final tree only; recent gate evidence is about 4-5 min, timeout 15 min | Pending trigger decision. |
| Post-commit diff check, exact paths, status | Final committed evidence | uncommitted or unauthorized material | Candidate commit; timeout 1 min | Pending. |

No Lean/Lake build is planned: no Lean/import/public-theorem path is authorized.

## Proof Digestion

Conceptual meaning, plain-English meaning, live assumptions, downstream
consumers, and skeptical-reviewer questions will be completed after the
production verdicts close. The live assumptions already frozen are that Git
returns repository-relative changed paths, the claim scanner remains the sole
production claim verdict, and workflow policy does not establish any
mathematical, payload, cost-model, machine, runtime, or performance claim.

## Production Design And Evidence Update

The claim policy is a controlled line-language classifier, not unrestricted
natural-language understanding. It pairs the retired tokens 76, 142, and 207
with the frozen live-role vocabulary and delegates path, line, allowance,
strictness, and exit status to claim_drift_scan.ps1. Its historical grammar
admits a single marked historical clause, the existing current-210 comparison
line, the existing live-compatibility-352 comparison line, and the exact
supersession arrow 207 -> 210. A second stale-current clause remains visible to
the same production verdict.

The design checker is an opt-out classifier. Decision records, internal
worklogs/acceptance matrices, audit reports, historical digests other than the
current publication digest, and the digestion evidence log are neutral.
Workflow roots are .agents, .codex, .github, scripts, AGENTS.md, and
docs/internal. Lean remains code-sensitive under every root. Every other
non-neutral path defaults to code-sensitive. Strict mode requires a resolvable
base and never falls back; symbolic refs remain compatible with CI, while the
template and completion gate require each governed worker's exact
40-character base commit.

## Authoritative Closure Table

| ID | Production evidence and anti-vacuity result | Status |
| --- | --- | --- |
| REQ-P1-CURRENT-COST-210-ENFORCEMENT | Production fixtures p1-current-cost-207-rejected, p1-canonical-query-cost-207-heldout, p1-uniform-modeled-trace-length-207-heldout, p1-costed-cost-207-heldout, and p1-number-first-current-charged-trace-207 all reject. p1-current-cost-210-control accepts. Repository strict scan reports 1,290 hits and zero failures. | Closed. |
| REQ-P1-HISTORICAL-COST-ALLOWANCE | Marked 207/76/142, historical 328, compatibility 352, and supersession-arrow controls accept. Both unrelated-clause marker/history bypasses and a second 207 after the arrow reject. README and PAPER_MODEL_ADEQUACY existing comparison forms receive allowed verdicts. | Closed. |
| REQ-P1-POLICY-TERM-TRUTH | Stable consumed IDs remain; the new 207 advisory status is historical-retired, the strict status calls 76/142/207 forbidden when presented as current, the false 207 control was replaced by a named reject, and no Lean identity changed. | Closed. |
| REQ-P1-DESIGN-COVERAGE-OPT-OUT | The production isolated-Git regression rejects held-out RMQ Lean, validation Lean, workflow script, public doc, unknown path, missing code decision, and missing workflow decision. Correct code/workflow decisions and every frozen neutral class accept. | Closed. |
| REQ-P1-STRICT-BASE-NONVACUITY | strict-missing-base and strict-unresolvable-base reject; nonstrict-local-worktree-mode detects the held-out Lean path and exits advisory zero; exact-base branch certification checks the complete changed range. | Closed. |
| REQ-P1-PRODUCTION-CLASSIFIER-REGRESSION | design_decision_check_regression.ps1 invokes the real checker in 18 isolated Git cases: 10 reject, 8 accept, drive-qualified Windows root checked, sleeper cleanup checked, and caller state restored. | Closed. |
| REQ-P1-GATE-WIRING | aggregate-gate-wiring proves exactly one design regression call, exactly one inherited claim regression call, and immediate design-regression LASTEXITCODE propagation. | Closed. |
| INV-P1-NO-PUBLIC-SEMANTIC-CHANGE | Exact changed-path inventory is the ten authorized paths only. No Lean, README, FAMILY_SUMMARY, other live claim surface, theorem, registry, roadmap, audit, or E1 file changed. | Closed. |
| INV-P1-E1-NONOVERLAP | Diff and report remain workflow-policy only and make no E1, merge, legacy, M1, or roadmap-closure claim. | Closed. |
| REPLAY-EXACT-REGISTRY | The claim runner pins 94 ordered sentence IDs plus 15 ordered context IDs. duplicate-fixture-id-control, missing-required-fixture-id-control, verdict-count-drift-control, exact-fixture-registry, exact-context-registry, and final pinned totals are production failures if perturbed. | Closed subject to the final unchanged-tree replay recorded in the worker response. |
| REPLAY-SELECTOR-NONVACUITY | No focused selector exists; both regressions execute their complete registries. | Not applicable by frozen contract. |
| REPLAY-SUBPROCESS-DEADLINE | Both runners require positive deadlines for Git/PowerShell stages, return 124 on timeout, terminate and wait for the owned process tree, and pass a cheap five-second sleeper under a 200 ms deadline. The initial synchronous-pipe deadlock was repaired by beginning asynchronous stdout/stderr draining before the wait. | Closed. |
| INV-P1-INHERITED-CLAIM-CHECKS | All inherited 2^128, removed-alias, source/freshness/position, readWord-attribution, absolute-path, path/line allowance, and tracked-state cases remain in the pinned production replay and pass. | Closed subject to final replay attestation. |
| CHK-P1-CLAIM-STRICT | Development production run: full claim regression exit 0 in 292.6 s with 62 reject, 32 accept, 15 context verdicts and clean restoration; strict repository scan exit 0 in 10.7 s with 1,290 hits and zero failures. Final unchanged-tree results are response-attested. | Closed when final reruns below pass. |
| CHK-P1-DESIGN-STRICT | Development production regression exit 0 in 37.8 s with 10 reject/8 accept and gate wiring; exact-base strict checker exit 0 in 3.3 s over 10 changed files; worker-prompt regression exit 0 in 39.9 s. Final unchanged-tree results are response-attested. | Closed when final reruns below pass. |
| CHK-P1-HYGIENE | Working-tree diff check is clean; final hygiene, committed-range diff, exact inventory, and clean status remain in the final sequence. | Closed when final and post-commit checks pass. |
| COMPLETE-P1-COMMITTED-EVIDENCE | The intended commit contains only the authorized production policy, regressions, gate/template consumers, workflow decision, and this worklog. Candidate SHA and clean post-commit evidence are response-attested. | Closed when the final commit and post-commit checks succeed. |

## Observed Command Ledger Before Final Freeze

| Command | Tree state | Timeout | Duration / result |
| --- | --- | --- | --- |
| Project skill preflight against governance 7e0e6089... | Clean exact base 0b8490c... | 120 s | 7.7 s, exit 0; canonical checkout/working/runtime inventories agree. |
| JSON parse, policy-term uniqueness/status checks, PowerShell syntax creation | Dirty development tree | 30 s | Each exit 0; policy version 20, one strict retired-current term, scripts parse. |
| claim_drift_scan.ps1 -Strict | Functionally final policy/tree before evidence update | 120 s | 10.7 s, exit 0; 1,290 hits, zero strict failures. |
| claim_drift_policy_regression.ps1 | Functionally final policy/runner before exact context-ID pin | 600 s | 292.6 s, exit 0; 94 ordered sentence fixtures, 62 reject, 32 accept, 15 context verdicts, clean restoration. |
| design_decision_check_regression.ps1 | Functionally final classifier/gate before evidence update | 300 s | 37.8 s, exit 0; exact gate wiring, 10 reject, 8 accept, sleeper cleanup, clean restoration. |
| design_decision_check.ps1 -Strict -Base 0b8490cb1dee4f02e7c72a5e097c1fa78361c588 | Dirty complete implementation before evidence update | 60 s | 3.3 s, exit 0; 10 changed files, 0 code, 8 workflow, 2 neutral. |
| worker_prompt_preflight_regression.ps1 | Functionally final template | 300 s | 39.9 s, exit 0; all named cases pass. |
| claim regression -AbsoluteWindowsOnly | Development parser/deadline control | 120 s | 16.3 s before async-drain repair and 11.8 s after exact-context instrumentation; both exit 0 with two production path verdicts and clean restoration. |

The aggregate gate is skipped if the final design regression again proves the
exact invocation counts and immediate exit propagation. That focused proof is
the conditional trigger named in the frozen contract; running the broad Lean
gate would duplicate unrelated builds despite no Lean/import/theorem change.

## Proof Digestion Update

Conceptually, omission is no longer an acceptance mechanism. A retired cost is
classified by its semantic role vocabulary, and a new repository path is
design-sensitive unless it belongs to a small documented evidence class.

In plain English: writing "the current bound is 207" in any registered live
surface now breaks the real gate, while honest history still works. Adding a
new proof, validator, public document, workflow script, or unknown repository
format now demands the right durable decision record even if nobody remembered
its filename in advance.

Live assumptions:

- Git diff and ls-files provide repository-relative paths; the checker also
  normalizes rooted paths under the repository.
- Regex-based claim policy remains a controlled tripwire, not a theorem about
  unrestricted prose semantics.
- Symbolic Base refs remain production-compatible for CI; governed worker
  prompts supply exact 40-character commits.
- Workflow evidence changes no mathematical or executable RMQ semantics.

Downstream consumers are scripts/gate.ps1, blocking CI's existing strict claim
and base-relative design steps, the worker prompt template, and the proof
completion gate.

Skeptical reviewer questions and answers:

- Could "historical" in a first clause hide current 207 later? No; both named
  unrelated-clause mutations reject through the production scanner.
- Could a new extension or directory evade the design gate? No; unknown
  non-neutral paths default to code-sensitive.
- Could the decision logs demand themselves recursively? No; they are exact
  neutral records while their presence satisfies the corresponding class.
- Could strict mode silently inspect only a clean worktree? No; missing or
  unresolvable Base exits nonzero before classification.
- Do the regressions test copied logic? No; every semantic case launches the
  production script, and the gate wiring check pins its aggregate consumer.

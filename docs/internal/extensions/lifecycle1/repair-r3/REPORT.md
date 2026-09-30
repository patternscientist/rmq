Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# LIFE-1-R3 report: failure-path integrity in lifecycle harnesses

- Handle/title: LIFE-1-R3, "(LIFE-1-R3) Repair failure-path integrity in lifecycle harnesses".
- Branch: claude/life-1-r3-finally-integrity. Worktree: C:/Users/poin/Documents/RMQ/.claude/worktrees/life1-r3-finally-integrity.
- Base: eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a. Governance: 7b227c49ef2ec044b702126cc41c9add847eed01.
- Final tip: 1f343c9f77ae8aba8d5565d03f94ed407edc4816 (clean tree).
- Contract: LIFE1_R3_FINALLY_INTEGRITY.md, 18,076 B, SHA-256 552fe34fcd732bf7997a6560b17070d7dca945cb92dc8c349eed33c541966c47.
- Matrix: docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md (frozen rows are an exact byte prefix since 695a7e72; evidence E-00..E-04 appended).
- Report file: the runtime refused to write docs/internal/extensions/lifecycle1/repair-r3/REPORT.md with the exact message "Subagents should return findings as text, not write report files. Include this content in your final response instead." This text is the complete report, returned for coordinator persistence.

All local work required by the R3 rows is done. Status is INCOMPLETE only because coordinator verification, a continuation audit of this repair, integration with main and CI certification remain. No gate, CI, audit or acceptance result is claimed.

## Commits

1. 695a7e72eb8c85a21689681fb6981c86dabbf31d - freeze R3 acceptance matrix (first edit) + WDD-01
2. d42919f80b0c886a910ee964b481e49888d6d65f - control registry, runner, doubles, selector controls, heavy wrapper + WDD-02
3. 03742c80bb4e08329c32d2d23b49c57a85b210d7 - base reproduction receipts + WDD-03
4. a2e40779dd2cefd9a8d541084af8efd6551636a4 - repair of the nine harnesses + WDD-04
5. 77324931643af6a20c952b2d8b2b106026694547 - candidate control receipts + WDD-05
6. c6d94ad006fb87434484dbfd4948dbc61b60dc6f - exact-blob materialization script for three LF-pinned frozen inputs + WDD-06
7. 4a2a56d549bba6cfc94e742c73d9e503023367a6 - content proof and restore mode; non-functional (two newline literals collapsed by a heredoc; no CR) + WDD-07
8. 2234de12541f699aa665e20b4a6dc9833c46d930 - fix of that collapse + WDD-08
9. a828d5137908044ffaaaa7abbb7555647998b293 - campaign receipts + WDD-09
10. 1f343c9f77ae8aba8d5565d03f94ed407edc4816 - final checks and row dispositions + WDD-10

## Changed paths (git diff --name-status --no-renames base..tip, 308 entries)

M: the nine harnesses (lifecycle1/repair-r1/{run_controls,finalizer_control,run_check,dependency_child}.ps1, lifecycle1/repair-r2/run_check.ps1, scripts/lifecycle_validator.ps1, lifecycle-native-p0/repair-r1/{integrity_controls,dependency_controls}.ps1, lifecycle-native-p0/repair-r2/harness_stream_controls.ps1) and docs/internal/WORKFLOW_DESIGN_DECISIONS.md (base bytes are an exact prefix of the tip). A: only files under docs/internal/extensions/lifecycle1/repair-r3/ (matrix, FAILURE_CONTROL_REGISTRY.json, failure_controls.ps1, selector_controls.ps1, heavy_run.ps1, materialize_registries.py, doubles/, receipts/). Zero diff on RMQ/, native/, lakefile.toml, lean-toolchain, scripts/owned_process_tree.ps1, gate.ps1, claim_drift_scan.ps1, CLAIM_DRIFT_POLICY.json, both frozen matrices, all CONTRACT_REQUIREMENTS.json, the frozen control registry and its case files, FAMILY_SUMMARY.md, DIGESTION_LOG.md, README.md. DESIGN_DECISIONS.md untouched (never demanded). No changed blob contains a CR; every changed file is i/lf (empty receipts i/none).

## Per-harness defect confirmation and repair (lines at eb8e4f25)

1. run_controls.ps1 (F1): pins L44-50 and setup L38-50 outside the try; only re-hash L98 success-only; finally L101-105 writes entry pins as sourcePins; L103 hash can throw in finally. Base: C/Q/M unrecorded in summary, S no summary. Repaired: setup after evidence root inside one try; catch keeps the record; finally re-hashes every pin in its own guard (all differences, not-captured marked), guards the shell hash, always writes summary.json (entrySourcePins + finalization), rethrows the original error.
2. finalizer_control.ps1: L386-387 success-only; export child L112-117 and all setup before the only try; inner finally L372-384 throws can mask. Base: C already recorded (expected accept), Q/M lose integrity, S no result.json. Repaired: run dir before pins; one try over pins/export/pair loop; guarded inner cleanup into cleanupErrors; finally checks registry, harness, helper, production pins; result.json always.
3/4. repair-r1 and repair-r2 run_check.ps1: entry source (and r2 invocation) pins never compared; result.json only on the child success path. Base: C exits 0 with a changed source; Q/M no integrity; S and K1-X no result.json. Repaired: finally compares present/absent sources, invocation files and HEAD; result.json always (entrySources, entryInvocation, finalization with childFailure); exit = child exit when intact, 2 timeout/overflow, 3 integrity/cleanup, 1 harness exception.
5. dependency_child.ps1: L108 success-only; L8 pin and L10-46 setup outside try. Repaired: production script and registry pinned inside try; separately guarded Console.Error/env restoration; receipt.json always.
6. lifecycle_validator.ps1: mutex released before identity check; identity throw masks stage error; first mismatch only; entry identity before try; no failure durable result. Repaired: log root first, per-path identity capture, compare before release, RESULT.json always; PASS.json and all diagnostics unchanged.
7. integrity_controls.ps1: candidate compare L187-188 outside finally; per-case finally throws L177/179/183 mask; git restore exit codes L170-171 unchecked; live sources read/copied never pinned. Repaired: tree snapshot + 7 live pins at entry; restoration steps guarded and exit-checked; finally compares pins and tree; RESULTS.json always; stream contract and both derivation anchors unchanged.
8. dependency_controls.ps1: L78 success-only; no outer finalization; inner finallys unguarded. Repaired: finally re-checks every captured installed-tool pin (including partial), historical inputs and owned fixture; RESULTS.json always.
9. harness_stream_controls.ps1: copied live sources never pinned; carrier check L121-125 success-only; finally only mutex. Repaired: 9 live pins at entry; every created carrier/fixture status-checked in finally; RESULTS.json always.
No listed file already satisfied the property; no other harness was changed or found violating.

## Controls (REQ-L1R3-CONTROLS)

Registry: 47 ordered controls (P/C/Q/S/M x 9 harnesses, K1-X owned-process exception, HS-R dirty carrier), normalized SHA-256 500dd96074bb0c5049f2f76627e9ff1d31f1085c8fab11ff8c795e72e22936ad pinned in the runner. Each control runs the whole harness file from an exact Git ref in a git-initialized disposable copy under .lake with one injected double fixed before entry pins, via scripts/owned_process_tree.ps1, then restores and verifies the exact manifest and a clean copy Git state; the runner also re-checks its own inputs and the real worktree Git state.

- base-pwsh (eb8e4f25, pwsh 7.6.5): 47/47 predictions matched, 806.2 s, global wait 0.013 s, deadline 5,400 s.
- base-winps (Windows PowerShell 5.1.26100.9444): 47/47 matched, 667.1 s.
- candidate-pwsh (a2e40779): 47/47 pass (core + structural finalization predicates), 807.1 s.
- candidate-winps attempt 1: INCOMPLETE, wrapper timeout at 18,675 s after a five-hour inactivity gap consistent with host suspension; receipt kept, not counted.
- candidate-winps: 47/47 pass, 340.2 s.
- selector/registry controls (omitted, valid, empty string, empty array, whitespace, malformed, unknown, duplicate; exact copy, omitted/duplicate/unknown middle ID, reorder, byte drift, empty registry): 15/15 at base and at candidate (42.3 s, 35.8 s).
Base failed clauses per harness/shape are tabulated in matrix E-01; the only already-satisfied base shape is FC-C.

## Campaigns (REQ-L1R3-CAMPAIGNS), via repaired repair-r2 run_check.ps1, global mutex wait <= 0.005 s

- Frozen 67-case registry, pwsh: 67/67 in frozen order, 333.5 s (historical ~351 s), exit 0, 12/12 summary pins verified.
- Frozen registry, winps: 66/66, 227.7 s, exit 0.
- Validator startup/single/full, pwsh: PASS 2/3/9 processes, 6.3/8.6/53.2 s; winps: 4.2/5.7/48.2 s; 12/12 identity pins verified each.
- p0 integrity (run_owned): 15/15, stream contract validated, 285.9 s; dependencies: 19/19, 22.3 s; harness-stream: 11/11, 118.4 s.
Every run_check finalization pass with 17/17 pins verified. The three frozen JSON inputs were materialized as exact Git blob bytes before and restored after (content proof: empty git diff, hash-object equals index blob). Uncovered, not passed: no winps campaign of the p0 harnesses.

## Checks (CHK-L1R3-VERIFICATION)

- project_skill_preflight.ps1: PASS, 3.0 s.
- lake build rmq_lifecycle_validate under both mutexes: exit 0, 13.6 s (deadline 14,400 s), exe 901f0dee... unchanged.
- design_decision_check.ps1 -Strict -Base parent -Head commit: exit 0 for all ten commits; range eb8e4f25..1f343c9f: exit 0 (308 files).
- claim_drift_scan.ps1 -Strict on final tip 1f343c9f: exit 0, 1,314 s, 3,668 hits, 0 strict failures; -SelfTest: exit 0, 2,476 s, PASS (also both passed at a828d513).
- git diff --check and git diff --check eb8e4f25..HEAD: exit 0.
- Both trust hygiene rg scans over RMQ and lakefile.toml: no matches.

## Limits

- Controls are harness control-flow tests with real owned processes, not semantic or native campaigns.
- M injects the exception into the integrity step; cleanup-throw paths are guarded in source but not injected by a control.
- Timeout/overflow/malformed child results share the ordinary-failure catch path; only ordinary failures and K1-X are exercised by the new controls (the frozen T01 timeout case still passes).
- Pre-evidence argument/selector/registry validation still writes no durable result (nothing launched or pinned).
- A process killed from outside cannot run its finally (candidate-winps attempt 1).
- The nine files' raw bytes now differ from historical per-branch inventories (lifecycle1 SOURCE_FREEZE/EVIDENCE_INDEX, lifecycle-native1 BASE_IDENTITY); those records and their branch-bound scope checkers are unchanged and not rerun.
- Replaying the frozen campaign in a default CRLF checkout requires materialize_registries.py first.

## Proof digestion

Conceptually: every lifecycle harness now answers three separate questions on every exit path - did the stage fail, did a protected input change, did cleanup succeed - and writes all three into its own durable result. In plain English: a failed run still re-checks every protected file and reports each difference next to the original failure, and summaries distinguish entry hashes from re-verified ones. Live assumptions: the unchanged owned-process helper, no host suspension mid-run, observed PowerShell 5.1/7.6.5 behaviour, SHA-256 file identity. A skeptical graduate student would ask whether a cleanup throw is ever injected (no, source-guarded only), whether a failing frozen case is exercised under the repaired orchestrator (only via controls), and whether anything consumes the renamed keys sourcePins/sources/invocation (only historical verifiers over historical receipts).

## Requests

Coordinator verification of the delta and a continuation audit on exact tip 1f343c9f77ae8aba8d5565d03f94ed407edc4816; then integration with main (expect the c9e26d27 lakefile conflict) and CI.

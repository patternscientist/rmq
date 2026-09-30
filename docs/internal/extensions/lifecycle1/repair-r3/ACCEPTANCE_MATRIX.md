# LIFE-1-R3 acceptance matrix: failure-path integrity in lifecycle harnesses

This matrix was created before any other edit in this branch. The requirement
rows above the append-only marker are frozen: they change only by an explicit
coordinator contract amendment. Evidence, dispositions and the command ledger are
appended below the marker. A row does not close by a script name, a green run or
this file; it closes only when the recorded evidence entails the exact requirement.

- Worker: LIFE-1-R3 (fresh governed repair task).
- Worktree: C:/Users/poin/Documents/RMQ/.claude/worktrees/life1-r3-finally-integrity.
- Branch: claude/life-1-r3-finally-integrity.
- Exact base: eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a (formal base bf31f983205175481fcb659caa4dfb70ef43e361).
- Workflow governance: 7b227c49ef2ec044b702126cc41c9add847eed01.
- Template: docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md.
- Source prompt: LIFE1_R3_FINALLY_INTEGRITY.md, 18,076 bytes, SHA-256
  552fe34fcd732bf7997a6560b17070d7dca945cb92dc8c349eed33c541966c47. The nine
  REPLAY/REQ/CHK requirement texts below are copied byte-for-byte from its lines
  41-49 (the text after `- <ID>: `), mechanically from those bytes.

## Inherited frozen rows (referenced, not restated)

Each inherited row is the complete table line at the exact base commit. Neither
frozen matrix may change on this branch.

| ID | Frozen source at base | Line | Row bytes | Row SHA-256 |
| --- | --- | --- | --- | --- |
| `L1-18` | `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` | 50 | 1130 | `996078e382eb9a9307aaa6974e7b0a509ceadd268c41376cb889a4a40ce884bb` |
| `INV-MUTATION-REPRODUCIBILITY` | `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` | 71 | 1236 | `6b792b08e24ea789e7c8963ebb745c3b5e29b18f83c9a38ba532641edf0169e6` |
| `CHK-SCOPE` | `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` | 75 | 744 | `4bb83f4848c4364913e217d12fd27b2b7150660506ce8e9c34f71fee634e228f` |
| `CHK-FINAL` | `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` | 74 | 741 | `294c21279c6a7580c227468fb242b38553d0406dc212c9bec5b121ec6718d900` |
| `INV-MUTATION-REPRODUCIBILITY` | `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` | 51 | 1663 | `9934894dea6aeb836f39cbbccae99d4373b184229bae3b9da9fe94f1954a1fb6` |
| `REPLAY-EXACT-REGISTRY` | `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` | 58 | 1121 | `c760381b6b2b2f2adb3faf054eb1c6f17989ed18d5b2804b231b279a9b5146f2` |
| `REPLAY-SELECTOR-NONVACUITY` | `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` | 59 | 1331 | `365553b6262146b76d83c73fd58d5677c8cef65462a4f8c2507186c2b9d33d05` |
| `REPLAY-SUBPROCESS-DEADLINE` | `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` | 60 | 3218 | `ad94e5de33cbf27878af500a0eb6ec517bd01a4184ddb9219368287adbc753f3` |

Frozen file identities at base: formal matrix 43,437 bytes, SHA-256
8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7; native matrix
80,759 bytes, SHA-256 05b3435261d9b531837e5879b8c6390eb7b298ce4b61dc34e425ac48f5607ea3.

## Requirement-to-evidence matrix

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `L1-18` | Inherited verbatim frozen row: `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` line 50 at `eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a` (row bytes and SHA-256 in the inherited-row table above; not restated here). | Inherited formal row; R3 closes only its failure-path integrity sub-clause | The frozen 67-case control registry replays through the repaired orchestrator with every case at its frozen verdict, and the orchestrator failure-path integrity clause is exercised by committed P/C/Q/S/M controls. | CONTROL_REGISTRY.frozen.json -> repaired run_controls.ps1 -> handler children -> summary.json finalization; launched by repaired repair-r2 run_check.ps1 -> result.json finalization. | Base F1 probe shape (changed pin plus failed child) must be rejected with both errors recorded; the unchanged base must be shown to omit the integrity record. | See append-only evidence below. | Open |
| `INV-MUTATION-REPRODUCIBILITY` | Inherited verbatim frozen row: `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` line 71 at `eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a` (row bytes and SHA-256 in the inherited-row table above; not restated here). Also native frozen row `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` line 51. | Inherited invariant | A committed versioned runner and registry replay every failure-path control with exact expected verdict surfaces, expected-accept P controls, restoration verification and a clean real tree. | FAILURE_CONTROL_REGISTRY.json -> failure_controls.ps1 -> disposable copy -> whole harness file -> durable result -> predicate verdict -> restoration manifest. | Run every control against the unchanged base harness bytes and record which shapes the base fails; a control that the base also passes is not discriminating for that clause. | See append-only evidence below. | Open |
| `CHK-SCOPE` | Inherited verbatim frozen row: `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` line 75 at `eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a` (row bytes and SHA-256 in the inherited-row table above; not restated here). | Inherited formal row | Exact base/branch/worktree, changed paths only inside the R3 write scope, frozen rows byte-identical, clean committed tree. | git diff --name-status --no-renames base..HEAD against the R3 write scope; frozen matrix blobs unchanged. | Any path outside the nine harnesses, repair-r3/** and append-only ledgers fails the scope check. | See append-only evidence below. | Open |
| `CHK-FINAL` | Inherited verbatim frozen row: `docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md` line 74 at `eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a` (row bytes and SHA-256 in the inherited-row table above; not restated here). | Inherited formal row | Final-required R3 checks run on the final content with exact identities and outcomes. | CHK-L1R3-VERIFICATION command ledger on the final tip. | A check run on an earlier tree or a timed-out/partial run is not recorded as passed. | See append-only evidence below. | Open |
| `REPLAY-EXACT-REGISTRY` | any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure. (Native frozen source: `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` line 58.) | Prompt restatement; also governs every new R3 runner | The R3 runner declares an exact ordered versioned registry, rejects missing/duplicate/unknown/reordered IDs and pinned-byte drift, and reports executed/expected counts; a lost control fails the run. | FAILURE_CONTROL_REGISTRY.json -> failure_controls.ps1 registry validation -> RESULT.json executed/expected. | Registry copies with an omitted middle ID and a duplicated middle ID are rejected by committed selector/registry controls. | See append-only evidence below. | Open |
| `REPLAY-SELECTOR-NONVACUITY` | omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing. (Native frozen source: `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` line 59.) | Prompt restatement; also governs every new R3 runner | Omitted selects the full registry; valid selects exactly one; empty, whitespace, malformed, unknown and duplicate selectors reject before any control executes. | selector_controls.ps1 -> owned launch of failure_controls.ps1 -> exact exit and diagnostic. | A focused run with an empty or whitespace selector must not select nothing and succeed. | See append-only evidence below. | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed. (Native frozen source: `docs/internal/extensions/lifecycle-native1/ACCEPTANCE_MATRIX.frozen.md` line 60.) | Prompt restatement; governs the nine repaired harnesses and every new R3 runner | Every control and campaign launch uses scripts/owned_process_tree.ps1 with a positive evidence-based deadline; exits and stderr retained; disposable bytes restored and verified in finally; host-infeasible conditions recorded as uncovered. | failure_controls.ps1 / campaign wrapper -> Invoke-RMQOwnedBoundedProcess -> retained process record. | A control that times out or whose restoration manifest differs is recorded as failed, not passed. | See append-only evidence below. | Open |
| `REQ-L1R3-PROPERTY` | For each harness in REQ-L1R3-HARNESSES that snapshots protected paths, stages or mutates files, or launches owned stages, on EVERY exit path (success; ordinary child failure; timeout; output overflow; unowned or malformed result; setup exception, including a missing pinned file at snapshot time; and an exception thrown by cleanup or by the integrity step itself): (a) owned cleanup and restoration run; (b) every entry pin, and every entry tree snapshot the harness takes, is independently compared with the live state in finalization, continuing past the first mismatch or exception and recording all differences; (c) the original stage error, every integrity difference and every cleanup error are recorded separately in the durable result and none masks another; (d) the durable result (summary/result/RESULTS json) is always written, or its own write failure is reported without replacing the first error; (e) the overall verdict is failure whenever any of these is non-empty. A summary may not present entry pins as if they were verified pins. | Local owned rung | For each repaired harness: a finalization block that runs on every exit path, re-checks every entry pin (and tree snapshot) independently, records stage/integrity/cleanup errors in separate fields of an always-written durable result, and fails the verdict when any is non-empty. | Repaired harness source (catch keeps stage error; finally re-checks each pin in its own try; durable write in its own try) -> durable result finalization block -> nonzero exit. | P/C/Q/S/M controls per harness, each run against base and repaired bytes; entry pins must not be presented as verified pins. | See append-only evidence below. | Open |
| `REQ-L1R3-HARNESSES` | repair exactly these files (line numbers at eb8e4f25; see the review input): docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1 (F1: L44-50 pins and L38-50 setup outside the try, sole re-hash L98 on the success path, finally L101-105 writes entry pins, L103 can mask); docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1 (L386-387 success-only, export child L112-117 before any try, inner finally throws mask); docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1 and docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1 (entry source pins never compared; result.json absent when the owned-process call throws; the r2 invocation pins included); docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1 (L108 success-only); scripts/lifecycle_validator.ps1 (finally releases the mutex before the identity check, identity throw masks the stage error, first mismatch only); docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1 (real-candidate compare L187-188 after the loop with no finalization; per-case finally throws mask; git restore exit codes unchecked); docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1 (installed-pin re-check L78 success-only; no outer finalization; RESULTS.json not written on failure); docs/internal/extensions/lifecycle-native-p0/repair-r2/harness_stream_controls.ps1 (copied live sources never pinned; carrier restoration check success-only). Independently confirm each defect from source before repairing it; if you find a listed file already satisfies REQ-L1R3-PROPERTY, record the evidence and leave it unchanged. If you find another harness in this lane that violates the property, stop and report it rather than widening scope silently. | Local owned rung | Each listed defect confirmed from base source (and by a base control where feasible) and repaired, or recorded as already compliant; any further same-lane violation reported instead of silently widening scope. | Base source line evidence -> base control outcome -> repaired source -> repaired control outcome. | A listed defect that the base control does not reproduce is recorded explicitly with the reason. | See append-only evidence below. | Open |
| `REQ-L1R3-CONTROLS` | Commit a versioned failure-path control registry and runner under docs/internal/extensions/lifecycle1/repair-r3/. For each repaired harness it contains, at minimum: P (intact, succeeds, no integrity difference); C (a pinned file changed, stage succeeds: rejected with the integrity difference); Q (the same change plus an ordinary stage failure: rejected with BOTH the stage error and the integrity difference recorded); S (setup failure, for example a missing pinned file at snapshot time: rejected with a durable result written); and M (an exception injected into cleanup or into the integrity step: the original stage error is still recorded). Each control runs the whole repaired harness file (not a copied detector) in a disposable copy under your worktree's .lake, with only the minimal injected stage or test double needed to create the condition, fixed before entry pins are taken, and restores and verifies exact bytes afterward. Controls run through scripts/owned_process_tree.ps1 with positive evidence-based deadlines. Include the registry controls required by the REPLAY rows (omitted, valid, empty, whitespace, unknown and duplicate selectors; omitted middle ID; duplicate middle ID). Before repairing, run the P/C/Q/S/M shapes against the UNCHANGED base harness where feasible and record which fail, so each control is shown to discriminate. | Local owned rung | Committed registry plus runner under repair-r3 with P/C/Q/S/M for every repaired harness and the selector/registry controls; all repaired outcomes as expected on pwsh 7 and Windows PowerShell 5.1 where supported; base outcomes recorded. | FAILURE_CONTROL_REGISTRY.json -> failure_controls.ps1 (-HarnessRef base or candidate) -> committed RESULT receipts. | Base run must fail at least one clause per defective harness; repaired run must pass all; selector negatives must reject before execution. | See append-only evidence below. | Open |
| `REQ-L1R3-CAMPAIGNS` | With the repaired harnesses, re-run and commit receipts for: the complete frozen 67-case control registry through run_controls.ps1 on both declared profiles (pwsh: 67 cases; winps: 66 cases; a historical pwsh run took about 351 s in total), invoked through the repaired repair-r2 run_check.ps1; the production lifecycle validator's standard modes as previously run in this lane; and the normal full run of each repaired lifecycle-native-p0 harness. The frozen registry and case files stay byte-identical; every case keeps its frozen expected verdict. Report executed/expected counts, durations, exits and receipt hashes. If a campaign cannot run on this host, record it as uncovered, never as passed. | Local owned rung | 67/66 frozen controls pass at their frozen verdicts through repaired run_controls via repaired repair-r2 run_check; validator standard modes pass; each repaired lifecycle-native-p0 harness normal full run passes; receipts committed with counts, durations, exits and hashes. | repair-r2 run_check.ps1 spec -> run_controls.ps1 -> summary.json; lifecycle_validator.ps1 -> RESULT.json/PASS.json; run_owned.ps1 integrity/dependencies and harness_stream_controls.ps1 -> RESULTS.json. | A partial, timed-out or setup-failed campaign is recorded as failed or uncovered, never passed; the frozen registry bytes must be unchanged in Git. | See append-only evidence below. | Open |
| `REQ-L1R3-PRESERVATION` | git diff --name-status --no-renames eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a..HEAD lists only paths inside the write scope. Zero diff under RMQ/, native/, lakefile.toml, lean-toolchain, scripts/owned_process_tree.ps1, scripts/gate.ps1, scripts/claim_drift_scan.ps1, docs/internal/CLAIM_DRIFT_POLICY.json, both frozen matrices, CONTRACT_REQUIREMENTS.json files, the frozen control registry and its case files, docs/FAMILY_SUMMARY.md, docs/DIGESTION_LOG.md and README.md. Ledgers are append-only. Every changed file is stored with LF endings and contains no lone carriage return (check with git ls-files --eol and a byte scan); a lone CR makes git classify a file as binary and skip normalization, which recently broke CI on main. | Local owned rung | Scope diff lists only write-scope paths; the protected paths have zero diff; ledgers append-only (base bytes are a byte prefix); every changed file LF in Git with no lone CR. | git diff --name-status --no-renames base..HEAD; git ls-files --eol; byte scan; ledger prefix comparison. | A single out-of-scope path, a CRLF-stored file, a lone CR or a non-prefix ledger edit fails the row. | See append-only evidence below. | Open |
| `CHK-L1R3-VERIFICATION` | Run and record (command, host, duration, deadline, mutex waits, exit): the base reproductions; all REQ-L1R3-CONTROLS on pwsh 7 and Windows PowerShell 5.1 where the harness supports both; the REQ-L1R3-CAMPAIGNS runs; scripts/claim_drift_scan.ps1 -Strict and scripts/claim_drift_scan.ps1 -SelfTest on the final tree (never commit scanner result lines or its summary line; state counts in prose); git diff --check; git diff --check eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a..HEAD; scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit> for every new commit and once for the range from the base; both trust hygiene scans. | Verification | Every listed command recorded with command, host, duration, deadline, mutex waits and exit on the final content. | Append-only command ledger below. | A check that did not complete, or ran on a different tree, is not recorded as passed. | See append-only evidence below. | Open |

Explicitly deferred by the prompt (non-blocking for this rung, coordinator-owned):
integration with main, the continuation audit, CI certification, acceptance and
scripts/gate.ps1.

<!-- LIFE-1-R3 APPEND-ONLY EVIDENCE BELOW THIS LINE -->

### E-00 Startup, preflight and build (2026-09-29)

- Worktree HEAD at start: eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a, branch
  claude/life-1-r3-finally-integrity, `git status --porcelain` empty.
- `scripts/project_skill_preflight.ps1 -GovernanceRef 7b227c49... -RequiredSkills
  rmq-proof-sprint -RuntimeProjectSkills rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`:
  PASS (required_mode=role-skills), 3.0 s. `git diff 7b227c49..HEAD -- .agents/skills`
  is empty.
- Validator executable: `.lake/build` was seeded by a read-only copy of the
  immutable exact-source tree `lifecycle-implementation-20260920/native1-topology-repair-20260928/source`
  (HEAD eb8e4f25, clean); then `lake build rmq_lifecycle_validate` ran under both
  mutexes via `heavy_run.ps1` (global wait 0.013 s, lane wait 0.0 s, deadline
  14,400 s): exit 0 in 13.6 s, "Build completed successfully", no rebuild of the
  executable. `.lake/build/bin/rmq_lifecycle_validate.exe` SHA-256
  901f0dee451560d620a7ba71ba32069e89169b4fa1e2c164c26b308e4ce69517 (identical to the
  source tree's).

### E-01 Base reproductions on the unchanged harness bytes (REQ-L1R3-CONTROLS, REQ-L1R3-HARNESSES)

Runner commit d42919f80b0c886a910ee964b481e49888d6d65f (no harness repaired).
`failure_controls.ps1 -HarnessRef base` exports every harness from the Git blob of
eb8e4f25. Each receipt is under `receipts/<name>/` (RESULT.json, the heavy-wrapper
RESULT.json and every control's durable result under `durable/`).

| Run | Shell | Heavy wrapper | Executed/expected | Predictions matched | Duration |
| --- | --- | --- | --- | --- | --- |
| base-pwsh | pwsh 7.6.5 | global mutex wait 0.013 s, deadline 5,400 s, exit 0 | 47/47 | 47/47 | 806.2 s |
| base-winps | Windows PowerShell 5.1.26100.9444 | global mutex wait 0.009 s, deadline 5,400 s, exit 0 | 47/47 | 47/47 | 667.1 s |
| selector-base | pwsh 7.6.5 | global mutex wait 0.012 s, deadline 1,800 s, exit 0 | 15/15 | 15/15 | 42.3 s |

Base core clauses that FAILED (identical on both shells; the runner accepts a base
rejection only when the same harness's P control passed in that run, and all nine
P controls passed):

| Harness | C | Q | S | M | extra |
| --- | --- | --- | --- | --- | --- |
| RC run_controls (F1) | integrity not in summary | stage and integrity not in summary | no summary | stage and integrity not in summary | |
| FC finalizer_control | none: base records it (expected accept) | integrity not recorded | no result.json | integrity not recorded | |
| K1 repair-r1 run_check | exit 0, no integrity | no integrity | no result.json | no integrity | X: no result.json |
| K2 repair-r2 run_check | exit 0, no integrity | no integrity | no result.json | no integrity | |
| DC dependency_child | integrity not in receipt | no receipt | no receipt | no receipt | |
| LV lifecycle_validator | no durable result | no durable result | no durable result | no durable result | |
| IC integrity_controls | no RESULTS.json | no RESULTS.json | no RESULTS.json | no RESULTS.json | |
| DP dependency_controls | exit 0, no integrity | no RESULTS.json | no RESULTS.json | no RESULTS.json | |
| HS harness_stream_controls | exit 0, no integrity | no RESULTS.json | exit 0 (missing live source never pinned) | no RESULTS.json | R: no RESULTS.json, carrier unchecked |

Discrimination: every defective shape predicted from source was reproduced, and
the only shape the base already satisfied (FC-C: the success-path protected-hash
check records a changed pin) was predicted as an expected accept. Every copy was
restored to its exact prepared manifest with a clean copy Git state, and the real
worktree Git state was unchanged across each run.

Selector/registry controls (REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY):
omitted selector probes all 47 IDs; `K1-P` probes exactly one; bound `''`,
`@()`, `' '`, malformed `k1-p`, unknown `ZZ-P` and duplicate `K1-P,K1-P` each
exit 1 with their exact diagnostic before any evidence directory exists; an
exact registry copy is accepted; registry copies with the middle ID `DC-P`
omitted, duplicated, an unknown middle ID `ZZ-Z` inserted, two middle IDs
reordered, one byte of drift and an empty control list are each rejected with
their exact diagnostic.

### E-02 Candidate control runs on the repaired harnesses (REQ-L1R3-CONTROLS, REQ-L1R3-PROPERTY)

Harness commit a2e40779dd2cefd9a8d541084af8efd6551636a4; runner and registry
unchanged since d42919f8. `-HarnessRef a2e40779...` exports the nine repaired
harnesses from that commit's Git blobs. A candidate control passes only when every
core predicate (completed owned launch, exit class, durable result present, the
registry's exact stage and integrity text groups present) AND every structural
predicate holds: `finalization.schema = life1-r3-finalization-v1`; verdict `pass`
for P and `fail` otherwise; the stage text found in `finalization.stageError`
(or `childFailure` for run_check) and absent when not expected; every integrity
text group found in `finalization.integrityErrors` and the list empty when not
expected; `cleanupErrors` empty; for P every `pinChecks` entry `verified` (or
`absent-verified`), otherwise a non-empty `pinChecks`. The copy must then restore
to its exact prepared manifest with a clean copy Git state.

| Run | Shell | Heavy wrapper | Executed/expected | Passed | Duration |
| --- | --- | --- | --- | --- | --- |
| candidate-pwsh | pwsh 7.6.5 | global wait 0.013 s, deadline 5,400 s, exit 0 | 47/47 | 47 | 807.1 s |
| candidate-winps-attempt1 | Windows PowerShell 5.1 | global wait 0.011 s, deadline 5,400 s | INCOMPLETE: timed out | not counted | 18,675.0 s |
| candidate-winps (attempt 2) | Windows PowerShell 5.1.26100.9444 | global wait 0.003 s, deadline 5,400 s, exit 0 | 47/47 | 47 | 340.2 s |
| selector-candidate | pwsh 7.6.5 | global wait 0.052 s, deadline 1,800 s, exit 0 | 15/15 | 15 | 35.8 s |

The first Windows PowerShell attempt is recorded as incomplete, not failed or
passed: its DP-S control directory was created at 17:41:35 local and its process
directory at 22:43:20 local, a five-hour gap with no activity, after which the
wrapper's stopwatch exceeded the 5,400 s deadline and the owned tree (ids 23144,
22072) was terminated. This is consistent with host suspension; the killed runner
could not write its own RESULT.json. Its wrapper receipt is committed under
`receipts/candidate-winps-attempt1-incomplete/`. The retry is a new run with a
fresh output root after confirming no owned process survived; the harness bytes,
runner and registry were unchanged.

The same 47 controls that the base failed for the predicted reasons now pass
with separate stage/integrity records on both shells; the 9 P controls pass on
both shells with every entry pin verified in finalization.

### E-03 Campaigns re-run with the repaired harnesses (REQ-L1R3-CAMPAIGNS)

Tree: HEAD 2234de12541f699aa665e20b4a6dc9833c46d930 (harness bytes identical to
a2e40779). Before the frozen campaign, `materialize_registries.py` wrote the exact
Git blob bytes of CONTROL_REGISTRY.json, CONTROL_REGISTRY.frozen.json (SHA-256
385c9bc9...) and finalizer_cases.json (1303ecf9...) into the checkout, proving an
empty `git diff --exit-code` and `git hash-object` equal to each index blob;
`--restore` re-checked-out the three paths afterwards with a clean status for them
(`receipts/materialization/`). Every campaign ran through the REPAIRED
`repair-r2/run_check.ps1` (spec `mutex=false`; each harness takes the lane mutex
itself) under `heavy_run.ps1` holding the global mutex. Complete receipts:
`receipts/campaign-<name>/`; machine summary: `receipts/CAMPAIGN_SUMMARY.json`.

| Campaign | Shell | Child deadline | Child exit | Seconds | Global wait | Result |
| --- | --- | --- | --- | --- | --- | --- |
| r3-controls-pwsh (frozen 67-case registry via run_controls.ps1) | pwsh 7.6.5 | 2,700 s | 0 | 333.5 | 0.004 s | 67/67 selected, executed and passed in frozen order; summary finalization pass, 12/12 entry pins verified |
| r3-controls-winps (frozen registry, winps profile) | Windows PowerShell 5.1 | 2,700 s | 0 | 227.7 | 0.004 s | 66/66 selected, executed and passed in frozen order; 12/12 pins verified |
| r3-validator-startup-pwsh | pwsh 7.6.5 | 600 s | 0 | 6.3 | 0.004 s | PASS, 2 processes; RESULT.json pass, 12/12 identity pins verified |
| r3-validator-single-pwsh (L01-W-EMPTY) | pwsh 7.6.5 | 600 s | 0 | 8.6 | 0.003 s | PASS, 3 processes; 12/12 verified |
| r3-validator-full-pwsh (-DeadlineSeconds 1800) | pwsh 7.6.5 | 2,400 s | 0 | 53.2 | 0.005 s | PASS, 9 processes (registry, startup, focused, 5 rejections, full 16); 12/12 verified |
| r3-validator-startup-winps | Windows PowerShell 5.1 | 600 s | 0 | 4.2 | 0.004 s | PASS, 2 processes; 12/12 verified |
| r3-validator-single-winps | Windows PowerShell 5.1 | 600 s | 0 | 5.7 | 0.003 s | PASS, 3 processes; 12/12 verified |
| r3-validator-full-winps | Windows PowerShell 5.1 | 2,400 s | 0 | 48.2 | 0.003 s | PASS, 9 processes; 12/12 verified |
| r3-p0-integrity (run_owned.ps1 -Kind integrity) | pwsh 7.6.5 | 3,000 s (inner 2,400 s) | 0 | 285.9 | 0.003 s | 15/15 controls, wrapper stream contract validated, RESULTS finalization pass, 7/7 live pins verified, candidate tree unchanged |
| r3-p0-dependencies (run_owned.ps1 -Kind dependencies) | pwsh 7.6.5 | 1,500 s (inner 1,200 s) | 0 | 22.3 | 0.003 s | 19/19 controls, stream contract validated, 13/13 pins (11 installed tools, 2 historical inputs) verified, fixture restored |
| r3-p0-harness-stream (harness_stream_controls.ps1, all 11) | pwsh 7.6.5 | 3,000 s | 0 | 118.4 | 0.004 s | 11/11 controls, RESULTS finalization pass, 9/9 live pins verified, 4 created carriers/fixtures status-checked |

Every run_check result.json reports finalization `pass` with 17/17 entry pins
verified (11 source paths plus driver, spec, executable, host, argument file and
checkout HEAD) and no stderr lines. The frozen registry and case files were not
changed in Git and every frozen case kept its frozen expected verdict (the
orchestrator compares each case's exact terminal record). The lifecycle-native-p0
harnesses were run on pwsh only, which is how their normal full runs are defined
(run_owned.ps1 uses the current shell); their Windows PowerShell 5.1 behaviour is
covered by the failure-path controls (candidate-winps 47/47), not by a winps
campaign, which is recorded as not run rather than passed.

### E-04 Final checks at a828d513 and row dispositions

- `scripts/claim_drift_scan.ps1 -Strict` at a828d513: exit 0 after 1,316 s; 3,668
  hits, 0 strict failures (scanner lines not committed).
- `scripts/claim_drift_scan.ps1 -SelfTest` at a828d513: exit 0 after 2,828 s,
  RESULT: PASS.
- `scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit>`: exit
  0 for each of 695a7e72, d42919f8, 03742c80, a2e40779, 77324931, c6d94ad0,
  4a2a56d5, 2234de12, a828d513; `-Base eb8e4f25 -Head a828d513`: exit 0 (308
  files).
- `git diff --check` and `git diff --check eb8e4f25..HEAD`: exit 0.
- Both trust hygiene scans over RMQ and lakefile.toml: no matches (rg exit 1).
- Scope: `git diff --name-status --no-renames eb8e4f25..HEAD` lists the nine
  harnesses, WORKFLOW_DESIGN_DECISIONS.md and additions under repair-r3 only;
  zero diff on every protected path; WDD base bytes are an exact prefix of the
  tip; no changed blob contains a carriage return; the frozen rows of this matrix
  are an exact byte prefix since 695a7e72.
- The worker runtime refused to write the required durable report file
  `repair-r3/REPORT.md` ("Subagents should return findings as text, not write
  report files."); per the Claude-runtime adaptation the complete report is
  returned verbatim to the coordinator with its byte length and SHA-256 for
  persistence. Final-tip rechecks after this commit are reported there.

Row dispositions (worker view; coordinator acceptance required):

| ID | Disposition |
| --- | --- |
| `REQ-L1R3-PROPERTY` | Evidence complete for the local rung: E-01 (base violates), E-02 (repaired passes all core and structural predicates on both shells), E-03. Limit: cleanup-throw injection is source-guarded only; M injects into the integrity step, which the contract allows. |
| `REQ-L1R3-HARNESSES` | All nine defects confirmed from source and by base controls; all nine repaired; no further same-lane violation touched. |
| `REQ-L1R3-CONTROLS` | Committed registry, runner, doubles and selector/registry controls; base 47/47 predictions matched and candidate 47/47 passed on both shells; selector/registry 15/15. |
| `REQ-L1R3-CAMPAIGNS` | 67/67 and 66/66 frozen cases via repaired run_check; validator standard modes on both shells; p0 integrity 15/15, dependencies 19/19, harness-stream 11/11 (pwsh; winps campaign not run and not claimed). |
| `REQ-L1R3-PRESERVATION` | Holds at a828d513 (see scope bullet); rechecked on the final tip in the handoff. |
| `CHK-L1R3-VERIFICATION` | Recorded above and in E-00 to E-03; final-tip repeats in the handoff. |
| `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, `REPLAY-SUBPROCESS-DEADLINE` | Satisfied by the R3 runners (E-01, E-02) and restored for the nine harnesses' failure paths. |
| `L1-18`, `INV-MUTATION-REPRODUCIBILITY` | The failure-path sub-clause the audit found open is now evidenced by committed replayable controls; overall row closure remains a coordinator and continuation-audit decision. |
| `CHK-SCOPE`, `CHK-FINAL` | Local checks pass; integration, CI and acceptance are deferred to the coordinator. |

Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# LIFE-1-R4 report: run_check verdict gap and residual failure-path findings

- Handle/title: LIFE-1-R4, "(LIFE-1-R4) Close the run_check verdict gap and residual failure-path findings".
- Branch: claude/life-1-r4-run-check-verdict. Worktree: C:/Users/poin/Documents/RMQ/.claude/worktrees/life1-r4-run-check-verdict.
- Base: d27ffa341f4ed8ceccc46817455eb26c73b319a1 (LIFE-1-R3 tip). Governance: 7b227c49ef2ec044b702126cc41c9add847eed01 (skill preflight PASS; required rmq-proof-sprint; runtime skills rmq-coordinator, rmq-proof-sprint, rmq-audit-prompt).
- Final tip: 2b2c022983385b4ee9d26224e9eef4b6d609e11e, clean tree. Candidate harness and runner bytes: d9411a7dae909462218fb32e3bb84e555cfa042c, unchanged through the final tip.
- Contract: LIFE1_R4_RUN_CHECK_VERDICT.md, 15,890 B, SHA-256 40f77ac4bbcc0f777364d7e27bdbce67bf785144d94c60ef7e2dcf222374f9f8. Finding source: LIFE1_R3_A1_FRESH_BLIND_DELTA.md, 34,798 B, SHA-256 1ae0d97e819c7e323164f8507ab25fe9de2d069e08642d81360ab0226aedb48f.
- Matrix: docs/internal/extensions/lifecycle1/repair-r4/ACCEPTANCE_MATRIX.md (frozen block created first at ea7e11bf and an exact byte prefix at the tip; evidence E-00..E-07 and dispositions appended below the marker).
- Report file: the runtime refused the report write with "Subagents should return findings as text, not write report files. Include this content in your final response instead." Per the contract this report is not written by a workaround; it is returned verbatim for coordinator persistence at docs/internal/extensions/lifecycle1/repair-r4/REPORT.md.

All local R4 work and the re-establishment of the R3 rows are done on one tip. Status is INCOMPLETE only because coordinator certification, the audit of this pass, integration with main and CI remain. No gate, CI, audit or acceptance result is claimed.

## Commits (d27ffa34..2b2c0229)

1. ea7e11bf - freeze the R4 acceptance matrix (first edit) + WDD-20260930-LIFE1-R4-01
2. b9027b1f - committed base probe and receipt collector; base reproductions + R4-02
3. 5fbc1c99 - repair of the nine harnesses + R4-03
4. 25451ca4 - validator: executable check before helper loading (caught by the probe) + R4-04
5. d9411a7d - versioned runner, v2 registry (60 controls), predicates, doubles, aux controls; runner, selector and heavy_run durable fixes + R4-05
6. 9a21a547 - control receipts; auxiliary fixture defect fixed + R4-06
7. 2802b84d - corrected auxiliary receipts + R4-07
8. 8ec10ec2 - campaign receipts + R4-08
9. 2b2c0229 - evidence and row dispositions + R4-09

## Changed paths (git diff --name-status --no-renames d27ffa34..2b2c0229: 808 entries, 16 M, 792 A)

M: the nine harnesses (lifecycle1/repair-r1/{run_controls,finalizer_control,run_check,dependency_child}.ps1, lifecycle1/repair-r2/run_check.ps1, scripts/lifecycle_validator.ps1, lifecycle-native-p0/repair-r1/{integrity_controls,dependency_controls}.ps1, lifecycle-native-p0/repair-r2/harness_stream_controls.ps1); repair-r3/{failure_controls,heavy_run,selector_controls}.ps1; repair-r3/doubles/{fault_function.ps1,stream_capture_override.ps1,validator_double.cs}; docs/internal/WORKFLOW_DESIGN_DECISIONS.md (the d27ffa34 blob, 973,117 B, is a byte prefix of the tip blob, 993,166 B). A: only docs/internal/extensions/lifecycle1/repair-r4/** (matrix, base_probe.ps1, aux_controls.ps1, predicates.ps1, make_registry.py, collect_receipts.py, FAILURE_CONTROL_REGISTRY.json, doubles/git_double.cs, receipts/**). Zero diff: the R3 v1 registry, repair-r3/receipts/**, repair-r3/REPORT.md, repair-r3/ACCEPTANCE_MATRIX.md, materialize_registries.py, the P3-4 historical verifiers, DESIGN_DECISIONS.md and every REQ-L1R3-PRESERVATION path. git ls-files --eol: 744 i/lf, 64 i/none (empty receipts); 0 CR bytes in the 808 changed blobs.

## Per-item confirmation and repair

- P2-1 (REQ-L1R4-VERDICT). Confirmed at d27ffa34 by the committed probe and base controls: both run_check files write `verdict: "pass"` next to `childFailure` for exit 7 and for a real helper timeout (exit 2). Repair: `$failed` includes `childFailure`; a malformed or unowned helper result is a stage error; the exit mapping is unchanged (a durable-write failure that would exit 0 exits 1). Every other writer of `life1-r3-finalization-v1` already used the overall meaning.
- P3-1 (REQ-L1R4-DURABLE). Confirmed: K1, K2 and the validator exit 0 after a failed durable write, the validator also writing PASS.json and its PASS line; heavy_run prints its success line. Repair in all nine harnesses and in failure_controls.ps1, heavy_run.ps1 and (same class, in scope) selector_controls.ps1: the write error is reported and the run fails with no success marker; PASS.json only after RESULT.json.
- P3-2 (REQ-L1R4-COVERAGE a, b). (a) IC-U: an exclusive lock held until process exit makes the fixture restoration throw inside cleanup while the stage fails; the stage error, two cleanup errors and 7/7 verified pins plus the tree check are all recorded. (b) The runner's pin-coverage predicate (repair-r4/predicates.ps1 Test-R4PinCoverage) requires every captured pin re-verified (verified, changed or unreadable-final), captured count equal to entryPinCount and, for setup failures, the registry's independent count (RC-S 5, FC-S 2, K1-S 9, K2-S 0, DC-S 0, LV-S 11, IC-S 4, DP-S 0, HS-S 6, LV-E 11, derived from capture order; they match all 47 R3 durable results).
- P3-3 (REQ-L1R4-COVERAGE c). Confirmed: the validator threw before its log root without its executable. Repair: identity capture, then the unchanged diagnostic, then helper loading, inside the evidence region; LV-E exercises it. Every other pre-root check is argument, selector or registry validation (inventory in matrix E-02).
- P3-5 (REQ-L1R4-LABELS). Readers: packed_native_lifecycle_stream_check.ps1 and repair-r3/literal_selector_controls.ps1 read only retained keys; the dormant lifecycle-native-p0 verifiers (repair-r2/verify_results.py, reused by repair-r3/verify_contract.py) read `source`, `helper`, `registry`, `validator`. Repair: entry pins under entrySource/entryHelper and entryRegistry/entrySource/entryValidator; the old keys regain their eb8e4f25 meaning, the post-run pin. No reader needed editing.
- P3-6 (REQ-L1R4-ORDER). Both run_check finally blocks and run_controls' per-case finally now record integrity before releasing the mutex (run_controls records `caseSlotChecks`). Static AST controls on exact blobs fail at d27ffa34 and pass at the tip.
- P3-7 (REQ-L1R4-OWNED-GIT). repair-r2 run_check reads HEAD (entry and final) and harness_stream_controls reads carrier/fixture status through the owned helper with 60 s deadlines; exit, streams and timeout are kept in the durable result (`gitProcesses`, `ownedRootStatus`); any failure is an integrity error.
- P3-4: deferred by the coordinator; the three historical verifiers are unchanged.

## Controls: base versus repaired

Registry v2 (repair-r4/FAILURE_CONTROL_REGISTRY.json, 48,252 B, normalized SHA-256 cf5ef090543773ef0a4fa473164e56633fabeef140301aad737bb2a7a3226dbc, 60 controls, base d27ffa34); the R3 v1 registry stays the runner default and byte-identical.

| Control | Finding | d27ffa34 (both shells) | Tip d9411a7d (both shells) |
| --- | --- | --- | --- |
| K1-F, K2-F | P2-1 | exit 7, verdict pass: rejected | exit 7, verdict fail: pass |
| K1-T, K2-T | P2-1 (real deadline) | exit 2, verdict pass: rejected | exit 2, verdict fail, helper TimedOut, deadline 3 s: pass |
| K1-W, K2-W | P3-1 | exit 0: rejected | exit 1, no durable file: pass |
| LV-W | P3-1 | exit 0, PASS.json, PASS line: rejected | exit 1, no PASS.json, no PASS line: pass |
| IC-U | P3-2 (a) | accepted (R3 already records it; predicted) | pass |
| LV-E | P3-3 | no RESULT.json: rejected | RESULT.json, diagnostic, 11 pins re-verified: pass |
| IC-L, HS-L | P3-5 | plain key holds the entry value: rejected | entry value only under entry*: pass |
| K2-G | P3-7 | hangs to the 180 s control deadline: timeout | owned 60 s timeout recorded, exit 3: pass |
| HS-G | P3-7 | no git exit/stderr in the integrity error: rejected | exit 128 and stderr recorded: pass |
| 47 R3 controls | R3 rows | accepted | pass |

Runs: base v2 pwsh 60/60 predictions matched (663.1 s), winps 60/60 (591.9 s); candidate v2 pwsh 60/60 (557.8 s), winps 60/60 (486.9 s); v1 replay at the candidate 47/47 (380.0 s); selector/registry controls 15/15 for v1 and 15/15 for v2 (19.6 s, 19.4 s); auxiliary controls 17/17 at d27ffa34 and 17/17 at 9a21a547 (ORD-K1/K2/RC fail at the base and pass at the tip, ORD-LV passes at both; HR-W exits 0 with its success line at the base and 1 without it at the tip; eleven synthetic predicate cases match verdict and exact reason, and the transcribed R3 predicate accepts the four pin mutations R4 rejects); base probe 6/6 defect at d27ffa34 and 6/6 repaired at d9411a7d. Every control restored and verified its copy; each run left the real worktree Git state unchanged.

## Campaigns (REQ-L1R4-CAMPAIGNS), head 2802b84d (harness bytes = d9411a7d)

Through repair-r2 run_check.ps1 under heavy_run.ps1 (global mutex only: each campaign harness takes the lane mutex itself), every finalization pass with 17/17 pins, global wait at most 0.006 s, exit 0:
- frozen registry: pwsh 67/67 in frozen order (273.4 s), winps 66/66 (204.5 s), registry 385c9bc9..., summary 12/12 pins, all 67/66 per-case slot checks verified;
- validator startup/single/full: pwsh 2/3/9 processes (5.4/8.2/47.1 s), winps (4.1/6.7/44.5 s), 12/12 identity pins, PASS.json;
- p0 integrity 15 controls (pwsh 273.5 s, winps 170.8 s), dependencies 19 (20.0 s, 14.0 s), harness-stream 11 (121.7 s, 94.4 s), all verdict pass; the winps p0 runs close the R3 "uncovered" note.
The three LF-pinned frozen inputs were materialized as exact blob bytes and restored afterwards (content proof, clean status). Receipt hashes are in each receipts/<name>/INDEX.json; campaign-summary/CAMPAIGN_SUMMARY.json indexes all fourteen.

## Scans and checks (final tip 2b2c0229 unless stated)

- design_decision_check.ps1 -Strict -Base <parent> -Head <commit>: exit 0 for all nine commits; range d27ffa34..2b2c0229: exit 0 (808 files).
- git diff --check d27ffa34..2b2c0229 and git diff --check: exit 0.
- Both hygiene rg scans over RMQ and lakefile.toml: no matches.
- claim_drift_scan.ps1 -Strict: exit 0, 1,266.7 s (deadline 5,400 s; global and lane mutex waits 0.004 s and 0.0 s); 3,679 hits, 0 strict failures.
- claim_drift_scan.ps1 -SelfTest: exit 0, 2,697.6 s (deadline 9,000 s; waits 0.004 s, 0.0 s); PASS (6 protected probes rejected and 2 attributed probes accepted; no emitted line cites a process-record path; the exclusion removed 431 hits, 4,110 to 3,679).
- Tree clean after every step; HEAD unchanged during the scans.

## Commands (host POINPAD; runner pwsh 7.6.5)

Matrix E-06 lists every command with deadline, mutex wait, duration and exit. Notable: a cold `lake build rmq_lifecycle_validate` under both mutexes, 1,356.6 s, exit 0 (the worktree had no build products); a development probe at 5fbc1c99 exited 1 and exposed the validator ordering fixed in 25451ca4; auxiliary attempt 1 at d9411a7d exited 1 on a fixture defect fixed in 9a21a547 (both kept as receipts, neither counted).

## Limits

- Owned-git hang/failure and write failures are exercised through test doubles (a compiled git double on PATH, a directory at the durable path); a real git hang is not host-creatable on demand.
- The durable-write failure of failure_controls.ps1 and selector_controls.ps1 is source-evident only (their fresh evidence roots cannot be obstructed without a runner-level fixture); heavy_run.ps1 is exercised by HR-W.
- Mutex ordering is certified statically on Git blobs; a behavioural race control would contend for the live lane mutex.
- The pin-coverage predicate treats any non-null entry value as captured, so an empty-string entry would count as captured (no harness writes one).
- dependency_controls' `pins`/`oldSummary` keys are the dependency inventory under test rather than a verification summary and were outside the LABELS row; noted for the coordinator.
- Candidate controls ran at d9411a7d and campaigns at 2802b84d; the final tip differs only by receipts, matrix and ledger (harness, runner, double, predicate and registry bytes identical).
- A process killed from outside cannot run its finally.

## Proof digestion

- What changed: the run_check "verdict" now means the overall verdict, so a failed or timed-out child can no longer sit beside `verdict: pass`; every harness and runner treats a failed durable write as a failed run; the validator records a missing executable in its durable result; two harnesses stop presenting entry pins under post-run names; integrity is checked while the lane slot is still held; and finalization git calls are bounded and recorded.
- In plain English: a green durable record now implies the child passed, the pins held, cleanup succeeded and the record itself was written; a hung git can no longer freeze finalization.
- New tests: 13 controls, each failing on the R3 tip and passing on the R4 tip (IC-U excepted by design), a real 3 s owned deadline rather than a flipped flag, a git double that really hangs or fails, and synthetic mutations showing the new predicates reject what the old one accepted.
- Live assumptions: the unchanged owned-process helper kills whole trees; SHA-256 identity; observed pwsh 7.6.5 and Windows PowerShell 5.1 semantics; the git double forwards command lines transparently (every control that used real git through it passed).
- A skeptical graduate student would ask: does any consumer still read the old integrity-only meaning of run_check's verdict (none found; passing runs still record pass); why is ordering certified statically rather than by a race (the live lane mutex); and why is IC-U accepted at the base (R3 already records cleanup errors; the control proves the path is exercised, which R3 never did).

## Requests

Coordinator certification of 2b2c022983385b4ee9d26224e9eef4b6d609e11e, persistence of this report at docs/internal/extensions/lifecycle1/repair-r4/REPORT.md, an audit of this pass, then integration with main and CI.

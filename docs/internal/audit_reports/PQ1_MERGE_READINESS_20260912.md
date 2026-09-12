# PQ1 merge-readiness verification receipt

Date: 2026-09-12 UTC. Disposition: **MERGE READY** for local `main`.
This is coordinator verification evidence, not another fresh blind audit.

Checked follow-up commit: `d23a0af2357511762b0781da55fba32c03e59a3c`.
Accepted mathematical/replay source: `6562ff62d14b17e918e7149f896bd0657ffd5aa0`.
Immutable independent audit report: `d21b190139fa810291ae271974ec00cde58af965`,
[`PQ1_FRESH_BLIND_4c89378.md`](PQ1_FRESH_BLIND_4c89378.md).
The [coordinator acceptance record](../packed_query/PQ1_COORDINATOR_ACCEPTANCE.md)
closes all 34 frozen requirement/invariant IDs and records the audit identities,
model limits, lifecycle disposition and remaining research scope.

## Follow-up repairs

- Current public and paper surfaces now record PQ1 acceptance and describe the
  program as loop-free. This closes the optional terminology finding without
  changing any theorem or model operation.
- The per-commit history check exposed a report-classification defect in
  `3c8097e57bb76a5d34cb70c9672671af06757d0d`. Dated internal audit Markdown now
  counts as evidence. Six exact cases accept the report and reject nearby
  Lean, script, prompt, plan and public-document paths. The eight retrospective
  certification exceptions and all audited commits are unchanged.
- The isolated per-commit fixture now fixes its own line-ending configuration
  so Windows PowerShell does not turn an unrelated Git conversion warning into
  a terminating error. Production warning-observation tests and the user's
  repository configuration are unchanged. Rationale and alternatives are in
  WDD-20260912-PQ1-016; acceptance decisions are DD-20260912-PQ1-023 and
  WDD-20260912-PQ1-015.

## Verification results

| Check | Result |
| --- | --- |
| Affected public import and exact-type consumer build | PASS; `RMQPaper` and `RMQ.Validation.PackedQueryContract` |
| Headline trust inventory | PASS; all 114 records use only `propext`, `Classical.choice`, `Quot.sound` |
| Production classifier regression, PowerShell 7 | PASS; 39 ordered cases, 24 reject and 15 accept; 58.325s |
| Production classifier regression, Windows PowerShell 5.1 | PASS; same 39 cases and exact verdicts; 50.669s |
| Incoming history from local main `24bc22dc107252e4f62b2dab1b7d2d2b61564bdc` through `d21b190` | PASS; all 128 non-merge commits certified individually, including `3c8097e`; 36.767s |
| Follow-up commit's strict design/workflow check | PASS; 32 paths, 20 code, 5 workflow, 7 neutral |
| Strict current claim scan on committed follow-up | PASS; 1563 hits, zero strict failures |
| Paper and citation checks | PASS; 36 ledger rows (30 accepted, 0 provisional, 6 open), all 27 pinned citations resolve |
| Constant synchronization | PASS; existing 210 and 427 surfaces remain synchronized |
| Production paper topology on clean follow-up commit | PASS; 89 documentary identifiers and 54 paper identifiers resolved; 120.999s |
| Frozen Git-blob preservation | PASS; original acceptance-matrix prefix 46,622 bytes and paper evidence-matrix prefix 22,406 bytes unchanged; immutable audit blob unchanged |
| Mathematical source preservation | PASS; only the separately verified headline docstring differs from the fully gated source; all 15 manuscript theorem blocks preserved except the candidate title label |
| Hygiene and whitespace | PASS; required trust-footprint scans have no matches; diff whitespace check passes |

Both full source gates remain valid evidence for unchanged mathematical and
Lean replay code: all 18 checkers passed at `6562ff6`, in 5654.834s on
PowerShell 7 and 7415.157s on Windows PowerShell 5.1. These include the full
38-case PQ1 mutation campaign, runtime/selector controls and other mandatory
campaigns detailed in the independent audit. The new report-classification
and fixture edits receive the separate both-host regression above; they are
not retroactively claimed to have been present in the earlier full gates.

The local machine-readable receipt is `.lake/pq1-merge/verification.json`,
with individual checker artifacts and hashes. Earlier failures are retained:
the original history classification failure, a paper check attempted before
its required clean commit, an initially stale expected regression count,
the Windows fixture warning, and a restoration check that correctly caught
coordinator staging during a test. Final certification used the corrected
tree and no concurrent tracked edits or staging.

This receipt adds evidence only. Its own strict claim and per-commit decision
checks precede integration. The user authorized fixes followed by merge;
integration is a fast-forward of local `main` to the branch containing this
receipt, with no conflict-resolution source changes. The active coordinator
branch and worktree are retained. Remote publication is outside this local
integration disposition.

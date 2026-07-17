# Worker And Worktree Lifecycle

This document governs the state of delegated ADD work. It prevents branch and
worktree accumulation from becoming hidden coordination debt.

## States

Every delegated task moves through the applicable states:

1. **Planned**: handle, target, base, and intended branch are assigned.
2. **Launched**: the prompt has been sent.
3. **Active**: a worker has created or confirmed its worktree and branch.
4. **Submitted**: the worker reports a commit or a read-only report. Submission
   does not imply that the worker's completion assessment is accepted.
5. **Candidate complete**: when applicable, the worker reports
   `CANDIDATE_COMPLETE` with the exact provisional declaration and a frozen,
   closed acceptance matrix containing attempted anti-vacuity challenges. This
   is self-audit, not acceptance. A missing status, informal "closed" claim, or
   requirement-to-theorem name list remains **Submitted**, not candidate
   complete.
6. **Audited**: the coordinator records a merge, port, reject, or follow-up
   verdict.
7. **Externally audited**: when required, a fresh blind auditor has reviewed
   the exact candidate commit against the frozen contract.
8. **Accepted**: the coordinator independently closed the matrix and any
   mandatory external-audit gate.
9. **Integrated**: accepted work is present in the coordinator frontier.
10. **Rejected**: the branch is not part of the frontier; useful evidence is
    recorded.
11. **Ported**: selected changes were applied elsewhere; the original branch is
    no longer authoritative.
12. **Archived**: the durable report/commit link and disposition are recorded.
13. **Retired**: the worktree is removed and the branch is retained or deleted
    according to the policy below.

A write task is not operationally complete at **Integrated**. It is complete
at **Retired**. A branchless read-only task is complete when its report is
submitted, audited, durably archived or incorporated into the coordinator
synthesis, and its temporary detached worktree (if any) is removed.

## Required Task Record

The coordinator should be able to recover:

- worker/auditor handle and requested chat title;
- task type and roadmap node;
- exact base and target branch/commit;
- worktree path, when applicable;
- submitted commit or report path;
- verification evidence;
- coordinator disposition;
- integration commit;
- retirement status.

This may live in the coordinator report while task volume is low. Add a
machine-readable active-task ledger when concurrent work regularly exceeds what
one coordinator update can state clearly.

## Branch Policy

- Write workers use coordinator-assigned `codex/` branches and fresh worktrees.
- Read-only scouts inspect an exact commit and do not need a branch.
- Report-only auditors may use an `audit/` branch with a single allowed report
  path.
- A same-worker repair for an unmet acceptance criterion remains part of the
  same lifecycle task even when it adds another commit.
- A branch must never be merged merely because its worker says it is complete.
- Public paper capstones, trust-boundary changes, combined space/execution
  theorems, and roadmap-node closures require a fresh blind exact-commit audit
  before acceptance or merge.
- Prefer additive aliases and porting over conflict-heavy merges when the
  frontier moved materially during the task.
- Tag or retain milestone/release branches. Ordinary integrated worker branches
  may be deleted after their commit is reachable from the durable frontier.
- Rejected branches may be deleted after their useful obstruction or audit
  evidence is preserved.

## Worktree Retirement

After integration/rejection:

1. verify the submitted commit and disposition are recorded;
2. verify no uncommitted worker files would be lost;
3. remove the worktree with `git worktree remove`;
4. prune stale worktree metadata;
5. delete an ordinary local/remote branch only when its useful commits are
   reachable or deliberately rejected;
6. record any intentionally retained branch and why.

Cleanup is a coordinator action. Do not automate destructive cleanup without a
dry-run inventory and explicit approval.

## Automated Completion Monitors

When the user opts into the coordinator's audited worker chain, record one
completion monitor per worker task together with its handle, task/thread ID,
exact governed base, branch, and owning coordinator task. A monitor may read
status but must not open, steer, or mutate an active worker.

Use a 30-minute heartbeat cadence by default. Before creating a task, check the
current task and automation inventories for the same handle/base/branch. If the
task is created but monitor attachment fails, retain its task ID and retry the
monitor only; never create a duplicate worker as recovery. Reconstruct this
inventory after coordinator restart before launching a successor.

After completion, the owning coordinator must audit the exact candidate,
finish reusable failure-mode feedback, and decide whether a successor prompt is
`READY_TO_SEND`. Delete the completed monitor only after that disposition is
reported and any launched successor has its own distinct monitor. A monitor is
coordination state, not branch-retirement evidence, and never authorizes merge,
push, branch deletion, or worktree cleanup.

## Audit Interaction

Fresh blind auditors receive exact commits and an audit packet, not a live
worker worktree or chat transcript. Continuation auditors may use the same
session for one correction loop. Longitudinal auditors compare selected
milestones and do not replace fresh final acceptance.

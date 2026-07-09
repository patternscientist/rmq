# Worker Prompt Template

Use this template for proof, implementation, validation, docs, or tooling
workers. Delete irrelevant bracketed guidance before sending.

```text
Worker identity:
- Worker handle: [WORKER_HANDLE].
- Requested chat/thread title: `([WORKER_HANDLE]) [SHORT_TASK_SUMMARY]`.
- Use this handle in the completion report.
- If your environment supports renaming the chat/thread, set that title before
  starting. If it does not, repeat the requested title at the top of your
  completion report.

Branch/worktree:
- Create a fresh worktree and branch named exactly: [WORKER_BRANCH].
- Base it on: [BASE_BRANCH].
- Fetch first and verify the base before editing.
- Do not edit the coordinator checkout.
- Do not revert or overwrite unrelated changes.

Goal:
[One sentence naming the exact theorem/profile/document/tooling target.]

Write scope:
- [File or directory 1]
- [File or directory 2]

Required target:
- [Exact theorem name, executable name, document name, or script behavior.]

Forbidden shortcuts:
- Do not replace theorem work with prose caveats.
- Do not add proof-only answer fields, uncounted payload, synthetic events, or
  public-route compatibility thresholds unless the prompt explicitly asks for
  that historical/compatibility surface.
- Do not conflate model-cost ticks, payload bits, proof-only fields, Lean
  runtime, or compiled-code behavior.
- Do not stage transcript dumps, zips, scratch dirs, or unrelated files.

Completion discipline:
- Stage only intended files.
- Commit the finished branch unless the prompt explicitly says not to commit.
- Include the branch name, worktree path, base branch, and final commit hash in
  the completion report. If committing is blocked, state the exact reason and
  leave the worktree status clear.

Context to read:
- docs/internal/RMQ_FINAL_ROADMAP.md
- docs/internal/AUDIT_PROTOCOL.md
- docs/internal/DESIGN_DECISIONS.md
- docs/internal/WORKFLOW_DESIGN_DECISIONS.md
- [Task-specific theorem/docs files]

Design-decision check:
- If you choose or change a proof/code/artifact architecture decision, update
  docs/internal/DESIGN_DECISIONS.md.
- If you choose or change ADD workflow, audit, automation, delegation,
  evidence, model-routing, or handoff policy, update
  docs/internal/WORKFLOW_DESIGN_DECISIONS.md.
- Entries should record rationale and rejected alternatives clearly enough that
  a future paper writer can reconstruct the design exposition.

Verification:
- [Targeted lake build or docs/script checks]
- git diff --check
- scripts/claim_drift_scan.ps1 [if public/trust prose changed]
- scripts/design_decision_check.ps1 [if architecture/workflow-sensitive files changed]

Completion report:
- worker handle;
- branch name, worktree path, base branch, and final commit hash;
- changed files;
- theorem names / script names / docs changed;
- conceptual meaning;
- live assumptions;
- skeptical-reviewer questions;
- design/workflow decisions logged, or why none were needed;
- exact verification command outcomes;
- next crisp target.
```

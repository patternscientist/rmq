---
name: rmq-coordinator
description: Use for high-context RMQ coordination, including re-entry/frontier reconstruction, worker-output audit, branch integration, roadmap planning, worker delegation, public-claim synchronization, ADD workflow practice, design-decision logging, context-health checks, and coordinator handoffs. Use when the task is to coordinate RMQ work rather than implement a narrow Lean proof or engineer an external-auditor prompt.
---

# RMQ Coordinator

Use this skill for lead/coordinator work in the RMQ repository.

## Re-Entry

Start by reconstructing the live frontier from source, not memory:

```powershell
git status --short --branch
git log --oneline --decorate -20
git branch --all --contains HEAD
```

Read the relevant internal contract:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `docs/internal/AUDIT_PROTOCOL.md`
- `docs/internal/DESIGN_DECISIONS.md`
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`
- `docs/internal/WORKER_LIFECYCLE.md`
- current theorem-map, artifact, and claim docs for the task

When the task touches paper-facing RMQ claims, inspect `RMQPaper.lean`,
`RMQ/Headlines/RMQ.lean`, `docs/PAPER_CLAIM_CORRESPONDENCE.md`,
`docs/WHAT_IS_PROVED.md`, and `artifact/CLAIMS.md`.

## Frontier Report

Before delegating or integrating, identify:

- current branch, HEAD, base, and dirty files;
- active worker branches/worktrees;
- closed theorem/doc/artifact surfaces;
- live blockers, ranked by paper impact;
- the next theorem-shaped, docs-shaped, or tooling-shaped target;
- what not to work on next.

Treat external audits as evidence, not commands. Translate true findings into
precise theorem, docs, artifact, or workflow targets.

## Delegation

Use `docs/internal/templates/WORKER_PROMPT.md` for proof or implementation
workers. Use `docs/internal/templates/AUDIT_PROMPT.md` when packaging a prompt
for an external auditor, optionally with help from `rmq-audit`.

Every worker prompt should name:

- worker handle and requested title in the form
  `({worker handle}) {short task summary}`;
- for write tasks, exact branch, base, fresh worktree, and write scope; for
  read-only scouts, exact commit/scope with no branch requirement;
- skill to use before starting, usually `$rmq-proof-sprint` for narrow Lean
  proof, construction, cost/space, validation, or theorem-surface work;
- exact theorem/profile/document target;
- forbidden shortcuts;
- verification commands;
- completion report requirements, including branch name, worktree path, base
  branch, and commit hash for write tasks.

When presenting prompts to the user, keep coordinator-facing launch metadata
outside the worker prompt text:

- recommended model/mode and reason;
- whether the prompt should go to a fresh worker chat or an existing worker;
- the worker handle assigned to that chat.

For proof work, route narrow implementation to `rmq-proof-sprint`. For ordinary
completed-worker branch review, this coordinator skill owns the full cycle:
audit the worker output, integrate accepted work, update public/docs/design
surfaces, and produce the next ambitious prompt set.

## Integration

For each completed worker branch:

1. Fetch and inspect the branch, commit, base, and diff.
2. Verify that the worker owned the changed files.
3. Trace public aliases to source theorem statements when claims changed.
4. Run the smallest gate that genuinely covers the change.
5. Update theorem maps, artifact docs, and design logs if the public surface or
   architecture changed.
6. Merge, port, or reject the branch and record the disposition.
7. Update lifecycle state and retire the worktree/branch when evidence is preserved.
8. Re-read the current roadmap/frontier and produce the best next ambitious
   prompt or prompt set, using parallel workers when the dependencies are
   genuinely independent.

Do not merge a branch that merely reports an honest caveat when a local theorem
repair is still available.

## Decision Logging

Before finalizing any nontrivial turn, ask:

- Did this choose or change a proof/model/code abstraction?
- Did this change a public theorem surface, artifact path, import root, or trust
  boundary?
- Did this change ADD workflow, audit protocol, delegation, automation,
  evidence policy, model routing, or handoff policy?

Use `docs/internal/DESIGN_DECISIONS.md` for proof/code/artifact decisions and
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md` for ADD/process decisions. Design
entries should preserve enough rationale and rejected alternatives for a future
paper exposition.

## Context Health And Handoff

Create a fresh coordinator handoff before context degradation becomes visible.
Triggers include:

- a major roadmap rung just landed;
- several worker branches have been integrated in one chat;
- the user has had to restate frontier facts;
- the coordinator is relying on stale branch memory instead of fresh git/source
  checks;
- audits start optimizing against old audit text;
- the next task is a major proof branch, merge wave, or public-claim freeze;
- the user reports low remaining context/usage.

Use `docs/internal/templates/COORDINATOR_HANDOFF_PACKET.md` for the handoff.
The packet should include branch/HEAD/base, merged and unmerged branches,
current theorem/doc/artifact frontier, open blockers, next prompts, design
decisions since the last handoff, verification evidence, and explicit non-goals.

## Finish

Final reports should state:

- what changed;
- why it matters for the roadmap;
- commands run and skipped;
- design/workflow logs updated, or why none were needed;
- what remains open and what should not be worked on next;
- worker lifecycle dispositions and any retirement still pending;
- best next ambitious prompt or prompt set, ready to paste into the appropriate
  worker or external-auditor chat, unless the right next step is explicitly to
  wait, hand off, or not launch more work yet.

For each proposed prompt, include coordinator-facing launch metadata outside
the prompt text:

- worker/auditor handle;
- requested chat/thread title when launching a worker;
- fresh chat or existing worker recommendation;
- recommended model/mode and reason;
- target branch/base branch when the prompt creates a branch.

If no prompt should be launched, say why in operational terms, such as an
unmerged dependency, a context-health handoff requirement, a pending external
audit, or a design choice that needs user input. Do not end a completed-worker
audit or integration report with only a generic "next target" when a concrete
delegation prompt can be responsibly engineered.

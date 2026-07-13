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
git worktree list --porcelain
git log --oneline --decorate --graph --all --simplify-by-decoration -35
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
  read-only scouts, exact commit/scope with no branch requirement and a durable
  report or coordinator-synthesis disposition;
- skill to use before starting, usually `$rmq-proof-sprint` for narrow Lean
  proof, construction, cost/space, validation, or theorem-surface work;
- exact theorem/profile/document target;
- the local owned rung and the larger roadmap node it feeds;
- the exact condition under which the local rung is complete and the distinct
  condition under which the roadmap node may be marked closed;
- a requirement-to-evidence matrix obligation and the applicable inherited
  invariants from the proof-sprint completion gate, assigned by stable ID;
- forbidden shortcuts;
- verification commands;
- completion report requirements, including branch name, worktree path, base
  branch, and commit hash for write tasks.

Before launch, verify that the worker's exact base contains the current
workflow skill and prompt policy. If proof and workflow branches are siblings,
join them in an explicit integration base or require the worker to merge the
named workflow commit before using the skill. Do not assume a worker can see
policy that exists only on another branch.

When presenting prompts to the user, keep coordinator-facing launch metadata
outside the worker prompt text:

- recommended exact model variant, reasoning/mode, and reason (for example,
  `GPT-5.6 Sol, Extra High, Fast`, never merely `5.6`);
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
4. Reconstruct the requirement-to-evidence matrix independently. Check the
   worker's `CANDIDATE_COMPLETE` declaration against the frozen prompt
   requirements, named consumer, and inherited invariants. Inspect checked
   theorem types and expand load-bearing definitions; declaration names and
   documentation summaries are not evidence.
5. For semantic liveness, coverage, ownership, refinement, or equivalence
   claims, perform a counterfactual mutation audit: add a dead source, remove a
   used source, replace the predicate by a tautology, or assign a consumer label
   without an evaluator edge. Identify the theorem that fails. If none fails,
   the row is open.
6. Record local-rung status and roadmap-node status separately; a closed helper
   or prerequisite does not close its consumer node.
7. For combined public claims, verify that space, execution, provenance, and
   machine conjuncts concern the same objects. For whole-machine claims,
   inventory every read segment, physical offset, and the input-size relation
   for the one query-independent word width. Check that validity guards apply
   to every combined field or are connected by a theorem on the same domain.
8. Trace returned values to charged reads and check the relevant value/state/
   route projection, not merely inequality of an aggregate record. Check actual
   evidence quantification and validity domain against the public claim; one
   concrete witness cannot close a universal row. Check actual footprint
   addresses against modeled address capacity when machine/store work changed.
9. Treat a missing or informal candidate status as `INCOMPLETE`; "closed at
   worker/gate level" is not the required provisional declaration.
10. Run the smallest gate that genuinely covers the change, including small and
   threshold boundary cases when layout or dispatch changed.
11. Treat claim-drift tooling as a consistency aid, not ground truth. Inspect the
   policy/allowlist itself when claims or constants change.
12. Update theorem maps, artifact docs, and design logs if the public surface or
   architecture changed.
13. For a public capstone, trust-boundary change, combined space/execution
   theorem, or roadmap-node closure, launch a fresh blind exact-commit audit
   before merge or closure. Do not give that auditor the worker verdict.
14. Record `ACCEPTED` only after the coordinator gate and any mandatory blind
   audit; otherwise continue, port, or reject the branch.
15. Update lifecycle state and retire the worktree/branch when evidence is
   preserved.
16. Re-read the current roadmap/frontier and produce the best next ambitious
   prompt or prompt set, using parallel workers when dependencies are genuinely
   independent.

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
- local-rung completion and roadmap-node completion as separate statuses;
- best next ambitious prompt or prompt set, ready to paste into the appropriate
  worker or external-auditor chat, unless the right next step is explicitly to
  wait, hand off, or not launch more work yet.

For each proposed prompt, include coordinator-facing launch metadata outside
the prompt text:

- worker/auditor handle;
- requested chat/thread title when launching a worker;
- fresh chat or existing worker recommendation;
- recommended exact model variant, reasoning/mode, and reason (for example,
  `GPT-5.6 Sol, Extra High, Fast`, never merely `5.6`);
- target branch/base branch when the prompt creates a branch.

If no prompt should be launched, say why in operational terms, such as an
unmerged dependency, a context-health handoff requirement, a pending external
audit, or a design choice that needs user input. Do not end a completed-worker
audit or integration report with only a generic "next target" when a concrete
delegation prompt can be responsibly engineered.

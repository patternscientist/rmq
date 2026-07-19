---
name: rmq-coordinator
description: Use for high-context RMQ coordination, including re-entry/frontier reconstruction, worker-output audit, branch integration, roadmap planning, worker delegation, public-claim synchronization, ADD workflow practice, design-decision logging, context-health checks, and coordinator handoffs. Use when the task is to coordinate RMQ work rather than implement a narrow Lean proof or engineer an external-auditor prompt.
---

# RMQ Coordinator

Use this skill for lead/coordinator work in the RMQ repository.

## Skill Availability Gate

Before re-entry or any completed-worker audit, verify that the checkout contains
every repo-local RMQ skill tracked at the declared workflow-governance frontier
and that the runtime exposes every explicitly required role skill. Run
`scripts/project_skill_preflight.ps1` with:

- the exact governance ref;
- `rmq-coordinator` as the required skill;
- the RMQ skill names actually shown in the runtime catalog.

The governance frontier controls workflow instructions; an older detached
source/audit target does not replace it. If the preflight script is absent, the
governance ref is not in the checkout ancestry, a canonical skill is missing or
stale in the checkout, or an explicitly required role skill is missing from the
runtime catalog, stop and notify the user. Report the working directory, HEAD,
governance ref, and the expected, checkout, and runtime skill sets. Do not
substitute `rmq-proof-sprint` or continue a best-effort coordinator run. Resume
only after the checkout/catalog is corrected and the task is restarted, unless
the user explicitly authorizes a disclosed fallback; a fallback cannot record
acceptance, integration, or roadmap closure.

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
for an external auditor, optionally with help from `rmq-audit-prompt`.

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

Close transitive write scope before launch. In particular, any prompt that may
edit `scripts/gate.ps1` must also include
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`; the strict workflow-decision check
requires that companion even when the gate edit changes comments only.

For a prompt that restores, renames, splits, or migrates a public theorem or
historical identity, close the Lean consumer surface before launch too. Record
`- Dependency-surface inventory:` with the exact searched declaration symbols,
every directly inspected tracked consumer path, and the expected repair paths
from the exact worker base. Trace aliases, validation guards, examples, trust
inventories, and public compatibility modules; do not treat a source-file
rename as self-contained merely because the source theorem elaborates. Every
expected repair path must already be in write scope before `READY_TO_SEND`.

For any prompt claiming that every live/current public documentation surface
is synchronized, derive the read/verification inventory from
`docs/internal/CLAIM_DRIFT_POLICY.json` `currentFactSurfacePathRegex`, not from a
prompt-local hand list. Put `- Current-surface inventory:` in the prompt, name
that registry and field, and before launch record the exact matched count, full
matched-path list, and expected-repair-path list produced from the exact worker
base. Inspect every matched tracked path yourself; do not delegate first
discovery of the closed inventory to the worker. Include every expected repair
path in write scope before `READY_TO_SEND`. The prompt preflight must reproduce
the registry count/path set and verify every declared repair path is owned. A
green strict scan is a lower bound, not evidence that the registry or term
vocabulary is exhaustive.

Put `Make the title of this chat exactly: ...` as the first line of the pasted
worker prompt. A title shown only as identity metadata is not an instruction to
rename the chat.

Classify every proposed prompt as `READY_TO_SEND` or `DRAFT_DO_NOT_SEND`.
Use `DRAFT_DO_NOT_SEND` whenever an exact base is not yet governed, a dependency
is unmerged, or the failure-mode feedback loop below is pending. Before marking
a prompt `READY_TO_SEND`, populate `docs/internal/templates/WORKER_PROMPT.md`
and run `scripts/worker_prompt_preflight.ps1` with the prompt file, exact
governance and worker-base SHAs, worker handle/title, required skill, branch,
and feedback-loop status. Treat a failed preflight as a launch blocker.

Run the preflight for every prompt artifact you emit, including
`DRAFT_DO_NOT_SEND`. A draft with feedback `PENDING` may pass the draft policy
without gaining launch authority. If the read-only contract forbids even a
temporary prompt artifact, report `NOT_RUN` and keep the prompt a non-launchable
specification. `READY_TO_SEND` always requires a populated template artifact
and a passing preflight; title/SHA/skill/branch literals alone are insufficient.
The preflight is a structural lower bound, not a semantic judge. Before
`READY_TO_SEND`, reread the roadmap target, local-versus-node closure, frozen
acceptance IDs, scope, forbidden shortcuts, verification, and report contract
against source evidence; record semantic-contract review `COMPLETE` and pass it
to the preflight. Trivial filler or merely long text is not a completed review.

Before launch, verify that the worker's exact base contains the current
workflow skill and prompt policy. If proof and workflow branches are siblings,
join them in an explicit integration base or require the worker to merge the
named workflow commit before using the skill. Do not assume a worker can see
policy that exists only on another branch.

Verify the destination task separately from the worker base. A returning task
may be labeled `READY_TO_SEND` only when its latest runtime inventory explicitly
shows every role skill required by that prompt. Repository presence, a prompt
instruction, or a branch created inside that task is not runtime evidence. If
the returning task's required-role catalog is unknown or stale, do not resend
there: start a fresh Codex worktree task from the exact governed repair-base
branch, mark the prompt `FRESH`, and require project-skill preflight as its first
action. Record destination task kind and runtime evidence in
`worker_prompt_preflight.ps1`. Moving an old task to a new branch/worktree does
not by itself certify that its runtime skill catalog was rebuilt.

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

### Opt-In Automated Completion Loop

When the user explicitly authorizes automatic worker launch and follow-up,
turn the normal coordinator cycle into an audited worker chain:

1. Create each worker as a separate user-owned Codex task at an exact governed
   branch/ref. Put the full preflighted worker prompt in the initial message;
   do not use a low-context subagent as a substitute for the requested task.
2. Register one logical completion-monitor record per worker. When the app
   permits only one heartbeat per coordinator task, multiplex all exact worker
   records in that heartbeat instead of creating a cron workaround. While a
   worker is active, read status without opening or steering it and report only
   a terse update. Never infer completion from inactivity or a quiet terminal.
3. On completion, treat the response as untrusted, run the full completed-
   worker audit at its exact commit, complete the failure-mode feedback loop,
   and only then engineer successor prompts from the current roadmap.
4. Automatically launch a successor only when its artifact is
   `READY_TO_SEND`, `worker_prompt_preflight.ps1` passes, semantic review and
   reusable-failure feedback are complete, its exact base contains current
   governance, and no active task already owns the same handle/base/branch.
   Add the successor's logical monitor record to the heartbeat in the same
   operation.
   `AUTO-CHAIN-PRIVATE-REPAIR-BASE`: when the sole launch blocker is that the
   completed candidate and current governance are sibling commits, create a
   dedicated local unpublished repair-base branch and worktree, join governance
   into the candidate, verify exact two-parent ancestry, changed-path scope,
   `git diff --check`, clean state, and project-skill preflight, then use that
   exact commit as the successor base. This is workflow construction, not
   acceptance or integration into the roadmap frontier. Stop if the join has a
   semantic/public-theorem conflict, needs a proof choice, touches `main` or a
   published frontier branch, would overwrite an owned branch, or requires a
   push.
5. Remove the completed worker's logical record after its audit and successor-
   launch disposition are delivered. Update the multiplexed heartbeat while
   other workers remain; delete it only when no logical records remain.
   `AUTO-CHAIN-MONITOR-RETIREMENT`: do not finish a terminal-worker turn while
   its old logical watch remains live. Use the automation API first. If deleting
   the currently executing empty heartbeat cannot acknowledge because it holds
   its own active-run lock, verify the exact automation ID, target thread, and
   empty watch set, then move only that exact catalog record recoverably out of
   the live automation directory and report the retired path. Never alter an
   unrelated automation. Preserve task/branch evidence; automation does not
   authorize destructive lifecycle cleanup.
6. Stop and notify the user instead of launching when a prompt remains a draft
   after the permitted private repair-base construction, a merge into `main` or
   another published/frontier branch or any push is required, dependencies
   conflict, the runtime skill inventory is unknown, the next step needs a new
   proof architecture choice, the private join has a semantic conflict, or
   concurrent heavy workers would make the launch unsafe or wasteful.

Before task creation, list current tasks and automations and match the exact
handle/base/branch tuple. Use a 30-minute heartbeat cadence by default, changing
it only when measured task duration justifies another interval. Task creation
and monitor attachment are not atomic: if creation succeeds but monitor setup
fails, preserve and report the created task ID, retry only monitor attachment,
and never create a replacement worker. On coordinator restart, reconstruct the
chain from task and automation inventories before launching anything.

Route nontrivial Lean proofs, public theorem repairs, and architecture-bearing
work to `gpt-5.6-sol` with `max` reasoning by default. Use `xhigh` for tightly
bounded mechanically checked repairs and `gpt-5.6-terra` with `xhigh` for
read-only or lower-risk tooling work. Do not select `ultra` routinely; require
an explicit coordinator record of why `max` is inadequate for that exact task.
Model strength does not relax proof-sprint, audit, or verification gates.

This loop automates launch, monitoring, audit, and next-prompt engineering. It
authorizes only the private governed repair-base joins described above. It does
not authorize integration into `main` or a published roadmap frontier, pushes,
branch deletion, worktree cleanup, public-claim publication, or acceptance
without the ordinary coordinator and blind-audit requirements.

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
   When the acceptance contract claims an exhaustive or production mutation
   campaign, require the cases, expected verdicts, and restoration checks to be
   committed and replayable from the candidate. Matrix prose, terminal output,
   an unreferenced Git object, or a one-off edited worktree is scheduling/process
   evidence only. For a public dependency, also require a checked exact-type
   consumer whose elaboration fails when the advertised conjunct is removed;
   printing the current theorem's axioms does not pin its type.
   A replay harness must also make its own coverage mechanically nonvacuous:
   declare the exact ordered case registry and any ID-to-object mapping, reject
   missing or duplicate IDs, require a focused selector to execute exactly one
   requested frozen ID, and reject unknown selectors. A total pass count is not
   an exhaustive registry check. If the harness invokes Lean or another child
   process, require a positive evidence-based per-stage deadline, process-tree
   termination on timeout, failure classification, and cleanup plus live-tree
   integrity checks in `finally`. Reproduce these controls without paying for
   the full semantic campaign before accepting its aggregate gate.
6. Put the positive predicate `P` and mutation predicate `Q` side by side,
   including guards and quantifiers. Require the same relation or a checked
   `P -> Q` bridge. Compare component versus top-level execution, attempted
   versus successful reads, arbitrary versus valid-query parameters, and
   event-value membership versus actual occurrence production.
   Audit formal obstructions by the same rule: require negation of the frozen
   target or a checked target-to-`False` implication on the same objects and
   quantifiers.  Do not compose an arbitrary-state mutation, an unbounded
   shape fact, and a singleton reachability witness by prose.  Require one
   checked canonical reachable family when their conjunction is load-bearing,
   and distinguish failure of the current implementation from impossibility
   of every construction the contract permits.
7. Audit information preservation in the theorem conclusion. If prose claims
   occurrence, multiplicity, or actual invocation provenance, require a global
   position or equivalent decomposition plus the producing instruction, folded
   pre-state, local occurrence, and computed invocation parameters. A proof
   term that used this data but returned a relation that erased it is weaker.
8. Record local-rung status and roadmap-node status separately; a closed helper
   or prerequisite does not close its consumer node.
9. For combined public claims, verify that space, execution, provenance, and
   machine conjuncts concern the same objects. For whole-machine claims,
   inventory every read segment, physical offset, and the input-size relation
   for the one query-independent word width. Check that validity guards apply
   to every combined field or are connected by a theorem on the same domain.
10. Trace returned values to charged reads and check the relevant value/state/
   route projection, not merely inequality of an aggregate record. Check actual
   evidence quantification and validity domain against the public claim; one
   concrete witness cannot close a universal row. Check actual footprint
   addresses against modeled address capacity when machine/store work changed.
11. Treat a missing or informal candidate status as `INCOMPLETE`; "closed at
   worker/gate level" is not the required provisional declaration.
12. Do not accept the worker's classification of residual work as "strictly
    stronger", future hardening, or out of scope. Map it independently to the
    frozen requirements and inherited IDs; only an explicit coordinator
    contract amendment can narrow or defer a row.
13. Run the smallest gate that genuinely covers the change, including small and
   threshold boundary cases when layout or dispatch changed.
14. Treat claim-drift tooling as a consistency aid, not ground truth. Inspect the
   policy/allowlist itself when claims or constants change.
15. Update theorem maps, artifact docs, and design logs if the public surface or
   architecture changed.
16. For a public capstone, trust-boundary change, combined space/execution
    theorem, or roadmap-node closure, launch a fresh blind exact-commit audit
    before merge or closure. Do not give that auditor the worker verdict.
17. For a report-only audit branch, verify report-sensitive checks on the
    committed report tree. A green gate run before the report was written does
    not certify the submitted audit commit; inspect and rerun strict claim
    drift rather than granting report paths a broad allowance.
18. Record `ACCEPTED` only after the coordinator gate and any mandatory blind
    audit; otherwise continue, port, or reject the branch.
19. Update lifecycle state and retire the worktree/branch when evidence is
    preserved.
20. Re-read the current roadmap/frontier and produce the best next ambitious
    prompt or prompt set, using parallel workers when dependencies are genuinely
    independent.

Do not merge a branch that merely reports an honest caveat when a local theorem
repair is still available.

### Verification Economics

Plan verification from the changed paths and acceptance rows before launching
commands. Classify each check as development-loop, final-required, or
conditional, and state what unique failure it can detect. Run cheap static
checks first, focused Lean targets next, public consumers next, and the
aggregate gate last only when the scope or frozen contract requires it. A
narrow proof, docs-only change, or read-only audit does not automatically need
every repository root, validator, harness, and aggregate gate.

Treat a command expected to take several minutes as an expensive check:

- run only one heavy Lean/Lake process at a time against a shared build tree;
- use prior exact-command timings to choose a timeout with realistic margin,
  never one shorter than a recent successful run;
- before retrying a timeout, inspect whether its child process is still live,
  whether build artifacts advanced, whether a dependency warm-up is missing,
  and whether the focused check fell back to a full build;
- never launch the same expensive command again on an unchanged tree merely
  because its wrapper timed out or stayed quiet. Resume/wait for the surviving
  process, or retry only after a material change such as fixing the failure,
  warming prerequisites, removing an owned orphan, narrowing the target, or
  revising a timeout shown by observed runtimes to have been too short;
- after a late aggregate-gate failure, reproduce and repair the failing
  component first, then run at most one final aggregate certification on the
  unchanged final tree.

Worker reports are not acceptance evidence, but their command timings and
failure locations are valid scheduling evidence. Reuse caches and completed
exact-tree stages without pretending that this replaces independent semantic
reconstruction. Record commands skipped as redundant or disproportionate and
why their covered risk was already tested. Full local gate repetition is not a
proxy for rigor.

### Failure-Mode Feedback Loop

Every completed-worker audit must classify any miss before the coordinator
delegates the repair:

1. Name the failure precisely and identify the gap between the frozen claim and
   the checked proposition.
2. Decide whether it is an isolated implementation defect or a reusable ADD
   failure mode. Do not add process for a one-off typo or ordinary proof bug.
3. For a recurring or generalizable miss, patch the smallest durable layer that
   would have prevented it: completion gate, known-failure reference, matrix,
   worker prompt, audit packet, coordinator checklist, or claim-drift policy.
4. Log the workflow decision with trigger, alternatives, rationale,
   consequences, exact branch evidence, and publication-facing significance.
   Log a separate proof/code decision when the repair also chooses a theorem or
   representation abstraction.
5. Use the failed candidate as a named regression fixture and verify the new
   rule would reject its exact evidence pattern without rejecting legitimate
   weaker claims that are labeled accurately.
6. Only then engineer the next ambitious prompt set from the updated roadmap
   frontier.

Record the disposition as a compact table with the precise miss, isolated or
reusable classification, durable layer, decision-log entry, named regression,
verification result, owner, and status. If the audit contract forbids edits,
complete the classification but mark durable patching and regression
`PENDING`; any requested repair prompt is `DRAFT_DO_NOT_SEND`. A later
governance-edit turn must complete and verify the loop before the prompt may be
upgraded to `READY_TO_SEND`.

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

- prompt status (`READY_TO_SEND` or `DRAFT_DO_NOT_SEND`) and prompt-preflight
  result;
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

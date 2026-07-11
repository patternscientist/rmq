# Worker Prompt Template

Delete bracketed guidance before sending.

```text
Worker identity:
- Handle: [WORKER_HANDLE]
- Requested title: `([WORKER_HANDLE]) [SHORT_TASK_SUMMARY]`
- Fresh or returning worker: [FRESH / RETURNING, with reason]

Skill:
- Use $[SKILL_NAME] before starting.

Checkout contract:
- Task mode: [WRITE / READ-ONLY].
- Exact base/target commit: [BASE_BRANCH_OR_COMMIT].
- Durable disposition for material read-only work: [REPORT PATH / COORDINATOR
  SYNTHESIS TARGET].
- For a write task, create branch exactly [WORKER_BRANCH] in a fresh worktree
  and report its path.
- For a read-only task, inspect the exact commit without creating a branch;
  temporary detached worktrees are allowed, but source and docs stay unchanged.
- Fetch and verify the target before starting.
- Do not edit the coordinator checkout or overwrite unrelated work.

Roadmap contract:
- Node/join: [ROADMAP_NODE_AND_CONSUMER]
- Goal: [ONE SENTENCE EXACT TARGET]
- Required theorem/file/tool: [EXACT TARGET]
- Write scope: [PATHS]
- Non-goals: [BOUNDARIES]
- Explicitly deferred work: [ITEMS]. A deferred item is non-blocking only when
  it is not required for this target or its inherited invariants to be true.

Acceptance contract:
- Before editing, create a requirement-to-evidence matrix for every prompt
  requirement, the named consumer, every applicable inherited invariant, and
  every requested check. Name the intended theorem/check for each row.
- Read and apply
  .agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md.
- Preserve all applicable inherited invariants: counted-store provenance,
  result dependency on charged reads, execution-derived trace/footprint,
  supplied-store agreement, successful-read backing, machine-width words,
  machine-width addresses and operands, all assigned edge cases, and no hidden
  readiness/compatibility dispatch.
- For machine/layout work, audit actual footprint addresses against
  `2 ^ wordWidth`, including dead/sentinel addresses; array bounds are not
  enough.
- For execution work, trace the returned result backward to the charged reads;
  post-hoc replay or decorative reads do not count.

Forbidden shortcuts:
- No prose substitute for proof.
- No proof-only answers, uncounted payload, synthetic events, semantic routing
  oracles, or stale compatibility thresholds on the reviewer path.
- Keep payload bits, proof fields, model ticks, machine state, Lean runtime, and
  measured performance distinct.
- Do not stage transcripts, archives, scratch files, or unrelated changes.

Context:
- Read AGENTS.md and the assigned section of
  docs/internal/RMQ_FINAL_ROADMAP.md.
- Read the target modules and direct consumer.
- Read only relevant design-decision entries and task-specific docs.
- Read .agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md.
- Use .agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md only if
  the target touches those traps.

Completion:
- Work until the named target closes or a valid obstruction dossier forces a
  coordinator decision.
- A commit, push, green build, local helper, or honest caveat is a checkpoint,
  not completion. If your self-audit says a required property remains for the
  next consumer, continue on the same branch and add another commit.
- Exercise applicable edge cases in Lean: empty, singleton, size two,
  threshold minus one, threshold, and representative query shapes.
- Log real code/artifact decisions in DESIGN_DECISIONS.md and workflow changes
  in WORKFLOW_DESIGN_DECISIONS.md.
- Stage only intended files and commit unless explicitly read-only.

Verification:
- [TARGETED BUILD/CHECKS]
- git diff --check
- powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1
- powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1
  [only if public prose changed]

Report:
- handle/title, exact inspected commit, and, for write tasks, branch,
  worktree, base, and commit;
- changed files and exact theorem/definition names;
- conceptual meaning, plain-English meaning, live assumptions, and downstream
  consumer;
- skeptical-reviewer questions;
- decisions logged or why none were needed;
- exact command outcomes;
- completed requirement-to-evidence matrix;
- one status from COMPLETE / OBSTRUCTED / BLOCKED / INCOMPLETE;
- use COMPLETE only with the exact declaration: `No assigned or inherited
  acceptance criterion remains unmet.`;
- lifecycle disposition requested, durable report/synthesis disposition, and
  next crisp target.
```

Model recommendations are coordinator-to-user launch metadata. Name the exact
variant, reasoning level, and speed/service mode; do not put them in the worker
prompt.

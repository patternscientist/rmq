# Worker Prompt Template

Delete bracketed guidance before sending.

Coordinator launch metadata (do not paste into the worker prompt):

- Prompt status: [READY_TO_SEND / DRAFT_DO_NOT_SEND].
- Failure-mode feedback: [COMPLETE / PENDING / NOT_APPLICABLE].
- Semantic-contract review: [COMPLETE / PENDING]. This is an independent
  coordinator reread of the target, closure conditions, acceptance IDs, scope,
  forbidden shortcuts, verification, and report contract; preflight structure
  checks do not replace it.
- Destination task: [RETURNING_TASK / FRESH_GOVERNED_WORKTREE].
- Destination runtime evidence: [VERIFIED_CURRENT / GOVERNED_START / UNKNOWN /
  STALE]. A returning task requires an explicit current runtime inventory;
  repository skill files or a later branch switch are not runtime evidence.
- Worker handle, fresh/returning chat, exact model variant/reasoning/service
  mode, exact governance SHA, exact worker-base SHA, and branch.
- Run `scripts/worker_prompt_preflight.ps1` for every emitted prompt artifact
  and record its result. `READY_TO_SEND` requires a passing populated-template
  check. A read-only audit with pending durable feedback may emit only
  `DRAFT_DO_NOT_SEND`; if its contract forbids even a temporary prompt file,
  record `NOT_RUN` and do not grant launch authority.

```text
Make the title of this chat exactly: ([WORKER_HANDLE]) [SHORT_TASK_SUMMARY]

Worker identity:
- Handle: [WORKER_HANDLE]
- Requested title: `([WORKER_HANDLE]) [SHORT_TASK_SUMMARY]`
- Fresh or returning worker: [FRESH / RETURNING, with reason]

Skill:
- Use $[SKILL_NAME] before starting.
- Workflow-governance ref: [EXACT COMMIT CONTAINING CURRENT RMQ SKILLS/POLICY].
- Before substantive work, run `scripts/project_skill_preflight.ps1` against
  that ref with `[SKILL_NAME]` required and the RMQ skill names actually shown
  in the task's runtime available-skills catalog. If the script is absent, any
  canonical checkout skill is missing/stale, or any explicitly required role
  skill is missing from the runtime, stop and notify the user; do not substitute
  another skill or continue best-effort. Unrelated coordinator-side skills need
  not be injected into a proof-only worker. Restart from a governance-containing
  checkout unless the user explicitly authorizes a disclosed fallback.

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
- Local owned rung: [EXACT LOCAL DELIVERABLE]
- Roadmap-node closure condition: [WHAT MUST HOLD BEYOND THIS RUNG]
- This task closes: [LOCAL RUNG / ENTIRE ROADMAP NODE]
- Goal: [ONE SENTENCE EXACT TARGET]
- Required theorem/file/tool: [EXACT TARGET]
- Write scope: [PATHS]
- Write-scope closure: if the task may edit `scripts/gate.ps1`, include
  `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` in the same scope because the
  strict workflow-decision checker requires a durable process entry even for a
  comment-only gate edit.
- Current-surface inventory: [FOR EXHAUSTIVE LIVE/CURRENT PUBLIC-SURFACE TASKS,
  NAME `docs/internal/CLAIM_DRIFT_POLICY.json` `currentFactSurfacePathRegex`,
  REQUIRE EVERY MATCHED TRACKED PATH TO BE INSPECTED, AND PUT EVERY EXPECTED
  REPAIR PATH IN WRITE SCOPE; OTHERWISE NOT_APPLICABLE].
- Non-goals: [BOUNDARIES]
- Explicitly deferred work: [ITEMS]. A deferred item is non-blocking only when
  it is not required for this target or its inherited invariants to be true.

Acceptance contract:
- Frozen acceptance IDs: [REQ-01..., INV-..., CHK-...]. The coordinator has
  selected the applicable inherited IDs; you may add but may not remove or
  weaken them.
- Before editing, create the matrix using
  docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md. Copy each requirement
  verbatim. For every row, state the exact proposition/check needed, named
  consumer and identity/composition chain, and an anti-vacuity challenge to
  attempt for every applicable semantic subclaim. Before closing a row, record
  each outcome and which theorem rejects the challenged mutation.
- Read and apply
  .agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md.
- Preserve every coordinator-assigned inherited invariant.
- For machine/layout work, audit actual footprint addresses against
  `2 ^ wordWidth`, including dead/sentinel addresses; array bounds are not
  enough.
- For execution work, trace the returned result backward to the charged reads;
  post-hoc replay or decorative reads do not count.
- For returned-value or routing claims, require evidence about that value,
  state, or route. Inequality of an aggregate execution or trace record is not
  enough when only the log is forced to change. Match the evidence
  quantification and validity domain to the public claim; a singleton witness
  does not prove a universal dependency theorem.
- For semantic liveness, coverage, or ownership, expand the definitions and
  show which theorem fails if a dead source is added, a live source is removed,
  or a consumer label is assigned without an evaluator connection.
- For every semantic mutation, record the accepted predicate `P`, the rejected
  predicate `Q`, and their complete quantifier/domain assumptions. Use the same
  relation, or prove a checked `P -> Q` bridge. A stronger negative predicate
  does not test a weaker positive predicate.
- For trace provenance, state whether the theorem preserves event values,
  occurrence positions, multiplicity, or actual invocation parameters.
  `List.Mem` supports only event-value membership. Preserve position,
  instruction, folded pre-state, local occurrence, and computed invocation
  parameters whenever the requirement claims occurrence-level production.
- For a public theorem combining space/execution/model claims, prove each
  conjunct concerns the same payload, store, execution, and word model.
- If acceptance cites a mutation campaign, commit a replayable runner or stable
  fixtures for every claimed case, expected verdict/failing surface, expected-
  accept control, and restoration/clean-tree check. Report prose, terminal
  transcripts, and dangling Git objects are not acceptance evidence. For a
  public dependency, add an independent expected-type consumer and show that
  mutating the public proposition itself breaks the committed check; printing
  or checking the theorem's mutable current type does not pin it.
- `REPLAY-EXACT-REGISTRY`: a replay harness must declare the exact ordered
  frozen case registry, reject missing or duplicate IDs, verify any ID-to-field
  or ID-to-object mapping, and check exact verdict counts; a total pass count
  alone is insufficient.
- `REPLAY-SELECTOR-NONVACUITY`: focused selection must execute exactly one
  requested frozen ID and must reject unknown IDs. Add cheap named controls for
  an omitted middle ID, duplicated middle ID, valid frozen ID, and unknown ID.
- `REPLAY-SUBPROCESS-DEADLINE`: every external compiler/tool stage in a replay
  harness must have a positive evidence-based deadline, classify timeout as
  failure, terminate its owned process tree, and run cleanup plus live-tree
  integrity checks in `finally`. Add a cheap sleeper self-test; do not discover
  this control by hanging the full semantic campaign.
- If a public wrapper guards valid inputs, ensure every combined field uses the
  same guard/domain. Raw adequacy may occur only under the valid-range premise
  or in a guarded packet with matching invalid semantics; a bridge theorem does
  not justify leaving raw adequacy unconditional in the same public record.
  Test invalid, reversed, and out-of-bounds cases.
- For a whole physical-machine claim, cover every read-producing segment in one
  pre-execution word array and relate its query-independent width/capacity to
  input size. A component slice or unconstrained little-o width fact is not
  enough.
- For classifier/linter work, treat named mutation fixtures as lower bounds,
  not the acceptance boundary. Freeze the category being classified; add
  category-level holdouts and allowance-bypass mutations; and exercise the
  production final verdict, including strictness, path/line context, focused
  single-file input, and absolute-path normalization where supported. Do not
  validate a copied detector in place of the production classifier.

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
- An obstruction must negate the exact frozen target or give a checked
  implication from that target to `False` with matching objects, guards, and
  quantifiers. Do not join separate arbitrary-state, shape-growth, and one-
  witness reachability facts by prose; prove the canonical reachable family
  that carries them together. A failure of the current implementation or one
  proposed decomposition is a checkpoint unless it rules out every
  construction permitted by the frozen contract.
- A commit, push, green build, local helper, or honest caveat is a checkpoint,
  not completion. If your self-audit says a required property remains for the
  next consumer, continue on the same branch and add another commit.
- Do not self-classify a skeptical question as "strictly stronger", "future
  hardening", or "out of scope" after implementation. Map it to the frozen
  requirements and inherited IDs; only the coordinator may approve a contract
  amendment that narrows or defers a row.
- Exercise applicable edge cases in Lean: empty, singleton, size two,
  threshold minus one, threshold, and representative query shapes.
- Log real code/artifact decisions in DESIGN_DECISIONS.md and workflow changes
  in WORKFLOW_DESIGN_DECISIONS.md.
- Stage only intended files and commit unless explicitly read-only.

Verification:
- Development-loop checks: [NARROW CHECKS USED WHILE EDITING]
- Final-required checks: [ONLY CHECKS REQUIRED ON THE FINAL TREE]
- Conditional checks: [COMMAND, TRIGGER, AND WHY IT IS NOT UNCONDITIONAL]
- For each expensive command, record covered acceptance rows, closest observed
  runtime, chosen timeout, exact tree state, duration, and result. Run only one
  heavy Lean/Lake process at a time per build tree.
- If a command times out or stays quiet, inspect its child process, CPU/artifact
  progress, prerequisites, and whether it fell back to a full build. Do not
  launch the same expensive command unchanged. Retry only after recording the
  material change that makes the rerun meaningful.
- Run the aggregate gate at most once on an unchanged final tree. After a late
  failure, reproduce and repair the smallest failing component before the one
  final aggregate rerun. Do not separately duplicate checks already included
  by the aggregate gate unless the prompt names a distinct acceptance purpose.
- git diff --check
- after committing, git diff --check [EXACT BASE SHA]..HEAD
- powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1
- powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1
  [only if public prose changed]

Report:
- begin with exactly one status line. For candidate completion, the first two
  lines must be exactly `Status: CANDIDATE_COMPLETE` and `I found no assigned
  or inherited acceptance criterion unmet; coordinator acceptance is still
  required.` Do not substitute "closed", "complete", or "merge-ready";
- handle/title, exact inspected commit, and, for write tasks, branch,
  worktree, base, and commit;
- changed files and exact theorem/definition names;
- conceptual meaning, plain-English meaning, live assumptions, and downstream
  consumer;
- skeptical-reviewer questions;
- decisions logged or why none were needed;
- exact command outcomes;
- durable completed requirement-to-evidence matrix, including anti-vacuity
  challenges attempted and outcomes, positive/mutation predicate pairs and
  bridges, and the provenance information level retained by each theorem;
- quote checked theorem types or every hypothesis/conclusion for evidence;
  declaration names alone do not close matrix rows;
- one status from CANDIDATE_COMPLETE / OBSTRUCTED / BLOCKED / INCOMPLETE;
- lifecycle disposition requested, durable report/synthesis disposition, and
  next crisp target.
```

Model recommendations are coordinator-to-user launch metadata. Name the exact
variant, reasoning level, and speed/service mode; do not put them in the worker
prompt.

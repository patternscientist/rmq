# RMQ Codex Guidance

## Project Skill Preflight

- The canonical RMQ project skills are the `SKILL.md` packages tracked under
  `.agents/skills` at the task's declared workflow-governance frontier. Before
  substantive repository work, confirm that the checkout contains the complete
  canonical set, identify the applicable role skill or skills, and confirm that
  those explicitly required skills are present in the task's runtime catalog.
  A role-specific task does not need unrelated coordinator-side skills injected
  into its runtime.
- Use `$rmq-coordinator` for coordination, re-entry, completed-worker audit,
  integration, roadmap planning, and handoff work; `$rmq-proof-sprint` for
  narrow Lean/proof/construction work; and `$rmq-audit-prompt` for preparing
  external audit prompts and evidence packets. `$rmq-audit-prompt` is a
  coordinator-side authoring skill, not an audit-worker skill. Audit workers
  follow their frozen prompt and `docs/internal/AUDIT_PROTOCOL.md`.
- When an exact governance ref is supplied, run
  `scripts/project_skill_preflight.ps1` with that ref, the applicable skill,
  and the RMQ skill names shown in the task's runtime catalog. Keep the
  governance checkout separate from any older source commit being audited.
  For example:

  ```powershell
  powershell -ExecutionPolicy Bypass -File scripts\project_skill_preflight.ps1 `
    -GovernanceRef <EXACT_SHA> `
    -RequiredSkills rmq-coordinator `
    -RuntimeProjectSkills "rmq-coordinator"
  ```

  Replace the runtime list with the RMQ skills actually exposed to the task; do
  not copy the expected list merely to make the check pass.
- If the script is absent, a canonical skill is missing or stale in the
  checkout, the runtime catalog omits an explicitly required role skill, or the
  governance ref is not in the checkout's ancestry, **stop before substantive
  work**. Report the working directory, checkout HEAD, governance ref, expected
  project skills, runtime project skills, and missing/stale names. Do not
  substitute another skill or continue best-effort.
- Resume only in a new or restarted task rooted at a checkout containing the
  governing workflow commit and exposing every explicitly required role skill,
  unless the user explicitly authorizes a fallback after the mismatch is
  disclosed. A fallback run cannot record coordinator acceptance, integration,
  or roadmap closure.

## Repository Expectations

- Treat this repository as a Mathlib-free Lean 4 project pinned by
  `lean-toolchain`; preserve the Lean/Std plus `omega` footprint unless the
  user explicitly decides otherwise.
- Use the existing half-open RMQ contract, leftmost tie policy, and value-level
  `List Int` semantics as the reference layer. Add representation refinements
  as adapters/refinements instead of rewriting the reference theory.
- Keep proof changes scoped. Prefer strengthening existing modules and theorem
  interfaces over creating parallel APIs.
- When changing public theorem surfaces or headline claims, update
  `docs/FAMILY_SUMMARY.md` and, when relevant, `README.md`.
- Preserve the distinction between payload bits, proof-only fields, model-level
  cost ticks, and executable Lean runtime behavior.
- For audits, follow `docs/internal/AUDIT_PROTOCOL.md`.
- When a branch makes or changes a nontrivial design decision, update
  `docs/internal/DESIGN_DECISIONS.md` or report why no update was needed.
- When a branch makes or changes a nontrivial ADD/process decision, update
  `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` or report why no update was
  needed.
- Write design-decision entries with enough rationale, rejected alternatives,
  consequences, and evidence for future paper exposition, not merely as terse
  change logs.

## Verification

- Plan verification from changed paths and acceptance rows. During development,
  run the narrowest affected target and direct consumer first. Reserve full
  `lake build` and `scripts/gate.ps1` for broad/integration/public-capstone
  changes or an explicit final contract; narrow proof, docs-only, and read-only
  work should use proportionate checks and record why broad gates were skipped.
- Run only one heavy Lean/Lake process at a time per build tree. For a
  multi-minute command, choose a timeout from observed runtimes with cold-cache
  margin. After a timeout, inspect surviving child processes, artifact progress,
  missing prerequisites, and accidental full-build fallback before retrying.
  Never rerun the same expensive command unchanged merely because its wrapper
  timed out or remained quiet.
- Run an aggregate gate at most once on an unchanged final tree. Diagnose a
  late failure with the smallest failing component, then reserve the next full
  run for final certification.
- Run this hygiene scan before finalizing:

  ```powershell
  rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
  ```

- For changes touching old smoke examples or proof trust-base claims, also run:

  ```powershell
  rg -n "native_decide|Lean\.ofReduceBool" RMQ
  ```

- Use `git diff --check` before finalizing file edits.

## Current Research Direction

- Highest-value parity gap: a real succinct upper-bound story, eventually
  approaching `2n + o(n)` payload bits with constant-time query under an
  explicit RAM/indexed-access model.
- Highest-value novelty: pair the existing `2n - O(log n)` lower-bound
  framework with a payload-accounted upper-bound construction.
- Near-term RMQ strategy: separate total positive directory geometry from
  optional compact-storage readiness, then prove one uniform all-size route and
  cost theorem before further executable/machine refinement.
- Current RMQ paper-hardening strategy: use
  `docs/internal/RMQ_FINAL_ROADMAP.md` as the delegation ladder and
  `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md` for process/tooling prerequisites
  before starting new broad roadmap work. Track delegated branches through
  retirement with `docs/internal/WORKER_LIFECYCLE.md`.

## Subagent Policy

- For substantial proof/development work, default to a quick parallelization
  check before editing: identify the join theorem or concrete target, the
  independent leaves that feed it, and the work the lead thread will do while
  agents run.
- Use subagents when they materially shorten the path to the current target.
  Avoid ceremonial parallelism: if there is no independent leaf with a clear
  consumer, proceed single-threaded and say why.
- Prefer read-only subagents for independent proof audits, theorem inventory
  checks, literature/source comparisons, and risk reviews.
- Use worker subagents for disjoint write scopes with pinned theorem
  signatures or construction contracts. Tell them they are not alone in the
  codebase, must not revert or overwrite other changes, and should continue
  through their loop until the assigned target closes or a real stop condition
  is met.
- Worker prompts for ambitious proof targets should name the actual target that
  must close. Do not offer an easier alternate endpoint as a valid completion
  route. A fallback target is acceptable only after the worker proves the
  original target impossible or mis-specified by a precise formal obstruction.
- Do not treat "avoid overclaiming" as a stop condition. Every report must be
  honest, but if the assigned target is not yet true and the next local
  proof/construction step is available, keep working instead of stopping at a
  clean partial checkpoint.
- For nontrivial proof, representation, store, trace, or cost-model work,
  workers must apply
  `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`. A commit,
  push, green build, or candid remaining-risk note is a checkpoint, not target
  closure. Freeze verbatim requirements and stable acceptance IDs before
  editing. Evidence rows must quote exact propositions and object-composition
  chains; theorem names alone do not close them. Workers may report only
  `CANDIDATE_COMPLETE`; the coordinator records `ACCEPTED` after independent
  reconstruction and any mandatory blind exact-commit audit.
- Every worker completion report must include a short proof-digestion section:
  what changed conceptually, what the work just done now means in plain
  English, what assumptions are live, and what a skeptical grad student would
  ask next.
- When completion relies on a mutation campaign, require committed replayable
  cases with expected verdicts, exact failing surfaces, expected-accept
  controls, and restoration/clean-tree checks. Report-only experiments,
  terminal transcripts, and unreferenced Git objects do not close acceptance
  rows. Public-dependency claims also require a checked expected-type consumer
  that fails when the public proposition is mutated.
- The lead thread remains responsible for periodic check-ins, steering agents
  away from premature loop breaks or side quests, integrating accepted work, and
  running the final gate. For public-facing milestones, it should also fold
  the worker's digestion note into `docs/DIGESTION_LOG.md` or a focused digest.
- When the user explicitly opts into automated worker chaining, use the
  `rmq-coordinator` audited completion loop: launch only preflighted
  `READY_TO_SEND` prompts in fresh governed Codex tasks, register one logical
  completion-monitor record per task (multiplexed in one heartbeat when the app
  permits only one), independently audit exact commits, complete reusable
  failure-mode feedback, and attach monitors to any automatically launched
  successors. Do not use that opt-in to infer authority to merge, push, delete
  branches/worktrees, or launch around unresolved dependencies or architecture
  choices.

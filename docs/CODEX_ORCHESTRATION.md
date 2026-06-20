# Codex Orchestration For RMQ

This note records the free Codex-native workflow tools that fit the RMQ
formalization work.

## What We Added

- `AGENTS.md`: durable repository guidance for future Codex sessions.
- `.agents/skills/rmq-proof-sprint/SKILL.md`: a repo-local workflow skill for
  RMQ proof, cost, space, succinct, and LCA tasks.
- `.codex/agents/rmq-proof-auditor.toml`: read-only custom subagent profile for
  audits.
- `.codex/agents/rmq-frontier-explorer.toml`: read-only custom subagent profile
  for milestone planning.

These are local/repo-scoped and do not require paid external services.
`AGENTS.md` and custom agents are picked up by new Codex runs; repo skills may
also require a restart if they do not appear immediately.

## Recommended Use

- Normal theorem implementation: use the main thread plus the
  `rmq-proof-sprint` skill.
- Bounded proof loops: use the main thread as coordinator, with substantial
  milestones chosen adaptively at each checkpoint. A loop should accomplish
  more than a normal single-prompt proof step without splitting tiny lemmas into
  artificial milestones.
- Before a large milestone: explicitly ask to spawn read-only subagents, for
  example:

  ```text
  Spawn two read-only subagents: rmq-proof-auditor checks current theorem
  statements and trust-base risks; rmq-frontier-explorer proposes the next
  three proof milestones. Wait for both and synthesize.
  ```

- During implementation: use subagents only for independent read-heavy audits
  or disjoint write scopes. Keep the main thread responsible for final
  integration and verification.
- For multi-chat branches, use `docs/WORKER_INTEGRATION_CHECKLIST.md` as the
  worker report template and coordinator merge gate.

## Bounded Proof Loop Template

1. Choose the next substantial milestone from the current family summary.
2. Spawn two or three read-only scouts for independent risks: API inventory,
   proof/off-by-one risks, and cost/model/documentation consistency.
3. Implement the smallest coherent slice locally while scouts run.
4. Integrate scout findings without broadening the milestone.
5. Iterate on `lake env lean <touched module>` failures with a small retry cap.
6. If the proof wants a new abstraction, the API choice is taste-sensitive, or
   the same blocker repeats, stop and report the blocker instead of churning.
7. Run a checkpoint: touched-module checks, then `lake build`, the trust-base
   scan, the `native_decide` scan when relevant, and `git diff --check`.
8. Update `docs/FAMILY_SUMMARY.md`.
9. If the checkpoint is clean and no stop condition fired, choose the next
   substantial milestone adaptively and repeat the loop. Otherwise report the
   checkpoint and blocker.

Default loop size: multiple meaningful milestone iterations, not one iteration
by default and not several tiny lemmas relabeled as milestones. Keep the user in
the loop at each checkpoint so the frontier can be redirected before proof churn
sets in.

## Features Not Adopted Yet

- Hooks: useful later for automatic `lake build` or hygiene scans, but they
  require hook trust/review and can become noisy during proof exploration.
- Plugins: useful if this RMQ workflow should be distributed outside this repo.
  A repo skill is simpler while the workflow is still evolving.
- `codex exec`: useful for CI-style scripted audits, but interactive proof work
  is still better in the app/thread until the checks stabilize.
- External autonomous agents such as Manus: unnecessary for the current Lean
  proof workflow and not the best free/default choice.

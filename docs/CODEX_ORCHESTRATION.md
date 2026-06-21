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
- Bounded proof loops: use the main thread as coordinator, with an ambitious
  owned target chosen adaptively at each checkpoint. A loop should try to close
  that target overall. Substantial proof steps are iteration results inside the
  loop, not automatic loop endpoints.
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

1. Choose the next ambitious target from the current family summary: the
   concrete component profile or capstone theorem to close, not merely the next
   helper layer.
2. Write the iteration goal reflection:
   - Overall goal: the capstone theorem or concrete component profile.
   - Current gap: what blocks it now.
   - Hard part: the proof/construction most tempting to postpone.
   - This iteration: the largest coherent step toward that hard part.
   - Not doing: adjacent outputs that would look useful but leave the gap.
3. Spawn two or three read-only scouts for independent risks: API inventory,
   proof/off-by-one risks, and cost/model/documentation consistency.
4. Implement the smallest coherent slice locally while scouts run.
5. Integrate scout findings without broadening the milestone.
6. Iterate on `lake env lean <touched module>` failures. A single tactic or
   proof-shape retry can have a small cap, but an obvious repaired statement,
   helper lemma, or construction variant starts the next iteration rather than
   ending the loop.
7. If the proof wants a new abstraction or the API choice is taste-sensitive,
   stop and report the design choice. Failed construction attempts by
   themselves are not enough to stop; continue through repaired statements and
   nearby construction variants unless a formal impossibility theorem shows the
   target is mis-specified, or an extreme dossier records at least fifty serious
   attempts failing for the same design-level reason. Repeating a known blocker
   or landing one useful partial theorem is not itself a loop endpoint.
8. Run a checkpoint: touched-module checks, then `lake build`, the trust-base
   scan, the `native_decide` scan when relevant, and `git diff --check`.
9. Update `docs/FAMILY_SUMMARY.md`.
10. If the checkpoint is clean and no strict stop condition fired, choose the
   next iteration adaptively and repeat the loop against the same owned target.
   Otherwise report the checkpoint and the exact stop condition.

Default loop size: enough meaningful iterations to close the owned target, or
to demonstrate that closing it now requires a fundamental design choice. A loop
should not stop just because it has produced one or two substantial steps in
the right direction. Keep the user in the loop only at strict stop points so the
frontier can be redirected before real design churn sets in.

The reflection is a guard against polished procrastination. If the best next
step is a difficult payload-live construction, a loop should not spend its
iteration on extra wrappers, docs, or negative variants unless those artifacts
are immediately consumed by that construction or prove the target signature
itself must change.

When reporting a short-of-target stop, include the brick-wall dossier: signatures
tried, the common obstruction, why obvious local repairs do not suffice, and
which design choice the coordinator must make. Failed constructions justify a
stop only after the fifty-attempt exhaustion standard above; a formal
impossibility theorem for the target statement can replace that threshold.

## Features Not Adopted Yet

- Hooks: useful later for automatic `lake build` or hygiene scans, but they
  require hook trust/review and can become noisy during proof exploration.
- Plugins: useful if this RMQ workflow should be distributed outside this repo.
  A repo skill is simpler while the workflow is still evolving.
- `codex exec`: useful for CI-style scripted audits, but interactive proof work
  is still better in the app/thread until the checks stabilize.
- External autonomous agents such as Manus: unnecessary for the current Lean
  proof workflow and not the best free/default choice.

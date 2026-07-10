# Codex Autonomy And Anti-Filler Policy

This is concise coordinator guidance. Normative proof-worker behavior lives in
`.agents/skills/rmq-proof-sprint/SKILL.md`; the active target lives in
`RMQ_FINAL_ROADMAP.md`.

## Objective Gate

A branch needs both proof integrity and target integrity. The first is checked
by builds, hygiene, axiom checks, and diffs. The second requires the named
construction to be consumed by its declared join without hidden cost, payload,
or oracle assumptions. A green gate is necessary and not sufficient.

## Autonomous Loop

Within the assigned branch, a worker should:

1. restate the target and consumer;
2. prove the smallest blocking lemma;
3. consume it;
4. run the narrow check;
5. inspect whether the named target is actually closed;
6. repeat while the next step is local and inside scope.

The worker must not stop merely because the branch is honest about being
partial.

## Valid Stops

- the named target closes;
- a minimal formal obstruction shows the target signature is wrong;
- materially distinct construction families fail for one structural reason and
  an obstruction dossier identifies the coordinator-level design choice;
- an external dependency, approval, or branch conflict blocks progress;
- the user redirects.

There is no fixed attempt count. Evidence quality, not repetition, justifies an
obstruction stop.

## Anti-Filler Rules

- Every branch feeds the active roadmap join.
- Helpers must be consumed by the target.
- New interfaces name their concrete instance.
- Cost follows charged operations; space follows payload actually read.
- Superseded routes are retired or quarantined when the replacement is stable.
- Public theorem names do not outrun their statements.
- Design choices are logged with alternatives and consequences.

## Parallelism And Handoff

Parallelize only independent leaves with disjoint ownership and a named join.
Read-only audit, dependency, and validation leaves are preferred. Shared
records, public signatures, and causally ordered abstractions have one owner.

The worker commits a narrow branch and reports exact evidence. The coordinator
audits, integrates/ports/rejects, updates the roadmap and lifecycle state, and
engineers the next prompt set.

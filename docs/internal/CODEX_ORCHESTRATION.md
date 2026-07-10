# Codex Orchestration

This document describes the coordinator/worker split. Detailed proof behavior
is owned by `rmq-proof-sprint`; audit behavior is owned by
`AUDIT_PROTOCOL.md`.

## Coordinator Responsibilities

- reconstruct the exact frontier from git and source;
- name one active roadmap join;
- identify independent leaves and assign disjoint ownership;
- prescribe worker handle, title, base, branch, worktree, skill, and target;
- give model/mode and fresh-vs-returning recommendations outside the prompt;
- monitor context health and hand off before stale chat assumptions dominate;
- audit worker output in source, not by report alone;
- integrate, port, reject, and retire branches/worktrees;
- update the roadmap and engineer the next ambitious prompt set.

## Worker Responsibilities

- use the assigned skill and branch contract;
- remain inside write scope;
- close the named target or produce a valid obstruction dossier;
- preserve cost/payload/trust fidelity;
- log real design decisions;
- run required checks;
- commit and report exact evidence.

## Parallelism

Before launching, state the join, each independent leaf and consumer, shared
interfaces with one owner, integration order, and coordinator work while
workers run. Avoid parallel implementation of causally ordered interfaces.
Prefer parallel read-only scouts when the architecture is not settled.

## Audit Cycle

Every submitted branch receives:

1. diff and freshness audit;
2. theorem/implementation and design-intent audit;
3. verification review;
4. design-decision review;
5. integrate/port/reject verdict;
6. roadmap and lifecycle update;
7. next prompt engineering.

External audits follow `AUDIT_PROTOCOL.md`: fresh blind for independent gates,
continuation for one correction loop, and longitudinal review for accumulated
architecture.

## Context Health

Use the coordinator re-entry and handoff templates. Handoff is routine when the
frontier cannot be restated from source concisely, prior reports dominate the
context, or the coordinator repeatedly rechecks facts it should pin in a
digest. A new coordinator reads source and exact commits; private reasoning is
not authority.

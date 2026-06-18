# Codex Autonomy & Anti-Filler Policy

Companion to `CODEX_ORCHESTRATION.md`. Fold this in or keep it adjacent. It
covers three things the base orchestration note does not yet: how to run the
loop with far fewer human checkpoints, how to stop the loop from producing
filler, and how to parallelize without make-work.

## The core principle

This is a Lean project, so "sound and complete" is largely machine-decidable:
`lake build` + a hygiene scan + a curated `#print axioms` check. That objective
signal is what buys autonomy -- encode the human's "yea, keep going" into a gate
the loop consults itself (`scripts/gate.ps1`).

But heed the failure mode this repo has actually exhibited: **across several
review rounds, every round passed the gate (green build, minimal trust base) and
yet several were filler** -- more model-level `_value/_erase/_cost/_run`
wrappers, new backends, and abstraction layers on the asserted-cost foundation,
instead of the hard target. So:

> A green gate proves soundness and non-regression. It does **not** prove the
> round moved the needle. The gate is necessary, not sufficient. Filler is
> almost always gate-green.

Two mechanisms therefore run together: the **gate** (soundness) and the
**roadmap contract** (value). Neither alone is enough.

## Autonomous loop

Driver (a shell loop around non-interactive Codex runs):

```text
while scripts/gate.ps1 ; do
  codex exec "Advance the next docs/ROADMAP.md target per docs/CODEX_AUTONOMY.md.
              Continue across targets while the gate stays green.
              Stop only on a stop condition below."
done
```

Change the base loop template's checkpoint rule from "keep the user in the loop
at each checkpoint" to:

> If the gate is green and a roadmap target remains, continue autonomously to
> the next target. Do not return to the human between green rounds.

A single run should discharge **one full roadmap target end to end**, and may
chain into the next target if the gate stays green and budget remains -- not one
tiny lemma, and not several tiny lemmas relabeled as a milestone.

### Stop conditions (the only reasons to surface to the human)

1. Gate red after one retry.
2. A change to a public contract (`RMQBackend`, `LeftmostArgMin`,
   `ExactRMQStateEncoding`, the LCA/RMQ bridge types) -- taste-sensitive.
3. A target needs a policy break (add Mathlib, admit an axiom, drop the
   plus-minus-one invariant, change the cost convention).
4. The same blocker recurs, or a target turns out mis-specified / unprovable as
   stated.
5. A genuinely taste-sensitive API/abstraction fork with no clear winner.
6. Roadmap exhausted.

Anything else: keep going.

## Anti-filler rules

1. **Work only from `docs/ROADMAP.md`.** A definition or theorem not traceable
   to the active target is scope creep -- do not add it.
2. **A target is "done" only when its pre-registered statement is proved** (the
   exact theorem shape in the roadmap typechecks, `sorry`-free). Filler cannot
   satisfy a hard, pre-committed signature.
3. **No new breadth unless the active target requires it.** No new RMQ backend,
   no new `_value/_erase/_cost/_run` quadruple, no new abstraction layer, unless
   discharging the current target is impossible without it. (This single rule
   would have prevented the filler rounds.)
4. **Debt must fall or a target must close.** Each round's report must show one
   of:
   - a roadmap target newly proved, or
   - a tracked debt metric strictly decreased.

   Debt metrics (automatable proxies):
   - `rg -c "tickValue|indexedReadCost|materializedMicrotableLookupCost" RMQ`
     -- count of *asserted* (vs. derived) cost charges; should trend down.
   - count of theorems gated on uncosted hypotheses -- adopt a naming
     convention (`_of_supplied`, `_of_firstOccurrences`, ...) and grep it; the
     goal is converting these into unconditional versions.
5. **The "so what" check.** Each closed target names one theorem a researcher
   would cite. If the report cannot point to one, the round was filler -- redo
   it.

## Parallelization policy

The rule that separates acceleration from make-work:

> A parallel task is legitimate **iff** its output is consumed by the current
> target's join theorem. If deleting the task would not block the join, it is
> filler -- do not spawn it.

So: **parallelize the decomposition of one target, never across unrelated
targets for throughput.** A lead pass decomposes the active target into
independent sub-lemmas that all feed one join theorem, spawns a worker per
independent leaf, and does the join itself.

- Good: the cost-model target's leaves -- `Array`/`List` refinement,
  instrumented primitive library, operational step semantics -- run in parallel,
  then the join proves `ticks = steps` and re-founds one algorithm on the
  substrate. All three are prerequisites of the same headline theorem.
- Bad: "worker 1 adds a Treap, worker 2 adds van Emde Boas, worker 3 polishes
  docs." Independent, parallel, and worthless to the goal.

Mechanics:
- Each write-worker gets its **own git worktree/branch** with disjoint file
  ownership; tell workers not to revert or overwrite other agents' work. The
  lead merges at the join.
- Read-only scouts (`rmq-proof-auditor`, `rmq-frontier-explorer`) may be many
  and cheap. Write-workers should be few and DAG-bound.

## Iteration report template

```text
Target:        <roadmap id + name>
Discharged:    <theorem name(s) that now typecheck>  | or: "in progress, leaf X"
Headline:      <the one citable theorem this produced>     (so-what check)
Debt delta:    asserted-cost count A -> B ; gated-hypothesis count C -> D
Gate:          PASS  (build / hygiene / axioms / diff)
Parallelism:   <leaves spawned and the join they fed, or "none">
Next:          <next roadmap target, or stop condition hit>
```

If "Headline" and "Debt delta" cannot both be filled, the round did not earn a
green light regardless of the gate.

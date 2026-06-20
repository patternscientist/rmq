# Codex Autonomy & Anti-Filler Policy

Companion to `CODEX_ORCHESTRATION.md`. Fold this in or keep it adjacent. It
covers three things the base orchestration note does not yet: how to run the
loop with far fewer human checkpoints, how to stop the loop from producing
filler, and how to parallelize without make-work.

**Before running the loop, read `docs/ROADMAP.md` → "Mission and positioning"**
for the big-picture goal (RMQ as the research-grade, CSLib-compatible,
gap-filling proof of concept for a hub-and-spoke library) and the A–D finish
line the loop is driving toward.

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

**Three** mechanisms therefore run together: the **gate** (soundness), the
**roadmap contract** (value), and an independent **adversarial audit**
(fidelity — see next section). None alone is enough.

## What the gate cannot see: cost-fidelity (the recurring blind spot)

The gate checks `lake build` + a hygiene scan + a curated `#print axioms`. It is
structurally **blind to whether a cost/complexity/space claim is real** —
`Costed.tickValue 1 (anExpensiveThing)` is perfectly sound and standard-axioms
clean. *Every* cost-fiction round in this project's history was gate-green. The
gate cannot tell:

- whether a cost is **derived** (a count of executed primitive ops) or
  **asserted** (`tickValue <const>` / a `:= 1` field);
- whether the returned **value is computed by the counted ops**, or computed
  separately in pure Lean (`Costed.pure`/`.map`) with a cost charged alongside;
- whether a **space** count (`payload.length = overhead`) is the structure the
  query *reads*, or a decoupled accounting field tied to it only by an arbitrary
  decoder;
- whether a `…_profile` headline has a **concrete instance**, or is an abstract
  conditional with no witness;
- whether a unit-cost "word op" is over a genuine **Θ(log n) machine word** or a
  super-word.

So treat green as "not unsound," never "faithful." Cost-fidelity is the audit's
job, plus the lints below.

### A cost/complexity/space claim is genuine only if ALL of:

1. **Derived, not asserted.** Cost = trace length / sum of primitive-op costs
   (`RAM.Exec` or equivalent), not a handwritten `tickValue`/constant field.
2. **Value flows through the ops.** The returned value is computed *by* the
   counted primitives — not produced in pure Lean and wrapped with a cost.
   (`Exec.primitive op x` with arbitrary `x` is the escape hatch; typed
   value-computing primitives close it.)
3. **Faithful primitives.** Unit cost only for a genuine single-machine-word /
   single-indexed-read op. Prefix-rank / scans are not O(1); a word op is O(1)
   only when the word is Θ(log n) bits — and that bound must be **concretely
   instantiated**, not a free parameter.
4. **Witnessed.** A family/profile is "done" only when a **concrete instance**
   exists (`def … : …Family`), not "for any structure with these fields." An
   abstract conditional with no witness is not a result.
5. **Space genuinely counted.** An o(n) / 2n+o(n) claim counts the structure the
   query actually reads, via a proven injective codec (e.g. `natToBitsLE` with a
   roundtrip) — not a parallel `encodeAux`/payload bound joined by an arbitrary
   decoder.
6. **Predecessors retired.** When a faithful version supersedes an unfaithful
   one, **delete** the old def + theorems *in the same round*. Removing it from
   `axiom_check` only ("delist") is not retiring — the fiction stays in source.

### Anti-pattern catalog (each was caught here; each was gate-green)

- **Asserted cost** — `tickValue <const>` / `:= 1` on an aggregate op.
- **Value/trace decoupling** — value in pure Lean, small cost charged; or
  `primitive op x` smuggling a heavy value.
- **Decoupled space accounting** — counted `payload` ≠ the (larger) structure
  the query reads; arbitrary `decode` fields.
- **Abstract-no-witness** — `…_profile` over a hypothesized family with no
  `def : …Family`.
- **Modeled-O(1)-for-O(n)** — unit cost over a super-machine-word; o(n) without a
  two-level directory.
- **Delist-don't-retire** — unfaithful theorem dropped from `axiom_check` but
  left in source.
- **Component-deepening** — hardening sub-components round after round without
  advancing the target's load-bearing close.

### Gate enhancements to add (catch the catchable subset)

- Lint: `tickValue` / literal `:= 1` cost on a non-single-read op in
  cost-bearing modules.
- Lint: a `…_profile` whose family type has **no** `def : …Family` instance
  (abstract-no-witness).
- Lint: a name dropped from `axiom_check` that still resolves and is
  unused/superseded (delist-without-delete).

The uncatchable remainder (value-flow, faithful-primitive, genuine-space) stays
the audit's job.

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
6. **A claim with no concrete witness is not done.** An abstract `…_profile`
   over a hypothesized family does not count until a `def … : …Family`
   instantiates it (see fidelity criterion 4).
7. **Retire in the same round.** If this round supersedes an unfaithful/old def,
   delete it now -- do not leave it behind or merely delist it from
   `axiom_check`.
8. **Never stop with unwired scaffolding.** A structure built but not connected
   to a live path (no consumer, no retired predecessor, no capstone) is a
   stop-rule violation, not a checkpoint -- it closes no target and leaves dead
   code.

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

### Proof workers are first-class, not just read-only scouts

In autonomous-loop mode the lead **should proactively spawn parallel *proof*
(write) workers** whenever the active target decomposes into ≥2 independent
leaves — do not wait to be asked, and do not restrict subagents to read-only
audits. This **overrides** the conservative "read-only only / spawn only on
explicit request" defaults in `AGENTS.md` and the `rmq-proof-sprint` skill,
which apply to ordinary single-prompt work, not to a running loop.

Proof-worker protocol (the lead runs this):
1. **Decompose, then write contracts first.** State the target's join theorem
   and, for each independent leaf, the exact lemma signature the worker must
   discharge (`theorem leafₖ : … := by sorry` as a contract stub the worker
   replaces). The signatures are the interface; workers must not change them.
2. **One worker per leaf, isolated.** Each write-worker gets its own git
   worktree/branch and **disjoint file ownership** (ideally one module per
   worker); tell it not to revert or touch other workers' files, and to prove
   its assigned signature exactly.
3. **Join.** The lead assembles the leaves into the join theorem and runs the
   gate. A leaf that turns out taste-sensitive or contract-forky is a **stop**
   (surface it), not a worker task — only dispatch leaves whose contract is
   already pinned.

Mechanics:
- Read-only scouts (`rmq-proof-auditor`, `rmq-frontier-explorer`) may be many
  and cheap. **Write/proof workers should be few, DAG-bound, and each gated by a
  pinned lemma signature** — that signature is what keeps a proof worker from
  drifting into filler.

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

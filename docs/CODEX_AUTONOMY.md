# Codex Autonomy and Anti-Filler Policy

Companion to `CODEX_ORCHESTRATION.md`. This note says how to run longer proof
loops, how to avoid gate-green filler, and how to parallelize without making
extra work.

Before running a loop, read `docs/ROADMAP.md`, especially "Mission and
positioning" and the A-D finish line. The loop is driving RMQ toward a
research-grade, CSLib-compatible proof of concept for a hub-and-spoke advanced
data-structure library.

## Core Principle

This is a Lean project, so "sound and complete" is largely machine-checkable:
`lake build`, a hygiene scan, and curated `#print axioms` checks. That objective
gate buys autonomy.

But this repo has already shown the failure mode: a round can pass the gate and
still be filler. More `_value/_erase/_cost/_run` wrappers, new breadth backends,
or abstraction layers on top of asserted costs can all be sound while failing to
move the project forward.

So three mechanisms run together:

- The gate checks soundness and non-regression.
- The roadmap contract checks value.
- A cost/space-fidelity audit checks whether complexity claims are actually
  backed by the counted representation and operations they cite.

A green gate is necessary, not sufficient.

## What The Gate Cannot See

The gate checks build, hygiene, and curated axiom dependence. It is structurally
blind to whether a cost, query-time, or space claim is faithful. For example,
`Costed.tickValue 1 expensiveValue` can be perfectly sound and axiom-clean while
claiming one step for work that was done off-trace.

The gate cannot tell by itself:

- whether a cost is derived from primitive operations or asserted as a literal
  tick;
- whether the returned value is computed by counted operations or produced by
  pure Lean and wrapped with a cost;
- whether a charged payload is the structure the query actually reads, or a
  separate accounting field tied to a larger proof-side object;
- whether a `..._profile` theorem has a concrete instance, or is only an
  abstract conditional over a hypothetical family;
- whether a unit-cost word operation is applied to a machine-sized word rather
  than a super-word.

A cost, query-time, or space claim counts as genuine only when all of the
following hold:

1. The cost is derived from trace length or primitive-operation costs, not a
   handwritten aggregate tick.
2. The value flows through the counted operations. Typed value-computing
   primitives are good; arbitrary value slots beside trace entries are not.
3. Unit-cost primitives are faithful to the model: one indexed read, one branch,
   one comparison, or one operation over a concretely machine-bounded word.
4. The theorem is witnessed by a concrete construction or family instance, not
   just an abstract interface theorem.
5. The charged space is the payload the encoded query reads, with decoder or
   exact-read proofs tying bits to the semantic entries.
6. Superseded unfaithful paths are retired in the same round, not merely removed
   from the axiom inventory.

Recurring anti-patterns:

- Asserted aggregate costs such as `tickValue` around non-primitive work.
- Value/trace decoupling, where the result is computed separately from the
  counted trace.
- Decoupled space accounting, where the query reads proof-side data larger than
  the charged payload.
- Abstract-no-witness results: a headline profile over a hypothesized family
  with no concrete `def : ...Family`.
- Modeled O(1) for O(n) work, especially word operations over unbounded words or
  unit reads from structures backed by scans.
- Delist-don't-retire, where an obsolete theorem is dropped from
  `axiom_check` but left in source.
- Component-deepening, where subcomponents are hardened repeatedly without
  advancing the target's load-bearing join theorem.

Useful lint ideas for the catchable subset:

```powershell
rg -n "tickValue|:= 1|indexedReadCost" RMQ
rg -n "_profile" RMQ
```

The lints are only prompts for review. Value-flow, faithful-primitive, and
genuine-space questions still require adversarial reading.

## Loop Modes

### Attended Loop

Use this when the user wants to stay in the loop. It should still be a loop, not
a one-lemma checkpoint. Work through a substantial roadmap slice, run the gate,
report the result, and name the next target. Do not report after every tiny
proof leaf unless a stop condition occurs.

### Unattended Loop

Use this only when the user explicitly requests unattended continuation. The
driver can be a shell loop around non-interactive Codex runs:

```text
while scripts/gate.ps1 ; do
  codex exec "Advance the next docs/ROADMAP.md target per docs/CODEX_AUTONOMY.md.
              Continue across targets while the gate stays green.
              Stop only on a stop condition below."
done
```

In unattended mode, change the checkpoint rule to:

> If the gate is green and a roadmap target remains, continue autonomously to
> the next target. Do not return to the human between green rounds.

A single run should aim to discharge one full roadmap target end to end, and may
chain into the next target if the gate stays green and budget remains. Do not
split what should be one milestone into several small "wins" just to claim more
iterations.

Before stopping an unattended loop, run a stop audit:

1. Did this round prove the named roadmap theorem or retire the named blocker?
2. Is the next theorem or construction suggested by the diff obvious and still
   within the current branch's owned files?
3. Did the round introduce an API hook, parameter, abstract family, or canonical
   identity witness while the concrete compact/payload-live witness remains
   exactly the missing item?

If 1 is no and either 2 or 3 is yes, the loop should continue. "The gate is
green" only proves soundness; it does not prove that a worker has reached a
valid loop endpoint.

## Stop Conditions

Surface early in unattended mode, or stop the current attended slice, when any
of these happens:

1. Gate red after one retry.
2. A public contract change is needed: `RMQBackend`, `LeftmostArgMin`,
   `ExactRMQStateEncoding`, or the LCA/RMQ bridge types.
3. A policy break is needed: adding Mathlib, admitting an axiom, changing the
   cost convention, or dropping a key invariant.
4. The same blocker recurs, or a target is mis-specified / unprovable as stated.
5. A taste-sensitive API or abstraction fork has no clear winner.
6. The roadmap is exhausted.

Within an explicitly approved unattended budget, anything else should be worked
through rather than surfaced immediately.

## Anti-Filler Rules

1. Work only from `docs/ROADMAP.md`. A definition or theorem not traceable to
   the active target is scope creep.
2. A target is done only when its pre-registered statement is proved
   `sorry`-free. A filler theorem cannot satisfy a hard, pre-committed
   signature.
3. No new breadth unless the active target requires it. No new RMQ backend, no
   new wrapper family, and no new abstraction layer unless it is needed for the
   current join theorem.
4. Debt must fall or a target must close. Each round's report must show one of:
   a roadmap target newly proved, or a tracked debt metric strictly decreased.
5. Each closed target names one theorem a researcher would cite. If the report
   cannot name one, the round did not earn a green light even if the gate passed.
6. A claim with no concrete witness is not done. An abstract profile over a
   hypothesized family does not close a target until a concrete instance or
   construction instantiates it.
7. Retire in the same round. If a faithful path supersedes an old or unfaithful
   definition, delete or disconnect the predecessor now; do not merely delist it
   from the axiom check.
8. Never stop with unwired scaffolding. A structure that has no live consumer,
   retired predecessor, or capstone theorem is not a checkpoint; it is unfinished
   work.
9. A hook is not the witness. Adding a configurable index, codec slot,
   directory parameter, or bridge theorem is useful only if the same round keeps
   going to the concrete construction/profile, unless a valid stop condition
   blocks it.

Useful debt metrics:

```powershell
rg -c "tickValue|indexedReadCost|storedMicrotableLookupCost" RMQ
rg -n "_of_supplied|_of_firstOccurrences" RMQ
```

The first approximates asserted-cost charges. The second approximates theorems
gated on uncosted supplied inputs.

## Parallelization Policy

A parallel task is legitimate iff its output is consumed by the current target's
join theorem. If deleting the task would not block the join, it is filler.

Parallelize the decomposition of one target, not unrelated targets for
throughput. The lead pass decomposes the active target into independent
sub-lemmas that all feed one join theorem, spawns a worker per independent leaf,
and does the join itself.

Good: for the cost-model target, separate leaves for Array/List refinement,
primitive operation semantics, and operational step soundness, then a join
theorem that refounds one algorithm on the substrate.

Bad: one worker adds a new backend, another polishes docs, another starts a
future data structure. That is parallel, but not goal-directed.

## Proof Workers

In an explicitly approved loop, proof workers are first-class, not only
read-only scouts. The lead should proactively spawn parallel write workers when
the active target decomposes into at least two independent leaves with pinned
contracts.

This loop-mode policy overrides the conservative "read-only unless asked"
default in ordinary single-prompt work. It does not override the need for
disjoint ownership, a clean join theorem, and gate verification.

Protocol:

1. Decompose, then write contracts first. State the join theorem and the exact
   lemma signatures each worker must prove. Workers should not change those
   signatures.
2. Isolate workers. Give each write worker a separate worktree/branch and
   disjoint file ownership, ideally one module or one small module family.
3. Join centrally. The lead merges or ports the leaves into the main worktree,
   proves the join theorem, and runs the gate.
4. Stop on forkiness. If a leaf turns into a taste-sensitive API choice or a
   public-contract change, stop and surface it rather than dispatching it.

Read-only scouts may be many and cheap. Write/proof workers should be few,
DAG-bound, and pinned by exact lemma signatures.

## Iteration Report Template

```text
Target:        <roadmap id + name>
Discharged:    <theorem names that now typecheck, or "in progress, leaf X">
Headline:      <the citable theorem this produced>
Debt delta:    asserted-cost count A -> B ; gated-hypothesis count C -> D
Gate:          PASS/FAIL (build / hygiene / axioms / diff)
Parallelism:   <leaves spawned and the join they fed, or "none">
Next:          <next roadmap target, or stop condition hit>
Stop audit:    <target retired? next obvious? abstract hook left? why stop is valid>
```

If "Headline" and "Debt delta" are both empty, the round was filler regardless
of the gate.

# RMQ Proof-Sprint Completion Gate

Read this file before editing for every nontrivial proof, representation,
cost-model, store, trace, or public-theorem task. A commit, push, green build,
or useful local theorem is a checkpoint. None is evidence by itself that the
assigned target is complete.

## 1. Freeze The Acceptance Contract

Before editing, write a requirement-to-evidence matrix covering:

- every explicit prompt requirement;
- the named downstream consumer and roadmap join;
- every inherited invariant below that applies;
- every requested verification command;
- every explicitly deferred item.

For each row, name the intended definition, theorem, executable check, or
formal obstruction. Mark a deferred item non-blocking only when the prompt
explicitly defers it and it is not required for the assigned claim to be true.
An omitted inherited invariant is still binding.

## 2. Inherited RMQ Invariants

Unless the prompt explicitly narrows the task to prose or a proof-independent
leaf, preserve and establish the applicable invariants:

- every consumed payload cell belongs to the counted payload;
- returned values and routing decisions depend on actual charged reads, not a
  semantic answer computed before the reads;
- traces and footprints are derived from the execution they describe;
- supplied-store agreement determines result, cost, and the relevant trace;
- every successful read is backed by the counted store;
- stored words fit the modeled machine word;
- every executed address, dead/sentinel address, and operand fits the modeled
  machine word, not merely the host array bounds;
- exactness covers all assigned sizes and edge cases without hidden readiness
  or compatibility dispatch;
- proof-only fields never carry answers or uncharged routing information;
- synthetic events, decorative rereads, and post-hoc replay do not support the
  execution claim;
- payload bits, proof fields, model ticks, machine state, Lean runtime, and
  measured performance remain distinct.

If a local component cannot yet satisfy an inherited invariant needed by its
named consumer, the component may be a valuable checkpoint, but the assigned
target is not complete.

## 3. Adversarial Dependency Checks

Before declaring completion, perform these checks when applicable.

### Value dependency

Trace the returned answer backward. Identify the charged reads that determine
it and the decoding/refinement theorems connecting those reads to the semantic
result. If the answer or decisive route is obtained from a semantic lookup,
proof field, or wide-cell value before the machine reads, the target fails.

### Address capacity

Prove bounds for addresses in the actual execution footprint against the
modeled address capacity, normally `2 ^ wordWidth`. Array in-range proofs alone
do not suffice. Include repeated reads, failed reads, and canonical dead or
sentinel addresses, and prove operand bounds required by the consumer.

### Counted-store provenance

Connect the exact store used by the execution to the payload counted by the
space theorem. Check offsets, component order, successful-read backing, word
width, and trace/footprint equality at the composed consumer, not only inside a
detached adapter.

### Edge cases

Exercise the smallest informative cases in Lean: empty when admitted by the
API, singleton, size two, threshold minus one, threshold, and representative
same-block, boundary, and interior queries. Prefer kernel-checked examples or
small proved lemmas. Do not use `native_decide` or `Lean.ofReduceBool`.

## 4. No Caveated Completion

The following statements in a final self-audit normally mean the worker must
continue on the same branch:

- "remaining audit risk" for an assigned or inherited invariant;
- "a reviewer should ask whether" a required property holds;
- "not yet globally backed", "not yet consumed", or "next consumer must prove"
  a property required by the named target;
- a weaker local rung is complete while the prompt named its downstream join.

Honesty is required, but disclosure does not convert an unmet criterion into a
finished task. A post-commit discovery creates another commit on the same
branch; it does not justify a completion report.

## 5. Valid Stop Conditions

A worker may stop only when one of these is true:

1. Every matrix row is closed and the final declaration below is true.
2. A kernel-checked obstruction or precise counterexample shows the target is
   false or mis-specified and forces a coordinator design decision.
3. A genuine external-state blocker prevents further progress and is named
   with the failed command or unavailable dependency.
4. The user or coordinator explicitly redirects the task.

Difficulty, elapsed time, token pressure, a green build, a clean checkpoint,
or the desire for an independent audit are not stop conditions.

## 6. Required Completion Declaration

The final report must include the completed matrix and exactly one status:

- `Status: COMPLETE` followed by: `No assigned or inherited acceptance
  criterion remains unmet.`
- `Status: OBSTRUCTED` with the formal obstruction and required coordinator
  choice.
- `Status: BLOCKED` with the external blocker and evidence.
- `Status: INCOMPLETE` when returning a checkpoint after an explicit redirect.

Do not use `COMPLETE` if any report section identifies work still required for
the assigned target or its inherited invariants.

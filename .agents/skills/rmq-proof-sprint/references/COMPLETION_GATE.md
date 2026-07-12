# RMQ Proof-Sprint Completion Gate

Read this file before editing for every nontrivial proof, representation,
cost-model, store, trace, or public-theorem task. A commit, push, green build,
or useful local theorem is a checkpoint. None is evidence by itself that the
assigned target is complete.

## 1. Freeze The Acceptance Contract

Before editing, write a requirement-to-evidence matrix using
`docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`. Cover:

- every explicit prompt requirement;
- the named downstream consumer and roadmap join;
- every inherited invariant below that applies;
- every requested verification command;
- every explicitly deferred item.

Give every row a stable ID. Copy prompt requirements verbatim; do not weaken
them by paraphrase. The coordinator must name the applicable inherited IDs in
the prompt. A worker may add an omitted invariant but may not remove or narrow
one. After editing starts, only evidence, status, and an explicitly approved
contract amendment may change.

For each row, record all of:

- the exact requirement;
- the intended definition, theorem, check, or formal obstruction;
- the exact proposition or check result that would entail the requirement;
- the named consumer and the composition/identity chain to it;
- one plausible falsifier or boundary case;
- status and residual gap.

A theorem name is not evidence. Quote its checked type or summarize each
hypothesis and conclusion precisely enough that the coordinator can compare it
to the requirement. Mark a deferred item non-blocking only when the prompt
explicitly defers it and it is not required for the assigned claim to be true.

## 2. Inherited RMQ Invariants

Unless the prompt explicitly narrows the task to prose or a proof-independent
leaf, preserve and establish the applicable invariants:

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;
- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads;
- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;
- `INV-STORE-AGREEMENT`: supplied-store agreement determines result, cost, and
  the relevant trace;
- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;
- `INV-WORD-WIDTH`: stored and returned words fit one declared modeled
  machine word;
- `INV-ADDRESS-WIDTH`: every executed address, dead/sentinel address, and
  operand fits the modeled machine word, not merely the host array bounds;
- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;
- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;
- `INV-NO-SYNTHETIC`: synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;
- `INV-CATEGORY-SEPARATION`: payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

The following IDs apply when the public claim has the corresponding shape:

- `INV-PUBLIC-COMPOSITION`: a theorem combining space, exactness, cost,
  provenance, or machine claims proves them about the same construction and
  execution. Conjoining true theorems about different payloads is not closure.
- `INV-GLOBAL-PHYSICAL-MACHINE`: a physical-machine claim supplies one
  pre-execution store/word array and a checked address translation for every
  executed segment, including failed/dead accesses. A theorem for one suffix or
  component is not a whole-machine embedding.
- `INV-WIDTH-SCALING`: one query-independent word-width declaration bounds all
  stored words, addresses, sentinels, operands, and primitive results, and its
  capacity/width is related to input size in the form required by the public
  word-RAM claim. A standalone asymptotic fact about an unconstrained width
  function is insufficient.

If a local component cannot yet satisfy an inherited invariant needed by its
named consumer, the component may be a valuable checkpoint, but the assigned
target is not complete.

## 3. Adversarial Dependency Checks

Before declaring candidate completion, perform these checks when applicable.

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

### Public composition and object identity

Expand the relevant definitions. Write an explicit chain from the public
builder/payload to the executed store and from the physical word array back to
that payload. If any link is a different definition, require a proved equality,
erasure, flattening, or extensional-equivalence theorem at the public consumer.
Compare actual object arguments in theorem statements; matching sizes or
similar names do not establish identity.

For a whole-machine claim, inventory every read-producing segment and show its
physical offset and width obligation. A component-slice theorem closes only
that component.

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
branch; it does not justify a candidate-completion report.

Likewise, a matrix row does not close merely because it contains a theorem
name. If the quoted conclusion is weaker than the requirement, concerns a
different object, or stops before the named consumer, mark it open.

## 5. Valid Stop Conditions

A worker may stop only when one of these is true:

1. Every matrix row is closed and the candidate declaration below is true.
2. A kernel-checked obstruction or precise counterexample shows the target is
   false or mis-specified and forces a coordinator design decision.
3. A genuine external-state blocker prevents further progress and is named
   with the failed command or unavailable dependency.
4. The user or coordinator explicitly redirects the task.

Difficulty, elapsed time, token pressure, a green build, a clean checkpoint,
or the desire for an independent audit are not stop conditions.

## 6. Required Candidate Declaration

The final report must include the completed matrix and exactly one worker
status:

- `Status: CANDIDATE_COMPLETE` followed by: `I found no assigned or inherited
  acceptance criterion unmet; coordinator acceptance is still required.`
- `Status: OBSTRUCTED` with the formal obstruction and required coordinator
  choice.
- `Status: BLOCKED` with the external blocker and evidence.
- `Status: INCOMPLETE` when returning a checkpoint after an explicit redirect.

Workers do not declare roadmap nodes accepted or branches merge-ready. Do not
use `CANDIDATE_COMPLETE` if any report section identifies work still required
for the assigned target or its inherited invariants.

## 7. Independent Acceptance

The coordinator reconstructs the matrix from the frozen contract and source,
checks theorem types and object identity, and records `ACCEPTED` or a repair
disposition. The worker's matrix is an index to evidence, not a certificate.

A public paper capstone, trust-boundary change, combined space/execution
theorem, or roadmap-node closure additionally requires a fresh blind audit of
the exact candidate commit before merge or closure. Give the auditor the
frozen acceptance contract, not the worker's verdict or narrative. The
coordinator remains responsible for auditing that report.

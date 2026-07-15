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
- one concrete anti-vacuity challenge or boundary case per applicable semantic
  subclaim and, before closure, each attempted outcome;
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
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;
- `INV-SEMANTIC-NONVACUITY`: semantic coverage, liveness, ownership, and
  refinement predicates are derived from the operational construction they
  describe. A predicate defined to be `True`, an enumeration restated as
  membership, or a separately hand-written consumer label does not establish
  operational liveness by itself;
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
  execution and over the same validity domain. Conjoining true theorems about
  different payloads or guarded and unguarded executions is not closure.
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

### Semantic non-vacuity and operational liveness

Expand every load-bearing definition behind a claimed semantic equivalence,
coverage theorem, source manifest, liveness predicate, or ownership relation.
For each such claim, attempt the relevant counterfactual mutation:

- add a dead source to a supposedly exact live-source manifest;
- remove a source used by an actual execution;
- assign a plausible consumer label without connecting it to an evaluator
  leaf;
- replace a semantic predicate by `True`, `False`, or a restatement of the
  finite enumeration.

Name the checked theorem or construction obligation that rejects the mutation.
If every advertised theorem would still pass, the semantic row remains open.
It is legitimate for every constructor of a finite universe to be live, but
that fact must be proved from operational reachability or read production, not
made true by the definition of `Live`.

#### Predicate identity and quantifier parity

For each positive claim and its mutation test, write the propositions beside
one another. If accepted sources satisfy `P source` but the mutation theorem
proves `not Q mutant`, closure requires either `P = Q` or a checked bridge
`P mutant -> Q mutant`. Compare all guards and quantifiers, including:

- direct component execution versus top-level query reachability;
- attempted reads versus successful reads;
- arbitrary parameters versus parameters produced by a valid query;
- one concrete instance versus every public instance;
- existential may-read paths versus actual emitted occurrences.

A stronger negative predicate makes a mutation easier to reject and therefore
does not validate a weaker positive predicate. If the predicates or domains do
not match and no bridge is proved, the semantic row remains open.

#### Provenance information preservation

State the evidence level in the matrix. `event \in trace` identifies an event
value but does not distinguish equal repeated occurrences. An occurrence-level
claim must retain a global position or equivalent multiplicity-preserving
decomposition, the producing instruction, the actual folded pre-state, and the
local occurrence that maps to that global occurrence. If a component path is
claimed for that invocation, its parameters must be equal to those computed by
the producing instruction, not merely compatible with the same source label.

Proof construction is not the theorem conclusion. Producing an invocation-
specific witness internally and then returning a record that erases its
parameters does not establish invocation-specific provenance.

### Value dependency

Trace the returned answer backward. Identify the charged reads that determine
it and the decoding/refinement theorems connecting those reads to the semantic
result. If the answer or decisive route is obtained from a semantic lookup,
proof field, or wide-cell value before the machine reads, the target fails.
When using a corruption or store-disagreement theorem as evidence, inspect its
conclusion at the relevant projection. A theorem saying two aggregate
executions differ is not value-dependency evidence if only the recorded word,
event list, or footprint is forced to differ. Require a conclusion about the
returned value, decisive state/route, or a refinement chain that makes that
dependency explicit. Match the evidence quantification and validity domain to
the public claim: one concrete or existential corruption witness does not prove
universal value dependency.

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

If a list-facing or public wrapper guards valid ranges, trace that guard through
every combined adequacy, result, cost, trace, and footprint field. A public
object quantified over all inputs must guard every field identically. Raw
adequacy may appear only under an explicit valid-range premise or inside a
guarded adequacy packet whose invalid case matches the public execution. A
valid-range bridge plus separate invalid-result theorems is insufficient if the
same public record still contains raw adequacy unconditionally. Test empty,
reversed, and out-of-bounds ranges; an empty guarded trace conjoined with an
unguarded adequacy packet is not one execution story.

For a whole-machine claim, inventory every read-producing segment and show its
physical offset and width obligation. A component-slice theorem closes only
that component.

### Edge cases

Exercise the smallest informative cases in Lean: empty when admitted by the
API, singleton, size two, threshold minus one, threshold, and representative
same-block, boundary, and interior queries. When a validity guard exists, also
exercise reversed and out-of-bounds queries. Prefer kernel-checked examples or
small proved lemmas. Do not use `native_decide` or `Lean.ofReduceBool`.

### Classifier and linter completion

A finite mutation fixture set establishes only a lower bound on what a
classifier or linter rejects; it does not establish the category boundary.
Before closing a classifier/linter row:

- state the token, syntax, or structured-data category being classified;
- add category-level holdouts that were not used to enumerate grammatical
  branches in the implementation;
- mutate each allowance boundary, including path-only, line-only, role-prefix,
  negation, and other bypass contexts that apply;
- exercise the production final verdict, including its strictness, path
  normalization, and allowance logic, rather than a copied regex or helper;
- cover parser shapes that can change classification, including focused
  single-file and absolute-path input when the production tool accepts them.

Known examples are minimum fixtures. Completion requires evidence that the
declared category and its allowance boundaries, not merely those sentences,
are gate-effective.

### Public-symbol migration completion

When a public theorem alias is renamed, removed, or moved to compatibility,
lexical claim checks and ordinary builds are necessary but insufficient.
Before closing the migration row:

- search the entire tracked repository for every removed spelling and classify
  the only allowed survivors as exact enforcement data or explicitly frozen
  history;
- extract documentary `RMQ.Headlines.*` references from prose, tables, and
  fenced inventories;
- elaborate generated `#check` files under the broad headline import and, for
  canonical paper anchors, under the narrower paper import;
- reject a compatibility/legacy declaration when a current paper surface
  presents it as a current anchor;
- run production-verdict mutations for prose, fenced code, a dead alias, and a
  renamed-name remnant.

Do not mark the row complete merely because no forbidden token appears in a
selected claim table. Documentary symbol resolution is the closure evidence.

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

A worker's statement that a residual question is "strictly stronger than the
assigned obligation" is not a stop condition. The worker must first map the
question to the frozen requirement wording and inherited invariant IDs. Only
the coordinator may approve a contract amendment that narrows or defers it.

## 6. Required Candidate Declaration

The final report must begin with exactly one worker status. For candidate
completion, its first two lines must be exactly:

```text
Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.
```

The report must then include or link the durable completed matrix. The allowed
statuses are:

- `Status: CANDIDATE_COMPLETE` followed by: `I found no assigned or inherited
  acceptance criterion unmet; coordinator acceptance is still required.`
- `Status: OBSTRUCTED` with the formal obstruction and required coordinator
  choice.
- `Status: BLOCKED` with the external blocker and evidence.
- `Status: INCOMPLETE` when returning a checkpoint after an explicit redirect.

Workers do not declare roadmap nodes accepted or branches merge-ready. Do not
use `CANDIDATE_COMPLETE` if any report section identifies work still required
for the assigned target or its inherited invariants.

Do not substitute phrases such as "closed at worker/gate level", "complete",
or "merge-ready" for the exact status and declaration. A report that omits the
required opening is a protocol failure and is treated as `INCOMPLETE` even when
the branch, CI, and artifact gates are green.

## 7. Independent Acceptance

The coordinator reconstructs the matrix from the frozen contract and source,
checks theorem types and object identity, and records `ACCEPTED` or a repair
disposition. The worker's matrix is an index to evidence, not a certificate.

A public paper capstone, trust-boundary change, combined space/execution
theorem, or roadmap-node closure additionally requires a fresh blind audit of
the exact candidate commit before merge or closure. Give the auditor the
frozen acceptance contract, not the worker's verdict or narrative. The
coordinator remains responsible for auditing that report.

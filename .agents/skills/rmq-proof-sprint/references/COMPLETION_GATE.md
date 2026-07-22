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

`FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`: when a prompt says inherited matrix
rows are frozen, verbatim, or byte-for-byte preserved, validate that claim
before any expensive verification. Decode the exact base blob and candidate
file as strict UTF-8, extract the complete frozen row for every inherited
stable ID, reject missing or duplicate IDs, and require exact UTF-8 byte
equality for each row. A row count, normalized text comparison, visual review,
or a read/write round trip through a locale-sensitive shell is insufficient.
Also reject recognizable mojibake such as `Â¬` or `â€œ...â€`, but treat that scan
only as a negative control: absence of those spellings does not replace exact
row equality. Record the base ref, candidate ref, inherited-ID count, and exact
changed IDs in the evidence ledger.

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
  encoded instruction operand fits the modeled machine word, not merely the
  host array bounds. Constructor-exhaustive evidence must include register
  identifiers, branch/jump targets, dormant code, and arithmetic operands;
- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;
- `INV-PROGRAM-ACCOUNTING`: input-dependent constants and metadata carried by
  executable code are counted machine data or are derived uniformly from
  counted/public inputs. Calling shape-specialized data "program code" does
  not remove it from the payload/state accounting obligation;
- `INV-ORACLE-INDEPENDENCE`: executable fixtures and edge-case expected values
  come from an independent specification or a theorem already connected to it,
  never from the implementation result being tested;
- `INV-VALIDATION-REACH`: executable validation imports and runs the new
  semantic layer. A validator for the predecessor implementation is regression
  evidence only and does not validate the new machine;
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
- `INV-CERTIFICATE-ANTI-BYPASS`: every mandatory field advertised by a public
  certificate is projected by a checked typed consumer at the exact proposition
  and object arguments required by the acceptance contract. Deleting or
  weakening a field, or replacing it with a sibling fact, must break that
  consumer rather than leave only constructor initializers and prose unchanged.
- `INV-MUTATION-REPRODUCIBILITY`: when acceptance relies on an exhaustive,
  production, or public-dependency mutation campaign, the candidate contains a
  versioned runner or fixtures that replay every claimed case, check the exact
  expected failure/acceptance surface, restore tracked state, and leave the tree
  clean. Report prose, copied terminal output, and dangling Git objects are not
  replayable evidence. A public theorem additionally has a checked exact-type
  consumer that fails when the advertised dependency is removed; `#print
  axioms` over the theorem's current type is not such a consumer.
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

### Small-step atomicity, code accounting, and independent validation

For a small-step or fully charged machine, expand every executed instruction
branch. Record the primitive work performed by its evaluator body and mutate
scan length or formula complexity; identify the theorem or bound that changes.
A one-step transition theorem and a category receipt do not establish
atomicity when the evaluator hides variable or multi-category work.

Enumerate every encoded field of every instruction constructor against the
width predicate. Mutate a dormant constructor with an oversized register,
offset, or jump target; the width certificate must fail. Inventory all
input-dependent literals in code and prove that each is counted, charged from
the store, or uniformly derived from public inputs.

For executable fixtures, write the expected result from the independent
reference semantics before running the implementation. A theorem whose
expected value is the implementation output is vacuous. Confirm that each
validator imports or invokes the new module and would fail after a deliberate
mutation to its evaluator.

### Counted-store provenance

Connect the exact store used by the execution to the payload counted by the
space theorem. Check offsets, component order, successful-read backing, word
width, and trace/footprint equality at the composed consumer, not only inside a
detached adapter.

When a contract makes ordered dynamic-read agreement primary and safe/static
footprint agreement a corollary, inspect theorem bodies as well as types. The
dynamic-read or source-region containment bridge must come from execution or
program structure, not by first invoking the legacy safe/static complete-result
equality. Otherwise the old theorem remains load-bearing and the claimed
dependency inversion is circular in proof architecture even if the final
proposition is true.

### Public composition and object identity

Expand the relevant definitions. Write an explicit chain from the public
builder/payload to the executed store and from the physical word array back to
that payload. If any link is a different definition, require a proved equality,
erasure, flattening, or extensional-equivalence theorem at the public consumer.
Compare actual object arguments in theorem statements; matching sizes or
similar names do not establish identity.

For a public certificate or bundled adequacy record, add a checked typed
consumer that projects every mandatory advertised field at its exact
proposition and object arguments. Attempt field deletion, proposition
weakening, and sibling-theorem substitution. If constructors can be adjusted
while all public consumers still elaborate, the field is packaging, not a
load-bearing acceptance dependency.

If the matrix closes a row by citing multiple mutations, commit a replayable
mutation runner or stable fixture set with the candidate. Each case must name
the source mutation, expected verdict and failing surface, and must verify
restoration hashes or a clean tracked tree before continuing. Include expected-
accept controls that distinguish a deliberately non-load-bearing packet change
from a required public-dependency failure. A local mutation that once failed is
useful discovery, but it cannot close `INV-MUTATION-REPRODUCIBILITY`.

For a public theorem dependency, add a checked consumer whose expected type is
independent of the theorem's mutable current declaration and whose proof route
actually consumes that theorem. Mutate the public proposition itself and show
that the committed check fails. Merely running `#print axioms theoremName`,
`#check theoremName`, or a topology scan that only names nearby declarations
adapts to the current type and does not pin the dependency.

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
- for branch certification, invoke scripts/design_decision_check.ps1 with
  -Strict -Base and the task's exact 40-character base commit. A strict run
  without a base must fail closed; a no-Base invocation is evidence only for
  an explicitly non-strict local-worktree mode.
- for opt-out or default-sensitive path classifiers, prove that a neutral
  directory cannot shadow a code-bearing extension and that a broad evidence
  directory cannot admit a new current-looking public surface merely by
  placement. Include production-verdict mutations for both boundaries; an
  allowlisted directory name is not evidence of file role.

Known examples are minimum fixtures. Completion requires evidence that the
declared category and its allowance boundaries, not merely those sentences,
are gate-effective.

### Public-symbol migration completion

When a public theorem alias is renamed, removed, or moved to compatibility,
lexical claim checks and ordinary builds are necessary but insufficient.
Before closing the migration row:

- search the entire tracked repository for every removed spelling and classify
  the only allowed survivors as exact enforcement data or precisely registered
  frozen-history occurrences;
- extract documentary `RMQ.Headlines.*` references from prose, tables, and
  fenced inventories;
- elaborate generated `#check` files under the broad headline import and, for
  canonical paper anchors, under the narrower paper import;
- reject a compatibility/legacy declaration when a current paper surface
  presents it as a current anchor;
- run production-verdict mutations for prose, fenced code, a dead alias, and a
  renamed-name remnant.

A frozen-history exception must be exact or role-scoped at occurrence level:
for example, an immutable snapshot path coupled to exact checked marker and
line content. A whole digest or audit-report directory is never an acceptable
history exemption, and a casual marker word is not authorization. Before
closing the row, run production-verdict mutations proving that the exact
registered occurrence accepts while the same occurrence at a current path, a
retired current-facing alias in an audit report, and forged, misplaced, or
duplicate markers reject. The mutation harness must verify tracked state before
and after every virtual edit.

Do not mark the row complete merely because no forbidden token appears in a
selected claim table. Documentary symbol resolution is the closure evidence.

### Verification coverage, timeout, and rerun discipline

Before running verification, add a compact command ledger to the acceptance
matrix. For each command record:

- development-loop, final-required, or conditional role;
- changed paths and acceptance rows covered;
- unique failure mode not already covered by another planned command;
- exact tree identity or dirty-diff state;
- expected runtime from the closest observed run and the chosen timeout;
- final outcome, observed duration, and any reason a rerun is necessary.

Order checks by information per unit time: static hygiene and diff checks,
focused module or executable targets, direct public consumers and relevant
axiom inventories, then broad builds or the aggregate gate. Do not prescribe
`lake build`, every named root, every validator, and `scripts/gate.ps1` as
independent mandatory runs when their coverage is duplicated and the frozen
contract does not require each result. Broad public, integration, artifact, or
trust-boundary changes normally need the aggregate gate; narrow proof, docs,
or read-only work may use proportionate focused checks with an explicit skip
reason.

When an executable replay imports changed Lean modules, probe host startup
before paying for the full campaign: run a bounded startup/shape smoke test,
then one known exact selector, then the complete registry. This is mandatory
when the changed import closure adds large closed concrete witnesses or other
proof-only data. If the smoke test is unexpectedly slow, inspect generated
initialization and move proof-only values behind theorem-local `let`s or an
equivalent proof-erased boundary before increasing the replay deadline. Run
broad trust, policy, topology, or aggregate certification only after these
controls pass and the content tree is frozen.

A focused selector must distinguish an omitted parameter from a parameter that
was explicitly bound to the empty string. Omission may select the full frozen
registry only when that behavior is part of the contract; bound empty,
whitespace, zero, unknown, missing, and duplicate selection must fail at the
actual command boundary before semantic execution. Test parameter-binding state
rather than only calling an internal selector helper with nonempty sentinels.

Timeout ownership must work on every operating system that runs the required
gate. If the gate runs on Windows and Ubuntu, use an owned-tree implementation
on both and run a sleeper that spawns a descendant and proves the root and child
are absent after timeout. Killing only the root process on a non-Windows host
does not establish process-tree cleanup.

For checks expected to take several minutes:

1. Run only one heavy Lean/Lake process at a time against a shared build tree.
2. Never set a wrapper timeout below a recent successful runtime for the same
   command and comparable tree. Add realistic margin for a cold worktree.
3. On timeout or prolonged silence, inspect the owned process tree, CPU use,
   artifact timestamps, direct-import artifacts, and whether a focused script
   fell back to a full build. Do not infer failure from silence alone.
4. If the child survived the wrapper timeout, wait for or resume that process;
   do not launch a duplicate. Stop an orphan only after identifying it as owned
   by this task and recording why its result cannot be used.
5. Retry an ended command only after a material change: a source fix, targeted
   dependency warm-up, corrected environment, narrower target, or a timeout
   revised from observed evidence. Record the prior run as incomplete, not as
   a failed semantic check.
6. If an aggregate gate fails late, reproduce only the failed component while
   repairing it. Run at most one new aggregate certification on the unchanged
   final tree after the component passes.

Do not run a standalone full replay or full topology suite on the frozen final
tree and then run an aggregate gate that executes the same suite again. Focused
development cases may precede the gate; duplicate final-tree suite ownership
requires a distinct acceptance purpose recorded in the ledger.

Any source, theorem, executable, or load-bearing checker edit invalidates the
checks that transitively consume it. A docs-only or matrix-only edit invalidates
the relevant claim/design/topology checks but does not automatically invalidate
unrelated Lean compilation. Explain the dependency judgment. The final report
must distinguish commands rerun, reused only for scheduling/cache purposes,
and skipped as redundant or disproportionate. Repetition is not independence.

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

An upper-bound proof does not establish semantic tightness. If a row says a
cost cap is *tight*, *attained*, or makes an older smaller cap impossible,
require a checked equality/lower-bound witness or a counterexample/negation of
the smaller bound on the same reachable object and domain. Syntactic facts
about the proof of `cost <= K`—including use of `exact`, absence of
`Nat.le_trans`, or zero visible arithmetic slack—remain upper-bound evidence
only. Comments and decision prose must use the same distinction.

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

For stop condition 2, the obstruction must match the frozen target's domain,
objects, guards, and quantifiers.  It must either negate the exact target or
provide a checked implication from the target to `False`.  Separate theorems
showing an arbitrary-state mutation, an unbounded shape parameter, and one
reachable concrete execution do not compose by prose into an unbounded family
of canonical reachable executions.  When reachability is load-bearing, prove
one checked family that simultaneously carries the growing parameter and the
actual invocation.  Also distinguish an obstruction to the current
implementation or one proposed decomposition from an obstruction to every
construction permitted by the frozen contract.  A narrower implementation
obstruction is valuable checkpoint evidence, but it does not authorize
`Status: OBSTRUCTED` for the target.

If a worker introduces a proxy proposition for an obstruction, every
load-bearing proxy clause must either quote the frozen requirement verbatim or
be derived by a checked theorem from the frozen target.  In particular, do not
add the contradiction-producing lower bound as a field of the proxy and then
negate that stronger proposition.  Boundary values, same-block arithmetic, or
accepted logical results are not an actual invocation witness: when execution
is load-bearing, retain an occurrence index, pre-state, instruction with its
evaluated operands, post-state, and the exact run/receipt object, or prove a
checked bridge to an equivalent operational predicate.

A worker's statement that a residual question is "strictly stronger than the
assigned obligation" is not a stop condition. The worker must first map the
question to the frozen requirement wording and inherited invariant IDs. Only
the coordinator may approve a contract amendment that narrows or defers it.

## 6. Required Candidate Declaration

Before the final candidate declaration, run both working-tree hygiene and the
committed range check. `git diff --check` on a clean post-commit worktree does
not certify the candidate commit; run `git diff --check <exact-base>..HEAD` (or
an equivalent exact committed-range check) after the final commit.

When the candidate changes a design-sensitive path, its final design-policy
evidence is `scripts/design_decision_check.ps1 -Strict -Base <exact-40-character-base>`.
Do not substitute a strict no-Base run: production intentionally rejects it.

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

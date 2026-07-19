# Known RMQ Proof Failure Modes

Read only the sections relevant to the assigned theorem. These are historical
constraints, not a substitute for inspecting current source.

## Complexity Fidelity

- Wrapping a pure semantic answer in a constant tick does not establish a
  constant-time algorithm.
- A successful read must be charged, machine-bounded, and backed by the counted
  payload used in the space theorem.
- Proof-only fields may carry invariants, never answers or uncharged routing
  oracles.
- Synthetic trace events and repeated decorative reads do not establish an
  execution story.
- Replaying charged reads after first obtaining a wide-cell or semantic value
  does not make that value machine-derived.
- Proving an address is within a host array does not prove it fits the modeled
  machine word. Check the actual footprint, including dead addresses, against
  `2 ^ wordWidth`.
- A per-component machine-backed adapter does not close a range or global-store
  claim until the composed execution derives its result and footprint from
  that store.
- Dense all-pairs tables need an actual sublinear budget; an eventuality theorem
  that excludes the branch being counted is not enough.

## Consumption

A helper closes a target only when the named downstream theorem consumes it.
Common incomplete endpoints include:

- a selector cell whose exactness assumes it already stores the semantic winner;
- a range witness exact only from a supplied answer/prefix position;
- endpoint-fringe exactness conditional on a supplied merged-candidate fact;
- an abstract profile whose concrete compact builder remains absent;
- a routing/index function that can hide search, predecessor, or oracle work;
- a new parameter or adapter with no concrete public instance.

An honest "remaining audit risk" is useful evidence, but it is also evidence
that an assigned acceptance criterion remains open. Commit the checkpoint and
continue rather than reporting the task complete.

## Expensive Verification And Blind Reruns

- A quiet Lean process is not necessarily hung. Check the owned process, CPU,
  and artifact timestamps before terminating or duplicating it.
- A wrapper timeout is not a semantic failure. If the child is still running,
  wait for that process instead of starting the same command again.
- Never retry the same expensive command on the same tree with the same cold
  dependencies and timeout. Change the condition first: warm the missing
  import, fix the actual error, narrow the target, or choose a timeout supported
  by an observed successful runtime.
- Do not run multiple heavy Lean/Lake commands concurrently against one build
  tree. Cache contention and memory pressure can turn otherwise bounded checks
  into misleading timeouts.
- A late full-gate failure should be debugged with the smallest failing
  component. Re-running the entire 20- or 30-minute gate after each local edit
  is waste, not stronger evidence; reserve one aggregate rerun for the final
  unchanged tree.
- Avoid double-paying for coverage. If the final aggregate gate includes a
  build or axiom inventory already run for diagnosis, the earlier run is useful
  diagnosis and cache warm-up, while the final aggregate result is the
  certification. Do not add another identical final invocation without a
  distinct acceptance purpose.

The regression pattern is: an expensive command reaches a tool timeout or
stays quiet, its surviving process or cache state is not inspected, and the
same command is launched again unchanged. The verification ledger in
`COMPLETION_GATE.md` must reject that pattern by recording tree identity,
runtime evidence, process disposition, and the material reason for every
rerun.

### B7-R3 regression: startup smoke precedes full executable replay

Commit `024e33eb922355bb811ed20191215c5992328ebc` is the named regression
fixture. Its imported proof module exposed closed size-3469 address/store
witnesses, so a full 21-case replay was used as the first startup observation
and crossed a 20-minute deadline. Fixture caching did not fix a shape-only
probe; moving the proof-only values into theorem-local `let`s reduced that
probe from a 120-second timeout to about two seconds.

Apply `B7R3-STARTUP-SMOKE-BEFORE-FULL-REPLAY` when an executable's import
closure changes. A ledger that starts with the full registry, or runs broad
candidate certification before startup smoke and one known selector pass,
fails the regression. The rule does not reject a genuinely slow complete
campaign: after startup and selector controls pass, its deadline may use an
observed full-run runtime with cold-cache margin.

## Letter-Complete Semantic Claims

A theorem can have the requested name and still fail the intended semantic
obligation. Known examples include:

- defining every source as live with `Live := True`, then proving counted/live
  equivalence from an exhaustive constructor list;
- assigning consumer names in a second hand-written table without connecting
  them to the evaluator leaves that issue reads;
- proving two complete trace records differ when only a logged return word is
  forced to differ, then presenting that as returned-answer dependency;
- combining a raw unguarded adequacy packet with a guarded list-facing result
  and calling the conjunction one execution story.
- accepting sources with a weak predicate `P`, rejecting a fresh mutation with
  a stronger predicate `Q`, and presenting `not Q` as evidence against `P`
  without proving `P -> Q`;
- proving a direct component may attempt a failed read and presenting that as
  top-level valid-query reachability or successful source liveness;
- using `List.Mem` to establish producer evidence and then describing it as
  occurrence- or multiplicity-preserving provenance for repeated equal events;
- constructing a witness from the actual invocation but erasing its parameters
  from the returned relation, then advertising invocation-specific ownership;
- declaring a remaining top-level or occurrence-level obligation "strictly
  stronger than assigned" without a coordinator-approved contract amendment.
- treating a finite list of classifier mutations as an upper bound on the
  forbidden category, so a nearby held-out verb or word order escapes;
- testing a raw regex instead of the production final verdict, or granting a
  whole-file allowance that lets a fresh forbidden claim pass outside the
  quoted contract row;
- parsing `file:line:text` by delimiters when drive-qualified or colon-bearing
  paths are valid scanner inputs, causing focused scans to change semantics.

For semantic coverage, liveness, ownership, dependency, and composition claims,
expand the load-bearing definitions and identify which checked theorem fails
under the corresponding mutation. Green builds, exhaustive enumeration, and
accurate declaration-name inventories do not supply that evidence.

### E1 regression: category labels do not make a fully charged machine

Commit `fd5e3d24d045c9ec503c258dfeb87599fe002e19` is the named regression
fixture for small-step acceptance. It had a genuine executable transition
system, simulation, receipts, a uniform fuel bound, and a green Word-RAM review,
but it did not close the advertised fully charged familiar-machine contract:

- `.localBPWindow` charged a recursive variable-length arg-min/rank scan as one
  step, while `.candidateOfSummary` hid several arithmetic operations behind a
  candidate category;
- invalid-range expected values were copied from the raw machine result being
  checked;
- `Instr.NatConstantsFitInBits` constrained `.natConst` and returned `True` for
  other encoded instruction operands;
- shape-dependent layout metadata lived in specialized program literals
  outside the counted physical store;
- the executable validator and cost harness exercised the predecessor
  `SuccinctRMQClassic` path rather than the new small-step machine;
- a post-commit working-tree diff check missed trailing whitespace in the
  candidate range.

Apply `INV-INSTRUCTION-ATOMICITY`, `INV-ORACLE-INDEPENDENCE`, the constructor-
exhaustive `INV-ADDRESS-WIDTH`, `INV-PROGRAM-ACCOUNTING`, and
`INV-VALIDATION-REACH` together. A category inventory, one-step increment
theorem, theorem-name ledger, or predecessor validator must reject this exact
evidence pattern rather than close it.

### E1 R2 regression: disconnected witnesses do not prove a target obstruction

Commit `39e97e08b14e8960c484cc7948409d550a97c955` is the named regression
fixture for obstruction quantifier parity.  It correctly exposed that the
current `.localBPWindow` evaluator hides a recursive scan behind two charged
ticks, and it separately proved:

- an arbitrary configuration can be mutated so its count register exceeds any
  proposed bound;
- the canonical raw block-size function is unbounded across List inputs; and
- one fixed canonical query reaches the `.localBPWindow` category.

Those propositions do not share one witness.  They do not prove a family of
canonical reachable executions whose actual count register is unbounded, and
they do not rule out every familiar decomposition allowed by the frozen E1
contract.  Consequently they obstruct the current macro instruction and fixed
scalar unrolling, not the frozen target itself.

Apply the valid-stop quantifier rule in `COMPLETION_GATE.md`: require either a
checked negation of the exact frozen target, a checked implication from that
target to `False`, or a canonical reachable family that preserves the growing
parameter and actual invocation in one proposition.  Separate existential
witnesses may be composed only by a checked bridge theorem.  Legitimate
narrower statements remain useful when labeled as implementation obstructions
and must not be rejected merely because they do not close the roadmap target.

### M1 regression: opaque certificate consumption does not pin its fields

Commit `9e68c48a52692fa4fb26f1790179d5c623cb47f1` is the named regression
fixture for certificate anti-bypass. Its reviewer-native machine certificate
contained mandatory well-formedness and supplied-store agreement fields, and a
public paper theorem accepted the certificate as an argument, but no checked
typed consumer projected every mandatory field at the exact propositions and
object arguments required by the acceptance contract. A field could therefore
be deleted and constructor initializers repaired while the intended public
dependency remained untested.

Apply `INV-CERTIFICATE-ANTI-BYPASS`: provide one checked consumer whose type
names the exact projections and arguments, and record field-deletion,
proposition-weakening, and sibling-substitution mutations. Passing a certificate
opaquely, constructing it, listing its field names, or mentioning it in a
public theorem body does not make every field load-bearing.

### M1 R2 regression: report-only mutations do not pin a public dependency

Commit `1f50e5698a0842b8c50c1e08d101b076152d6bef` is the named regression
fixture for mutation reproducibility. It repaired the earlier opaque-field
defect: an independent 24-proposition `RequiredFacts` type projected every
certificate field literally, and the paper theorem included guarded
`WellFormed`, guarded `RequiredFacts`, and exact ordered-dynamic complete-
`TraceResult` agreement.

The acceptance matrix nevertheless claimed a 24-field deletion campaign plus
11 proposition/object/public mutations without committing a mutation runner or
fixtures. The cited snapshot was an unreferenced Git object outside the
candidate ancestry. The committed headline check printed the paper theorem's
current axiom inventory but did not pin its expected public type. Deleting only
the paper theorem's guarded `RequiredFacts` conjunct and its tuple proof still
allowed both `lake build RMQPaper RMQ` and
`lake env lean scripts/headline_axiom_check.lean` to pass.

Apply `INV-CERTIFICATE-ANTI-BYPASS` and
`INV-MUTATION-REPRODUCIBILITY` together:

- retain the real 24-field typed projection;
- add a committed exact-type consumer that extracts the guarded certificate,
  guarded required facts, and physical ordered-dynamic complete-result
  obligations from the paper theorem itself;
- add a versioned runner for every claimed field deletion, weakening, sibling
  substitution, guard removal, and public-dependency deletion, plus an expected-
  accept packet-only control;
- require the runner to check the intended failing surface, restoration hashes,
  and clean tracked state after every case.

Do not treat matrix prose, an axiom printout that follows the mutable theorem
type, copied logs, or an unreachable snapshot as committed mutation evidence.
Legitimate weaker packaging may remain when labeled non-load-bearing and covered
by the expected-accept control.

### Public-symbol migration is not a lexical claim scan

A rename/removal can pass a claim-language scan and still leave a dead theorem
reference in prose, a fenced inventory, a theorem map, or a file whose import
does not expose the cited declaration. Searching only current Markdown table
rows is likewise insufficient: it misses prose and code fences, while a green
Lean build does not elaborate documentary identifiers.

Migration closure requires all of the following:

1. a repository-wide search for every removed spelling, with only exact
   enforcement files and precisely registered frozen-history occurrences
   exempted;
2. extraction of documentary public identifiers from prose, tables, and
   fences;
3. generated Lean resolution under the import promised by each document
   (`RMQPaper` for canonical RMQ paper anchors, the broad barrel for broader
   headline references);
4. mutations for prose, fenced code, an invented dead name, a renamed-name
   remnant, and a compatibility declaration presented as current.

A lexical scanner remains useful as a tripwire, but it is not evidence of
public-symbol migration closure.

Frozen history is an occurrence-level exception, not a directory role. An
acceptable mechanism couples an exact immutable snapshot path to exact checked
metadata and line content, or enforces an equivalently narrow structured
scope. Never exempt a mixed-role digest or audit-report directory wholesale.
The words `FROZEN-HISTORY`, a history-like filename, or an unvalidated marker
do not grant an allowance. Mutate the exact production verdict to show that a
registered occurrence accepts while the same text at a current path, a forged
marker, a duplicate marker, and an audit-report occurrence reject.

### W18 regression: relation splitting

The W18 producer-provenance candidate improved the forward theorem from an
arbitrary-state category join to an actual prefix-state producer witness, but
its positive source coverage and negative fresh-source mutation used different
relations. Accepted sources had a direct component `HasProducerMayPath`, which
could include a failed attempt outside top-level query reachability; the fresh
source was rejected with the stronger `HasOperationalProducer`. Since no
bridge from the positive predicate to the negative predicate was proved, the
mutation did not challenge the accepted property.

The same candidate began from `event \in trace`, so equal repeated events were
not position-distinguished, and its public path record erased the actual
invocation parameters used to build the proof. This is the canonical regression
test for predicate identity, quantifier parity, and provenance information
preservation. Do not treat a stronger residual theorem as optional merely
because a worker report labels it future hardening.

### E1 R3 regression: surrogate obstruction by stipulated lower bound

Candidate `7fe5b8ba353b955b8e989ddd2ae8dc2371140518` correctly proved an
unbounded family of accepted same-block boundary intervals and soundly negated
a new scalar familiar-run packet.  It did not close the frozen E1 obstruction:
the proxy target stipulated `localCount <= localBPSteps`, while the frozen
contract permitted any equally familiar primitive decomposition and contained
no such numeric lower bound.  No checked frozen-target-to-proxy bridge derived
that clause.

The candidate also named its boundary predicate a canonical invocation even
though it retained no run, transition, receipt occurrence, full instruction,
evaluated operands, pre-state, or post-state.  The arithmetic family would
remain true if the production route stopped executing the local-BP instruction.

Apply `E1R3-SURROGATE-OBSTRUCTION-REGRESSION`:

- compare every load-bearing proxy clause against the frozen contract;
- require a checked implication from the frozen target to the full proxy;
- reject a contradiction-producing lower bound introduced only by definition;
- distinguish accepted boundary arithmetic from occurrence-indexed operational
  reachability; and
- retain the result only as a narrow decomposition obstruction when those
  bridges are absent.

This regression does not reject useful narrow impossibility theorems.  It
rejects only their promotion to full-target `OBSTRUCTED` status.

### B7/A08 regressions: upper-bound attainment and evidence-location policing

Candidate `6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25` proved the amended
interior cost only as `cost <= 33`. Its proof used the new bound directly, but
that supplied neither an equality witness nor a lower bound. Treating the lack
of a transitivity step as proof that 33 is attained also led prose to call the
older `cost <= 30` statement unprovable without a checked counterexample.

Apply `B7-UPPER-BOUND-IS-NOT-ATTAINMENT` whenever a worker claims tightness:
require an equality/lower-bound witness or checked negation on the same
reachable family. A bare upper bound may still close an upper-bound row when
accurately labeled; this regression rejects only promotion to attainment or
impossibility.

Audit report `1bc6b3597b97720c5c5dad0a2e87277cf28fd7ea` then inferred that
24 B7 rows lacked evidence because frozen table cells were blank and statuses
remained `Open`, despite row-keyed append-only evidence and coordinator-owned
acceptance. It also named IDs that were not in the frozen matrix.

Apply `A08-EVIDENCE-LOCATION-IS-NOT-EVIDENCE-ABSENCE`: enumerate the real
frozen IDs, accept every location the matrix schema explicitly permits, and
reject a row only for a substantive evidence gap. This does not bless appended
prose as proof; theorem, consumer, identity, executable, and anti-vacuity links
must still be reconstructed independently.

## Select And Close History

For historical C1 descriptor-select work, proof fields such as
`descriptor_some_exact`, `descriptor_none_exact`, and
`descriptor_word_choice_exact` state obligations; they are not the compact
builder. A full per-occurrence local-delta payload also fails the intended
`LittleOLinear` budget.

For historical C2 BP-close work, direct scans over interior block summaries are
exact but not uniformly constant. The compact route requires charged local,
global, and top-level navigation plus endpoint repair and a theorem identifying
the leftmost minimum-excess prefix with the RMQ/LCA answer.

## Current Final-Route Constraint

The present architectural campaign separates total block geometry from optional
compact-storage readiness. A local patch that merely lowers the zero-block scan
constant preserves the wrong abstraction and does not advance the campaign.

## Obstruction Dossier

A worker may stop short of a requested positive target only when the target is
closed, a concrete theorem proves it mis-specified, an external dependency
blocks progress, or the coordinator must choose between genuine architecture
forks.

When local variants repeatedly fail for one structural reason, report an
obstruction dossier containing:

1. the exact target signature;
2. the materially distinct construction families attempted;
3. the smallest failed obligations or counterexamples;
4. why nearby syntactic variants cannot repair the failure;
5. the representation, invariant, cost-model, ownership, or theorem choice now
   required.

There is no magic attempt count. Repetition without materially new information
is not evidence; a minimal formal obstruction is stronger than a long list of
similar failed proofs.

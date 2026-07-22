# Claim Drift Policy

Claim-drift scans are tripwires, not doctrine. They find sensitive language and
force a policy decision: current, qualified, legacy-only, historical, forbidden,
or intentionally superseded.

When theorem work genuinely changes the public truth, update the checked
theorem surface, public docs, this policy, and the relevant design-decision log
together.

## Evidence Standard

Each sensitive claim should identify its evidence tier:

- kernel theorem;
- model theorem;
- executable validation;
- artifact evidence;
- process evidence.

Process evidence is never enough for a mathematical or executable claim.

## Supersession Rule

If a claim is superseded, do not merely delete it from the scan. Change its
policy:

- current claim -> legacy compatibility;
- current blocker -> historical blocker;
- public theorem constant -> old theorem alias;
- future-work gap -> closed, with theorem or artifact evidence.

The scan should then fail only when old wording appears as the current public
story.

## Policy Data

`scripts/claim_drift_scan.ps1` reads
`docs/internal/CLAIM_DRIFT_POLICY.json`. Keep the JSON concise and update this
human-readable file when the interpretation changes.

## Controlled Claim-Language Lint

The strict `2^128` rule is a controlled claim-language lint, not a complete
natural-language semantic checker. Its suspicion boundary has only two token
classes: the exponent and standalone canonical execution/route/query language
within one bounded line. It does not require an activation, premise, or
threshold word. Narrow anchored allowances then admit explicit negation,
historical notes, compatibility companions, and proof-only witness roles.
`noncanonical` and `non-canonical` are distinct tokens and are not canonical-
role matches.

The only whole-path allowance is this policy pair. Rejected examples in W19's
acceptance matrix are allowed only by the conjunction of that exact path and an
exact frozen `POLICY-01`--`POLICY-06` or `POLICY-R1`--`POLICY-R6` table-row
marker. A new unmarked claim in the same file remains a strict violation.

The strict scanner's exit verdict is the policy result. Regression fixtures
invoke `claim_drift_scan.ps1 -Strict` itself, so path and line allowances and
the term's `strict` flag are tested together with its PCRE pattern. The scanner
parses structured `rg --json` records and normalizes repository-local absolute
paths before applying policy. Relative, drive-qualified Windows, colon-bearing,
and focused single-file inputs therefore share one parser and verdict path.
The aggregate gate and CI both run the repository scan in strict mode.

Finite fixtures are lower bounds, not a completeness claim. The regression
therefore includes category-level holdouts, deceptive negative/role prefixes,
the conjunctive matrix-row allowance, a fresh unmarked matrix-file misuse, and
absolute single-file input. These test the stated controlled boundary and its
allowance bypasses without claiming unrestricted semantic understanding.

The strict detector treats a canonical execution's 2^128 mention as suspicious before role allowance; this policy-file example is admitted only by the exact policy-file path allowance.

The strict current-cost detector uses the same production-verdict discipline
over the registered current-fact surfaces. Its controlled category pairs one
of current, canonical, principled, uniform, modeled, query, charged-trace,
trace-length, or Costed.cost language with a member of the registered retired
set within one physical line or one adjacent continuation line. It never joins
across a blank paragraph or more than one line boundary. The accepted current
bound is 210.

The retired set is 76, 142, and 207.

CLAIM-HISTORY-A07-COST is a controlled trailing marker, not a filename-wide or
word-only exemption. It admits a single explicitly historical clause, the
current-210-then-historical-comparison form used by the current publication
surfaces, or the distinctly named live-compatibility-352-then-retired-
comparison form. A marker or the word "historical" in an unrelated clause does
not authorize a stale-current statement later on the line. The production
regression exercises that bypass boundary through claim_drift_scan.ps1 -Strict.
An arrow is not an exemption.

The retired query bound moved from 207 to the current bound 210.

A current subject that owns a retired value still fails even when followed by
an arrow to the live bound. The existing B7 change-history sentence is also
accepted only because it identifies the moved whole-query literal and the
charge-policy movement. A second clause that presents a retired token as live
remains a violation.

## Canonical Paper Topology

Policy version 14 rejects every spelling removed during the W21 paper-surface
migration: the six unqualified legacy query aliases, the transitional and
large-regime aliases, and the compatibility-only W18 projection names. The
only whole-path allowances are exact policy or lint enforcement files. Audit
reports receive no allowance. Historical aliases may remain only on a line
beginning with the exact marker
`<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT -->` in one of the two exact registered
June 28 snapshot files. The path and line conditions are conjunctive; neither a
digest directory nor casual `FROZEN-HISTORY` wording grants an allowance. The
production scanner regression exercises each removed-name category and every
history-scope boundary.

A lexical claim scan is still only a tripwire. It cannot establish that a
rename migrated every documentary Lean reference, that a surviving name is in
scope under the document's advertised import, or that a compatibility name is
not being presented as current. `scripts/paper_topology_lint.ps1` therefore
performs a repository-wide removed-name search and generates Lean `#check`
files: every unmarked documentary `RMQ.Headlines.*` name—including names in the
README-linked current publication digest and audit reports—resolves under the
broad barrel, and every canonical RMQ name used by paper maps also resolves
under `RMQPaper`.
`scripts/paper_topology_lint_regression.ps1` mutates prose, fenced code, a dead
name, a renamed W18 name, and a compatibility-as-current anchor through that
production verdict.

The topology lint requires `RMQPaper` to import only `RMQ.Headlines.RMQ`,
requires the broad `RMQ.Headlines` barrel to import the explicit
`RMQ.Headlines.RMQCompatibility` module, requires all declarations in that
compatibility module to contain `Legacy` or `Compatibility`, and blocks old
query regimes from the canonical module, current public rows, and headline
axiom inventory. The aggregate gate runs the lint, its mutation regression,
and the headline axiom inventory.

## Initial Sensitive Claims

- Novelty language such as "first mechanized" or "first-ever" must be qualified
  by a referee-grade novelty-search caveat unless a future paper process closes
  that search.
- "Logs cannot be forged" must be scoped to interpreter-generated traces and
  checked provenance/model theorems.
- "Artifact ready" and "AE-ready" should only appear when the artifact status is
  actually being claimed.
- "Lean runtime" should not be presented as the RAM model-cost theorem.
- No current canonical execution theorem uses `2^128` as an activation premise.
  Explicit legacy compatibility companions may retain that sufficient premise.
  Separately, W19's proof-only sparse-local nonvacuity witness uses symbolic
  `N = 2^128`; that witness is not an execution, payload, cost, runtime, or
  paper-main-theorem premise. The broad two-token detector covers possessive,
  activated-at, threshold-free, exponent-first, and spaced/unspaced forms.
  Narrow role allowances keep explicit negation, historical records,
  compatibility companions, and proof-only sparse-local witnesses accepted.
- `210` is the current principled canonical charged-trace bound, with exact
  algebra `2*35 + (2*11 + 2*37 + 33) + 11 = 210` and cost equal to emitted
  trace length. The current route is `readWord`-only: attempted payload reads
  are charged and `wordRank`/`wordSelect` remain compatibility-only
  constructors that are never emitted by this route. Controller operations
  remain explicitly uncharged.
- The strict event-silent category is a current-surface zero-remaining form:
  `no` followed immediately by `event-silent` (or `event silent`), then
  `computation` or `work`, optionally followed by `left`, `is left`, `remain`,
  `remains`, or `remaining`. It has no path-wide or same-line keyword
  allowance; words such as `historical`, `retired`, `rejected`, `quoted`,
  `unqualified`, `policy`, and `scan` do not license the classified form. The
  accurate boundary is that no input-size-dependent or unbounded event-silent
  loop remains; instruction dispatch, register moves, fixed-width decoding,
  bounded arithmetic/comparison, option tests, branching, candidate merging,
  trace assembly, and validity guards are still uncharged. Explicitly bounded
  wording remains permitted.
- The canonical current-surface registry includes the reviewer-grade claim
  correspondence, family summary, and model-adequacy packet as well as the
  artifact, theorem-map, roadmap, trust, and current-digest surfaces. An
  exhaustive synchronization task must inspect every path matched by
  `currentFactSurfacePathRegex`; before launch its prompt records the exact
  base-derived match count, full inspected-path set, and expected repair paths,
  all of which must be covered by write scope. A prompt-local hand list or
  worker-side first discovery is not sufficient.
- A registered current publication surface that asserts the strong
  `readWord`-only fact must name
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`.
  File-level required-attribution checks complement line-oriented vocabulary
  lint: a generic execution story, the weaker three-constructor alias, or the
  construction-facing capstone must not be presented as though its own checked
  type contains the stronger conjunct. Accurately labeled weaker and
  compatibility claims remain permitted beside the strong alias.
- `CLAIM-HISTORY-A07-EVENT-VOCABULARY`: the weaker three-constructor current
  route description, including `payload read or bounded word primitive`
  paraphrases, is historical or explicitly compatibility-labeled only.
- `CLAIM-HISTORY-A07-COST`: the retired bounds `76`, `142`, and `207` are
  historical only.

  On a registered current surface, place this exact marker at
  the end of the explicitly historical clause or use one of the two documented
  current-210/live-compatibility-352 comparison forms; a marker in an unrelated
  clause is not an allowance.
- `328` is the literal-pinned historical checked transitional U2 bound under
  `RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq`, retained for audit
  comparison rather than as the paper-facing cost. The current raw expression
  is distinctly named `RMQ.SuccinctClassic.liveCompatibilityQueryCost` and
  equals `352`; it is a compatibility value, not the historical identity or
  the paper-facing `210` bound.
- `4144`, Ready-regime `118`, the zero-block route, and `196727` are
  compatibility/history only, not the canonical reviewer execution.
- W15's post-hoc physical-result construction and W17's static category join
  were rejected. W18 remains a compatibility checkpoint. W19 supplies indexed
  occurrence preservation, invocation-parameter preservation, successful
  closed-valid reverse reachability, and common-predicate mutation rejection;
  coordinator reconstruction and blind exact-commit audit remain separate.
- Event-value producer evidence means an emitted event value belongs to an
  actual producing instruction's trace at the folded prefix state. Reserve
  "occurrence-level producer provenance" for a theorem that also retains the
  global and local occurrence, multiplicity, producing instruction, actual
  state, and component invocation parameters.
- A semantic mutation must test the same predicate and domain used by the
  positive acceptance theorem, or a checked implication must connect them.
  W19's positive claim quantifies a successful `some word` occurrence, its
  mutation predicate permits any `word?`, and
  `ReviewerProducerClaim.hasOperationalProducer_of_successful` checks the
  required implication over the common claim domain.
  Component may-read, successful read, top-level valid-query reachability, and
  actual emitted occurrence are distinct evidence levels.
- Successful closed-valid source reachability is a global existential: each
  source has some valid query witness. It must not be wrapped in unused current
  `xs`/`left`/`right`/`ValidRange` parameters or described as a read by every
  current query. Indexed forward provenance remains query-specific.
- Current machine claims must identify the same public `buildPayload`, reviewer
  physical words, execution, ordered footprint, and reviewer word width.
- "Physical execution" in the current reviewer story must name the genuine
  `FlatPhysical` supplied-store evaluator and translation adapter, not a mapping
  of an already-computed logical result and trace.
- The canonical live manifest is one typed universe of exactly 22 physical
  sources over logical segments `0..22`, including canonical close. Logical
  segments `0` and `19` share the BP source. Live segment `21` is present;
  rejected fresh segment `23` is outside the manifest. The current singleton
  repeated-read fixture uses global positions `0` and `15` from producing
  instruction positions `0` and `1`.
- `CLAIM-HISTORY-A07-SOURCE-COUNT`: the retired 20-source count is historical only.
- `CLAIM-HISTORY-A07-FRESH-SEGMENT`: rejected fresh segment `21` is historical only.
- `CLAIM-HISTORY-A07-TRACE-POSITIONS`: global positions `0` and `12` are historical only.
- The public list space statement is
  `buildPayload.length <= 2*n + overhead n` with little-o overhead. Exact
  physical-word erasure remains mandatory, but no padding may manufacture a
  size equality.
- Invalid or empty list ranges return `none` across the canonical,
  supplied-store, trace, costed, and reviewer-physical surfaces.
- `118` is compatibility/history, not the canonical all-size theorem.
- "No extraction gap" must not erase the remaining executable/compiler ladder;
  Lean executability is evidence about runnable definitions, not a verified
  backend.

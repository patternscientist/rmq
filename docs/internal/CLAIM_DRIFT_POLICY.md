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
- `76` is the current principled canonical charged-trace bound, with exact cost
  equal to emitted trace length. It charges payload reads and word-rank/select
  primitives; controller operations remain explicitly uncharged.
- `328` is the historical checked transitional U2 bound, retained for audit
  comparison rather than as the paper-facing cost.
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
- The canonical live manifest is one typed universe of exactly 20 sources,
  including canonical close. Legacy close/interior storage is compatibility
  only; BP code is the explicitly shared source.
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

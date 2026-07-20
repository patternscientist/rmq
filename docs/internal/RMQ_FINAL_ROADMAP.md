# RMQ Final Roadmap

This is the live internal roadmap for making the RMQ spoke strong, elegant,
and immediately legible to formal-methods reviewers. It is a delegation and
architecture document, not a public claim surface.

## Success Standard

A reviewer should be able to find, without reverse-engineering the repository:

1. one classical list-facing RMQ theorem and its exact Lean source;
2. the matching lower bound and the `buildPayload.length <= 2n + o(n)` upper bound;
3. the counted payload, proof-only data, machine state, and cost measure;
4. a familiar execution/refinement chain from the public query to a small
   machine model;
5. one reproducible artifact path with expected outputs;
6. the design rationale for every non-obvious abstraction or regime.

For this roadmap, elegance means that mathematical concepts determine the
interfaces. Compatibility thresholds, proof accidents, and historical routes
must not determine the public architecture. A regime split is acceptable only
when the represented algorithm genuinely has two regimes.

## Verified Baseline

The integrated paper frontier already contains:

- the narrow `RMQPaper` reviewer root and `RMQ.Headlines.RMQ` alias surface;
- the list-facing at-most-`2n + o(n)` constant-query profile and exact lower-bound
  package;
- flat counted-payload backing for successful reads and a no-synthetic final
  trace;
- list-facing supplied-store/footprint result, cost, and exactness theorems;
- canonical transitional all-size cost `328`, with `4144`, Ready `118`,
  zero-block, and `196727` retained only as compatibility/history surfaces;
- differential validation and a theorem-adjacent executable cost harness;
- a prepared Cartesian builder path with theorem-backed agreement;
- paper/artifact correspondence, import-closure, trust, provenance, and
  reproduction documents.

The remaining central weakness is architectural. The current canonical
relative-summary `Active` predicate combines block geometry, payload readiness,
and word-width facts. Inactive layouts therefore collapse several geometric
parameters to zero, which creates a special zero-block structural replay and a
larger all-size constant. The next campaign replaces that patchwork with total
positive parameters and a uniform query route.

## Dependency DAG

```text
F0 declaration/import closure -----+---------------------------> A1 refactor
                                    |
P1 total parameter design ----------+--> U1 total layout --------+
                                    |                            |
N1 naming/module design ------------+----------------------------+
                                                                 v
                                                        U2 uniform directory
                                                                 |
                                                                 v
                                                        U3 all-size cost
                                                                 |
                          +--------------------------------------+------+
                          v                                             v
                 M1 exact adequacy/certificate                 E1 machine model
                          |  |                                          |
                          |  +--> S1 bit-addressed serialized query      |
                          |       (deferred; does NOT gate V1)           |
                          |                                             |
                          +----------------------+----------------------+
                                                 v
                                      V1 artifact and paper freeze
```

`M1` and `E1` are SIBLINGS under `U3`, not sequential — neither waits on the
other. `S1` hangs off `M1` because it consumes the supplied-store transfer
lemma `M1` makes primary, and is deferred out of the `V1` path deliberately.

The `F0`/`P1`/`N1` scouts are complete and joined in
`RMQ_DECLARATION_CLOSURE_2026_07_10.md` and
`RELATIVE_RMM_LAYOUT_DESIGN.md`. Those syntheses, rather than the individual
chat reports, govern `U1`.

## Active Campaign

### F0. Pin The Reviewer Dependency Closure

Status: complete for U1 planning; A1 removal still needs global reverse
consumers and checked import-pruning experiments.

The Lean declaration probe found 126 imported workspace modules and 72 modules
in the all-headline declaration closure. Fifty-four import-only modules are A1
candidates, not dead-code findings. See
`RMQ_DECLARATION_CLOSURE_2026_07_10.md`.

### P1. Design Total Relative-RmM Layout

Status: complete; synthesized in `RELATIVE_RMM_LAYOUT_DESIGN.md`.

The canonical layout has positive routing divisors and widths, while truthful
semantic counts may be zero on empty domains. Computational layout data is
separate from `Valid`, `SummaryFits`, and `CompactReady` proof predicates. No
layout projection depends on storage readiness.

### N1. Fix The Canonical Naming And Module Architecture

Status: complete for U1. The accepted namespace and sequencing decisions are
recorded in `RELATIVE_RMM_LAYOUT_DESIGN.md`; the scout's fine-grained file tree
is advisory and will be reconsidered after U2 stabilizes proof boundaries.

### U1. Implement Total Layout Parameters

Status: complete at `03043fe`.

`RelativeRmm.Layout`, its canonical constructor, intrinsic validity,
summary-fit, compact-readiness, legacy Active/Ready equivalences, and Ready-route
parameter agreement now live in `RelativeSummary.lean`. The raw upper-cover
theorem moved upstream from `LocalBPDecoder.lean`. Query dispatch, payload,
trace, cost, and public theorem claims did not change.

Acceptance:

- every routing divisor and width is positive;
- every count has truthful zero semantics;
- no layout projection branches on `SummaryFits` or `CompactReady`;
- legacy Active/Ready and current Ready-route behavior agree through checked
  lemmas;
- no public query, payload, trace, cost, or artifact claim changes.

### U2. Build One Uniform Local/Interior Directory Route

Status: **ACCEPTED** at exact target
`4f7ec8be47ecd65b2859a3784fadeab48a629e4e` after coordinator reconstruction
and the fresh blind A04 audit recorded at
`f5c2ab03a064e56f90a17574041cd116568416d8` on 2026-07-14.

Every size uses `RelativeRmm.canonicalLayout` and the same close/LCA reviewer
route. One exhaustive typed universe has 22 physical sources over logical
segments `0..22`; segments `0` and `19` share the BP-code source. It includes canonical close
and the B2/B3 fringe/select chunk-table sources.
For every indexed read, W19 retains the same global occurrence, program
instruction occurrence, folded prefix state, component-local position, exact
invocation parameters, source, and composed-trace offset for that exact current
query. Separately, the non-parameterized
`ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` packet proves that
every counted source and shared-BP consumer has a successful witness in some
actual closed whole-query execution under a valid ordinary `List Int` query.
It does not say every source is read by the current query. Fresh segment `23`
is rejected by the common occurrence relation, and a checked bridge embeds the
successful positive predicate into the mutation-side arbitrary-result
predicate. W18 event-value and component may-read facts are compatibility only.
Region exclusivity,
logical-segment coverage, and absence of canonical legacy duplicates also hold.
The existing supplied-store evaluator runs through a checked
flat-physical address-translation adapter. Its execution-derived ordered
footprint controls agreement; a checked consumed-address disagreement changes
the execution, proving physical-store dependence. One pre-execution physical
word list erases exactly to public `buildPayload`, while the amended public
space statement is `buildPayload.length <= 2*n + overhead n` with little-o
overhead and no padding. Empty,
singleton, size-two, and symbolic threshold-boundary cases are kernel checked.
No Ready/Active/inactive or zero-block dispatch is reachable from
`RMQPaper` / `RMQ.Headlines.RMQ`.

Acceptance evidence:

- `canonicalRelativeRmmInteriorDirectory_profile_allSize`;
- `canonicalRelativeRmmInteriorRangeFootprint_address_fits_reviewerWordBits`;
- `canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree`;
- `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_store_parametric`;
- `concreteBPNativeSuccinctRMQCanonicalInteriorPhysicalFootprint_fits`;
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact`;
- `concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases`;
- `concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`,
  `repeated_equal_read_occurrences_have_distinct_receipts`, and the
  typed source/region/segment coverage chain;
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical`;
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint`;
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator`;
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne`;
- `concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence`,
  `concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_successful_closed_valid_occurrence`,
  `ReviewerProducerClaim.hasOperationalProducer_of_successful`, and
  `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer`;
- `concreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`, consumed once
  by `listIntSuccinctRMQPaperMainTheorem`, outside current-query quantifiers;
- `SuccinctClassic.queryCosted_invalid` and its canonical, supplied-store,
  trace, costed, and physical wrappers;
- reviewer physical successful-read backing and whole-query word/address bounds
  in the final adequacy packet.

The coordinator independently reconstructed the frozen matrix and accepted
A04's finding-free REQ-01--REQ-08 verdict. A04's sole P3 finding concerned
three stale comments describing synthetic fallback; the integration change
corrected those comments without changing definitions or theorem statements.
U2 is closed, and the single-payload, physical-store, occurrence-provenance,
word-width, and literal-pinned historical transitional-`328` chain is the U2
base for U3. The live raw-expression compatibility value is separately named
and equals `352`.

### U3. Reprove One Principled All-Size Cost Bound

Status: **candidate complete after the A05 publication-topology correction on
`codex/rmq-u3-principled-allsize-cost`**; the next fresh blind exact-commit audit
remains coordinator-owned. A05 report commit `64cfd2d...` was read directly and
was not merged.

The unchanged uniform route now has the principled checked charged-trace sum
`210 = 2*35 + (2*11 + 2*37 + 33) + 11`, proved by
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq` and bounded
against the global trace by
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`.
The strong current bridge
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`
classifies every emitted event as `readWord`, excludes the synthetic fallback,
and proves that direct
`WordRAM.TraceEvent.nonSyntheticWeight` certificate weights sum to both trace
length and the `Costed` cost of the same execution before being bounded by
`210`. This equality is canonical-trace evidence: `TraceResult.toCosted` charges
trace length and would count a synthetic compatibility marker if one were
present, while `nonSyntheticWeight` assigns that marker weight zero.

A05 accepted that operational chain but rejected the paper topology because six
unqualified historical profiles remained coequal exports. The correction adds
`concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`,
which combines the canonical reviewer payload, physical erasure, space
envelopes, exact global execution, direct positional backing for every
successful trace read, non-synthetic weight equality to trace length and the
same `Costed.cost`, and `210` bound in one checked theorem. `RMQPaper` imports
only its canonical headline alias. Historical source theorems remain reachable
solely through the explicit `RMQ.Headlines.RMQCompatibility` module under
`Legacy`/`Compatibility` names; compatibility-only W18 projections now live
there as `CompatibilityW18` aliases as well.

Self-contained topology repair also makes documentary symbol migration a
blocking checked obligation. Repository-wide old-name search leaves removed
spellings only in exact enforcement data or two registered June-snapshot
occurrences. Each historical occurrence is an exact path plus exact
case-sensitive marker-and-line value required exactly once; the same marker is
rejected elsewhere. The README-linked current publication digest and all audit
reports are fully scanned. The topology lint elaborates every documented
headline identifier under the broad barrel plus every canonical paper
identifier under `RMQPaper`. Prose, fenced, dead-name, renamed-W18,
compatibility-as-current, current-digest, audit-report, and frozen-scope
mutations are blocking.

Acceptance:

- **Candidate satisfied:** the bound is a sum of named select, rank, endpoint
  fringe, and interior-directory costs;
- **Candidate satisfied:** there is no input-size compatibility threshold in
  the public route; macro crossing is an execution-derived structural premise;
- **Candidate satisfied:** genuine-event classification, no-synthetic evidence,
  non-synthetic certificate weights, trace length, `Costed` cost, and the upper bound
  describe the same global execution;
- **Candidate satisfied:** final adequacy, supplied-store footprint transfer,
  `List Int`, paper/root aliases, examples, and numeric inventories consume the
  new theorem;
- **Candidate satisfied:** every current paper-facing construction/query row
  names the canonical payload/global-trace execution, while the blocking
  topology lint prevents retired aliases and regimes from re-entering the
  paper module, claim tables, or headline inventory.

Scope boundary: U3 is only a theorem in the current charged-trace model. It
does not prove serialized-payload querying, preprocessing complexity, or
conventional word-RAM complexity. Controller dispatch, arithmetic, branching,
decoding, local scans, and merging remain documentary uncharged omissions. U3
does not predeclare a replacement instruction vocabulary; E1 must define its
richer machine and prove a simulation.

### M1. Make Machine Adequacy Reviewer-Native

Status (updated 2026-07-19): **near-complete but unmerged. Do not re-build.**
Four of the five named invariant families are certified on `main`; all four
clauses are proved on `codex/m1-reviewer-native-machine-adequacy-r4`, which
needs a `76` -> `210` rebase before it can compile. The residual is a rebase, an
audit, and a small amount of composition — see the ordered list at the end of
this section.

(The previous status line read "partially present; strengthen after `U3`". It
was written before the r4 branch existed and reads as an invitation to build
work that is already done; superseded rather than deleted so the change is
visible.)

Make exact agreement on the dynamic read set the primary supplied-store
theorem. Keep safe-footprint agreement as a convenient corollary. Bundle the
recurring address, operand, word-width, store, and trace invariants into a named
machine-well-formedness certificate consumed by the headline theorem.

The public statement should make the following chain obvious:

```text
list query
  = canonical costed query
  = supplied-store execution under exact read agreement
  = first-order controller execution
```

SCOPE RULING (2026-07-19, owner-approved). The four clauses above are M1's
scope. They are unchanged since 2026-07-09 and are correct as written.

`DESIGN_DECISIONS.md`'s DD-20260714-007 contains the sentence "M1 must still
connect querying to a serialized payload representation". That sentence did
NOT amend this rung. Its drafting worker was asked and recalls it as a `U3`
scope disclaimer — noting that serialization, preprocessing and a fully charged
machine remained downstream — and specifically does not recall assigning
serialized-payload querying to M1, nor distinguishing a word-addressed from a
bit-addressed target when drafting it. The next record the same day,
DD-20260714-008, restates the same obligation neutrally as a "downstream
obligation" without the M1 attribution. Bit-addressed serialized-payload
querying is now rung `S1` below; it does not gate `V1`.

NAMING NOTE (evidence only; the requirement text above is unchanged). "first-order
controller execution" is a roadmap phrase with no counterpart in the codebase —
it occurs only in this document. The Lean object the chain's last step denotes
is `canonicalInterpretedQueryCosted`
(`RMQ/Core/SuccinctRMQClassic.lean`), reached through the certificate field
`refines_canonical_interpreted`. A worker grepping the roadmap's phrase will
find nothing.

M1's residual is smaller than the status line implies: four of the five named
invariant families are already certified on `main` by
`ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`
(`RMQ/Core/SuccinctFinalModelAdequacy.lean`), the missing one being
**word-width**; and all four clauses are proved on the unmerged branch
`codex/m1-reviewer-native-machine-adequacy-r4`, which cannot compile against
`main` because it proves a field via `nonSyntheticWeight_sum_le_76` and `76` is
now a frozen historical constant superseded by `210`.

RESIDUAL, in dependency order. Items 1-2 are the critical path; 3-5 are
composition from material that already exists; 6 is the gate.

1. **Rebase `codex/m1-...-r4` onto `main` and resolve `76` -> `210`.** Its
   24-field certificate covers all five invariant families including
   **word-width**, the one `main` lacks. Both certificate theorems are fully
   proved and unconditional and the certificate is genuinely consumed by
   `listIntSuccinctRMQPaperMainTheorem`. The `76` field touches a **public
   paper-theorem conjunct**, so re-derive against `210` rather than transcribing
   a numeral. Merge-base `5f59455`; the branch is 12 commits ahead of it while
   `main` is 189 ahead. **Judgement-bearing** — do not merge as-is, and do not
   supersede: nothing on `main` or in `E1` replaces it.
2. **Refresh the M1 mutation registry** (41 semantic cases) against B2's
   `segment < 23` drift. Previously recorded as REQUIRED. Mechanical but
   operand-exact.
3. **Canonical-pinned exact supplied-store theorem.** Compose
   `..._globalReadStore` (`RMQ/Core/SuccinctFinalStoreParam.lean`) with
   `queryTraceResultWithStore_eq_of_orderedReadFootprint`
   (`RMQ/Core/SuccinctRMQClassic.lean`). Mechanical.
4. **Safe-agreement-as-corollary**, so clause 2 holds in the direction the rung
   asks for. Fully available today: `every_emitted_read_has_listed_region` plus
   `canonical_segments_complete` give every emitted read `segment < 23`, and the
   dead trace segment is `29`, so safe agreement implies exact agreement
   directly. Mechanical.
5. **A chain-shaped public statement.** All four links exist; none is a chain.
   The `queryCosted = canonicalInterpretedQueryCosted` link exists **only as a
   conjunct inside a bundle** — there is no standalone theorem. The public
   surface is a flat ~14-conjunct tuple rather than an equation chain.
   **Judgement-bearing** — it is a public-surface shape decision.
6. **Fresh blind external audit at the accepted M1 commit.** The r4 branch
   self-reports `WORKING`, not ACCEPTED, and the coordinator log records the
   gate as passed with "Coordinator acceptance + fresh-blind audit remain open".
   No audit has named a defect in the Lean content; the blockers are the
   registry drift and this audit.

**What M1 does NOT owe:** anything from `E1`. The two are siblings under `U3`
and share no vocabulary — `storesAgreeOnOrderedReadFootprint` and
`orderedReadFootprintWithStore` occur **zero times in any E1 file**. `E1`'s
receipt equality is a **single-store** fact instantiated at the canonical store;
`M1`'s clause 1 is a **supplied-store** theorem quantified over stores agreeing
on the read set. Along one axis `E1` is stronger (it fixes order and read
values, not just an address set); along `M1`'s axis it is silent. Do not treat
`E1`'s completion as discharging any part of this rung.

### S1. Bit-Addressed Serialized-Payload Querying (deferred)

Status: deferred, named so it is not homeless. **Does not gate `V1`.**

State the canonical charged query against the raw `List Bool` payload —
`buildPayload` (`RMQ/Core/SuccinctRMQClassic.lean`), the object the
`2 * n + o(n)` bound is stated over — rather than against the word-addressed
physical store.

Why it is deferred rather than folded into `M1`: `flattenPayloadWords` is **not
proven invertible**, because the payload words carry only
`word.length <= reviewerWordBits` and no uniform-width equality. So a
bit-addressed statement needs either a uniform-width theorem or an explicit
chunking decoder, neither of which exists. That is new construction, not
composition, and it consumes exactly the supplied-store transfer lemma `M1` is
meant to make primary — so it must follow `M1`, not ride inside it.

Not unexplored territory: `BPCloseRMQNavigationDirectory.queryEncodedCosted`
already takes a `List Bool` payload and has an exactness theorem plus a
`2n + o(n)` encoded profile, at the family layer rather than as a paper
capstone. The open work is lifting that to the canonical charged route.

Do not describe any word-addressed composition as "serialized-payload
querying". Four reviewer-facing surfaces currently disclaim this capability;
claiming it before `S1` lands would overclaim against all four.

### A1. Refactor Around The Stable Argument

Status: partially begun; perform after `U2` stabilizes interfaces.

Use the `F0` and `N1` reports to:

- split payload layout, program/trace semantics, cost derivation, and adequacy;
- turn old monolithic modules into thin compatibility roots where useful;
- quarantine history, obstruction, proposal, and superseded route modules;
- remove dead aliases and private helpers only after reverse-dependency proof;
- preserve stable public aliases and regenerate the import-closure report.

Mechanical movement and semantic strengthening should be separate commits.

### E1. Add A Small-Step Reference Word-RAM Machine

Status: first-order controller and U3 actual-event accounting exist; E1 must
define a richer instruction semantics and prove a fully charged small-step
simulation.

Define the smallest familiar instruction semantics needed by the existing
first-order query controller. Prove result agreement and a step/trace-cost
correspondence. The machine is a reviewer-legible refinement target, not a
claim about Lean wall-clock time.

In parallel, complete the executable evidence path:

- deterministic payload/query fixtures;
- differential answer checks;
- no-synthetic and successful-read coverage checks;
- model ticks reported separately from construction/query wall-clock timings;
- ready-threshold measurements once construction is fast enough.

External C/Rust generation is optional. Add it only if it reduces reviewer
friction after the reference-machine theorem exists; a bespoke translation
validator that is harder to audit than the Lean executable is not progress.

### V1. Independent Verification And Submission Freeze

Status: final milestone.

- run Linux CI with pinned versions and stored logs/timings;
- run an advisory independent checker (`nanoda`) and the project axiom/hygiene
  gates;
- freeze theorem correspondence, import closure, claims, related work, novelty
  search log, and artifact instructions;
- produce a DOI-ready and, if needed, anonymous artifact bundle;
- obtain one fresh blind external audit of the exact release commit, then use
  the same auditor only for its correction loop and a different fresh auditor
  for final acceptance if material changes land.

## Parallelization Rules

- Parallelize independent evidence/design leaves that feed one named join.
- Give only one worker ownership of a shared abstraction or theorem signature.
- Run validation, dependency analysis, and audit work in parallel with proof
  work when they are source-read-only.
- Do not launch implementation workers for `U1` and `U2` concurrently; their
  interfaces are causally ordered.
- After every worker completion, the coordinator audits, integrates or rejects,
  updates this DAG, and engineers the next prompt set.

## Work Not To Start Yet

- C/Rust generation or a verified backend before `E1`.
- Broad BP-navigation, rank/select, or union-find expansion.
- Public renames before the uniform route and architecture map stabilize.
- Deletion based on file size or import reachability alone.
- More local zero-block constant patches that preserve the active-is-geometry
  coupling.
- Prose caveats in place of theorem-shaped repairs.

## Standard Gates

Proof/implementation branches choose the smallest relevant target build and
then run the paper-root, trust, hygiene, design-decision, and diff gates. Public
surface changes also update claim correspondence and numeric checks. Process
branches run:

```powershell
git diff --check
powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1
powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1
```

Exact worker checks belong in the worker prompt; this roadmap should not embed
stale branch-specific prompts.

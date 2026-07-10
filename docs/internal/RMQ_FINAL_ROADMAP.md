# RMQ Final Roadmap

This is the live internal roadmap for making the RMQ spoke strong, elegant,
and immediately legible to formal-methods reviewers. It is a delegation and
architecture document, not a public claim surface.

## Success Standard

A reviewer should be able to find, without reverse-engineering the repository:

1. one classical list-facing RMQ theorem and its exact Lean source;
2. the matching lower bound and the `2n + o(n)` payload upper bound;
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
- the list-facing `2n + o(n)` constant-query profile and exact lower-bound
  package;
- flat counted-payload backing for successful reads and a no-synthetic final
  trace;
- list-facing supplied-store/footprint result, cost, and exactness theorems;
- public all-size cost `4144`, fast-regime cost `118`, and legacy `196727`
  compatibility surfaces;
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
                          |                                             |
                          +----------------------+----------------------+
                                                 v
                                      V1 artifact and paper freeze
```

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

Status: next, after the independent U1 interface audit.

Make all sizes use the same directory abstraction. First attempt to totalize
the existing hierarchy so small instances degenerate naturally. Introduce a
separate counted packed implementation only if a formal obstruction shows that
the total hierarchy cannot cover the bounded small regime cleanly. The top-level
query must not dispatch to an unbounded structural scan because a parameter
became zero.

Acceptance:

- all successful reads remain charged and backed by counted payload;
- no proof-only answer fields, dense answer tables, or synthetic events;
- the same semantic exactness theorem covers small and ready inputs;
- the old zero-block route is unreachable from the reviewer path, then retired
  or quarantined as compatibility history.

### U3. Reprove One Principled All-Size Cost Bound

Status: blocked on `U2`.

Derive the all-size constant from the uniform route. Aim for `118`, but do not
force that numeral if a clean machine derivation gives a nearby constant. The
paper-facing theorem should expose one explained constant; old `4144` and
`196727` theorems may remain as compatibility aliases outside the main path.

Acceptance:

- the bound is a sum of named primitive/directory costs;
- there is no input-size compatibility threshold in the public route;
- the exact-cost and upper-bound surfaces agree with the executable trace;
- the paper/root aliases and numeric equality checks are updated together.

### M1. Make Machine Adequacy Reviewer-Native

Status: partially present; strengthen after `U3`.

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

Status: first-order controller exists; small-step simulation remains.

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

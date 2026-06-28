# RMQ

[![CI](https://github.com/patternscientist/rmq/actions/workflows/ci.yml/badge.svg)](https://github.com/patternscientist/rmq/actions/workflows/ci.yml)

**TL;DR:** We used Lean to machine-check that range-minimum queries can be
answered exactly in constant modeled time while storing only `2*n + o(n)` bits
of Cartesian-shape data, essentially two bits per array element. The same
development also proves the matching information-theoretic lower bound with
the coefficient-correct `2n - 1.5 log n - O(1)` Catalan slack, so the leading
space term is formally optimal.

A Lean 4 formalization project for range-minimum query and the reusable
advanced-data-structure spokes growing out of it. The RMQ theorem stack remains
the citable center; the repository now also exposes standalone rank/select,
balanced-parentheses navigation, union-find, and shared model-hub import roots.

For a family-level theorem inventory, dependency DAG, correctness/cost matrix,
and consolidated modeling notes, see
[`docs/FAMILY_SUMMARY.md`](docs/FAMILY_SUMMARY.md).
For the plan to grow this RMQ proof-of-concept into a larger verified
data-structures library, see
[`docs/REPOSITORY_STRATEGY.md`](docs/REPOSITORY_STRATEGY.md).
For the standalone rank/select spoke, see
[`docs/RANK_SELECT_FRONTIER.md`](docs/RANK_SELECT_FRONTIER.md).
For the union-find spoke, see
[`docs/UNION_FIND_FRONTIER.md`](docs/UNION_FIND_FRONTIER.md).
For a compact external-reader scope summary, see
[`docs/WHAT_IS_PROVED.md`](docs/WHAT_IS_PROVED.md).
For the trust base and verification commands, see
[`docs/TRUST_BASE.md`](docs/TRUST_BASE.md).
For the compact skeptical-review packet for the headline theorem, see
[`docs/TRUST_AUDIT_PACKET.md`](docs/TRUST_AUDIT_PACKET.md).
For a documentation map, see [`docs/README.md`](docs/README.md).
For the completed cleanup record and library-shaping roadmap, see
[`docs/CLEANUP_AND_ROADMAP.md`](docs/CLEANUP_AND_ROADMAP.md).

License: Apache-2.0; see [`LICENSE`](LICENSE).

## Public Import Roots

The current public roots are:

```lean
import RMQ              -- RMQ/LCA family and succinct RMQ capstone
import RMQHub           -- reusable cost/RAM/refinement/table/lower-bound hub
import RMQRankSelect    -- standalone rank/select spoke
import RMQBPNavigation  -- balanced-parentheses navigation spoke
import RMQUnionFind     -- union-find specification and forest-refinement spoke
import VerifiedDS       -- thin aggregate facade over the active public roots
```

`RMQ` remains the stable artifact name for the existing theorem inventory.
`VerifiedDS` is intentionally only a facade for now: it tests the broader
library shape without forcing a namespace or repository migration before the
spoke APIs settle.

## What This Is, And Why Care

Range-minimum query (RMQ) asks for the leftmost index of the minimum value in a
subarray. That sounds small, but it is the engine behind Cartesian trees,
constant-time lowest-common-ancestor queries, Fischer-Heun preprocessing, and
succinct tree navigation.

The surprising fact is that RMQ does not need to store the array values after
preprocessing: the Cartesian shape determines every answer. This repo verifies
that story end to end under explicit model assumptions.

This repo formalizes RMQ as a connected algorithm family, not as one isolated
implementation. In Lean 4, without Mathlib or custom axioms, it proves:

- one shared half-open, leftmost-minimum contract for many RMQ backends;
- the RMQ/LCA reductions in both directions, including Cartesian trees and
  Euler-tour depth traces;
- Fischer-Heun-style linear preprocessing and constant supplied-query bounds
  under an explicit RAM/indexed-access model;
- a no-premise information-theoretic RMQ lower bound from Cartesian-shape
  counting, including the proved doubled integer form
  `4*n - (3*log2(2*n+1)+3) <= 2*bits`, i.e. the coefficient-correct
  `2n - 1.5 log n - O(1)` Catalan slack without rational arithmetic; and
- a payload-accounted BP-native succinct RMQ capstone:
  `2*n + o(n)` payload bits with constant modeled query cost.

The significance is the combination. The project checks the semantic theorem
that the data structures answer the right query, the reduction theorem that RMQ
and LCA are interderivable in the standard ways, the lower-bound theorem that
the shape information really costs almost `2*n` bits, and a matching succinct
upper-bound profile under named model assumptions. That is the honest pitch:
not "Lean's lists are magically constant-time," but a proof-auditable RMQ stack
where correctness, payload bits, and cost-model claims are separated and
connected.

## Current Status

The project currently builds without Mathlib, using only Lean/Std plus `omega`.
It proves a common half-open, leftmost-argmin contract for:

- a direct linear scan backend,
- a plus-minus-one RMQ package with the Euler-depth invariant and a verified
  linear-scan instance,
- a sparse table backend,
- a hybrid block backend with boundary scans and sparse middle summaries,
- a self-recursive hybrid backend with aligned boundary scans and recursive
  middle summaries,
- a certified raw microtable backend over Cartesian shapes, and
- value-level Fischer-Heun backends, including an exact all-input wrapper.

The headline succinct theorem is the two-sided capstone alias
`Headlines.succinctRMQTwoNPlusOConstantQuery`
(for
`SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`):
for Cartesian-shape RMQ, the stored payload is the exact balanced-parentheses
shape code plus `o(n)` auxiliary bits, and every valid half-open query is exact
with a uniform constant modeled cost through the generic sparse-exception
false-close/select access family and compact BP close/LCA directory. The same
theorem also exposes the sharpened lower side
`4*n - (3*log2(2*n+1)+3) <= 2*bits`, pairing the concrete upper structure with
the coefficient-correct Catalan slack in one citeable surface.

The hybrid proof is already factored through a generic three-piece combinator:
an exact nonempty left boundary, an optional middle interval, and an optional
right interval combine into one exact leftmost argmin witness.

Cost bounds are either model-level `Costed` theorems under the documented
RAM/unit-cost indexed-access convention, or derived `RAM.Exec` trace bounds
over counted Array/branch/compare/allocation primitives. They are not claims
about Lean's executable `List` runtime.

## Layout

- `RMQ/Core/Spec.lean`: query validity, `LeftmostArgMin`, index combination,
  and reusable exactness combinators.
- `RMQ/Core/Cost.lean`: lightweight Mathlib-free cost accounting with
  `Costed`, `pure`, `bind`, `tick`, `run`, erase laws, and additive cost laws.
- `RMQ/Core/RAM.lean`: tiny traced RAM substrate whose costs are derived from
  primitive operation traces, with Array reads, comparisons, branches, and
  allocations/pushes as counted primitives.
- `RMQ/Core/Refine.lean`: reusable reference/executable refinement helpers,
  starting with `Refine.StoredMatrix`, an Array-backed representation plus a
  proof that it erases to the List-of-Lists reference table.
- `RMQ/Core/TableModel.lean`: generic model-level indexed access, unit-cost
  read wrappers, a compatibility alias for stored matrix certificates, and
  payload-bit accounting views for separating counted state payloads from
  proof-only auxiliary fields.
- `RMQ/Core/LowerBound.lean`: generic finite-domain encoding lower-bound
  helpers: fixed-length bitstrings, lossless encodings, injection/capacity
  counting, and logarithmic-slack arithmetic.
- `RMQ/Core/Window.lean`: direct scan/window lemmas.
- `RMQ/Core/Backend.lean`: explicit backend interface with soundness,
  completeness, invalid-query rejection, and generic built-backend equality.
- `RMQ/Core/LCA.lean`: proof-friendly rose-tree Euler node/depth traces, the
  plus/minus-one depth invariant, first-occurrence windows, direct root-path
  LCA semantics, the `TracePathAgreement` bridge statement, a derived
  `TracePathExactOnLabels` semantic exactness theorem, a trace-side
  leftmost-minimum reference candidate, generated path-annotated Euler traces,
  a finite generated-label agreement certificate, structural
  `LabelsUnique -> TracePathAgreement` proof via generated Euler-window
  invariants, and the RMQ-backed tree-level LCA theorem for certified traces.
- `RMQ/Core/PlusMinusOne.lean`: first-class plus-minus-one RMQ inputs,
  packaging `AdjacentDepthsDifferByOne` for Euler-depth lists, plus
  delta-signature replay, certified normalized signature tables, and a backend
  wrapper that can forget back to the ordinary `RMQBackend` contract.
- `RMQ/Core/Reduction.lean`: contract-level RMQ/LCA reduction interfaces:
  label-unique generated Euler traces turn RMQ backends into LCA backends,
  with trace/path-agreement and finite-check wrappers still available, and
  certified interval-to-LCA encodings turn LCA backends into RMQ backends.
- `RMQ/Core/Cartesian.lean`: proof-friendly Cartesian tree construction over
  list indices, root/range-minimum lemmas, the proved `BuiltRangeLCASpec`
  endpoint-LCA certificate, and a concrete certified RMQ-to-LCA reduction.
- `RMQ/Core/Shape.lean`: explicit binary Cartesian shapes with empty children,
  the first RMQ-behavior/shape equivalence theorem over all subranges,
  exact fixed-size shape signatures, constant-shift RMQ/shape preservation,
  recursive canonical representative arrays for every shape, and the Catalan
  split recurrence for `shapeCount`.
- `RMQ/Core/EncodingLowerBound.lean`: RMQ/Cartesian instance of the generic
  lower-bound layer: fixed-length bit encodings that distinguish all Cartesian
  shapes of size `n` have capacity at least `shapeCount n`; exact RMQ query
  decoders over representative arrays induce such lossless shape encodings. A
  Mathlib-free Remy-style counting argument proves the quadratic Catalan bound
  `2^(2*n) <= (2*n+1)^2 * shapeCount n`, yielding the concrete
  no-premise `2*n - (2*log2(2*n+1)+2)` bit lower bound. It also proves the
  squared count `2^(4*n) <= (2*n+1)^3 * shapeCount n^2`, which gives the
  coefficient-correct doubled slack theorem
  `4*n - (3*log2(2*n+1)+3) <= 2*bits` for exact RMQ encodings. A
  state-encoding adapter lets concrete built-state encoders inherit these
  lower bounds, and a canonical representative state encoding instantiates
  that adapter.
- `RMQ/Core/Succinct.lean`: exact list-backed rank/select primitives,
  balanced-parentheses predicates, model-level packed rank/select with
  unit-cost query theorems, and generated Euler-tour parentheses that are
  proved balanced and erase to the generated plus-minus-one depth trace.
- `RMQ/Core/SuccinctSpace.lean`: public barrel for the role-split
  broadword/succinct-space theorem interfaces. The split modules below it own
  Mathlib-free `o(n)` overhead accounting, payload-word/table encodings,
  payload-backed rank/select components, BP-native Cartesian shape payloads of
  exact length `2*n`, broadword RMQ profiles, and the proved close-navigation
  RMQ adapter.
- `RMQ/Core/SuccinctRankSelect.lean`, `RMQ/Core/GenericSelect.lean`,
  `RMQ/Core/BPCloseNavigation.lean`, and `RMQ/Core/SuccinctRMQ.lean`:
  role-named barrels for the live succinct stack. `GenericSelect` now exports
  physically split pure bitvector select modules, including low-level facts,
  parameter, primitive, slot/span, entry, flag-rank, relative-table, directory,
  select-source, and family layers; BP compatibility is a separate terminal
  bridge. The other barrels collect construction-level rank/select, compact BP
  close navigation, and the final payload-accounted BP-native RMQ capstone.
- `RMQ/Core/RankSelectSpec.lean`,
  `RMQ/Core/RankSelectCompressed.lean`, and
  `RMQ/Core/RankSelectPublic.lean`:
  standalone rank/select extraction surfaces. `RankSelectSpec` packages exact
  bitvector access/rank/select over stored bits with an `n + overhead n`
  payload profile, `RankSelectCompressed` adds the fixed-weight
  compressed/FID theorem shape with a Mathlib-free binomial-count universe plus
  a packed-code-only local RRR block kernel consumed by an ambient fixed-weight
  block-composition scaffold, a charged class/length-read local kernel,
  block-size route-table cost discipline, decoded route-field profiles over
  charged metadata reads, packed fixed-width route-word readback profiles,
  canonical route field-table constructors, a single-store route/class-length
  envelope whose ambient evaluator consumes charged class/length reads, a
  family-level combined-metadata `o(n)` bridge, a global block-count/field-width
  budget bridge for fixed-block route/class-length families, fixed-size chunk
  decomposition bounds plus a sentinel chunk variant for route-total
  class/length metadata budgets, log-sized chunk-count budgets with `o(n)`
  block counts, a narrow log-log class/length metadata budget for sentinel
  log chunks, a formal obstruction showing route-width-padded class/length
  metadata is already linear, constructive sentinel-chunk access/rank/select
  routes, a conservative raw `n + o(n)` block-primary bound, and conditional
  bounded-regime bridges for the local decoder, ambient route tables, and
  ambient compressed primary-budget join, and
  `RankSelectPublic` exposes the public Jacobson/Clark
  bitvector family theorem as
  `RankSelect.jacobsonClarkNPlusOConstantQuery` and its strengthened
  word-bounded profile
  `RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery`.
- `RMQ/Headlines.lean`: short aliases for the main public theorem surfaces,
  including `Headlines.exactRMQLowerBoundDoubledCatalanSlack`,
  `Headlines.rankSelectNPlusOConstantQuery`,
  `Headlines.rankSelectWordBoundedNPlusOConstantQuery`, and
  `Headlines.succinctRMQTwoNPlusOConstantQuery`.
- `RMQ/Archive/SelectObstructions.lean` and
  `RMQ/Archive/BPSpecializedCapstone.lean`: small checked archives for the
  retained obstruction witnesses and old BP-specialized relative-split
  capstone; `RMQ/Archive/SelectCompatibility.lean` keeps stable compatibility
  aliases, while superseded intermediate prototype surfaces are intentionally
  not anchored. These are opt-in through `RMQArchive.lean`, not imported by the
  main `RMQ` root.
- `RMQRankSelect.lean`: standalone rank/select spoke import root. It exposes
  the public bitvector spec plus the Jacobson/Clark construction as a
  plain-bitvector API. Its proof-support import closure still shares the
  succinct-space and shape/lower-bound infrastructure, but it does not expose
  an RMQ/LCA/Fischer-Heun backend or the final RMQ capstone as its public API.
- `RMQBPNavigation.lean`: standalone balanced-parentheses close-navigation
  spoke import root. It exposes the compact close/LCA navigation facade under
  `RMQ.BPNavigation`, plus the first rank/select-backed tree-navigation bridge
  (`closeOfInorderCosted`, `inorderOfCloseCosted`,
  `shapeAccessCloseRankProfile`). This is still not yet a full
  tree-navigation library API.
- `RMQUnionFind.lean`: standalone union-find spoke import root. It exposes the
  finite-partition specification, exact costed reference operations,
  parent-pointer forest refinement, union-by-rank/root-mass/rank-power
  checkpoints, full-compression find refinement, log-rank amortized checkpoint,
  first rank-bucket-width accounting checkpoint, and rank-slack compression
  kernel whose aggregate potential drop pays successful full-compression find
  slack up to constant credit. A follow-up checkpoint replaces the
  answer-shaped union delta with a coarse size-log union credit. The first
  multilevel Tarjan-style checkpoint separates cross-level rank gaps from
  within-level residual slack under an iterated-log rank schedule; the
  clean-credit follow-up removes the trace-dependent successful-find credit and
  replaces the whole-forest union credit with a local level-potential delta. It
  is followed by a phase-count profile whose successful-find credit depends on
  a global iterated-log phase count after residual rank slack is absorbed into
  the potential. The sharper level-index profile replaces that hidden full
  rank-slack layer with explicit `tarjanLevelPotential + tarjanResidualPotential`
  accounting and proves that the combined drop pays the original trace rank
  slack. A follow-up obstruction theorem shows this exact residual-as-difference
  design collapses back to rank slack under the natural sub-gap condition, so
  the true Tarjan step still needs a different recursively indexed residual. It
  does not yet prove Tarjan's inverse-Ackermann bound or a small uniform union
  credit.
- `VerifiedDS.lean`: thin neutral aggregate facade over the active public roots
  (`RMQ`, `RMQHub`, `RMQRankSelect`, `RMQBPNavigation`, and `RMQUnionFind`).
  This signals the broader verified-data-structures direction without renaming
  modules or changing citable RMQ theorem names.
- `RMQ/Core/SuccinctReduction.lean`: reduction-facing adapter from
  plus-minus-one RMQ backends over generated Euler-tour parentheses to the
  ordinary RMQ/LCA backend interfaces.
- `RMQ/Core/Microtable.lean`: shape-indexed local query offsets, the finite
  shape universe for block signatures, a proved raw shape-only microtable, and
  a certified microtable contract that lifts to an exact in-block `RMQBackend`.
- `RMQ/Core/CostKernels.lean`: costed direct window scan and raw microtable
  lookup, with erasure theorems and first cost formulas/bounds. Query/table
  lookup costs use a RAM model where indexed reads are unit-cost.
- `RMQ/Core/Recursion.lean`: Mathlib-free well-founded recursion over strictly
  shorter summary lists, concrete full-block minimum summaries, and lifting
  lemmas from summary candidates back to original-list candidates, including
  a generic recursive-middle hybrid combinator.
- `RMQ/Core/Schedule.lean`: stable block-boundary scheduling helpers shared by
  hybrid variants.
- `RMQ/Impl/LinearScan.lean`: simplest exact backend.
- `RMQ/Impl/PlusMinusOne.lean`: first verified plus-minus-one backend
  instance, plus the normalized delta-signature backend and its contract-level
  equivalence to the linear instance.
- `RMQ/Impl/SparseTable.lean`: sparse table cells, materialized table lookup,
  and backend proof.
- `RMQ/Impl/SparseTableInstrumented.lean`: first Array-backed sparse-table
  cell/row/query bridge in the traced RAM substrate, proving refinement to the
  verified List cell/row/query definitions plus derived trace bounds. Its
  query validity guard uses `Array.size`, and its memoized log-row build now
  has derived primitive-trace build and build-then-query theorems.
- `RMQ/Impl/SparseTableMemoCost.lean`: first cost-faithful sparse-table build
  layer, with memoized successor rows proved equivalent to recursive sparse
  rows, an exact-cost log-row builder for Fischer-Heun summaries, and query
  equivalence with the verified sparse table. The old Fischer-Heun summary
  query now goes through the stored Array-table adapter in
  `RMQ/Impl/SparseTableInstrumented.lean`.
- `RMQ/Impl/FischerHeunCost.lean`: exact finite microtable cost/count profile:
  raw shape lookup costs at most `blockSize + 1`, and the shape-table universe
  has exactly `shapeCount blockSize` entries, plus the Catalan envelope
  `shapeCount b <= 4^b` and the square-root table-count corollary
  `rawShapeTableCount b * rawShapeTableCount b <= n`. It also contains the
  assembled Fischer-Heun cost profile: linear preprocessing and constant
  supplied-query cost under the stated RAM/unit-cost indexed-access model,
  plus the canonical quarter-log block-size theorem for large inputs.
- `RMQ/Impl/FischerHeun.lean`: value-level Fischer-Heun assembly:
  materialized state with certified raw microtable, block-minimum summary, and
  summary sparse table; canonical build/query wrappers; and an exact backend
  proof that composes full-block boundary microtable lookups with the
  recursive-hybrid summary scheduler. It also includes a costed raw microtable
  construction that folds over shape rows and local-query slots, costed build
  erasure, supplied-state query cost erasure for freshly built states, and
  fresh-query cost/run theorems, plus an exact all-input wrapper that falls
  back to linear scan outside the canonical large-input regime. Same-block and
  final-boundary queries use padded local microtable lookups, yielding a
  constant supplied query bound for positive block sizes. The module also
  instantiates the lower-bound state-encoding interface with a
  Fischer-Heun-shaped state whose counted payload is separated from proof-only
  built-state fields.
- `RMQ/Impl/HybridBlock.lean`: block summaries, sparse middle query, public
  hybrid query, and backend proof.
- `RMQ/Impl/RecursiveHybrid.lean`: aligned query schedule and public
  self-recursive hybrid backend built with `recurseOnSummary`.
- `RMQ/Impl/RecursiveHybridCost.lean`: recursive-hybrid build/query cost
  recurrences, including the solved linear build bound
  `buildCost xs <= 2 * xs.length`.
- `RMQ/Impl/LCACost.lean`: costed Euler-trace construction, supplied
  LCA/RMQ-reduction query wrappers, and an explicit indexed-access
  LCA-via-RMQ query model that charges first-occurrence reads, a supplied RMQ
  query, and the returned-node read.
- `RMQ/Impl/LCAFischerHeun.lean`: exact LCA adapters obtained by composing
  generated Euler depths with canonical/all-input Fischer-Heun RMQ backends,
  plus a concrete large-regime indexed-query theorem charging at most `14`
  ticks for first-occurrence reads, the Fischer-Heun RMQ query, and the
  returned-node read.
- `RMQ/Impl/Equivalence.lean`: contract-level equality instantiations for the
  public RMQ backends, now including canonical and all-input Fischer-Heun.

## Build

The project is pinned to Lean `leanprover/lean4:v4.22.0`.

```powershell
lake build
```

Concise public-headline check:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/headline_check.ps1
```

Standalone rank/select spoke checks:

```powershell
lake build RMQRankSelect
lake env lean scripts/rank_select_axiom_check.lean
```

Standalone BP-navigation spoke checks:

```powershell
lake build RMQBPNavigation
lake env lean scripts/bp_navigation_axiom_check.lean
```

Standalone union-find spoke checks:

```powershell
lake build RMQUnionFind
lake env lean scripts/union_find_axiom_check.lean
```

Optional archive checks:

```powershell
lake build RMQArchive
lake env lean scripts/archive_axiom_check.lean
```

Checked external import examples:

```powershell
lake build RMQExamples
```

Full repository gate, matching the GitHub Actions CI job:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/gate.ps1
```

Useful proof-hygiene check:

```powershell
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQHub.lean RMQRankSelect.lean RMQArchive.lean RMQExamples.lean lakefile.toml
```

## Next Direction

The RMQ proof-of-concept is now past the main theorem capstone. Natural
follow-ups are polish, extraction, and the next spoke rather than another hidden
RMQ blocker:

- make an even flatter encoded/payload-only presentation of the BP-native
  succinct theorem;
- turn the shallow `RAM.Exec` trace model into a first-order interpreter if the
  next research target needs interpreter-level anti-vacuity;
- extract the reusable cost/refinement/lower-bound hub toward a CSLib-style
  library surface;
- refine the landed standalone Jacobson/Clark rank/select theorem toward
  concrete global routing over the ambient fixed-weight block-composition
  scaffold, consume the canonical eight-table route-layout constructor and
  route/class-length family promotion in a block decomposition/routing family,
  feed the log-sized sentinel chunk block-count budget into a concrete charged
  route-table family, replace the conservative raw-length primary bridge by
  the fixed-weight `log binomial + o(n)` primary block-code budget, discharge
  the route fields from charged routing tables rather than proof-only routes,
  and deepen
  the landed BP-navigation close/rank bridge into a fuller tree-navigation API;
  and
- deepen the new union-find spoke from specification/reference backend to
  forest refinement, union-by-rank, and path compression.

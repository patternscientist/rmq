# RMQ

A standalone Lean 4 formalization project for reusable range-minimum query
correctness results.

This repository started as a small extraction from a VeriBench-oriented RMQ
development. The code here is intentionally library-shaped rather than
benchmark-shaped: the goal is to factor reusable specifications, backend
contracts, and correctness lemmas that can support multiple RMQ algorithms.

For a family-level theorem inventory, dependency DAG, correctness/cost matrix,
and consolidated modeling notes, see
[`docs/FAMILY_SUMMARY.md`](docs/FAMILY_SUMMARY.md).

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
  no-premise `2*n - (2*log2(2*n+1)+2)` bit lower bound. A state-encoding
  adapter lets concrete built-state encoders inherit the same lower bound,
  and a canonical representative state encoding instantiates that adapter.
- `RMQ/Core/Succinct.lean`: exact list-backed rank/select primitives,
  balanced-parentheses predicates, model-level packed rank/select with
  unit-cost query theorems, and generated Euler-tour parentheses that are
  proved balanced and erase to the generated plus-minus-one depth trace.
- `RMQ/Core/SuccinctSpace.lean`: broadword/succinct-space theorem interfaces:
  Mathlib-free `o(n)` overhead accounting, payload-backed rank/select
  components, BP-native Cartesian shape payloads of exact length `2*n`, and a
  proved close-navigation RMQ adapter. `RMQ/Core/SuccinctFinal.lean` now
  consumes the concrete compact false-close/select witness and compact BP close
  directory in a payload-accounted `2*n + o(n), O(1)` BP-native theorem; the
  remaining succinct work is hardening the bounded-local-BP primitive and, if
  desired, giving an even flatter encoded/payload-only presentation.
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

Useful proof-hygiene check:

```powershell
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
```

## Next Direction

The forward LCA side is structural: a label-unique generated Euler trace plus
any exact RMQ backend over its depths induces an exact LCA backend. The reverse
side now has a concrete Cartesian tree proof: endpoint LCAs in the built
Cartesian tree are exactly leftmost RMQ witnesses, yielding
`Cartesian.certifiedReduction`.

The lower-bound frontier has moved past the Catalan count: the project now
proves the quadratic bound and the resulting fixed-length exact-RMQ
log-slack bit lower bound. The plus-minus-one and succinct layers now provide
verified hooks for normalized delta signatures, packed rank/select queries,
and generated balanced Euler-tour parentheses whose depth trace agrees with
the generated rose-tree Euler depths. The recursive canonical
representative-array theorem is now proved in `Core.Shape`: every Cartesian
shape has a canonical list witness of the right length whose computed shape is
exactly the original shape. A baseline canonical representative state encoder
now instantiates the lower-bound interface, and `Impl.FischerHeun` adds a
one-block Fischer-Heun-shaped encoder with a payload/proof-only split. The
shared `Core.TableModel` layer now names the indexed-read and payload-accounting
model those encoders and succinct adapters can refine through. `Impl.LCACost`
now instantiates that model for first-occurrence tables, Euler node/depth
arrays, and the supplied RMQ query composition. `Core.SuccinctReduction` now
adds the plus-minus-one/Euler-parentheses semantic bridge, and `Impl.LCACost`
can run the indexed query model through that bridge. `Impl.LCAFischerHeun`
now instantiates the same indexed query model with concrete canonical and
all-input Fischer-Heun RMQ backends. The next LCA targets are preprocessing
and storage accounting for the first-occurrence/node/depth tables, and a real
packed plus-minus-one RMQ query backend over Euler parentheses.

The recursive-hybrid build recurrence is now solved with an explicit linear
bound, and the Fischer-Heun shape-table count is now bounded by the
square-root budget under the base-2 condition `4*b <= log2 n`. The canonical
Fischer-Heun theorem now chooses `b = log2 n / 4` and proves the remaining
microtable and summary-log budgets automatically once `16 <= b`.

The current hard-target roadmap starts by grounding costs in a derived
primitive trace rather than handwritten unit-cost formulas. The first landing
point is `RMQ/Impl/SparseTableInstrumented.lean`, which replays sparse-table
cell construction, counted row pushes, memoized log-row building, and query
through Array operations and integer comparisons, and exposes a `StoredTable`
adapter for Array-backed tables refining List reference tables. It proves
`sparseRowArrayBuild_value_toList`, `sparseRowArrayBuild_steps_le`,
`query_refines_and_steps_le_seven`, and the memoized-build/query theorems
`memoBuild_refine_with_steps`, `memoBuild_and_query_refine_with_steps`, and
`memoQueryWithTracedBuild_refine_with_steps`; Fischer-Heun now consumes that
adapter for its stored summary table.

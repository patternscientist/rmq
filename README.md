# Verified Range-Minimum Query

[![CI](https://github.com/patternscientist/rmq/actions/workflows/ci.yml/badge.svg)](https://github.com/patternscientist/rmq/actions/workflows/ci.yml)

**TL;DR:** This project uses Lean to machine-check a classic optimal RMQ
story: after preprocessing an array, exact range-minimum queries can be answered
in constant modeled time from a Cartesian-shape payload of at most
`2*n + o(n)` bits,
and any fixed-length payload-only exact RMQ encoding needs
`2n - 1.5 log n - O(1)` bits. The same code base is now growing into a
verified advanced-data-structures testbed, with standalone rank/select,
balanced-parentheses navigation, and union-find spokes.

Range-minimum query (RMQ) asks for the leftmost position of the smallest value
in a subarray. The surprising theorem is not that RMQ can be solved, but that
the array values can be discarded: the Cartesian shape alone determines every
answer. This repository verifies that story end to end, including correctness,
modeled query cost, payload-bit accounting, a public succinct upper-bound
surface with a numeric doubled-Catalan slack comparison, and a separately cited
encoding-quantified information-theoretic lower-bound theorem.

For the current publication-oriented explanation aimed at mathematically mature
readers with little data-structures background, see
[`docs/digests/PROJECT_DIGESTION_CURRENT.md`](docs/digests/PROJECT_DIGESTION_CURRENT.md).
The deeper first-contact background note remains
[`docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md`](docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md).

## Why Care

RMQ is a small-looking problem that sits under several core data-structure
ideas: Cartesian trees, lowest-common-ancestor queries, Fischer-Heun
preprocessing, succinct tree navigation, and rank/select-style bitvector
indexing. A formally checked RMQ stack is therefore a good stress test for
verified data-structure infrastructure.

The main contribution here is not new paper mathematics. It is that the known
theory is connected in Lean *with its modeling assumptions made explicit and
audited* -- what counts as one stored bit, and what counts as one step, are Lean
objects that are checked, not informal promises. Concretely:

- many RMQ implementations satisfy one shared leftmost-minimum contract;
- RMQ and LCA are reduced to each other through verified tree/Euler/Cartesian
  machinery;
- the succinct upper bound has explicit payload accounting and constant modeled
  query cost, with payload bits separated from proof-only fields so no answer can
  be hidden in a free-to-read certificate; and
- the lower bound proves that the leading `2*n` payload term is optimal.

All of this is Mathlib-free: the project is pinned to Lean/Std plus `omega`,
with no `sorry`, custom axioms, `unsafe`, `partial`, or `noncomputable`
definitions in the checked source.

## Headline Theorems

The RMQ-only paper aliases live in
[`RMQ/Headlines/RMQ.lean`](RMQ/Headlines/RMQ.lean) and are imported by
`RMQPaper`. The aggregate full-repository alias barrel remains
[`RMQ/Headlines.lean`](RMQ/Headlines.lean); it explicitly adds
[`RMQ/Headlines/RMQCompatibility.lean`](RMQ/Headlines/RMQCompatibility.lean)
for checked historical profiles under `Legacy`/`Compatibility` names.

| Alias | Meaning |
| --- | --- |
| `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | Reader-facing theorem over ordinary `xs : List Int`: `buildPayload.length <= 2*n + overhead n` with `overhead = o(n)`; valid half-open queries return the exact leftmost RMQ answer, invalid or empty ranges return `none`, and modeled query cost is constant. |
| `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | Reader-facing no-synthetic execution story over ordinary `xs : List Int`, including the same public space inequality and range contract. Exact physical-word erasure is also conjoined directly in the paper main theorem; the construction is not padded to manufacture a size equality. |
| `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` | Paper-facing theorem consuming one global reviewer-manifest semantic packet, then combining the list theorem's amended at-most payload bound, `overhead = o(n)`, exact valid answers, current-query raw adequacy and occurrence provenance, the all-invalid none/empty/zero packet, translated supplied-store `.value` provenance, constant modeled query cost, and the final no-synthetic flat-payload trace story. |
| `RMQ.Headlines.listIntSuccinctRMQQueryCostedWithStoreEqQueryCostedOfFootprint` | List-facing supplied-store equality: under final footprint agreement with `SuccinctClassic.globalReadStore xs`, `SuccinctClassic.queryCostedWithStore xs store left right` is the same costed query as canonical `SuccinctClassic.queryCosted xs left right`. |
| `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal` | List-facing supplied-store exactness: if a caller-provided store agrees with `SuccinctClassic.globalReadStore xs` on the final checked footprint, valid half-open queries through `SuccinctClassic.queryCostedWithStore` erase to the exact leftmost `List Int` RMQ answer. |
| `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal` | List-facing supplied-store all-size cost transfer: under the same footprint agreement, the supplied-store query has modeled cost at most `SuccinctClassic.queryCost`. |
| `RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile` | Canonical construction-facing profile: doubled-Catalan space envelopes, the at-most `2*n + o(n)` canonical reviewer payload, exact physical-word erasure, direct positional physical backing for every successful read, exact queries through the same global trace, non-synthetic certificate weight equal to both trace length and its `Costed.cost`, and the uniform bound `142`. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | All-size execution-story theorem for the final succinct RMQ query: the costed query refines one globally segmented trace, every event is either a payload read or bounded word primitive, and every read agrees with one concrete global payload store. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory` | Store-extensional all-size execution story: any read store agreeing with the concrete global store on the emitted payload-read events validates the same final-query trace. |
| `RMQ.Headlines.succinctRMQCanonicalInteriorDirectoryProfileAllSize` | Canonical all-size interior profile: exactness, component store, execution footprint, successful-read backing, and reviewer-width guarantees. The current execution has the separate charged-trace cap `30`; `240` remains the transitional interface cap. |
| `RMQ.Headlines.succinctRMQCanonicalReviewerMachineWordsComponentSlice` | Exact physical machine-word placement of the canonical component after the counted prefix. |
| `RMQ.Headlines.succinctRMQCanonicalInteriorPhysicalFootprintFits` | Every physical address consumed by the canonical interior execution fits the pre-execution reviewer word width. |
| `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe` | Paper-facing theorem: the uniform canonical trace has charged-trace cost at most `142`. |
| `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostEqTraceLength` | Exact accounting bridge: modeled cost equals emitted charged-event trace length. |
| `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultEventReadWordOrWordRankOrWordSelect` | Every event actually emitted by the canonical whole-query trace is a payload read, word-rank, or word-select event. |
| `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqCost` | For the canonical no-synthetic trace, the `WordRAM.TraceEvent.nonSyntheticWeight` certificate sum equals the `Costed` cost of the same execution. |
| `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe142` | The non-synthetic-weighted actual emitted trace is bounded by `142`. |
| `RMQ.Headlines.succinctRMQSyntheticCostOnlyPrimitiveMemBreaksNonSyntheticWeightLengthEquality` | Counterfactual check: a synthetic event anywhere in a trace makes its `nonSyntheticWeight` sum differ from its length. |
| `RMQ.Headlines.succinctRMQChargedTraceCostAlgebra` | Component cap `2*select13 + (2*rank4 + 2*fringe4 + interior30) + rank4`; the actual-event bridge above connects it to execution. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory` | Uniform structural execution story with direct same-block decoding and canonical component-store cross-block replay. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | No-synthetic all-size execution story: the same bounded global trace contains no dedicated synthetic cost-only marker events. |
| `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | Canonical reviewer-payload no-synthetic execution story: successful reads are counted in one exhaustive typed 20-source universe, including canonical close, and cross-block replay is uniform for all sizes. |
| `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical` | Genuine supplied flat-physical execution: the existing supplied-store evaluator reads the caller's flat store through checked address translation and refines the canonical logical execution, preserving value, cost, ordered successes/failures, repeated reads, and footprint. |
| `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionEqOfOrderedFootprint` | Agreement on the first physical execution's consumed ordered footprint determines the complete physical execution. |
| `RMQ.Headlines.succinctRMQReviewerPhysicalValueFromSuppliedStore` | Projection theorem: the flat physical answer is exactly the existing translated supplied-store evaluator answer. |
| `RMQ.Headlines.succinctRMQReviewerPhysicalValueDependency` | If translated supplied-store evaluator values differ, the corresponding flat-physical `.value` projections differ. |
| `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance` | Every indexed read in the closed global trace retains that same global occurrence, its program instruction occurrence, the prefix-folded pre-state, local position, exact component invocation parameters, source, and multiplicity-preserving offset. |
| `RMQ.Headlines.succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence` | Every counted source is successfully read by some actual closed whole-query execution under a valid ordinary `List Int` query. |
| `RMQ.Headlines.succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence` | Select, rank, and canonical-close consumers each have a successful closed-valid occurrence through their exact invocation leaf. |
| `RMQ.Headlines.succinctRMQReviewerFreshUnusedSourceNoProducer` | Fresh segment `21` is rejected by the same common closed-valid-occurrence predicate used by accepted sources; the checked positive-to-mutation bridge accounts for successful versus arbitrary-result reads. |
| `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy` | Query-independent semantic-adequacy packet: every counted source and shared-BP consumer has some successful closed-valid execution witness, successful `P` implies the common mutation predicate `Q`, and fresh segment `21` fails `Q`. It does not say the current query reads every source. |
| `RMQ.Headlines.listIntSuccinctRMQInvalidPhysicalSemantics` | Invalid public inputs have one guarded none/empty/zero logical and physical execution for every supplied store. |
| `RMQ.Headlines.listIntSuccinctRMQQueryCostedInvalid` | One public validity boundary rejects every invalid or empty range; specialized empty, reversed, and out-of-bounds aliases are exported beside it. |
| `RMQ.Headlines.concreteBPCloseNavigationProfile` | Concrete payload-backed BP close-navigation profile: relative-split false-select/rank-close plus compact relative-rmM close/LCA, with `2*n + o(n)` payload, constant modeled query cost, exact Cartesian-shape RMQ answer semantics, and machine-word-bounded component payload reads. |
| `RMQ.Headlines.concreteBPCloseNavigationGlobalPayloadStoreExecutionStory` | Concrete BP close-navigation execution story: the same query is represented by a globally segmented `WordRAM.TraceResult`, with payload reads matched against one concrete store and successful reads backed by counted component stores. |
| `RMQ.Headlines.concreteBPCloseNavigationGlobalPayloadStoreBoundedExecutionStory` | Bounded concrete BP close-navigation execution story: the trace/store packet also has finite trace-local bounds for read addresses and word-primitive operands/results. |
| `RMQ.Headlines.concreteSuccinctBPTreeNavigationGlobalPayloadStoreBoundedExecutionStory_currentCloseStoreObstruction` | Checked obstruction: the current concrete close/LCA store cannot be reused as the matching-open leg for a fuller succinct BP tree-navigation execution story. |
| `RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` | Conditional component-level interpreter-backed BP close-navigation profile, parameterized by a supplied word-bounded sampled encoded close-navigation family. |
| `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | Coefficient-correct Catalan lower-bound slack, stated in doubled integer form. |
| `RMQ.Headlines.rankSelectNPlusOConstantQuery` | Standalone Jacobson/Clark-style plain-bitvector rank/select with `n + o(n)` payload and constant modeled query cost. |
| `RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery` | The rank/select profile strengthened with machine-word-bounded concrete payload reads. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | Fixed-weight compressed/FID rank/select family with fixed-weight primary payload plus `o(n)` auxiliary payload and constant modeled access/rank/select. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | Interpreter-backed replay of the fixed-weight compressed/FID rank/select family: same payload/profile shape, with access/rank/select reads routed through `WordRAM` bridges. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile` | Fused fixed-weight compressed/FID rank/select capstone: compressed payload plus `o(n)`, exact constant-query access/rank/select, interpreted replay, one target-independent global payload store, and bounded trace-local event widths. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreNoSyntheticFusedProfile` | Strengthened compressed/FID rank/select capstone: the fused global payload-store story also proves successful read events are backed by component stores and no synthetic cost-only events occur. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory` | Target-independent global-store execution story for compressed/FID rank/select: for fixed `bits`, shared access plus rank false/true and select false/true traces all read from one concrete payload store. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory` | Bounded target-independent global-store execution story for compressed/FID rank/select: the shared access/rank/select traces also carry trace-local finite widths bounding payload-read addresses and word-primitive operands/results. |

The provenance layer separates two semantic obligations: indexed occurrence
provenance preserves invocation parameters for the exact current query, while
a global packet proves every counted source has some actual successful
closed-valid query witness under the same operational relation used to reject
segment `21`. The canonical reviewer route has one live public payload,
`SuccinctClassic.buildPayload`. One pre-execution reviewer physical word list
erases exactly to that payload. The existing supplied-store evaluator runs
through a checked adapter that reads the supplied flat store at translated
physical addresses; canonical execution refines the logical execution while
preserving decoded result, modeled cost, ordered trace (including repeated and
failed reads), and the execution-derived footprint. Its query-independent width is
`machineWordBits (400000 * (n + 1))`, with a checked linear capacity bound and
an explicit `O(log (n + 2))` inequality.

The supplied-store theorem uses the execution's ordered read footprint, retaining
repeated and failed reads. Agreement there determines the complete physical
`TraceResult`. Answer dependency is separately stated at `.value`: physical
execution returns the translated supplied-store evaluator value, and a checked
decisive singleton corruption changes `some 0` to `none` while a
trace-preserving value-ignore mutant does not. Operational checks also reject
dead-source addition, used-source removal, and mismatched consumer labels.
Occurrence evidence starts from a global `getElem?` witness and retains
the same position through the program instruction, folded pre-state, local
component occurrence, and exact select/rank/close parameters. A checked
singleton regression keeps the equal events at global positions `0` and `12`
as distinct obligations. The source witnesses use actual successful closed
valid executions, including symbolic large witnesses for sources `12`--`19`;
component may-read and earlier event-value facts remain compatibility facts. The
current charged-trace cap is `142` (the retired event-silent-fringe cap `76` is frozen as `canonicalSilentFringeQueryCost`); detailed earlier cost and dispatch
chronology lives only in the
[`compatibility history`](docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md)
and has no reverse edge into the reviewer route.

The construction-level theorem names are intentionally verbose, so that the
model assumptions and dependency path remain inspectable. See
[`docs/TRUST_AUDIT_PACKET.md`](docs/TRUST_AUDIT_PACKET.md) for the alias chain,
the theorem shape, and curated `#print axioms` checks.

For a concise repository orientation by import root, theorem spine, proof-core
cluster, compatibility shim, archive, example, and validation code, see
[`docs/CODE_MAP.md`](docs/CODE_MAP.md).

## Public Import Roots

```lean
import RMQPaper         -- narrow RMQ paper theorem root
import RMQ              -- RMQ/LCA family and succinct RMQ capstone
import RMQHub           -- reusable cost/RAM/refinement/amortized/lower-bound hub
import RMQRankSelect    -- standalone rank/select spoke
import RMQBPNavigation  -- balanced-parentheses navigation spoke
import RMQUnionFind     -- union-find specification and forest-refinement spoke
import VerifiedDS       -- thin aggregate facade over the active public roots
import VerifiedDS.Hub
import VerifiedDS.RMQ
import VerifiedDS.RankSelect
import VerifiedDS.BPNavigation
import VerifiedDS.UnionFind
```

`RMQPaper` is the reviewer-clean paper root: it imports the RMQ-only headline
surface without standalone rank/select public spokes, standalone BP-navigation
public spokes, union-find, archive roots, proposal/legacy/compat barrels, or
old implementation roots. `RMQ` remains the stable artifact name for the
broader current theorem inventory.
`VerifiedDS` and its role modules are deliberately only facades for now: they
signal the broader library direction without forcing a namespace or repository
migration before the spoke APIs settle.

## What Is Proved

For external readers, start with [`docs/WHAT_IS_PROVED.md`](docs/WHAT_IS_PROVED.md).
For the full theorem inventory and dependency map, see
[`docs/FAMILY_SUMMARY.md`](docs/FAMILY_SUMMARY.md).
For the measured paper-root import closure, see
[`docs/RMQ_IMPORT_CLOSURE.md`](docs/RMQ_IMPORT_CLOSURE.md).
For tiny checked examples of the public surfaces, see
[`RMQExamples/Concrete.lean`](RMQExamples/Concrete.lean).

At a high level, the repository currently includes:

- exact RMQ backends: linear scan, plus-minus-one RMQ, sparse table, hybrid
  block RMQ, recursive hybrid RMQ, certified microtables, Fischer-Heun-style
  structures, and the final succinct Cartesian-shape RMQ profile, now with a
  direct public theorem over ordinary `List Int` inputs;
- RMQ/LCA reductions over rose trees, Euler tours, Cartesian trees, and
  balanced-parentheses representations;
- an information-theoretic RMQ lower-bound framework, including the sharpened
  Catalan slack equivalent to `2n - 1.5 log n - O(1)`;
- a payload-accounted BP-native succinct RMQ upper bound with payload length at
  most `2*n + o(n)` and constant modeled query cost;
- an interpreter-backed final succinct RMQ query surface whose all-size
  execution story emits one global `WordRAM.TraceEvent` stream; every event is
  either a payload read or a bounded word primitive, and every read is checked
  against one concrete payload store;
- a standalone rank/select spoke with public Jacobson/Clark-style profiles, a
  concrete fixed-weight compressed/FID capstone family surface, and an
  interpreter-backed replay of that compressed/FID query path; and
- a union-find spoke with finite-partition specs, parent-pointer forest
  refinement, union-by-rank invariants, full-compression refinement, and early
  amortized-analysis checkpoints on the path toward Tarjan-style bounds.

## Model Scope

The cost statements are model-relative. They use a small `Costed` layer and a
traced RAM substrate with unit-cost indexed reads, word operations, branches,
comparisons, and table accesses where explicitly modeled. They are not claims
about Lean's executable `List` runtime.

The space statements count payload bits separately from proof-only fields and
certificates. The succinct RMQ theorem counts the balanced-parentheses shape
payload plus `o(n)` auxiliary payload; proof objects that certify correctness
are not counted as data-structure storage.

For the trust base, non-claims, and exact verification commands, see
[`docs/TRUST_BASE.md`](docs/TRUST_BASE.md) and
[`docs/TRUST_AUDIT_PACKET.md`](docs/TRUST_AUDIT_PACKET.md).

## Build And Verify

The project is pinned to Lean `leanprover/lean4:v4.22.0`.

```powershell
lake build
```

Full repository gate, matching the GitHub Actions CI job:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

Paper-artifact reproduction gate:

```bash
scripts/reproduce_artifact.sh
```

Concise public-headline check:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\headline_check.ps1
```

Standalone spoke checks:

```powershell
lake build RMQRankSelect
lake env lean scripts\rank_select_axiom_check.lean

lake build RMQBPNavigation
lake env lean scripts\bp_navigation_axiom_check.lean

lake build RMQUnionFind
lake env lean scripts\union_find_axiom_check.lean
```

Useful proof-hygiene scan:

```powershell
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQHub.lean RMQRankSelect.lean RMQArchive.lean RMQExamples.lean lakefile.toml
```

## Background And References

The mathematics is classical; the contribution is the audited Lean connection.
Classical sources behind each piece (the Lean code re-derives, rather than
imports, this material):

- **RMQ <-> LCA, constant-time RMQ:** Gabow-Bentley-Tarjan (1984); Bender &
  Farach-Colton, *The LCA problem revisited* (2000).
- **Cartesian trees:** Vuillemin (1980).
- **Succinct trees / balanced parentheses:** Jacobson (1989); Munro & Raman
  (2001).
- **rank/select in `o(n)` extra bits:** Jacobson (1989); Clark (1996); Munro
  (1996).
- **Compressed bitvectors / FID:** Raman, Raman & Rao, "RRR" (2002) -- the
  `log2 C(n,k) + o(n)` entropy bound behind the compressed rank/select frontier.
- **Fischer-Heun RMQ:** Fischer & Heun (2011).
- **Union-find / inverse Ackermann:** Tarjan (1975) -- the `O(alpha(n))` amortized
  bound the union-find spoke is scaffolding toward.

## Documentation Map

- [`docs/CODE_MAP.md`](docs/CODE_MAP.md): concise orientation map for public
  roots, final succinct RMQ theorem/model-adequacy spines, proof-core modules,
  compatibility shims, archive files, examples, and validation code.
- [`docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md`](docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md):
  immutable historical Lean-club snapshot; exact frozen lines are marked and
  remain outside the current paper surface.
- [`docs/digests/PROJECT_DIGESTION_CURRENT.md`](docs/digests/PROJECT_DIGESTION_CURRENT.md):
  current publication-oriented project digestion. Its documentary headline
  identifiers are checked under both the broad and `RMQPaper` imports; dated
  fast-regime discussion is explicitly labeled compatibility history.
- [`docs/ADD_PROVENANCE.md`](docs/ADD_PROVENANCE.md): public provenance note for
  the audit-driven development workflow; ADD is process evidence, not a proof
  object or trust base.
- [`docs/PAPER_CLAIM_CORRESPONDENCE.md`](docs/PAPER_CLAIM_CORRESPONDENCE.md):
  reviewer-grade paper claim correspondence table with Lean aliases, source
  theorem names, source files, and exact check commands.
- [`docs/PAPER_RELATED_WORK.md`](docs/PAPER_RELATED_WORK.md): paper-ready
  related-work draft and limitations framing for a formalization submission.
- [`docs/WHAT_IS_PROVED.md`](docs/WHAT_IS_PROVED.md): compact scope summary.
- [`docs/TRUST_AUDIT_PACKET.md`](docs/TRUST_AUDIT_PACKET.md): skeptical-review
  packet for the headline theorem.
- [`docs/WORD_RAM_REVIEW_PACKET.md`](docs/WORD_RAM_REVIEW_PACKET.md): focused
  review packet for the first-order Word-RAM anti-oracle boundary.
- [`docs/TRUST_BASE.md`](docs/TRUST_BASE.md): dependency policy, model
  glossary, and verification commands.
- [`docs/FAMILY_SUMMARY.md`](docs/FAMILY_SUMMARY.md): full theorem inventory,
  dependency DAG, and per-structure status matrix.
- [`docs/RANK_SELECT_FRONTIER.md`](docs/RANK_SELECT_FRONTIER.md): standalone
  rank/select status and compressed/FID frontier.
- [`docs/UNION_FIND_FRONTIER.md`](docs/UNION_FIND_FRONTIER.md): union-find
  status and amortized-analysis frontier.
- [`docs/REPOSITORY_STRATEGY.md`](docs/REPOSITORY_STRATEGY.md): why this repo
  is still named `rmq`, why `VerifiedDS` is only a facade for now, and when a
  future umbrella package would make sense.
- [`docs/README.md`](docs/README.md): documentation index.

## Current Development Docket

The RMQ capstone is in place with the uniform canonical reviewer route and its
principled all-size charged-trace cap `142`.
Earlier cost and dispatch statements remain in the explicit
[`compatibility history`](docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
The development frontier is now to
package, calibrate, and reuse the infrastructure:

1. deepen balanced-parentheses navigation into a fuller tree-navigation API and
   continue turning useful component traces into public store-backed execution
   stories where that materially clarifies theorem surfaces;
2. push the union-find spoke from the current sequence/event scorecard toward a
   true inverse-Ackermann amortized theorem over strict residual events; and
3. have E1 define a richer instruction semantics and prove that it simulates
   the same canonical execution while charging controller work; the current theorem deliberately
   provides no parallel controller-operation vocabulary, and M1's
   serialized-payload query and complete preprocessing obligations remain
   separate; and
4. promote shared cost, refinement, lower-bound, and amortized-analysis pieces
   into a more neutral library surface only when concrete reuse demands it.

License: Apache-2.0; see [`LICENSE`](LICENSE).

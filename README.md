# Verified Range-Minimum Query

[![CI](https://github.com/patternscientist/rmq/actions/workflows/ci.yml/badge.svg)](https://github.com/patternscientist/rmq/actions/workflows/ci.yml)

**TL;DR:** This project uses Lean to machine-check a classic optimal RMQ
story: after preprocessing an array, exact range-minimum queries can be answered
in constant modeled time from a Cartesian-shape payload of `2*n + o(n)` bits,
and any fixed-length payload-only exact RMQ encoding needs
`2n - 1.5 log n - O(1)` bits. The same code base is now growing into a
verified advanced-data-structures testbed, with standalone rank/select,
balanced-parentheses navigation, and union-find spokes.

Range-minimum query (RMQ) asks for the leftmost position of the smallest value
in a subarray. The surprising theorem is not that RMQ can be solved, but that
the array values can be discarded: the Cartesian shape alone determines every
answer. This repository verifies that story end to end, including correctness,
modeled query cost, payload-bit accounting, and a separately proved
encoding-quantified information-theoretic lower bound.

For a further explanation aimed at mathematically mature
readers with little data-structures background, see
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

Short public aliases live in [`RMQ/Headlines.lean`](RMQ/Headlines.lean).

| Alias | Meaning |
| --- | --- |
| `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery` | Reader-facing theorem over ordinary `xs : List Int`: build a payload of length `2*n + o(n)` bits and answer valid half-open RMQ queries exactly, with leftmost ties, within constant modeled query cost. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` | BP-native succinct RMQ with exact queries, `2*n + o(n)` payload bits, constant modeled query cost, paired with the separately proved encoding-quantified lower bound. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted` | Whole-query-interpreted variant of the final BP-native succinct RMQ capstone: same theorem shape, with the final query control represented by a closed first-order program whose leaves are interpreted close-select, compact close/LCA, and register-backed answer-rank operations. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace` | Unified-`WordRAM.TraceEvent` variant of the same capstone: the final query emits one trace stream, with close-select, answer-rank, and compact-close rank-seed reads replayed as structural payload/register traces. |
| `RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime` | Large-regime WordRAM variant: same two-sided theorem shape, with an explicit size premise that routes the compact close/LCA leg through structural local/fringe/interior trace replay rather than the all-size fallback. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExecutionStory` | All-size execution-story theorem for the final succinct RMQ query: the costed query refines one globally segmented trace, every event is either a payload read or bounded word primitive, and every read agrees with one concrete global payload store. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreExtensionalExecutionStory` | Store-extensional all-size execution story: any read store agreeing with the concrete global store on the emitted payload-read events validates the same final-query trace. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreBoundedExecutionStory` | Bounded all-size execution story: the global trace also carries a finite trace-local bit width bounding every payload-read address and every natural operand/result exposed by word primitives. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreAllSizeStructuralExecutionStory` | All-size structural execution story: the zero-block same-block and cross-block interior close-navigation leaves are replayed by payload-backed structural traces. |
| `RMQ.Headlines.succinctRMQGlobalPayloadStoreNoSyntheticExecutionStory` | No-synthetic all-size execution story: the same bounded global trace contains no dedicated synthetic cost-only marker events. |
| `RMQ.Headlines.succinctRMQFlatPayloadStoreNoSyntheticExecutionStory` | Flat-payload no-synthetic execution story: the final query reads from one query-independent flat layout with component/offset backing evidence for successful reads. |
| `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory` | Large-regime companion: under the explicit size premise, the compact close/LCA leg uses the positive-block local/fringe/interior structural replay rather than the all-size fallback. |
| `RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory` | Bounded large-regime companion to the global-store execution story. |
| `RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery` | Conditional component-level interpreter-backed BP close-navigation profile, parameterized by a supplied word-bounded sampled encoded close-navigation family. |
| `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` | Coefficient-correct Catalan lower-bound slack, stated in doubled integer form. |
| `RMQ.Headlines.rankSelectNPlusOConstantQuery` | Standalone Jacobson/Clark-style plain-bitvector rank/select with `n + o(n)` payload and constant modeled query cost. |
| `RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery` | The rank/select profile strengthened with machine-word-bounded concrete payload reads. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile` | Fixed-weight compressed/FID rank/select family with fixed-weight primary payload plus `o(n)` auxiliary payload and constant modeled access/rank/select. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile` | Interpreter-backed replay of the fixed-weight compressed/FID rank/select family: same payload/profile shape, with access/rank/select reads routed through `WordRAM` bridges. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreFusedProfile` | Fused fixed-weight compressed/FID rank/select capstone: compressed payload plus `o(n)`, exact constant-query access/rank/select, interpreted replay, one target-independent global payload store, and bounded trace-local event widths. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreExecutionStory` | Target-independent global-store execution story for compressed/FID rank/select: for fixed `bits`, shared access plus rank false/true and select false/true traces all read from one concrete payload store. |
| `RMQ.Headlines.rankSelectCompressedFIDFixedWeightGlobalPayloadStoreBoundedExecutionStory` | Bounded target-independent global-store execution story for compressed/FID rank/select: the shared access/rank/select traces also carry trace-local finite widths bounding payload-read addresses and word-primitive operands/results. |

The construction-level theorem names are intentionally verbose, so that the
model assumptions and dependency path remain inspectable. See
[`docs/TRUST_AUDIT_PACKET.md`](docs/TRUST_AUDIT_PACKET.md) for the alias chain,
the theorem shape, and curated `#print axioms` checks.

## Public Import Roots

```lean
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

`RMQ` remains the stable artifact name for the current theorem inventory.
`VerifiedDS` and its role modules are deliberately only facades for now: they
signal the broader library direction without forcing a namespace or repository
migration before the spoke APIs settle.

## What Is Proved

For external readers, start with [`docs/WHAT_IS_PROVED.md`](docs/WHAT_IS_PROVED.md).
For the full theorem inventory and dependency map, see
[`docs/FAMILY_SUMMARY.md`](docs/FAMILY_SUMMARY.md).
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
- a payload-accounted BP-native succinct RMQ upper bound with `2*n + o(n)`
  payload and constant modeled query cost;
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

- [`docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md`](docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md):
  stress-tested Lean-club explanation of the current project state.
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

The RMQ capstone is in place. The next development frontier is to reuse and
stress-test the infrastructure:

1. deepen balanced-parentheses navigation into a fuller tree-navigation API and
   continue turning useful component traces into public store-backed execution
   stories where that materially clarifies theorem surfaces;
2. push the union-find spoke from the current sequence/event scorecard toward a
   true inverse-Ackermann amortized theorem over strict residual events; and
3. promote shared cost, refinement, lower-bound, and amortized-analysis pieces
   into a more neutral library surface only when concrete reuse demands it.

License: Apache-2.0; see [`LICENSE`](LICENSE).

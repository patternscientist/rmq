# Deep Project Digestion: 2026-06-28

Audience: a mathematically mature Lean-club reader who may know what a theorem
prover is, but who is not assumed to know RMQ, LCA, rank/select, balanced
parentheses, monads, word-RAM models, succinct data structures, or amortized
analysis.

Status: this digest describes `main` at `457ac44` on 2026-06-28. It is a
teaching document, not a replacement for Lean. The Lean files, build targets,
and axiom-check scripts remain the source of truth.

## One-Screen Summary

This project proves a verified range-minimum-query theorem in Lean and uses the
same infrastructure to grow two new verified data-structure spokes.

Range-minimum query, or RMQ, asks for the leftmost minimum value in a subarray.
The central mathematical fact is that all RMQ answers are determined by the
array's Cartesian tree shape. That shape can be written as balanced parentheses
using exactly `2*n` bits for `n` array positions. With smaller auxiliary
rank/select and close-navigation tables, the project proves exact RMQ queries
with `2*n + o(n)` payload bits and constant modeled query cost. It also proves
the matching leading lower bound from Catalan counting.

The public RMQ headline is:

```lean
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
```

which abbreviates:

```lean
RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
```

The project is now broader than RMQ. `RMQRankSelect` is a standalone
rank/select spoke; `RMQBPNavigation` exposes the balanced-parentheses
navigation layer used by the RMQ capstone; and `RMQUnionFind` is the first
non-succinct spoke, focused on refinement and amortized analysis.

## What Changed Conceptually In The Current Public State

The RMQ capstone story is stable. The newest conceptual movement is in the two
spokes.

Rank/select moved from "we have many fixed-weight components" toward "the
global compressed/FID accounting has a real log-chunk primary bridge." The
project now proves that sentinel log chunks do not waste the fixed-weight
information budget by more than `o(n)`, and it exposes a split-width table/RAM
route-directory surface so route metadata and local class/length metadata do
not have to share one overwide field size. The remaining gap is a concrete
family instantiation, not the primary enumerative budget.

Union-find moved from rank-slack amortization toward Tarjan-shaped scaffolding.
The proof now has explicit level, clean-credit, phase-count, and level-index
potential profiles. It also has a formal warning sign:
`tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le` shows that
one natural residual definition collapses back to ordinary rank slack. The
remaining gap is the true indexed residual counter needed for an
inverse-Ackermann theorem.

## The Import Roots

Use these roots to inspect the public surface:

```lean
import RMQ              -- RMQ/LCA family and succinct RMQ capstone
import RMQHub           -- reusable cost/RAM/refinement/table/lower-bound layers
import RMQRankSelect    -- standalone rank/select spoke
import RMQBPNavigation  -- balanced-parentheses navigation spoke
import RMQUnionFind     -- union-find specification and forest-refinement spoke
import VerifiedDS       -- thin aggregate facade over the public roots
```

`VerifiedDS.lean` imports those roots and deliberately does little else. The
repo is still named RMQ because the RMQ capstone is the stable, citable artifact
and most theorem names are still RMQ-shaped. `VerifiedDS` is the staging facade
for the broader verified-data-structures direction.

## 1. What Is This Project?

In plain English: this repository asks whether a textbook data-structure
theorem can be connected end to end in Lean, with the theorem's model
assumptions visible instead of implicit.

The RMQ capstone connects five kinds of statements.

1. A reference specification: what answer is correct?
2. A shape theorem: why can the values be discarded?
3. An upper bound: how many payload bits are stored, and how does a query use
   them?
4. A lower bound: why can no exact encoding beat the leading `2*n` term?
5. A cost model: what counted operations justify the phrase "constant query"?

The repository then reuses the same proof vocabulary for rank/select,
balanced-parentheses navigation, and union-find.

## 2. What RMQ Means

The core RMQ contract lives in `RMQ/Core/Spec.lean`.

For a list `xs : List Int`, a valid query is a nonempty half-open range:

```lean
RMQ.ValidRange xs left right
```

meaning `left < right` and `right <= xs.length`.

The correct answer is described by:

```lean
RMQ.LeftmostArgMin xs left right idx
```

This says:

- `idx` lies in `[left, right)`;
- `xs[idx]` is no greater than every value in the range; and
- every earlier index in the range has a strictly larger value.

The strict earlier-index clause is the leftmost tie rule. If the range contains
two equal minima, the smaller index wins.

Example:

```text
xs = [3, 1, 4, 1, 5]
query [0, 4) = index 1
query [2, 5) = index 3
```

This is a data-structure theorem rather than a programming trick because the
goal is not merely to compute one answer. The theorem asks for a representation
that preprocesses the input once, stores very few bits, and answers every valid
future query with a fixed modeled cost.

## 3. Why Cartesian Shape Determines RMQ

A Cartesian tree is built from an array by making the leftmost minimum the root,
then recursively building the left and right subtrees from the subarrays on each
side.

For `[3, 1, 4, 1, 5]`, the root is the first `1`, at index `1`. The left
subtree comes from `[3]`; the right subtree comes from `[4, 1, 5]`, whose root
is the `1` at index `3`.

The key fact is:

> For any interval of array positions, the RMQ answer is the node in the
> Cartesian tree that is the lowest common ancestor of the interval's endpoint
> nodes, with the repository's leftmost tie convention.

Lowest common ancestor, or LCA, means the deepest tree node that is an ancestor
of both queried nodes. The word "deepest" is tree language for "furthest from
the root." Since the Cartesian tree root of any interval is the interval's
leftmost minimum, the tree shape records the comparisons needed for all
intervals.

The important point is that the actual integer values are no longer needed once
the Cartesian shape is known. Any representative array with the same shape has
the same RMQ answers. The Lean development proves this through the Cartesian
and RMQ/LCA bridge modules, with public inventory under
`docs/FAMILY_SUMMARY.md` and the final shape-facing query theorem in
`RMQ.Core.SuccinctFinal`.

## 4. What `2*n + o(n), O(1)` Says

For an input of length `n`, the BP-native succinct RMQ theorem says:

- the stored shape code has length exactly `2*n`;
- the auxiliary payload is `o(n)`;
- every valid RMQ query returns the same index as the reference scan; and
- every query has a fixed bound in the project's modeled cost system.

The public theorem includes the exact payload statement:

```lean
(concreteBPNativeSuccinctRMQPayload accessFamily shape).length =
  2 * n + concreteBPNativeSuccinctRMQOverhead
    genericSparseExceptionBPCloseAccessOverhead n
```

and the exactness statement:

```lean
(concreteBPNativeSuccinctRMQQueryCosted
  accessFamily shape left (left + len)).erase =
  some (scanWindow shape.representative left len)
```

Here `scanWindow` is the reference answer over a canonical representative array
for the shape. The theorem is saying that the succinct query agrees with that
reference answer for every valid nonempty query.

The `O(1)` part is represented by a concrete cost bound over
`concreteBPNativeSuccinctRMQQueryCosted`. This is a model-level bound, not a
benchmark statement about Lean execution.

## 5. Why The Lower Bound Matches

The lower-bound alias is:

```lean
RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
```

which abbreviates:

```lean
RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack
```

The idea is counting. Different Cartesian shapes can force different RMQ answer
tables. An exact RMQ encoding for all arrays of size `n` must distinguish all
the relevant shapes. The number of binary tree shapes of size `n` is Catalan,
whose logarithm has leading term `2*n` bits with a smaller logarithmic
correction.

The Lean theorem states the slack in a doubled integer form, avoiding rational
coefficients in the public statement. Informally, it corresponds to the familiar
leading lower bound:

```text
2n - 1.5 log n - O(1)
```

The upper theorem stores `2*n + o(n)` bits. The lower theorem says the leading
`2*n` cannot be beaten for exact fixed-length RMQ state encodings. That is the
match: not exact equality of every lower-order term, but equality of the
dominant payload term.

## 6. What Modeled Cost Means

The project distinguishes three things that are easy to conflate:

- total correctness: does the returned answer equal the reference answer?
- modeled complexity: how many abstract operations does the model count?
- executable runtime: how fast does Lean's compiled code run?

The theorem statements here are about the first two. They are not native
runtime claims.

The basic cost carrier is `RMQ.Costed`, from `RMQ/Core/Cost.lean`. A value
`x : Costed a` contains:

- `x.value`, the returned value; and
- `x.cost`, a natural number representing modeled cost.

`x.erase` forgets the cost and keeps the value. Exactness theorems usually talk
about `erase`; cost theorems talk about `cost`.

`RMQ.RAM.Exec`, from `RMQ/Core/RAM.lean`, is a trace model. It records primitive
operations such as reads, writes, branches, comparisons, and word rank/select
operations. Its cost is the length of the trace. The file provides a conversion
from `RAM.Exec` to `Costed`.

A word-RAM-style assumption is a mathematical assumption about this model: a
bounded machine word read, comparison, branch, or word-level rank/select
primitive costs one modeled step when the theorem has proved the read comes
from counted payload and the word fits the declared word-size bound. This is
how succinct data-structure theorems usually talk about constant-time bit
navigation, but here the assumption is kept visible in theorem names and docs.

If you have seen monads, `Costed.bind` and `RAM.Exec.bind` are sequential
composition. If you have not, read them as "do the first computation, then feed
its value into the next one, and add the recorded costs."

## 7. Payload Bits Versus Proof-Only Fields

Succinct data structures are about stored bits. Lean structures, however, can
also carry proofs. A proof field can certify that a table is sorted, bounded, or
exact. That proof is useful to Lean, but it is not a bit stored in the modeled
data structure unless a theorem explicitly counts it as payload.

This project therefore separates:

| Category | Meaning |
| --- | --- |
| Payload bits | Modeled stored bits, such as BP shape bits, rank/select directory bits, route tables, and bounded payload words. |
| Proof-only fields | Invariants, exactness proofs, and side conditions used by Lean to verify the construction. |
| Modeled cost | Natural-number costs attached by `Costed` or derived from `RAM.Exec` traces. |
| Lean runtime nonclaims | The project does not claim that Lean's `List` evaluator or proof-carrying structures run in the modeled time. |

This distinction protects the theorem from a common failure mode: hiding a
semantic oracle in a proof field or callback and charging it as if it were one
table read. Several interfaces in the repo are intentionally labeled as weak
composition surfaces until a concrete payload-backed inhabitant is supplied.

## 8. Rank/Select And Balanced Parentheses In The RMQ Proof

The RMQ capstone stores a Cartesian tree shape as balanced parentheses.

To answer a query `[left, right)`, the final BP-native query performs the
following conceptual route:

1. Use false-select to find the close parenthesis for the inorder node `left`.
2. Use false-select to find the close parenthesis for the inorder node
   `right - 1`.
3. Use the compact BP close/LCA directory to find the close parenthesis of the
   LCA of those endpoints.
4. Use false-rank at `answerClose + 1` to convert that close parenthesis back
   into an inorder node index.

The definition carrying this path is:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted
```

The exactness theorem composing the path is:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted_exact
```

The final public inhabitant uses:

```lean
RMQ.SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily
```

whose directory combines:

- a rank structure over `shape.bpCode`, and
- a generic sparse-exception select source for selecting `false` bits in the
  same BP code.

## 9. Rank/Select Spoke: What Changed Conceptually

The plain-bitvector rank/select theorem is stable:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery
```

It proves `access`, `rank`, and `select` with `n + o(n)` payload and constant
modeled query cost for ordinary bitvectors.

The active frontier is compressed/FID rank/select. A fixed-weight bitvector is
a bitvector of length `n` with exactly `k` ones. There are
`binomialCount n k` such bitvectors, so the information-theoretic primary
payload is roughly:

```text
log2 (binomialCount n k)
```

The latest public state proves the log-chunk primary budget bridge. In plain
English:

> If we split the bitvector into sentinel log-sized chunks and store one
> fixed-weight code per chunk, the sum of those per-chunk code lengths fits
> under the global fixed-weight code length plus `o(n)` slack.

The key handles are:

```lean
RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks
RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound
RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks
```

The same frontier also exposes the replacement table/RAM route-directory
surface:

```lean
RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile
```

This split-width profile matters because route fields and local class/length
fields have different size needs. Padding class/length metadata to the wider
route width is formally ruled out:

```lean
RMQ.RankSelect.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength
```

Dense all-code decoder tables for log chunks are also ruled out as sublinear
payload:

```lean
RMQ.RankSelect.noFixedWeightLogChunkDenseDecoderLittleO
```

What remains open is not the primary fixed-weight budget. It is the positive
constructor: instantiate the split-width log-chunk table/RAM family with
concrete charged route payloads and a genuinely sublinear shared decoder
payload.

## 10. Balanced-Parentheses Navigation Spoke

Balanced-parentheses navigation is the reusable tree-navigation layer extracted
from the RMQ capstone.

The public import root is:

```lean
import RMQBPNavigation
```

The current public profiles are:

```lean
RMQ.BPNavigation.compactCloseDirectoryProfile
RMQ.BPNavigation.shapeAccessCloseRankProfile
```

Plain English: the spoke proves the close/LCA navigation that the RMQ theorem
needs, plus a bridge between close positions and inorder indices through
rank/select. It is not yet a full library of every balanced-parentheses tree
operation a user might expect.

## 11. Union-Find Spoke: What It Means

Union-find represents a partition of elements into disjoint sets. The abstract
specification is in `RMQ/Core/UnionFind.lean`:

```lean
RMQ.UnionFind.State
RMQ.UnionFind.State.find?
RMQ.UnionFind.State.unionSpec
RMQ.UnionFind.State.SamePartition
```

The concrete forest layer is in `RMQ/Core/UnionFind/Forest.lean`. It represents
sets by parent pointers. A root is its own representative; a non-root points
upward toward the root.

The first refinement checkpoint is:

```lean
RMQ.UnionFind.Forest.parentForestRefinement_profile
```

It says executable forest root search agrees with abstract `State.find?`.

The later full-compression representation checkpoint is:

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile
```

Path compression means a successful `find` follows the parent chain to the
root and rewrites visited nodes to point directly to that root. The theorem
proves this preserves the abstract partition and records exact trace/cost
facts about the visited path.

The amortized story then adds potentials. A potential is stored analysis credit:
an operation may take more immediate work if it decreases the potential enough
to pay for that work.

The rank-slack checkpoint proves that full compression zeroes a local slack
along the visited trace and that a global slack potential can pay successful
finds with constant find credit:

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackCheckpoint_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackSizeUnionAmortizedBackend_profile
```

The Tarjan-level frontier then splits parent-to-root rank slack into
cross-level and residual parts:

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIter
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanRankLevel
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelAmortizedBackend_profile
```

The phase-count and level-index profiles move closer to the classical Tarjan
proof shape:

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanPhaseCountAmortizedBackend_profile
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelIndexAmortizedBackend_profile
```

The caveat is formal, not rhetorical. The theorem

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le
```

shows that the current additive level-plus-residual design can collapse back to
ordinary rank slack when the residual is defined as "the part not paid by the
level gap." A true inverse-Ackermann proof needs a different residual index,
not merely a relabeling of the same slack.

## 12. What Is Proved Now, What Is Not Claimed

Current proved public story:

- exact RMQ semantics over half-open ranges with leftmost tie policy;
- many exact RMQ and LCA backends under the shared contract;
- a BP-native succinct RMQ capstone with `2*n + o(n)` payload and constant
  modeled query cost;
- a matching leading RMQ lower bound through Catalan shape counting;
- standalone plain-bitvector rank/select with `n + o(n)` payload and constant
  modeled query cost;
- compressed/FID route-budget and split-width table/RAM frontier theorems;
- balanced-parentheses close/LCA navigation needed by the RMQ capstone; and
- union-find abstract specs, forest refinement, path compression, and
  rank-slack/Tarjan-level amortized scaffolds.

Not claimed:

- Lean native execution time is not proved constant;
- proof-only fields are not stored payload;
- the compressed/FID rank/select constructor is not complete;
- the BP-navigation spoke is not yet a complete tree-navigation API;
- union-find does not yet prove the inverse-Ackermann amortized theorem;
- the union-find model is not yet a mutable-array refinement;
- `VerifiedDS` is not yet a separate mature package boundary.

## Assumptions Ledger

| Layer | Payload bits | Proof-only fields | Modeled cost | Runtime nonclaim |
| --- | --- | --- | --- | --- |
| RMQ reference | No compact payload claim; it is the value-level spec. | `LeftmostArgMin` witnesses and uniqueness proofs. | Some implementations have `Costed` wrappers; the spec itself defines correctness. | The reference scan is not a constant-time runtime claim. |
| RMQ capstone | BP shape code of length `2*n` plus counted rank/select and close-navigation payload. | Shape membership, balance, exactness, and lower-bound proofs. | Constant query bound over `concreteBPNativeSuccinctRMQQueryCosted`. | Not a production packed executable. |
| Plain rank/select | Stored bits plus Jacobson/Clark auxiliary payload. | Directory correctness and side-condition proofs. | Constant modeled access/rank/select cost. | Not a claim about Lean list indexing. |
| Compressed/FID frontier | Fixed-weight primary codes, route tables, class/length tables, and shared decoder payload only when counted by profiles. | Auxiliary-family premises and route equations until a concrete payload-backed family consumes them. | Current profiles charge route/local reads; final constant query still needs the concrete family. | Full-payload readback baselines are not the final runtime story. |
| BP navigation | Counted close-directory and rank/select words. | BP balance, close exactness, and LCA/RMQ bridge proofs. | Modeled table and word reads. | Not a complete general BP navigation library. |
| Union-find forest | Parent, rank, and mass fields are representation data in the forest model. | Invariants such as `RootMassInvariant`, `RankPowerMassInvariant`, and potential-drop lemmas. | `Costed` trace lengths and `RepresentationAmortizedBackend` inequalities. | Not yet an imperative mutable-array implementation. |
| Tarjan scaffold | No new serialized payload theorem beyond the forest representation. | Level schedules, potentials, residual definitions, and amortized proofs. | Cross-level potential pays part of find cost; residual/union credits remain explicit. | Not yet inverse-Ackermann amortized runtime. |

## Skeptical Grad Student Questions

**If the Cartesian shape determines RMQ, why do we need rank/select?**

The shape tells us the answer in principle. Rank/select and BP navigation are
how the compact bitstring is navigated without expanding the tree or scanning
the interval.

**Does `2*n + o(n)` include the proof that the directory is correct?**

No. It counts modeled payload bits. Lean proof fields certify the data
structure, but they are not serialized storage in the theorem's space account.

**Can the cost model hide an expensive computation behind one charged step?**

That is the risk the docs keep naming. The final RMQ path uses concrete
payload-backed rank/select and close-navigation components. Some intermediate
interfaces are intentionally described as weak until a concrete read-backed
inhabitant consumes them.

**Did the compressed/FID rank/select theorem close?**

No. The log-chunk primary budget bridge is proved, and the split-width
table/RAM profile states the right public shape. The missing theorem is the
positive constructor for concrete route payloads and a sublinear shared
decoder.

**Did the union-find Tarjan theorem close?**

No. The project now has Tarjan-shaped potential scaffolding, phase-count-shaped
successful-find credit, and a level-index checkpoint. The residual index is
still raw within-level rank slack, and the code proves a collapse diagnostic
showing why that definition cannot by itself become the classical theorem.

**Why not rename everything to `VerifiedDS` now?**

Because the stable, citable artifact is still the RMQ theorem stack, and the
new spokes are still settling their APIs. `VerifiedDS` is a facade that lets
downstream readers import the broader surface without forcing a namespace
migration.

## Next Theorem-Shaped Frontiers

1. **Compressed/FID concrete constructor.** Instantiate
   `RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile`
   with concrete charged route-directory payloads over
   `fixedWeightLogChunkBlocksWithSentinel`, a narrow class/length metadata
   account, and a sublinear shared decoder payload. The result should consume
   the existing access/rank/select route exactness from payload reads and prove
   a uniform constant modeled query bound.

2. **Union-find inverse-Ackermann bridge.** Replace the current raw residual
   rank slack in `tarjanLevelIndexPotential` with a recursively bucketed or
   Ackermann-indexed residual counter, avoiding
   `tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le`, and
   bound both successful-find and union credits by the intended
   inverse-Ackermann-style quantities.

RMQ itself also has a presentation frontier: produce a flatter payload-only
statement of the BP-native capstone for external readers. This is polish, not a
hidden correctness blocker.

## Stress-Test Rounds

This digest went through a simulated adversarial classroom loop before
finalization.

### Round 1 Objections

Data-structures novice: RMQ, LCA, rank/select, BP, FID, succinctness, and
amortization were too dense when introduced through theorem names.

Lean/formalization novice: `Costed`, `RAM.Exec`, payload, proof-only fields,
and `erase` needed ordinary-language explanations before use.

Skeptical mathematician: the first draft did not say why the lower bound
matches the upper bound beyond both having a `2*n` symbol.

Cost-model skeptic: "constant time" could be misread as Lean runtime.

Library-maintainer skeptic: `VerifiedDS` and the RMQ name looked like branding
drift unless the import-root story was explained.

Grad-student explainer: the rank/select FID frontier could not be restated
without knowing what fixed-weight codes and log chunks were.

Revisions made: added the example RMQ query; moved glossary-style explanations
before theorem handles; split modeled cost from runtime; added the Catalan
counting paragraph; added the import-root section; rewrote the FID section
around fixed-weight universes and the log-chunk primary-budget bridge.

### Round 2 Objections

Data-structures novice: union-find still sounded like "Tarjan proved" because
the names were impressive.

Lean/formalization novice: the document said "proof-only" but did not list
which fields are payload versus proof in each spoke.

Cost-model skeptic: the BP query route needed to say which actions are charged
navigation steps.

Skeptical mathematician: the FID frontier needed a negative result, otherwise
the remaining gap sounded like routine engineering.

Grad-student explainer: the next theorem targets needed to be theorem-shaped,
not project-management tasks.

Revisions made: added the assumptions ledger; named the BP query route step by
step; added the dense-decoder and route-width obstruction handles; expanded the
Tarjan caveat around residual slack and the collapse theorem; rewrote the next
frontiers as concrete theorem targets.

### Fixedpoint

Remaining objections are genuine open frontiers rather than missing
explanations: compressed/FID needs a concrete split-width log-chunk family, and
union-find needs an indexed residual counter strong enough for the
inverse-Ackermann theorem. Those caveats are now stated in the main text,
assumptions ledger, skeptical questions, and theorem-shaped frontiers.

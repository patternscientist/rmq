# Project State Digest: 2026-06-28

This note is the current classroom-facing project digest. It is written for a
mathematically mature reader who may know proof and asymptotics but not Lean,
succinct data structures, union-find, monads, or the word-RAM model.

Status label: `main` now includes the latest rank/select compressed/FID
route-directory profiles and the union-find Tarjan-level amortization scaffold.
The theorem handles below are ordinary project state, not branch-relative
claims.

The public import roots are:

```lean
import RMQ
import RMQHub
import RMQRankSelect
import RMQBPNavigation
import RMQUnionFind
import VerifiedDS
```

`VerifiedDS` is only a thin aggregate facade. The citable theorem names still
live under the older RMQ, rank/select, BP-navigation, and union-find roots.

## What Is Proved Now

The stable RMQ capstone is unchanged. The short alias
`RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` abbreviates
`RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`.
It says that Cartesian-shape RMQ has an exact BP-native representation with
`2*n + o(n)` payload bits and constant modeled query cost, paired with the
coefficient-correct Catalan lower side. The lower-bound alias is
`RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`, expanding to
`RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`.

Plain English: range-minimum query asks for the leftmost minimum in an
interval. Cartesian shape preserves exactly the order information needed for
all such queries. The lower bound says there are almost `2^(2*n)` relevant
shapes to distinguish. The upper bound stores a balanced-parentheses code of
length `2*n` plus smaller navigation tables and answers through checked
rank/select and close-navigation components.

The stable plain-bitvector rank/select theorem is also landed. The public
handles are `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` and
`RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery`, also exposed by
`RMQ.Headlines.rankSelectNPlusOConstantQuery` and
`RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery`. These prove stored
bit access, exact rank, exact select, `n + o(n)` payload, constant modeled
query cost, and in the strengthened theorem bounded payload-word reads.

Rank/select compressed/FID update: the compressed/FID path has now removed a
major counting blocker for sentinel log chunks. The merged proof proves
that the sum of per-block fixed-weight code lengths is bounded by the global
fixed-weight payload budget plus one slack bit per block, and that for
log-sized sentinel chunks this block-count slack is `o(n)`. The key handles
are:

- `RMQ.RankSelect.binomialCountMulLeAdd`;
- `RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks`;
- `RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound`;
- `RMQ.RankSelect.fixedWeightAmbientBlockCompositionWordBoundedCompressedProfileOfLogChunkBlocks`;
- `RMQ.RankSelect.fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`.

The same integrated work adds the table/RAM route-directory envelope and the
split-width repair that separates wide route fields from narrow local
class/length fields:

- `RMQ.RankSelect.fixedWeightAmbientTableRAMRouteDirectoryFamilyWordBoundedCompressedProfileOfPrimaryBudget`;
- `RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyWordBoundedCompressedProfile`;
- `RMQ.RankSelect.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`;
- `RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile`.

This is stronger than the old raw-size theorem
`RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLeLengthAddBound`. The
old theorem only said "block codes fit under raw `n + o(n)`"; the new bridge
says "block codes fit under the fixed-weight information budget
`log2 (binomialCount n m) + o(n)`" for the log-chunk construction.

Compressed/FID rank/select is still not complete. What remains is a concrete
family instantiation: a charged route-directory and local-decoder family over
the sentinel log chunks that consumes the access/rank/select route equations
from payload reads, preserves narrow class/length metadata, and has a uniform
constant modeled query bound. In particular, the theorem surface is no longer
waiting for the log-chunk primary budget, but it is still waiting for the
payload-live global dictionary construction.

The BP-navigation spoke exposes the reusable close-navigation layer through
`RMQBPNavigation`. The public handles are
`RMQ.BPNavigation.compactCloseDirectoryProfile` and
`RMQ.BPNavigation.shapeAccessCloseRankProfile`. This is the RMQ-facing close
and close/rank bridge, not yet a full tree-navigation library API.

The stable union-find spoke includes a finite partition reference model,
parent-pointer forests, union-by-rank/root-mass/rank-power invariants, full
path compression, rank-gap/log-rank/rank-bucket checkpoints, and rank-slack
amortized profiles:

- `RMQ.UnionFind.Forest.parentForestRefinement_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRepresentationBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankBucketAmortizedBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackCheckpoint_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackAmortizedBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionRankSlackSizeUnionAmortizedBackend_profile`.

Union-find Tarjan-level update: the merged union-find spoke adds a multilevel
potential scaffold. It introduces an executable iterated-log rank schedule and
splits a parent-to-root rank gap into two pieces: the part that crosses levels
and a residual within the current level. The aggregate potential pays the
cross-level part; the find credit still pays the residual part plus constant
`2`. The key handles are:

- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelIter`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanRankLevel`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.traceRootParentRankSlack_le_tarjanLevelGap_add_residual`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelFindCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelUnionCredit`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelAmortizedBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelCleanCreditAmortizedBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanPhaseCountAmortizedBackend_profile`;
- `RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState.fullCompressionTarjanLevelIndexAmortizedBackend_profile`.

This is a real Tarjan-shaped scaffold, not the Tarjan theorem. The residual
credit `tarjanLevelFindCredit` still contains
`traceRootParentTarjanResidualSlack`; it can be large inside a fixed level.
The union credit `tarjanLevelUnionCredit` is
`tarjanLevelPotentialBound backend + 1`, a whole-forest bound, not a small
uniform operation credit. The concrete level schedule is currently
`tarjanRankLevel rank = tarjanLevelIter 2 rank`, not an operation-sequence
inverse-Ackermann schedule. The level-index checkpoint also proves the collapse
diagnostic
`tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le`, showing why
the next residual counter must be genuinely indexed rather than simply
`rankSlack - levelGap`.

## What Became Stale

The previous digest was accurate before the latest integration, but stale in
three ways.

First, it said the rank/select compressed/FID frontier still needed the
primary enumerative budget. Corrected statement: for sentinel log chunks, the
primary fixed-weight budget bridge is now proved. The remaining blocker is
concrete family instantiation behind the split-width table/RAM envelope.

Second, it treated union-find's newest amortization story as rank-slack plus a
coarse size-log union credit. Corrected statement: the union-find proof
work adds a Tarjan-level scaffold splitting cross-level gaps from residual
within-level slack, plus clean-credit, phase-count, and level-index refinements.

Third, it described the next union-find frontier as "introduce a multilevel
bucket potential." Corrected statement: that scaffold exists; the next theorem
must shrink or parameterize the residual and whole-forest credits enough to
approach an inverse-Ackermann sequence bound.

## Plain-English Map Of The Spokes

RMQ is the shape story. Instead of storing array values, store the tree shape
that determines all leftmost minima. Lean is used here to connect the reference
definition, the Cartesian-shape reduction, the counting lower bound, and the
payload-accounted upper construction.

Rank/select is the bitvector navigation story. `access i` asks for bit `i`;
`rank b i` counts how many `b` bits appear before `i`; `select b k` finds the
position of the `k`th `b`. For ordinary bitvectors, the Jacobson/Clark theorem
is complete. For fixed-weight bitvectors, the project is trying to store the
bitvector by its number among all bitvectors with the same number of ones.
The new merged result proves that splitting into log chunks does not
waste the information-theoretic primary payload budget by more than `o(n)`.

BP navigation is the tree-navigation bridge used by the RMQ capstone. It turns
balanced-parentheses positions into tree navigation facts and back into RMQ
answer indices through checked rank/select and close operations.

Union-find is the amortization laboratory. The data structure represents a
partition by parent pointers. `find` follows parents to a representative;
path compression rewrites the visited pointers to point directly to the root.
Lean is used to prove both that this preserves the abstract partition and that
a potential function pays for the pointer chasing. The new merged Tarjan-level
and level-index scaffolds are exactly about choosing a better potential
function.

The model hub is the shared vocabulary: `Costed`, `RAM.Exec`, indexed table
reads, bounded stores, payload views, and finite lower-bound encodings. These
objects are how the project says "constant modeled query" without claiming
that Lean's own `List` evaluator is constant time.

## Assumptions Ledger

| Layer | Payload bits | Proof-only fields | Modeled cost | Runtime nonclaim |
| --- | --- | --- | --- | --- |
| RMQ capstone | BP shape code plus counted rank/select and close-navigation payload. | Shape, balance, exactness, and refinement proofs. | Constant query cost in `Costed`/RAM indexed-access model. | No Lean `List` constant-time claim. |
| Plain rank/select | Stored input bits plus Jacobson/Clark auxiliary payload. | Directory correctness proofs and side conditions. | Access/rank/select are constant modeled operations. | No native-runtime timing claim. |
| Compressed/FID rank/select | Fixed-weight codes, route tables, class/length tables, and bounded stores when counted by a profile. | Route equations and auxiliary-family premises until consumed by concrete charged data. | Route/local reads are charged; constant time still needs the concrete family. | Full-payload readback baseline is not constant time. |
| BP navigation | Counted close-directory and rank/select words. | BP balance and close correctness witnesses. | Modeled table and word reads. | Not a complete production tree-navigation library. |
| Union-find | Parent, rank, and mass fields are executable representation data in the forest model. | Invariants such as `RootMassInvariant`, `RankPowerMassInvariant`, and potential-drop proofs. | `Costed` trace length and `RepresentationAmortizedBackend` inequalities. | Not a mutable-array implementation or Lean-runtime theorem. |
| Tarjan-level scaffold | No new serialized payload claim beyond the forest model. | The level schedule, level potential, and residual/union-credit proofs are analysis objects. | Cross-level potential pays part of find cost; residual and union credits remain explicit. | Not yet inverse-Ackermann amortized runtime. |

## Skeptical Grad Student Questions

**Did rank/select compressed/FID close?**

No. The merged primary budget bridge removes an important counting
blocker for sentinel log chunks. It does not yet build the concrete charged
route-directory/local-decoder family that answers access/rank/select with
constant modeled cost.

**What exactly did the new primary-budget proof buy?**

It proves that storing one fixed-weight code per log chunk does not blow the
main compressed payload budget. The product of the per-block fixed-weight
universes injects into the global fixed-weight universe with one slack bit per
block, and the number of log chunks is `o(n)`.

**Does the Tarjan-level union-find profile prove Tarjan?**

No. It has the right kind of decomposition: cross-level work is paid by a
potential drop. But the residual within-level work and union credit remain
explicit and potentially large. There is no inverse-Ackermann sequence theorem
yet.

**Why does the digest keep saying "modeled cost"?**

Because the formal cost theorem is about a small mathematical model of
charged reads and word operations. Lean checks the proof of that model
statement. It does not automatically turn list-backed definitions into a
constant-time executable program.

**Can proof-only invariants hide storage?**

They can if one is careless. The project deliberately separates serialized
payload fields from invariants and proofs. Future mutable-array or extracted
implementations must state which fields are executable state and which are
certificates used only for verification.

## Next Two Theorem-Shaped Frontiers

1. Rank/select FID concrete family instantiation:
   build a charged route-directory/local-decoder family over
   `fixedWeightLogChunkBlocksWithSentinel` that consumes
   `fixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeWordBoundedCompressedProfileOfLogChunkBlocks`,
   supplies route fields from payload reads, preserves narrow class/length
   metadata, and proves a uniform constant modeled access/rank/select bound.

2. Union-find inverse-Ackermann bridge:
   generalize the fixed `tarjanRankLevel = tarjanLevelIter 2` scaffold to a
   phase schedule tied to operation counts or rank-universe parameters, then
   bound `traceRootParentTarjanResidualSlack` and
   `tarjanLevelUnionCredit` by the intended inverse-Ackermann-style credits.

For RMQ itself, the useful follow-up remains presentation polish: a flatter
payload-only statement of the BP-native capstone and routine drift checks from
short public aliases to construction-heavy theorem names.

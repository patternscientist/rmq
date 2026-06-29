# Design Note: Frontier Obstructions and the Architecture to Remove Them

**Based on:** `main` at commit `933b481` ("Integrate Claude proof digestion
audit").
**Branch:** `claude/design-frontier-harnesses` (this note plus the two new
harness modules it describes).
**Scope:** the two *formal design obstructions* the project has hit — one in
union-find amortization, one in compressed/FID rank/select — why they are the
same kind of bug, the architecture that removes them, how to preempt the next
ones, and the reusable Lean harnesses landed here as the first step.

This is a design document. The claims about what is *proved* refer to named Lean
theorems; the claims about what is *not yet proved* are stated as open targets,
not as results.

---

## 1. The two obstructions, precisely

Both are real theorems in the repository that block the obvious continuation of
the current design.

### 1a. Union-find: the potential collapses

`RMQ/Core/UnionFind/Forest.lean` defines the Tarjan-facing residual
*subtractively*:

```
nodeRootParentTarjanResidualSlack root x
  := nodeRootParentRankSlack root x - nodeRootParentTarjanLevelGap root x
tarjanLevelIndexPotential := tarjanLevelPotential + tarjanResidualPotential
```

with `tarjanRankLevel := tarjanLevelIter 2` (a *fixed* two-iteration log). The
obstruction theorem

```
tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le
```

proves that whenever the level gap is `<=` the parent rank slack (the natural
condition), `tarjanLevelIndexPotential = rankSlackPotential`. Per node this is
`levelGap + (rankSlack - levelGap) = rankSlack`: an *algebraic re-partition of the
quantity being bounded*. It carries no new information, so the potential stays
`O(rankSlack) = O(log n)`-shaped and cannot reach inverse-Ackermann.

### 1b. Rank/select (compressed/FID): single scale, two needs

`RMQ/Core/RankSelectCompressed.lean` uses a *full*-log block:

```
fixedWeightLogChunkBlockSize n := Nat.log2 n + 1
fixedWeightLogChunkDenseDecoderLowerBound n := 2 ^ blockSize * blockSize   -- ~ 2n log n
```

so a universal decode table over a block has `2 ^ (log2 n) = n` rows
(`RankSelectPublic.noFixedWeightLogChunkDenseDecoderLittleO`: not `o(n)`).
Separately, a per-block *route pointer* needs `Theta(log n)` bits while *class /
popcount* needs only `Theta(log log n)`; storing both at one width is linear
(`RankSelectPublic.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength`).

### 1c. Same bug, twice

Both are *single-scale where the problem has two scales*. Union-find folds one
cost quantity into itself (conservation, not progress). Rank/select pads a narrow
field to a wide one and sizes a shared table to the wrong (full-log) block. The
architecture below makes "two scales" the default in both places.

---

## 2. Union-find: design to reach `O(alpha(n))`

The fix is not a better subtraction; it is a genuinely **two-coordinate,
independently-monotone** progress measure — the Tarjan / Tarjan–van Leeuwen
`(level, index)` assignment.

1. **A real Ackermann hierarchy** (none exists yet; `tarjanLevelIter` is only
   iterated log). Define `A_k(j)` with `A_0(j) = j+1`,
   `A_{k+1}(j) = A_k^{(j+1)}(j)`, and `alpha(n) = min { k : A_k(1) > n }`, with
   monotonicity lemmas. The existing `RankPowerMassInvariant` (`2^rank <= mass`,
   hence `rank <= log2 n`) bounds `alpha(rank) <= alpha(n)`.

2. **`level(x)` and `index(x)` as functions of the forest state**, not of cost:
   - `level(x) = max { k : rank(parent x) >= A_k(rank x) }`
   - `index(x) = max { i : rank(parent x) >= A_{level x}^{(i)}(rank x) }`
   Node potential `phi(x) = (alpha(n) - level x) * rank x - index x` (nonnegative
   because `level <= alpha(n)` and `index <= rank x`). The decisive change from
   today's code: `index` is an *independent* counter bounded by `rank x`, not
   `rankSlack - levelGap`; its total is not conserved against the level term.

3. **Two monotonicity lemmas** (standard, but the real labor):
   - *Preservation:* for a fixed non-root `x`, `level x` and `index x` never
     decrease as unions/compressions proceed (ancestor ranks only grow; `rank x`
     freezes once `x` is non-root). So `phi(x)` only decreases.
   - *Find pays:* on a find path, all but `<= alpha(n) + 2` nodes strictly
     increase `level` or `index` when relinked to the root (since
     `rank(root) > rank(old parent)`), dropping `phi` by `>= 1` each. The
     `alpha(n) + 2` unpaid nodes are the per-find credit.

The lexicographic `(level, index)` pair is the progress measure the subtractive
residual cannot produce, because it has no second, separately-bounded axis.

**The reusable principle:** *a potential term is legitimate only if it has a
monotonicity proof independent of the cost it pays for.* Concretely, separate the
**structural-invariant layer** (ranks, mass, `level`/`index` + their
monotonicity) from the **credit layer** that consumes it; today's design fused
them, which is exactly how a tautological potential slipped in.

(The operation set is already right: full path compression with union by rank is
covered by the Tarjan–van Leeuwen `O(alpha(n))` analysis, and the functional
forest is fine for the *complexity* theorem; a mutable-array refinement is an
orthogonal later concern.)

---

## 3. Rank/select: design to reach a concrete `O(1)` compressed FID

The *space* side is already done (the per-block budget bridges prove
`sum (block budgets) <= log C(n,k) + o(n)`, and `binomialCount` is the genuine
coefficient). What is blocked is the *query/overhead* side, and the obstructions
point straight at the classical RRR architecture.

1. **Shrink the block to sub-log.** Use `B = floor(log2 n / 2)` (any
   `B <= c log n`, `c < 1`). Then a *single shared* universal decode/rank table
   has `2^B = O(sqrt n)` rows, giving in-block decode + rank + select in one
   lookup — turning the dense-decoder obstruction into a positive `o(n)`
   table-size bound. The budget bridges survive a block-size change (the
   `+1`-per-block rounding is `n/B = o(n)` for any sub-log `B`); only the table
   *requires* sub-log. Keep the table; do **not** switch to arithmetic unranking
   (that is `O(B) = O(log n)` per query and breaks `O(1)`).

2. **Make the route directory two-level, not flat per-block** — this is the
   *next* obstruction, not yet hit. Even with split widths, a route pointer *per
   block* at `Theta(log n)` bits is `n/B * log n = Theta(n)`. The standard fix is
   the superblock/block hierarchy: superblocks of `Theta(log^2 n)` bits carry
   *absolute* rank/position pointers (`Theta(log n)` bits, only `n/log^2 n =
   o(n)` of them); blocks carry *relative* pointers + class at `Theta(log log n)`
   width. Split widths are necessary but insufficient on their own; the two
   scales must also be two *levels*.

3. **Reuse, do not re-build.** The plain rank/select spoke and the RMQ capstone
   already contain a two-level sampled directory (`superStride ~ log^2 n`,
   `localStride`, super/local entries). The compressed FID should be an
   *instance* of that functor with `(block size = sub-log, block payload =
   compressed offset, in-block kernel = universal table)`, not a separate flat
   `LogChunkRouteDirectory`. Building a parallel flat family is what led to
   re-deriving — and re-hitting — the width/scale problems.

---

## 4. Cross-cutting architecture (and how to preempt the next obstruction)

Bake two rules into the design:

- **Hierarchical, scale-matched accounting everywhere.** No per-element field at
  uniform width: each field's width = `log(its range at its level)`; group so
  that wide fields are rare (superblocks) and common fields are narrow (blocks).
  Provide one generic two-level sampled-directory functor and discharge "is it
  `o(n)`?" *once*, not per spoke.

- **Potentials from independent invariants, plus a sequence harness.** State the
  end-goal as a *sequence* theorem ("`m` operations cost
  `O((m+n) alpha(n))`"), produced from per-operation certificates by a generic
  telescoping layer — so a per-op inequality that does not compose cannot be
  mistaken for the real bound.

- **Separate the invariant layer from the credit/overhead layer** as a module
  boundary in every spoke, so a potential can never again be a rearrangement of
  the cost, and an overhead can never again be a single uniform width.

---

## 5. What this branch lands (Step 1 + the achievable part of Step 2)

Two new modules, both Mathlib-free, `sorry`-free, and trust-clean
(`#print axioms` resolves to a subset of `{propext, Classical.choice,
Quot.sound}`; registered in `scripts/axiom_check.lean`). They are the reusable
harnesses the architecture above calls for — not the end-goal theorems.

### `RMQ/Core/AmortizedSequence.lean` — the amortized telescoping harness

Generalizes the per-operation `RMQ.Amortized.Bound` / two-step `compose` to a
whole sequence:

- `RMQ.Amortized.runBound` — total actual work + final potential `<=` total
  credit + initial potential (the telescope).
- `RMQ.Amortized.totalActual_le` — total actual work `<=` total credit + initial
  potential (the headline amortized bound).
- `RMQ.Amortized.totalActual_le_length_mul` — uniform-credit corollary:
  `<= (#operations) * c + Phi_initial`.

This is exactly the harness the union-find inverse-Ackermann theorem needs to
turn a per-find `phi`-drop certificate into a sequence bound. It is
data-structure agnostic (any structure supplies a potential and a per-op
`Bound`).

### `RMQ/Core/SampledLayoutBudget.lean` — two-level / sub-log accounting

- `RMQ.SuccinctSpace.twoLevelLayoutOverhead` + `twoLevelLayoutOverhead_littleO`
  — a superblock level at full sampled-directory width plus a block level at
  narrow `log log` width is `o(n)`. The positive counterpart of the route-width /
  class-length obstruction: two levels, two widths.
- `RMQ.SuccinctSpace.subLogBlockSize` (`= floor(log2 n / 2)`) with
  `two_pow_subLogBlockSize_sq_le` — `(2^B)^2 <= n`, i.e. the universal table has
  `<= sqrt n` rows; and `subLogBlockTableRows_littleO` — `n |-> 2^B` is `o(n)`.
  This is the positive theorem the dense-decoder obstruction asked for: shrink
  the block, and the shared table's row count becomes `o(n)` (versus `>= n` at a
  full-log block). It removes the obstruction at the *row-count* level.

---

## 6. What remains open (honest boundary)

These harnesses are the foundation, not the closure. Still to do:

- **Union-find (the hard new math):** the Ackermann hierarchy, the `level`/
  `index` node functions with their two monotonicity lemmas, the
  `<= alpha(n) + 2` find-pays lemma, and the assembly through
  `AmortizedSequence` resting on `RankPowerMassInvariant`. This is the actual
  inverse-Ackermann theorem; only its accounting harness is landed here.
- **Rank/select (full table-size `o(n)`):** `subLogBlockTableRows_littleO` bounds
  the table *row count* by `o(n)`; the full table is rows `x` per-entry width
  (`~ sqrt n * polylog`), whose `o(n)` needs a `log = o(sqrt)` growth lemma
  (`(scale * log2 n)^2 <= n` eventually) not yet in the Mathlib-free toolkit.
  That is a small, well-scoped arithmetic gap.
- **The concrete FID family:** instantiate the existing two-level sampled
  directory at sub-log block size with the universal table, wire access / rank /
  select to `O(1)` charged reads, and prove exactness from payload reads. This is
  the open frontier; the budget side and the table-row-count side are now in
  hand.
- **A generic two-level directory functor:** `twoLevelLayoutOverhead` is the
  overhead lemma; promoting the existing bespoke two-level directories to one
  parameterized functor (so plain rank/select, compressed FID, and BP navigation
  are instances) is the larger refactor that fully preempts re-deriving the
  accounting per spoke.

## 7. Suggested order

1. **Done here:** the `AmortizedSequence` telescoping layer; the two-level
   overhead `o(n)` lemma; the sub-log table-row-count `o(n)` lemma.
2. **Rank/select next:** the `log = o(sqrt)` lemma, then instantiate the two-level
   directory at sub-log `B` with the universal table and wire `O(1)` queries.
3. **Union-find:** Ackermann hierarchy + `level`/`index` + monotonicity +
   find-pays, fed through `AmortizedSequence`.

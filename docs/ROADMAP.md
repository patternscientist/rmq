# RMQ Hard-Target Roadmap

Ordered, pre-registered targets. The loop discharges them in dependency order;
"done" means the target's stated theorem typechecks `sorry`-free. These are the
*needle-moving* results -- not breadth. Derived from the standing project debt:
the cost story is asserted (unit-cost ticks), and the lower bound has no matching
real upper bound.

## How to use this file

- Materialize each target as a real statement only once its supporting
  constructs exist. Until then keep it here as prose + the intended theorem
  shape. Do **not** pre-commit a compiled `Prop` that is trivially true.
- **Anti-vacuity rule.** A target stated as `∃ f, P f` is worthless if some
  trivial `f` satisfies `P` (e.g. `∃ steps, steps bounded` is satisfied by
  `steps := 0`). Every target below must reference a *principled* construction
  (an instrumented monad, an actual encoder), not an arbitrary witness. When you
  turn a target into Lean, check that a degenerate witness does **not** prove it.
- One target per autonomous run (may chain if the gate stays green). Update
  `docs/FAMILY_SUMMARY.md` and extend `scripts/axiom_check.lean` with the new
  headline theorem when a target closes.

## Dependency DAG

```
M1 (real cost model)  ──►  M3 (unified O(n)/O(1) LCA: build + query)
        │
        └──────────────►  M2 (succinct upper bound) ── query-time half needs M1
```

M1 is the keystone: it unblocks the honest time-half of both M2 and M3. Do it
first.

---

## M1 -- Keystone: a cost model where time is *derived*, not asserted

**Problem.** Every current "O(1)/O(n)" rests on charges written by hand
(`materializedMicrotableLookupCost := 1`, `indexedReadCost := 1`,
`firstOccurrenceCosted` charging 1 for a linear scan). A reviewer's first
objection is "your costs are definitions, not proofs."

**Done-criteria.** An instrumented executable substrate (Lean `Array`) where
ticks are introduced *only* by primitive operations, plus:

1. `instrumentedQuery` for one structure (start with the sparse table) proven
   equal to the verified `List` backend, and
2. its derived step count bounded by the intended complexity, and
3. a soundness theorem tying the step count to a small operational/RAM
   semantics (`ticks = steps`).

The headline theorem has the shape: `instrumentedSparseQuery refines
SparseTable.query ∧ steps(instrumentedSparseQuery) ≤ c`, where `steps` is the
operational step count, **not** an author-supplied function.

**Parallel decomposition (one join):**
- Leaf A: `Array` ↔ `List` refinement lemmas (indexing, length, `toList`).
- Leaf B: instrumented primitive cost library (read / compare / alloc each cost
  1 *by construction of the interpreter*, not by `tickValue`).
- Leaf C: small operational/RAM step semantics + its `Costed`-soundness lemma.
- Join (lead): re-found the sparse table on A+B, prove refinement + step bound,
  discharge via C.

**Debt it reduces.** Drops asserted-cost charges; converts the sparse-table
cost theorems from model-level to machine-grounded.

## M2 -- Succinct upper bound → tight space bound

**Problem.** The repo has the rare half (a no-premise `2n − O(log n)` lower
bound) but only loose `2n`-bit encodings; no construction approaches the bound,
and no tightness theorem pairs the two sides.

**Done-criteria (two stages).**
- M2a (space, no cost model needed): a `LosslessShapeEncoding` / encoder with
  payload `≤ 2n + o(n)` bits, stated against the existing bit-length accounting.
  Combined with `EncodingLowerBound.two_mul_sub_log_slack_le_bits_...`, state the
  **tight space theorem**: RMQ encoding size is `2n ± Θ(log n)` bits.
- M2b (query time, needs M1): the encoder answers queries in constant *derived*
  steps under the M1 substrate -- the real Fischer-Heun succinct claim.

**Anti-vacuity.** M2a must exhibit a concrete encoder with a proved
`query_exact`, not merely assert an encoding of that size exists.

**Debt it reduces.** Closes the headline parity gap; turns the lower bound into
a two-sided result.

## M3 -- Unified end-to-end O(n)/O(1) LCA (build + query)

**Status.** Correctness is already done (`LCAFischerHeun` /
`SuccinctReduction` prove `IsPathLCA`). The gap is cost: query cost is
query-only and model-level, conditioned on a *supplied* first-occurrence table
whose construction is uncosted.

**Done-criteria.**
1. `FirstOccurrenceBuildLinear`: a costed first-occurrence-table build with cost
   `≤ c · n` (closes the uncosted-preprocessing hole).
2. Under M1, a single theorem bundling **build cost `≤ c · n` and query cost
   `≤ c'`** for the Fischer-Heun-backed LCA -- no `_of_firstOccurrences`
   side hypothesis.

**Anti-vacuity.** The query bound must consume the *built* first-occurrence
table (cost charged), not assume it as a hypothesis.

**Debt it reduces.** Eliminates the `_of_firstOccurrences` gated-hypothesis
class for LCA; produces the recognizable Bender–Farach-Colton headline with both
correctness and machine-grounded cost.

---

## Cheap win (anytime, not a substitute for the above)

State the tight *space* bound from M2a's lower-bound side plus the existing
`shapeCount_le_four_pow` upper count -- it reads well and is nearly free, but it
is packaging, not the ambition. Do not let it crowd out M1.

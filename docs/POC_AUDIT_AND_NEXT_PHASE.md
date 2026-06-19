# RMQ POC — Latest Audit + Next Phase (tight bound, then hub extraction)

Date: 2026-06-18. Audit-branch record. Codex's working-tree `ROADMAP.md` /
`CODEX_AUTONOMY.md` are canonical steering docs; the Part 2 plan below should be
folded into the canonical `ROADMAP.md`.

Decision (user): **stay on RMQ for now.** Next concrete work, in order:
(1) finish the *tight* RMQ bound; (2) polish + extract, validate, and document
the hub as a standalone. New spokes, a probability/amortization hub layer, and
CSLib coordination are **deferred** (CSLib coordination stays after the demo,
≈ 2026-06-24).

---

# Part 1 — Latest audit (dense-LCA linear-budget / "POC complete" round)

**Health.** Build green; no `sorry`/`admit`/`axiom`/`native_decide`/`partial`/
`extern`/`noncomputable`; curated trust base depends only on
`{propext, Classical.choice, Quot.sound}` (0 `sorryAx`/`ofReduceBool`).

**What landed.**
- `denseLCA_linearBuild_constantQuery_profile`: the dense LCA headline in clean
  profile form — `densePreprocessBuildCost ≤ densePreprocessLinearBudget` with
  `densePreprocessLinearBudget := 22 * |nodes| + 3` (a genuine single linear
  term), `IsPathLCA` correctness, query `cost ≤ 16`, and combined
  `build + query ≤ 22·|nodes| + 3 + 16`.
- A–D statuses flipped to "POC complete," each honestly caveated (see below).
- A's previously-flagged residual is effectively closed: the sparse-build
  value-side `++ [cell]` snoc is gone; row construction now charges one counted
  `pushArray` per cell, and `RAM.Exec`'s constructor + raw primitive are sealed
  (clients use typed value-computing primitives only).

**A–D scorecard (all complete; caveats are disclosed, not hidden).**

| Target | Status | Honest caveat |
|---|---|---|
| A — machine-step cost model | ✅ complete as a **hardened shallow RAM model** | counted primitives + sealed constructor; not yet a first-order operational interpreter (value/trace paired by discipline). Residual uncounted work is lower-order (top-level `toArray` of `O(log n)` rows; the `xs.toArray` input boundary). |
| B — refinement framework + 2 instances | ✅ complete | two derived `Refine.StoredMatrix` instances (sparse table + FH); FH capstone `fischerHeun_refines_with_steps`. |
| C — lower-bound framework + RMQ instance | ✅ complete | generic `Core.LowerBound` ("does not mention RMQ"); RMQ re-derived through it. |
| D — research headline | ✅ complete (two profiles) | standalone FH fresh O(n) build / O(1) query (`canonicalReady` precondition) **and** dense LCA linear build / constant query (`DenseNatLabels` + `canonicalReady`). |

**Stop assessment.** Appropriate. Small focused round (+49 lines) delivering
real demo-prep value (clean profile headline + honest status reconciliation),
trust intact, nothing left half-done. The persistent assoc-list cleanup from the
prior round was completed before this one (path fully retired, no dangling refs).

**Preconditions to state plainly (demo honesty, not flaws).**
- FH fresh O(n)/O(1): `canonicalReady` (large enough; block size ≥ 16).
- Dense LCA O(n)/O(1): `DenseNatLabels` (nodes labeled `0..n-1`) — exactly the
  RMQ-via-LCA setting (Cartesian-tree nodes are array indices), so frame it as
  natural, not restrictive.
- "Machine-step" = counted primitive ops in the unit-cost RAM model (one array
  read = one step); the cost layer is a hardened shallow monad, not a first-order
  interpreter. Standard model; state it as such. The `#print axioms` reveal is
  the strongest live trust demonstration.

**Bottom line.** The bounded finish line (A + B + C + one-of-D) is met, with two
clean headline profiles. The POC is demo-ready.

---

# Part 2 — Next phase (RMQ only): tight bound, then hub extraction

## E1 — Finish the tight RMQ space bound (the flagship excitement hook)

**Why first.** Matching upper+lower bounds are almost never formalized; this is
the single result most likely to excite a data-structures researcher, and it
proves "tight bounds" is a real *library capability* rather than a one-sided
claim. It is a continuation of RMQ (no new domain), and it seeds the eventual
succinct spoke.

**Goal.** Pair the existing no-premise lower bound
(`2n − (2·log₂(2n+1) + 2)` bits) with a concrete succinct **upper-bound**
encoder of `≤ 2n + o(n)` bits whose query/decoder is proved exact, yielding a
two-sided **`2n ± Θ(log n)`** space theorem.

**Done-criteria.** A single theorem combining (i) the lower bound and (ii) a
concrete encoder's bit count, stating the RMQ encoding size is `2n ± Θ(log n)`.
The encoder must answer (or losslessly determine) all RMQ queries from its bits.

**Anti-vacuity.** A *concrete* encoder with a proved exact query/decode — not a
bare existential, and not the current loose `2n`-bit shape payload presented as
if it were the succinct construction. The `o(n)` slack must be a real bit-length
bound, not hand-waved.

**What already exists to build on.** `EncodingLowerBound` (lower bound);
`shapeCount_le_four_pow` (the `≤ 4^n` count → `≤ 2n` information-theoretic upper
*count*); the canonical representative encoding (`2n` bits, loose). A cheap
stepping-stone is to state the two-sided bound from the lower bound + the `4^n`
count; the *headline* is the genuine `2n + o(n)` encoder with exact queries.
This needs a small succinct/bitvector rank-select layer — scope it to RMQ's
encoding here (it is also the seed of the future succinct spoke, but do not let
it grow into the spoke yet).

## E2 — Polish, extract, validate, and document the hub as standalone

**Why now.** The hub (`Cost`, `RAM`, `Refine`, `TableModel`, `LowerBound`) was
grown to fit RMQ; whether it is genuinely reusable or secretly RMQ-shaped is
untested. The cheapest time to find out is now, while RMQ is the only client.

**Tasks.**
1. **Separate.** Move the hub modules into a package/namespace with **zero RMQ
   imports**; keep RMQ-specific Core (`Spec`, `Window`, `Shape`, `LCA`,
   `Cartesian`, `EncodingLowerBound`, …) in the spoke.
2. **Validate dependency direction.** Confirm hub ← spoke only — no hub module
   imports any RMQ-specific module. (`LowerBound` already advertises RMQ-freedom;
   confirm `Cost`/`RAM`/`Refine`/`TableModel` likewise.)
3. **Build standalone.** Give the hub its own lake lib target and confirm it
   compiles without the RMQ spoke — the actual reusability test.
4. **Document interfaces.** A short hub README: what a spoke imports, the
   `Refine` contract, the `RAM`/`Cost` cost model and its caveats, and the
   `LowerBound` encoding API. Without this, a future spoke re-derives everything.
5. **Generalize the gate.** Split `scripts/axiom_check.lean` into hub-level and
   spoke-level trust checks so the hub has its own standing trust guarantee.
6. **CSLib portability seam.** Keep the `Cost.Time ↔ TimeM` correspondence
   explicit so the hub is upstream-ready (the actual CSLib conversation stays
   after the demo).

**Done-criteria.** Hub builds as a standalone lake target with no RMQ
dependency; RMQ imports it as a client; hub interfaces are documented; hub-level
`axiom_check` passes.

## Deferred (explicitly NOT now)

- New spokes (succinct rank/select as its own spoke, count-min/sketch, cuckoo,
  IBLT, Fibonacci/splay).
- Probability and amortization hub layers (required by the probabilistic /
  amortized spokes; build only after a deterministic validating spoke + CSLib
  feedback).
- CSLib coordination thread (after the demo, ≈ 2026-06-24).
- First-order operational interpreter for the cost model (A's "future"
  strengthening; only needed for a machine-model lower bound).

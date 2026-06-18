# RMQ Roadmap — Hub-and-Spoke Proof of Concept

## Mission and positioning (read first)

This repo is **spoke #1 and the proof of concept** for a larger hub-and-spoke
library of frontier-grade formalized advanced data structures. RMQ is the
instantiation that proves the pattern; the reusable parts (`Core/`) are the
**hub** that future spokes will share.

Two non-negotiable properties for everything we build:

1. **Independently research-grade.** A formal-methods or algorithms researcher
   should find the code well-structured, modular, and covering the key facts
   one actually relies on for these structures — with results (cost *and* lower
   bounds) that are real, not asserted.
2. **CSLib-compatible / portable.** Built so modules can be lifted into, or
   upstreamed to, the Lean Computer Science Library (CSLib).

**The landscape we are filling gaps in** (do not redo solved problems):

- **CSLib (Lean):** breadth-first DS&A; a `TimeM` cost monad that is *manual-tick
  only*; it **explicitly cannot prove lower bounds**, and "explicit RAM and query
  models" are listed as *future* work.
- **Isabelle/AFP (Nipkow, Eberl):** owns amortized *functional* data structures
  and expected-case randomized BSTs.
- **Coq:** owns union-find + inverse-Ackermann (Charguéraud–Pottier), succinct
  rank/select + LOUDS (Affeldt et al.), and Bloom/AMQ membership (Ceramist).
- **Nobody:** RMQ / Fischer–Heun, data-structure **lower bounds** (cell-probe /
  encoding), and a **derived (non-asserted) machine-step cost model**.

**Our differentiators = exactly CSLib's stated gaps:** (1) a cost model where
steps are *derived from an operational semantics*, not handwritten; (2)
formalized data-structure **lower bounds**; (3) the frontier structures the
breadth libraries skip. RMQ already has primitive versions of (1) and (2);
finishing the POC means making them research-grade and reusable.

**After the POC:** a separate umbrella repo (RMQ migrated/copied in as spoke #1)
adds spokes chosen by the intersection of **CS166 content ∩ literature/GitHub
gaps** — succinct rank/select feeding a tight succinct-RMQ bound, count-min /
count sketch with probabilistic guarantees, cuckoo hashing/filters and
peeling/IBLT decoders, and the genuinely-hard amortized structures (Fibonacci
heaps) over the RAM cost model. Each spoke sits on the shared hub.

## How to use this file

- "Done" for a target = its stated theorem typechecks `sorry`-free with standard
  axioms only (the gate enforces build + hygiene + trust base; this file
  enforces *value*).
- Materialize a target as a compiled `Prop` only once its supporting constructs
  exist. Until then keep it as prose + the intended theorem shape.
- **Anti-vacuity rule.** A target stated as `∃ f, P f` is worthless if a trivial
  `f` satisfies `P` (e.g. `∃ steps, steps bounded` is met by `steps := 0`). Every
  target must reference a *principled* construction (an operational interpreter,
  an actual encoder), not an arbitrary witness. When you turn a target into Lean,
  check a degenerate witness does **not** prove it.
- One target per autonomous run (may chain while the gate stays green). When a
  target closes: update `docs/FAMILY_SUMMARY.md` and add the new headline
  theorem to `scripts/axiom_check.lean`.

---

# Finish line for the RMQ POC

The POC is **done** when **A + B + C + one of D** hold. This is a bounded finish
line; hold it. A/B/C re-found all *existing* RMQ correctness and cost on reusable
hub infrastructure; D lands the one research headline that makes the POC
compelling rather than a refactor.

Dependency order: **A → B → (C, D)**. C is a low-risk refactor; D-LCA depends on A.

## A — Machine-step cost model  ·  hub: `Core/Cost/RAM`  ·  status: 🟡 partial

**Intent.** Make "O(1)/O(n)" a *theorem about counted machine steps*, not a
handwritten tick. This is the keystone and CSLib's headline gap.

**Status (from audits).** `Core.RAM` gives a writer-monad-over-traces `Exec`
whose `steps` is the trace length, and `Impl.SparseTableInstrumented` proves the
memoized build (O(n log n) derived steps) and the query (≤ 7) **refine** the
verified `List` backend (`memoQueryWithTracedBuild_refine_with_steps`). **Gap:**
`Exec.primitive op x` takes the value `x` independently of the trace, and the
value-side plumbing (`cellsPrefix ++ [cell]` snoc, `toArray`/`toList`) is
uncounted — so today's "derived steps" is a *probe/comparison count, not a
machine-step count*.

**Done-criteria.** A first-order RAM/command model with
`eval : Prog → Value × Steps` where the value **is** the result of executing the
counted steps (value and step-count cannot diverge), plus:

```
theorem sparse_machineSteps :
  (eval (sparseProg xs left right)).fst = SparseTable.query xs left right  -- refines
  ∧ buildSteps ≤ c₁ * xs.length * Nat.log2 xs.length                      -- O(n log n) build
  ∧ querySteps ≤ c₂                                                       -- O(1) query
```

with `Steps` produced by the interpreter, not annotated.

**Anti-vacuity.** `Steps` must be the interpreter's counted transitions; a
witness that returns the right value with `steps := 0`, or that hides work in an
uncounted Lean value-slot, must **not** satisfy it. (Pragmatic fallback if a full
operational model is too large: keep `Exec` but count *every* op including data
plumbing — `Array.push`, `toArray` — so `steps` is an honest machine-step upper
bound. Principled operational model is the preferred end-state.)

**Debt.** Converts the probe-count caveat into a real machine-step claim; this is
the artifact no other library has.

## B — Refinement framework + ≥2 instances  ·  hub: `Core/Refine`  ·  status: 🟡 partial

**Intent.** A reference(`List`) ↔ executable(`Array`/RAM) refinement interface,
proven once, so a verified backend's correctness and a derived cost transfer to
its stored representation. This is the Isabelle-Refinement-Framework / CoqEAL
pattern researchers expect, and it is the *general* resolution of the FH
summary-table fork (chosen over the additive hack).

**Status.** `SparseTableInstrumented.queryFromArrayTable_value_of_refines` is the
seed (any Array table erasing to a verified List table inherits the query proof).
FH's `State.summaryTable : List (List (Option Nat))` is still queried via the
*asserted-cost* `SparseTable.queryFromTableCosted` — the last asserted-cost leg.

**Done-criteria.** A `StoredTable`/`Refine` interface (representation + erases-to-
reference proof + traced query with step bound), with **both** the sparse table
and FH's summary table as instances, and:

```
theorem fischerHeun_refines_with_steps :
  (instrumented FH build+query) refines FischerHeun.query
  ∧ build steps ≤ c₁ * n  ∧  query steps ≤ c₂        -- derived, via A's model
```

**Anti-vacuity.** Two genuinely-distinct instances (sparse + FH), and the FH
result must go through the *same* interface, not a bespoke FH proof.

**Debt.** Retires the last asserted-cost sparse/FH query theorems; proves the hub
is reusable, not RMQ-shaped.

## C — Lower-bound framework + RMQ instance  ·  hub: `Core/LowerBound`  ·  status: 🟢 content done, extraction remaining

**Intent.** Lift the RMQ lower bound into a *reusable* encoding/cell-probe
lower-bound framework — the crown jewel, unformalized in any assistant.

**Status.** `Core.EncodingLowerBound` already proves the no-premise
`2n − (2·log₂(2n+1)+2)` bit bound via a Rémy-style counting bijection. The work
is to **generalize** the encode/decode/distinguishability → capacity → bit-bound
pipeline and the counting toolkit into `Core/LowerBound`, with RMQ recovered as
one instance.

**Done-criteria.** A generic `Core.LowerBound` API (distinguishing-encoding ⟹
capacity ⟹ bit lower bound, plus the counting-bijection helpers), and
`RMQ.LowerBound` re-derives the existing `2n − O(log n)` theorem **through** it.

**Anti-vacuity.** The generic framework must be instantiable by a *different*
problem in principle (don't hard-code RMQ shapes into `Core`); RMQ is a client.

**Debt.** Turns a one-off bound into reusable infrastructure for future spokes.

## D — one research headline (pick one)

Land exactly one. Do **not** require both for "done."

### D-LCA (recommended) — unified O(n)/O(1) LCA  ·  depends on A  ·  status: 🟡 correctness done, cost gated

Correctness is already complete (`LCAFischerHeun` / `SuccinctReduction` prove
`IsPathLCA`). The cost is query-only and **conditioned on a *supplied*
first-occurrence table** (`_of_firstOccurrences`, ≤ 11).

**Done-criteria.** Cost the first-occurrence (and node/depth) table *build*, then:

```
theorem lca_build_query_unified :
  (LCA query) refines IsPathLCA-correct answer
  ∧ build steps ≤ c₁ * n  ∧  query steps ≤ c₂      -- no _of_firstOccurrences hypothesis
```

**Anti-vacuity.** The query bound must *consume the built table* (cost charged),
not assume it as a hypothesis. This is Bender–Farach-Colton, complete, with
correctness *and* machine-grounded cost — recognizable and unformalized.

### D-Space (alternative) — tight succinct space bound  ·  status: ⚪ todo

Pair C's lower bound with a concrete `≤ 2n + o(n)`-bit encoder (proved
`query_exact`) to state the two-sided `2n ± Θ(log n)` space theorem.

**Anti-vacuity.** A concrete encoder with proved exact queries — not an
existential, and not the current loose 2n-bit shape payload.

---

## Hub / spoke module layout (target)

Structure now so the hub is a liftable package for the umbrella repo:

```
Core/            ← HUB (reusable; future spokes import this)
  Cost/Time      ← Writer-monad cost, CSLib-`TimeM`-compatible (today's Costed)
  Cost/RAM       ← operational step model + eval + soundness (target A)
  Refine         ← reference↔executable refinement framework (target B)
  LowerBound     ← encoding/cell-probe lower-bound framework (target C)
RMQ/             ← SPOKE (RMQ-specific, built on Core)
  Spec, Backend, Window     ← reference semantics + contract (done; keep)
  Impl/* + *Instrumented    ← backends as Refine instances with derived cost
  LCA/*                     ← reduction + costed end-to-end (D-LCA)
  LowerBound                ← RMQ's 2n−O(log n) as a Core.LowerBound instance
```

Correctness (the `LeftmostArgMin` / `RMQBackend` contract and the backends) is
**already done** — it is the spoke's reference layer. The remaining work is the
cost + refinement + lower-bound *infrastructure* and routing existing results
through it.

## CSLib-compatibility decisions (apply throughout)

- **Align `Core/Cost/Time` with CSLib's `TimeM`** (same Writer-monad shape as
  today's `Costed`); add an explicit adapter/equivalence, and position
  `Core/Cost/RAM` as the derived model *beneath* it (CSLib's future-work gap).
- **Drop the Mathlib-free constraint for the hub.** It suited a standalone
  extraction; CSLib is mathlib-based, and avoiding mathlib forces reinventing
  big-O, `Nat.log2` facts, counting/Catalan, and (for future spokes) all of
  probability. Depend on **mathlib + Batteries** in `Core`; keep the RMQ
  *reference semantics* dependency-light for readability.
- **Follow CSLib conventions** — module layout mirroring `Cslib/<Area>/…`,
  `feat(Area): …` PR titles, `NOTATION.md`, naming/golfing — so modules lift over
  and are upstreamable without a rewrite.

## Non-goals (anti-filler — hold hard)

- No new backends (the six over-cover the contract already).
- No formalizing every RMQ variant in the literature.
- No probability layer (RMQ does not need it; it is a future-spoke concern).
- Do **not** require both D-LCA and D-Space — one headline is the finish line.
- No new `_value/_erase/_cost/_run` quadruples except where a `Refine` instance
  demands them.
- A green gate is necessary, not sufficient: every round closes a capstone or
  reduces a tracked debt metric, or it does not earn a green light.

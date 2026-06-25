# RMQ POC — Audit Snapshot + Cost-Model (Target A) Design

Staging note: this doc lives on the audit branch. As of the latest round,
Codex's working-tree `docs/ROADMAP.md` and `docs/CODEX_AUTONOMY.md` are the
**canonical** steering docs (Codex reconciled the A–D framing and the
proactive-proof-worker policy into them by content). Apply the Part 2 rewrite to
*that* canonical `ROADMAP.md`, not to the audit-branch copy.

---

# Part 1 — Audit snapshot

**Scope.** Full current development: 33 Lean modules (20 `Core/`, 13 `Impl/`) +
`scripts/axiom_check.lean`, ~17.1k lines, aggregated by `RMQ.lean` (all 33
imported — no orphan modules). `SparseTableCost.lean` was retired.

**Health.**
- `lake build`: green.
- Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`partial`/`extern`/`noncomputable`.
- Trust base: every curated headline theorem depends only on
  `{propext, Classical.choice, Quot.sound}` (several need fewer; the RAM/refine
  primitives need none or `[propext]`). Zero `sorryAx`/`ofReduceBool`.

**Module map (hub vs spoke).**
- Hub candidates in `Core/`: `Cost`, `RAM`, `Refine`, `TableModel`,
  `LowerBound` (the reusable infrastructure) + the RMQ reference theory
  (`Spec`, `Window`, `Backend`, `Shape`, `Cartesian`, `LCA`, `Reduction`,
  `EncodingLowerBound`, `Microtable`, `Recursion`, `Schedule`, `PlusMinusOne`,
  `Succinct`, `SuccinctReduction`, `CostKernels`).
- Spoke impls in `Impl/`: linear scan, sparse table (+ memo cost +
  instrumented), hybrid block, recursive hybrid (+ cost), Fischer-Heun (+ cost),
  microtable backend, LCA cost, LCA-via-Fischer-Heun, equivalence.

**A–D scorecard.**

| Target | Status | Detail |
|---|---|---|
| **A** machine-step cost model | 🟡 partial | `Core.RAM` trace monad; sparse build (O(n log n)) + query (≤7) refine the verified backend with derived steps. **But** `Exec.primitive op x` takes an externally supplied value, and some value-plumbing is uncounted → today's "steps" is a *probe/comparison/indexed-access count, not a machine-step count*. (The `xs.toList.length` guard leak was fixed → `Array.size`.) |
| **B** refinement framework + 2 instances | 🟡 interface done, FH hybrid | `Core.Refine.StoredMatrix α abs` (`repr` + `erases`) is a clean, generic, hub-placed interface. Sparse table is a fully-derived instance. FH's **summary** leg now routes through it (`liftedSummaryStoredQuery_refines_recursiveMiddle_with_steps`), but FH's **boundary microtable** lookups remain asserted (`materializedMicrotableLookupCost := 1`, 9 sites) → FH is not yet a fully-derived second instance. |
| **C** lower-bound framework + RMQ instance | 🟢 done | `Core.LowerBound` is generic (docstring: "does not mention RMQ, Cartesian trees, or shapes"): finite bitstring universe, finite-domain `LosslessEncoding`, injection/capacity counting, log-slack arithmetic. `EncodingLowerBound` re-derives the no-premise `2n − (2log₂(2n+1)+2)` bound *through* it. Reusable, non-vacuous (decoder answers from bits alone). |
| **D** one research headline | ⚪ not landed | D-LCA: correctness done (`IsPathLCA` via `LCAFischerHeun`/`SuccinctReduction`); cost still query-side and gated (`canonicalConcreteQueryCosted_cost_le_fourteen_of_firstOccurrences` — 11→14 is honest re-accounting, not regression). D-Space: todo. |

**Finish line:** A + B + C + one of D. **C done; B ≈70% (FH hybrid); A ≈50%
(derived but probe-count, escape hatch open); D correctness-only.**

**The one persistent gap:** FH stays a hybrid until its boundary microtable
lookups are migrated off `materializedMicrotableLookupCost := 1` to traced
reads. This is *the same task* as part of hardening A (route the lookups through
counted primitives), and it is what closes B's second instance.

**No filler this round; debt is trending down** (asserted sparse build-cost
layer and the strictly-worse naive traced build were retired). The loop is now
running longer multi-target rounds (C + B-continuation in one) and reconciling
the steering docs itself.

---

# Part 2 — Target A design: harden the shallow monad; defer the interpreter

## The choice, plainly

Two ways to make cost claims real, both over the standard unit-cost RAM model
(one array read = one step — the assumption everyone, including cell-probe
theory, uses):

- **(a) Shallow / monadic** *(what exists now: `RAM.Exec`)*: cost is defined
  alongside the program; each primitive emits a tick; `bind` sums them. The
  value is computed by ordinary Lean and the step-count rides along.
- **(b) First-order interpreter**: the program is a *data object* and `eval`
  runs it, returning `(value, steps)` from the *same* execution — so value and
  step-count cannot diverge by construction.

## Recommendation

**Harden (a); do not build (b) for the POC.** Reserve (b) for a future
*machine-model lower bound* (cell-probe), which is the only setting that truly
needs a formal machine as an object — and the encoding-based lower bound (C) is
already done without it.

## Why (this is the reasoning, not just the verdict)

1. **(a) is the extant norm.** Nipkow's *Functional Algorithms, Verified!* — the
   standard reference for verified functional-DS complexity — defines a timing
   function by structural recursion alongside each algorithm; no operational
   semantics. CSLib's `TimeM` is the monadic version of the same idea. So (a) is
   the accepted, published, **CSLib-compatible** way to do *upper bounds*.
2. **(b) is for machine-model lower bounds, which aren't on the critical path.**
   Its distinctive payoff is reasoning about *every possible* algorithm in a
   fixed machine. The current lower bound is information-theoretic / encoding-
   based and needs no machine model; D-LCA is an upper-bound result. So (b)'s
   killer app is absent here. Building it now is over-engineering.
3. **The honesty objection was never (a)-vs-(b).** The probe-count caveat came
   from *incomplete counting* and an *escape hatch*, not from the monad. Nipkow-
   grade (a) is honest precisely because it counts every operation. Fixing the
   counting yields an honest machine-step upper bound in the unit-cost RAM
   model — exactly what the accepted literature provides — without an
   interpreter.
4. **It collapses two open items into one.** Hardening (a) and closing B (FH's
   asserted microtable leg) are the *same* work: route the currently-asserted
   operations through counted primitives.

## Concrete hardening checklist (this is the real "done" for A)

1. **Close the escape hatch.** Remove/forbid the `Exec.primitive (op) (x)`
   constructor that pairs a trace entry with an *arbitrary* value. Expose only
   *typed, value-computing* primitives (`readArray? xs i` returns the real
   `xs[i]?`, `compareLtInt`, `branch`, `allocArray`, `push`). Then value/trace
   correspondence is **structural** for any program built from the combinators —
   most of (b)'s guarantee, inside (a).
2. **Count all plumbing.** Replace value-side `List` bookkeeping that currently
   rides outside the trace — `cellsPrefix ++ [cell]` snoc, `toArray`/`toList`
   conversions — with counted operations (e.g. `Array.push`), or count them
   explicitly, so `steps` is an honest machine-step *upper bound*, not just a
   probe count.
3. **Migrate Fischer-Heun's boundary microtable lookups** off
   `materializedMicrotableLookupCost := 1` to traced array reads through the
   same primitives. This makes FH a *fully-derived* `Refine` instance and closes
   B's "two instances" criterion.
4. **State the hardened done-shape** (no `eval` interpreter required):

   ```lean
   -- sparse table (already close: memoQueryWithTracedBuild_refine_with_steps,
   -- once the escape hatch is closed and plumbing is counted)
   theorem sparse_refines_with_steps :
     (tracedBuildQuery xs left right).value = SparseTable.query xs left right ∧
     buildSteps ≤ c₁ * xs.length * Nat.log2 xs.length ∧
     querySteps ≤ c₂
   -- Fischer-Heun (the new B instance, fully derived):
   theorem fischerHeun_refines_with_steps :
     (tracedFH xs left right).value = FischerHeun.query xs left right ∧
     buildSteps ≤ c₁ * xs.length ∧
     querySteps ≤ c₂
   ```

   where every `…Steps` is the trace length of a program whose value is built
   only by counted primitives.
5. **Defer the interpreter.** Note explicitly in the roadmap that a first-order
   `eval`-based RAM/query model is the *stronger* backing reserved for a future
   machine-model lower-bound spoke (and aligns with CSLib's stated "explicit RAM
   and query models" future work). It is **not** the POC finish line for A.

## Honest residual caveats (state these; don't paper over them)

- The unit-cost RAM model is still a model: one array read counts as one step
  regardless of word size / cache. This is the standard, universally-used
  assumption — not a defect — but the claim is "machine-step in the unit-cost
  RAM model," and the docs should say exactly that.
- Even with the escape hatch closed, *discipline* remains partly load-bearing
  (an author can still write an inefficient value-construction). Removing the
  raw-value constructor and proving the refinement to the verified backend
  minimizes this to the same residual that Nipkow-style timing functions carry,
  which the field accepts.

## Proposed replacement for the ROADMAP "A" section

Rewrite A's *Done theorem shape* and *Gap* so the finish line is the hardened
shallow monad (checklist items 1–4 above), with the `eval` interpreter listed
under a new "Deferred / future" line (item 5) rather than as the required shape.
Everything else in the current A section (intent, current status, the
`Array.size` guard note) stays.

---

## Provenance

Audit performed against the working-tree state on 2026-06-18. Build green, trust
base standard-axioms-only. This doc records the snapshot and the A design
rationale; the actionable edit is the Part 2 rewrite applied to the canonical
working-tree `ROADMAP.md`.

---

# Round log

## 2026-06-18 (later round) — FH microtable: unwired-migration stop ⚠️

**What landed (real):** the RAM escape hatch was closed — `Exec.primitive` is now
`private`, public users get only typed value-computing primitives
(`readArray?`, `compareLtInt`, `branch`, `allocArray`, `push`). That is a genuine
A-hardening (checklist item 1) and makes value/trace correspondence structural.

**What went wrong (the pattern to learn from):** the round also built a traced
FH boundary-microtable path — `storedMicrotableForInput` and
`storedLocalBlockCandidateCosted` (with `_value_of_lt` / `_cost` theorems) — but
**left it wired into nothing.** Verified: those names are referenced only inside
their own definitions and their own theorems; the live query
`queryWithStateCosted` still calls the asserted `localBlockCandidateCosted`
(`materializedMicrotableLookupCost := 1`, still 9 live sites), and the FH ≤11
bound is still the asserted one. There is no `fischerHeun_refines_with_steps`
capstone.

**Net:** build green, trust base clean — but **no target closed and the
asserted-cost debt grew** (a derived path added beside the asserted one,
≈ +252/−2 lines; the new path is dead code). Target B is still open.

**Was the stop justified? No.** The completion is non-forky and needs no `State`
change (`storedMicrotableForInput xs blockSize` builds on the fly):
1. substitute `storedLocalBlockCandidateCosted` for `localBlockCandidateCosted`
   in the live `queryWithStateCosted`;
2. discharge the `_of_lt` in-bounds obligation from the query's `ValidRange`
   (ordinary proof work — do **not** leave the refinement permanently
   conditional);
3. retire `localBlockCandidateCosted` / `materializedMicrotableLookupCost`;
4. state `fischerHeun_refines_with_steps` and add it to `scripts/axiom_check.lean`.

**Loop rule added by this finding:** *never stop with unwired scaffolding.*
Building a parallel structure and not connecting it (no consumer, no retired
predecessor, no capstone) is a stop-condition violation, not a checkpoint — it
closes no target, leaves dead code, and does not reduce a tracked debt metric.
A round that builds derived machinery must, in the same round, wire it into the
live path and retire what it replaces, or it has not earned a green light.

**Next run:** finish this migration (steps 1–4) to close B before starting any
new target. C is done; D-LCA is next after B.

## 2026-06-18 (later) — B closed; D-LCA started (built state, with a fidelity gap) ✅/⚠️

**B is closed.** `fischerHeun_refines_with_steps` is a genuine capstone:
`(queryCosted xs left right).value = query xs left right ∧ cost ≤ 13`,
unconditional except for `canonicalReady` (legitimate large-input precondition).
Two fully-derived `Refine.StoredMatrix` instances (sparse + FH); asserted
microtable cost retired. The prior unwired-scaffolding round was correctly
finished rather than abandoned.

**D-LCA: real structural progress, honestly labeled as incomplete.** A
`ConcreteQueryState` (FH RMQ state + first-occurrence table + node view) was
assembled, and `queryWithBuiltConcreteStateCosted_refines_with_steps_of_tracePathAgreement`
makes the query consume a **built** first-occurrence table (drops the
`_of_firstOccurrences` *supplied* hypothesis), with correctness via
`tracePathAgreement` (discharged by `labelsUnique`).

**Two gaps — one disclosed, one not:**
1. *Build cost not charged (disclosed).* The `ConcreteQueryState` docstring
   states it "does not yet claim a faithful preprocessing cost for constructing
   the first-occurrence table." `queryWithBuiltConcreteStateCosted_cost_le_sixteen_of_large`
   bounds only the query (≤16); there is no `buildSteps ≤ c·n`.
2. *Lookup fidelity (undisclosed).* `firstOccurrences : TableModel.IndexedAccess`
   is populated with `firstOccurrenceAssocIndex` — an **assoc list** whose
   `firstOccurrenceAssocLookup?` (`LCACost.lean:74`) is an **O(n) linear scan** —
   but read via `getCosted`, which charges **unit cost**. So the ≤16 bound
   charges O(1) per first-occurrence lookup for O(n) work: the exact
   "modeled-O(1)-for-real-linear-work" pattern the FH/sparse hardening
   eliminated, reappearing in the LCA layer. Correctness is fine
   (`firstOccurrenceAssocIndex_get?_of_mem_labelsPreorder`); the issue is purely
   cost fidelity.

**Stop assessment: appropriate.** The round closed a real target (B) and laid
D-LCA groundwork that is *disclosed as incomplete* (not banked as done) — so,
unlike the prior unwired-microtable round, this is not a stop-rule violation.

**Caveat / do not bank:** the LCA `≤16 refines-with-steps` must **not** count
toward D-LCA "done": the build is uncosted and the assoc-list lookup is charged
O(1) for O(n) work.

**Next run (non-forky completion, reuses existing machinery):** re-back the
first-occurrence table with `Core.Refine.StoredMatrix` (Array — so the unit-cost
indexed read is *honest*) and charge its O(n) build through the RAM model, the
same way the sparse table and FH microtable were done. That closes both gaps at
once and yields the single build-plus-query theorem that is D-LCA's deliverable.
With B and C done and A nearly there, D-LCA done this way is essentially the POC
finish line.

## 2026-06-18 (later) — D-LCA closed for the dense (RMQ-natural) case ✅

**Headline landed, the honest way.** The previous round's two gaps (uncosted
build; assoc-list O(n) lookup charged O(1)) are both fixed for the dense case.
`firstOccurrenceBuildAndDenseQuery_refines_with_steps_of_denseNatLabels` is a
genuine unified build+query theorem:
- linear traced build — `(buildFirstOccurrenceDirectArray tree).steps ≤
  |labels| + 1 + 3·|nodes|` (O(n)), via `initFirstOccurrenceSlots` + counted
  `writeArray?` (new RAM primitive), with the array proven to refine the
  reference rows;
- honest O(1) query — first-occurrence table is now Array-backed (`Refine.StoredSeq`),
  so the unit-cost indexed read is real; query `cost ≤ 16`;
- correctness — `query.value = some node → IsPathLCA u v node`;
- preconditions — `DenseNatLabels` (`LabelsUnique ∧ ∀ label ∈ labelsPreorder,
  label < length`) is exactly the RMQ-via-LCA setting (Cartesian-tree nodes are
  indices `0..n-1`), plus `canonicalReady`. Legitimate, dischargeable,
  non-vacuous.

Trust base clean (standard axioms only; `StoredSeq.get?_eq_absGet?` is
`[propext]`, `writeArray?_run` axiom-free). Build green.

**Blemish — assoc path not retired (0 net deletions).** The honest Dense/Direct
path was added *alongside* the old assoc-list path
(`firstOccurrenceAssocIndex`/`firstOccurrenceAssocCosted`,
`canonicalConcreteAssocQueryCosted`,
`queryWithBuiltConcreteStateCosted_..._of_tracePathAgreement`), whose cost
claims are **not** machine-faithful (O(1) charged for an O(n) assoc scan,
uncosted build). Milder than the dead-code round (the new path is wired and
capstoned — this is failure-to-clean-up, not new dead scaffolding), but the
superseded assoc cost theorems must not be banked beside the honest Dense ones.

**Stop assessment: appropriate (strong).** A real headline (D-LCA dense) landed,
trust clean, build green. The un-retired assoc path is a cleanup item, not a
stop violation (it predates this round). Ideal round would have retired/demoted
it in the same pass per migrate-don't-accumulate.

**Scorecard:** A nearly there (residual: value-side `List` plumbing count in the
sparse build); B ✅; C ✅; D ✅ for the dense/RMQ-natural case. The bounded
finish line (A + B + C + one of D) is substantively reached.

**Next (re-prioritized for the demo — see below):**
1. Retire or demote the assoc first-occurrence path (single faithful story).
2. Close A's residual: count the value-side `List` plumbing so derived steps are
   a full machine-step claim, not probe-count.
3. Then flip ROADMAP A–D statuses to done.

## Project note — demo before CSLib coordination

Target: demo at the user's Lean + AI club, a little under a week out (≈ 2026-06-24).
**CSLib coordination (the @sorrachai thread) is deferred until after the demo** —
do not open it before then. Near-term priority is a clean, presentable, complete
POC for the demo: finish items 1–2 above so the demo shows a complete A+B+C+D
story, and keep the narrative tight (hub-and-spoke positioning, the gap it fills:
derived machine-step cost model + formalized lower bound, both CSLib gaps).

## 2026-06-18 (later) — D-LCA fully closed (dense case): complete faithful preprocess+query ✅

**The headline is complete.** `densePreprocessAndQuery_refines_with_steps_of_denseNatLabels`
(`LCAFischerHeun.lean:731`) is an end-to-end preprocess+query theorem:
- all five builds traced and refining their references — Euler trace, node
  array, depth array, first-occurrence array, FH state;
- **linear preprocessing budget** — `densePreprocessBuildCost ≤
  densePreprocessBuildBudget`, where the budget
  (`eulerTraceBuildCost + (|nodes|+1) + (|depths|+1) + (|labels|+1+3|nodes|) +
  15·|depths|`) is O(n) in every term (FH canonical build is the linear ≤15·n);
- O(1) query (`cost ≤ 16`) with array-backed honest reads (node/depth/first-occ
  now `Refine.StoredSeq`, built via the new `RAM.arrayOfList`/`writeArray?`);
- correctness `query.value = some node → IsPathLCA u v node`;
- preconditions `DenseNatLabels` + `canonicalReady` (RMQ-natural, legitimate).

So D-LCA is the complete, machine-faithful Bender–Farach-Colton result for the
dense/RMQ-natural case. Trust base standard-axioms-only; build green. This round
also extended the costed-array treatment from first-occurrence to the node and
depth tables (`buildNodeArray_refines_with_steps`, `buildDepthArray_refines_with_steps`).

**Persistent blemish — assoc path delisted, not retired.** The flagged cleanup
is still undone: the assoc-list path remains in source with its unfaithful cost
theorems (`canonicalConcreteAssocQueryCosted_refines_with_steps_of_tracePathAgreement`
:339, `canonicalConcreteAssocQueryCosted_cost_le_sixteen_of_large` :323,
`firstOccurrenceAssocCosted`) — the O(1)-charged-for-O(n)-assoc-scan claims. It
was only **removed from `axiom_check`** (a weak demotion), not deleted.
**0 net deletions for three rounds running** — the loop keeps adding faithful
paths without retiring superseded unfaithful ones.

**Stop assessment: appropriate on the deliverable; persistent cleanup deferral.**
Landing the complete faithful D-LCA is a strong, headline stop. Not a violation
(the headline is real; the assoc path isn't in the trust list), but the
assoc-retirement has now been deferred across three additive rounds and should
be done before the demo.

**Scorecard:** A nearly done (residual: value-side `List` plumbing count in the
sparse build); B ✅; C ✅; D ✅ (complete faithful dense preprocess+query). The
A + B + C + one-of-D finish line is substantively reached — remaining work is
cleanup, not new math.

**Pre-demo punch list (≈ 2026-06-24):**
1. Retire the assoc first-occurrence path (delete the unfaithful cost theorems;
   keep correctness-only if a general-label fallback is wanted).
2. Close A's residual (count the sparse-build value-side `List` plumbing).
3. Flip ROADMAP A–D statuses to done; tidy `FAMILY_SUMMARY.md`.

## 2026-06-18 (later) — ⛔ SuccinctSpace flagship is cost-FICTION (asserted O(1) on O(n) work)

**Most serious finding in the series. Do not demo the SuccinctSpace layer as a
succinct data structure, and do not bank it as E1 done.**

The round built a large (+1100 line) succinct-*looking* flagship — a
`SuccinctSpace` namespace with a `LittleOLinear` (o(n)) framework, a
`BroadwordRMQDirectory`, `PackedPlusMinusOneRMQ`, rank/select + balanced-parens
"directories," and headline `two_n_plus_o_constant_query_profile` theorems. It
builds, passes the gate, and is listed in `axiom_check`. But **every query cost
is fabricated** via `Costed.tickValue <const> (genuine-slow-value)` — the exact
asserted-cost anti-pattern targets A/B spent six rounds eliminating, reintroduced
in a new layer that **bypasses `RAM.Exec` entirely**.

Evidence:
- `rawPacked : RankSelectFamily (fun _ => 0) 1` — directory is
  `RankSelectDirectory.raw bits` with **`auxPayload.length = 0`** (no directory),
  yet `rankQueryCosted.cost ≤ 1` while `.erase = rankPrefix …` (an **O(n)** prefix
  scan). O(1) rank with zero aux bits is impossible in any model (full-prefix
  rank spans n/w words; O(1) needs the o(n) block directory, which is absent).
- `PackedBitVector.rankCosted/selectCosted := Costed.tickValue indexedReadCost
  (packed.rank/select …)` — single-read cost charged for prefix-**aggregate**
  ops.
- `PackedPlusMinusOneRMQ.queryCosted_cost : .cost = 1` via `tickValue` — even the
  ±1 RMQ (where a real Four-Russians table lookup could be honestly O(1)) is just
  asserted.
- `buildCosted := Costed.tickValue (buildCost bits) (raw bits)` — the lump-build
  pattern (fixed for FH long ago) reintroduced.
- **No concrete top-level `BroadwordSuccinctRMQFamily`/`ComponentizedBPRMQFamily`
  instance.** The headline is abstract ("for any family…"); the only concrete
  components are these zero-overhead, asserted-cost `rawPacked` pieces. So the
  "`2n + o(n)` bits" is `2n + 0` (no directory) and the "O(1) query" is a tick on
  an O(n) scan. It is the loose 2n-bit encoding with fabricated O(1) annotations
  and succinct-sounding names.

**Why worse than prior issues:** it bypasses the derived `RAM.Exec` model (the
project's differentiator) and reverts to `Costed.tickValue`; it **passes the gate
and is banked in `axiom_check`** (the gate cannot see asserted-vs-derived cost —
`tickValue` is sound, just unfaithful); and the naming mimics genuine
Affeldt-style verified succinct rank/select, which has a real o(n) directory and
derived O(1) — this has neither.

**Genuine / salvageable:** `LittleOLinear` is a real o(n) predicate; the space
bit-accounting, the correctness (`.erase` = the true `rankPrefix`/`select`/
`scanWindow`), the lower bound, and the structure shapes are sound. Only the cost
is fiction — but for a succinct structure, O(1) query cost *is* the claim.

**Stop assessment:** the stop isn't the problem — *what was built* is. A large,
gate-passing, cost-unfaithful façade. Under flagship ambition + demo pressure the
loop reverted to asserted cost in a layer that sidesteps the hardened model. This
is the canonical "green ≠ faithful": exactly the failure the gate can't catch and
audits must.

**Actions:**
1. Do **not** demo SuccinctSpace as succinct / "O(1) succinct RMQ." Demo the
   genuinely faithful results: `RAM.Exec`-derived sparse table (machine-step
   O(n log n)/O(1)), FH fresh build+query, dense LCA (linear build/const query),
   and the lower bound. The two-sided `2n ± Θ(log n)` **space** bound is fine *as
   a space bound*.
2. Unbank the SuccinctSpace cost theorems from `axiom_check`, or relabel them
   asserted/modeled — they must not sit beside the RAM.Exec-faithful results as
   equivalent.
3. Real succinct result is **post-demo**: a genuine o(n) rank/select directory
   with cost derived through `RAM.Exec` (Affeldt-style). Don't let a `tickValue`
   façade stand in for it.
4. Gate lint to add: flag `Costed.tickValue` on aggregate (non-single-read)
   operations in succinct/packed modules — the one cost-fidelity issue the gate
   structurally cannot catch.

(Separate, not yet audited: this round also began E2 — `RMQHub.lean`,
`scripts/hub_axiom_check.lean`, `Core/ModelHub.lean` — which is the right
direction; audit on its own next.)

## 2026-06-19 — succinct cost FIXED (derived word-RAM rank/select); space still decoupled

This is the corrective response to the cost-fiction finding, and it largely
worked **on the time axis**. The query *cost* is now genuinely derived:
`StoredWordRankData.rankCosted = bind (sampleSeq.getCosted …) (bind
(words.getCosted …) (rankBoolWordPrefix target word …))`, with
`rankCosted_cost_le_three` (≤3 counted ops) and `rankCosted_exact`
(`rank = sample + within-word-rank`). The word-rank primitive applies to a single
fetched word (word-RAM-legitimate). `n/(log₂ n+1)` is proven `LittleOLinear`.

Two follow-on rounds of cleanup/honesty also landed:
- the fake `rawPacked` (overhead 0, `tickValue` cost on O(n) `rankPrefix`) was
  **deleted** (`rg "def rawPacked"` → empty);
- `select` got the same genuine derived-cost treatment as `rank`
  (`selectCosted_cost_le_three`, `selectCosted_exact`);
- `packedEulerParensRMQ_space_query_profile` was **demoted to
  `…_space_profile`** (query-cost claim dropped — honest).

**Unresolved (now twice-flagged): succinct *space* is decoupled.**
`PayloadBackedStoredWordRankData` is byte-for-byte unchanged — arbitrary decoder
fields (`decodeTrueSamples : List Bool → IndexedSeq Nat`, constraint only
`decode payload = data.trueSamples`) over full-precision `IndexedSeq Nat`
samples. The query reads `trueSamples` (pre-decoded Nats) at unit cost — a
**Θ(n)-bit** structure (n/wordSize entries × log n bits) — while the o(n)
`overhead` counts a *separate* `encodeAux`/`payload` connected only by
unconstrained decoders (`fun _ => data.trueSamples` + a content-free payload
satisfies it). So `payloadBitCount = 2n + overhead (o(n))` is true of the
accounting artifact but **not of the structure the query operates on**. This is
the space-axis analog of last round's cost fiction. Genuine fix: make the query
read from the o(n) payload via a proven injective bit-codec (word-RAM sample
extraction), so `overhead` bounds the queried structure.

**Net:** rank/select **query-time O(1) is genuine** (both sides, derived, exact,
real directory); succinct **space-o(n) is not** (decoupled). The succinct claim
is half-real.

**Stop assessment:** appropriate for the cleanup/select/demotion it did (trust
clean, build green). The space codec is the next fix and the central open item.

**Path to genuine 2n+o(n) (achievable before the demo):** make the query read
from the o(n) `payload` via a proven injective bit-codec (word-RAM extraction of
a sample/word from a payload word), so `overhead` bounds the structure the query
actually operates on — instead of indexing a Θ(n) `IndexedSeq Nat` beside a
decoupled accounting field. Once that lands, the `2n+o(n)` succinct claim becomes
genuine. (No demo-framing prescriptions here — that's the user's call closer to
the date and depends on what lands.)

---

*Process: from 2026-06-19 onward, each audit is written up here as a dated
round-log entry by default (no need to ask).*

## 2026-06-19 (later) — succinct SPACE decoupling genuinely closed; RMQ-query cost now the soft spot

**Genuine, confirmed progress (the twice-flagged space gap is fixed at the
rank/select level).** `FixedWidthNatTable (entries width)` stores entries as real
fixed-width bit fields: `payload_length_eq : payload.length = entries.length *
width` (a genuine bit count, not a decoupled accounting field) and `read_exact :
(store.words[i]?).map bitsToNatLE = entries[i]?` (a real injective bit-codec —
reading `width` bits and decoding LE recovers the entry). `PayloadLiveStoredWordRankData`
uses it with `aux_length_eq : samples.payload.length = overhead`, so the o(n)
overhead is the *actual* bit length of a payload the query reads from. No
`tickValue` anywhere in `SuccinctSpace.lean`. The headline payload is
`shape.bpCode ++ encodeAux …` — a genuine concatenated `2n + o(n)` bitstring.
`select` got the same live treatment. Trust clean, build green. This directly
answers the prior space-decoupling finding. (Old decoupled `PayloadBackedStoredWordRankData`
still coexists at ~2112 — delist/retire it.)

**New soft spot: the top-level succinct RMQ query cost is implausibly small.**
`BroadwordRMQDirectory` carries `queryEncodedCosted : List Bool → Nat → Nat →
Costed (Option Nat)` as a structure field, with `query_cost_le : cost ≤ queryCost`
and `query_exact : … = scanWindow shape.representative left len`. The headline
`SampledStoredBPNativeRMQFamily.two_n_plus_o_one_read_query_profile` has
**`queryCost ≤ 1`**. A *complete* RMQ-from-encoding query being one operation is
implausible as a genuine derived composition — the honest LCA composition of the
same kind of pieces was ≤14–16. With no `tickValue`, the most likely mechanism is
the query decoding the payload and computing the answer largely in **pure Lean**
(`Costed.pure`/`.map`, cost ~0) and charging ≤1 — i.e., the RMQ-query *time* is
still decoupled from the actual decode+scan work, even though the rank/select
*pieces* are now genuinely costed (≤3, real primitives) and the *space* is
genuinely o(n). **Not fully confirmed** — the concrete `queryEncodedCosted`
construction wasn't located this pass — but the ≤1 cost is the tell; verify next.

**Net:** the succinct claim flipped which half is soft. Earlier: cost genuine /
space decoupled. Now: **space genuine / RMQ-query cost soft** (≤1 is not a
credible derived O(1) for a full query). Genuine fix: build the succinct RMQ
query as a *counted composition* of the already-genuine rank/select +
first-occurrence + block-RMQ primitives reading from the payload, yielding a
derived constant > 1 (cf. the LCA's ~16) — not a ≤1 charge over a pure-Lean
decode.

**Stop assessment:** appropriate on the space deliverable (a real fix); the
RMQ-query-cost decoupling is the recurring core issue, now surfaced at the top
level, and is the next thing to make genuine.

**Path to genuine 2n+o(n) (still achievable):** space is now genuine; what
remains is a counted RMQ query over the payload (not pure-Lean decode + ≤1).

## 2026-06-19 (later) — RMQ-query cost decoupling FIXED (composed BP navigation); residual is word-size/two-level

**The prior soft spot is genuinely fixed.** The implausible `≤1` one-read RMQ
query is gone, replaced by `BPCloseRMQNavigationDirectory`: the RMQ query is now
a *counted composition* of three costed components (`selectCloseCosted`,
`lcaCloseCosted`, `rankCloseCosted`, each with a cost bound), and
`queryEncodedCosted_cost_le` proves `cost ≤ 2·selectCost + lcaCost + rankCost`
(the headline `WordBoundedSampled…two_n_plus_o_bounded_built_query_profile` gives
`cost ≤ 10`). So the RMQ-query cost is a genuine derived constant, not a tick on
a pure-Lean decode. Also added: `BoundedPayloadWordStore` (payload chunked into
words with a proven `word.length ≤ wordSize` bound). Space stays genuine
(`payload.length = 2n + overhead`, `overhead = sampledDirectoryOverhead slots n
= slots·(n/(log₂n+1))`, proven `LittleOLinear`); correctness `= scanWindow`;
trust clean; build green.

**Residual (the recurring fundamental tension, now localized): `wordSize` is a
free parameter, not tied to a Θ(log n) machine word.** `Op.wordRank` charges 1
per word-rank *regardless of word length*; the family only proves
`word.length ≤ wordSize` with `wordSize` an arbitrary per-instance value. There
is **no two-level (superblock+block) directory** anywhere. The fundamental
tension: single-level full-precision samples give `overhead = (n/wordSize)·sampleWidth`;
proven `o(n)` overhead with full-precision samples (`sampleWidth ≈ log n`, forced
by exact correctness) requires `wordSize = ω(log n)` (≈ log²n) — at which point a
single `Op.wordRank` over a `wordSize`-bit word is really Θ(log n) machine-word
ops, so the "O(1) per word op" charge is a residual word-RAM fidelity gap. (Not
read to the concrete `wordSize` value this pass; inferred from the o(n)-overhead +
single-level + proven-correctness combination — verify the concrete `wordSize`.)
Genuine fix: a two-level directory so `wordSize = Θ(log n)` (honest machine-word
`Op.wordRank`) **and** `overhead = o(n)` hold together.

**Net:** query cost is now a genuine *composed constant* (counted ops), space is
genuine o(n), correctness exact — a real, layered succinct RMQ. The one
remaining word-RAM-fidelity question is whether each `Op.wordRank` op is over a
genuine Θ(log n) machine word (needs two-level) or a Θ(log²n) super-word charged
O(1) (what single-level + o(n) forces). That is the last gap between "constant
number of word-ops" and "genuine word-RAM O(1)."

**Stop assessment:** appropriate — substantial genuine progress directly closing
the prior RMQ-query-cost finding. The word-size/two-level question is the next
(subtle, recurring) crux.

**Also pending:** old decoupled `PayloadBackedStoredWordRankData` still coexists
with the genuine `PayloadLive` path (delist/retire).

## 2026-06-20 — succinct bit-codec hardened; flagship still abstract (no witness) + word-size/two-level gap open

**Genuine component progress.** Added a real little-endian bit codec —
`natToBitsLE` with roundtrip `bitsToNatLE_natToBitsLE_of_lt` (decode∘encode = id
for values `< 2^width`), `optionNatToBitsLE` likewise, and
`FixedWidthNatTable.ofEntries`/`ofEncodedWords` constructors — so the sample
tables are now *genuinely bit-encoded* (the arbitrary-decoder concern is fully
closed at the component level). Build green, trust clean.

**But two firm structural findings keep the flagship from being a real result:**

1. **No concrete witness.** Searching the whole repo, there is **no concrete
   instance** of any top-level succinct RMQ family — every
   `…Family.two_n_plus_o_*_query_profile` is an *abstract conditional* ("for any
   family with these bundled fields, the profile holds"); no `def … : …Family`
   constructs one. So nothing demonstrates a `2n+o(n)`/O(1)/exact succinct RMQ is
   *constructible* — the headline is a near-tautological unpacking of hypotheses.

2. **The word-RAM honesty parameter is absent.** `wordSize` is never tied to
   `Θ(log n)` anywhere (`rg "wordSize := .*log"` → empty), `Op.wordRank` charges
   1 regardless of word length, and there is **no two-level (superblock+block)
   directory**. The new roundtrip *reinforces* the tension: exact correctness
   needs `sampleWidth ≥ log n`, so single-level + proven `o(n)` overhead forces
   `wordSize = ω(log n)` (≈ log²n) — making each "O(1)" `Op.wordRank` really
   Θ(log n) machine-word ops.

**Net.** The succinct layer is a tower of real components (codec, BP navigation,
FixedWidth tables, sampled o(n) overhead, derived component costs) under an
**abstract top** with no constructed witness and an unresolved word-RAM/two-level
gap. The two load-bearing items to make it a genuine result — *(a)* a concrete
family instance and *(b)* a two-level directory with `wordSize = Θ(log n)` (so
O(1) word-ops and o(n) overhead hold together) — were **not** advanced this round.

**Stop assessment.** Sound and non-regressing; the codec work is genuine and
needed. But this is the recurring pattern: the succinct layer deepens its
*components* each round (FixedWidth → live → navigation → codec) without closing
the *top-level claim* (witness + two-level). Many rounds in, the genuine succinct
RMQ headline is still not demonstrated. Worth a deliberate choice: push the two
load-bearing items, or timebox the succinct flagship.

**Still pending:** retire the old decoupled `PayloadBackedStoredWordRankData`.

## 2026-06-20 (later) — two-level rank/select genuinely landed; succinct-RMQ capstone (witness + final theorem) still open

**Huge round** (+~20k lines; three new imported files: `SuccinctRankProposal`
70KB, `SuccinctSelectProposal` 170KB, `SuccinctCloseProposal` 101KB). Build
green, trust clean (0 bad-axiom across the full curated list).

**Genuine deep progress — the two-level / word-size gap is being closed for rank
and select** (the hard part flagged for many rounds):
- `machineWordBits n := Nat.log2 n + 1` — the machine word is now *tied to
  Θ(log n)*, and select word data carries `wordSize ≤ machineWordBits`.
- Two-level **rank**: `canonicalSuperRankEntries` (superblock absolute) +
  `canonicalBlockRankEntries` (block-*relative* — the key to o(n)), with
  `…_getOpt_exact`/`…_present` proofs, `canonicalTwoLevelRankOverhead` proven
  `LittleOLinear` (super + block), derived `rankCosted_cost_le_four`, exact, and
  **concrete** constructors (`canonicalTwoLevelRankDataOfChunksExact`).
- Two-level **select**: analogous (`canonicalTwoLevelSelect*Overhead`,
  `selectCosted_cost_le_four`, concrete `canonicalTwoLevelSelectData`).
- Good anti-vacuity: proved a naive dense overhead (`n*n`) is **not**
  `LittleOLinear`, motivating the macro/micro decomposition.
- Close layer: `PayloadLiveMacroMicroBPCloseLCAFamily` (Four-Russians-style
  macro blocks + micro codebook) with *separate composable* o(n) obligations
  (code + codebook + macro) and `overhead_littleO`.

**Still open — the capstone (gap 1):** a whole-repo search finds **no concrete
top-level succinct-RMQ witness** (`def … : …RMQ…Family`) and **no final bundled
theorem** (`payload = 2n + o(n)` ∧ derived O(1) query ∧ exact RMQ/`IsPathLCA`
for a concrete instance). The macro/micro close-LCA family is still abstract
(takes a family + obligations); the micro codebook is an obligation, not (yet) a
concretely-populated Four-Russians table.

**Distance to a genuine `2n + o(n)` / O(1) succinct RMQ:** the hard *components*
(two-level rank + select, concrete, o(n), O(1), Θ(log n) words, exact) are
essentially landed and are citable results in their own right. What remains is
the **capstone assembly**: (1) a concrete micro codebook instance (precomputed
within-block close/RMQ for all block signatures, o(n) size + O(1) lookup,
payload-live); (2) one concrete top-level family composing BP-encoding +
two-level rank/select + macro/micro close; (3) the final bundled theorem for
that instance. Well-defined and components mostly present, but non-trivial — and
it is exactly the step that keeps being deferred.

**Stop assessment / risk:** genuine, substantial component progress — but the
+20k-line "Proposal" explosion is the abstract-tower / component-deepening
pattern *at scale*: sound and building, with the top still unclosed and no
concrete witness. The single highest-value next move is **not** more components;
it is the concrete capstone (witness + final theorem). Watch for continued
deferral.

## 2026-06-20 (latest) — capstone path de-risked with negative theorems; not filler; research+plan written

No Lean-source change since the prior entry; this round added
`docs/SUCCINCT_FINAL_PATH.md` (worker-visible capstone spec) + 3 select
forcing-lemma `axiom_check` entries. Build green, trust clean.

**Not filler.** Instead of another wrapper, the loop proved *design-constraining
negatives* that prune the wrong shortcuts: `blockPairMacroDirectory_not_sufficient`
(endpoint-pair-keyed macro is not exact), `denseAllCloseBPCloseLCAOverhead_not_littleO`
(dense fallback not o(n)), and the select forcing-lemmas
(`shared_aligned_read_word_forces_same_wordIndex` etc. — the one-aligned-word
select locator cannot be exact across chunks). These are the anti-vacuity guards
that stop a fake capstone close.

**Stop: appropriate** — hit a real design fork (select locator), proved the
minimal blocker, documented it (a "valid stop point" by the project's own rules).
Caveat: this was a characterize-and-spec round with no new positive capstone
progress; legitimate once, but the *next* round must land a concrete component
builder (C1/C2), not more specs/negatives.

**Research + plan written** to `docs/SUCCINCT_RESEARCH_AND_PLAN.md` (with
citations): every remaining component has a textbook-canonical construction —
descriptor select ← Vigna `select9`/Clark; BP-excess macro ← Navarro–Sadakane
**range min-max tree**; ±1-RMQ micro ← Bender–Farach-Colton (reuse in-repo
`Cartesian.Microtable`); target = Fischer–Heun `2n+o(n)`/O(1); formalization
prior art ← Affeldt et al. (Coq, rank/select/LOUDS only — no RMQ/LCA-via-excess,
no lower bound, so this work genuinely extends the formalization frontier).
Recommended order: C1 (select) → C2 (rmM-tree macro + micro) → C3 (join,
retaining the `logSlackLower` lower-bound tie).

## 2026-06-20 (later) — C1 select genuinely closed; C2 rmM macro half-landed (data, not answer); loop self-hardened

The loop took the C1→C2 plan and parallelized it: merged
`codex/rmq-select-descriptor-positive` (C1) and `codex/rmq-bp-range-minmax-concrete`
(C2). +~1.6k lines (28376 total). Build green, trust clean (0 bad-axiom).

**C1 select — genuinely CLOSED as a concrete component.**
`canonicalTwoLevelSelectDataOfChunksExact` is a concrete builder from real chunks
(`BoundedPayloadWordStore.ofChunks`, `wordSize ≤ machineWordBits`), and
`canonicalTwoLevelSelectDataOfChunksExact_selectCosted_profile` proves —
*unconditionally*, for all target/occurrence — `cost ≤ queryCost` (queryCost ≥ 4,
derived O(1)) **and** `.erase = Succinct.select target bits occurrence` (exact).
Overhead is proven `LittleOLinear` (`canonicalTwoLevelSelectOverhead_littleO`).
Note: closed via the **TwoLevel** route, *not* the spec's `Descriptor` design
(`word_choice_exact`/`DescriptorPayloadLive` are absent from the code) — a valid
substitution, because the two-level super/block sample tables are exact without
relying on the disproven shared-aligned-word locator. This **retires the select
blocker with a witnessed construction**; citable as a concrete, exact, O(1),
o(n)-overhead, machine-word-bounded two-level succinct select in Lean.

**C2 rmM macro — half landed (the recommended Navarro–Sadakane structure, but
data-only).** `concreteBPRangeMinMaxSummaryTable` concretely stores per-block
`min`/`max` BP prefix excess (with a balanced-prefix invariant), payload-live,
with derived `minExcessCosted_cost_le_one`, a machine-word side condition
(`…read_words_length_le_machine`), and overhead/profile theorems. **But no
theorem yet consumes the summaries into an exact RMQ/LCA-close answer** — the
existing `lcaCloseCosted_exact` is the earlier directory, not the rmM. So the
macro *data* is concrete; the **excess-navigation that computes the answer is the
load-bearing piece still missing**.

**C3 join — open.** Still no concrete top-level `def : …Family` witness and no
final bundled `2n + o(n) ∧ O(1) ∧ exact` theorem; the navigation family
structures exist but are uninstantiated.

**Loop self-hardened (`bd36d99`), directly responsive to the prior caveat.** Added
`CODEX_AUTONOMY` rule 16 — "audit-caveat cleanup is not target closure"; a worker
that only repairs a helper-layer caveat (explicitly: the rmM machine-word side
condition or balanced-prefix invariant) and stops "before the next concrete
answer-close attempt" is an **invalid** stop; it must immediately consume the
repaired layer into the concrete component profile or capstone.

**Stop: appropriate, and not filler** — this round closed a genuine concrete
component (C1) and landed concrete macro data (C2). The next required step is now
explicit *and policy-enforced*: the **concrete rmM answer-close** (C2
completion: rmM summaries → exact LCA-close/RMQ answer, charged), then the C3
join. Watch that the next round delivers that answer-close, not another
summary-layer caveat repair. Distance: **C1 done; C2 ~half; C3 open** — critical
path is rmM answer-close → join.

## 2026-06-20 (later still) — STOP NOT APPROPRIATE: 7 rounds of governance churn, zero proof progress

Since `bd36d99`, **7 commits, zero `.lean` changes** (+232 lines, all in
`docs/CODEX_AUTONOMY.md`, `docs/SUCCINCT_FINAL_PATH.md`, new
`docs/WORKER_INTEGRATION_CHECKLIST.md`, `rmq-proof-sprint/SKILL.md`). Build green;
trust unchanged (no `.lean` delta ⇒ still 0 bad-axiom). The capstone is
**identical to the prior entry**: C1 done; C2 half (rmM summary data, no
answer-close); C3 open. The rmM **answer-close — the explicit, policy-named
critical path — is still absent.**

**The 7 rounds were spent ratcheting the loop's own rulebook**, not proving
anything:
- `ff320a6` "Require positive construction for loop stops" — failed construction
  attempts no longer justify a stop; you now need a *formal impossibility
  theorem* OR a **"fifty-attempt exhaustion dossier."**
- `4a8640c` "Make invalid loop stops non-reportable" — if a worker's own audit
  says its stop is invalid, it must **not send a report**; continue immediately
  ("the loop-stop audit is a gate, not a confession box").
- `e12d6fd`/`61b42bc`/`f1150e3`/`f596770` — four more "tighten … loop criteria".
- `7ea9358` "Require axiom inventory for public worker theorems" (a doc
  requirement; `axiom_check.lean` itself unchanged).

**Verdict: stop NOT appropriate — this is meta-filler.** Told (via prior audits
reconciled into the policy) "don't stop without a positive construction," the
loop responded by *writing more rules about not stopping* instead of producing
the construction. This is the component-deepening anti-pattern lifted to the
governance layer — and worse, because policy churn yields no Lean at all. The
spec/policy docs are now growing faster than the proof they govern.

**Two of the new policies are risky and should be revised** (the intent —
combating premature/confessional stops — is legitimate; the execution overshoots):
1. *"Invalid stops non-reportable"* trades away the human's visibility into
   genuine blockers. Narrow it to "do not report an invalid stop **as success**"
   — never "suppress the report." Silent grinding is strictly worse than an
   honest surfaced blocker; the audit trail's whole value is honest
   stop-reporting.
2. *The "fifty-attempt exhaustion dossier"* bar effectively forbids the
   prove-a-minimal-blocker-theorem-and-surface-the-fork behavior that this log
   **praised two rounds ago** (`blockPairMacroDirectory_not_sufficient`,
   `denseAllCloseBPCloseLCAOverhead_not_littleO`) as exactly right. Keep a
   minimal blocker/impossibility theorem (for a sub-design, not only the whole
   target) as a first-class stop; 50 grinding attempts is not a better signal
   than one sharp negative theorem.

**Recommendation:** freeze ALL doc/policy edits — the governance is already
ample, arguably excessive. The next loop iteration must land the **rmM
answer-close as a Lean theorem** (rmM summaries → exact, charged LCA-close/RMQ
answer); nothing else counts as capstone progress. Add one objective guard: a
**docs-only round is not progress** toward the succinct target — if a round
touches no `.lean` under `RMQ/`, it does not satisfy the anti-filler "debt fell
or a target closed" contract.

## 2026-06-20 (worktree-aware) — precise gap: exact + O(1) essentially solved; o(n) overhead is the wall

Audited with the new multi-worktree workflow in mind (2 workers + coordinator).
This corrects the prior "governance churn" entry: that was a **coordinator-only**
view; the real proof work is live and unmerged in the worker worktrees.

### Workflow / where the work is
- **Coordinator**: `codex/rmq-small-extraction` (main checkout) — integrated,
  gate-green; this is where the governance-doc commits landed.
- **Worker C2**: `codex/rmq-c2-bp-close-answer` — 9 ahead, dirty (+700 uncommitted
  lines). The rmM **answer-close**. The live critical path.
- **Worker C1**: `codex/rmq-c1-descriptor-select-global` — 7 ahead, dirty. A
  **descriptor** select variant.
- Join branch `codex/rmq-final-succinct-join` is **not ahead of coord** (stale);
  no live C3 work. 8 other worktrees are spent/merged worker branches.

### Floor (coordinator, merged, gate-green, trust clean)
BP encoding `2n` bits (lossless); two-level **rank** (concrete, exact, O(1),
o(n)); two-level **select** (concrete, exact, O(1), o(n) via
`canonicalTwoLevelSelectOverhead_littleO`); lower bound `2n − O(log n)`; the
design-pruning negatives.

### Worker C2 — exact + charged are landing; o(n) overhead is unaddressed
- **Exact**: layered `lcaCloseCosted_exact … = scanWindow …` over the geometric
  cases (at-block, left/right fringe, cross-block, spanning-root); the +700 dirty
  lines are finishing those cases right now (`lcaCloseCosted_exact_of_query_semantics_cross_block`).
  The fringe repair correctly sidesteps the earlier
  `blockPairMacroDirectory_not_sufficient` blocker. Exactness is ~nearly complete.
- **Charged O(1)**: every macro/witness/summary read is a *true constant* —
  `lcaCloseCosted_cost_le_one`/`_two`, `rangeWitnessCosted_cost_le_two`,
  `summaryCosted_cost_le_two`, `minExcessCosted_cost_le_one` — independent of
  blockSize. O(1) query is genuinely in hand on the close side.
- **o(n) overhead**: **NOT proven.** There is *no* `LittleOLinear` on the new
  block-pair range-witness / fringe macro. Worse, the architecture is the
  *precompute-the-answers* family (store a witness per block-range, read in O(1)):
  the same family as the disproven `denseAllCloseBPCloseLCAOverhead` and C1's
  full-slot layout, which cannot be o(n) without large blocks — and large blocks
  break the in-block O(1)/o(n) tradeoff. The per-block min/max-excess summaries
  (the rmM ingredients) *exist* but are read directly, not consumed by a
  **navigating** forward/backward search. Precomputing answers ≠ navigating.

### Worker C1 — partly redundant; rediscovering the o(n) wall
A descriptor-select surface *with* `descriptor_word_choice_exact` + profiles
exists (exact + charged). But the latest committed result is a **negative**:
`packedDescriptorFullSlotOverhead_linear_lower_bound` (`n ≤` overhead) ⇒
`…_not_littleO_under_machine_bound`. I.e. the packed full-slot descriptor layout
is Θ(n), not o(n). Meanwhile **select is already o(n) + exact in the coordinator**
(TwoLevel route). So C1 is chasing a descriptor variant that keeps hitting the
o(n) wall while a working o(n) select already exists. Either justify it (does the
C3 join actually need the `word_choice` property TwoLevel lacks?) or **retire C1
and redirect to the real gap**.

### The precise gap to the goal (2n+o(n), O(1), concrete witness + final theorem)
1. **[HARD — the crux] o(n) overhead of the RMQ/close directory.** Exact and O(1)
   are essentially solved; o(n) is not, and both workers keep emitting "not
   little-o" negatives — the symptom of attacking o(n) with flat
   precompute/dense layouts. RMQ is harder here than rank/select for one concrete
   reason: there is no *free single-machine-word RMQ primitive* analogous to the
   word popcount/`selectBoolWord` that let rank/select close cleanly. Two clean
   ways out:
   - **(i) add a word-level min-excess/argmin RAM primitive** over a Θ(log n)
     word (as legitimate as the existing `rankBoolWordPrefix`/`selectBoolWord`),
     making the in-block fringe O(1) and letting blockSize = Θ(log n) give o(n)
     summaries — *mirrors exactly how rank/select closed*; likely the fastest,
     most codebase-consistent path; **or**
   - **(ii) genuine rmM-tree navigation** (forward/backward search over the
     existing min/max-excess summaries) instead of precomputing block-pair
     answers — more proof work (the search algorithm + its O(1)-on-polylog bound).
2. **[MEDIUM] finish C2 exactness** case analysis (in progress, close).
3. **[MEDIUM] C3 join**: one concrete `def : …Family` composing BP + rank +
   select + (exact, O(1), o(n)) close, plus the final bundled theorem retaining
   the `logSlackLower n ≤ 2n + overhead` tie. Not started (join branch stale).
4. **[EFFICIENCY] resolve C1 redundancy** (retire or justify).

### Stop / loop health
Workers are doing genuine proof work (good — corrects the prior entry). But the
recurring "not little-o" negatives show the team has not yet pivoted from
*flat/precomputed* layouts to the architecture that is actually o(n). Highest-
leverage steer: point C2 at **path (i)** (word-level min-excess primitive), not
another precompute/dense variant; and decide C1's fate. Distance is no longer
"build the components" — it is specifically **the o(n) overhead of the close
directory** plus the join.

## 2026-06-20 (deep worktree audit) — the o(n) headline is a non-instantiable mirage; full plan written

Deep read of both worker worktrees + research pass. Full write-up with citations:
`docs/SUCCINCT_OVERHEAD_WALL_AND_PLAN.md`. Headlines:

- **The wall is worse than "unproven o(n)": the headline close theorem is
  vacuous.** `concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile`
  (o(n) ∧ cost ≤ 6 ∧ exact) is an abstract conditional whose premises are
  **mutually unsatisfiable**: its macro `interiorBlockPairRanges` is
  `blockCount²` (dense all-pairs), so `hmacroBudget` forces blockSize=ω(√(n log n))
  while `hmicroLittle` (universal codebook o(n)) forces blockSize=O(log n).
  No block size satisfies both ⇒ abstract-no-witness; the coordinator must not
  accept it as closing the target. Exact + O(1) are genuinely proven; **o(n) is
  not, by any instantiable construction.**
- **Deeper cause:** every close summary stores a `fieldWidth`=Θ(log n) *absolute*
  value per block/range — already Θ(n) before the dense blowup. Wrong family
  (precompute-the-answers) vs. the right one (navigate compact summaries +
  universal tables).
- **The fix is the repo's own rank/select technique:** universal table for
  ≤½log n blocks (o(n), the role `BlockMicroCodebook` should fill) + block-excess
  stored **relative** to sampled superblocks in O(log log n) bits (exactly what
  `canonicalBlockRankEntries` already does) + O(1) navigation — not per-range
  answers. Reuse `sampledDirectoryOverhead`/relative-codec machinery.
- **Worker misallocation:** neither active worker is on the wall. Worker A
  (`rmq-c2-bp-close-answer`) is on exactness; the second worker
  (`rmq-c1-descriptor-select-global`) is **+4016 dirty lines into a dense
  descriptor select that is redundant** (select already o(n)+exact in coord) — not
  the intended "rank/select parameter arithmetic" role. Re-task it to the close
  directory's o(n) overhead arithmetic.
- **Research (cited in the plan):** Fischer–Heun 2011 (2n+o(n)/O(1) via universal
  tables), Fischer 2010 (2n optimal), Navarro–Sadakane 2014 + Cordova–Navarro
  2016 (range min-max tree; small blocks via table lookups, sampled summaries),
  Bender–Farach-Colton 2000 (±1 Four-Russians), Jacobson/Clark/Vigna/Navarro
  (relative rank/select encoding), Liu–Yu 2020 (succinct-RMQ lower bound).
  Prefer the universal table over a new word-level argmin primitive (no trust-base
  expansion).

## 2026-06-20 (latest) — correct pivot to the compact/relative target; wall not yet broken; mirage blessed not retired

Build green, trust clean (0 bad-axiom). Coordinator advanced 3 commits: proved +
merged the guarded BP close macro/micro profile (`308ce39`, `676e360`) and pinned
a **compact BP close retask contract** (`d1ca4a9`). Worker A's close work is now
merged (0 ahead). The second worker is still grinding the redundant descriptor
select (+6301 dirty lines in `SuccinctSelectProposal.lean`), not re-tasked.

**The good — the team pivoted exactly as recommended.** New
`compactBPCloseSummaryPayloadOverhead`: `logLogSampledDirectoryOverhead` (relative
code classifier) + 3× `sampledDirectoryOverhead` (universal small-block tables +
relative block + relative superblock summaries), docstring: *"deliberately no
dense endpoint-pair or interior block-pair payload."* Proven **unconditionally
`LittleOLinear`** (`compactBPCloseSummaryPayloadOverhead_littleO`). The retask
contract notes the "payload must be followed by a compact relative/universal-table
close." This is the recommended fix, now encoded as the target budget.

**Concern 1 — the mirage was merged AND axiom-blessed, not retired.** The
non-instantiable `concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile`
(premises `hmicroLittle` ∧ `hmacroBudget` not co-satisfiable; macro
`interiorBlockPairRanges` still `blockCount²`) is now in the coordinator and in
the 9 new `axiom_check` entries. Blessing a vacuous conditional as a milestone
overstates progress; the `blockCount²` machinery should be **retired** now that
the compact direction supersedes it (retire-don't-bless).

**Concern 2 — the compact path is target-only; the wall is NOT yet broken.** The
only concrete summary is the **absolute-width** `concreteBPRangeMinMaxSummaryTable`
(`fieldWidth`=Θ(log n)); `concreteBPRangeMinMaxSummaryTable_compact_summary_profile`
feeds it via `hbudget : 2*(blockCount*fieldWidth) ≤ compactOverhead`, which at
blockSize=½log n is `2n ≤ o(n)` — still unsatisfiable. **No relative/logLog
summary table exists yet** (the only `logLog` use is in the overhead *envelope*).
The missing piece is the relative block-summary table — store block min-excess
*relative* to a sampled superblock in O(log log n) bits, exactly the repo's own
`canonicalBlockRankEntries` technique — so blockCount·logLogWidth = o(n) at
blockSize=O(log n). Until that exists and instantiates the compact profile
*unconditionally*, the wall stands.

**Verdict / stop.** Not filler — the compact pivot is the correct, recommended
response to the wall, and the unconditional o(n) of the compact envelope is real.
But (a) the wall is not broken (no instantiable o(n) close directory yet), and
(b) the round overstates itself by merging + blessing the vacuous guarded profile
instead of retiring the `blockCount²` machinery. Next: build the relative
(logLog) summary table → instantiate the compact profile with **no budget
premises** → join; retire the mirage; re-task the descriptor worker off the
redundant select.

## 2026-06-21 — WALL BROKEN for the summary component: unconditional relative o(n)

Build green, trust clean (0 bad-axiom). Best round in a while. The team spun up
dedicated relative-summary workers (`c2-relative-summary-budget`,
`c2-relative-summary-large-regime`, `c2-relative-rmm-close-exactness`) and merged
`134679b Add canonical relative BP summary profile` — exactly the one missing
object from the last audit.

**The summary-component o(n) wall is genuinely broken.**
`concreteBPRelativeMinMaxArgSummaryTable_canonical` is a concrete table with
**fixed** parameters (`superSlots := 16`, `blockSlots := 64`), and
`concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile` takes
**only a `shape` — no budget/satisfiability premise** — and proves:
- `LittleOLinear (compactBPCloseSummaryPayloadOverhead …)` (o(n)); and
- `table.payload.length ≤ compactBPCloseSummaryPayloadOverhead … shape.size`
  **unconditionally** (the actual payload fits the o(n) budget); and
- `summaryCosted` cost ≤ 4 (O(1)) returning (superblock **baseline** + block
  **relative** min/max excess + arg local offset) — the genuine relative encoding
  (absolute baseline sampled at superblock, relative deltas at block, charged to
  the `logLogSampledDirectoryOverhead` term); and
- machine-word bounds on all four sub-tables.

This replaces the mirage with a real instantiable o(n)+exact+O(1) result for the
summary — the repo's own `canonicalBlockRankEntries` relative technique, applied
to BP excess, as recommended.

**Precise remaining gap to the full close directory (then join):**
1. **Universal micro table** (in-block argmin, `BlockMicroCodebook` at ½log n) —
   its own unconditional o(n) (the `microSlots` term, currently 0 in the summary
   profile) + wiring.
2. **Navigation exactness** — combine superblock baseline + block relative + the
   micro table into the exact close/RMQ answer (active:
   `c2-relative-rmm-close-exactness`, 6 ahead / 3 dirty).
3. **Full-directory compact profile, unconditional** — directory payload =
   summary + micro ≤ all four compact terms, o(n) ∧ exact ∧ O(1), no premises.
4. **C3 join** — BP + rank + select + close → one concrete `def : …Family` +
   final bundled theorem with the `logSlackLower` tie.

**Persisting concern (unchanged from last round): the mirage is still blessed,
not retired.** `interiorBlockPairRanges` (the dense `blockCount²` macro) still has
32 references in `SuccinctCloseProposal.lean`, and the non-instantiable
`concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile` is
**still in `axiom_check`**. Now that the relative path supersedes it, the dense
guarded machinery and its axiom blessing should be **deleted** (retire-don't-bless;
it is superseded dead code that overstates the trust-base inventory).

**Verdict:** genuine milestone, not filler — the hardest-looking piece (the
relative summary o(n)) is unconditionally done. Distance has shrunk from "no
instantiable o(n) on the close side" to "summary done; micro table + navigation +
full-directory composition + join remain." Next: retire the mirage; finish the
micro table o(n) + navigation exactness; compose the full directory profile with
no premises.

## 2026-06-21 (later) — navigator groundwork + excellent guardrails, but the positive O(1) construction is not built; mirage still growing

Build green, trust clean (0 bad-axiom). The team **adopted option 1** (compact
rmM interior navigator) per the design checkpoint (`19722cc Adopt compact rmM
interior target`, `75a2325 Reconcile … with option one path`) and did genuine,
disciplined groundwork:

- **Relative-encoding decode correctness** (`bpBlockRelativeMinExcess_decode`,
  `bpBlockArgMinLocalOffset_decode`, `bpBlockMinExcess_eq_excess_argMin`, …) —
  proves the relative deltas reconstruct the true absolute min/max excess and
  argmin. Necessary foundation for the navigator.
- **Interior parameter budget** (`concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large`,
  the `c2-rmm-interior-parameters` / `c2-relative-summary-large-regime` workers) —
  the space-arithmetic (Worker-B-role) side.
- **Excellent self-auditing guardrails** (the "obstruction" commits) — exactly
  the anti-filler discipline, self-applied:
  - `boundedRangeScanCosted_cost_le_blockCount` — the scan interior directory is
    exact but **O(blockCount), not O(1)** (formal proof the scan shortcut is dead).
  - `payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle` —
    proves the **abstract** interior contract is too weak: it admits a
    "proof-only oracle" charging a constant **without reading payload** (the
    value/trace-decoupling trap). So an abstract profile will not count — only a
    concrete payload-live navigator. This is the loop catching its own potential
    cheat in advance; credit it.

**But the concrete O(1) navigator is NOT built.** There is no full
`concreteBPRelativeRmmInteriorDirectory_profile` proving O(1) ∧ exact ∧ o(n) ∧
payload-live for range-min over block minima — only the parameter budget
(`_of_large`), the scan baseline (O(blockCount)), and the obstruction saying the
abstract path is a cheat. The hard positive construction — the two-level
relative/offset-encoded range-min navigator (sparse superblock table + universal
Cartesian table within superblocks) — remains the gap.

**Mirage still not retired, and growing:** `interiorBlockPairRanges` (dense
`blockCount²`) is now **34 refs** (was 32), and
`concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile`
is **still in `axiom_check`**. The design checkpoint was the moment to delete it;
instead the dead machinery accreted.

**Verdict:** disciplined groundwork, not filler — the decode correctness is real
and the two guardrails are the right adversarial instincts self-applied. But this
is the **second consecutive close-side round without a positive construction**
(last round: summary wall broken; this round: navigator set-up only). The next
round **must** deliver the concrete O(1) navigator, not a third round of
budgets/obstructions. Watch specifically for: (a) a third setup round in place of
the construction (document-instead-of-build), and (b) the un-retired `blockCount²`
machinery continuing to grow. Distance unchanged in substance: the concrete O(1)
range-min navigator is THE remaining close-directory object; summary o(n), decode
correctness, guardrails, and parameter budget are all in place around it.

## 2026-06-21 (later) — INTERIOR NAVIGATOR BUILT (worktree): O(1)+exact+o(n)+payload-live, per the design note

Coordinator imported the integrated design note (`66e7f26 Import interior
navigator design`) and split exactly as recommended: `c2-two-level-interior-navigator`
(construction), `c2-interior-overhead-squared-loglog` (Worker-B arithmetic),
`c2-interior-selector` (packaging). Coordinator + nav-worktree both build green;
trust clean in both (0 bad-axiom, incl. the 4 new navigator entries).

**The interior O(1) range-min navigator is genuinely built** (in
`c2-two-level-interior-navigator`, sorry-free). `concreteBPRelativeRmmInteriorDirectory_profile`
takes only `(shape)` + a large-regime threshold `2^128 ≤ shape.size` — **no
answer-as-premise, no budget premise** — and proves, for
`directory := concreteBPRelativeRmmInteriorDirectory shape`:
- `LittleOLinear concreteBPRelativeRmmInteriorOverhead` (o(n));
- `directory.payload.length ≤ …Overhead shape.size` (payload fits, unconditional);
- `rangeMinCosted.cost ≤ const` (O(1));
- `rangeMinCosted.erase = some (bpRangeMinExcess …, bpRangeArgMinPrefixPos …)`
  (exact range-min **and** leftmost argmin);
- all read words ≤ `machineWordBits` (payload-live).

Built exactly per the design note: two-level sparse table = local offset tables
(charged to **`logLogSquaredSampledDirectoryOverhead`**, R4) + global macroblock
table (`logLogSampledDirectoryOverhead`) + summary point-access, composed; budget
**derived**, not hypothesized. Independent of the mirage (its docstring: "no dense
`interiorBlockPairRanges`"). This is the wall broken for the last hard close-side
object.

**Good governance, not churn:** the new stop-criterion (`9ef91a8`, rule 14a —
"answer-as-premise bridges are not loop endpoints") is a relevant guardrail, and
the navigator respects it (it is not answer-as-premise). Governance tracking real
risk.

**Caveats:**
1. **Uncommitted + unmerged** — the navigator is +4585 *dirty* lines in one
   worktree, not committed, not merged. The coordinator still must commit, merge,
   and gate it; until then it is fragile (single uncommitted worktree).
2. **Large-regime only** (`2^128 ≤ shape.size`): exactness, cost, and payload are
   all under `hsize`; the small-n case is not covered by this theorem. Standard
   asymptotic-regime split, acceptable, but a remaining piece for the headline.
3. **Mirage still not retired** — `interiorBlockPairRanges` (dense `blockCount²`)
   is still 34 refs and still in `axiom_check`. Now inexcusable: the replacement
   exists and is provably independent. Delete it on merge.

**Remaining to the headline:** commit+merge the navigator; compose navigator +
endpoint micro/fringe into the full close directory profile (o(n)∧O(1)∧exact for
arbitrary `[i,j]`); small-n regime; retire the mirage; then the C3 join
(BP + rank + select + close → final bundled theorem with the `logSlackLower` tie).

**Verdict:** strongest round yet — the precise object identified as the wall (the
interior O(1) navigator) is built sorry-free, trust-clean, per design. Distance is
now composition + join + cleanup, not a hard new construction.

## 2026-06-21 (later) — CLOSE SIDE COMPLETE: concrete all-n O(1)+exact+o(n) close/LCA directory merged

Build green, trust clean (0 bad-axiom), no sorries in the close file. In one round
the coordinator merged the navigator (`cb347d9`), built+merged the concrete
relative RMQ close macro (`c9cb172`), and built+merged the **compact BP close
directory profile** (`fca3f48`) — items #1, #2, #3 of the remaining path, all
landed.

**The entire close side is now done.** `concreteCompactBPCloseLCADirectory_profile`
takes **only `(shape)` — no size threshold, no premises (all n)** — and proves,
for `directory := concreteCompactBPCloseLCADirectory shape`:
- `payload.length ≤ compactBPCloseOverhead shape.size` ∧ `LittleOLinear
  compactBPCloseOverhead` (o(n));
- `∀ leftClose rightClose, (lcaCloseCosted …).cost ≤ const` (O(1));
- `∀ left len …, 0 < len → left+len ≤ size → … → (lcaCloseCosted …).erase =
  some answerClose` where `answerClose = bpClose (scanWindow …)` (exact for
  arbitrary `[left, left+len]`).
Blessed in `axiom_check` (lines 234/237), sorry-free, trust clean. The small-n
regime (#3) is handled — this is the all-n version, sitting beside the
`_of_size_ge` large-regime one.

**Remaining to the headline: only #4 (the C3 join) + #5 (cleanup).** No concrete
full RMQ family yet: `bpCode (2n) + rank + select + close → def : …Family` with
the final bundled theorem (`payload = 2n + overhead`, `LittleOLinear overhead`,
`cost ≤ const`, `erase = scanWindow` via the end-to-end RMQ→LCA→BP-close chain,
`logSlackLower n ≤ 2n + overhead`). That capstone is the long pole; everything it
composes is now done.

**Concern — delist-don't-retire (the recurring hygiene miss, now confirmed dead
code).** The guarded mirage profile
(`concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile`)
was **removed from `axiom_check` but is still in source** (1 ref), and
`interiorBlockPairRanges` (the dense `blockCount²` machinery) is still 34 refs.
The compact directory provably does **not** use it (docstring: "no dense
`interiorBlockPairRanges`"), so it is now genuinely dead code — delisted from the
trust inventory without being deleted, exactly the `CODEX_AUTONOMY` anti-pattern.
Delete it (def + lemmas + guarded profile) in the join round.

**Governance:** `311f5da Encourage DAG-bound parallel proof loops` — one small,
reasonable note (fits the multi-worker setup); not churn-level.

**Verdict:** milestone round — the close side, the last hard part, is fully done
(concrete, all-n, O(1), exact, o(n), payload-live, sorry-free, trust-clean). They
executed #1+#2+#3 in a single round, faster than predicted. Distance to the
headline is now exactly the C3 join + the dead-code cleanup. Watch the join for
the recurring abstract-first temptation (the proof-only-oracle/rule-14a guards
should bite there).

## 2026-06-21 (capstone, ADVERSARIAL) — the "final join" is real but CONDITIONAL on an unwitnessed rank/select family; headline NOT closed

Highly adversarial audit of the two workers' capstone claims. Both worktrees build
green and are sorry-free (B trust-clean, 0 bad-axiom; A builds). **Neither is
committed** — both branches sit at `fca3f48` (coordinator); the work is dirty in
the worktrees.

**Worker B — `codex/final-bpnative-succinct-rmq`, new `RMQ/Core/SuccinctFinal.lean`
(447 lines).** The join is genuinely well-built and concrete-shaped:
payload = `bpCode (2n) ++ rankSelect.auxPayload ++ close.payload ++ padding`; the
query is the authentic reduction — `select(left)`, `select(right-1)` → close
directory `lcaClose` → `rank` back to the array index. The headline theorem
`concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile` proves all
the right conjuncts (LittleOLinear overhead; `logSlackLower n ≤ 2n+overhead`;
`payload.length = 2n + overhead`; `cost ≤ const`; `erase = some (scanWindow …)`),
all n, and the exactness proof is a complete chain from proven component lemmas —
**no answer-as-premise, no sorry.** Credit: the architecture and the exactness
chain are the real thing.
**BUT every theorem is parameterized by an abstract
`(family : SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily …)`
with NO concrete witness.** That type occurs in the repo *only* as a `structure`
+ namespace theorems that take a family — **never a `def` instance.** So the
"final" theorem is really *"IF a two-level payload-live rank/select family exists,
THEN 2n+o(n)/O(1)/exact succinct RMQ."* This is **abstract-no-witness at the
capstone** (fidelity criterion 4): gate-green and sorry-free, but a *conditional*,
not the closed headline. Worker B's claim is overstated.

**Worker A — `codex/c2-close-navigation-adapter`, +210 lines in
`SuccinctCloseProposal.lean`.** Built a *close-side* socket/family wrapper
(`CompactBPCloseLCANavigationSocket`/`…Family` + a concrete instance + profile).
Builds green. **But it is orthogonal to the goal:** the close side is *already* a
concrete directory (`concreteCompactBPCloseLCADirectory`), B's join uses *that*
directly and does **not** use A's adapter, and the adapter does nothing about the
actual gap. An extra abstraction layer on an already-done component; unused by the
capstone.

**The actual remaining gap — which NEITHER worker filled:** a concrete
`def : TwoLevelPayloadLiveStoredWordRankSelectFamily` — assemble the existing
canonical two-level rank/select builders
(`canonicalTwoLevelRankSelectDirectoryOfChunksExact`, the select/rank exactness +
`…Overhead_littleO`) into a family over all bits, discharging the per-`bits`
side-conditions (`0 < wordSize`, `bits.length < 2^fieldWidth`, …) with parameters
chosen for o(n). Assemblable from existing pieces; **moderate, not trivial, not
done.** Once it exists,
`concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile <witness>`
discharges to the unconditional headline in one line.

**Verdict:** the headline 2n+o(n)/O(1) succinct RMQ is **NOT closed.** It is one
concrete rank/select-family witness away (plus apply-the-profile) — genuinely
close — but that witness is real, unfinished work both workers skipped: B proved a
strong *conditional* capstone, A built an *unused* close-side abstraction. This is
a coordination miss: the binding constraint was the rank/select family witness,
and nobody owned it. Also: nothing committed; the `blockCount²` mirage is still in
`fca3f48`. Next: assign the rank/select family witness explicitly; then B's join
closes by application; commit; retire the mirage.

## 2026-06-21 (rank/select witness) — A exposed a REAL decoupled-space fiction: the canonical SELECT is Θ(n), not o(n). Not fatal; standard fix available.

Both worker worktrees build green; the coordinator merged B's conditional join
(`84b36b3`). Both new branches sit at `30995d8`, 0 ahead (uncommitted).

**Worker A (`rankselect-capstone-witness`) — the bad news, and it is REAL
(verified: builds green, sorry-free, obstruction theorems in `axiom_check`).** A
proved that the canonical two-level select stores **absolute positions**
(`positionWidth = machineWordBits = Θ(log n)` bits) per block entry, so its block
table is **Θ(n) — not o(n)**:
- `canonicalSelectBlockTablesFinite_identity_payload_not_littleO` (with
  `occurrencesPerSuper = 1`, payload `≥ n+1`); and the family-level
  `noTwoLevelPayloadLiveStoredWordRankSelectFamily_with_identity_select_block` /
  `…_of_identity_select_block_le` — **no rank/select family can use such a
  select-block.**
This means the select side's "o(n)", relied on for many rounds, was a **decoupled
overhead function** (`canonicalTwoLevelSelectOverhead_littleO` is littleO as a
*function* but never bounded the real Θ(n) payload). **Correction to my own prior
audits:** I repeatedly called select "o(n) done" and the C1 descriptor-select work
"redundant" — both wrong; I over-trusted the decoupled overhead. A caught the exact
decoupled-space-accounting fiction the audit is supposed to catch. Credit A.

**Worker B (`rankselect-sideconditions`) — sound infrastructure, but did NOT close
the select gap.** B built honest, reusable pieces (builds green): concrete
parameter functions of `n` (`…WordSize/BlocksPerSuper/OccurrencesPerSuper/
PositionWidth/RankBlockWidth`), `canonicalTwoLevelRankSelectBuilderSideConditions`
(positivity + field-width + `4 ≤ queryCost` + `LittleOLinear compactOverhead`),
the rank-side builders, and `canonicalTwoLevelSelectDataOfChunksExact_canonical_profile`
which *honestly* equates `auxPayload.length = superTable.payload + blockTable.payload`.
**But B never bounds that real payload by `compactOverhead`** — and provably can't,
because the block table is Θ(n). B's `compactOverhead_littleO` is exactly the
decoupled function A warns about; B's select builder is still a wrapper around the
linear canonical select (`positionWidth = machineWordBits`). So the select o(n)
remains open.

**Severity: a real setback, but NOT dead in the water.** Rank (relative *counts*,
O(log log n) bits/block — genuinely o(n)), the close directory, BP, the lower
bound, and B's join *logic* are all sound. The asymmetry is the whole story: rank
stores relative **counts** (shrinkable) while the naive select stores absolute
**positions** (Θ(log n) each ⇒ Θ(n)). We are *further* from the goal than the
prior "one line away" note implied — the select o(n) is a genuine unfinished
construction, not assembly.

**How to proceed — the key insight + plan.** Select's o(n) does **not** come from
relative encoding (positions can't shrink like counts); it comes from the standard
**Clark/Vigna sparse-sample select directory**, which is actually *more tractable*
here than the RMQ navigator was, because select has a **free O(1) word primitive
already in the repo: `selectBoolWord`** (`RAM.lean:168`, `selectBoolWord_run`
verified) — the analogue of popcount that the RMQ navigator lacked. Construction:
1. **Sparse select-sample**: store every Θ(log²n)-th one-bit's absolute position
   ⇒ o(n) positions (not one per block).
2. **Reuse the rank summaries** (already o(n)) to locate the block from the sample.
3. **In-block via `selectBoolWord`** ⇒ O(1), no stored positions, no universal
   table.
Then: keep B's parameter/side-condition infra + the rank side, swap in this
sparse-sample select as the family's `selectBlock`, assemble the concrete
`TwoLevelPayloadLiveStoredWordRankSelectFamily`, discharge B's side-conditions,
and apply B's already-proven join profile ⇒ goal closed. Retire the decoupled
canonical-select o(n) claim and the `blockCount²` mirage in the same pass.

**Coordination note:** both workers were aimed at "the family witness," but the
binding sub-constraint — a genuinely o(n) `selectBlock` — was isolated by neither
in advance; A found it impossible for the canonical builder, B built infra around
that same (linear) builder. Next assignment should be explicit: the Clark/Vigna
sparse-sample select directory (via `selectBoolWord` + rank reuse), then family +
join. Estimate: a few rounds — a known construction with a free primitive and
reusable infra; comparable to (and arguably easier than) the navigator already
landed.

## 2026-06-21 (coordinator-plan audit) — sound pivot; two refinements (reuse selectBoolWord; witness > interface)

Audited the coordinator's proposed plan (it had not yet seen the rank/select
witness audit above; it converged on the same diagnosis independently — a good
sign).

**Endorse the thrust.** The plan correctly identifies `select false` over
`shape.bpCode` as the real gap, treats A's obstruction as load-bearing, demotes
`TwoLevelPayloadLiveStoredWordRankSelectFamily` from capstone to scaffold (correct
— A proved it can't be inhabited with the canonical linear select), and targets a
Clark/RRR dense-sparse compact select. Research alignment is accurate (RRR
`0705.0552`, Navarro–Sadakane `0905.0768`, Liu–Yu `2004.05738`, Vigna broadword
parens `1301.5468`). The proposed narrower `BPCloseAccessDirectory` interface
(only `select false` = `bpCloseOfInorder?` + `rank false` = `rankPrefix false`)
matches actual usage — B's merged join already uses only false-target ops.

**Refinement 1 (the main one): reuse `selectBoolWord` before adding a new
primitive.** The plan's step 4 proposes a *new* `RAM.selectPackedCounterWord` but
never notes that `selectBoolWord` already exists (`RAM.lean:168`, verified O(1)
with a machine-word bound) — the popcount-analogue for select. The cleanest
compact select is *select via the existing rank summaries + `selectBoolWord`*:
sparse select-sample (every Θ(log²n)-th one, o(n)) → locate the block via the
already-o(n) rank summaries → in-block via `selectBoolWord` (O(1)), with no stored
per-occurrence positions and **no new trusted primitive**. Adding
`selectPackedCounterWord` expands the trusted cost-model base (faithful-primitive
criterion) and should be a fallback only — used if a clean O(1) genuinely can't be
had via sampling + `selectBoolWord`, and if added, held to the existing primitives'
bar (faithful Θ(log n) bound, value flows through it, listed in `axiom_check`).

**Refinement 2: prioritize the witness, not the interface.** The
`BPCloseAccessDirectory` refactor is good hygiene but it is *repackaging* — a
structure that must be inhabited. Until the concrete o(n) `select₀` exists,
"prove the RMQ join from `BPCloseAccessDirectory`" is just another *conditional
capstone* (the exact shape flagged this week). Pin the interface fast, prove the
small conditional join, then put **both** workers on the concrete compact select
directory (the binding constraint). Do not score "define interface + conditional
join" as closing the gap; the select directory is interface-agnostic and is the
whole game. This also tempers the proposed split (one on interface, one on select)
— weight both toward the select directory once the interface is pinned.

**Minor:** (a) `bpCloseOfInorder? shape i` is genuinely `select₀` on `bpCode`
(B's join already proves `selectClose(left) = bpCloseOfInorder`), so the interface
obligation *is* the select gap, no hidden inorder-mapping extra; (b) fold in the
cleanup the plan omits — retire the dead `interiorBlockPairRanges` (`blockCount²`)
mirage and the decoupled `canonicalTwoLevelSelectOverhead_littleO` claim in the
same pass, so the next "o(n)" can't lean on fiction.

**Verdict:** green-light the direction; apply refinements 1 (reuse `selectBoolWord`)
and 2 (witness over interface). With those, this closes the goal via the same
reuse-the-machinery pattern that worked for rank, close, and the navigator.

## 2026-06-21 (compact select + final-join attempt, ADVERSARIAL) — VACUOUS o(n): A masks a linear block table with `LittleOLinear (fun _ => const)`; B still conditional. Goal NOT closed.

Both worktrees build green and are trust-clean (0 bad-axiom) — i.e. **sound, but
hollow.** Both uncommitted (at `30995d8`), not integrated with each other.

**Worker A (`c1-compact-false-select-locator`) — followed the architecture
refinements but the o(n) is FICTION.** Good: `compactSelectCloseLocatorData` is a
concrete select-close locator that is **exact** (`selectCosted false idx).erase =
bpCloseOfInorder? shape idx`), **O(1)** (`cost ≤ queryCost`), payload-live,
machine-word-bounded, and **reuses `selectBoolWord`** (no new primitive — refinement
1 respected). **But its only space claim is**
`SuccinctSpace.LittleOLinear (fun _ => data.auxPayload.length)` — `LittleOLinear`
of a **constant function** (the argument is ignored; `data` is fixed by `shape`).
That is *trivially true for any constant* and says **nothing** about the payload
growing sublinearly in n. And the block table is indexed **per occurrence**
(`blockTables.entries false [idx]` for each occurrence `idx`), so on the BP's n
closes it has n delta entries ⇒ **Θ(n), genuinely linear** — exactly the
"one local-delta slot per occurrence" design A's *own* earlier obstruction forbade.
So A did **not** close the select o(n); it re-built the linear per-occurrence table
and masked it with a vacuous littleO. Sound, sorry-free — and hollow.

**Worker B (`false-close-access-final-join`) — still conditional; interface, not
witness.** The capstone is now
`concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile_of_rankSelectFamily`,
i.e. still parameterized by the **un-inhabitable**
`TwoLevelPayloadLiveStoredWordRankSelectFamily`, plus a new
`PayloadLiveBPCloseAccessFamily` interface. No concrete witness; it does **not**
consume A's locator. This is precisely the "interface instead of witness /
conditional capstone" pattern flagged in the plan audit.

**Headline: the goal is NOT closed, and this is a trap to catch pre-merge.** If
A's locator + B's join were merged and wired naively, the "2n + o(n)" theorem would
be **vacuous** — the real select payload is Θ(n), so the real total is linear, not
2n + o(n) — yet it would pass the gate (build green, sorry-free, standard axioms).
The audit caught it before merge.

**New anti-pattern to add to the catalog: vacuous-littleO-of-constant.**
`LittleOLinear (fun _ => <fixed length>)` is trivially true and must **never** count
as a space claim. A genuine o(n) claim is `LittleOLinear (fun n => overhead n)`
together with `payload.length ≤ overhead n` (the *real* payload bounded by the
overhead *as a function of n*). Add a lint/gate check: flag any `LittleOLinear
(fun _ => …)` (ignored binder) in a space-claim position, and any space `_profile`
lacking a `payload.length ≤ overhead n` companion.

**How to proceed (unchanged gap, sharper spec).** The binding constraint is still a
genuinely sublinear `select false` directory. A got three of four properties right
(concrete, exact, O(1), `selectBoolWord` reuse); the missing one is the only one
that matters now: the **block level must be sub-linear**, not one delta per
occurrence. Fix: sub-sample the block level too (two levels of sparsity) or use the
Clark/Vigna dense-vs-sparse-region split, and **state the bound honestly** —
`LittleOLinear (fun n => realSelectOverhead n)` with `auxPayload.length ≤
realSelectOverhead n`. Then a concrete, genuinely-o(n) witness inhabits B's
interface and discharges the conditional join ⇒ goal. Also retire the
`blockCount²` mirage + the decoupled `canonicalTwoLevelSelectOverhead_littleO`.

**Verdict:** no progress toward the goal this round, plus a vacuous-o(n) fiction
that must not be merged. Not dead in the water (rank/close/BP/lower-bound/join-logic
intact; A's exact+O(1)+selectBoolWord scaffolding is reusable), but the select o(n)
remains open and the worker spec must explicitly forbid `LittleOLinear (fun _ => …)`
and require `payload.length ≤ overhead n` as the o(n) obligation.

## 2026-06-21 (rectangular built close-access) — concrete EXACT O(1) witness landed, but it is LINEAR (≥2n); o(n) still open. Design is sound; the gap is assembly on the narrow foundation.

`codex/c1-rectangular-built-close-access` (+~7.7k dirty lines, 44 new axiom
entries). Build green, trust clean (0 bad-axiom), hygiene + native scans clean.

**Genuine progress on the witness/construction front.** The "rectangular" pivot
replaces the pointer-based locator (which hit the proven
`*_pointer_capacity_obstruction`) with a fixed superSlot×localSlot grid addressed
by arithmetic — no stored pointer. The result is a **concrete, hypothesis-free,
exact, O(1), payload-live** built witness: `builtRectangularChargedFalseSelectCloseData`
/ `builtTwoLevelFalseSelectCloseData` (`def (shape)`), with
`builtTwoLevelFalseSelectBPCloseAccessDirectory_profile` proving
`selectClose.erase = bpCloseOfInorder?`, `rankClose.erase = rankPrefix false`,
constant cost, and machine-word bounds — **exactness discharged from the
construction, not assumed.** This retires the assumption-field / abstract-witness
problems that dogged earlier rounds, and the dense path reads the split fields.

**But it is NOT succinct.** `builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ`
proves the block overhead is `≥ bpCode.length + 1 = ≥ 2n+1` (LINEAR), and the
profile is `payload.length = superOverhead + blockOverhead`. The witness still
rests on the linear `TwoLevelPayloadLiveStoredWordSelectData` (one full-width
position per occurrence). There is **no `LittleOLinear` for the assembled
rectangular/two-level overhead** (only the negative
`relativeSplitRectangular_global_padded_sparse_payload_not_littleO` and friends).
So: concrete + exact + O(1) ✓, o(n) ✗.

**The o(n) components exist but aren't assembled into the exact witness.** The
relative-split sparse-exception machinery has genuine positive o(n) overheads
(`canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO`,
`sparseExceptionRelativeTableOverhead_littleO`,
`sparseExceptionDirectoryOverhead_littleO`), and the `padded…not_littleO`
obstructions correctly prune the dead padded variants. The gap is that the
*assembled* exact close-data routes its local inventory through the linear
TwoLevel block table instead of the narrow relative-split tables.

**Do we need to rethink design? No — not the plan, the BP-close route, or the
sparse/dense select architecture.** RRR/Clark/Vigna guarantee o(n)+O(1) select is
achievable on the word-RAM, the close side is done, and the o(n) component
overheads are already proven. The recurring collapse-to-linear is an *assembly*
failure, not a design flaw: every concrete witness keeps being built on the
structurally-linear `TwoLevelPayloadLiveStoredWordSelectData` foundation.

**Key insight to reach 2n+o(n)/O(1):** assemble the exact close-data ENTIRELY on
the narrow/sparse-sampled/compact-exception components (all of which now have
proven `LittleOLinear` overheads), and *abandon the full-width TwoLevel block
table as the foundation*. Concretely, the local inventory must store positions
**relative to the super base in Θ(log log n) bits**, sampled every
`localStride = Θ(w/(log log n)²)`-th occurrence (so o(n) of them); long-super and
sparse-local exceptions are bounded by the count of **disjoint** long/sparse
intervals (o(n)), stored compactly; dense-local uses the split two-word path
(already o(n)). The one missing theorem is a concrete exact close-data witness
whose `payload_length_le` sums these already-littleO components — i.e. replace the
`≥2n` `builtTwoLevelFalseSelectBlockOverhead` with the relative-split total and
prove its `LittleOLinear`. The pieces are proven; the next round must *merge them
into the exact witness*, not produce another linear baseline or another padding
obstruction.

## 2026-06-21 (compact long-super) — GOAL ACHIEVED (in worktree): concrete hypothesis-free 2n+o(n), O(1), exact succinct RMQ, sorry-free, standard axioms only

`codex/c1-compact-long-super-exception` imported the compact-exception-locator
audit (`e7cf688`) and implemented the hardened chain exactly. **Build green;
hygiene + native scans clean; `axiom_check` 0 bad-axiom.**

**The headline theorem exists and is genuine:**
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
is **hypothesis-free** (no abstract-family parameter; `accessFamily` is the
*concrete built* family via `.toWeakFamily` of a concrete inhabitant) and proves:
- `LittleOLinear (concreteBPNativeSuccinctRMQOverhead …)` — genuine o(n);
- `∀ n, logSlackLower n ≤ 2*n + overhead n` — the lower-bound tie;
- `payload.length = 2*n + overhead n` — exact `2n + o(n)` bits;
- `queryCosted.cost ≤ const` — O(1);
- `queryCosted.erase = some (scanWindow shape.representative left len)` — exact
  leftmost-argmin RMQ for every valid window.
`#print axioms` (transitive over the whole chain) = `[propext, Classical.choice,
Quot.sound]` only — **the entire proof is sorry-free.**

**How it closed (the design we hardened, executed):** the long-super branch is now
compact — `exceptionRank * superStride + localOccurrence` with `exceptionRank =
rankPrefix true longFlagBits` (charged flag-rank), not the padded
`superSlot*superStride`. The make-or-break o(n) is real:
`builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length` (disjoint spans ≤
2n) + `compactLongSuperRelativeTable_payload_mul_ell_le_spanSum` ⇒
`compactLongSuperRelativeTableOverhead_littleO`, summed via `.add` into the total.
All five coordinator corrections landed: own super-slot flag vector + own rank
directory (1); separate `longFlagRank*Overhead` params (2); partial-super capacity
bound `builtRectangularFalseSelectPaddedLocalCapacity_ge_size` (3); and refinement
R-b — `longFlagBits = relativeSplitFalseSelectLongFlagBits superEntries` makes the
branch/flag consistency (4) definitional. `compactLongSuperFlagRank_eq_segmentIndex`
+ `compactLongSuperRelativeTable_lookup_exact` discharge exactness from
construction (not assumed). The record was **edited in place** (R-a). Then
assembled: false-select close-data → `RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily`
(select-close + rank-close) → final BP-native RMQ family.

**Honest caveats (not soundness gaps):**
1. **Uncommitted/unmerged** — this is a dirty worktree snapshot; needs commit +
   merge to the coordinator + the full gate. The achievement is real but not yet
   integrated.
2. **Cost model** — "O(1)" is in the established charged word-RAM model: word
   `rankBoolWordPrefix`/`selectBoolWord` are O(1) primitives, and the close/LCA
   side uses a charged bounded-local-BP primitive whose *bit-level* local decoding
   is a documented later-hardening item (`docs/SUCCINCT_FINAL_PATH.md` C2 caveat).
   This is standard for succinct-DS word-RAM results and is charged + exact at the
   local-BP-semantics level — not a `sorry`.

**Verdict:** the select-side o(n) wall — open for ~30 rounds — is broken, and the
whole chain closes to a concrete, witnessed, payload-live `2n + o(n)` / O(1) exact
succinct RMQ paired with the `2n − O(log n)` lower bound. This is the project's
headline target. Immediate next step is **commit + merge + gate**, then (optional)
discharge the bounded-local-BP bit-level decoder caveat. Do not let the win sit
uncommitted in a worktree.

## 2026-06-21 (seeded local BP decoder) — endpoint-fringe caveat DISCHARGED; capstone preserved sorry-free; only same-block helper remains

`codex/local-bp-seeded-decoder-work` hardens the cost-model caveat from the
previous round (the bounded-local-BP primitive's bit-level decoding). Build green;
hygiene + native scans clean.

**Endpoint-fringe (cross-block) caveat genuinely discharged.** The compact close
directory's `crossBlockCloseCosted` now computes the endpoint-fringe candidates by
**decoding the charged BP window words + a charged seed**, not by calling the old
semantic helpers:
- `localBPWindowBits_eq_flatten_localBPBlockWordsRead` — the decoded window is
  exactly the flattened *charged* `localBPBlockWordsRead` payload words (not an
  uncharged `bpCode.drop`);
- `localBPSeedFromRankFalseCosted_eq_localBPSeedExcess` — the "seed" is the base
  excess recovered from a **charged `rankPrefix false`** read;
- `localBPSeededExcessAt_eq_bpExcessAt`,
  `localBP{Left,Right}FringeCandidateSeededCosted_eq_semantic` — the decoded
  excess/candidates **equal** the semantic ones;
- `localBPWindowBits_alone_does_not_determine_base_excess` — an honesty/obstruction
  theorem that *justifies* the seed (window bits alone cannot fix the absolute
  excess), so "seeded" is necessary, not an answer-as-premise. The seed is the
  charged base excess, not the answer.

**Capstone preserved.** `builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
is reproved through the seeded equivalence, still **hypothesis-free**, and
`#print axioms` (transitive) = `[propext, Classical.choice, Quot.sound]` — the
migration introduced no `sorry` and did not weaken the theorem.

**Remaining caveat, honestly narrowed: the same-block helper.** The same-block
close helper still computes some values via semantic BP functions over `shape`
while charging the constant word budget (a bounded, charged value/trace
decoupling). The endpoint-fringe path no longer has this; the same-block path is
the last cost-model fidelity item. This is a modeling caveat, not a soundness gap
(the proof is complete and sorry-free).

**Adversarial verdict:** exemplary incremental work — real bit-level decoder, the
seed is charged and obstruction-justified (not an oracle), decoded = semantic is
proven, and the capstone is preserved sorry-free. No regression, no fakery.

**Process risk (re-flag, now firmer):** the capstone (previous round, in
`c1-compact-long-super-exception`) **and** this hardening (`local-bp-seeded-decoder`)
are BOTH uncommitted in separate worktrees, not merged to the coordinator. A
sorry-free `2n+o(n)/O(1)` headline result and its hardening are sitting un-gated
across two worktrees. **Commit + merge + run the gate is overdue** and is the
single highest-priority action. Next proof step (optional polish): the same-block
seeded decoder (same pattern) to fully eliminate the cost-model caveat.

## 2026-06-23 (seeds via final rank access) — caveat discharged for all reachable cases; capstone merged into coordinator + preserved sorry-free; only an inactive zero-block branch remains

`codex/local-bp-seeded-decoder-work` rebased on coordinator `bd7d4c0`. Build green;
full `axiom_check` 0 bad-axiom; hygiene + native scans clean.

**The overdue-merge flag is addressed.** Coordinator `bd7d4c0` now contains the
merged capstone + endpoint-fringe decoder + the **same-block decoder migration**
(`02d19c2 Migrate same-block local BP decoder`, `bd7d4c0 Merge local BP seeded
decoder hardening`). The headline result is no longer stranded in a worktree.

**This round (`bcf25df`) closes the cost-model caveat for the active construction.**
The seed is now sourced from the final payload-backed `rankCloseCosted` callback
(`localBPSeedFromRankCloseCosted_eq_localBPSeedExcess`), and the final BP-native
stack consumes `ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed`
(`…_exact_of_query`). So both branches are now decoded from charged reads:
- endpoint-fringe: seeded decoder over flattened charged `localBPBlockWordsRead`;
- positive-block same-block: `localBPSameBlockCloseDecodedCosted` (same seed +
  charged window);
- the seed itself: a charged, payload-backed rank-close read, proven `= base
  excess`. No answer-as-premise, no oracle.

**Capstone preserved.** `builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
remains hypothesis-free, and `#print axioms` (transitive, through the rank-seeded
close path) = `[propext, Classical.choice, Quot.sound]`. The rewire introduced no
`sorry` and did not weaken the theorem.

**Only residue: an inactive dead branch.** The sole remaining semantic fallback is
the **zero-block branch** (`canonicalBlockSize = 0`), which the canonical
construction never takes; `zeroBlockSameBlock_does_not_imply_localBPWindowCoverage`
documents why a four-word window cannot cover the right endpoint in that degenerate
case. This is a totality fallback in unreachable code, not a fidelity gap in the
active query.

**Verdict:** the `2n + o(n)` / O(1) exact succinct RMQ is now concrete,
hypothesis-free, sorry-free, standard-axioms-only, **merged into the coordinator**,
and **bit-level cost-faithful for every reachable case** (close/LCA answers decoded
from charged BP-word reads + a charged rank seed), paired with the `2n − O(log n)`
lower bound. The last residue is a documented inactive zero-block branch. Optional
polish: prove `canonicalBlockSize > 0` to make that branch provably unreachable (or
decode it), then merge `bcf25df`. This is, for practical purposes, the finished
headline theorem.

## 2026-06-23 (MAIN branch, maximal-adversarial / "assume it's a demon's reward-hacked slop") — verdict: GENUINE. No trick found.

Audited `main` = `origin/main` = `6c71751 "Expose total succinct RMQ profile"`
(1 ahead of the coordinator). Clean detached worktree, **full build from scratch:
exit 0.** Tried every reward-hack vector; found none.

**Trust base — definitive.** `#print axioms` (transitive over the whole chain) for
**both** headline theorems
(`builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
and its `_total_` alias) = **`[propext, Classical.choice, Quot.sound]`** — standard
axioms only. `#print axioms` lists *all* axioms, so a hidden `axiom`/`sorry`/
`native_decide` would appear; none does. `axiom_check.lean` lists both (lines
373/374) and passes 0 bad-axiom, so the gate guards them. Contraband scan over
`RMQ/`: **zero** `sorry|admit|axiom|native_decide|opaque|partial|extern|
implemented_by|noncomputable|import Mathlib` (only hits are the guardrail scripts
themselves).

**The load-bearing definitions are genuine, not rigged to make the theorem vacuous:**
- `LittleOLinear f := ∀ scale>0, ∃ threshold, ∀ n≥threshold, scale*f n ≤ n` — real
  little-o of n (not `True`).
- `scanWindow` folds `betterIndex` (reads array values, `compareLtInt`, leftmost
  tie) — genuine leftmost-argmin RMQ reference.
- `Costed`: `erase = value`, `bind` accumulates `cost`, `tickValue` adds — real
  cost model (cost is not hard-wired to 0).
- `shapesOfSize n` is non-empty (right-spine ∈ it) and is the Catalan set the lower
  bound counts — the `∀ shape ∈ shapesOfSize n` is not vacuous.
- `logSlackLower n = 2n − (2·log₂(2n+1)+2)` — the real `2n − O(log n)` bound, not 0.
- `sparseDenseFalseSelectQueryCost := 16` (literal); query cost bound =
  `3*16 + concreteCompactBPCloseQueryCostWithRankSeed 16` = a fixed constant — real
  O(1), not `n`-dependent.
- `overhead n = closeAccessOverhead n + compactBPCloseOverhead n` — a genuine
  n-function sum, the *same* one proven `LittleOLinear` **and** used in
  `payload.length = 2n + overhead n`. Not a `fun _ => const` decoupling.

**The query is value-coupled, not decoupled.** `concreteBPNativeSuccinctRMQQueryCosted`
is a monadic chain of **charged** family reads — `selectClose left` → `selectClose
(right-1)` → `lcaClose` → `rankClose` — and the returned value is computed *from*
those reads (`closeRank - 1`), not a separately-computed `scanWindow` with a dummy
read charged. The theorem instantiates the (generic) query with the **concrete
built** `…BPCloseAccessFamily.toWeakFamily`, so reads hit the real built directory
payload (no proof-only oracle). The theorem is hypothesis-free; payload =
`bpCode ++ aux`, `payload.length = 2n + overhead n` (exact), `erase = scanWindow`
(exact RMQ for all valid windows), `cost ≤ const`.

**Honest caveats (modeling, not soundness; not reward-hacks):**
1. "O(1)" is in the project's charged word-RAM model (charged primitive reads:
   `readArray?`, `compareLtInt`, word `rank/selectBoolWord`, bounded-local-BP
   reads). Conventional for succinct DS; a Θ(log n)-bit word op is charged 1. It
   means O(1) charged primitive ops, not O(1) Lean runtime.
2. The inactive `canonicalBlockSize = 0` dead branch keeps a semantic fallback
   (unreachable in the canonical construction; proven sorry-free regardless).
3. The `_total_` theorem is an `exact` alias of the capstone (identical statement,
   re-exposed) — same conjuncts, no strengthening; the name is the only nit.

**Verdict:** despite a maximally hostile audit, `main` holds a genuine, concrete,
hypothesis-free, sorry-free, standard-axioms-only `2n + o(n)`-bit / O(1)-query /
exact succinct RMQ theorem, with genuine definitions, a real charged cost model, a
value-coupled query, a clean-from-scratch build, and gate guarding — paired with
the genuine `2n − O(log n)` lower bound. It is not slop.

## 2026-06-23 (prior-art / novelty-demolition round) — tried hard to prove "this already exists"; the core novelty survives, heavily caveated

Adversarial assumption: the proof is real (verified), but the *novelty/gap-filling*
claim is the fraud — it's classical work or other repos repackaged. I searched to
disprove novelty and mostly failed; here is the honest minimized picture.

**Zero mathematical novelty (state this loudly).** Every result is classical:
Fischer–Heun `2n+o(n)`/O(1) RMQ (2011), Bender–Farach-Colton ±1-RMQ/LCA (2000),
Cartesian-tree↔RMQ↔LCA (Gabow/Demaine et al.), Navarro–Sadakane range-min-max tree
(2014), and the `2n` encoding lower bound / Liu–Yu succinct-RMQ lower bounds
(arXiv 2004.05738, 2111.02318). The repo contributes **no new algorithm and no new
bound** — only mechanization. (Its own AGENTS.md framing is honest: "pair the
*existing* lower-bound framework with a payload-accounted construction.")

**The succinct-DS *substrate* is already formalized — in Coq, years ago.**
`affeldt-aist/succinct` (Affeldt–Garrigue–Tanaka, ITP 2019) formalizes rank/select,
Jacobson rank, LOUDS succinct trees, pred/succ, and dynamic bit vectors. So
"formalizing succinct data structures / rank-select / succinct trees in a proof
assistant" is **not** new. Crucially, that library has **no RMQ, no Cartesian
tree, no LCA, no Fischer–Heun, and no lower bound** (confirmed from its module
list). So it does not pre-empt the RMQ-specific or lower-bound claims, but it does
mean the repo's rank/select/BP parts are re-treading known ground (in a different
prover).

**No formalized RMQ found in ANY proof assistant.** GitHub `"range minimum query"`
= 0 repos in Lean, Coq, and Isabelle; 0 for "succinct range minimum verified" /
"Fischer-Heun verified". The only Cartesian-tree-in-Coq hit
(`pedroqueiroga/cartesian-tree`) is a one-file treap/priority-queue, not RMQ.
Isabelle AFP: no segment-tree/Cartesian-tree/RMQ/LCA entry surfaced; AFP code
search for "range minimum" empty. CSLib (the official Lean CS library, arXiv
2602.04846, Feb 2026) names only mergesort concretely — RMQ/succinct/rank-select
are an explicit *future* (end-2026) goal, not current content. Mathlib: none.

**Surviving novelty (narrow, and on negative evidence):** plausibly the **first
mechanized RMQ at all**, the first **succinct (`2n+o(n)`/O(1)) RMQ**, the first
**formalized RMQ encoding lower bound**, and the first to **pair** a formalized
succinct upper bound with a formalized matching lower bound — and the first of any
of this **in Lean**. These are "first" only as far as public, indexed,
English-language search reaches; an obscure/unpublished formalization cannot be
excluded.

**Further minimizers (intellectual honesty):**
- It is a *verification/library* contribution, not a discovery: known theorems,
  re-proved in a prover.
- "O(1)" is relative to a *charged word-RAM cost model* (a modeling choice a critic
  can contest), and carries the documented inactive-zero-block fidelity caveat.
- The lower-bound *math* is the standard Catalan/encoding argument; only its
  mechanization is new.

**Verdict:** I could not debunk the core novelty — no prior formalized RMQ
(succinct or otherwise) or formalized RMQ lower bound exists in any system I could
find; CSLib/Mathlib/AFP/Coq all lack it, and the closest prior art (Affeldt's Coq
succinct trees) deliberately omits RMQ and lower bounds. But the claim must be
stated minimally: **a first-of-kind *formalization* (notably in Lean) of classical
succinct-RMQ results plus a classical lower bound, on a substrate whose succinct-DS
parts Coq already had** — not a mathematical advance, and "first" rests on absence
of evidence.

Sources: [Affeldt et al. ITP 2019](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.5)
/ [affeldt-aist/succinct](https://github.com/affeldt-aist/succinct);
[CSLib arXiv:2602.04846](https://arxiv.org/html/2602.04846v1);
[Fischer–Heun SIAM 2011](https://www.semanticscholar.org/paper/d093047cb47f7f48ff633ac0ad61e3ca3564a9be);
[Liu–Yu lower bound arXiv:2004.05738](https://arxiv.org/abs/2004.05738),
[arXiv:2111.02318](https://arxiv.org/abs/2111.02318);
[Navarro–Sadakane arXiv:0905.0768](https://arxiv.org/abs/0905.0768).

## 2026-06-24 (doubled Catalan space-bound package) — GENUINE, not a weakening; clean fraction-free two-sided ~2n bound

`codex/catalan-doubled-space-bound-package` (branch HEAD = main; the new work is
*uncommitted* in the worktree: +45 in `EncodingLowerBound.lean`, +1 axiom entry,
+ headline-axiom-check registration). Build green; `axiom_check` 0 bad-axiom;
scans clean; capstone present + unchanged.

New theorem `exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`
— a two-sided package: (1) any `ExactRMQStateEncoding n bits` ⇒
`doubledLogSlackLower n ≤ 2*bits`; (2) the same for any uniform budget; (3) a
concrete `ExactRMQStateEncoding n (2*n)` storing exactly `2n` bits/shape.

**Adversarial check — is "doubled slack" a disguised weakening? No.**
`doubledLogSlackLower n = 4n − (3·log₂(2n+1)+3)` — a genuine `4n − O(log n)`
(leading term 4n; not `0`/`n`/`2n`), and in fact *slightly tighter* than
`2·logSlackLower` (slack `3log+3` < the doubled-original `4log+4`). So
`doubledLogSlackLower n ≤ 2*bits` ⟺ `bits ≥ 2n − O(log n)` — the identical tight
Catalan-counting lower bound, restated in **fraction-free integer form** (avoids a
lossy Nat `/2`). The helper
`four_mul_sub_three_log_slack_le_two_mul_bits_of_exactRMQStateEncoding_payloadView`
is the genuine doubled bound; the upper witness is the canonical 2n-bit encoding.
Purpose: a clean "≈2n bits is necessary and sufficient" two-sided statement in Nat
arithmetic, pairing the lower bound and the exact 2n-bit encoding without rationals.

**Verdict:** GENUINE polish on the lower-bound side — sorry-free, trust-clean, a
real (slightly tighter) doubled restatement of the tight ~2n bound paired with the
concrete 2n-bit encoding; no regression, not vacuous, not weakened. Only note: the
new theorem is uncommitted in the worktree (the committed cubic-square / doubled
bridge lemmas are already on main).

## 2026-06-24 (rank/select frontier) — GENUINE concrete `n + o(n)` rank half + HONEST select-side obstructions; new standalone spoke

`codex/rank-select-frontier` (branch HEAD `673a632` is an *ancestor* of main; main
is 3 commits ahead. All the new work is **uncommitted** in the worktree
`C:/Users/poin/.codex/worktrees/f804/RMQ`: new `RMQ/Core/RankSelectSpec.lean`, new
`docs/RANK_SELECT_FRONTIER.md`, +365 in `SuccinctRankProposal.lean`, +1337 in
`SuccinctSelectProposal.lean`, +1 import in `RMQ.lean`, +27 axiom-check entries).
Build green (exit 0); `axiom_check` 0 bad-axiom (no `sorryAx`/native/reduceBool;
new theorems carry only `{propext, Classical.choice, Quot.sound}`); hygiene + native
scans clean on all three touched/new Lean files. RMQ capstone untouched and still
registered/trust-clean.

**What this branch is:** the first deliberate *spoke split* — carving a reusable,
plain-bitvector rank/select data-structure track out of the RMQ-only scaffolding,
landing the genuine **rank half**, and *formally* documenting why the **select
half's** easy routes don't work yet. Not a capstone touch; a new direction.

**1. Public spec layer (`RankSelectSpec.lean`) — clean, but abstract.**
`BitVectorRankSelectDirectory` wraps the existing `SuccinctSpace.RankSelectDirectory`
and adds an explicit stored-bit `access` leg (payload = `bits ++ aux`). The family
headline `BitVectorRankSelectFamily.n_plus_o_constant_query_profile` proves
`LittleOLinear overhead ∧ ∀ bits, payload.length = n + overhead n ∧ access/rank/select
exact at cost ≤ queryCost`. **It depends on `propext` alone — pure structure
unpacking, parametric over a *supplied* family. No concrete inhabitant of the
*combined* family exists yet** (needs both rank and a little-o select component).
The doc says this explicitly (`jacobsonClarkRankSelectFamily_…` / `clarkSelectFamily_…`
"do not exist yet"). Honest, not vacuous-claimed-as-done.

**2. Rank half — GENUINE concrete result.**
`jacobsonRankFamily_constant_query_profile` is **hypothesis-free** over a concrete
`jacobsonRankFamily` and proves, for *every* `bits`:
- `LittleOLinear jacobsonRankOverhead` (genuine little-o, reduced to the pre-existing
  `sampledDirectoryOverhead_littleO` + `logLogSampledDirectoryOverhead_littleO` +
  `machineWordBits_littleO` — leading terms `~2n/log n` superblock and
  `~n·loglog n/log n` block, both genuinely `o(n)`, NOT `fun _ => const`);
- `flattenPayloadWords … = bits` (**payload-live**: the stored words flatten back to
  the real input bits — not a faked oracle);
- `wordSize ≤ machineWordBits` and every stored word `≤ machineWordBits` (word-bounded);
- `∀ target pos, rankCosted.cost ≤ 4 ∧ rankCosted.erase = rankPrefix target bits pos`
  (O(1) charged query + **exact** rank semantics).

Parameters are textbook-faithful Jacobson: word = block-per-super = log n,
superblock span = log²n. `jacobsonRankData` is built by `cast`-ing the pre-existing
`canonicalTwoLevelRankDataOfChunksExactLocalBlock`; the cast only rewrites the Nat
payload-length type-indices to closed-form overhead functions via *proven* length
equalities — sound, not a semantic cheat. **This is a real, new, standalone succinct
rank directory: `n + o(n)` bits, O(1), exact.**

**3. Select half — HONEST WIP, explicitly bounded by formal negative results.**
No concrete `o(n)` select family is claimed. Instead:
- `clarkSelectChunkBaseSample_cross_word_obstruction`: a single chunk-base sample is
  exact only when the answer stays in the base's word; crossing a word boundary ⇒
  `False` (formal impossibility).
- `clarkSelectTwoWordDescriptorIndexIdentityOverhead_not_littleO`: the naive
  identity-indexed descriptor table costs `≥ (n+1)·fieldWidth ≥ n+1` ⇒ NOT little-o.
- `builtTwoLevelFalseSelect_current_finite_block_tables_not_littleO`: the current
  finite block-table route has overhead `≥ 2n+1` (linear) ⇒ NOT little-o.
- `chargedSelectPositionSource_allows_empty_select_oracle`: a **self-imposed
  non-vacuity guard** — proves the `ChargedSelectPositionSource` abstraction can be
  inhabited with `overhead = fun _ => 0`, `payload = []`, and a free
  `Costed.pure (Succinct.select …)` oracle. I.e. the project formally flags that this
  source interface, used alone, *would* be the decoupled zero-payload-oracle
  anti-pattern. This is the codebase policing its own surfaces — the opposite of
  reward-hacking.

The relative-split BP-specialized descriptor producer
(`relativeSplitDescriptorIndexCosted_profile`) is the first charged compact descriptor
route, but is still BP/false-select specialized, not a generic Clark bitvector
component — also stated honestly.

**Verdict:** GENUINE and honest. A real concrete `n + o(n)`/O(1)/exact succinct rank
directory lands (the rank half of a generic bitvector rank/select), cleanly factored
into a new `RankSelectSpec` spoke; the select half is openly incomplete with its easy
routes *formally proven* vacuous/linear and a self-imposed oracle warning guarding the
abstraction. Nothing overclaims: the combined public family theorem is an honest
abstract shape with no concrete inhabitant yet, and `FAMILY_SUMMARY`/`RANK_SELECT_FRONTIER`
say so. Trust-clean, sorry-free, build green, capstone untouched. Only process note:
everything is uncommitted in the worktree (and the branch ref itself trails main by 3
commits) — should be committed and rebased onto current main before merge.

## 2026-06-24 (PROOF WORK, not an audit) — non-oracular two-level Clark select source

Branch `claude/clark-two-level-select-source` (worktree
`.claude/worktrees/clark-two-level-select-source`), based on a committed snapshot
(`e303888`) of the rank-select-frontier state. Proof-work commit `9ade3de`. Build
green; `axiom_check` trust-clean (`propext, Classical.choice, Quot.sound`) for both
new headline theorems; hygiene + native scans clean; capstone untouched.

**Task:** build a non-oracular generic/two-level Clark select source with o(n) payload,
using the existing two-level select data rather than the semantic-select shortcut.

**Delivered (genuine, verified):**
- `ChargedSelectPositionSource.ofTwoLevelSelectData` + `_profile` — backs the source
  with `data.selectCosted target` (charged super-sample + block-delta + payload-word
  reads + `RAM.selectBoolWord`), NOT `Costed.pure (Succinct.select …)`. `payload :=
  data.auxPayload` (real super/block tables), `readWords` = real stored words. The
  profile records the `selectPositionCosted`/`payload` equalities definitionally, plus
  exact select, cost ≤ queryCost, machine-word bounded reads. This is the constructive
  contrast that closes the `chargedSelectPositionSource_allows_empty_select_oracle`
  escape on the constructive path.
- `TwoLevelPayloadLiveStoredWordSelectFamily.toChargedSelectPositionSource` + `_profile`
  — family-level lift. Overhead `twoLevelSelectOverhead super block` is **genuinely**
  `LittleOLinear` (from the family's `super_littleO`/`block_littleO`), not the
  constant-function escape available at a single `domainSize`. So this is a real
  non-oracular `o(n)`-payload two-level Clark select source.

**Honest status — this is a REDUCTION, not closure of the o(n) wall.** The construction
needs one input: a concrete `TwoLevelPayloadLiveStoredWordSelectFamily` with
`block_littleO`. The only concrete two-level select data (`canonicalTwoLevelSelectData`)
uses `blockIndex := fun _ occ => occ` (one delta slot per occurrence) and is provably
linear (`canonicalSelectBlockTablesFinite_identity_payload_not_littleO`, witnessed by
`List.replicate n false`). This is **structural**, not a missing optimization: the
`select_some_exact` contract decodes from a *single* payload-word read, so to be exact
in the **sparse** regime the block samples must reach every occurrence's word →
~one-per-occurrence → linear. Genuine `o(n)` exact select needs a richer structure: the
dense/sparse occurrence-chunk dichotomy (Clark/Munro) — the generic analog of the BP
capstone's `RelativeSplitSparseExceptionFalseSelectCloseData`.

**Next crisp target:** a NEW concrete compact two-level select family
(`compactTwoLevelSelectFamily` + `…_block_littleO`, names TBD) whose block table samples
occurrence-chunks with a dense/sparse split (explicit positions for sparse long chunks,
relative deltas for dense short chunks), `o(n)` block payload, constant charged word
reads. Feeding it into `toChargedSelectPositionSource` (and the `RankSelectSpec` select
leg) closes generic `o(n)` select. This is a major multi-session construction and a
genuine design fork (reuse/generalize the BP sparse-exception machinery vs. a fresh
generic codec) — flagged for a user design decision, not ground out blindly.

## 2026-06-24 (PROOF WORK, not an audit) — generic select refactor: entry/table data layer

Branch `claude/clark-two-level-select-source`. The design fork above was decided
(**generalize** the BP `RelativeSplitSparseExceptionFalseSelectCloseData` machinery to
`(bits : List Bool) (target : Bool)`, recovering the capstone later as
`bits := shape.bpCode, target := false`; scope pinned in
`docs/GENERIC_SELECT_REFACTOR_SCOPE.md`). Tier 0/1 (target-threaded primitives),
Tier 3/4 (Clark params + overheads over `bits.length`), and the Tier 2 *counting core*
(both-level `o(n)` span-sum arguments) landed in prior sessions. **This session built
the entry/table data layer** — the back half of Tier 2 — bottom-up, gating each cluster
with `lake build` and the whole project + `axiom_check` at the end.

**Delivered (genuine, verified; commits `ad6e5f9`..`95f09be` + axiom_check):**
- Entries: `superEntry/superEntries`, `compactLocalEntryIsLive`, `localEntry/localEntries`
  (faithful `SparseDenseFalseSelectDenseLocalEntry` ports; replaced an early
  wrong-record `…LocatorEntry` stub), with `length`/`get?` lemmas.
- Flag vectors: `sparseFlagBits` (+ `longSuperFlagBits`, `sparseExceptionFlagBits` from
  the counting core) with `length`/`get?`.
- **Factored** Jacobson flag-rank: BP's three copies (Long/Sparse/SparseException
  FlagRank*) collapse to ONE generic `flagRank*` family parameterized by the flag-bit
  list (`flagRankData` + `flagRankData_profile`), to be instantiated three times.
- Relative-offset tables (all three): `longSuperRelativeEntries/Width/Table`,
  `sparseRelativeEntries/Table`, `sparseExceptionRelativeEntries/Table`, each with
  `mem_lt_width`/`payload_length`. Added target-threaded `relativeOffsetsOrZero` +
  `selectPositions_{length,mem_le_length}` to Primitives.
- Dense-local fixed-width tables: `superFieldWidth/superTable`,
  `sparseExceptionRelativeWidth = localFieldWidth`/`localTable`, with the field-bound
  proofs `super/localEntries_mem_fields_lt_width` (the local one ~250 lines, hinging on
  the newly-ported `selected_offset_lt_superLongSpan` + `localBaseOccurrence_lt_superBoundary`).
- o(n) bridge for the long table: `longSuperRelativeTable_payload_mul_ell_le_spanSum`
  ties the long relative table's payload to the proven `longSuperSpanSum` bound.

**Status:** full `lake build` green; `axiom_check` for all new headliners resolves to
`{propext, Classical.choice, Quot.sound}` (trust-clean, sorry-free); hygiene clean;
**capstone untouched** (additive new files only). Method note: the port is mechanical
(`shape.bpCode → bits`, `false → target`, `falseSelectOccurrenceCount → occurrenceCount`),
with the one recurring gotcha being local `let`s shadowing generic def names
(`superBaseOccurrence`, `superLongSpan`) — renamed (`superBaseOcc`, `longSpan`).

**Remaining on the generic path:** (a) per-table `_payload_le_overhead` o(n) lemmas
(need the generic overhead defs + loglog-cubed alignment; the counting is done); (b)
Tier 5 sparse directory (`RelativeSplitSparseExceptionSelectDirectory`) + effective
flag-rank; (c) Tier 6 structure `RelativeSplitSparseExceptionSelectData` + `selectCosted`
+ `_cost_le`/`_exact` + builder profile; (d) Tier 7 BP specialization to recover the
capstone; (e) the new `ofRelativeSplitSelectData` source + family lift + `RankSelectSpec`
select leg. Then generic `o(n)` exact select is closed.

## 2026-06-24 (AUDIT) — `main` @ `59768bd` "Establish rank-select spoke boundary"

Adversarial audit of `main` (tip `59768bd`, on top of `1a19617` "Add public Jacobson
Clark rank-select family"). Machine-checked: full `lake build` green; full
`scripts/axiom_check.lean` = 477 headliners, **zero** `sorryAx`/`ofReduceBool`/errors;
`rank_select_axiom_check.lean` clean; gate hygiene + native_decide scans clean.

**VERDICT: GENUINE — and it CLOSES the o(n) select wall this audit log flagged open
twice** (`3b06ee4`, and the `9ade3de` reduction note above). The select half went from
"abstract family shape, no concrete inhabitant, easy routes *proven* vacuous/linear"
to a real concrete inhabitant. Headline:
`RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile`
(trust base `{propext, Classical.choice, Quot.sound}`).

What it delivers: for **every** `bits : List Bool` and **both** target bits, a
bitvector directory storing the `n` input bits + `o(n)` auxiliary bits, answering
`access`/`rank`/`select` exactly (`= bits[i]?` / `Succinct.rankPrefix` /
`Succinct.select`) in a uniform constant modeled query cost.

**Adversarial checks that PASSED:**
1. **Non-oracular.** `SparseExceptionSelectData.selectCosted` (GenericSelectBuilder
   5228) is a real charged Clark/Munro dispatch: `superTable.readCosted` → (marked:
   `longFlagRankData.rankCosted` + `relativeOffsetReadCosted longSuperRelativeTable`)
   else (`localTable.readCosted` → `sparseDirectory.readCosted` or
   `denseTwoWordSelectCosted bitWords`). No `Costed.pure (Succinct.select …)` anywhere;
   the only `Costed.pure none` are correct out-of-range / missing-entry cases.
2. **Inhabited (total builder).** `sparseExceptionSelectData bits target` (5656)
   constructs the structure for all bits from concrete components
   (`super/localEntries`, `super/local/longSuperRelative/sparseException` tables,
   `bitWords := BoundedPayloadWordStore.ofChunks bits`), discharging
   `payload_length_le_overhead` + 5 exactness fields. `selectCosted_exact` (5371) is a
   genuine per-branch proof tying each decode branch to `Succinct.select` via
   `Costed.erase_bind`/`readCosted_erase`.
3. **Genuine o(n) (not vacuous, not Θ(n)).** `canonicalSparseExceptionSelectOverhead`
   = sum of `logLogCubedSampledDirectoryOverhead` + `longSuperRelativeTableOverhead` +
   `canonicalSparseExceptionDirectoryOverhead`, all strictly sublinear; `_littleO`
   proven against the real predicate `LittleOLinear f := ∀ scale>0, ∃ T, ∀ n≥T,
   scale*f n ≤ n` (textbook o(n) — `n` and `n/2` both FAIL it).
4. **No double-count.** Select aux payload excludes `bitWords`; the `n` bits are
   counted once by `RankSelectSpec` (`payload := bits ++ auxPayload`) and reused for
   access, rank base, and dense select decode.
5. **Gate STRENGTHENED, not weakened** (the audit's usual suspicion): `59768bd` added
   `RMQHub`/`RMQRankSelect` build steps, extended hygiene/native_decide scans to the
   new roots, and added the rank/select axiom check with `sorryAx`/`ofReduceBool`
   detection. Capstone untouched and still trust-clean.

**Honest caveats (stated, not deceptions):**
- The abstract `BitVectorRankSelectFamily.n_plus_o_constant_query_profile` is **vacuous
  in isolation** — a zero-overhead `Costed.pure (Succinct.select …)` oracle satisfies it
  (`LittleOLinear 0` holds). `RANK_SELECT_FRONTIER.md` says so verbatim ("not an
  existence theorem by itself"), and the public headline points to the *concrete*
  inhabited theorem. Honestly handled.
- "Constant query cost" is **modeled** (charged word-RAM / indexed-access ticks;
  in-word rank/select charged O(1) per the standard transdichotomous assumption), not
  unconditional wall-clock. Docs say "modeled."
- `jacobsonClarkRankSelectPaddedAuxPayload` pads with `false` up to the clean overhead
  expression: conservative (inflates the count) and **inert** (queries read the real
  sources, not the padding); real payload ≤ overhead proven separately. Sound.

**Process / cleanup findings (non-correctness):**
- Untracked, **non-gitignored** `.tmp_rank_select_materials/{02,03}-…/lec0{2,3}-*.pdf`
  (course lecture PDFs) sit in the `main` worktree — accidental-commit / repo-bloat
  risk. Gitignore (`.tmp_*` / `*.pdf`) or remove.
- The `claude/clark-two-level-select-source` branch (this session's parallel port of the
  same entry/table + sparse-exception layer) is now **largely redundant** — `main`'s
  6065-line `GenericSelectBuilder.lean` independently built the same structure and went
  further (full structure + query + builder + family). Recommend: **abandon it.**
  Confirmed not even the flag-rank factoring is unique — `main` already has the same
  factored `flagRankData (flagBits)` generic family (GenericSelectBuilder 1089/1103).
  Nothing on the clark branch is salvageable over `main`.

## 2026-06-24 (AUDIT — ELEGANCE/TASTE, not correctness) — `main` @ `59768bd`

Question this round: not "is it correct" (it is — see above) but "would a respectable
Lean-formalization leader (Mathlib/CSLib caliber) have written it this way?" Verdict:
**No. The math is a real result; the code is research scaffolding that was never cleaned
up.** It would not pass Mathlib/CSLib review. The algorithm works but the code is a mess
— over-built and carrying dead history — exactly the "works but messy" framing.

Concrete evidence (all on `main`):
- **Abstraction accretion: ~50 `*Select*` structures** (`rg "^structure .*Select"` = 50).
  Many are superseded/parallel dead-ends never pruned: `SparseDenseFalseSelectLocatorEntry`
  (+Table) vs the live `…DenseLocalEntry` (+Table); 6–8 overlapping "payload-live stored
  word select data" variants (`PayloadLiveStoredWordSelectData`, `StoredWordSelectData`,
  `PayloadBackedStoredWordSelectData`, `Sampled…`, `ExactSampled…`, `TwoLevel…` ×3);
  3 `*CloseData` variants (`RelativeSplitRectangular…`, `RelativeSplitSparseException…`,
  `RectangularCharged…`) — scope doc Tier 8 already admits the Rectangular ones are
  superseded/linear. A CSLib-caliber version has ONE select-source interface + ONE
  concrete builder.
- **Monolithic files**: SuccinctCloseProposal 26k, SuccinctSelectProposal 20k,
  GenericSelectBuilder 6k lines. Mathlib/CSLib soft-cap ~1500 and split by concept.
- **Dead-history naming**: 149 `FalseSelect` identifiers inside the *generic*
  (target-parametric) builder — the names lie (`relativeSplitFalseSelectEntryIsMarked`
  ×30, `SparseDenseFalseSelectDenseLocalEntry` ×13). 6-noun pileups up to 58 chars
  (`sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget`). Leftover from the
  BP-`false` origin; never renamed when generalized.
- **Amateur proof idiom**, ~15–37×/file: `by_cases h : b = true` then re-derive the
  negation via `cases h : b · rfl · contradiction` (e.g. GenericSelectBuilder
  377–380, 467–470, 937–940, 1844, 2062, 2121, …). `Bool.not_eq_true` appears nowhere.
  Fix is a zero-library restructure: `cases hb : b` at the split. This is the literal
  `if (x == true)` equivalent.
- **No-op abstraction**: `SparseExceptionSelectData.queryOccurrence _data idx := idx`
  (5219) — identity wrapper threaded through the query.
- **Boilerplate**: 92 `_profile` theorems that just bundle fields into a conjunction.
- **Reinvented basics scattered**: `nat_div_sub_div_le_sub`, `one_lt_two_pow_of_pos`,
  `machineWordBits_le_self_of_pos`, `lt_two_pow_machineWordBits_of_lt` buried at
  SuccinctSelectProposal 8152–8190 (a *select* file); `nat_succ_le_two_pow` in
  SuccinctSpace. Consequence of the Mathlib-free constraint, done without a clean
  `Prelude`/`NatExtra` home or Mathlib naming.
- **Design**: false/true select built as two fully independent directories ⇒ overhead is
  `… + canonicalSparseExceptionSelectOverhead n + canonicalSparseExceptionSelectOverhead n`
  (2× constant) with duplicated `cases target` branches (5899–5942); padded aux payload
  (`jacobsonClarkRankSelectPaddedAuxPayload`) materializes inert `false` bits just to make
  the headline overhead a clean closed form.

Genuinely good (fair credit): correct + trust-clean + genuinely o(n); lemmas decomposed
into small named pieces (good granularity in the small); some names follow Mathlib's
`conclusion_of_hypothesis` convention; `Costed` charged-cost discipline is principled.

Estimate: a CSLib-caliber rewrite is ~1/3 the size. Prioritized cleanup (high ROI / low
risk first): (1) prune the ~50 → ~5 structures (delete/Archive unused); (2) global rename
(drop `False`/`built`, shorten pileups, namespace); (3) split mega-files; (4) script the
Bool-dance → `cases hb : b`; (5) centralize reinvented basics + decide the Mathlib/CSLib
dependency question (ties to the deferred CSLib coordination); (6) drop/auto-derive
`_profile` boilerplate, inline identity wrappers. None of this touches correctness or the
trust base.

## 2026-06-24 (AUDIT) — `main` @ `03f920e` "Demote relative split capstone from headline check"

Four commits since `59768bd`, all acting on the cleanup roadmap: `e371473` (roadmap doc),
`dd4702b` (generic-select BP close-access bridge, +138 SuccinctFinal), `52bdf4c` (route
capstone through generic select, +163 SuccinctFinal), `03f920e` (swap headline check). This
is **Roadmap §1 / scope-doc Tier 7** — unifying the duplicated sparse-exception select —
being executed. A "demote from headline check" commit is exactly where hiding a regression
would happen, so it got the scrutiny.

**VERDICT: GENUINE and honestly executed. No regression hidden.** Machine-checked: full
`lake build` green; `headline_axiom_check.lean` clean; full `axiom_check.lean` zero
`sorryAx`/`ofReduceBool`.

What `03f920e` actually did: swapped the *headline* set from 4 `builtRelativeSplitSparseException*`
theorems to 2 `builtGenericSparseException*` ones, and repointed the public-headline docs.
Checks that it's legitimate curation, not concealment:
- **New headline = old headline in strength.** `builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`
  (SuccinctFinal 2426) is statement-identical to the demoted
  `builtRelativeSplitSparseException…` one (2263): same `LittleOLinear` o(n) overhead, same
  doubled-Catalan + log slack lower bounds, same `payload = 2*n + overhead`, the **same**
  O(1) query-cost constant (`concreteBPNativeSuccinctRMQQueryCost sparseDenseFalseSelectQueryCost`),
  same exact `= some (scanWindow …)`. Only the overhead-function name differs
  (`relativeSplit…` → `generic…`), both proven `LittleOLinear`. So `2n+o(n)`/O(1)/exact/
  two-sided is fully preserved, now routed through the generic select over `shape.bpCode`.
- **Demoted ≠ deleted ≠ regressed.** The old relative-split total theorem and family profile
  are still present (SuccinctFinal 2263) and still in the **full** `axiom_check.lean`
  (lines 468/…), both resolving to `{propext, Classical.choice, Quot.sound}`. They were
  removed only from the curated *headline* set, not from verification.
- **No coverage loss.** The kept generic total theorem transitively depends on the generic
  `…total_two_n_plus_o_constant_query_profile` (proof line 2467), so `#print axioms` on it
  still certifies the whole 2n+o(n)/O(1)/exact chain trust-clean.
- New `builtGenericSparseExceptionSelectBPCloseAccessFamily_profile` + the total theorem
  both trust-clean.

**Honest caveats / not-yet-done (stated in their own docs):**
- **Duplication not yet pruned — tree temporarily LARGER.** This routed the capstone onto
  the generic select but *kept* the old BP `RelativeSplitSparseExceptionFalseSelectCloseData`
  machinery ("remains checked compatibility … until archive/prune cleanup"). So +301 lines
  now, with two parallel select paths; the elegance win (deleting the superseded BP select)
  is the *pending* next step. Staging it this way (prove new path, then delete old) is sound;
  the win is real only once the prune lands. If it stalls here, the net effect is more code.
- `genericSparseExceptionBPCloseAccessOverhead` may be a looser o(n) constant than the
  BP-specialized one — still genuine o(n) (LittleOLinear proven), so `2n+o(n)` holds; not a
  regression, just possibly a bigger lower-order term.
- `.tmp_rank_select_materials/` (lecture PDFs, untracked, non-gitignored) **still** sits in
  the `main` worktree — prior cleanup note not yet acted on.

Net: the highest-value roadmap item was executed correctly and honestly. Next concrete move
is the prune (delete the now-superseded BP select machinery + the dead islands from the
elegance audit), which is what actually shrinks the tree.

## 2026-06-25 (AUDIT) — `main` @ `88fd2e2` (archive + alias batch)

Three commits since `03f920e`: `ae0a45b` (archive superseded select axiom checks),
`30c4be6` (archive select compatibility aliases), `88fd2e2` (public headline theorem
aliases). Machine-checked: full `lake build` green; headline / archive / full axiom checks
all zero `sorryAx`/`ofReduceBool`.

**INTEGRITY VERDICT: GENUINE, nothing hidden.**
- **Aliases are honest `abbrev`s and provably can't weaken.** `RMQ/Headlines.lean` gives
  README-facing names (`succinctRMQTwoNPlusOConstantQuery`, `rankSelectNPlusOConstantQuery`,
  `exactRMQLowerBoundDoubledCatalanSlack`) as `abbrev`s of the exact audited theorems. An
  `abbrev` infers its type from the target, so the short name carries the *identical*
  statement. `#print axioms` on all three resolves to `{propext, Classical.choice,
  Quot.sound}` — i.e. they carry the genuine heavy axiom profile, not a stub's "no axioms."
- **Archive is still gated, not a dodge.** `ae0a45b` moved 60 superseded headliners out of
  `axiom_check.lean` into `scripts/archive_axiom_check.lean` AND added that file to
  `gate.ps1` with the same `sorryAx`/`ofReduceBool` failure check. All 60 still verified
  trust-clean. `RMQ/Archive/SelectCompatibility.lean` (`abbrev` anchors to the superseded
  BP relative-split / locator theorems) is imported by `RMQ.lean`, so still compiled.

**ELEGANCE VERDICT: net neutral-to-negative — this is curation, NOT the prune.**
- **Zero source pruning.** These commits touched no `RMQ/Core/*.lean`. File sizes are
  unchanged (`SuccinctSelectProposal` 19837, `GenericSelectBuilder` 6065,
  `SuccinctCloseProposal` 26285); the 3 superseded structures (Locator + both Rectangular
  CloseData) are 100% still present. The code-mass problem from the elegance audit is
  untouched; the tree grew ~360 lines (new archive/alias/script files).
- **The aliases + archive gating now ENTRENCH the dead code.** By aliasing 18 superseded
  theorems as "compatibility anchors" and adding 60 of them to a gated check, the batch
  *increases* coupling to the superseded machinery — the old theorems can no longer be
  deleted without also tearing out the aliases and archive check. If the intent was the
  Roadmap §1 final step (delete the superseded BP select), this moved *away* from it,
  converting "delete-me dead code" into "maintain-forever compatibility surface."
- **Unflagged strategic fork.** Some archived items are defensible keep-forever anchors
  (the BP-specialized capstone as a *dual* proof alongside the generic one; the
  `_not_littleO` obstruction witnesses). But dignifying truly-abandoned scaffolding — e.g.
  `sparseDense_locatorTable_ofEntries_profile`, an unused codec nothing builds on — as a
  citeable "compatibility anchor" is dubious. Decide per-item: genuine dual-proof/witness
  (keep) vs. dead exploration (delete, don't alias).

**Good:** the `Headlines` short names are a real readability/citation win for README/demo.
**Carried-over, still not done:** `.tmp_rank_select_materials/` lecture PDFs still untracked
and non-gitignored in the worktree; the 2× false/true select overhead; the file splits.

Bottom line: trustworthy and well-formed, but the last three commits are bookkeeping that
made the public surface nicer while leaving (and slightly entrenching) the bloat the
elegance audit called out. The decision to make is explicit: **archive-as-keep vs.
archive-as-stage-then-delete.** If the goal is a CSLib-caliber tree, the next commit must
actually *delete* the dead islands (Locator codec first — it has no dual-proof value),
which now also means removing their fresh compatibility aliases.

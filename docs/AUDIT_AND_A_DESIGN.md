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

**Demo framing:** honest claim is "verified word-RAM rank *and* select with
derived O(1) query"; do **not** claim "succinct 2n+o(n) RMQ" (space decoupled).
Lead with the airtight results (RAM.Exec sparse table, FH fresh build/query,
dense LCA, lower bound).

---

*Process: from 2026-06-19 onward, each audit is written up here as a dated
round-log entry by default (no need to ask).*

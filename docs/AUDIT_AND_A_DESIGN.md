# RMQ POC — Audit Snapshot + Cost-Model (Target A) Design

Staging note: this doc was imported from the audit branch as a historical audit
record. The working-tree `docs/ROADMAP.md` and `docs/CODEX_AUTONOMY.md` are the
**canonical** steering docs. In particular, the current roadmap keeps
Mathlib-free Lean/Std as the default and refines D-LCA toward a dense
direct-address node-ID theorem while preserving arbitrary-label correctness.
Use this document for audit rationale and failure-mode reminders, not as an
override of the live roadmap. This record also predates the final BP-native
succinct RMQ capstone; any line below that calls D-Space optional or future is
historical rather than current.

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

Current override: the historical scorecard below predates the latest loop.
The live roadmap now treats the POC finish line as landed with A/B/C plus
D-LCA under the hardened-shallow RAM/component-budget model. The public-facing
D-LCA theorem is
`LCAFischerHeun.denseLCA_linearBuild_constantQuery_profile`; the remaining
work is post-POC fidelity hardening, especially a first-order RAM interpreter
and one monolithic executable dense-LCA preprocessing trace.

| Target | Status | Detail |
|---|---|---|
| **A** machine-step cost model | POC complete, interpreter future | `Core.RAM` is a hardened shallow trace substrate: raw primitives are sealed, sparse build/query use derived traces, FH stored summary/local reads are charged through counted adapters, and the `xs.toList.length` guard leak was fixed to `Array.size`. It is still a probe/indexed-access trace model, not a first-order machine interpreter. |
| **B** refinement framework + 2 instances | POC complete | `Core.Refine.StoredMatrix`/`StoredSeq` now support sparse-table queries, FH summary tables, and dense LCA first-occurrence/node/depth stores. FH boundary microtable reads are no longer the old asserted `materializedMicrotableLookupCost := 1` path; the public large-regime supplied-query bound is `<= 13`. |
| **C** lower-bound framework + RMQ instance | 🟢 done | `Core.LowerBound` is generic (docstring: "does not mention RMQ, Cartesian trees, or shapes"): finite bitstring universe, finite-domain `LosslessEncoding`, injection/capacity counting, log-slack arithmetic. `EncodingLowerBound` re-derives the no-premise `2n − (2log₂(2n+1)+2)` bound *through* it. Reusable, non-vacuous (decoder answers from bits alone). |
| **D** research headlines | D-LCA and D-Space landed | `denseLCA_linearBuild_constantQuery_profile` is the dense/preindexed LCA cost headline. The later BP-native succinct RMQ capstone is recorded in the live roadmap and README; older D-Space notes in this historical audit are superseded. |

**Finish line:** A + B + C + one of D. The POC finish line is now landed under
the documented hardened-shallow RAM/component-budget model.

**The persistent post-POC gap:** this is not yet a full first-order RAM
interpreter or one monolithic RAM execution for dense LCA preprocessing. Those
are the next fidelity upgrades, not blockers for the scoped RMQ POC.

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

## 2026-06-18 (final pass) - assoc path retired; dense D-LCA remains the headline

The assoc-list first-occurrence path described above has now been retired from
the compiled implementation and theorem inventory. The live LCA cost story is
the dense/preindexed node-ID path:

- `LCACost.firstOccurrenceDirectRows` / `firstOccurrenceDirectStored` provide
  the direct-address first-occurrence table.
- `LCAFischerHeun.buildDenseConcreteQueryState` builds the concrete query state
  from the canonical Fischer-Heun RMQ state, dense first-occurrence store, and
  node store.
- `queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels`
  is the current built-state query capstone with the large-regime `<= 16`
  query bound.

The remaining D-LCA caveat is therefore no longer hidden linear lookup in an
assoc list. It is the normalization of the assembled component budget into the
final public-facing theorem: choose the tree-size measure, state the dense-label
preprocessing-plus-query profile against it, and keep arbitrary-label LCA
correctness as the separate semantic layer.

## 2026-06-20 (succinct capstone) - blockers pinned; next round must be positive

The succinct BP-native RMQ path is now better constrained, but still not closed.
The latest merged work added design-constraining negative theorems:

- `SuccinctClose.blockPairMacroDirectory_not_sufficient`: endpoint
  close-block pairs are not enough information for an exact BP close/LCA macro.
- `SuccinctClose.denseAllCloseBPCloseLCAOverhead_not_littleO`: the
  direct all-close endpoint fallback is exact and charged, but not an `o(n)`
  auxiliary payload.
- `SuccinctSelect.SelectSampleWordExact.shared_aligned_read_word_forces_same_wordIndex`
  and the two-level `shared_local_locator...` lemmas: one shared aligned
  payload word cannot serve successful selects whose answers lie in different
  chunks.

These results are useful anti-vacuity guards: they prevent a fake capstone over
an under-keyed macro, a dense non-succinct table, or a shared select locator
that silently reads the wrong payload word. They are not themselves the
succinct-RMQ capstone.

The companion note `docs/SUCCINCT_RESEARCH_AND_PLAN.md` records the current
positive plan: C1 descriptor select based on two-level select sampling; C2 a
Navarro-Sadakane-style BP range-min-max macro with charged endpoint-fringe
repair and a Four-Russians local micro table; C3 the concrete final join with
the existing `logSlackLower` lower-bound tie.

Stop assessment: the negative-theorem round was legitimate once because it
pruned tempting but false closes. The next round should not stop on another
blocker unless a concrete C1/C2 construction attempt makes the target
ill-specified and produces a minimal impossibility theorem. The expected
deliverable is a positive component profile or a concrete construction consumed
by such a profile.

## 2026-06-21 - Relative summary wall broken; option-1 interior target pinned

The audit branch's latest note was written before the coordinator pinned option
1, but its central finding survives reconciliation: the relative summary
component is now real, unconditional progress rather than another abstract
budget envelope.

`SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical` and
`SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile`
give the project a concrete BP relative min/max/arg summary table with fixed
canonical parameters, no budget/satisfiability premise, `LittleOLinear`
compact-overhead accounting, bounded four-word reads, and machine-word
side conditions. This is the first close-side summary component that is both
payload-live and instantiable at the intended succinct scale.

The audit's "retire the mirage" warning is also directionally right:
`interiorBlockPairRanges` and the sampled guarded endpoint-fringe theorem remain
useful as scaffolding and negative evidence, but they must not be treated as a
headline close-directory witness because the sampled theorem still depends on a
dense all-pairs interior payload budget. Once the compact replacement lands,
the dense sampled profile should be removed from the curated headline inventory
or deleted outright.

The option-1 decision sharpens the remaining C2 target. We are not pursuing a
direct scan over the relative summaries, a sparse-table-sized payload, or a
recursive final-RMQ oracle. The next positive checkpoint is:

```lean
concreteBPRelativeRmmInteriorDirectory_profile
```

That theorem should build a compact rmM/min-max-tree-style interior navigator
over complete-block minimum candidates. It may consume the relative summary
table as leaves, but it must answer the middle full-block interval by a constant
number of charged payload reads plus bounded arithmetic, prove exact leftmost
range-minimum witnesses, prove `LittleOLinear` auxiliary payload, and expose
machine-word bounds for every read.

After that, the close chain is mechanical in shape but still substantial:
consume the interior navigator in
`concretePayloadLiveRelativeRmmBPCloseMacro_profile`, then in
`concreteCompactBPCloseLCADirectory_profile`, and finally in the BP-native
succinct RMQ join.

## 2026-06-21 - Interior navigator built and merged

The compact relative-rmM interior navigator is now in the coordinator branch.
`SuccinctClose.concreteBPRelativeRmmInteriorDirectory_profile` is the
positive C2 interior checkpoint the audit had been demanding: under the
large-regime threshold `2^128 <= shape.size`, it packages a concrete two-level
directory with `LittleOLinear` payload overhead, payload bounded by the concrete
overhead term, bounded query cost, exact leftmost range-minimum witness erasure,
and machine-word bounds for the charged local/global/summary reads.

This result is materially different from the older dense
`interiorBlockPairRanges` path. The new profile derives the local offset-table
and global macroblock-table budgets instead of assuming a dense all-pairs
interior budget, and it routes the answer through payload-backed reads rather
than an answer-as-premise selector cell.

The dense sampled guarded endpoint-fringe theorem is no longer in the curated
`scripts/axiom_check.lean` headline inventory. It remains in source as legacy
scaffolding and contrast material until the close-directory composition fully
consumes the compact interior navigator; it should not be cited as a concrete
`2*n + o(n)` close-directory witness.

Remaining C2/C3 work is now composition rather than discovery: consume
`concreteBPRelativeRmmInteriorDirectory_profile` in the relative-rmM close macro,
then the compact BP close/LCA directory, then the final BP-native succinct RMQ
join with the lower-bound slack theorem.

## 2026-06-21 - Capstone audit reconciled: final join is conditional

The audit branch's adversarial capstone note is correct on the binding
constraint. Worker B's `RMQ/Core/SuccinctFinal.lean` join is real and has now
been merged: it composes BP select, concrete compact BP close/LCA navigation,
and BP rank back to representative-array RMQ, with payload length
`2*n + overhead`, `LittleOLinear` overhead, bounded query cost, and exact
valid-window erasure.

But the theorem is still conditional on an abstract
`SuccinctSelect.TwoLevelPayloadLiveStoredWordRankSelectFamily`. A repo
search confirms that structure has profile theorems and canonical builder
pieces, but no concrete family witness yet. The headline is therefore not closed
until such a witness is built and the merged
`SuccinctFinal.concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
is instantiated at it.

Worker A's close-navigation adapter remains parked. It builds a clean
close-side socket/family layer, but the close side is already concrete and the
merged final join consumes `concreteCompactBPCloseLCADirectory` directly. It is
not the missing capstone ingredient.

The next proof target is intentionally theorem-shaped rather than exploratory:
construct a concrete two-level payload-live stored-word rank/select family over
all bitvectors from the canonical two-level rank/select builders, discharge the
word-size, sample-width, positivity, and little-o side conditions, then apply
the final BP-native join theorem with no abstract family parameter remaining.

## 2026-06-21 - Rectangular built close-access audit: exact and constant, but linear

The latest `codex/c1-rectangular-built-close-access` worker branch made real
construction progress but did not close C1. It landed the span-packing theorem
`SuccinctSelect.builtRelativeSplitFalseSelectShortSuperLocalSpanSum_le_bpCode_length`
and the unconditional repaired sparse-exception relative-table budget
`SuccinctSelect.builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead`.
Those are load-bearing: the narrow sparse-exception payload no longer depends
on an unproved semantic span hypothesis.

The branch also built an exact, constant-query false-close/select route through
`SuccinctSelect.builtTwoLevelFalseSelectCloseData_profile` and consumed
it in `SuccinctFinal.builtTwoLevelFalseSelectBPCloseAccessDirectory_profile`.
This is a useful compatibility witness, but it is not a succinct witness. The
same branch proves
`SuccinctSelect.builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ`,
so the block select payload is at least `shape.bpCode.length + 1`, hence
linear in the BP payload length. Any final path that rests on
`builtTwoLevelFalseSelectCloseData` or the full-width
`TwoLevelPayloadLiveStoredWordSelectData` block table is therefore a known
linear baseline, not the `o(n)` C1 component.

The rectangular routing idea itself is still sound. The failure is assembly:
the exact witness keeps falling back to the full-width two-level select table
instead of assembling the already-budgeted narrow relative-split components.
The next theorem-shaped target is therefore not another linear exact baseline
and not another padding obstruction. It is a concrete
`RelativeSplitSparseExceptionFalseSelectCloseData` builder from `shape.bpCode`,
using the narrow relative-table payload, sparse flag/rank side structure,
relative long/sparse exception offsets, and dense two-word fallback, followed
by consumption in the close-access/final RMQ path. The branch should prove the
payload bound against a genuine `LittleOLinear` overhead function and should
not leave branch exactness as free structure fields.

## 2026-06-22 - Compact false-close witness merged

The repaired relative-split C1 target is now implemented in the worker branch
and reconciled into the coordinator branch. The concrete theorem
`SuccinctSelect.builtRelativeSplitSparseExceptionFalseSelectCloseData_profile`
builds the false-close/select data from `shape.bpCode`, including the compact
long-super side table indexed by charged long-flag rank plus local occurrence.
The final theorem
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
then consumes that concrete close-access witness in the BP-native RMQ join.

The previous cost-fidelity caveat is also fixed on the concrete C1 query path:
`RelativeSplitSparseExceptionFalseSelectCloseData.selectCloseCosted` uses the
cheap executable guard `idx < shape.size`; the full false-count identity
`rankPrefix false shape.bpCode shape.bpCode.length = shape.size` appears only
in proof-only exactness reasoning. The remaining caveat is the already
documented C2 model boundary: the compact close/LCA side uses a charged
bounded-local-BP primitive whose bit-level local decoder can be hardened later.

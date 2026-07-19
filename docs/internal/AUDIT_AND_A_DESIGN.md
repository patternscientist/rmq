# RMQ POC — Audit Snapshot + Cost-Model (Target A) Design

Staging note: this doc was imported from the audit branch as a historical audit
record. The working-tree `docs/ROADMAP.md` and `docs/internal/CODEX_AUTONOMY.md` are the
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

The companion note `docs/internal/SUCCINCT_RESEARCH_AND_PLAN.md` records the current
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
2026-07-04 note: this paragraph records the original large-regime checkpoint.
The current all-size public route no longer uses the legacy interior witness
fallback: Ready shapes use the two-level directory, active non-Ready shapes use
a bounded summary scan, and inactive shapes have a pure-none interior replay.
`SuccinctClose.concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`
is retained as a sufficient Ready theorem, with the old `2^128` theorem kept
only as a compatibility corollary.

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

## 2026-06-25 (AUDIT) — `main` @ `0bd7006` (A1 executed: namespace alignment)

Three commits since `f7a774e`: `e7715b0`/`38b7d07`/`0bd7006` introduce/align the
`SuccinctRank` / `SuccinctSelect` / `SuccinctClose` namespaces — the prior audit's top
item (A1). Integrity perfect: build green; all four axiom checks resolve, zero
`sorryAx`/`ofReduceBool`/errors — headline 15, archive 4, rank-select 5, full 421;
headline capstone still `{propext, Classical.choice, Quot.sound}`.

**VERDICT: A1 done, and done the right way.**
- **"Proposal" dropped from live namespaces.** Files under `SuccinctSelect/`,
  `SuccinctClose/` declare `namespace SuccinctSelect` / `SuccinctClose` (top-level
  path-aligned); only 1 file each still declares the old `*Proposal` namespace.
- **Clean compat-shim layer (as recommended).** The 3 `*Proposal.lean` roots are now thin
  `export`-based compatibility shims (e.g. `SuccinctSelectProposal.lean` 576 lines, mostly
  re-exports) with a docstring steering new code to `RMQ.Core.SuccinctSelect` /
  `RMQ.SuccinctSelect`. ~25 `Proposal` refs remain, all in that transitional layer.
- **`axiom_check` updated to the new names** (`RMQ.SuccinctSelect.*`), counts unchanged —
  no theorem lost, no check masked.

**Minor / standing:**
- Namespace alignment is at the *directory* level (all `SuccinctSelect/**` files share one
  `SuccinctSelect` namespace, sub-namespaced by structure e.g. `SparseExceptionSelectData`),
  not per-subdirectory. That's idiomatic Lean (namespace-by-type, not by file path), so it's
  fine — not a gap.
- **B-tier idiom polish still pending** (unchanged): 33 Bool case-extraction dances, 229
  mega-simps (≥5 lemmas), no global prelude.
- 3 compat shims to retire once downstream migrates; `SuccinctSpace.lean` has
  since been split into role modules under `RMQ/Core/SuccinctSpace/` with the
  old file kept as a thin barrel; Mathlib/CSLib dependency call still open.

Bottom line: the structural + naming cleanup is now essentially complete — navigable file
sizes, dead-ends pruned, and idiomatic path-aligned namespaces with "Proposal" gone from the
live API, all with a flawless integrity record. What's left (B-tier proof idioms, shim
retirement, the dependency decision) is the narrow "navigable → maximally idiomatic" gap,
none of it debt. The project now reads like a real Lean CS-library component.

## 2026-07-17 (C05 coordinator round) — E1 obstruction validated; M1 R4 completed by coordinator ✅/⚠️

**Scope:** worker-output audits of E1-01R3 (`codex/e1-fully-charged-small-step-machine-r3`,
candidate `7fe5b8b`) and M1-01R4 (`codex/m1-reviewer-native-machine-adequacy-r4`), plus
roadmap-vs-goal reconciliation. Coordinator ran as user-authorized disclosed fallback
(Claude runtime; `rmq-*` skills not in runtime catalog; governance `5f59455` not in
checkout ancestry — read directly from tracked SKILL.md files instead).

**E1-01R3 — obstruction VALID, kernel-verified.**
`e1R3FamiliarMachineTarget_obstruction : ¬ E1R3FamiliarMachineTarget` and its unbounded
same-block family independently reconstructed from source; quantifiers match the frozen
contract; the frozen R3 wording matches the issued prompt verbatim; axioms
`[propext, Classical.choice, Quot.sound]` independently re-checked at the exact clean
candidate (129.6s, exit 0). Math: canonical block width is `2*(log2 n + 1)` = Θ(log n);
the accepted 76-event route fetches the window in 4 unit-charged word reads and extracts
min-excess event-silently; per-position charging + positional trace equality + one literal
all-size total are jointly unsatisfiable. Verdict: the frozen E1 contract is
mis-specified, not the machine unreachable. Coordinator fork (user decision pending):
Option A — charge word-level primitives and state the transdichotomous word-RAM model
publicly (recommended); Option B — four-Russians table route (larger refactor, optional
hardening). Do not merge `7fe5b8b`; preserve as obstruction evidence for the amended
E1 contract. **Process finding:** the R3 "frozen" matrix rows were committed atomically
with the obstruction proof — pre-register frozen rows in the repair-base commit in future.

**M1-01R4 — candidate completed at `947bde5` (coordinator tail).**
Worker's uncommitted 5-file repair audited clean against all frozen R4 rows (exact
registry, nonvacuous selectors, whole-block A01/A02 fidelity, bounded subprocesses,
honest matrix with no phantom-gate claims). Worker was credit-blocked before the final
gate; coordinator ran it: first aggregate failed solely on Q05 timing out at the 300s
ceiling while focused Q05 rejects in 7.875s — recalibrated `StageDeadlineSeconds`
default to 900s (hang bound, not performance assertion; WDD-20260717-007 and matrix row
amended with C05 attribution), then the single permitted retry passed (exit 0, 3183.6s;
41/40/1 semantics; 16/14/2 topology; claim drift 0 strict failures). Committed on the
worker branch with both range checks and strict design check green. Coordinator
acceptance + fresh-blind audit remain open. Note: production topology lint's runner pin
changed boundary-ID tokens → three `REPLAY-*` anchors (strictly stronger; deliberate).

**Roadmap reconciliation:** U3 is integrated into main but never formally accepted —
A05 (twice) and A06 findings all resolved, but no fresh blind audit of the resolved
state and the U3 matrix still says CANDIDATE_COMPLETE; recommendation: spend A07 at the
commit where the cost-model amendment lands. The cost-model fork must be decided before
E1-R4 or M1 headline phrasing freezes. Governance branch (12 commits,
`4a60853..5f59455`) is content-safe but unmerged; `2c30a3a` (gate.ps1) and
WDD-003/006 authority grants need an explicit user nod.

## 2026-07-17 (C05 round 2) — B2 charged-fringe candidate reconstructed clean ✅

**Scope:** coordinator reconstruction audit of `d1d645e` on
`claude/b1-b2-charged-fringe-tables` (B2-01 checkpoint `fff3f2f` + B2-02
wiring), against the frozen `B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` and
`OPTION_B_CHARGED_FRINGE_DESIGN.md`.

**Verdict: all ten adversarial checks CONFIRMED; build B3 on `d1d645e`.**
Highlights: matrix freezes provably precede implementation (0-byte requirement
diffs across the ladder); dispatcher name/namespace/statement identity
preserved with the same-block arm untouched; substitution proven through the
chunk-fold bridge, not definitional; 142 is a sum of individually proven
component bounds (2*13 + (2*4 + 2*37 + 30) + 4) with 76 frozen per the 328
pattern; ReviewerSource append-only (21 constructors, segment 21 live via an
actual read, fresh-unused anti-vacuity witness moved to segment 22 at
identical strength); charged reads are store-produced with a checked
corruption witness at the exact read slot; transitional-cap consumers lost no
coverage; hygiene clean.

**Coordinator ratifications:** (1) dispatcher relocation to
`ChargedFringeWiring.lean` — ratified (names preserved, import-direction
forced); (2) transitional-cap close-bound hypotheses — ratified (derived at
every consumer); (3)+(4) dead-segment remaps — ratified (internal-only;
legacy/canonical segment-21 vocabulary divergence noted as a comment-fix);
(5) anchor-registry `SumLe76 -> SumLe142` — ratified (a CURRENT anchor
tracking the current route; the frozen legacy anchor list is untouched and
the historical 76 survives as a frozen constant).

**Queued non-blocking repairs (B3 in passing, or B5):** stale "76"
docstrings at `RMQ/Headlines/RMQ.lean:27` and
`RMQ/Core/SuccinctFinalRAM.lean:9543`; `docs/PAPER_THEOREM_MAP.md:86` and
`docs/PUBLICATION_STRATEGY.md:67` prose; a clarifying comment on the legacy
`FlatPayloadSegmentSource? 21 => .closeSummaryMinRel` label.

**Cross-branch fact:** B2's adequacy regeneration (`segment < 22`, shifted
packet text) invalidates exact operands in the M1-R4 mutation registry
(`947bde5`) and the R3-era runner wired into this branch's gate. An
M1-registry refresh rung is REQUIRED between B2 integration and M1 final
acceptance; the full aggregate gate on the B2 branch is deferred to that
refresh. B2 rung acceptance itself remains gated on the A07 fresh blind
exact-commit audit at the B-complete commit, per the campaign plan.

## 2026-07-18 (C05 round 3) — B3 candidate reconstructed clean; one doc defect ✅

**Scope:** coordinator reconstruction of `6e105a5` (B3 rung, range
`d1d645e..6e105a5`): chunked in-word rank/select swap, segment-22 select
table, derived literal 207, readWord-only vocabulary theorem.

**Verdict: all ten checks CONFIRMED; proceed to B4 on `6e105a5`.** Freeze
`a32713c` provably precedes implementation with byte-identical requirement
wording for all 29 B3 rows; dispatcher names preserved with retired bodies
under explicit `Register` names; the headline capstone diff is exactly three
`142→207` literals; substitutions prove leaf identities against the spec
(`boolRankPrefix`/`boolSelectInWord`) through packed-entry decode lemmas;
207 = rfl of the named algebra with components proven against the actual
costed functions; the vocabulary theorem's subject is the headline-consumed
whole-query object, universally quantified, with `isReadWord` structurally
excluding word primitives; store extension append-only, dead witness at 23
byte-identical modulo the constant, segment 22 live via a genuine successful
read; zero forbidden tokens; public docs keep the honest framing with no
claim inflation; no B2 closed row weakened.

**Defect (paper-facing, trivial):** `docs/PAPER_CLAIM_CORRESPONDENCE.md:7`
still lists `...NonSyntheticWeightSumLe142`, a dead identifier (renamed
`SumLe207`), lint-invisible due to its `...` prefix. Queued into B4's first
bookkeeping commit with the "23 sources → 22 sources (23 segments)" evidence
wording slip and the optional `..._cost_le_thirteen/four` legacy renames.

**Caveats recorded:** legacy navigation family drift (segment 22 repurposed,
nav rank bridge deleted; DD-20260718-002) — B4 must confirm no registered
navigation execution story changed statement or counts an unreadable region.

**A07 seed questions:** (1) two-sided chunk-width regime bounds at all n
incl. n=0,1 (8-chunk coverage vs genuinely-o(n) select-table rows); (2)
uniform application of the declared charge policy — no free spec-level
arithmetic obtains information equivalent to a charged bit-vector read;
(3) navigation legacy story consistency.

## 2026-07-18 (C05 round 4) — B4 candidate reconstructed clean; roadmap edit ratified ✅

**Scope:** coordinator reconstruction of `d90b062` (B4 provenance-hardening
rung, range `6e105a5..d90b062`).

**Verdict: all ten checks CONFIRMED; proceed to B5.** Freeze precedes
implementation with byte-identical requirement wording (22 rows); the three
new packet fields are additive, load-bearing through
`listIntSuccinctRMQPaperMainTheorem`'s first conjunct, with no field removed;
repeated-equal-read receipts carry full W19 data via checked
`ProducesEventAt` tuples (positional arithmetic, no kernel trace evaluation);
regime theorems are two-sided/all-size with kernel-safe corner pins; the
value-dependency lift is honestly scoped on every surface (full-TraceResult
inequality at whole-query level; `.value` dependency carried by the closed
component witnesses); the navigation quarantine is accurate; doc edits carry
no claim inflation; the two cost-lemma renames were verbatim-statement and
consumer-free; hygiene clean.

**Coordinator ratifications:** the out-of-scope `RMQ_FINAL_ROADMAP.md` edit
is RATIFIED — verified as a faithful two-sentence numeral sync (22 sources /
23 segments; fresh segment 23) to facts already true at base, with the
process correctly forced through a WDD entry by the strict design check.

**B5 doc queue (priority order):** (1) four public surfaces still saying
"fresh segment 21" (`README.md:94`, `docs/WHAT_IS_PROVED.md:14,95`,
`artifact/CLAIMS.md:68`, `docs/PAPER_MAIN_THEOREM.md:60`) — misdescribes the
anti-vacuity witness; (2) packet blurbs to mention the three new fields;
(3) 33-cap file attribution in `PAPER_MODEL_ADEQUACY.md`; (4) WHAT_IS_PROVED
"stronger execution surface" rewording per the quarantine; (5) unused-simp
warning cleanup at `SuccinctFinalRAM.lean:5694-5824`.

**A07 carry-forward seeds:** store-vs-littleO object identity for segments
21/22; whole-query ANSWER-level (`.value`) dependency on chunk-table contents
remains unproven (candidate E1 target); nav counted-space statement or bridge;
stale-numeral hunt after B5; deliberate packet-type growth; witness fragility
of the repeated-read fields under any future program change (re-derive, not
weaken).

## 2026-07-18 (C05 round 5) — same-block LCA branch found still event-silent ⚠️

**Finding (E1-R4i, coordinator-verified from source).** The accepted route's
same-block LCA branch was never charged. `localBPSameBlockCloseSeededCosted`
(`LocalBPDecoder.lean:1128-1143`) sets `cost := 4` while computing
`localBPSeededPrefixRangeMinExcess` and
`localBPSeededPrefixRangeArgMinPrefixPos` over
`count = rightClose - leftClose + 1` positions — unbounded in input size
(`count` reaches `blockSize = 2*(Nat.log2 size + 1)`). This is exactly the
family the refuted E1-R3 obstruction exhibited.

**Why four reconstruction audits missed it.** B2 swapped the CROSS-block arm
and deliberately left the same-block arm byte-identical; every audit checked
that as *route-identity preservation* and scored it CONFIRMED. It was — but
"unchanged" is not "safe" when the campaign's goal is to eliminate a property
that unchanged code still has. The readWord-only vocabulary theorem does not
catch it either: it constrains event TYPES, not uncharged computation.

**Collateral defect.** The B4 charge-policy section of
`docs/PAPER_MODEL_ADEQUACY.md` states that uncharged work is bounded-per-step
register computation. That is FALSE on this branch and must be repaired
together with the charging (or, if charging were declined, corrected to an
explicit unbounded-residue disclosure).

**Coordinator decision: Option (a) — charge it, as a new B-campaign rung
(B6), not inside E1.** Rationale: leaving it re-hides exactly the scan
DD-20260717-C05-001 forbids; no new mathematics is required
(`bpFringeChunkFoldCosted_global_eq_localBPSeeded`,
`ChargedFringeChunks.lean:1694`, already proves the 33-capped chunk fold
computes the same min-excess/argmin pair, side condition discharged all-size
by `four_machineWordBits_le_32_mul_bpFringeChunkBits`); and the route must be
settled before the machine simulates it, or E1's frozen rows become moving
targets. The literal moves 207 -> at most 240; re-deriving a constant while
freezing the old value is the established, twice-audited pattern (76 -> 142 ->
207). "Frozen public identity" forbids renaming or deleting `queryCost_eq`,
not re-deriving its value.

**E1 status:** BLOCKED pending B6, with no rework implied — the rank-close and
select-close canonical leg simulations are leaf legs and remain valid.
E1-R4i's canonical select form landed complete at `c0c32c4`.

**Process lesson (WDD candidate):** a campaign that eliminates a property
must audit UNCHANGED code for that property, not only the delta. Add to the
coordinator checklist: for each campaign invariant, enumerate every branch of
every dispatcher the invariant must hold on, and check the untouched arms.

## 2026-07-18 (C05 round 6) — B6 component landed; literal authorization withdrawn ✅

**B6-01 (`3068fee`) built and proved the charged same-block leg** (three new
modules, 1251 insertions, zero deletions beyond one import) but honestly did
NOT swap it into the route, reporting INCOMPLETE with a twelve-site resume
inventory. Correct call: a green component is not the target.

**Coordinator-verified correction to round 5.** I predicted the literal would
move 207 -> <=240. Wrong. `canonicalLcaCloseCostedWithRankSeed_cost_le`
(`ChargedFringeWiring.lean:101-150`) is a `by_cases` bounding EACH branch
separately by the same cap `canonicalCompactBPCloseQueryCostWithRankSeed`;
`closeLCA = 2*rankClose + 2*endpointFringe + interiorDirectory = 126` while the
charged same-block arm pays `rankCost + 37 = 48`. The cap absorbs it.
**The authorization to move the literal is WITHDRAWN as unnecessary**: no new
historical constant, no `SumLe207` anchor rename, no doc numeral migration,
no frozen-identity churn. B6-02 must derive this rather than assume it, and
report if the derivation disagrees.

**Second B6-01 finding, ratified:** the swap can preserve dispatcher identity
byte-for-byte (stronger than B2's own M9, which added a parameter), because
the same-block window is definitionally B2's fringe window
(`localBPWindowBits_eq_flatten_localBPBlockWordsRead`) and the reads reuse the
segment-21 table. Therefore NO store, payload, overhead, capacity, erasure, or
`ReviewerSource` work is required — a much smaller blast radius than B2/B3.

**Geometry caveat carried forward:** B2's "whole block lies inside the BP code"
fact is FALSE same-block (the final block may extend past
`shape.bpCode.length`); B6-01 covered each close position separately. Any
successor must not import B2's strictness argument here.

**Empirical corroboration:** the cost harness reports live
`canonicalRoute=sameBlock` executions at modeledTraceCost 52-54, confirming
the arm is reachable on the accepted route, not legacy.

**Still open until the swap lands:** the charge-policy claim at
`docs/PAPER_MODEL_ADEQUACY.md:139-153` remains false; B6-01 correctly declined
to repair prose ahead of the code.

## 2026-07-18 (C05 round 7) — B6 reconstructed clean; charge-policy alarm adjudicated ✅

**B6 reconstruction of `bacd41b` (range `c0c32c4..bacd41b`): PROCEED.** All ten
checks confirmed. Freeze byte-identical across 20 rows with the REQ-B6-05
literal prediction PRE-REGISTERED in the freeze commit and later borne out.
The silent scan is genuinely gone from every reachable path (all surviving
callers classified legacy/compat, none reachable from the whole-query object).
207 re-derives from the untouched named algebra; `queryCost_eq` transports it
and that file is not even in the delta. Vocabulary theorem necessarily
re-elaborated against the amended dispatcher. W19 witness universally
quantified with a genuine successful read. Corruption witness targets the
returned close with the slot proven in the footprint. Zero removed
declarations; zero forbidden tokens.

**Non-blocking repairs queued:** (1) INV-ALL-SIZE evidence column over-claims
"no size hypothesis" for equivalence theorems — cite
`bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq_of_query`, which
discharges the three hypotheses from purely query-side facts, and narrow the
phrasing to the cost lemmas; (2) note the `ReviewerProducerReadPath` widening
(new `lcaSameBlock` constructor, no elimination sites) under REQ-B6-04 — the
reverse-liveness statement is unchanged but marginally weaker; (3) tighten the
"no event-silent computation left" sentence; (4) **naming repair, highest
value for future auditors:** the legacy `concreteBPNativeLCACloseGlobalWord
TraceResult` and the accepted `...AllSizeStructural` differ by one suffix and
sit 60 lines apart — apply the existing `Legacy` convention.

**Charge-policy alarm ADJUDICATED — audit verdict too strong.** A parallel
audit reported the select-close guard `if idx < occurrenceCount bits target`
as an undisclosed Theta(n) event-silent computation. Coordinator-verified at
source: the bridge is ALREADY CHECKED in-tree —
`GenericSelect.falseSelectOccurrenceCount_eq` (`BPCompat.lean:21`, `rfl`) and
`falseSelectOccurrenceCount_eq_size` (`SlotBasics.lean:35-38`, via
`SuccinctSpace.bpCode_rankFalse_full`) give
`occurrenceCount shape.bpCode false = shape.size`. The guard is therefore
`idx < shape.size`, a comparison against an input parameter.

**Principle recorded (paper-facing, use it consistently):** a Lean-level list
traversal is a REPRESENTATION ARTIFACT when its value is checked-equal to an
input parameter or to a charged read (`occurrenceCount` -> `shape.size`;
`localBPWindowBits` -> the four charged word reads via
`localBPWindowBits_eq_flatten_localBPBlockWordsRead`; `queryOccurrence`,
`queryPos`, `machineWordBits`). It is ALGORITHMIC WORK requiring a charge when
it computes the ANSWER by traversing data (the B2 fringe scan, the B6
same-block scan). The doc must state this distinction and enumerate the
artifacts with their bridge lemmas rather than asserting an absolute.
Folded into E1-R4j's M7 doc work.

**Non-issue dismissed:** the `selectClose := 13` sightings are the FROZEN
historical algebras (76/142); the current algebra uses `selectClose := 35`
(`SuccinctFinalRAM.lean:8808`), consistent with 207.

**E1 cleared to proceed** on `bacd41b` under three conditions relayed to the
worker: target the post-B6 trace; name the accepted `...AllSizeStructural`
object explicitly (suffix footgun); rely on 207 unchanged.

## 2026-07-18 (C05 round 8) — A07 blind audit: REJECT, all findings accepted ⚠️

**A07 (Codex, fresh blind, cross-family) audited `4a60853..bacd41b` and returned
REJECT.** Report: `docs/internal/audit_reports/2026-07-18_A07_option_b_charged_
route_audit.md`, commit `bb76860` on `codex/a07-option-b-charged-route-audit`.
Coordinator independently verified every blocker at source. **All findings
accepted; none contested.**

What PASSED (auditor's own list, independently reconstructed): the 207
read-count theorem and its derivation, builds, headline axiom check, cost
harness, query semantics, payload-bit accounting, read-only trace vocabulary,
width/capacity, and construction identity.

**P1-1 — the mandatory WordRAM trust-base gate is BROKEN at the target.**
`scripts/wordram_axiom_check.lean:197` and `scripts/axiom_check.lean:975` still
request `..._nonSyntheticWeight_sum_le_76`; the live theorem is `..._sum_le_207`
(`SuccinctFinalRAM.lean:9411`). `gate.ps1:76-80` treats this as fatal, so the
full gate exits 1. **This is a coordinator process failure, not a worker
failure.** Every rung prompt from B3 onward said "Do NOT run gate.ps1 --
coordinator owns it pre-integration", and the coordinator then never ran it
across B3, B4, B6, or E1. B3's rename updated the headline check and topology
lint but missed these two inventories, and four rungs of green batteries could
not catch it because the battery excluded the one check that would.

**WDD-mandated rule change (durable):** (a) any rung that renames, retires, or
introduces a public identifier MUST run `wordram_axiom_check.lean` and
`axiom_check.lean` in its final battery -- they are cheap and they are the only
name-level trust check; (b) the coordinator runs the full `gate.ps1` at every
RUNG boundary, not once at integration. A battery that omits a mandatory gate
component is not a battery.

**P1-2 — whole-query returned-ANSWER dependency is open.**
`INV-B4-VALUE-DEPENDENCY` ("returned values and routing decisions depend on
actual charged reads") is marked Closed, but the checked theorems conclude only
full-`TraceResult`-record inequality; since the disagreeing read is itself in
the trace, record inequality can hold with `.value` identical. Component-level
corruption witnesses exist but a single witness is not a universal claim.
Disposition: **PROVE the answer-level theorem; do not narrow the invariant.**
This is the anti-oracle core -- it is what separates "the machine computes the
answer from the counted data" from "the machine merely logs reads."

**P1-3 — REQ-B6-04 is Closed above its checked conclusion.** The same-block
liveness witness reaches only the isolated LCA-close component trace under a
block-equality hypothesis: no `xs`, no `ValidRange`, no whole-query position, no
receipt. Disposition: add one valid singleton whole-query witness with an
indexed segment-21 occurrence and full receipt -- B4 already did this shape for
segment 22, so the pattern exists.

**P2-1 — REQ-B4-03 erases the fact it requires.** The repeated-equal-read
witnesses prove `firstPos ≠ secondPos` but the receipts existentially hide
`instrPos`; nothing in the conclusion says the two producing instruction
occurrences differ. Facts used in a proof and erased from the conclusion do not
close an information-level claim. Disposition: expose `instrPos1 ≠ instrPos2`
(the proof already has both witnesses).

**P2-2 — space theorem counts flattened contents, not allocated cells.** Sound
as the repository's payload-bit theorem, but sentinel and per-cell padding cells
are not charged. Disposition: mandatory scope text now; a separate
allocated-cell theorem queued as a strengthening rung (B8), because a reviewer
comparing against the literature's `2n + o(n)` bits will ask exactly this.

**P2-3 — public docs state retired route facts.** `RMQPaper.lean:8-9` (retired
literal), `README.md:82` (old 13/4/4 algebra), `README.md:85` +
`FAMILY_SUMMARY.md:59` + `Headlines/RMQ.lean:248` (20-source universe; actual is
22 sources / segments 0-22), `README.md:112-116` + `FAMILY_SUMMARY.md:75-79`
(fresh segment 21; actual is 23). The topology lint passes because it checks
identifier topology, not prose values -- a real coverage gap in the lint.

**P3 — matrix rows Closed on process attestation.** Named rows across B2/B3/B4/
B6 rest on attested command outcomes rather than checked propositions.
Disposition: relabel attested rows distinctly from kernel-checked rows;
complete REQ-B6-07's commit list; REQ-B6-05 is now coordinator-confirmed (the
literal genuinely did not move).

**Verdict on the verdict:** REJECT is correct and the milestone gate did its
job. The campaign's mathematical core stands; the defects are claim-to-evidence
gaps, one broken script, and stale prose. Repairs delegated to Codex (which
authored the original W19 provenance apparatus) on a separate worktree so E1 can
continue uninterrupted.

## 2026-07-18 (C05 round 9) — verification-standard rule from a self-caught defect

**Trigger:** worker E1-R4k spliced new sections at a marker string that was a
substring of a `/-!` doc-comment line, creating a nested unterminated comment
that swallowed an entire region. Two commits (`06673fd`, `9320bbf`) therefore
claimed lemmas that were **inert comment text**. Per-file
`lake env lean <file>` reported CLEAN, because commented-out code produces no
errors, and the check was additionally resolving against a stale dependency
olean. The worker detected and repaired this itself (`22a8b90`) and disclosed
it unprompted.

**Durable rule (applies to every worker prompt from now on):**
`lake build <root>` is the BINDING verification standard. `lake env lean
<file>` is an iterate-loop aid only and may NOT be cited as the evidence that a
milestone compiles. A milestone commit's evidence must include a root build.
Additionally, when a rung claims a NEW theorem, the cheapest independent proof
that the constant actually exists is `#print axioms` on it -- a name inside a
comment has no axioms because it has no constant.

**Assessed blast radius:** low. The A07 blind audit independently ran the full
builds, both axiom inventories, and the headline check against the campaign
frontier and found only the stale `_sum_le_76` identifier -- a missing-constant
error, which is exactly the failure mode a commented-out theorem would also
produce. Every reconstruction round additionally quoted theorem statements read
from source. No evidence of a second instance; no re-audit ordered.

**Related:** this is the second defect this session traceable to a check whose
green output did not mean what the reader assumed (the first being the deferred
aggregate gate, round 8). Both share a root cause worth stating in the
completion gate: **a green check is evidence only of what it actually
examined.** Prefer the check that would fail loudly over the check that is
convenient to run.

## 2026-07-19 (C05 round 10) — V1-S01 scout accepted; validator regression found

**Disposition: ACCEPT the scout.** V1-S01 (Codex) delivered a report-only
scout at `f218b98` on `codex/v1-s01-independent-verification-scout`, parent
verified as the exact target `bacd41b`. It correctly declined to commit CI
automation it could not validate on Linux, correctly separated "verified by
running" from "inferred by reading", and correctly refused to assert
submission-readiness. Quality is high; findings accepted in full.

**NEW BLOCKER not found by A07 — the documented concrete validator FAILS.**
`lake exe rmq_succinct_classic_validate` exits 1 after 127.7 s at
`RMQ/Validation/SuccinctClassic.lean:253`, `singletonRepeatedEqualReadPositionsOK`.
Coordinator-verified at source: the fixture hardcodes global trace positions
`0` and `12` (its docstring says "twelve-event component traces"). A singleton
query is SAME-BLOCK, so the B6 swap changed that trace and position 12 no
longer carries the matching read. The Lean theorems are unaffected -- B4 stated
`firstPos`/`secondPos` symbolically (`secondPos = prefixLen + p`), so they
adapt and still prove; only the executable fixture's literal is stale.
Documented reproduction calls the validator BEFORE the axiom checks and gate,
so a stranger's very first substantive step fails.

**Root cause is the coordinator's battery specification, for the second time.**
Round 8 recorded that I omitted `gate.ps1` from every rung battery and a stale
identifier survived four rungs. The same defect class recurs here: my battery
spec listed the cost harness but NOT `lake exe rmq_succinct_classic_validate`,
so no rung ran the executable validator, and my B6 reconstruction explicitly
instructed the auditor to treat executables as given. Three independent checks
(worker battery, coordinator reconstruction, A07 -- whose gate run aborted
earlier on the stale axiom name) all missed a failing validator.

**Battery specification amended (durable, applies to every future rung):** the
final battery MUST include, at minimum, the root builds, BOTH axiom
inventories, `lake exe rmq_succinct_classic_validate`, the cost harness, the
hygiene scans, both `git diff --check` forms, the strict design check, claim
drift, topology lint -- and the coordinator runs full `gate.ps1` at the rung
boundary. Any rung that changes an accepted-route TRACE must additionally
re-run every executable fixture that indexes trace positions.

**POSITIVE, and significant: independent kernel checking works.** An official
Lean 4.22 exporter produced a 54.5 MB dependency closure for the canonical
headline two-sided profile, and current Nanoda source checked all **6,643
exported declarations with no errors**. This is the strongest independent
trust-base evidence the project has. Full-module export (407 MB) panics inside
Nanoda's definitional-equality checking, and the latest RELEASED Nanoda cannot
parse Lean export format 3.1 -- both are upstream checker limitations, not
project defects. Next step: pin the exporter and the known-working Nanoda
source commit, curate a list of filtered headline closures, and record the
admitted axiom list.

**Other findings (already in flight):** stale `_sum_le_76` inventories and the
retired-fact documentation drift are A07 P1-1/P2-3, delegated to R1. The Linux
CI blocker is new detail on a known gap:
`scripts/project_skill_preflight_regression.ps1:38` invokes `powershell`, which
does not exist on Ubuntu runners (`pwsh` does), plus Windows-shaped child paths
and `GIT_CONFIG_GLOBAL=NUL`; the smallest fix is redispatching via
`(Get-Process -Id $PID).Path` as sibling scripts already do.

## 2026-07-19 (C05 round 11) — second defect in axiom_check.lean; R1 scope amended

**Finding (E1-R4l, reported not edited — correct, the file belongs to the
concurrent repair worker).** `scripts/axiom_check.lean` exits 1 at the accepted
base `d90b062` for TWO independent reasons, only one of which A07 identified:

1. (A07 P1-1, known) line 975 requests `..._nonSyntheticWeight_sum_le_76`; the
   tree carries `..._le_207`.
2. (NEW) it imports `RMQ.Core.GenericSelectBPCompat`, which `lake build RMQ`
   never builds, so the script fails to LOAD at all — independent of the stale
   name. Fixing only the name leaves the script broken.

Substantively the run is clean once the dependency is built (zero `sorryAx`
across 2430 lines), but the script cannot certify that while it aborts.
Consequence: the battery item "`axiom_check.lean` MUST exit 0" is currently
unsatisfiable by any worker until BOTH defects are repaired. R1's scope is
amended accordingly.

**Process note, positive:** this is the first rung executed under the round-9
and round-10 rule changes, and both took effect. E1-R4l cited root builds
rather than per-file checks, ran `#print axioms` on all 23 claimed theorems to
confirm they are real constants (no `sorryAx`, no comment-swallowed
declarations), and caught roughly twenty wrong line numbers in its own resume
inventory before committing it. The rules are doing what they were written to
do.

**Risk flagged for the successor:** the address preamble must first establish
whether `blockSize` is a per-shape constant on the accepted route, because the
ISA deliberately has no variable-divisor instruction (`divConst` only). Expected
to be fine — `canonicalBPRelativeSummaryBlockSizeRaw shape = 2 * (Nat.log2
shape.size + 1)` is determined by the shape, and machine programs are
constructed per shape — but it must be confirmed, not assumed, and if it fails
it is a genuine ISA-level obstruction requiring a coordinator decision rather
than a worker workaround.

## 2026-07-19 (C05 round 12) — interior-leg runtime log2: third instance, decision pending

**Finding (E1-R4m, coordinator-verified at source).** The divisor risk gate
PASSED: `blockSize` is shape-determined (`2 * (Nat.log2 shape.size + 1)`,
always >= 2) at every accepted-route call site, so the address preamble needs
only `divConst`/`mulConst` with per-shape immediates -- no invented
instruction. But a different ISA-level issue blocks the interior leg.

`bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598-599`) -- the classic
sparse-table two-span trick -- is evaluated on a RUNTIME-derived `blockCount`,
and the resulting level feeds the accepted read address
(`LocalGlobalSparse.lean:200-202`). Two distinct consequences:

1. **Machine level (E1's blocker).** The machine must compute the level to
   reproduce the accepted receipts. The existing ISA can, by halving with the
   constant 2, but that loop runs `Nat.log2 count` times with NO literal
   all-size cap -- contradicting REQ-E1-06(c) as frozen, and therefore
   REQ-E1-07. Structurally the same shape as the refuted R3 obstruction but far
   weaker: log-many rather than per-position, and every iteration charged.
2. **Route level (NEW, beyond E1's scope).** The accepted route computes this
   silently. Under the round-7 principle it is ALGORITHMIC WORK -- it forms an
   address -- not a representation artifact, since its value is not
   checked-equal to an input parameter or a charged read. So the B6-repaired
   charge-policy claim is STILL incomplete. This is the THIRD instance of the
   defect class (B2 fringe scan, B6 same-block scan, now interior log2).

**Why A07 missed it:** A07 inspected `InteriorDirectory.lean:1785-1809` and
correctly found a constant-branch decomposition there. The log2 lives two
levels deeper, in the sparse argmin. Building the machine is what forced it
into view -- the E1 rung earning its keep as a defect detector, exactly as
intended.

**Honesty qualifier carried from the worker:** this is a structural finding
from reading route definitions with exact file:line, NOT a checked Lean
non-existence theorem. Proving no literal bound exists would need a step lower
bound nobody has attempted. Adjudicate it as well-evidenced, not as proved.

**Also recorded:** the planned M5 supersession wording ("every loop is a chunk
fold under a literal cap") is FALSE as written for this leg. The per-position
clause is genuinely void; the literal-cap clause is not, until this is
resolved. Do not ship that sentence unamended.

**Options (coordinator recommendation: C, with A as the stall fallback):**
- (A) Declare an `msb`/`log2` unit-cost ISA instruction. Cheapest; unblocks E1
  immediately; msb is standard in word-RAM formulations and is real hardware
  (BSR/LZCNT). But it is a declared primitive, and it leaves the route-level
  silence disclosed rather than fixed.
- (B) Amend REQ-E1-06(c) to `A + B * machineWordBits`. Honest, but the machine
  step count becomes Theta(log n) -- the headline weakens from constant-step to
  O(log n)-step, which a reviewer will read as "not constant time".
- (C) **Charge it: store the level, or read it from an o(n)-bit
  floor-log2 table.** Fixes BOTH levels with one mechanism; keeps the campaign's
  signature theorem (every charged event is a memory read) intact; adds no
  declared primitive; reuses the exact B2/B3/B6 pattern, so the machinery and
  audit patterns already exist. Size: the sparse structure indexes macro-block
  counts, i.e. n/polylog many values at log log n bits each, comfortably o(n).
  Cost: one more B-style route rung (new/extended counted region, re-derived
  literal, provenance, full battery) -- on B6's evidence roughly 2-3 sessions.
- (D) Restructure to avoid log2 entirely -- speculative, not investigated.

Note (C) is the same move the campaign already made twice, and the same
resolution shape as the queued allocated-cell space theorem: fix the mechanism
rather than widen the assumption set.

## 2026-07-19 (C05 round 13) — user chooses the charged fix; B7 launched

**User decision:** pursue the charged fix for the sparse level, "or whatever
option gives the best and most unimpeachable result." Explicitly NOT
authorized: an `msb`/`log2` machine instruction, or weakening any bound to
accept Theta(log n) work. This is the second time the user has chosen the more
expensive, more precedent-matching route over the cheaper assumption (the
first being Option B over Option A at the campaign's start), and it is
consistent with the project's stated goal of minimising precedent-free
justification.

**Coordinator source verification before launch — the finding is confirmed with
exact executed sites.** `let level := Nat.log2 count` appears in the EXECUTED
interior evaluator at `EndpointFringe/InteriorCandidate/InteriorRAM.lean:573`,
`:621`, `:819`, `:867` (the last two on `macroSpanCount`), on runtime-derived
arguments. The level reaches an accepted read address through
`bpGlobalSparseCellSlot macroCount macroStart level = level * macroCount +
macroStart` (`EndpointFringe/InteriorCandidate/LocalGlobalSparse.lean:199-201`).
Four executed sites, not one.

**B7 launched** on branch `claude/b7-charged-sparse-level` in worktree
`.worktrees/b7-charged-level`, based at the campaign HEAD `f6564ec`, isolated
from the two concurrent workers. Its milestone 0 is a MECHANISM DETERMINATION
committed before any implementation, choosing the highest workable option from:
(1) the level is already derivable from a directory entry the route already
reads -- nearly free; (2) store it as a widened field in an existing counted
entry; (3) a new o(n) floor-log2 table in the established B2/B3/B6 pattern;
(4) restructure to remove the runtime log2. Preference order is deliberate:
prefer arithmetic on data already charged over new counted storage.

**Explicitly required of B7:** derive whether the route literal moves rather
than assuming either way (B6's added reads fit under the existing MAX-over-
branches cap and 207 did not move; that may or may not recur), re-establish the
readWord-only vocabulary theorem over the amended route, and repair the
charge-policy section of `PAPER_MODEL_ADEQUACY.md` so it is true after the rung.

**Stretch goal set, and it is the strategically important one:** a COMPLETE
INVENTORY of every uncharged computation reachable from the accepted
whole-query route, each classified as representation artifact (with its checked
bridge lemma) or charged. Three instances of this defect class have now been
found by three different mechanisms -- a worker refusing to fake a proof, a
coordinator adjudicating an audit alarm, and a machine construction forcing
every quantity to have a provenance. An enumeration is what converts "we fixed
the ones we found" into "here is the complete list", and it is the single
highest-value artifact remaining for reviewer confidence.

## 2026-07-19 (C05 round 14) — log2 scout: my citations were wrong; option (A) is dead

**The scout corrected the coordinator, not the worker.** The sites I circulated
(`InteriorRAM.lean:573/621/819/867`) are cost-model TWINS not on the executed
route -- their caller chain dead-ends at
`concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe`
(`SuccinctFinalRAM.lean:2238`), which has no definition-level caller. The
executed route is the `FlatStoreComputation` family, and the class-(a) sites
that feed a read address are exactly THREE:
`InteriorDirectory.lean:2117` (local, -> `bpLocalSparseCellSlot`),
`InteriorDirectory.lean:2131` (global, -> `bpGlobalSparseCellSlot`), and
`SparseArgMin.lean:599` (sets `rightLocalStart`). Worst case is six `Nat.log2`
evaluations per query on the cross-macro branch. Corrections relayed to B7
before it could build on the wrong anchors. **Lesson: I propagated line numbers
from a worker report without walking the caller chain myself. Verify the
REACHABILITY, not just the existence, of a cited site.**

**`machineWordBits` is clean** -- every definition-level call on the route takes
a shape-determined argument (`shape.bpCode.length` or a `canonicalLayout`
field, itself a pure function of shape). Per-shape constant, not a defect. This
closes a question that had been open since the model-adequacy work.

**Three findings that change the engineering:**
1. The level CANNOT come from an existing charged read -- chicken-and-egg, since
   the address of every candidate read already requires the level. Mechanisms
   "derive from existing read" and "store in existing entry" collapse into "new
   table indexed by count, read first".
2. Charging `Nat.log2` alone is INSUFFICIENT: `bpSparseLogSpan = 2 ^ Nat.log2 n`
   is a second Theta(level) recursion whose result sets an address argument.
   Both level and span must come from the row.
3. No new segment and no new `ReviewerSource` constructor are needed -- the
   interior execution maps onto ONE segment via
   `flatStoreExecutionTraceResultAtSegment`. Same property that made B6 cheap.

**The decisive open number:** `canonicalRelativeRmmPrincipledInteriorChargedTrace
Cost := 30` appears exactly tight (3 two-spans x cost-le-ten). If tight, interior
30 -> 33, closeLCA 126 -> 129, and the route literal 207 -> 210, dragging the
full claim-registry/topology/doc migration; if it has >= 3 reads of slack, the
literal holds and this is a clean B6-shaped rung. The scout established
tightness by arithmetic and a docstring but did NOT read the cap proof
(`InteriorDirectory.lean:4457-4505`). B7's first task is now to settle it and
commit the answer before implementing. A moving literal is authorized and
mechanical -- 76 -> 142 -> 207 are all already frozen historical constants --
so this changes cost, not viability.

**Option (A) is dead, on a sharper argument than the coordinator's.** At the
trace layer cost IS trace length, so an event-free msb instruction costs ZERO
there: (A) operates at the wrong layer and buys nothing where the route's
charge policy lives. Worse, the standardness claim for a unit-cost msb is
**nowhere substantiated in this repository** -- zero hits for msb / most
significant bit / clz / leading zero / floor-log across `PAPER_MODEL_ADEQUACY`,
`PAPER_RELATED_WORK`, `RELATED_WORK_AND_LIMITATIONS`, `WORD_RAM_REVIEW_PACKET`,
`PAPER_MAIN_THEOREM`, and `TRUST_BASE`; the only occurrence is a bare uncited
assertion in a worklog. Against the project's own ratified decisions preferring
tables to primitives (`DESIGN_DECISIONS.md:2430-2433`, `:3610-3613`), (A) would
have been a regression dressed as a shortcut.

**Scout's own recommendation was (B)**, on cost grounds. Overruled: (B) does not
fix the route-level defect at all -- it only restates E1's machine bound -- and
the user's instruction was explicitly the most unimpeachable result. Recorded
because a dissenting recommendation should survive in the record: if the cap
proves tight AND runway later becomes critical, (B) plus an honest disclosure
is the fallback, not (A).

**Also corrected:** the note at `E1_WORKLOG.md:2340-2343` rejecting a table read
as "breaking REQ-E1-04 positional receipt equality" is over-strict. B2, B3 and
B6 each added reads to the accepted route; changing the trace is a re-freeze
cost, not an impossibility.

## 2026-07-19 (C05 round 15) — the E1 machine is executed for the first time

**Milestone.** Until this session `E1Machine.run` had NO CALLER anywhere in the
repository. Every machine fact was a kernel-discharged `RunsTo` proposition; no
modeled instruction had ever been run. `RMQ/Validation/E1MachineValidate.lean`
(new `lean_exe rmq_e1_machine_validate`) is the first execution, and it exits 0:

- independent reference `refRMQ` written from the specification, calling
  neither the route, the machine, `Cartesian`, `SuccinctClassic`, nor
  `scanWindow`; 31 fixtures, 576 expectations (258 `none` / 318 `some`),
  materialised BEFORE any machine run; 0 self-check failures;
- dispatch vs route: 405 cases, 0 mismatches;
- same-block leg: 90 cases, 0 exit failures, **0 receipt mismatches**;
- select leg: 32 cases, 0 exit failures, 0 receipt mismatches.

The leg checks are the strongest content in the campaign to date: the machine's
EXECUTED `readLog` is diffed event-by-event against the route's independently
computed `.trace`, with neither side derived from the other. That is executable
confirmation of the same receipt clause the `RunsTo` theorems prove -- two
independent evidence tiers agreeing on the same object.

**Mutation evidence, and a lesson in what to check.** The dispatch mutation
(`natEq -> natLt`) produced 266 disagreements. The leg mutation (back-edge
`brNZ fCnt 97 -> 98`) preserved program length AND still reached the correct
exit pc, so an exit-code or control-flow check sees NOTHING -- the harness
prints that 0 deliberately. Only the receipt diff caught it: 81 mismatches,
30060 modeled steps against the honest 30343. Record this as the argument for
diffing receipts rather than verdicts.

**Reporting-integrity finding.** `scripts/wordram_axiom_check.lean` exits 1 at
this base (line 197 prints axioms for `..._sum_le_76`, an unknown constant).
A07 found it, this session's worker independently confirmed it, and its branch
never touched the script. But an EARLIER session's log recorded that same
script as exiting 0 -- a deterministic error cannot exit 0, so that earlier
report was wrong. Worker-reported check results are ATTESTATION, not
verification; this is the same evidence-tier point A07's P3 finding made about
matrix rows, now demonstrated on a command result. Reinforces the round-8 rule
that the coordinator runs the gate at rung boundaries, and adds a prompt-level
requirement: report observed results with the decisive output line pasted, and
never carry a predecessor's claimed result forward as your own observation.

**Also settled this session:** the branch dispatch is genuinely unblocked and
its distinction from the blocked leg is now stated precisely -- `blockSize =
2 * (Nat.log2 shape.size + 1)` is a function of `shape` alone and is an
encodable immediate, whereas the interior `Nat.log2` is applied to a
runtime-derived `blockCount` feeding a read address. **The distinction is the
operand, not the logarithm.** Worth quoting in the eventual model statement.

**Anti-vacuity raised again:** because a branch `target` is a bare `Nat`, a
hosting witness alone is insufficient -- a theorem about a target past the end
of the program is equally true and equally worthless. The worker discharged
hosting against a concrete program whose same-block target is COMPUTED from the
cross arm's length, then EXECUTED both directions onto distinguishable halts.
That bar (execute both branches, do not merely host them) should carry forward.

**Round 15 addendum — coordinator independently verified the disputed check.**
Ran `lake env lean scripts/wordram_axiom_check.lean` at the campaign HEAD under
the heavy-verification mutex: **exit 1**, confirming A07 and the E1 worker and
refuting the earlier session's logged exit 0. Recording a first-hand
observation rather than a third attestation, which is the point of the rule.

## 2026-07-19 (C05 round 16) — B7 is forced into one atomic commit; inventory corrections

**B7-02 implemented step 2, verified it elaborates with zero errors, then
REVERTED it rather than commit.** Correct call, and the reasoning is worth
preserving: `CanonicalRelativeRmmInteriorStoreProfile.component_flattens`
(`InteriorDirectory.lean:5456`) asserts the component store flattens to the
enumerated payload list, so any new region is necessarily COUNTED. A counted
region no execution reads is a dead source, which the standing rules forbid at
EVERY commit. Therefore the reads must be wired in the same commit; wiring them
breaks the per-two-span caps; that moves the interior cap; that moves the
literal. **Steps 2-5 are one atomic commit and cannot be separated.** Verified
by the actual failure, not inferred:
`FlatPayload.lean:2271:8: type mismatch ... canonicalRelativeRmmInteriorComponentStore_flattens_payload`.

This is the anti-dead-source rule doing real work: it forces the swap to be
honest in one step rather than allowing a window in which counted storage
exists that nothing reads.

**Inventory corrections of record**, all checked at source and all against
COORDINATOR-circulated anchors:
- the file is under `EndpointFringe/InteriorCandidate/`, not `PrefixRange/`;
- every `InteriorDirectory.lean` line number previously circulated is low by
  ~59 (`canonicalRelativeRmmPrincipledInteriorChargedTraceCost` is at `:1843`,
  not `:1783`);
- `..._CloseCost_eq` does not exist; the real names are
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq`
  (`SuccinctFinalRAM.lean:8818`, = 126) and `..._ChargedTraceCost_eq`
  (`:8823`, = 207);
- there are **four** executed sites, not two — the `Costed` twins at `:1769`
  and `:1783` are equated to the `Computation` sites through the `_refines`
  chain;
- and a **fifth parallel family nobody had listed**: `WordReads.lean:203` and
  `:260`, each with its own `let level := Nat.log2 count`.
- step 2 additionally breaks four PRE-EXISTING `_refines` proofs (`:2818`,
  `:2872`, `:2926`, `:2982`) whose `hmiddle` terms spell the store list out
  literally.

Three successive rounds have now corrected circulated line numbers. Treat every
anchor in a prompt as a hypothesis; the campaign's own record is that they drift
faster than they are re-verified.

**Located, not solved — the one genuinely novel piece.** The space-accounting
theorems (`:5276`, `:5303`): the existing proof's `m * M <= 5 * n` yields
`M <= 5n`, far too loose for the level term (it gives ~`n log n`, destroying
o(n)). The tighter `M = (Nat.log2 n + 1)^2` must be used directly. Budgeted
explicitly for B7-03 rather than assumed away.

**Process note:** B7-02's step-2 work was saved only to a SESSION-LOCAL
scratchpad, which would have been lost. B7-03 is instructed to reconstruct and
commit it as `docs/internal/B7_STEP2_WIP.patch`, following the `B3_M5_WIP.patch`
precedent. Add to the standing rules: work that cannot be committed as green
must still be committed as a patch artifact, never left in a scratchpad.

## 2026-07-19 (C05 round 17) — the "binding standard" rule was itself incomplete

**Finding (E1-R4p).** `lake build RMQ` printed `Build completed successfully`
while `RMQ/Validation/E1MachineValidate.lean` was failing to compile, hiding
three compile errors. The module belongs to a `lean_exe` target, not the `RMQ`
library, so the library build never touched it.

This corrects the round-9 rule. "`lake build <root>` is BINDING" is true only
for what that root actually closes over. **Amended standing rule:** a battery
must build and run EVERY target whose correctness it claims — explicitly
`lake build <exe>` and `lake exe <exe>` for each executable, in addition to the
library roots. Running the executable is what forces its build; a library build
is not a proxy for it.

This is the fourth instance this campaign of a green check whose scope was
narrower than its reader assumed: the deferred aggregate gate (round 8),
per-file `lake env lean` on commented-out code (round 9), the omitted executable
validator (round 10), and now a library build that skips `lean_exe` targets.
The general form is stable enough to state as doctrine: **name what a check
covers, and assume it covers nothing else.**

**Second finding — the cross-block blocker is not the interior leg.** Reading
the cross-block object at source (`RelativeRmmMacro/ChargedFringeTrace.lean:1144`,
a path component earlier surveys omitted), it sequences FIVE sub-computations,
not four, and the seeds are not adjacent. The three-way candidate merge
`bpCandidateMerge3?` has NO machine block at all — a repo-wide search over
`RMQ/Core/WordRAM/` for any merge block returns nothing. `sameBlockClose` does
not generalise to it: that block exploits `bpFringeCandGlobal` being total into
`some`, whereas `middle?` is genuinely optional. So the cross-block arm is
blocked ahead of the interior leg, by missing machine work rather than by the
adjudicated `Nat.log2` question. The worker designed the block (16 instructions,
read-free, `+1`-biased option encoding per the house idiom) and recorded the
interior's interface obligation, but did not build it — six control paths
exceeded the budget to build AND verify, and a half-built module is worse than
none. Correct call; it is now the next unblocked target.

**Premise correction in the campaign's favour:** the leg theorem did NOT need
re-derivation. `sameBlockLeg_runsTo_canonical` was already base-parametric; only
the concrete witness was pinned to base 0, and it hardcoded FOUR internal
addresses rather than the two previously named. The fix was a new witness
program plus a specialisation lemma (`sameBlockLegProgramAt_zero`) proving the
base-parametric form collapses to the original, so nothing already landed
regressed.

**Reporting discipline continues to pay:** the worker observed 298 axiom lines
where an earlier session's log recorded 311, and reported what it ran. Two
sessions running have now corrected a predecessor's logged check output.

## 2026-07-19 (C05 round 18) — B7 scope shrinks; a worker declines an authorization

**Site count is FOUR, not six — proved, not assumed.** B7-03 walked consumers
from the root and discharged the "fifth family" worry negative: both
`WordReads.lean` definitions funnel into `bpTwoLevelInteriorCandidateWordsRead`,
whose only def-body consumers are the LEGACY directory's `payloadWordsRead`
field (the canonical directory sources that field from
`canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore`) and a logical
audit projection consumed by two theorems. Charging the four reachable sites
closes the rung with no residual Theta(log n) computation behind it. The worker
re-verified this by hand rather than accepting its own subagent's account, and
correctly refused to propagate that subagent's line numbers because it had read
the tree mid-edit.

**The space-accounting fix was not the predicted one.** The prediction was a
symbolic `M = (Nat.log2 n + 1)^2`. The actual fix is the tight cube bound
`hMw : M * w <= 8 * n` already sitting three lines above in the same proof.
Links 1-3 are done: `..._payload_length_eq_raw` stays an exact equality;
`..._le_linear` has its constant DERIVED 218 -> 527; `_littleO` remains, with
its decisive error recorded verbatim for the successor.

**A worker declined a coordinator-granted relaxation.** The delegation
explicitly authorized weakening `..._eq_legacy_of_compactReady` to `<=`. B7-03
did not use the authorization: it kept the exact equality, strengthened to
`= legacy + canonicalRelativeRmmInteriorLevelTableOverhead shape`. Recording
this because it is the disposition the completion gate exists to produce --
an authorization to weaken is a ceiling, not an instruction, and a worker that
finds the stronger statement achievable should take it.

**Minor but worth knowing:** a committed `.patch` artifact necessarily trips
`git diff --check`, because a blank context line in a unified diff is a single
space. The `B3_M5_WIP.patch` precedent has the identical property (103 hits).
Structural, not a source defect; stripping the spaces would corrupt the patch.
Expect and explain these hits rather than fixing them.

**Recovery mechanism validated.** The step-2 work that lived only in a
session-local scratchpad is now durable at 661 lines and `git apply --check`
clean. Two workers in a row have correctly refused to commit a partial swap and
refreshed the patch instead. The rule holds: work that cannot be committed
green must still be committed as an artifact, never left in a scratchpad.

## 2026-07-19 (C05 round 19) — two discriminators, neither subsuming the other

**Methodological finding (E1-R4q), worth carrying into the paper's evidence
story.** The three-way candidate merge block is READ-FREE, so receipt diffing --
the discriminator that caught every previous machine mutation, including the
single-operand rebased back edge that preserved length, opcodes and exit pc --
is UNAVAILABLE: honest and mutant emit the same empty receipt. Its mutant D
changes one source operand and preserves exit pc, modeled steps AND receipt,
verified case for case (`mergeMutantDIsValueOnly=true`). Only the independent
reference VALUE rejects it.

So the two discriminators are complementary and neither subsumes the other:
- receipt diffing catches control-flow-preserving mutations in read-bearing
  blocks, where the value may coincidentally agree;
- independent-value checking catches value-only mutations in read-free blocks,
  where the receipt is necessarily identical.
A validator carrying only one of them has a blind spot with a known shape. Both
are now present and both have a witnessed mutation they alone reject.

**Honest non-claim:** the worker recorded that REQ-E1-04 gained NOTHING this
session and said why in the worklog -- a read-free block has no receipt to
compare. Declining credit the evidence does not support is the behaviour the
completion gate exists to produce.

**A prose-only fact got a lemma.** `bpFringeCandGlobal_isSome` -- totality of the
global fringe candidate -- was relied on at several sites and asserted in three
prose comments, with no lemma anywhere. Now proved. Worth a sweep for other
load-bearing facts that live only in comments.

**New unrecognised prerequisite for the cross-block arm.** The earlier inventory
listed "the two arms hosted" as comparable to re-hosting seeds. It is not:
`sameBlockLegProgramAt` exists because someone built the leg's instruction-list
form, whereas the fringe ARM has no counterpart -- `fringeArm_runsTo` is stated
entirely against hosting hypotheses and a repo-wide search for any
`fringeArmProgram` returns nothing. An arm layout plus a five-segment layout
with a hole is new construction, larger than the merge that was just built. The
worker stopped rather than start it, which was right.

**The interior interface is now a signature rather than an intention:** `middle?`
arrives in `mMV` (77) biased, position in `mMP` (78), unconstrained when absent.
DD-20260718-012 records why a sentinel encoding would break the accepted route's
leftmost tie-break under strict `<`.

## 2026-07-19 (C05 round 20) — the frozen constants were not frozen

**Defect of record, campaign-wide, found by B7-04.** The frozen historical
algebras for 76 and 142 set `interiorDirectory :=
canonicalRelativeRmmPrincipledInteriorChargedTraceCost` -- the LIVE definition.
Moving the live interior cap 30 -> 33 therefore rewrites history to 79 and 145
and breaks two frozen `rfl` identities. **A historical constant parameterised by
a moving part is not frozen.** This is a defect in how B3 and B6 executed the
freeze pattern, not merely a B7 obstacle: the campaign has twice claimed to
preserve a historical record that is in fact a function of current definitions.

Repair ordered as a prerequisite to B7's cap move: mint a pinned literal
historical interior component (30), repoint the 76 and 142 algebras at it, and
re-verify both frozen `_eq` identities by `rfl`. A SWEEP for the same defect
class across all frozen constants is ordered with it -- any frozen constant
whose definition references a live def rather than a literal is the same bug.
`328` is reported unaffected; confirmation required, not assumed.

Note what this implies about the earlier reconstruction rounds: B3's and B6's
literal migrations were audited and passed, because at those moments the
identities did hold by `rfl`. The defect is only observable when a tracked
component moves. **An identity that holds today is not evidence that a constant
is pinned.** Worth carrying into the audit checklist: for any claimed frozen
value, check whether its DEFINITION is a literal or a reference.

**Staging split approved with the worker's correction adopted.** I proposed
decoupling the literal migration from the store swap. The worker endorsed it as
mechanically sound but required that the intermediate slack be SELF-ANNOUNCING
IN LEAN rather than only recorded in the worklog -- because REQ-B7-05's own
anti-vacuity challenge exists to catch "the literal moved because a cap was
loosened", and between commits A and B that state passes every mechanized check
except CHK-04. Adopted: commit A must carry a checked proposition stating the
current route's interior cost is <= 30 while the algebra field is 33, so the
looseness is visible to a checker rather than to a reader of prose. Commit B
retires it by making the bound tight again. This is the second time a worker has
improved a coordinator-proposed relaxation rather than simply taking it.

**Measurement humility.** The literal-store-decomposition repair surface is a
LOWER bound, not a measurement: two further breakages (`ReviewerPhysical.lean:
1815`, `ReviewerReachabilitySmall.lean:2088`) surfaced only because that
session's build progressed further than any previous one. Successors are told to
expect overrun and not to read a surprise breakage as being off-plan.

**Cross-branch routing recorded:** `ReviewerReachabilitySmall.lean:2088` is an
a07-owned file but a hard build blocker for B7. B7 carries the minimal repair in
its own clearly-marked single-file commit so the coordinator can drop or keep it
at merge depending on what a07 landed. B7's history otherwise touches no
a07-owned file.

## 2026-07-19 (C05 round 21) — watchdog stall; coordinator runs the experiment

**B7-05 stalled** (agent watchdog, no output for 600s) while running the very
experiment its plan called for. Two ordered prerequisites had already landed
committed, which is why the stall cost almost nothing:
- `228ae8f` — **the freezing-discipline defect is repaired.** The frozen 76/142
  algebras no longer reference the live interior cap.
- `0445d1d` — the cross-branch build repair for the a07-owned
  `ReviewerReachabilitySmall.lean`, in its own clearly-marked single-file commit
  so the coordinator can drop or keep it at merge.
Uncommitted state was a single clean line: the live interior cap 30 -> 33.

**Root cause worth naming:** a Lean rebuild after changing a core constant can
sit silent for well over ten minutes, and the agent watchdog kills at 600s of no
output. The campaign's longest builds already run ~380s at baseline and much
longer on a cold cache. **Long silent builds are structurally hostile to
watchdogged agents.** Mitigation adopted: when a worker's next step is a
whole-library rebuild triggered by a core-definition change, the COORDINATOR
runs it in a background shell (no watchdog) and hands the result back, rather
than having the worker block on it. This is the same division of labour already
used for the aggregate gate.

Coordinator therefore ran the 30 -> 33 experiment directly. Expected shape of
the result, recorded BEFORE seeing it so the prediction is falsifiable: the cap
PROOFS should still pass, because widening a cap makes `cost <= cap` strictly
easier; what should break is the `rfl` identities that COMPUTE from the live
field — `closeLCA = 126` and `wholeQuery = 207` — which is precisely what
commit A exists to migrate to 129 and 210. If instead a cap proof fails, the
staging split is unsound and the rung returns to a single atomic commit.

**Round 21 result — prediction confirmed, staging split VERIFIED SOUND.**
Coordinator ran the experiment directly. Setting the interior cap to 33:

1. First failure was NOT a cap proof. It was `InteriorDirectory.lean:4567`, the
   CROSS-MACRO branch — the zero-slack one B7-03 identified. Its three siblings
   wrap their bounds in `Nat.le_trans ... (by simp [...])`, which adapts to any
   cap; the cross-macro branch applies its lemma directly with `exact`, so a
   `<= 33` goal stops type-matching. Giving it the same wrapper its siblings
   already have fixes it — verified by rebuild.
2. With that wrapper the interior module builds, the run reaches 418.9s (versus
   28.8s before), and it fails at EXACTLY the three predicted sites, all of them
   commit A's scope: `SuccinctFinalRAM.lean:8821` and `:8825` (`rfl` failures on
   the `closeLCA = 126` and `wholeQuery = 207` identities) and `:9015` (one
   consumer type mismatch).

So the recorded prediction holds with one mechanical amendment: cap PROOFS
remain provable because widening a cap makes `cost <= cap` strictly easier, and
only the identities that COMPUTE from the live field must migrate. **Commit A is
sound and its failure surface is now enumerated rather than estimated.**

Coordinator reverted both experimental edits, leaving the worker a clean tree at
`0445d1d` so commit A is authored by the worker rather than by the coordinator.
The boundary matters: finishing an experiment a stalled worker started is
coordinator work; writing its commit is not.

**Watchdog mitigation now standing policy.** Whole-library rebuilds after a
core-definition change run 400s+ silent and kill a watchdogged agent at 600s.
Workers must keep output flowing, tee to a polled file, or keep builds
incremental; if a silent cold rebuild is genuinely required, the worker stops
and the COORDINATOR runs it in a background shell and hands back the result.
Same division of labour already used for the aggregate gate.

## 2026-07-19 (C05 round 22) — parameterization worked; complementarity executed both ways

**The interior-agnostic structuring succeeded** (E1-R4r, `49d4810`). The
cross-block arm is stated over `crossBlockArmSpec`, which takes the interior's
whole `TraceResult` as an ARGUMENT, and `crossBlockArmSpec_eq` proves the
accepted object at `ChargedFringeTrace.lean:1144` IS that spec at the interior's
current contents. The interior therefore appears concretely in exactly ONE
equation. When B7 lands and the interior's trace changes, that equation is
re-derived and the structure above it is untouched. This was the whole point of
the sequencing constraint and it held.

Two prior lessons were also applied by construction rather than by repair: the
arm program is base-parametric from the start (no base-0 version, no `_zero`
lemma to schedule — the tax the same-block leg paid), and the worker built two
NEW range preambles after finding `windowRange` is not reusable by either cross
arm (its high endpoint is the same-block span, while the arms run to a block end
and from a block start), rather than pinning to arithmetic that happened to
typecheck.

**Discriminator complementarity is now EXECUTED in both directions**, not
argued. Mutant E charges a fold read to the next segment: same length, same
opcode categories, and because the witness store answers every segment
identically, pc, steps, value and position are ALL unchanged
(`mutantE_isReceiptOnly=true`) — caught only by receipt diffing. It is the exact
mirror of the previous session's mutant D, which preserved receipts and was
caught only by the independent value. Two witnessed failures, one for each
discriminator, neither subsuming the other. The validator now selects per block
and the worker must state which and why.

**Correction to the coordinator's own brief.** `rmq_succinct_classic_validate`
does NOT fail on a stale runtime fixture, as I had been telling workers. It
fails at COMPILE time — `RMQ/Validation/SuccinctClassic.lean:253:0: expression
singletonRepeatedEqualReadPositionsOK did not evaluate to 'true'` — so the
executable never runs. More severe than described, and it means the Validation
module does not build at all. Corrected in all downstream briefs; R1 owns it.
That is the fourth consecutive session in which a worker corrected a claim made
by a predecessor or by me.

**Next unblocked target identified precisely:** `fringeArm_runsTo`
(`E1FringeArmBlock.lean:940`) states NO register-preservation clause, so the
left arm's stashed `mLV`/`mLP` cannot be shown to survive to the merge. That is
a strengthening of an existing theorem and it gates the composed cross-block
`_runsTo`. Not blocked by the interior.

## 2026-07-19 (C05 round 23) — commit A lands; a self-retiring honesty artifact

**B7 commit A is green and verified** (`f6000c3`..`21544b4`): interior cap
30 -> 33, literal 207 -> 210 re-derived by `rfl`, 207 frozen with ALL-LITERAL
algebra fields (each frozen algebra now owns its own pinned components, so the
freezing defect cannot recur), consumers and both axiom scripts migrated.

**The worker improved on a coordinator-verified fix — third time this
campaign.** I supplied a per-branch `Nat.le_trans` wrapper for the zero-slack
cross-macro `exact`. It declined and instead kept the tight proof body VERBATIM
under a new name concluding at the literal `30`, then re-derived the cap-facing
theorem from it. Consequences: no branch mentions the cap at all, so all four
branches close unchanged including the bare `exact`; the tight content stays
independently checkable; and because the CONSUMED name did not change, external
consumers and both axiom scripts needed no edits. A structural fix where mine
was a patch.

**The slack artifact is self-retiring by construction**, which is better than
what I specified:
`..._announced_slack_...` asserts `cost <= 30 /\ 30 < cap /\ cap = 33`. The
middle conjunct makes it an ANNOUNCEMENT rather than a bound, and it becomes
UNPROVABLE once the swap consumes the headroom. Commit B must therefore DELETE
it; it cannot be quietly weakened. An honesty artifact that expires on its own
is worth more than one that relies on someone remembering to remove it.

**Two rows correctly kept OPEN though they superficially read as closed** --
this is the round's most important disposition:
- REQ-B7-05: the literal now reads 210 and re-derives by `rfl`, but the row
  demands it move BECAUSE NEW READS ENTERED THE ACCOUNTING, "not because a cap
  was loosened". At commit A it moved because a cap was loosened -- exactly the
  condition the row exists to reject.
- CHK-04: the harness exits 0 with `canonicalBoundIs210=true` everywhere, yet
  all twelve `modeledTraceCost` values are BYTE-IDENTICAL to the pre-swap
  baseline. Correct for a commit that adds no reads, and independent empirical
  confirmation that the slack theorem is honest -- but the anti-vacuity half is
  unmet.
A worker declining two rows whose mechanized checks all pass is the completion
gate working exactly as designed.

**Inherited finding to settle at commit B's first build:** the WIP patch section
repairing `ReviewerReachabilitySmall.lean` was DROPPED, because commit `0445d1d`
already repairs the same proof and does it better -- quantifying `hmiddle` over
`forall post` (store-growth-invariant) where the patch enumerated the new tail
literally, which is the very brittleness that caused the original breakage.
Unverified: whether the generalised proof survives the store extension. If it
fails, repair in the generalised style rather than reinstating the deleted hunk.

**Lint coverage gap, recurring.** a07-owned stale numerals persist at
`README.md:70,76,140,334` and `docs/FAMILY_SUMMARY.md:9,43,48,133,446,1041`
(`:9` carries `interior30`) with BOTH lints exiting 0. Same class as A07's P2-3:
the topology lint checks identifier topology, not prose numeric values. Two
independent campaigns have now been bitten by it. Worth a dedicated numeric-prose
check rather than another round of manual sweeps.

## 2026-07-19 (C05 round 24) — a third discriminator; E1 pauses at its boundary

**E1's cross-block arm is composed and green** (`cc4adc1`): 370 instructions,
receipts positionally equal to `crossBlockArmSpec`'s trace, with `hInterior`
supplying the interior's own `RunsTo` as a HYPOTHESIS — trace, categories and
value all parameters. Nothing pinned to current interior behaviour, exactly as
the sequencing constraint required.

**COORDINATOR DECISION: E1 pauses here.** The worker's own summary is decisive —
"the single remaining cross-block obligation is discharging `hInterior`;
everything around it is done and green". Discharging `hInterior` IS the interior
leg, which is B7's. Every remaining E1 item (interior simulation, whole-query
glue, derived step literal, amended-target Prop, matrix closure) is downstream
of it, and all eleven rows are whole-query scoped. Launching another E1 worker
now would be ceremonial parallelism against an invented hypothesis. **B7 is the
sole critical path until it lands.**

**A THIRD discriminator, and the reasoning that produced it.** Mutant D was
value-only (caught by the independent reference), mutant E receipt-only (caught
by receipt diffing). The worker observed that NEITHER has any power over a
mutation that computes the right answer, performs the right reads, in the right
step count, and merely scribbles on a register it does not own — which is
precisely the class the session's new preservation clause excludes. So it added
a preservation phase: `presCases=36`, `presCheckedRegs=66`, `presFailures=0`.
**Mutant G** renames the epilogue's scratch register consistently:
`mutantG_isPreservationOnly=true` (exit pc, steps, value and position all match
honest, case for case), caught only by preservation, with the clobbered register
identified as `fClose` in the cross layout.

Three discriminators, three witnessed mutations, none subsuming another. And
the worker documented its own check's VACUITY CONDITION unprompted: the sentinel
seeding is load-bearing, because from a zero-seeded register file the
preservation phase proves nothing. Naming the conditions under which your own
evidence would be empty is the habit this campaign has been trying to instill.

**Two gaps found by needing them rather than by survey:**
`rankSeedLeg_runsTo_canonical` carried only the clauses the same-block leg
happened to need; and `fOne` (register 40) sits INSIDE the fold bank 40..62,
which `candMerge3_runsTo` requires as a hypothesis without restating — so a
one-instruction `crossPinOne` re-pins it (layout 369 -> 370). Both are the kind
of defect that only surfaces at composition time.

**Preservation clause is exact, not conservative:** `FringeArmUntouched` is the
precise union of the fold and cand-global untouched sets, not an
under-approximation that would have been easier to prove and weaker to consume.

**Corrections carried forward:** `set` is Mathlib-only here (fails as "unknown
tactic", then misreports the whole proof as unsolved goals); PC arithmetic stops
associating definitionally once `interior.length` enters it (`A+176+n+1` is not
`A+177+n` by defeq), handled by a new `runsTo_pc_congr`.

## 2026-07-19 (C05 round 25) — a coordinator phrase was wrong; frozen-constant policy stated

**The obstruction, and it is a good one.** B7-07 found that "one charged read
per two-span call" — MY phrasing in the delegation — is FALSE as stated. A
charged read costs one unit PER MACHINE WORD TOUCHED
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`,
`InteriorDirectory.lean:3945`, requires `width <= machineWordBits`), and the
level table's entry width exceeds that on reachable shapes:

| size | b | macroSize | domain | width | machineWord | read cost |
|---|---|---|---|---|---|---|
| 2048 | 12 | 144 | 146 | 15 | 13 | 2 |
| 32768 | 16 | 256 | 258 | 17 | 17 | 2 |
| 65536 | 17 | 289 | 291 | 17 | 18 | 1 |

and macro-crossing is genuinely reachable at 2048 (`macroSize 144 < blockCount
170`), so the maximizing branch carries three reads at cost 2: interior 36,
closeLCA 132, literal **213** — contradicting the 210 commit A had already
frozen and migrated everywhere. The worker caught this by COMPUTING WIDTHS
rather than trusting the coordinator's phrase. Second coordinator claim this
rung has corrected.

**Note what caught it:** REQ-B7-05's anti-vacuity challenge. The row exists to
reject a literal that moved because a cap was loosened, and it did exactly that
job on a tree where every mechanized check was green.

**RULING — tighten the width, and the reason is policy, not cost.** A frozen
historical constant records a value that GENUINELY DESCRIBED THE ACCEPTED ROUTE
at some point. 76, 142 and 207 each did. **210 never did** — it exists only
inside commit A's staging window, an artifact of a deliberately loosened cap.
Freezing it would place a fiction in the historical record, which is worse than
redoing a migration. **The historical record must not accumulate values that
never described a real machine.** Recorded as standing policy for any future
staged migration.

The width fix is also independently better engineering: tightening
`bpSparseLevelCell_lt` from bounding the level by `domain` to
`Nat.log2 (domain * (Nat.log2 domain + 1)) + 1` makes the read genuinely one
machine word, which is what the phrase was always supposed to mean.

**Hard requirement attached:** a table of three sizes is NOT a proof. The fit
must be established for all shapes where the cross-macro branch is reachable,
as a checked proposition. The fit plausibly FAILS at small sizes (at size 4,
width ~6 against `machineWordBits` ~4) and is saved only because macro-crossing
is unreachable there (`blockCount 1 < macroSize 9`) — so the reachability
hypothesis must appear in the statement, and it must be the hypothesis the
route's own dispatch already establishes, NOT a size threshold introduced for
convenience. A threshold in the public route is precisely what this project
forbids. If the all-size proof does not go through, the worker stops and
reports rather than falling back to 213.

**Settled and closed:** the dropped `ReviewerReachabilitySmall.lean` hunk was
correctly dropped — `0445d1d`'s `forall post`-quantified `hmiddle` absorbs both
new store regions untouched, verified green at [229/244]. B7 crosses no a07
concurrency boundary after all.

## 2026-07-19 (C05 round 26) — the numeric-prose gap is closed by a self-auditing checker

**T1 delivered `scripts/numeric_prose_check.ps1` + a 12-case regression
(10 reject / 2 accept)** on `claude/numeric-prose-lint` at `6a8a09f`, closing the
gap that bit twice (A07's P2-3, then B7-06's sweep) where stale documented
numerals passed BOTH existing lints. Coordinator ran it independently: exits 1,
reports exactly one violation, invariants hold, frozen symbols pin.

**Three design choices worth preserving, none of which were specified:**
1. **Zero hardcoded constants, enforced by a registry SELF-AUDIT** that strips
   regex syntax and rejects any remaining numeral not explicitly declared. All
   12 expected values are extracted from their Lean declarations at run time, so
   the checker follows a campaign automatically instead of going stale at the
   same rate as the prose it polices. A checker that checks itself against the
   exact failure mode it exists to prevent.
2. **Clause scoping, not line scoping** — forced by `README.md:73` carrying a
   live cap AND a transitional cap on one line. A line-scoped historical test
   would have exempted the live number and been quietly useless. This was the
   part flagged in the brief as "where the value is", and it is.
3. **A "Lean constant and every doc site moved together -> ACCEPT" control.**
   This is what proves the checker follows legitimate migrations rather than
   obstructing them. Without it the checker gets switched off the first time a
   campaign moves a number honestly.
Marking a clause historical cannot launder a wrong number: it routes to the
entry's FROZEN sibling and must equal it; a marker with no frozen sibling is
itself a failure; and frozen symbols must resolve even with zero doc sites, so
deleting a pinned declaration cannot silently disable the discrimination.

**One genuine violation found**, out of 52 registered sites:
`docs/WHAT_IS_PROVED.md:75` documents `240` where the live interior cap is `30`.
Correctly diagnosed: the repair is to MARK THE CLAUSE TRANSITIONAL, not change
the number — the value matches the frozen `canonicalRelativeRmmInteriorQueryCost`
(`InteriorDirectory.lean:1777`), and `README.md:73` already states the pair
correctly. The A07-era stale numerals were all consistent at `4a60853`, i.e.
repaired since; the checker now pins them so a third recurrence fails.

**NEW GOVERNANCE GAP, same family, one level up.**
`design_decision_check.ps1`'s `workflowPatterns` ENUMERATES INDIVIDUAL SCRIPT
PATHS, so a new gate-class script can be introduced with no design-log entry and
strict checking passes VACUOUSLY — which is exactly why strict passed on T1's
own branch. The worker correctly left that workflow-sensitive file alone and
reported it. Queued as a follow-up: the pattern should match gate-class scripts
structurally rather than by enumeration.

**Gate wiring deliberately deferred to a verified-invocation check only.** The
aggregate gate is already RED on the a07-owned `wordram_axiom_check` stale
constant, so a full end-to-end run would fail on that and prove nothing about
this checker. T1 wires and verifies the invocation, states the external block
plainly, and stops — rather than manufacturing a green it cannot honestly claim.

**Round 26 addendum — T1 complete at `b406bd4`, and a deferral.**

Repair landed as diagnosed: `docs/WHAT_IS_PROVED.md:75` keeps the `240` and marks
the clause transitional, naming the live `30` alongside. Both values now check
green routed to DIFFERENT declarations (frozen
`canonicalRelativeRmmInteriorQueryCost` vs live
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost`), making that row a
second instance of the one-line live/historical mix that forced clause scoping —
the repair exercises the mechanism instead of dodging it. Checker: `NUMERIC-PROSE
PASS (53 sites; 2 historical; 12 symbols extracted from Lean; 0 hardcoded
expected values)`.

**A consequence the worker caught and converted rather than deleted:** repairing
the tree invalidated its own regression case 1, which asserted that the base tree
REJECTS. Rather than dropping it, it became
`historical-marker-stripped-rejected` — strip the marker back off, require
rejection — so this specific drift cannot silently return. Counts preserved at
12 cases / 10 reject / 2 accept.

**Gate wiring verified by extraction, not inspection.** The block was pulled out
of `gate.ps1` and driven in isolation against stub scripts exiting 1, confirming
`Fail` actually fires for each. The worker's own framing is the correct
instinct: "a guard that is present but not honoured would have looked identical
to inspection." No end-to-end green attempted or claimed; that remains blocked on
the a07-owned `wordram_axiom_check` red.

**The governance gap is now empirically confirmed from the inside:** strict
design checking passed VACUOUSLY while two new gate-class scripts were the only
change, and only began demanding entries once a path that happened to be
enumerated was touched.

**COORDINATOR DEFERRAL, deliberate.** The obvious follow-up is to make
`design_decision_check.ps1` match gate-class scripts structurally rather than by
enumeration. **Not now.** That script is executed by every active worker's final
battery; changing a gate script while five branches are running batteries
against it would alter their verification semantics mid-flight and make their
ledgers non-comparable. Queued for the merge window, when the tree is quiet.
Reason recorded so a successor does not read the delay as an oversight.

**Reconciliation note for the merge:** the `WHAT_IS_PROVED.md` edit is one table
row, also touched by B7. The reconciler must keep the word "transitional" in
that clause — if B7 rewords it, the checker will fail rather than let it drift,
which is intended behaviour.

## 2026-07-19 (C05 round 27) — width closed all-size; a false-negative trap in our own check

**The width obstruction is CLOSED**, committed green at `fa5e94d`:

```
theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
      SuccinctRank.machineWordBits shape.bpCode.length
```

plus the global twin. The requirement held: this is an ALL-SIZE proposition
under the route's OWN hypothesis, not a sampled table and not a convenience
threshold. `hmacro` is what the interior dispatcher already derives from its
branch guard plus route-level bounds before any cross-macro two-span call is
reachable, and the pre-existing relative-width lemma carries the identical
hypothesis. The coordinator's small-size worry was confirmed exactly: at
`size = 4` the width is 6 against a 4-bit word and the fit FAILS — saved only
because macro crossing there needs `9 < 1`. And `10 <= base` is DERIVED by
eliminating `base <= 9` against `base^3 < size < 2^base`, not introduced.
Branches without `hmacro` are covered unconditionally at the `cost_le_eight`
rate.

The old bound was exponentially slack by construction — it bounded the stored
LEVEL by `domain` when the level is `Nat.log2 i` for `i < domain`. Tightening to
`domain * (Nat.log2 domain + 1)` is strictly stronger, so nothing was weakened.
The width appears SYNTACTICALLY in 13 places, so the worker bridged with
`bpSparseLevelWidth_le_square_width` rather than reproving, leaving `527` and
both `LittleOLinear` envelopes untouched and sound.

**A FALSE-NEGATIVE TRAP IN OUR OWN EXISTENCE CHECK — sixth instance of the
family.** `import RMQ` does NOT reach `InteriorDirectory`, so `#print axioms`
on a declaration there reports `unknown constant` EVEN AFTER A GREEN ROOT
BUILD. That is indistinguishable from "the theorem was never built" — precisely
the signal this campaign adopted `#print axioms` to detect (a name inside a
comment has no constant). An auditor using an indirect import could therefore
conclude a real theorem is missing. **Rule: when confirming axioms, import the
module DIRECTLY, and never read `unknown constant` from an indirect import as
evidence of absence.** Added to the standing standards.

The running tally of checks whose scope was narrower than their reader assumed:
the deferred aggregate gate; per-file `lake env lean` on commented-out code; the
omitted executable validator; `lake build <lib>` skipping `lean_exe` targets;
strict design checking passing vacuously on unenumerated script paths; and now
`#print axioms` through an indirect import. Six, all found by doing rather than
by reviewing. The doctrine stands: **name what a check covers and assume it
covers nothing else.**

Also of record: splicing Lean source with Windows Python at default encoding
produces mojibake that Lean reports as "unknown tactic" — a misleading error for
an encoding fault.

**Commit B did not land**, correctly: no swap, so the literal is not re-justified
by reads, the slack artifact is still present and still true, and REQ-B7-05 and
CHK-04 remain Open and unclaimed with the harness unrun. Five workers in a row
have now declined to commit a partial swap.

## 2026-07-19 (C05 round 28) — post-B7 prompts pre-staged

Both follow-on prompts are written and committed at
`docs/internal/PREPARED_C05_POST_B7_PROMPTS.md`, needing only the B7 candidate
SHA substituted. Written now rather than at the handoff for two reasons: a
session spent drafting is a session not spent proving, and this conversation is
long enough that the prompts should survive a coordinator handoff independently
of anyone's context.

**Prompt 1 — B7 reconstruction audit (read-only).** Ten items. The ones that
carry the rung's weight: that the silent computation is gone from every
REACHABLE path (with the `WordReads` unreachability re-verified rather than
inherited, since it is the difference between closing the rung and leaving a
Theta(log n) hole); that the slack artifact is DELETED and could not have
survived; that the literal is justified BY READS rather than by slack, which is
REQ-B7-05's entire point; that CHK-04 shows interior windows actually moved off
the recorded baseline; that the width fit rests on the route's own hypothesis
rather than a convenience threshold, with the small-size case handled by
reachability rather than exclusion; and that NO commit in the sequence ever had
counted storage without a reader. It also carries forward the `#print axioms`
indirect-import trap so the auditor cannot mistake it for a missing theorem.

**Prompt 2 — E1 unblock.** Discharges `hInterior` against the AMENDED interior,
which now performs more reads than when the cross-block arm was written, then
composes the full LCA leg, the whole-query glue, the derived step literal, the
amended-target Prop, the validator's whole-query phase, and matrix closure. It
carries an explicit warning that the supersession sentence "every loop is a
chunk fold under a literal cap" was FALSE while the interior recursion existed
and must not be shipped from an older draft — it becomes true only with the B7
dependency stated.

**One decision recorded ahead of firing:** E1 cannot discharge `hInterior`
against an interior not in its tree. Recommendation is to merge B7 into the E1
branch and run the audit in parallel, since the audit is read-only against the
B7 commit itself — a finding is repaired on the B7 branch and re-merged, and
E1's additive machine modules do not modify the interior, so a repair does not
invalidate them.

## 2026-07-19 (C05 round 29) — the swap is in the tree; one diagnosed blocker

**The full swap is applied and uncommitted** in the B7 worktree: nine files
covering the store extension, the four wired sites, the cap and literal
migration, the model-adequacy doc, the claim-drift policy and the topology lint.
Working-tree state survives agent death, so nothing was at risk — but the worker
exhausted its budget cycling on silent builds and was handed off rather than
resumed again.

**The blocker is one root cause with a cascade.** `lake build RMQ` exits 1 at
294.7s with `whnf` heartbeat timeouts in `reviewerCanonicalInterior_mayRead`
(`SuccinctFinalRAM.lean:5953`, `:5992`), and the third error — `(kernel) unknown
constant` at `:6020` — is purely downstream: that theorem never elaborated, so
its constant never existed. Note this is the SAME SHAPE as the indirect-import
trap logged last round, and here it genuinely means "not built". The two are
visually identical, which is precisely why that trap is dangerous.

**Coordinator diagnosis, from reading the proof rather than the error.** The
witness discharges membership through a `List.mem_append_left` cascade that
encodes the READ ORDERING. After the swap the local span computation reads the
LEVEL FIRST, so the level-table read is now leftmost and the span read is no
longer the head of that chain — the cascade describes a route that no longer
exists. The `Nat.log2 1` sitting in the slot expression is the same tell: it
computes at proof level exactly what the amended route now obtains from a
charged read. Secondary and probably contributory: the enlarged `offsets` and
component store push bigger concrete structures through `whnf` in the `simpa`
unfoldings.

**`maxHeartbeats` is explicitly forbidden as the fix**, and the reason is worth
recording as a general rule. Raising it would make the build pass while leaving
a proof that encodes a stale read order — a theorem that typechecks and
describes the wrong machine. That is strictly worse than a red build, and it
survives review precisely because it presents as a performance tweak. **A
timeout in a proof about an execution's structure is evidence about the
structure, not about the budget.**

**Build-discipline handoff now used three times on this rung.** A cold rebuild
runs 300-700s silent; a watchdogged agent cannot wait on it without burning its
budget or being killed. The worker commits, says so, and the coordinator runs
the build in a background shell and returns the result with a diagnosis. This is
the same division of labour as the aggregate gate and it is working.

**Merge-reconciliation items recorded:** the swap touches
`RMQ/Validation/SuccinctClassic.lean` (which also carries an a07-owned fixture —
the literal migration legitimately touches the file, the fixture is left alone)
and `docs/internal/CLAIM_DRIFT_POLICY.json`. Every moved numeral must be listed,
because the new numeric-prose checker derives expected values from Lean at run
time and will fail on any documented numeral that did not move with its source.

## 2026-07-19 (C05 round 30) — B7 COMMIT B LANDED; a DD-ID collision across branches

**The swap is committed and green at `d5a9355`.** The last known uncharged
size-dependent computation on the accepted RMQ route is charged. `lake build RMQ
RMQPaper RMQExamples` exit 0; the literal re-derives
`concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq = 210 := by rfl`
and `#print axioms` reports it and `queryCost_eq` as **"does not depend on any
axioms"** — computed, not asserted. Cross-macro attains the cap at ZERO slack
(within-macro 26/slack 7, adjacent 22/11, left-middle 22/11), so the bound is
tight rather than comfortable. 207 and 126 are frozen over PINNED LITERAL
components, so they cannot track the live cap — the freezing defect stays fixed.
The slack artifact is deleted, with a tombstone at `InteriorDirectory.lean:
5541-5555` recording that it was deleted rather than weakened.

**The coordinator's diagnosis was right about the mechanism and wrong about the
file.** I named `SuccinctFinalRAM.lean`; the live defect was in
`ReviewerReachabilitySmall.lean:2096` — the symptom in the file I named had
already been fixed in the uncommitted tree, which was never logged because
session 9 produced no worklog entry. The worker VERIFIED rather than assumed
(checking that `SuccinctFinalRAM.lean` already elaborated and that
`InteriorDirectory.olean` post-dated its source) instead of chasing my stale
report. Cause (1) was genuinely live at the real site: `slot := ...
(Nat.log2 2)` with `exact List.mem_append_left _ hlocalSpan` claiming the SPAN
read was leftmost, when after the swap the two-span computation binds the LEVEL
read first. Repaired structurally; `maxHeartbeats` untouched. This is precisely
the case where raising it would have produced a theorem describing the wrong
machine.

**CHK-04 ruling: add a fixture, do not exclude one.** Six of eight crossBlock
windows moved; the two static ones have `blockCount = 2`, so the interior is
invoked with `count = 0` and costs 0 both before and after. The reasoning is
sound, but excluding a fixture BECAUSE it did not move — on the strength of an
argument — is the exact move anti-vacuity rows exist to prevent, and it would
convert an observation back into an argument. It also exposed a real gap worth
closing on its own merits: **tie-boundary behaviour with a live interior is
currently untested**, since every fixture in that group has `blockCount = 2`.
B7-11 adds a `blockCount >= 3` tie-boundary fixture and keeps the existing one
as legitimate zero-interior coverage.

**PROCESS DEFECT — parallel branches minted colliding design-decision IDs.**
Merging B7 into the E1 branch conflicted on `DESIGN_DECISIONS.md`: pre-existing
entries end at `DD-20260718-011`, and then E1 and B7 INDEPENDENTLY minted
`DD-20260718-012` for entirely different decisions. Resolved by renumbering E1's
standalone entry to `-014`, leaving B7's `-012`/`-013` Milestone 0/0b chain
intact. **A second collision is already pending:** T1 also minted
`DD-20260719-001`, which B7 has used for the width decision — that one must be
renumbered when `claude/numeric-prose-lint` merges.

The ID namespace is a shared mutable resource and nothing guards it. Options for
the merge window: allocate per-branch ID prefixes, or move to a
content-addressed scheme, or simply have the coordinator assign IDs at launch.
Recorded rather than fixed now, because changing the convention mid-merge would
churn every open branch.

**E1 unblocked:** B7 merged into `claude/b1-b2-charged-fringe-tables` at
`f9b1ecc`, tree clean, 28 E1 modules and B7's `SparseLevelTable` both present.
Merged-tree build verification running.

**Round 30 addendum — merged tree verified, E1 fired.** `lake build RMQ` on the
merged `f9b1ecc` exits 0 at 249/250 with zero errors: E1's 28 machine modules
and B7's charged interior compose cleanly. The pre-staged E1 unblock prompt was
fired with the B7 SHA substituted, carrying forward the three consequences the
worker must account for — the interior now performs MORE reads than when the
cross-block arm was written, the route literal is 210, and the interior cap is
33 attained at zero slack.

Two guards added to the E1 brief from B7's experience rather than from theory:
**do not raise `maxHeartbeats` to clear a timeout in a proof about execution
structure** (B7 hit exactly that, and the real cause was a membership cascade
encoding a stale read ORDER — raising the limit would have produced a theorem
describing the wrong machine); and **take the next design-decision ID from above
the maximum actually observed in the file**, since two branches already minted
colliding IDs and a third collision is pending at the T1 merge.

**B7-11's window accounting correction accepted.** There are NINE crossBlock
windows, not eight — `tiny-leftmost-ties [0,5)` was omitted from the
predecessor's table entirely, so the "6 of 8 moved" framing I ruled on rested on
an incomplete inventory. The ruling stands regardless (adding a live-interior
fixture was right on coverage grounds, not on counting grounds), but this is now
frequent enough to state as practice: **treat every enumerated list in this
campaign as provisional until a successor re-derives it.** Inventories have been
short at least four times — executed sites twice, the repair surface twice, and
now the window table.

**B7-11's new fixture is probed, not assumed.** `tie-boundary-live-interior`
(n=24, base=5, blockSize=10, blockCount=4) has three windows with
`interiorLive=true` and `count=1..3`, and the interior is LOAD-BEARING: the
minimum value occurs only at indices in interior blocks 1-3 while both fringe
blocks carry none, so leftmost tie-breaking is decided by the interior
range-min. That is precisely the interaction the ruling identified as never
having been exercised.

**A scoping judgment deliberately left to the worker, with the labelling fixed
by the coordinator.** Measuring a pre-swap "before" value for the new fixture
may require a full rebuild at an old commit. There is a cheaper derivation
available — a window provably invoking the interior with `count > 0` and showing
a post-swap interior cost of 18 cannot have cost 18 pre-swap, since the pre-swap
interior performed no level-table reads. Either is acceptable, but the worker
must STATE which it used and let the coordinator rule. The difference between a
measurement and a derivation belongs in the evidence record, not buried in a
worker's reasoning, because the eventual auditor must weigh them differently.

## 2026-07-19 (C05 round 31) — B7 CANDIDATE-COMPLETE; CHK-04 closed on observation

**B7 reports CANDIDATE_COMPLETE at `6ad4198`.** CHK-04's evidence is sharper
than the row required: across all 21 windows, **the set that moved is EXACTLY
the set with a live interior** — all nine crossBlock windows with `count > 0`
moved, all twelve without a live interior held still, and no window falls on the
wrong side. The new `tie-boundary-live-interior` fixture (n=24, base=5,
blockSize=10, blockCount=4) moves 112->114, 107->109, 105->107 while its
`count = 0` control holds at 73.

**Two dispositions worth preserving.**

The worker MEASURED BOTH SIDES rather than carrying the recorded baseline
forward — a detached scratch worktree at the pre-swap commit received the
identical fixture — and the nine pre-existing values reproduced the recorded
baseline exactly. The baseline is therefore corroborated rather than inherited,
which is strictly better evidence than the row asked for.

And it DECLINED the coordinator's a-priori shortcut. I had offered that a window
provably invoking the interior with `count > 0` and costing 18 post-swap cannot
have cost 18 pre-swap, since the pre-swap interior made no level-table reads.
The worker did not use it, and its reason is exactly right: **"CHK-04 exists to
convert an argument into an observation, and answering it with a second argument
would repeat the shape of the move the ruling rejected."** Fourth
coordinator-offered shortcut declined in this campaign, and right every time.

**Also recorded:** the previous window table was short by one — `tiny-leftmost-
ties` was omitted entirely — so the "6 of 8 moved" framing I ruled on rested on
an incomplete inventory. The ruling stands on coverage grounds regardless. And
the tie-boundary group's coverage gap is genuinely closed: on that group, store
growth had been visible on every shape (`payloadBits` 541->616, 577->652,
1871->2096, 4635->5103, 10781->11384) but had NEVER been paired with an observed
read, because every fixture in it had `blockCount = 2`.

**One honest non-derivation flagged by the worker:** the delta is
shape-determined rather than count-determined (+2 at counts 1,2,3,8 on n=24 and
n=64; +1 at counts 9,10,14 on both n=128 shapes). The natural reading is a
differing branch through the interior, but the worker declined to assert it as a
checked fact. Handed to the audit as an explicit question.

**A08 reconstruction audit launched** against `6ad4198`, carrying the three
traps this rung produced: the indirect-import `#print axioms` false negative, the
`whnf`-timeout-as-structural-evidence lesson, and the instruction to treat every
enumerated inventory as provisional. Its closing question is the one the whole
rung exists to settle: **does the accepted route now have ANY remaining
uncharged computation whose cost grows with input size?**

**Gate deliberately NOT run at this rung boundary**, contrary to my own standing
rule, and the exception is recorded so it is not mistaken for the lapse that
rule was written to prevent: `gate.ps1` aborts early on the a07-owned
`wordram_axiom_check` red, so it would fail before reaching anything this rung
could have broken and would establish nothing. The full gate runs at the merge
window once R1 lands.

## 2026-07-19 (C05 round 32) — the reachability question, settled with one scope caveat

**The `WordReads.lean` unreachability claim is CONFIRMED, and for a sharper
reason than "no callers".** Those definitions DO have callers, three levels
deep, terminating at exactly two non-proof consumers: `InteriorDirectory.lean:
954` (the `payloadWordsRead` field of the LEGACY concrete directory, where the
accepted trace instead refines to `canonicalRelativeRmmInteriorDirectory` whose
own `payloadWordsRead` derives from the charged execution) and
`InteriorDirectory.lean:1720` (a logical projection whose only consumers are two
theorems). `payloadWordsRead` is additionally a read-set SPECIFICATION field
paired with a width obligation, not a cost-bearing computation, and
`evalGlobalWordTrace` never projects it. The bottom of the accepted chain is
free of `Nat.log2`/`bpSparseLogSpan`: `count` now reaches the charged table only
as a READ INDEX, and `domain` is a structural constant.

**So the answer the rung exists to settle is: on the accepted route, no.** No
uncharged computation whose cost grows with input size survives.

**But one scope caveat, verified by the coordinator and worth stating in the
paper-facing wording.** Surviving uncharged runtime `Nat.log2` DOES exist in
trace-producing code reachable from a SIBLING entry point — the `OfSizeGe`
family (`SuccinctFinalRAM.lean:4486`, `InteriorRAM.lean:574/622/820/868`) and
the `...WithStoreLegacy` mirror (`ConcreteDirectoryRAMStoreParam.lean:3624`).
Coordinator checked where that surface is exposed: `OfSizeGe` appears ONLY in
`RMQ/Headlines/RMQCompatibility.lean:133,137` — the quarantine module the U3
topology work created for retired surfaces — and NOWHERE in `RMQPaper.lean`,
`Headlines/RMQ.lean`, `docs/WHAT_IS_PROVED.md`, or `artifact/CLAIMS.md`. Its
guard is `2 ^ 128 <= shape.size`.

Disposition: properly quarantined, no repair needed. **But the claim must be
worded to its actual scope.** "No uncharged size-dependent computation on the
ACCEPTED ROUTE" is true and provable; "nowhere in the repository" is false, and
a reviewer who greps for `Nat.log2` will find these within minutes. The
charge-policy section must say which, and should name the compatibility family
explicitly rather than leaving it to be discovered. Queued for the E1 M7 doc
work, which already owns that section.

This is the same discipline the campaign applied to the representation-artifact
distinction: state the boundary precisely and name what sits on the other side
of it, rather than making an absolute claim that a five-minute search refutes.

**Minor, queued:** `SparseLevelTable.lean:9` cites `InteriorDirectory.lean:2117`
and `:2131` as the uncharged sites; those line numbers now point at refinement
theorems. The docstring describes the pre-change state and no longer resolves —
the same anchor-drift class this campaign has logged repeatedly.

## 2026-07-19 (C05 round 33) — the scan is dead; space accounting audited; E1 resized

**THE SUSPECTED SCAN IS DEAD FROM THE ACCEPTED ROUTE — settled by the
coordinator, not left open.** E1-R4t flagged that it could not determine whether
`boundedSummaryRangeScanTraceResultAtSegments` (a name suggesting a linear scan)
is reachable from the whole-query root, and correctly said its tracing was
"consistent with dead but not a proof of absence". Resolved: its only two
non-theorem references sit at `ConcreteDirectoryRAM.lean:1205` and `:1232`, both
inside `concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSize
StructuralLEGACY` (def `:1196`) and a `..._total_legacy` theorem (`:1219`). The
accepted route consumes the NON-legacy `...AllSizeStructural` (def `:1188`),
whose body ends before `:1196` and contains no scan reference. **REQ-E1-07's
supersession note is safe**, and the interior has five branches, not six.

Worth noting the pattern: this is the third time a `Legacy`-suffixed sibling has
sat one line-range away from an accepted definition and needed disambiguating —
after the `...AllSizeStructural` near-homonym and the `OfSizeGe` family. The
queued `Legacy` naming repair keeps earning its place.

**Space accounting independently audited at `6ad4198` — clean, with two honest
loosenesses.** All four links present and wired (counted region as two
instantiations folded into the existing `.canonicalClose` source rather than a
new one; capacity; littleO; flatten/erasure). The bridge lemma
`bpSparseLevelWidth_le_square_width` is EXACT — its right-hand side is literally
the pre-tightening definition of the width, confirmed against `78d15c3` — and
its sole hypothesis `0 < domain` is free everywhere, since every domain is
`bound + 2`. The public statement `buildPayload_length` / `overhead_littleO` is
BYTE-IDENTICAL to `f6564ec`: no added hypotheses, no thresholds. Local and
global envelopes are genuinely distinct (cube vs sampled), never conflated.

Two loosenesses to record rather than repair:
1. `527` is a proof-CHECKED literal, not machine-derived, and hugely
   conservative — the component bounds contributing `196n + 113n` cover true
   table sizes of `~log^2 n * log log n` and `~n/log^2 n`. Sound, and in the safe
   direction, but do not describe it as tight.
2. The global side's PROVED envelope is `n/log n`, not the `n/log^2 n` its
   docstring names as the true size. Still `o(n)`, so the littleO conclusion
   stands — but `n/log^2 n` must not be cited as a proved bound.
The audit also independently corroborated the frozen-algebra repin: the commit's
own docstring concedes 76 and 142 "were not frozen at all" before and were
silently tracking the live route.

**E1 resized by a real finding.** The interior's atomic read is NOT
single-chunk in general. Under macro crossing `width <= machineWordBits` gives
one chunk (the 11-per-two-span rate behind the attained 33), but the
within-macro branch has only `width <= 7 * machineWordBits`
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`), and the within-macro
bound's arithmetic is explicitly `26 = 8 + 9 + 9`. **At small shapes one logical
interior read can emit up to eight physical events.** E1-R4t's atom is correct
but insufficient alone and carries the width bounds as explicit hypotheses
rather than discharging them; an eight-capped chunk fold is needed. This is NOT
a return to the pre-B7 obstruction — 8 is a literal cap, using the same
`x - (x - 8)` chain the fringe's 33-cap already uses, so REQ-E1-06(c) survives.

E1-R4t landed the read atom with the validity test performed BY THE MACHINE
(`natLt` on its own index register, branched) rather than by a Lean-level `if`
around the block, so the dead-address path is a charged path — the anti-vacuity
shape REQ-E1-05 asks for.

## 2026-07-19 (C05 round 34) — a coordinator claim corrected; interior block ruling

**A worker refused to write a coordinator-supplied claim into a public-facing
doc because it failed inspection. That refusal was correct and is the headline
of this round.** I gave E1-R4u a "coordinator-verified scope precision" for
`docs/PAPER_MODEL_ADEQUACY.md`. It checked rather than transcribed, found the
wording did not survive, and recorded the discrepancy for adjudication instead
of shipping it. **Never let a coordinator assertion enter a public claim surface
unchecked** — that is exactly how a repository acquires a statement a reviewer
can refute in five minutes.

**Adjudication, verified at source by the coordinator this round.** Part of the
refutation was a misreading of my compressed phrasing, and part was a genuine
correction. The precise, defensible statement is:

- Runtime `bpSparseLogSpan count` — hence `Nat.log2` on a RUNTIME-derived
  argument — survives in trace-producing definitions at
  `InteriorRAM.lean:574, 622, 820, 868`. **CONFIRMED**: `:574` and `:622` both
  read `let span := bpSparseLogSpan count`.
- Those are reachable from
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe`
  (`SuccinctFinalRAM.lean:4486`), which is guarded by `2 ^ 128 <= shape.size`,
  and from the `...WithStoreLegacy` mirror. **`:4486` itself contains no
  `Nat.log2`** — it is the ENTRY POINT, not the site. My phrasing listed both on
  one line and invited exactly the misreading the worker had.
- The `OfSizeGe` family is exposed only through `RMQCompatibility.lean:133,137`
  — coordinator's own grep, unchanged.
- **The `Nat.log2` occurrences in `Headlines/` and `WHAT_IS_PROVED.md:542` are
  NOT counterexamples.** `WHAT_IS_PROVED.md:542` reads "`Nat.log2 bits.length +
  1` word size" — that is the WORD-SIZE definition on a shape-determined
  argument, which the round-7 principle classifies as structural, not as
  uncharged runtime computation. The worker was right that the string appears
  there and wrong that it refutes the point.

So the doc sentence must be about **`Nat.log2` applied to a RUNTIME argument in
an EXECUTED evaluator position**, not about the string `Nat.log2` appearing
anywhere. Written loosely it is refutable by `grep`; written precisely it is
true, provable, and exactly the distinction the representation-artifact
principle already draws. That precision is now the requirement handed forward.

**RULING on the pending interior-block decision.** Two blocks now exist and are
not interchangeable: the 7-instruction atom assuming `width <= wordSize`, and
the 37-instruction fold assuming only `0 < chunkCount <= 8`. **Compose the
interior on the FOLD, uniformly across all five branches.** Reasons: the atom's
hypothesis is exactly the conditional single-chunk fit that holds only under
macro crossing, so using it everywhere would require discharging on the
within-macro branch what is not available there; a per-shape generator choice
would introduce a size-dependent branch that must then be checked against
INV-ALL-SIZE, which forbids size dispatch on the public route — a real risk for
a marginal instruction saving; and one block means one layout for the whole
interior, which is cheaper to compose and far cheaper to audit. Retain the atom
as a proven component; it is not wasted, and the fold's cap being
MACHINE-ENFORCED (`chunkCount - (chunkCount - 8)` computed at runtime) keeps the
no-size-dispatch property trivially true.

**Two engineering notes worth preserving.** The fold's two-loop shape was FORCED,
not chosen: the ISA has `mulConst`/`divConst` but no register-by-register
multiply, so the route's little-endian `2^(j*wordSize) * chunk j` cannot be
formed, only Horner's big-endian accumulation — hence an ascending read loop
matching the route's receipt order plus a read-free digit reversal. Reading
descending would have collapsed it to one loop, and the worker rejected that
because it would trade a read-free loop for a wrong trace order, "precisely B7's
failure class". And it deliberately gave `interiorChunkCount_le_eight` NO
`0 < wordSize` hypothesis because it does not need one, noting that a decorative
hypothesis "would silently owe it to every consumer" — the same discipline that
kept `FringeArmUntouched` an exact union rather than an under-approximation.

**New M6 data point:** on the fold, paths 2 and 3 agree on BOTH modeled steps
(52) and returned value (0), and are separated only by the read log. So on that
block neither value checking nor step counting has any power — only
event-by-event receipt diffing does. Three discriminators, and the block that
needs each of them is now witnessed.

## 2026-07-19 (C05 round 35) — standing decision authority recorded

**User authorization (stepping away):** drive E1 to completion and resolve
blockers autonomously, without waiting for input on design decisions.

**The decision rule, restated in the user's own framing:** the goal is the
strongest version of the RMQ spoke with "reviewers have to spend brainpower
auditing the justifications as opposed to pattern matching against precedent"
MINIMIZED. So where options differ, choose whichever yields the most
UNIMPEACHABLE result — the one a reviewer recognises from the literature rather
than has to audit as a bespoke construction. Cost and session count are
secondary.

This is now settled preference rather than a per-case question: the user has
twice chosen the more expensive precedent-matching route when offered a cheaper
one (Option B over Option A at the campaign's start; the charged sparse-level
fix over an `msb` primitive or a weakened bound), and has never preferred the
cheaper option.

**Precedents this rule has already produced, to keep autonomous decisions
consistent with the ones the user made personally:**
- tables over primitives — four-Russians lookup is the literature's move; a
  declared unit-cost primitive is exactly the precedent-free justification being
  minimised;
- charge it rather than assume it — never add an instruction that makes an
  uncharged computation free, never weaken a bound to accommodate one;
- never mint a historical constant for a value that never described a real route
  (a staging artifact is a fiction; redo the migration instead);
- prove, do not sample — a table of sizes is not an all-size proof, and
  hypotheses must be the route's own rather than a size threshold introduced for
  convenience, since size dispatch on the public route is forbidden;
- observation over argument — a row that exists to convert an argument into an
  observation must not be closed with a second argument;
- one layout over per-shape dispatch when the alternative introduces a
  size-dependent branch;
- state claims to their actual scope, naming what sits on the other side of the
  boundary rather than making an absolute a reviewer can refute by grep.

**Still escalated, not decided alone:** removing public surface (B5b alias
consolidation, compatibility pruning), merging to `main`, recording formal
ACCEPTED, and anything that would weaken a frozen acceptance row. Those are
ownership decisions rather than engineering ones, and the disclosed-fallback
constraint on this runtime bars the last two regardless.

Recorded in coordinator memory as well, so the authority and its precedents
survive context compaction and any handoff.

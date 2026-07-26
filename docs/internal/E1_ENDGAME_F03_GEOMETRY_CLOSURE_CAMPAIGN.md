# EG-CP-F03 geometry-closure campaign — coordinator report

Coordinator: C06 (Claude runtime). Date: 2026-07-26.
Governed base: `d09bed78185d2b13c36a29b018bb9544176a714c` (`origin/main`).
Row under study: `EG-CP-F03-GEOMETRY-CLOSURE`,
`docs/internal/RMQ_ENDGAME_ROADMAP.md:374`, front-loaded within Stage F by the
Day-0 amendment at `:384`.

**This record accepts no theorem, authorizes no merge, and makes no public
claim.** It is the front-loaded research campaign that Stage F's own schedule
places *before* the frozen implementation prompt, per `WDD-20260725-008`.

---

## 1. Outcome

| | |
|---|---|
| **Substance** | `F03_CLOSABLE_PENDING_PROOF`. No route-controlling value was established to be unreconstructable from the allowed inputs. No `X` row was found anywhere in the classified surface. |
| **Process** | **F03 is NOT closed, and this campaign does not meet the row's own minimum-evidence clause.** |
| **Obstruction** | **None established.** Per the roadmap's `CHECKED_OBSTRUCTION` rule (`:406-419`), nothing here qualifies: no value was shown unreconstructable over the frozen objects and quantifiers. |

The row demands an *"exhaustive typed inventory for every current logical-read
source **and universal consumers**, not representative rows."* This campaign
delivered a source-side inventory and a consumer-side branch census, but it did
**not** define or produce a universal-consumer inventory, did **not** classify
controller leaf L2, and landed **no theorem in the repository**. Those are
recorded in §5 as the residual, not glossed.

---

## 2. What is established

### 2.1 The content channel is closed (the exhaustiveness linchpin)

`Cartesian.CartesianShape` (`RMQ/Core/Shape.lean:21`) is an inductive type, so
executable code can observe it only through its eliminators. Over the
**value-only, theorem-skipping transitive closure** of
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore`
(`RMQ/Core/SuccinctFinalStoreParam.lean:2418`) — **917 constants**, reproduced
independently by four agents, stable at 1031 under a value+type
over-approximation and 1013 from the public `queryTraceResultWithStore` — the
eliminator subgraph closes by direct-referrer analysis:

- `CartesianShape.rec` is referenced only by `casesOn`, `below`, `brecOn`;
- `casesOn` only by `reprCartesianShape.match_1`;
- `below`, `brecOn`, `match_1` only by `bpCode` and `size`.

Therefore **`bpCode` and `size` are the complete content channel**, and since
`bpCode_length` (`RMQ/Core/Shape.lean:51`) gives
`shape.bpCode.length = 2 * shape.size`, *length* is size-only and only
*contents* are at issue.

Supporting checks, all executed: `CartesianShape` is not a structure, so
projection/eta leakage is impossible; the closure buckets as def 596 /
theorem 115 / rec 19 / ctor 108 / induct 79 with **axiom 0, opaque 0, quot 0,
missing 0**, so the traversal cannot have truncated silently; `sorryAx`,
`Classical.choice` and `DecidableEq CartesianShape` are all absent from the core
— the controller never compares shapes.

One correction to the coordinator's original framing: `size` and `bpCode` are
*not* the module's only observers — `rootOffset?`, `representative`, `fullCode`,
`queryOffset?`, `decodeFullCode?` and the derived `DecidableEq` all eliminate
shapes. Each was probed individually and **none is in the computational core**,
which is the quantifier that matters.

### 2.2 The consumer-side census

A **642-site** branch/divisor census over the same 917-constant core — ite 38,
dite 8, cond 1, matcher 84, recursor 430, decide 5, div 51, mod 16, log2 9, a
**total count, not a sample** — yields:

- exactly **three** shape-dependent deciders, all size-only:
  `Nat.log2 shape.size`, `shape.size / base shape`, `Nat.log2 (base shape)`;
- **zero** shape-dependent modulus;
- exactly **one** shape-dependent divisor: `/ (Nat.log2 shape.size + 1)`;
- exactly **three** content-dependent `Bool`-returning constants:
  `GenericSelect.superIsLong` (`RMQ/Core/GenericSelect/Slots.lean:103`),
  `localIsSparseException` (`:859-861`), `compactLocalEntryIsLive`
  (`RMQ/Core/GenericSelect/Entries.lean:47`). The latter two are
  `!superIsLong && …`, so **the frontier collapses to one predicate**.

### 2.3 Mechanism results (checked in scratchpad, not in-tree)

- **The interior cone is content-blind by construction.**
  `machineReadComputationAt`
  (`RMQ/Core/SuccinctSpace/MachineChunkedTableProgram.lean:343-353`) binds its
  table argument as `_table` — *unused* — so table contents reach neither the
  issued addresses nor the returned value; only `entries.length`, `width`,
  `wordSize`, `base`, `deadAddress`, `i` can. It is the **sole read primitive**
  in `InteriorDirectory`. Hence `bpExcessAt` and the interior family are class
  **B**, by checked mechanism rather than assumption.
- **`payload_length_eq` is a *field* of `FixedWidthNatTable`**
  (`RMQ/Core/.../Tables.lean:26`), so content cannot influence payload length for
  any inhabitant. This is the structural root of the F3/F4 size-only result.
- **`occurrenceCount bpCode true = size`** and the `false` counterpart, via the
  repo's own `bpCode_rankTrue_full` (`RangeSummary.lean:62`). The guard
  `idx < occurrenceCount bits target` is therefore `idx < n` — size-only.
- **Exact geometry, by `rfl` onto Nat-only mirrors**: summary base
  `= Nat.log2 n + 1`; blockCountRaw `= n / base`; and the cell width
  `w(n) = machineWordBits (2n) = Nat.log2 (2n) + 1`
  (`RMQ/Core/SuccinctFinal.lean:767-769`), which serves **both** rank divisors
  since `wordSize` and `blocksPerSuper` are `rfl`-equal.

### 2.4 The differential evidence, with its ceiling stated

Roughly 900,000 same-size full-transcript comparisons across six independent
refuter teams produced **zero divergences**, with anti-vacuity controls that
fired on cue (deliberately mis-specified controls diverged 33/38/76 times; the
footprint was shown to vary with endpoints, with probe replies, and with `n`).

**This evidence has a hard ceiling and must never be reported as coverage.**
Measured regime walls:

| gate | first live at |
|---|---|
| segment-20 (interior) reads > 0 | n = 10 |
| summary-table active flip | n = 512 (**build-only**; verified *not* on the query path) |
| interior ready | n = 1000 |
| interior macro-crossing arms B3/B4/B5 realizable | n ≈ 3457 |
| `superIsLong` firing no longer excluded | n ≈ 13,276 |

Largest completed whole-query cross-shape grid: **n = 31**. No evaluation in this
campaign crossed the third wall. Coverage past it exists only by proof.

---

## 3. Corrections to the coordinator's own instrument

Recorded because the coordinator built the instrument and must not be its only
reviewer.

1. **The 6-row `bpCode` table is a source list, not an inventory.** It was
   refuted twice, independently, by execution:
   - *False-clean mode.* "Every `bpCode` occurrence sits under `List.length`,
     therefore size-only" is a per-constant **syntactic** test read as a **taint**
     claim, and the inference is invalid. Canonical witness:
     `bpBlockArgMinPrefixPosFrom` (`RangeSummary.lean:419-430`) scored clean —
     its only `bpCode` is `shape.bpCode.length` — while line 426 branches on
     `bpExcessAt shape` and returns a position. **10 of the 19 rows labelled
     "derivable from n" are transitively content-dependent.**
   - *Invisibility.* **39 content-dependent constants in the core appear in
     neither list** (`bpRangeArgMinBlock`, `bpBetterArgMinBlock`,
     `bpGlobalSparseCellBlock`, `bpLocalSparseCellOffset`,
     `bpBlockArgMinLocalOffset`, …), and **controller leaf L2 is structurally
     invisible** to it: `concreteBPNativeLCACloseGlobalWordTraceResultAllSize\
StructuralWithStore` never references `bpCode`. The true content-dependent set
     is **55 constants**; the campaign classified **6**.

   The exhaustiveness that survives is the two-level argument of §2.1 + §2.2,
   not the table.
2. **The coordinator's "`superIsLong` is settled" framing was wrong.** The
   arithmetic result — `superIsLong` is identically false while
   `m ≤ superLongSpan m = wordBits(m)³·ell(m)`, first firing at length 16384 —
   is a **crossover, not a ceiling**. `superSpan` (`Slots.lean:97-100`) is a
   genuine content-dependent select difference and `superLongSpan`
   (`RMQ/Core/GenericSelect/Params.lean:31`) is polylog, so the predicate is live
   for every larger `n` — precisely the asymptotic regime the packed target
   claims. The structural observation that the leaf probes segments 9/10/11
   (`longFlagRankData`) and 12 (`longSuperRelativeTable`) on every execution
   remains true and is good class-P evidence, but it is **not a theorem**.
3. **Probe-geometry base is 17, not 6.** `concreteBPNativeRankCloseTraceSegmentBase := 17`
   (`Segments.lean:48`); segments 17/18/19/21, with base+3 = 20 unused. Verdicts
   are unaffected (the size-only result is base-universal), but anything mapping
   logical segments to physical cells would have been laid out against the wrong
   segments.
4. **F1's single letter "S" understates it.** The three fixed reads at base+0/+1/+2
   are S; up to eight chunk-table reads at base+4 have addresses computed from the
   reply of the base+2 probe — class **P**. Both benign. Record
   "S on the shape channel, P on the chunk-table selectors."
5. **F2's scope must be fenced.** "L3 is the only direct consumer" holds at the
   store-parametric root and at `queryTraceResultWithStore`, but **not** at
   `SuccinctClassic.queryTraceResult` (closure 1069, three parents, all 17 rank
   accessors reachable). The surfaces are bridged definitionally by
   `queryTraceResultWithStore_globalReadStore`
   (`RMQ/Core/SuccinctRMQClassic.lean:1336-1339`); the row must record the scope
   rather than elide it.

---

## 4. Implied header schema

**K = 1.**

| # | field | expression | width |
|---|---|---|---|
| H1 | `n` | `shape.size` | `w(n) = ⌊log₂ 2n⌋ + 1` bits, one cell |

Everything else the controller needs is derived from H1 by closed arithmetic and
requires no storage: `w(n)`; rank block width `⌊log₂ w²⌋+1`; the super/block
overheads; summary base `⌊log₂ n⌋+1`, blockSize `2·base`, blocksPerSuper `base`,
blockCount `n/base`, relativeWidth `2(⌊log₂ base⌋+1)+3`; the nine interior
component offsets (prefix sums of content-blind word counts); fringe chunk bits.

**Why the select directory needs no field.** Slot counts are driven by a
*popcount*, which for a general bitvector would have to be stored — but
balancedness forces it, and the repo already proves
`falseSelectOccurrenceCount_eq_size` (`SlotBasics.lean:35-38`). This is the one
place a header field would otherwise be mandatory, and an existing theorem
retires it.

**The K = 3 branch is a live architecture decision, not a proof detail.**
`selLongRelative` and `selSparseRelative` are empty in every executable regime
precisely because `superIsLong` never fires there. Both already have `n`-only
budgets in code (`SpanBudgets.lean:1068-1069`, `:540-541`). If F01 pads each to
its budget, K stays 1; if it declines, those two bases become content-dependent
and K = 3. Same root as the T1/T2 obligations below.

---

## 5. Residual — what F03 still requires

### 5.1 Process gaps this campaign did not close

1. **Controller leaf L2 was never classified.** Its top-level route selector —
   `if blockOfClose blockSize leftClose = blockOfClose blockSize rightClose`
   (`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeWiring.lean:494-503`) —
   is literally F03's "branch" and "table selector", and no row covers it. It is
   very likely `S` (`blockSizeRaw` was proved size-only), which is exactly why
   the omission is a *process* failure. **The entire same-block arm**
   (`ChargedSameBlockTrace.lean:55-73`) is absent from the campaign, and it is the
   common case for short ranges and the only case reachable at small `n`.
2. **The inventory was refuted mid-campaign and never rebuilt.** 6 of 55
   content-dependent constants were classified. Nobody ran the one-script check
   that the 39 invisible constants lie inside the six cut lists that isolate
   `bpExcessAt`.
3. **"Universal consumers" was never defined or inventoried.** Half the row's
   stated minimum evidence is absent, and the campaign did not say so.
4. **Probe counting has no row.** Arity was bounded for one leaf only (F1, ≤ 11).
   Observed trace lengths grow with `n` — 32–62 events at n ≤ 8, 99–114 at
   n = 10–20 — and nobody wrote down the controller's probe-count function or
   checked it is `n`-independent. This is the "counted" half of "counted
   cell-probe" and it belongs to F03/F08.
5. **The campaign's best experiment ran only in the vacuous regime.** Running the
   controller with shape `rightSpine n` against the real store built from
   `leftSpine n` returns leftSpine's value *and its entire trace* — the strongest
   possible class-P demonstration. It was run at n = 4, 5, 6, where segment 20
   receives zero reads. Re-running it at n ≥ 1000 is the single most
   verdict-relevant missing execution.

### 5.2 Theorem surface

Nothing below exists in `RMQ/`; a grep for every name returns zero hits. All
compile today in `docs/internal/f03_evidence/` with axioms
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

| tier | content | est. |
|---|---|---|
| **Tier 0** | Port ~40 existing scratchpad theorems (placement, naming, import hygiene, green build). | 4–6 d |
| **T1** | **The decisive residual.** `L1_size_only`: the select leaf consumes `bits` only through `bits.length` and `occurrenceCount bits false` (both already kernel-proved size-only). Sub-obligations: ghost-argument erasure; independence from the entry lists; clamp-length arithmetic in closed `n`-form. **Threshold-free — the only instrument that reaches past the n ≈ 13,276 crossover.** | 6–9 d |
| **T2** | Bounded-regime stopgap: `superSpan bits t s ≤ 2·superStride bits.length + bits.length`, giving `superIsLong = false` below the crossover. Worth landing; **does not discharge the asymptotic claim** and must not be recorded as closing the row. | 2–4 d |
| **T3** | Interior offsets congruence: `a.size = b.size → canonicalRelativeRmmInteriorComponentOffsets a = … b`. | 2–3 d |
| **T4** | **The literal F03 statement** (capstone): for all `a b store l r` with `a.size = b.size`, the ordered read footprint and the output value agree. Mostly congruence plumbing once L1/L2/L3 are done, since `WholeQueryNatExpr` (`RMQ/Core/SuccinctFinalRAM.lean:2963-2971`) is already closed. | 3–5 d |
| **T5** | Segment cardinalities as functions of `bpCode.length` — needed because the packed layout turns `(segment, index)` into `segmentOffset(segment) + index`. | 1–2 d |
| **T6** | Packed rewrite and controller expressivity (arguably F04 scope): `n`-parameterised twins, rewire the evaluator, delete the `shape` parameter; then either extend `WholeQueryNatExpr` with `div`/`log2` or read `w(n)` from H1. | 5–8 d |

**Total 23–37 focused proof-days**, with T1 carrying essentially all schedule
risk. Tier 0 + T3 + T5 (~8–11 d) is a defensible partial landing that makes the
row citable from a commit; **T1 is what actually closes it.**

---

## 6. What would change the verdict

**To `CHECKED_OBSTRUCTION`.** Exhibit two same-size shapes, a store and
endpoints whose footprint or value differ. Given the census, the only place such
a witness can live is the `superIsLong` cone at n ≳ 13,276, where a
span-maximising shape (`node (rightSpine 1) (leftSpine (n-2))`, measured to
attain `superSpan = n + superStride(2n) − 2`) fires the predicate while a
balanced shape of the same size does not. If that divergent value reaches the
select leaf's observable through any channel other than the two already proved
size-only, F03 has a genuine `X` and the packed target needs an architecture
change — most likely a second header field, which would also settle K = 1 vs 3.
**A failed T1 attempt that isolates such a channel *is* the obstruction; a T1
proof that merely will not go through is not.**

**To `F03_CLOSED`.** Land Tier 0 + T1 + T3 + T4 in-tree on a green branch with
`#print axioms` clean and declarations a reviewer can cite by commit. F03 can be
closed **without ever evaluating at n = 13,276** — T1 is threshold-free, which is
why it and not T2 is decisive.

**What would NOT change it.** Another sweep below the crossover; a `rfl` that
blows recursion depth; a run that exceeds the time budget. Per the roadmap's own
rule these are encoding and harness costs. The campaign already produced ~900,000
clean comparisons in that regime and the marginal value of more is zero, because
the regime is provably vacuous on the only live content-dependent branch.
**Further execution below the crossover should not be commissioned.**

---

## 7. Open questions carried forward

1. Does the select leaf consume `bits` through any channel other than
   `bits.length` and `occurrenceCount bits false`? Four independent mechanical
   scans say no and every execution agrees; no theorem says so. **This is T1.**
2. Are `longSuperRelativeEntries` and `sparseDirectory.relativeEntries` (store
   segments 12/16) provably empty for balanced-parenthesis codes, or merely empty
   in the tested range? Same `superIsLong` root; decides K = 1 vs 3.
3. Will F01 pad `selLongRelative`/`selSparseRelative` to their existing `n`-only
   budgets? Architecture decision, not a proof detail.
4. Does the interior macro hierarchy behave as designed? Arms 3 and 4 first
   become realizable at n ≈ 3457 and **have never been executed**. The two-level
   structure the architecture is built around is entirely unexercised.
5. Should the two never-projected `Nat` fields at `SuccinctFinal.lean:531-532` be
   **deleted** rather than proved size-only? Repo-wide grep finds zero
   dot-projections; deletion turns the F3/F4 argument from "size-only in value"
   into "not present", which is strictly more unimpeachable.
6. Is `bpFringeChunkBits m = Nat.log2 m / 8 + 1` defensible? The literal `/8` is
   bespoke against the standard four-Russians `(lg n)/2`. More conservative and
   still `o(n)`, so safe — but it has no stated derivation and will draw a
   question.
7. Adjacent, not F03, and it will be asked: at n = 128 the measured
   access-overhead budget is 2,083,425 bits against 6,594 used. `LittleOLinear`
   is proved, so this is asymptotically sound, but the crossover where the
   structure is genuinely succinct is very far out. Belongs on F01/A03 and
   interacts with the known open overhead question.

---

## 8. Evidence

`docs/internal/f03_evidence/` — 321 files, preserved verbatim from the campaign's
session-scoped working directory so the evidence survives the session.

**Status: UNVETTED working artifacts.** They are not part of any build target,
have not been reviewed declaration-by-declaration by the coordinator, and are not
acceptance evidence. They are preserved because a prior failure mode in this
project was exactly a strong claim with no branch, no commit, and no replay; the
theorem names cited in §5.2 are recoverable from these files, and a porting
worker should start there rather than re-derive.

Coordinator-authored instruments, cited in §2:
`f03_inventory.lean`, `f03_inventory2.lean` (computational core + the syntactic
test whose failure modes §3.1 records), `f03_channels.lean` (eliminator cut),
`f03_regimes.lean` (regime map), `f03_select_leaf.lean`, `f03_lca_leaf.lean`,
`f03_superlong.lean`, `f03_longflag.lean` (crossover and segment evidence), and
`F03_COORDINATOR_FINDINGS.md`.

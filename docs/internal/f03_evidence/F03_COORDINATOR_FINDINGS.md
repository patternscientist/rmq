# F03 coordinator findings — read this before designing any experiment

Produced at commit `d09bed7`. Lean runs from
`C:/Users/poin/.codex/visualizations/2026/07/17/019f6d85-7626-7433-a60b-81f8be29689a/b7r4-main-integration`.

## 1. THE REGIME THRESHOLD — this invalidates all small-n evidence

`canonicalBPRelativeMinMaxArgSummaryTableActive` (a `Prop` with a `Decidable`
instance; use `decide (...)` to print it) evaluates as:

| n | active | summaryBlockSize |
|---|---|---|
| 0 … 384 | **false** | **0** |
| 512 | **true** | 20 |
| 1024 | **true** | 22 |

Measured on left spine, right spine, balanced, and two pseudo-random shapes at
each of n = 0,1,2,3,4,5,6,7,8,12,16,20,24,32,48,64,96,128,192,256,384,512,1024
(`scratchpad/f03_regimes.lean`).

**Consequence: every cross-shape query experiment run below the threshold
exercises only the degenerate arm.** The coordinator's own n=3 result, and any
sweep over n ≤ 8, cannot speak for the summary/interior machinery at all. Do not
cite small-n agreement as evidence for closure without saying this. Run the
treatment at n ≥ 512, with n = 384 as the inactive control.

## 2. EVERY NAMED GEOMETRY VALUE IS SHAPE-INVARIANT AT EQUAL SIZE

Across those same five structurally extreme shapes at every size listed above,
all of the following agreed exactly, with **zero** disagreements:

`summaryBase`, `summaryBlockCountRaw`, `summaryBlockSize`, `summaryBlockCount`,
`summaryBlocksPerSuper`, `rankWordSize`, `rankBlockOverhead`,
`rankSuperOverhead`, `rankBlockWidth`, `fringeChunkBits`, `bpCode.length`,
and the `summaryTableActive` flag.

This includes **F3 `builtRelativeSplitBPCloseRankBlockOverhead`** and
**F4 `builtRelativeSplitBPCloseRankSuperOverhead`**, the two rows the syntactic
instrument flagged as reading `bpCode` CONTENTS with zero occurrences under
`List.length`. They are content-mentioning in SYNTAX but size-only in VALUE.

The reason is visible in the definitions
(`RMQ/Core/SuccinctFinal.lean:813-830`): both are
`(SuccinctRank.canonical*RankSampleTables shape.bpCode …).payload.length` —
they pass the real bits in, but project only the **length** of the resulting
payload, which is (samples × width) and therefore size-derived.

**This is the shape of the residual F03 proof obligation for those rows:** a
lemma that `canonicalSuperRankSampleTables bits w b w' |>.payload.length` and
`canonicalBlockRankSampleTablesOfLocalSpan …|>.payload.length` depend on `bits`
only through `bits.length`. Empirically true; not yet proved.

## 3. EXACT WIDTH FUNCTIONS (needed by EG-CP-F01 / A03)

Fitted to the measured table and confirmed against the definitions:

- `builtRelativeSplitBPCloseRankWordSize shape = SuccinctRank.machineWordBits shape.bpCode.length`
  (`RMQ/Core/SuccinctFinal.lean:767-769`), i.e. **w(n) = ⌊log₂(2n)⌋ + 1**
  (n=512 → 11; n=1024 → 12).
- `canonicalBPRelativeSummaryBase` = **⌊log₂ n⌋ + 1**
  (n=384 → 9; n=512 → 10; n=1024 → 11).

Both are standard log-word geometry, not bespoke.

## 4. THE CANDIDATE F03 UNIVERSAL CONSUMER

One theorem discharges F03's universality requirement and simultaneously
supplies F06's "cross-shape transcript determinism for equal allowed
inputs/probe replies":

```lean
theorem f03_geometry_closure
    (shapeA shapeB : Cartesian.CartesianShape)
    (hsize : shapeA.size = shapeB.size)
    (store : WordRAM.ReadStore) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shapeA store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shapeB store left right
```

If it holds, the controller depends on the semantic shape ONLY through
`shape.size = n`. That is exactly geometry closure, and it would mean the free
semantic-shape argument can be replaced by `n` **without rewriting the route** —
a derivation rather than a rewrite. Treat refuting or supporting this statement
as the highest-value target available.

Note it is stated over `shape.size`, not `bpCode`, and quantifies over ALL
stores and ALL endpoints, including invalid ones.

## 4b. LEAF-LEVEL RESULTS SO FAR (`scratchpad/f03_select_leaf.lean`)

Isolating leaves L1 (select-close) and L3 (rank-close) is far cheaper than the
whole query and targets the highest-risk row directly. Discriminating inputs are
structurally maximal at equal size:

  leftSpine  bpCode = `true^n ++ false^n`  (all opens, then all closes)
  rightSpine bpCode = `(true false)^n`     (perfectly alternating)
  balanced   bpCode = mixed

Result at n = 8, 64, 128, over one address-sensitive shape-free store, at
idx/pos ∈ {0, 1, n/2, n-1}: **leftSpine, rightSpine and balanced produce
identical traces and identical values in every case.** Select traces are 9
events; rank traces 4–7.

This matters because `concreteBPNativeSelectCloseGlobalWordTraceResultWithStore`
passes `GenericSelect.sparseExceptionSelectData shape.bpCode false` as an
explicit VALUE argument (`RMQ/Core/SuccinctFinalStoreParam.lean:645-653`), not a
type index. Classical sparse/dense select directories choose a per-superblock
regime from the actual distribution of set bits, so this was the single most
likely place for a free content input. It has not diverged yet.

**UPDATE — the active regime is now covered for L1 and L3.** Re-run at n = 256
and n = 512 (`scratchpad/f03_sel_n256.lean`, `f03_sel_n512.lean`): leftSpine,
rightSpine and balanced again produced **identical traces and identical values**
in every case. At n = 512 the summary table is ACTIVE. Select traces stayed at
9 events; rank traces 4–5.

So leaves L1 and L3 have now held across maximally different same-size bit
distributions at n = 8, 64, 128, 256, **512**, with zero divergences.

Still untested: leaf **L2**,
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore`, which
drives the relative-RMM interior/summary machinery — precisely what switches on
at the threshold. A run at n = 384 (inactive control) / 512 / 640 is in flight
(`scratchpad/f03_lca_leaf.lean`). Do not call F03 either way before L2 lands.

Also note the contrast between the two leaves:
- L3 rank (`:442-448`) takes `builtRelativeSplitBPCloseRankData shape`, whose
  content occurrence is a **type index** — erased, and so incapable of steering
  an address on its own.
- L1 select (`:645-653`) takes a content-built structure as a **value**. The
  burden of proof is different for the two, and a classification that treats
  them alike is not doing its job.

## 4c. THE SELECT LONG/SPARSE REGIME — SETTLED TWO WAYS
(`scratchpad/f03_superlong.lean`, `scratchpad/f03_longflag.lean`)

After the interior cone was closed by the `_table`-unused mechanism theorem, the
last content-reading branches were the select-layer span predicates
`superIsLong` / `localIsSparseException` / `compactLocalEntryIsLive`.
`superSpan` is a POSITION DIFFERENCE, so unlike `occurrenceCount` it is not
forced by `bits.length`. Two independent lines settle it.

**Line 1 — arithmetic.** `superIsLong bits t s = (superLongSpan bits.length <
superSpan bits t s)`, and a span can never exceed the string length, so the
predicate is IDENTICALLY FALSE — for every content whatsoever — whenever
`m <= superLongSpan m`. Executed scan over `m = 2^0 … 2^25`:

    superLongSpan(m) = wordBits(m)^3 * ell(m);  m=2^13: 10976 > 8192  cannot fire
                                                m=2^14: 13500 < 16384 CAN fire

**First length at which `superIsLong` can fire at all: m = 16384, i.e. n = 8192
nodes.** Consequence: EVERY cross-shape experiment below n = 8192 — mine at
n ≤ 512, the campaign's 625-shape sweep at n ≤ 7, the cliff family at n ≤ 256 —
is VACUOUS on this row. State that; do not let it pass as coverage.

**Line 2 — structural, and the one that actually decides it.** The select leaf
reads segments **9, 10, 11** (`selectData.longFlagRankData`) and **12**
(`selectData.longSuperRelativeTable`) on EVERY execution, at every size, for
every shape family. Observed addresses at n=256 (identical for leftSpine,
rightSpine and cliff):

    [(1,1),(2,1),(3,1),(4,1),(9,0),(10,0),(11,0),(21,22),(12,250100)]

Those segments exist precisely to store the long/sparse decision and its
exception data (`RMQ/Core/BPNavigationRAM.lean:847-862`). So the regime is
learned by PROBING, not computed from free bits: `superIsLong` in the closure is
table CONSTRUCTION (**B**), and the query-time regime is a probe reply (**P**).

**Anti-vacuity for the cliff family.** `node (leftSpine K) (rightSpine M)` has
bpCode `true^(K+1) false^(K+1) (true false)^M` — opens packed, then a run of
closes with no opens. It genuinely moves the spans: at n=256, maxSuperSpan(true)
is 100 for leftSpine but 299 for cliff. So content really does vary the spans,
and the transcripts still agree: **80 select-leaf comparisons across
leftSpine / rightSpine / three cliff variants at n = 16…256, zero divergences.**

## 5. CONTENT-CHANNEL COMPLETENESS (the exhaustiveness linchpin)

In the 917-constant computational closure (values only, theorems skipped), the
only constants referencing any `CartesianShape` eliminator besides `bpCode` and
`size` themselves are `reprCartesianShape.match_1`, `casesOn`, `below`, and
`brecOn` — generic infrastructure and the `Repr` instance. No project geometry
function destructures the tree. Notably **no `DecidableEq CartesianShape`
instance is in the core**, so the controller never compares shapes.

Scripts: `f03_inventory.lean`, `f03_inventory2.lean`, `f03_channels.lean`.
This argument is what makes the 6-row frontier exhaustive rather than
representative. Attack it before relying on it.

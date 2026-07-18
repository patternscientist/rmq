# B6 Worklog — charged same-block LCA leg

Worker B6-01, branch `claude/b1-b2-charged-fringe-tables`, base
`c0c32c4a0ba63fda2246806f0775ebe5b61d928d`.
Mission: close the last event-silent computation on the accepted RMQ route,
the same-block LCA branch (`localBPSameBlockCloseSeededCosted`,
`LocalBPDecoder.lean:1128-1143`, `cost := 4` over an unbounded per-position
scan). Frozen contract: `docs/internal/B6_SAMEBLOCK_ACCEPTANCE_MATRIX.md`.

## M0 — survey (read-only), matrix freeze

Baseline `lake build RMQ RMQPaper RMQExamples` at `c0c32c4`: exit 0.

### Confirmed at source

The finding is real and reachable. `.lcaClose` dispatches to
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
(`SuccinctFinalRAM.lean:2330`, from `WholeQueryInstr.evalGlobalWordTrace`
`:3185-3191`), which calls
`lcaCloseTraceResultWithRankSeedAllSizeStructural`
(`ChargedFringeWiring.lean:49`). That dispatcher branches on same-block vs
cross-block (`:57-63`): the cross-block arm is the charged B2 consumer, the
same-block arm is `localBPSameBlockCloseDecodedTraceResultWithRankSeed`
(`ConcreteDirectoryRAM.lean:1559`), still event-silent.

### Three structural facts that make this a substitution, not research

1. **The window is the same object.**
   `localBPWindowBits_eq_flatten_localBPBlockWordsRead`
   (`LocalBPDecoder.lean:228`) proves
   `localBPWindowBits shape blockSize close =
   flattenPayloadWords (localBPBlockWordsRead shape blockSize close)`.
   The same-block leaf's `window` is the right-hand side; B2's fringe leaves
   use the left-hand side. So the SAME segment-21 chunk table applies with
   no new table, no new segment, and no store/erasure/capacity/o(n) work.
2. **The value equality is already proved.**
   `bpFringeChunkFoldCosted_global_eq_localBPSeeded`
   (`ChargedFringeChunks.lean:1694`) is generic in `window/seed/base/
   start/count`; its `hlen` side condition is discharged all-size by
   `four_machineWordBits_le_32_mul_bpFringeChunkBits` (`:49`). The
   same-block leaf computes exactly the pair that theorem produces, then
   applies `bpCandidateClose?`.
3. **The dispatcher already has the extension slot.**
   `lcaCloseTraceResultWithRankSeedAllSizeStructural` carries an unused
   `(_sameBlockSegment : Nat)` parameter (`ChargedFringeWiring.lean:54`).
   Because the same-block chunk reads go to the SAME table as the fringe
   reads, they can be charged at `fringeSegment`, leaving the dispatcher
   signature byte-identical — strictly stronger name/statement identity
   preservation than B2's own M9 achieved (B2 added a parameter).

### Load-bearing arithmetic finding: the route literal does NOT move

The delegation prompt predicts `queryCost = 207` moves "to at most 240".
Read at source, the close/LCA principled cap is a MAX over the two branches,
not a sum:

- `bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost
  = 2*rankCost + 2*37 + 30` (`ChargedFringeSubstitution.lean:28`, with
  `bpChunkedEndpointFringeChargedTraceCost = 37` at `:25` and
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 30` at
  `InteriorDirectory.lean:1783`). At `rankCost = 11` that is `126`.
- The charged same-block arm will cost `rankCost + 4 + 33 = rankCost + 37`
  (one rank seed, four window words, at most 33 chunk reads) — `48` at
  `rankCost = 11`.
- `canonicalLcaCloseCostedWithRankSeed_cost_le_principled`
  (`ChargedFringeWiring.lean:150`) discharges the same-block arm at
  `:163-179` with `hcap : rankCost + 4 <= 2*rankCost + 104` by `omega`.
  After the swap the same obligation is `rankCost + 37 <= 2*rankCost + 104`,
  also `omega`-closed for every `rankCost`.

So no algebra field changes, and the derived route literal is expected to
re-derive to `207` unchanged. The prompt's authorization to move the literal
is expected to go UNUSED — strictly less public-surface disruption than
authorized. This is recorded in REQ-B6-05 with the derivation outcome
treated as authoritative per the prompt's own "the derived value wins" rule.
No historical constant is minted unless the derivation actually moves.

### Reuse cost of segment 21 (verified)

The fringe table is a pure function of `shape.bpCode.length`
(`bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)`), provisioned
at `Segments.lean:79` (`concreteBPNativeFringeChunkTraceSegment := 21`),
store arm `:224-228`, exactness lemma
`concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable` (`:247`).
A second consumer of the same table needs NO new store, payload, overhead,
capacity, erasure, or reviewer-source work; the existing
`SuccinctFinalStoreParam.lean:1221` `fringeChunkTable` agreement field also
covers it. The only new obligations are a `ReviewerProducerReadPath`
constructor for the same-block leaf (mirroring `lcaFringeLeft`/
`lcaFringeRight`, `SuccinctFinalRAM.lean:5309`), its `_trace_forall` /
`_matchesReadStore` / `_no_syntheticCostOnlyPrimitive` suite, and a W19
successful-occurrence witness on a SAME-BLOCK execution.

### Reusable generic layer (no cloning needed)

`ChargedFringeTrace.lean:174/:185` `bpFringeChunkFoldTraceResultAtSegment`
(`WithStore`) are polymorphic in both `table` and `fringeSegment`, with the
full obligation suite at `:194-427` (`_toCosted`, `_eq_of_agree`,
`_store_parametric`, `_matchesReadStore`, `_trace_forall`,
`_no_syntheticCostOnlyPrimitive`, `_head_mem`). The B3 select mirror at
segment 22 reused this layer rather than cloning it; that is the template.

### Milestone plan

- M1 Costed leaf: `bpChunkedSameBlockCloseSeededCosted` + `_cost_le` (<= 37)
  + `_value_eq` against `localBPSameBlockCloseSeededCosted`; decoded and
  with-rank-seed twins + their cost/value lemmas.
- M2 Trace layer: `...TraceResultAtSegment(WithStore)` on the generic fold,
  full obligation suite; decoded twins.
- M3 Atomic swap: dispatcher arms in `ChargedFringeWiring.lean` (signature
  unchanged), route exactness and cost re-proved.
- M4 Provenance/adequacy regeneration + W19 same-block witness.
- M5 Literal re-derivation (expected: confirms 207), vocabulary theorem
  re-established, charge-policy doc repair, verification battery.

## Ledger

| # | Commit | Content | `lake build` |
| --- | --- | --- | --- |
| M0 | `6775e22` | frozen B6 matrix + worklog; no Lean changes | baseline `RMQ RMQPaper RMQExamples` exit 0 at `c0c32c4` |
| M1 | `194c4e6` | `ChargedSameBlockChunks.lean`: charged Costed same-block leaf, literal cost bound, value equivalence, decoded rank-seed twins | `lake build RMQ` exit 0, 88.5 s |
| M2 | `285c43e` | `ChargedSameBlockTrace.lean`: seeded + decoded trace twins, full obligation suite, WithStore layer | `lake build RMQ` exit 0, 82.2 s |
| M3a | (this commit) | `ChargedSameBlockSubstitution.lean`: query-side geometry discharge, exact-value substitution at the accepted same-block call site | `lake build RMQ` exit 0, 87.3 s |

## M1 — charged same-block leaf at the Costed layer

New module
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedSameBlockChunks.lean`
(imported by `ChargedFringeWiring.lean` so it is live in the library build,
following B2's additive-then-atomic-swap precedent; the swap is the
immediate successor milestone and this module is NOT yet consumed by the
route).

Delivered:

- `bpChunkedSameBlockCloseSeededCosted` — four charged window-word reads
  then at most 33 charged `bpFringeChunkTable` reads through the B2 fold,
  then the accepted `bpCandidateClose?` projection. The per-position scan is
  absent from the charged path; the recursion is `bpFringeChunkFoldCostedFrom`
  on the chunk counter only.
- `bpChunkedSameBlockCloseSeededCosted_cost_le : ... .cost <= 37` — literal,
  no size hypothesis, no readiness guard, no shape side condition.
- `bpChunkedSameBlockCloseSeededCosted_value_eq` — `.value` equals
  `(localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
  seed).value`, universally quantified over shape/blockSize/leftClose/
  rightClose/seed under exactly three hypotheses (`hvalid`, `hstart`,
  `hcov`); `hcount` is discharged internally since
  `0 < rightClose - leftClose + 1` always holds. Proof reuses
  `bpFringeChunkFoldCosted_global_eq_localBPSeeded` verbatim and closes the
  window mismatch with
  `← localBPWindowBits_eq_flatten_localBPBlockWordsRead`.
- `bpChunkedSameBlockCloseDecodedCostedWithRankSeed` + `_cost_le`
  (`<= rankCost + 37`) + `_value_eq`, threading
  `localBPSeedFromRankCloseCosted` exactly as the accepted decoded twin
  does (no seed reconstruction from window bits, so
  `localBPWindowBits_alone_does_not_determine_base_excess` is untouched).

No new table, segment, store region, payload component, or overhead term was
introduced, so REQ-B6-04's store/erasure/capacity/o(n) obligations reduce to
provenance only, as predicted at M0.

## M2 — charged same-block leg at the trace layer

New module
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedSameBlockTrace.lean`
(namespace `RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory`, matching
the accepted trace twins).  `ChargedFringeWiring.lean` now imports it, so
both new modules are live in the library build.

Seeded layer, mirroring `bpChunkedLeft/RightFringeCandidateSeededTrace-
ResultAtSegment` exactly:

- `bpChunkedSameBlockCloseSeededTraceResultAtSegment(WithStore)` — the four
  accepted window-word reads at segment `0`, then one chunk-table read per
  visited chunk at `fringeSegment`, then `bpCandidateClose?`.
- `_refines : toCosted = bpChunkedSameBlockCloseSeededCosted`.
- `_trace_forall` — every event is a window read or a
  `readWord fringeSegment address (table.store.words[address]?)` at an
  in-range slot (`address < bpFringeChunkRowCount ...`).
- `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`, and the WithStore
  `_eq_of_agree`, `_store_parametric`, `_matchesReadStore`,
  `_no_syntheticCostOnlyPrimitive`.

Decoded layer:

- `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment(WithStore)`
  threading `localBPSeedFromRankCloseTraceResult` exactly as the accepted
  decoded twin does, with `_refines`, `_eq_of_agree`, `_store_parametric`.

The reads go to the SAME `bpFringeChunkTable` at the SAME segment the B2
cross-block fringe already reads, so no new store region, payload component,
capacity bound, or erasure obligation arises; the existing
`SuccinctFinalStoreParam` `fringeChunkTable` agreement field already covers
the supplied-store layer.

`lake build RMQ` exit 0, 82.2 s.  Hygiene scan on the new module: no hits.

Still NOT consumed by the route.  M3 (the atomic dispatcher swap) is next.

## M3a — exact-value substitution at the accepted same-block call site

New module `ChargedSameBlockSubstitution.lean` (namespace
`RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory`, matching
`ChargedFringeSubstitution.lean`).

`bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq_of_query`
discharges the three geometry hypotheses of the M1 value lemma from the
accepted route's own query-side facts (`hrankExact`, `hlen`, `hbound`,
`hleft`, `hright`, `hsame`), giving

```
(bpChunkedSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
    (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose rightClose).value =
  (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
    (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose rightClose).value
```

The discharge is much shorter than B2's cross-block one because the
same-block leaf shares its window base and range start with the LEFT fringe
leaf, so `hvalid` and `hstart` are the left-fringe facts verbatim.

One genuine difference from the cross-block case, worth recording because it
is the only place the same-block geometry is NOT a specialization of B2's:
B2 proves the whole block lies inside the BP code
(`hleftEndLen`) using STRICTNESS `blockOfClose leftClose < blockOfClose
rightClose` from `hcross`, then `blockOfClose leftClose + 1 <= blockCount`.
That strictness is unavailable in the same-block case, and the fact is
genuinely false there: the same-block case admits the FINAL block, whose end
may exceed `shape.bpCode.length`. The repair is to cover each close position
separately (`localBPWindowBits_covers_of_le_width` at `pos := leftClose + 1`
and at `pos := rightClose + 1`) rather than covering the whole block; both
positions are `< shape.bpCode.length` by `bpCloseOfInorder?_bounds`, and both
are `< blockStart + blockSize <= base + 4W` by `hsame` and
`localBPWindow_block_end_le_four_words`. `hcov` then follows by `omega` from
the two covers, which also handles the `rightClose < leftClose` Nat-truncation
case correctly.

`lake build RMQ` exit 0, 87.3 s. Hygiene scan on the new module: no hits.

## RESUME INVENTORY (verified this session; B6 is INCOMPLETE at `b77f385`)

Everything below was read at source in this worktree. Nothing here is
implemented. The library is green at every committed point; the accepted
route is NOT yet swapped, so the same-block branch is still event-silent and
the mission target is NOT delivered.

### What is landed and green

| Module | Contents |
| --- | --- |
| `ChargedSameBlockChunks.lean` | `bpChunkedSameBlockCloseSeededCosted`, `_cost_le` (<= 37), `_value_eq`; decoded twins `bpChunkedSameBlockCloseDecodedCostedWithRankSeed`, `_cost_le` (<= rankCost + 37), `_value_eq` |
| `ChargedSameBlockTrace.lean` | `bpChunkedSameBlockCloseSeededTraceResultAtSegment(WithStore)` with `_refines`, `_trace_forall`, `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`, and WithStore `_eq_of_agree`, `_store_parametric`, `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`; decoded `...DecodedTraceResultWithRankSeedAtSegment(WithStore)` with `_refines`, `_eq_of_agree`, `_store_parametric` |
| `ChargedSameBlockSubstitution.lean` | `bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq_of_query` (query-side geometry discharge) |

### STEP 1 - five missing decoded-level obligation lemmas

Add to `ChargedSameBlockTrace.lean`. Each is the decoded (rank-seed)
analogue of a seeded lemma already present in that file. The proof shape to
copy is `ChargedFringeTrace.lean:1051`
(`bpChunkedCrossBlockClose..._trace_forall`): `unfold` then
`apply WordRAM.TraceResult.bind_trace_forall`, with the seed case
discharged by `localBPSeedFromRankCloseTraceResult_trace_forall`
(`ChargedFringeTrace.lean:1094`).

1. `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment_trace_forall`
2. `..._matchesReadStore`
3. `..._no_syntheticCostOnlyPrimitive`
4. `...AtSegmentWithStore_matchesReadStore`
5. `...AtSegmentWithStore_no_syntheticCostOnlyPrimitive`

### STEP 2 - the atomic swap in `ChargedFringeWiring.lean` (12 sites)

Line numbers exact at `b77f385`. The dispatcher signature does NOT change:
the same-block chunk reads go to the SAME table at `fringeSegment`, so the
existing unused `(_sameBlockSegment : Nat)` parameter (`:55`) stays unused
and every name and statement identity is preserved byte-for-byte. This is
strictly stronger identity preservation than B2's own M9 achieved.

| Line | Current | Replace with |
| --- | --- | --- |
| 39 | `localBPSameBlockCloseDecodedCostedWithRankSeed` | `bpChunkedSameBlockCloseDecodedCostedWithRankSeed` |
| 60 | `localBPSameBlockCloseDecodedTraceResultWithRankSeed` | `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment shape rankCloseTrace fringeSegment blockSize leftClose rightClose` |
| 431 | `localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore` | the `...AtSegmentWithStore` twin |
| 88 | `..._refines` | `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment_refines` |
| 117 | `..._cost_le` (`hlocal` gives `rankCost + 4`) | `bpChunkedSameBlockCloseDecodedCostedWithRankSeed_cost_le`; the `hcap` at `:120-124` becomes `rankCost + 37 <= canonicalCompactBPCloseQueryCostWithRankSeed rankCost`, still closed by `omega` after the same unfolds |
| 166 | `..._cost_le` (`hlocal` gives `rankCost + 4`) | same swap; the `hcap` at `:169-174` becomes `rankCost + 37 <= 2*rankCost + 2*37 + 30`, `omega`-closed for every `rankCost` |
| 228 | `..._exact_of_query_same_block` | keep the accepted theorem and transport it across the M3a substitution, exactly as the cross-block case does at `:250-269`: `rw [hvalue]; exact haccepted` |
| 319 | `..._trace_forall` | STEP 1 lemma 1 |
| 474 | `...WithStore_eq_of_agree` | `...AtSegmentWithStore_eq_of_agree` (landed) |
| 549 | `...WithStore_store_parametric` | `...AtSegmentWithStore_store_parametric` (landed) |
| 580 | `...WithStore_matchesReadStore` | STEP 1 lemma 4 |
| 612 | `...WithStore_no_syntheticCostOnlyPrimitive` | STEP 1 lemma 5 |

`_no_syntheticCostOnlyPrimitive` at `:328` and `_matchesReadStore` at `:364`
also have same-block cases reached through the `:319` `_trace_forall`; check
both after the swap.

### STEP 3 - downstream regeneration (largest remaining piece)

The same-block branch begins emitting `readWord 21 _ _` events, which the
whole-query inductions do not currently expect. Expect work at:

- `SuccinctFinalRAM.lean:2330`
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural` - already
  passes `concreteBPNativeFringeChunkTraceSegment` (21); no signature change.
- `SuccinctFinalRAM.lean:5309` `ReviewerProducerReadPath` - add an
  `lcaSameBlock` constructor mirroring `lcaFringeLeft` / `lcaFringeRight`,
  carrying the event's membership in the same-block candidate component
  trace at the fringe segment; then regenerate the producer and occurrence
  provenance packets and `lcaCloseGlobalWordTraceResult_producerReadPath`.
- every `_trace_forall` induction over the whole-query trace that currently
  discharges the same-block branch as read-free.
- `SuccinctFinalModelAdequacy.lean` - provenance fields.
  `canonical_segments_complete` is UNCHANGED (still `< 22`) because no new
  segment is introduced.
- W19: add a SAME-BLOCK successful-occurrence witness in
  `ReviewerReachabilitySmall.lean`. The existing witness is the
  increasing-16 CROSS-block execution and does not cover this arm. This is
  the one W19 obligation the segment-21 reuse does not inherit for free.

NO store, payload, overhead, capacity, erasure, or `ReviewerSource` work is
required: the table, its segment, its store arm (`Segments.lean:224-228`),
its exactness lemma (`:247`), and the `SuccinctFinalStoreParam.lean:1221`
agreement field are all reused unchanged.

### STEP 4 - literal, vocabulary theorem, docs

- Re-derive `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
  by `rfl`. EXPECTED: `207`, unchanged, because no algebra field changes and
  the branch cap absorbs the new reads (M0 arithmetic, re-verified at M3a).
  If it re-derives to 207: mint NO historical constant, leave
  `SuccinctClassic.queryCost_eq`, the cost harness, the validation and
  examples guards, and the `SumLe207` topology anchor untouched, and record
  in REQ-B6-05 that the authorization to move the literal went unused. If it
  moves, follow the 142-freezing pattern at `SuccinctFinalRAM.lean:8729-8752`
  and update all 27 Lean sites plus `scripts/paper_topology_lint.ps1:354`
  and `scripts/headline_axiom_check.lean:97`.
- Re-establish
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
  over the amended route. The new events are `readWord`, so it should
  survive, but it must be re-proved over the amended object, not inherited.
- Repair `docs/PAPER_MODEL_ADEQUACY.md:139-153`. The sentence "after B2/B3
  every uncharged step is a BOUNDED-PER-STEP register computation ... not an
  unbounded scan" is FALSE at `b77f385` and stays false until STEP 2 lands.
  It becomes true once the same-block arm is swapped; the repaired text
  should name the same-block leg and its 33-cap explicitly.

### Honest status

REQ-B6-01, REQ-B6-02 and REQ-B6-03 are closed as COMPONENT claims (charged
leaf with literal cap, value equivalence including the query-side
substitution, and the trace surface). REQ-B6-04, -05, -06, -09 and the
inherited whole-route invariants are OPEN: the accepted route still executes
the event-silent same-block leaf, so the mission target - closing the last
event-silent computation on the accepted route - is NOT delivered. Per the
completion gate a green component checkpoint is not completion, so this rung
reports INCOMPLETE.

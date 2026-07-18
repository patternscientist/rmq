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
| M0 | (this commit) | frozen B6 matrix + worklog; no Lean changes | baseline `RMQ RMQPaper RMQExamples` exit 0 at `c0c32c4` |

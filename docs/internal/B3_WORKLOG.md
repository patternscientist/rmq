# B3 Worklog (rank/select leaf recharge; readWord-only vocabulary)

Worker B3-01, branch `claude/b1-b2-charged-fringe-tables`, base = B2
candidate HEAD `d1d645e` (`d1d645ee221c1756f8c61c5ea222950f73e43c8c`).
Matrix: B3 continuation rows in
`docs/internal/B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` (this commit).
Worklog file decision: `B2_WORKLOG.md` is left frozen as the closed B2
record; B3 milestones log here (recorded in DD-20260717-005).

## Design snapshot (fixed at M1)

- ONE chunk scale for everything: `c = bpFringeChunkBits m` over
  `m = shape.bpCode.length`, the B2 scale.  New lemma
  `machineWordBits m <= 8 * bpFringeChunkBits m` (same omega as the B2
  32-chunk window bound) bounds every in-word rank/select word by 8 chunks.
- In-word rank: NO new table.  The existing segment-21 `(v, a, b)` fringe
  chunk table already decodes in-chunk prefix ranks: the entry at slot
  `(v, t, t)` has empty-range min field
  `bpFringeChunkExcessOffsetAt c v t = c + rankTrue(t) - rankFalse(t)`,
  and with `rankTrue + rankFalse = t` this gives
  `rankTrue(t) = (minField + t - c) / 2` (truncation-free by
  `bpFringeChunkExcessOffsetAt_add_false`), `rankFalse(t) = t - rankTrue(t)`.
  One read per chunk; chunks covering `[0, effLimit)` where
  `effLimit = min limit word.length` (the clamp makes the evaluator agree
  with `boolRankPrefix`, which also stops at the word end, WITHOUT reading
  `false` padding as data); read count `min (ceil(effLimit / c)) 8`,
  cap identity on the reachable domain.
- In-word select: per-chunk slice popcounts from the same `(v, t, t)` reads
  route an early-exit fold (`k < count_j` branch decided by the decoded
  read); the containing chunk finishes with ONE read of the NEW select
  table `bpChunkSelectTable c target` (rows `2^c * (c+1)`, slot
  `v * (c+1) + k`, entry = position of the k-th target bit of the c-bit
  pattern of `v`, sentinel `c` when absent).  Because the routing count is
  the SLICE popcount, the selected position provably lies inside the slice
  (padding positions unreachable), and sentinel entries are unreachable on
  the honest route.  Read count `<= 8 + 1 = 9`.
- Leaf recharges (Costed layer, parallel-then-swap):
  - `TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted c target pos`
    = 3 accepted sample/word reads + chunked in-word rank (`<= 3 + 8 = 11`);
    value equal to `rankCosted` at every invocation given
    `machineWordBits bits.length <= 8c`-side conditions from the
    structure's own fields.
  - `bpChunkedDenseTwoWordSelectCosted` mirrors the accepted dense leaf's
    exact branch structure with the two in-word ranks and one in-word
    select replaced (`<= 1 + 8 + 8 + max(9, 1 + 9) = 27`).
  - `SparseExceptionDirectory.bpChunkedReadCosted` (`<= 11 + 1 = 12`),
    `SparseExceptionSelectData.bpChunkedSelectCosted`
    (`<= 4 + max(11 + 1, 4 + max(12, 27)) = 35`).
- Store: select table = reviewer/global segment 22, constructor appended
  last; fringe reads stay at 21.  Cost algebra projection:
  `selectClose 35, rankClose 11, endpointFringe 37, interior 30` giving
  `wholeQuery = 2*35 + (2*11 + 2*37 + 30) + 11 = 207` (DERIVED at the swap
  commit; the checked derivation wins).
- Vocabulary theorem (B-campaign signature): after the swap, every event of
  the accepted whole-query global word trace is a `readWord` constructor;
  paper-facing name planned
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
  + headline abbrev.

## Milestones

- [x] M1 matrix extension + this worklog + DD-20260717-005 (docs only).
- [x] M2 `ChargedWordChunks.lean`: word-geometry lemma
      (`machineWordBits_le_8_mul_bpFringeChunkBits`), in-chunk rank decode
      (`bpChunkRankOfEntry(_packed)`, `bpFringeChunkMinOffset_self`,
      `bpRankPrefix_true_add_false`), chunked in-word rank fold
      (`bpChunkedWordRankCosted`, cost <= 8,
      `_value` = `RAM.boolRankPrefix` under `word.length <= 8c`), select
      chunk table (`bpChunkSelectTable c target`) + size/width/erasure/
      littleO/capacity facts, chunked in-word select fold
      (`bpChunkedWordSelectCosted`, cost <= 9,
      `_value` = `RAM.boolSelectInWord` under `word.length <= 8c`),
      select-table corruption witness
      (`bpChunkSelectTable_corruption_changes_select_value`: honest
      `some 0` vs corrupted-slot-0 `some 1` on word `[false]`, occ 0).
- [ ] M3 `ChargedRankSelectLeaves.lean`: the four Costed leaf recharges +
      value equivalences + literal cost bounds.
- [ ] M4 trace layer (FlatStoreComputation folds at segments 21/22, house
      surface lemmas), parallel select/rank trace twins.
- [ ] M5 atomic swap: route consumers + reviewer source 22 + payload/
      overhead + cost re-derivation + adequacy/provenance regeneration +
      vocabulary theorem + headline/validation/harness updates +
      docstring fixes (REQ-B3-13).
- [ ] M6 final battery + matrix closure + report.

## Current state / resume point

M1 committed (docs only).  Implementation starts at M2.

Planned M4 steps, following `ChargedFringeTrace.lean` verbatim as the
template:

1. `ChargedRankSelectTrace.lean`: `bpChunkedWordRankComputationFrom` /
   `bpChunkedWordSelectComputation` as `FlatStoreComputation`s (one word
   read per chunk, `bitsToNatLE` decode into the M2 step functions);
   `_run_value` (= the M2 Costed folds on any table's own words),
   `_run_reads_length`, `_run_footprint`; then
   `TraceResultAtSegment(WithStore)` wrappers at parameters
   `(rankSegment := 21-global / component-local per AtSegments style,
   selectSegment := 22)` with `_toCosted`, `_eq_of_agree`,
   `_store_parametric`, `_matchesReadStore`, `_trace_forall`,
   `_no_syntheticCostOnlyPrimitive`.
2. Trace twins of the four leaf recharges mirroring
   `GenericSelect/RAM.lean` (`rankTraceResult` :333,
   `selectTraceResult` :1779, `selectTraceResultRelabeled` :1835) and
   `RAMStoreParam.lean` twins, with the `wordRank`/`wordSelect` emissions
   replaced by the segment folds; segment plumbing via a
   `chunkTableSegment`/`selectTableSegment` extension of
   `concreteBPNativeSelectCloseTraceSegmentLayout`.
3. M5 swap at `SuccinctFinalRAM.lean:23/:30/:37/:1304/:1649/:1671`
   consumers + `ReviewerPhysical` constructor 22 + `FlatPayload` layout +
   adequacy/provenance + cost algebra fields
   (`selectClose := 35`, `rankClose := 11`) + derived literal + 142 frozen
   (pattern `SilentFringeChargedTraceCost`) + vocabulary theorem +
   REQ-B3-13 docstring fixes in the same commit as the derived literal.

## Verification ledger (B3)

(commands, exit codes, durations recorded per milestone)

- M1: docs only.
- M2: `lake env lean RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedWordChunks.lean`
  exit 0 (4 fix iterations, ~1.5-2.5 min each).  Toolchain notes for the
  successor: (a) core `Nat.min_eq_left/right`, `Nat.min_zero`,
  `Nat.succ_min_succ` are stated over the generic `min` while the house
  goals use `Nat.min` — never `rw` them directly; introduce a `have` with a
  `Nat.min` type ascription first (B2 style); (b) `decide` cannot reduce
  through `Nat.log2` (well-founded recursion), so witness proofs must route
  around table widths via `readCosted_erase`-style theorems (the new
  `bpChunkedWordSelectCostedFrom_step_found` exists for exactly this);
  (c) `Nat.log2 (c+1) <= c+1` needs the factor-2 slack contradiction
  pattern from `ChargedFringeTableFacts`, not a direct pow argument.
- M2 library root: `lake build RMQ` exit 0, 23 s incremental (module
  registered in `RMQ.lean` this commit; 211 jobs).

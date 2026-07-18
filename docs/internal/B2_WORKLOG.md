# B2-01 Worklog (charged chunked fringe)

Branch `claude/b1-b2-charged-fringe-tables`, base `b6338ea`. Matrix:
`docs/internal/B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` (commit `ae99812`).

## Design snapshot (fixed at M2 start)

- Chunk width `bpFringeChunkBits m = Nat.log2 m / 8 + 1` over the bpCode
  length `m`, mirroring `RankSelectSpec.fixedWeightSubLogChunkBlockSize`
  (`RankSelectCompressedSubLog.lean:25`) so the o(n) budget can reuse the
  proven `/8`-slack template
  (`fixedWeightSubLogChunkDenseDecoderBudget_littleO_core`,
  `RankSelectCompressedSubLog.lean:1264`).
- Window `4 * machineWordBits m` bits fits in <= 32 chunks (omega on
  `L = 8q + r`); prefix positions run to `len`, so the fold visits chunk
  indices `0..relHi/c`, at most 33 chunks, one charged table read each.
- ONE packed table `bpFringeChunkTable c : FixedWidthNatTable`, row per
  `(chunkValue v < 2^c, startOff a <= c, endOff b <= c)`, slot
  `(v*(c+1)+a)*(c+1)+b`, entry packs `(deltaOffset, rangeMinOffset,
  rangeArgMin)` base-((2c+2),(c+1)); all excess fields offset-encoded by
  `+c` with truncation-free characterization lemmas (REQ-B2-11).
- Boundary handling: mechanism 1 of the design doc generalized — the
  `(value, startOff, endOff)` index covers full chunks (a=0,b=c), partial
  first/last chunks, and short trailing slices (pattern padding with `false`
  only ever read at offsets `t <= slice.length`, proven, so padding never
  corrupts excess).
- Charged fringe = 4 window word reads + <= 33 table reads (literal 37).
- Equivalence strategy: rewrite accepted per-position scan
  (`localBPSeededPrefixRangeArgMinPrefixPos(From)`) into a clamp-free
  generic scan under the accepted coverage hypotheses; prove generic-scan
  split/merge/reindex algebra; per chunk, table argmin = generic scan of the
  chunk spec; running excess via `rankPrefix_append/drop/take` additivity;
  no-truncation side conditions discharged from a window-validity hypothesis
  (`forall t <= len, rankPrefix false window t <= seed + rankPrefix true
  window t`), which holds at accepted call sites via
  `localBPSeededExcessAt_eq_bpExcessAt` + `bpExcessAt_prefix_nonnegative`.

## Milestones

- [x] M1 matrix frozen and committed (`ae99812`).
- [x] M2 `ChargedFringeChunks.lean`: geometry, spec, packed entries, table,
      correctness lemmas (compiles clean via `lake env lean`).
- [x] M3 scan algebra + silent chunked fold + fold = accepted-scan
      equivalence (`bpFringeChunkFold_eq_localBPSeeded` checked).
      Toolchain note: `omega` here does NOT reason about `Nat.min`/`Nat.max`
      — every min/max fact must be supplied via `Nat.min_le_left/right`,
      `Nat.min_eq_left/right`, `Nat.le_min.mpr`, `Nat.max_eq_left/right`,
      `Nat.le_max_left/right` before `omega`; `rw [Nat.succ_mul]` without
      explicit arguments corrupts numeral products (rewrites `2*c`), always
      pass explicit args (`Nat.succ_mul j c`).
- [x] M4 charged Costed evaluator + left/right wrappers + literal cost bound
      + corruption witness (value dependency): done, all checked.
- [x] M5 store/space (delivered scope): `ChargedFringeSpace.lean` —
      table payload length identity, component erasure, width <= 3c+6,
      width <= reviewerWordBits n (all n), rowCount <= 64(n+1) capacity
      feed, `bpFringeTableOverhead_littleO`, candidate amendment pair
      `bpChunkedBuildPayloadCandidate/OverheadCandidate` with checked
      `2n + o(n)` shape. ReviewerSource extension + public name swap
      COUPLED to wiring successor (DD-20260717-003; matrix
      REQ-B2-04/05/06 annotated OPEN with reasons).
- [x] M6 (Costed layer): `ChargedFringeSubstitution.lean` —
      `bpChunkedCrossBlockCloseCostedWithRankSeed(_value_eq,
      _cost_le_principled)` pin the wiring at the accepted Costed
      call site under the accepted route's own query-side facts.
      TraceResult/WithStore substitution + actual wiring = named
      successor rung.

## Current state

M1 done. M2+M3 drafted in
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeChunks.lean`
(first compile in progress). Structure of the file:

- geometry (`bpFringeChunkBits`, 32-chunk window bound);
- chunk spec (`bpFringeChunkExcessOffsetAt` + truncation-free
  characterization `_add_false`, `bpExcessAtBits` bridge);
- generic scan (`bpFringeScanBetter/ArgMinFrom/ArgMin` + `_le/_ge` bounds,
  split `_add`, `_assoc`, run-merge `_eq_better_scanArgMin`, `_append`,
  affine reindex `_affine`);
- packed table (`bpFringeChunkPacked` + `_arg/_min/_delta` unpack,
  `bpFringeChunkSlot` + decode, `bpFringeChunkEntries`,
  `bpFringeChunkTable : FixedWidthNatTable`, `readCosted_erase`);
- window chunks (`bpFringeWindowChunkValue`, padding lemma
  `natToBitsLE_bitsToNatLE_append_replicate`, pattern/slice rank agreement);
- accepted-scan bridge (`bpFringeWindowScore`, `BPFringeWindowValid`,
  `localBPSeededExcessAt_base_add`, clamp-free scan lemmas);
- chunk decomposition (`bpFringeWindowScore_chunk_char`);
- silent fold (`bpFringeChunkCand/FoldStep/FoldFrom/Fold`,
  `bpFringeExpectedBest`, single-chunk step `bpFringeChunkBestStep`,
  invariant `bpFringeChunkFoldFrom_snd_invariant`, top-level
  `bpFringeChunkFold_snd_eq`, accepted bridge
  `bpFringeChunkFold_eq_localBPSeeded` with `Option.map (base + .)`).

Next (M4): charged fold `bpFringeChunkFoldCostedFrom` (generic over any
`FixedWidthNatTable`, one `readCosted` per chunk, decode via `%`/`/`),
`bpFringeChunkStepDecoded`, cost = count lemma, value = silent fold lemma
(via `readCosted_erase` + unpack), wrappers
`bpChunkedLeft/RightFringeCandidateSeededCosted` (4-tick window +
`Nat.min (relHi/c + 1) 33` capped fold — cap is identity on reachable
domain since `relHi <= window.length <= 4W <= 32c`), cost <= 37 literal,
value equivalence with `localBPLeft/RightFringeCandidateSeededCosted`
under (hvalid, hcount, hstart, hcov), corruption witness at c = 1 with
entries `[2,2,1,1,18,18,21,21]`, corrupted slot 5 -> 22, window `[true]`,
seed 1 (values 1 vs 3 at position 0).

## Verification ledger

(commands, exit codes, durations recorded per milestone)

- M1: none (docs only).
- M2/M3 deps: `lake build RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam ...` exit 0, 8m50s (mutex held).
- M2+M3: `lake env lean RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeChunks.lean` exit 0 (after 3 fix iterations; ~2-3 min each).
- M4: same command exit 0 (2 iterations).
- M6: `lake build RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks` exit 0 (76 jobs); `lake env lean .../ChargedFringeSubstitution.lean` exit 0 (2 iterations: namespace fix).
- M5 deps: `lake build RMQ.Core.SuccinctRMQClassic` exit 0, 5m45s (mutex held).
- M5: `lake env lean .../ChargedFringeSpace.lean` exit 0 (2 iterations: by_contra unavailable, zero-case normalization).
- Final: see report (root build, hygiene rg, git diff --check, design_decision_check).

## Open risks

- Reviewer store extension (REQ-B2-04/05) may ripple into
  `SuccinctFinalRAM`/`SuccinctFinalModelAdequacy` (`segment < 21`); decision
  and fallout to be recorded at M5 (B4-scope breakage must be explicit).
- The `(v,a,b)` table triples the index space vs a `(v,offset)` design;
  o(n) budget unaffected (`/8` slack), but the M5 width-vs-reviewer-word
  lemma (`w <= reviewerWordBits n` for all n) still needs a small
  log-vs-linear argument.

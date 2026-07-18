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
- [x] M3 `ChargedRankSelectLeaves.lean`: the four Costed leaf recharges +
      value equivalences + literal cost bounds:
      `TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted`
      (`_cost_le` <= 11, `_value_eq` = `rankCosted` value for every
      target/pos under `wordSize <= 8c`, `_exact`);
      `bpChunkedDenseTwoWordSelectCosted` (<= 27, `_value_eq`);
      `SparseExceptionDirectory.bpChunkedReadCosted` (<= 12, `_value_eq`);
      `SparseExceptionSelectData.bpChunkedSelectCosted` (<= 35,
      `_value_eq` for every idx under the data's own three word-size
      bounds, `_exact` = `Succinct.select target bits idx`); plus
      `BoundedPayloadWordStore.read_word_length_le`.
- [x] M4a `ChargedRankSelectTrace.lean` (word-level trace folds):
      `bpChunkReadTraceResult` (one genuine `readWord segment slot` event
      recording the supplied store's word, value = its `bitsToNatLE`
      decode — the `Program.evalR` readWord discipline generalized to
      data-dependent addressing) with toCosted_of_agree/matchesReadStore/
      trace_forall/no_synthetic/store_parametric;
      `bpChunkedWordRankTraceResultAtSegmentWithStore` (+`From`) with
      `_toCosted_of_agree` (= the M3 Costed rank fold under table-segment
      agreement), bounded `_trace_forall` (every event is a
      `readWord tableSegment slot` with `slot < bpFringeChunkRowCount c`),
      `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`,
      `_store_parametric`;
      `bpChunkedWordSelectTraceResultAtSegmentsWithStore` (+`From`,
      two segments rankSegment/selectSegment) with the same surface plus
      the canonical select-address bound
      `_trace_forall_of_honestRank` (under honest-rank-table agreement
      every select-segment read has `address < bpChunkSelectRowCount c`).
- [x] M4b `ChargedRankSelectLeafTrace.lean` (worker B3-02): raw-word
      read atom `bpWordReadTraceResult` (+ agree/forall/matches/
      no-synthetic/parametric), relative-offset atom
      `bpRelativeOffsetReadTraceResultWithStore`, AtSegments-level
      general select `_trace_forall` wrapper, and the four chunked leaf
      trace twins —
      `TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore`
      (3 direct sample/word `readWord`s + segment-parameterized chunk
      fold; register presentation retired at these sites only,
      DD-20260718-001),
      `bpChunkedDenseTwoWordSelectTraceResultWithStore` (+ bounded
      `_trace_forall_of_honestRank`),
      `SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`,
      `SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore`
      (accepted super/local entry-table WithStore reads reused
      verbatim) — each with `_toCosted_of_agree` (= the M3 chunked
      Costed twin under per-segment agreement / entry-table pullbacks),
      `_trace_forall`, `_matchesReadStore`,
      `_no_syntheticCostOnlyPrimitive`, `_store_parametric`.
- [x] M5-prep `ChargedRankSelectWiring.lean` (worker B3-02, parallel):
      shape-level chunk-scale word-size bounds (all four hypotheses of
      the M3 value equivalences discharged from `wordSize_le_machine` /
      `longFlagRank_wordSize_le_machine` / `rank_wordSize_le_machine`
      fields + `machineWordBits_le_8_mul_bpFringeChunkBits`); chunked
      route Costed consumers
      `concreteBPNativeChunkedSelectCloseCosted` (value_eq to
      `selectCosted`, cost <= 35, `_exact` = `Succinct.select`) and
      `concreteBPNativeChunkedRankCloseCosted` (value_eq to
      `rankCosted false`, cost <= 11, `_exact` = `Succinct.rankPrefix`);
      canonical-store agreement facts for segments 17/18/19; chunked
      rank-close global word trace
      `concreteBPNativeChunkedRankCloseGlobalWordTraceResult` with
      `_refines`/`_matchesReadStore`/`_no_syntheticCostOnlyPrimitive`
      and the rank-leg vocabulary fact `_events_readWord`.
- [ ] M5 atomic swap: route consumers + reviewer source 22 + payload/
      overhead + cost re-derivation + adequacy/provenance regeneration +
      vocabulary theorem + headline/validation/harness updates +
      docstring fixes (REQ-B3-13).
- [ ] M6 final battery + matrix closure + report.

## Current state / resume point (B3-01 checkpoint, HEAD after matrix
## evidence commit)

Delivered and committed, library green at every commit:

- M1 `a32713c` (matrix rows REQ-B3-01..14 frozen, this worklog,
  DD-20260717-005);
- M2 `93ab753` (`ChargedWordChunks.lean`: in-word rank/select chunk core,
  select table + facts, universal value equivalences, corruption
  witness);
- M3 `63aa401` (`ChargedRankSelectLeaves.lean`: the four Costed leaf
  twins with `_value_eq` at every invocation, costs 11/27/12/35);
- M4a `2517a32` (`ChargedRankSelectTrace.lean`: word-level trace folds at
  parameterized segments with the full B2-style surface);
- REQ-B3-13 docstring/comment fixes `fcd491e`.

The successor resumes at M5 with everything below still to do; the
Costed layer (M3) and the trace layer (M4a word-level + M4b leaf twins in
`ChargedRankSelectLeafTrace.lean`) need NO further work.  M4b agreement
hypotheses are shaped for the canonical store: per-address agreements at
the layout segments (rank samples at `rankBase`/`+1`/`+2`, relatives,
bit words, chunk table, select table) plus the existing entry-table
pullback equalities; discharge them from
`concreteBPNativeSuccinctRMQGlobalReadStore` simp facts at M5.

1. M5 atomic swap commit (C05 coupling; mirror B2-02 M9 and
   DD-20260717-004 exactly):
   - route consumers `concreteBPNativeRankCloseInterpretedCosted` (:30),
     `concreteBPNativeSelectCloseInterpretedCosted` (:23) := the chunked
     Costed twins at `c := bpFringeChunkBits shape.bpCode.length`
     (hypotheses discharged by `wordSize_le_machine` fields +
     `machineWordBits_le_8_mul_bpFringeChunkBits`); trace twins at
     `SuccinctFinalRAM.lean:37/:1304/:1649/:1671` := the M4b chunked
     trace twins; LCA rank-seed threading unchanged (the dispatcher's
     rank parameter receives the swapped rank close).
   - `ReviewerPhysical.lean`: `ReviewerSource.selectChunkTable` appended
     as constructor 22 (payload
     `(bpChunkSelectTable (bpFringeChunkBits shape.bpCode.length)
     false).payload`), segment map 22, erasure/capacity
     (`bpChunkSelectRowCount_le_linear`)/width
     (`bpChunkSelectEntryWidth_le_machineWordBits_capacity`)/address
     folds, manifest nodup (22 sources), liveness + producer may-path +
     successful-occurrence witness; dead-source witness moved to
     segment 23 at identical strength; adequacy
     `canonical_segments_complete <-> segment < 23`,
     `compatibility_tail_unreachable` at `23 <=`.
   - `FlatPayload`/`SuccinctRMQClassic`: reviewer payload layout gains
     the select-table payload appended last; overhead +=
     `bpChunkSelectTableOverhead`; public statement shapes verbatim;
     capstone `rfl` conjunct preserved; read-backing gains the
     segment-22 disjunct.
   - cost algebra: `selectClose := 35`, `rankClose := 11` (component
     bounds `bpChunkedSelectCosted_cost_le` /
     `bpChunkedRankCosted_cost_le` + 3 sample reads); derived literal by
     `rfl` (projection `2*35 + (2*11 + 2*37 + 30) + 11 = 207`; the
     checked derivation wins); every 142 consumer re-proved; 142 frozen
     as historical following the `SilentFringe...` pattern (name
     suggestion: `...SilentWordRankSelectChargedTraceCost_eq = 142`);
     re-sync the two REQ-B3-13 docstrings to the new literal; harness
     boolean + `RMQExamples` guards updated.
   - vocabulary theorem (REQ-B3-10, paper-facing): after the swap every
     whole-query trace event is a `readWord` — prove via the regenerated
     `_trace_forall` inductions (all component handlers now readWord
     shaped); suggested name
     `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
     + headline abbrev.
2. M6 final battery per the delegation prompt (mutex
   `Global\RMQHeavyVerification` for anything > 5 min; full battery at
   the candidate tree; `git rev-parse` the base for
   `design_decision_check.ps1 -Strict -Base
   d1d645ee221c1756f8c61c5ea222950f73e43c8c`).

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
- M3: `lake env lean .../ChargedRankSelectLeaves.lean` exit 0
  (2 fix iterations, ~2 min each; the rank cost proof needs explicit
  triple-nested `cases` so the read word is named for the fold bound);
  `lake build RMQ` exit 0, 12 s incremental (212 jobs); hygiene rg no
  hits.
- M4a: `lake env lean .../ChargedRankSelectTrace.lean` exit 0
  (2 iterations; `List.Mem event [x]`/`[]` eliminations need explicit
  `cases hmem with | head | tail` — plain `simp at hmem` does not reduce
  the prefix-form `List.Mem`); `lake build RMQ` exit 0, 12 s incremental
  (213 jobs); hygiene rg no hits.
- REQ-B3-13 commit: `lake build RMQ` exit 0, 7m05s (the FlatPayload
  comment rebuilt the heavy downstream chain; run under the
  `Global\RMQHeavyVerification` mutex next time — this one was launched
  expecting an incremental no-op); `claim_drift_scan.ps1` exit 0
  (694 hits, 0 strict failures).
- Checkpoint battery at `a1a7659`: `git diff --check` and
  `git diff --check d1d645e..HEAD` clean;
  `design_decision_check.ps1 -Strict -Base d1d645e...` exit 0
  (10 changed files); working tree clean; every commit in
  `d1d645e..HEAD` had `lake build RMQ` green at commit time.
  `paper_topology_lint.ps1` and the cost harness were NOT run at this
  checkpoint (public theorem surface untouched by B3-01; they are M6
  candidate-tree obligations).
- M4b (worker B3-02):
  `lake env lean .../ChargedRankSelectLeafTrace.lean` exit 0 after
  3 iterations (~2 min each).  Toolchain notes for the successor:
  (a) after `cases` on a funext-bound `Option` variable, the
  surrounding `match`/`ite` stays iota-unreduced in goals WITHOUT a
  `.toCosted` head — insert `dsimp only` before any `rw [if_pos ...]`
  or fold-lemma rewrite (the `_toCosted_of_agree` proofs did not need
  it, every `_store_parametric` and the select `_trace_forall` did);
  (b) `set_option ... in` must precede the doc comment, not sit
  between `-/` and `def`; (c) the accepted-style
  `simp [...] at hmem` membership destructuring does NOT work on
  prefix-form `List.Mem` hypotheses (M4a ledger note confirmed) — the
  select twin's `_trace_forall` uses the bind_trace_forall +
  `cases hval : (...).value` + `dsimp only` script instead.
  `lake build RMQ` exit 0, 14.8 s incremental (214 jobs, module
  registered in `RMQ.lean`, mutex held); hygiene rg no hits over the
  touched files; `git diff --check` clean.
- M5-prep (worker B3-02):
  `lake env lean .../ChargedRankSelectWiring.lean` exit 0 first
  iteration; `lake build RMQ` exit 0, 9.9 s incremental (215 jobs,
  mutex held); hygiene rg no hits; `git diff --check` clean.  The
  segment-17/18/19 agreement facts reduce by
  `simp [concreteBPNativeSuccinctRMQGlobalReadStore,
  concreteBPNativeRankCloseTraceSegmentBase,
  ...rankRegisterWordRAMStore, WordRAM.Store.readWord?]` alone.

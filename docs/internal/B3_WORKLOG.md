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
- [x] M5 atomic swap: route consumers + reviewer source 22 + payload/
      overhead + cost re-derivation + adequacy/provenance regeneration +
      vocabulary theorem + headline/validation/harness updates +
      docstring fixes (REQ-B3-13).  (workers B3-03 + B3-04)
- [x] M6 final battery + matrix closure + report.  (worker B3-04)

## Current state / resume point (B3-02 checkpoint)

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
- REQ-B3-13 docstring/comment fixes `fcd491e`;
- M4b `4cd74c1` (`ChargedRankSelectLeafTrace.lean`: the four chunked
  leaf trace twins, WithStore, readWord-only emissions;
  DD-20260718-001);
- M5-prep `5eba561` (`ChargedRankSelectWiring.lean`: chunked route
  Costed consumers with all hypotheses discharged at shape level;
  chunked rank-close global word trace at the canonical store with
  `_refines` and the rank-leg `_events_readWord`).

The successor (B3-03) resumes at the M5 ATOMIC SWAP COMMIT; the Costed
layer (M3), the trace layer (M4a + M4b), and the route-glue layer
(M5-prep) need NO further work.  Concrete swap notes beyond the M5 plan
below:

- Swap points: `concreteBPNativeSelectCloseInterpretedCosted` /
  `concreteBPNativeRankCloseInterpretedCosted`
  (`SuccinctFinalRAM.lean:23/:30`) := the M5-prep chunked consumers
  (values re-proved via `_value_eq`); trace twins at `:37/:1304` :=
  `SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore` at
  `concreteBPNativeSelectCloseTraceSegmentLayout`, chunk segment 21,
  select segment 22, canonical store; rank-close trace twins := the
  M5-prep `concreteBPNativeChunkedRankCloseGlobalWordTraceResult`.
- The select twin's `_toCosted_of_agree` needs: 8 entry-table pullback
  equalities (present shape: the existing house pullback facts — find
  them where the current WithStore route discharges them,
  `SuccinctFinalStoreParam.lean`), per-address agreements at 9/10/11
  (long flag rank), 12 (long relative), 13/14/15 (sparse rank), 16
  (sparse relative), 0 (bit words), 21 (chunk table — existing
  `_fringeChunkTable` fact), and 22 (select table — NEW, lands with the
  store extension: add
  `concreteBPNativeSelectChunkTraceSegment : Nat := 22` +
  `else if segment = 22 then (SuccinctClose.bpChunkSelectTable
  (bpFringeChunkBits shape.bpCode.length) false).store.words[index]?`
  to `concreteBPNativeSuccinctRMQGlobalReadStore` in `Segments.lean`,
  same commit as the `ReviewerSource.selectChunkTable` constructor per
  C05).  The 9/10/11 and 13/14/15 facts follow the M5-prep
  segment-17/18/19 simp pattern verbatim (store maps them to
  `rankRegisterWordRAMStore true` segments 0/1/2).
- Vocabulary theorem: every M4b/M5-prep twin's `_trace_forall` handlers
  are all `readWord`-shaped, so the whole-query statement is the
  composition of `_events_readWord`-style instances over the swapped
  whole-query trace; the interior/endpoint fringe components were
  already readWord-only after B2 (their `_trace_forall` lemmas are in
  `ChargedFringeTrace.lean` / the interior trace modules).
- Cost algebra: `selectClose := 35`, `rankClose := 11` from the M5-prep
  `_cost_le` wrappers; derived route literal by `rfl` (projection
  `2*35 + (2*11 + 2*37 + 30) + 11 = 207`); freeze 142 as
  `...SilentWordRankSelectChargedTraceCost_eq = 142` following the 76
  (`canonicalSilentFringeQueryCost`) pattern from `d1d645e`; grep for
  `142` across `SuccinctFinalRAM.lean`, `SuccinctFinalModelAdequacy`,
  `SuccinctRMQClassic`, `Headlines/RMQ.lean`, `Validation/*`,
  `RMQExamples/*`, `scripts/paper_topology_lint.ps1` (`SumLe142`
  CURRENT-anchor rename is coordinator-ratified per the B2 precedent),
  `scripts/headline_axiom_check.lean`; re-sync the two REQ-B3-13
  docstrings to the new literal in the same commit.
- Study `git show d1d645e` per-file before starting: the reviewer-store
  extension (`ReviewerPhysical.lean` + `FlatPayload.lean` +
  `Segments.lean` + adequacy/provenance regeneration) mirrors that
  commit with 21 -> 22 and the dead-source witness moving 22 -> 23.

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

## Current state / resume point (B3-03 checkpoint, M5 IN PROGRESS)

Worker B3-03 executed roughly 70% of the M5 atomic swap.  NOTHING of the
swap is committed (C05 atomicity); the ENTIRE swap lives in the WORKING
TREE of this worktree, and as insurance in the committed patch
`docs/internal/B3_M5_WIP.patch` (apply from a clean `67247f3`+this-commit
tree with `git apply docs/internal/B3_M5_WIP.patch`; delete the patch file
in the eventual swap commit).  DO NOT reset the working tree without
applying/keeping the patch.

DONE and verified green (each via `lake build <module>`, incremental):

- Store extension (segment 22 = `bpChunkSelectTable c false`):
  `Segments.lean` (+`concreteBPNativeSelectChunkTraceSegment := 22`, store
  branch, `_selectChunkTable` read fact), `ReviewerPhysical.lean`
  (`ReviewerSource.selectChunkTable` appended, maps/folds/nodup/length 22,
  coverage < 23, dead witness moved 23, capacity via
  `bpChunkSelectRowCount_le_linear`, width via
  `bpChunkSelectEntryWidth_le_machineWordBits_capacity`),
  `FlatPayload.lean` (overhead += `bpChunkSelectTableOverhead`, layout
  gains `selectChunkPayload` appended last, `_selectChunk_slice`, reviewer
  read store segment 22, read-backed 4th disjunct).  All three build green.
- `ChargedRankSelectWiring.lean` (green): select-leg canonical-store
  agreement facts (bit words, long flag 9/10/11, long relative 12, sparse
  13/14/15/16, select table 22) + 8 entry-table pullbacks; entry-table
  `events_readWord` helpers; `concreteBPNativeChunkedSelectCloseGlobalWordTraceResult`
  with `_refines` (= chunked Costed via `_toCosted_of_agree`, all 25
  hypotheses), `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`,
  `_events_readWord`; the segment-22 LIVENESS witness
  `concreteBPNativeChunkedInWordSelect_selectTable_mayRead` (in-word select
  fold on word `[false]`, occ 0, canonical store: found-branch fires a
  genuine segment-22 read; decode via `bpChunkRankOfEntry_packed` +
  `bpWordChunkRank_step`); base-parameterized
  `concreteBPNativeChunkedRankCloseSeedReadStore shape base` (segments
  base..base+2 + chunk at base+4, so base 17 lands at counted segment 21)
  with 4 read facts.
- `SuccinctFinalRAM.lean` BUILDS GREEN with the full swap core:
  - swapped `concreteBPNativeSelectCloseInterpretedCosted` /
    `concreteBPNativeRankCloseInterpretedCosted` := the chunked Costed
    consumers; `concreteBPNativeSelectCloseWordTraceResult` /
    `...GlobalWordTraceResult` := the chunked select global trace;
    `concreteBPNativeRankCloseWordTraceResultAtSegment` := chunked rank
    twin at the seed store (chunk at base+4);
    `concreteBPNativeRankCloseWordTraceResult` := AtSegment 0;
    `..._canonical_eq` (AtSegment 17 = M5-prep chunked global object).
  - LEGACY SPLIT (REQ-B3-04, key design decision): the pre-canonical
    compatibility chain keeps the retired register evaluators under NEW
    names `concreteBPNativeSelectCloseRegisterInterpretedCosted` /
    `concreteBPNativeRankCloseRegisterInterpretedCosted` /
    `concreteBPNativeSelectCloseRegisterWordTraceResult` /
    `concreteBPNativeRankCloseRegisterWordTraceResult(AtSegment)`;
    `concreteBPNativeLCACloseInterpretedCosted`,
    `concreteBPNativeSuccinctRMQQueryInterpretedCosted`,
    `WholeQueryInstr.eval/evalLeafTrace/evalWordTrace(OfSizeGe)`, the
    legacy LCA replays and the legacy-store matches theorems (incl.
    restored `_matchesReadStore_total` and OfSizeGe legacy matches) are
    rewired to the Register legs, so the axiom-pinned
    `_refines_queryCosted`/`_exact` lattice keeps statements verbatim.
    The three `_refines_*CloseCosted` bridges are restated over the
    Register names; NEW `concreteBPNativeSelectCloseInterpretedCosted_exact`
    (erase = `bpCloseOfInorder?` via
    `select_false_bpCode_eq_bpCloseOfInorder?`) and
    `concreteBPNativeRankCloseInterpretedCosted_exact` serve the canonical
    route.  Deleted (superseded, B2-deletion precedent): the legacy-store
    rank matches theorem for the chunked AtSegment (replaced by
    `concreteBPNativeRankCloseRegisterGlobalWordTraceResult_matchesReadStore`).
  - cost: algebra selectClose := 35, rankClose := 11; closeLCA_eq = 126;
    `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq = 207`
    (rfl; derived literal CONFIRMS the 207 projection); 142 frozen as
    `concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost(_eq/Algebra)`;
    `_cost_le_thirtyFive`/`_cost_le_eleven` for the swapped legs
    (13/4 lemmas retained for the Register legs); principled cost proof
    re-derived (LCA bound 126 via
    `canonicalLcaCloseCostedWithRankSeed_cost_le_principled ... 11`);
    transitional 328 re-proved via 207 <= 328;
    `nonSyntheticWeight_sum_le_142` renamed `_le_207`; two-sided profile
    conjuncts at 207.
  - VOCABULARY THEOREM (REQ-B3-10) PROVED:
    `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
    (every event of the accepted whole-query global word trace
    `.isReadWord`; via per-leg `events_readWord` inductions).
  - provenance: `ReviewerProducerReadPath` select constructors now cite
    the chunked WithStore components + NEW `selectDenseInWord` constructor
    (free in-word fold, used only for segment-22 liveness); may-path
    battery rebuilt WithStore-style (`selectEntryTableWithStore_mayRead`,
    `chunkedRankTraceWithStore_mayRead`, `chunkedSparseDirectoryWithStore_mayRead`,
    `chunkedDenseTwoWordSelectWithStore_mayRead`,
    `chunkedRelativeOffsetWithStore_mayRead`); `counted_producer_may_path`
    covers `.selectChunkTable` at segment 22; reviewerReadSegmentLive
    bounds 22 -> 23; FreshUnusedCanonicalSource -> segment 23;
    noFiniteSmallInterior/noReadyClose for swapped legs via
    matchesReadStore + store-none helpers; operand-fit via events_readWord.
- `SuccinctFinalModelAdequacy.lean` + `SuccinctFinalSemanticProvenanceAdequacy.lean`
  edited (207 field rename, < 23) - compile status pending downstream.
- `BPNavigationRAM.lean` store profile: segment 22 remapped from
  `summary.maxRelTable` to the select table + `_selectChunkTable` read
  fact + read-backed disjunct + successful_read_backed by_cases (its LCA
  trace theorems still red, below).

REMAINING (last full-library build failed ONLY in these files):

1. `SuccinctFinalStoreParam.lean` (errors at 392/865/3394 [3394 = <22
   fix ALREADY APPLIED in tree]): replace the two WithStore leaves:
   `concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore` :=
   `(builtRelativeSplitBPCloseRankData shape).bpChunkedRankTraceResultWithStore
   store base (base+1) (base+2) (base+4) c false pos`;
   `concreteBPNativeSelectCloseGlobalWordTraceResultWithStore` :=
   `bpChunkedSelectTraceResultWithStore layout 21 22 store c idx` (then
   `_globalReadStore` for select is `rfl` against the wiring def, for rank
   it is `(..._canonical_eq shape pos).symm`); `_matchesReadStore` /
   `_no_synthetic` := twin lemmas; `_store_parametric` := twin
   store_parametric fed by hread at local segments 0/1/2/3 after EXTENDING
   `concreteBPNativeRankCloseSegmentMap` with `| 3 => base + 4` (check its
   consumers' segment case splits gain a `3` case; the pullback lemma at
   :40 is then false as stated - restrict it to the register store or
   drop, its only consumer was the old `_globalReadStore`).  The
   `_eq_of_trace_read_agreement` chain must be re-proved for the chunked
   twins: per-fold induction, pattern = (a) head read agreement via
   `List.Mem.head` gives `bpChunkReadTraceResult_eq...` then `rw`, (b)
   tail agreement transported through `bind_trace` + `mem_append_right`
   REWRITING BY the head equality; do the rank twin by `show`-ing the
   exact def body from `ChargedRankSelectLeafTrace.lean:154` (do NOT
   guess field names), then the select twin over its six components
   (entry tables via the existing private
   `program_evalR_eq_of_trace_read_agreement`).  A draft of the fold-level
   lemmas is in the session scratchpad pattern above; rewrite them against
   the real defs.
2. `ReviewerReachabilitySmall.lean` (546/551/468/715/748/763/950/1029/
   1052/1481): singleton select-table successful reads must be recomputed
   over the CHUNKED select trace; the `change` patterns must target
   `bpChunkedSelectTraceResultWithStore` bodies; `_refines_selectCloseCosted`
   rewrites -> use `concreteBPNativeSelectCloseInterpretedCosted_exact` /
   `_refines` instead; rank uses (763, 952-960 statements over
   `AtSegment shape 17 2`) now describe the chunked trace - re-prove via
   the twin surface.  NEW W19 obligation: successful segment-22 occurrence
   on a real closed valid execution - the singleton execution's select
   goes dense (super+local unmarked), word `[true,false]`, first-chunk
   false-count 1 > 0 so the found branch issues a SUCCESSFUL segment-22
   read; script it like the `_trace_forall_of_honestRank` hreadVal block
   (`ChargedRankSelectTrace.lean:620-700`) + `bpChunkSelectSlot_lt_rowCount`;
   then extend `small_successful_closed_valid_occurrence` list with
   `.selectChunkTable` (mirror B2's `fringeChunkTable` case at the same
   theorem).
3. `ReviewerReachabilityLong.lean:639` / `ReviewerReachabilitySparse.lean:681`:
   `change` patterns over the old select trace body -> retarget to the
   chunked def (their symbolic witnesses cite long/sparse component reads,
   whose chunked components emit the same segments 9-16 plus 21).
4. `BPNavigationRAM.lean:1837` (its rank interpreted refines - rewire the
   nav profile's rank leg like the SuccinctFinalRAM legacy split or to the
   chunked consumer, whichever its store profile matches: nav store 21 =
   fringe table, 22 = select table now, so the CHUNKED legs match) and
   `:2101` (LCA matches: pass the nav-store fringe fact
   `concreteBPCloseNavigationGlobalReadStore_fringeChunkTable` and the
   chunked rank matches handler).
5. Public/doc sync (NOT started): `SuccinctRMQClassic.lean`
   (queryCost_eq = 207; freeze `canonicalSilentWordRankSelectQueryCost`
   abbrev + `_eq = 142` following the B2 pattern), `Headlines/RMQ.lean`
   (main-theorem conjunct 207, docstrings, `SumLe142` -> `SumLe207`
   abbrev rename [coordinator-ratified], NEW vocabulary headline abbrev
   for `..._readWord_only`), `Validation/SuccinctClassic.lean`
   (canonicalBoundOK: 207 + frozen 142 + 76 + 328),
   `Validation/SuccinctClassicCostHarness.lean` (canonicalBoundIs207),
   `RMQExamples/Concrete.lean` (guards 207 + 142),
   `scripts/paper_topology_lint.ps1` + `scripts/headline_axiom_check.lean`
   (SumLe207), README/docs numeric tables (claim_drift will flag), matrix
   closure rows + DD entries (log: seed-store +4 layout, Register legacy
   split, deleted/restored legacy theorems, `_cost_le_thirtyFive/eleven`
   renames, mayRead witness design), `RMQ.lean` needs no new module.
6. M6 battery per the delegation prompt.

Verified-in-session builds: `lake build RMQ.Core.SuccinctFinal.RAM.FlatPayload`
/ `...ReviewerPhysical` / `...ChargedRankSelectWiring` /
`RMQ.Core.SuccinctFinalRAM` all exit 0 (last SuccinctFinalRAM build ~6
iterations, few minutes each); full `lake build RMQ` fails only in the
five files above; hygiene rg over all touched files: 0 hits.

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
- Checkpoint battery at `6394c0c` (worker B3-02): `git diff --check`,
  `git diff --check abe2c08..HEAD`, and
  `git diff --check d1d645e..HEAD` all clean;
  `design_decision_check.ps1 -Strict -Base d1d645e...` exit 0
  (12 changed files); `claim_drift_scan.ps1` exit 0 (697 hits,
  0 strict failures); working tree clean; every commit in
  `abe2c08..HEAD` had `lake build RMQ` green at commit time.
  `paper_topology_lint.ps1` and the cost harness remain M6
  candidate-tree obligations (public theorem surface untouched by
  B3-02's parallel layer).


## Completion (B3-04): M5 landed, M6 battery

Worker B3-04 finished the remaining 30% of the M5 swap on top of the
B3-03 working tree (per-file notes below), created the ONE atomic swap
commit, and ran the M6 battery.  The recovery patch
`docs/internal/B3_M5_WIP.patch` was deleted in the bookkeeping commit
(its job is done; the swap is committed).

Per-file completion notes (beyond the B3-03 checkpoint):

- `SuccinctFinalStoreParam.lean`: rank segment map extended
  (`| 3 => base + 4`); register pullback lemma at :40 deleted (only
  consumer was the retired `_globalReadStore` proof); both WithStore
  leaves redefined to the M4b chunked twins (rank at
  `base..base+2, base+4`; select at the house layout + segments 21/22);
  select `_globalReadStore` is `rfl` against the wiring def, rank via
  `(_canonical_eq).symm`; `_matchesReadStore`/`_no_synthetic` from the
  twin lemmas; `_store_parametric` from the twin fed by `hread` at
  local segments 0/1/2/3; the `_eq_of_trace_read_agreement` chain
  re-proved COMPOSITIONALLY: new private `StoreTraceLocal` atoms
  (`bpChunkRead`/`bpWordRead`), fold lemmas (rank/select `From` folds by
  count induction over `storeTraceLocal_bind`), and chunked leaf
  compositions (rank twin, relative-offset read, sparse directory,
  dense two-word, select twin); the dead private `SelectClosePullbacks`
  section deleted; the read-agreement record gains `selectChunkTable`
  (footprint case added in `of_footprint`; `..._rankClose` footprint
  lemma re-proved over the 4-case map).  Compiled green on the first
  iteration.
- `ReviewerReachabilitySmall.lean`: WithStore<->Relabeled transfer
  lemmas for the super/local entry tables at the canonical store (via
  the wiring pullback facts + `readTraceResultRelabeledWithStore_eq_of_pullback`);
  chunked select-trace membership helpers (super/local/dense); chunked
  rank head-read helper; the singleton entry-table successful reads
  (segments 1-8), shared-BP read (0), rank claims (17/18/19) recomputed
  over the chunked traces; `_exact`-based select/rank value proofs
  (`concreteBPNative{Select,Rank}CloseInterpretedCosted_exact` replace
  the retired `_refines_*CloseCosted` rewrites).  NEW W19:
  `reviewerSingleton_selectChunkTable_successful_read` - the singleton
  dense route (basePosition 1, wordSize 2, chunk bits 1, word
  `[true, false]`) reaches the in-word select fold at occurrence 0,
  chunk 0 has false-count 0, chunk 1 fires the found branch's
  SUCCESSFUL segment-22 read at slot 0 (scripted via `read_exact` +
  `bpFringeChunkEntries_getElem` + `bpChunkRankOfEntry_packed` decode
  steps and fold-value lemmas `bpChunkedWordRankCosted_value`);
  `small_successful_closed_valid_occurrence` list extended with
  `.selectChunkTable` (aggregate cluster list in
  `ReviewerReachability.lean` extended to match).
- `ReviewerReachabilityLong.lean` / `ReviewerReachabilitySparse.lean`:
  the long/sparse select component witnesses recomputed over the
  chunked route.  KERNEL-SAFETY PATTERN (recorded in DD-20260718-002):
  at the symbolic 2^15/2^128 shapes, concrete-record defeq (kernel
  whnf through the built structures) deep-recursed the kernel; every
  such step is now a GENERIC lemma over symbolic data instantiated
  propositionally: `twoLevelRankData_sample_words_present*` (sample
  word existence at pos 0), `chunkedRankTwinWithStore_value_zero*`
  (chunked rank twin value 0 at slot 0 via `_toCosted_of_agree` +
  `bpChunkedRankCosted_value_eq` + `rankInterpretedCosted_exact` with
  `Succinct.rankPrefix_zero` REWRITTEN, never simp-unfolding
  `rankPrefix` at concrete bits), `chunkedSparseDirectoryTrace_{rank,relative}_mem`,
  `chunkedSelectTrace_sparse_read_mem`.  Toolchain notes: (a) omega
  does NOT see `Nat.min` here - use `Nat.zero_min _` with a `Nat.min`
  ascription (B2 ledger pattern); (b) `simp [Succinct.rankPrefix]` or
  `Costed.erase`-simpa at concrete huge structures is a kernel bomb -
  rewrite with the standalone `rankPrefix_zero` and keep `erase`/`value`
  conversions inside generic lemmas; (c) `sorry`-poisoned declarations
  are NOT kernel-checked, so sorry-bisection cannot localize kernel
  deep-recursion (verified empirically; final tree has no sorry
  anywhere).
- `BPNavigationRAM.lean`: nav rank leg rewired to the chunked consumer
  (nav store 21/22 = chunk/select tables):
  `concreteBPCloseNavigationRankCloseGlobalTraceResult_refines` restated
  to `= concreteBPNativeRankCloseInterpretedCosted` (proof = the
  canonical `_refines_interpretedCosted`);
  `concreteBPCloseNavigationCanonicalCosted`'s rank component is the
  chunked interpreted consumer; the B2-era bridge
  `concreteBPCloseNavigationRankCloseInterpretedCosted_refines_rankCloseCosted`
  deleted as superseded (equality false at chunked costs; B2-deletion
  precedent); rank matches theorem re-proved via the chunked twin's
  `_trace_forall` with per-segment seed-store/nav-store word equalities.
- Public/doc sync: `SuccinctRMQClassic.queryCost_eq = 207`; NEW frozen
  `canonicalSilentWordRankSelectQueryCost(_eq = 142)` following the
  76/328 pattern; `Headlines/RMQ.lean` main-theorem conjunct 207,
  docstrings synced (REQ-B3-13 re-sync), `SumLe142` -> `SumLe207`
  (coordinator-ratified current-anchor rename), NEW vocabulary abbrev
  `succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`;
  `Validation/SuccinctClassic.canonicalBoundOK` = 207 && frozen 142 &&
  76 && 328; harness boolean `canonicalBoundIs207`;
  `RMQExamples/Concrete.lean` guards 207 + frozen 142;
  `scripts/headline_axiom_check.lean` + `scripts/paper_topology_lint.ps1`
  current anchors renamed to `SumLe207` and extended with the
  vocabulary anchor; README/`docs/FAMILY_SUMMARY.md` current-cap
  numerals synced to 207 with the frozen 142 note (B2-mirror scope
  only; broader doc migration stays B5 per REQ-B3-13).

- M5 swap commit `f1c8af3` (worker B3-04): pre-commit gate = full
  `lake build RMQ` on the candidate tree, `Build completed successfully`
  exit 0 (fresh compile of every swapped module across the session; the
  final synchronous verification run was a no-op green).  Toolchain
  notes for successors: (a) `sorry`-poisoned declarations are NOT
  kernel-checked - sorry-bisection cannot localize kernel deep
  recursion; (b) concrete-record defeq at the symbolic 2^15/2^128
  reviewer shapes deep-recurses the kernel (44 GB observed on the
  pre-fix Long file) - push every such step into a generic lemma over
  symbolic structures and instantiate propositionally; (c) omega does
  not reduce `Nat.min` here; use `Nat.zero_min` behind a `Nat.min`-typed
  ascription (B2 ledger pattern); (d) never simp-unfold
  `Succinct.rankPrefix`/`Costed.erase` at concrete huge structures -
  rewrite with `rankPrefix_zero` and keep erase/value conversion inside
  the generic lemma.
- M6 battery (worker B3-04, candidate tree at `f1c8af3` +
  doc-sync `25a310b`):
  - `lake build RMQ`: exit 0 (`Build completed successfully`).
  - `lake build RMQPaper RMQExamples`: exit 0, 46 s.
  - hygiene `rg` forbidden tokens over `RMQ` + `lakefile.toml`: 0 hits;
    `native_decide|ofReduceBool` over `RMQ`: 0 hits.
  - `lake exe rmq_succinct_classic_cost_harness`: exit 0, 55 s; every
    window `agrees=true`, `canonicalBoundIs207=true`,
    `underCanonicalBound=true`.
  - `git diff --check`: clean; `git diff --check d1d645e..HEAD`: clean
    at the final HEAD (transient hits were only the committed recovery
    patch, deleted in this bookkeeping commit).
  - `design_decision_check.ps1 -Strict -Base d1d645e...`: exit 0
    (35 changed files), 3 s.
  - `claim_drift_scan.ps1`: exit 0 (762 hits, 0 strict failures), 10 s.
  - `paper_topology_lint.ps1` (mutex-held): first run failed on the
    stale `SumLe142` documentary rows in
    `docs/PAPER_CLAIM_CORRESPONDENCE.md` / `docs/WHAT_IS_PROVED.md` /
    `artifact/CLAIMS.md`; stale-doc-constant sync applied (allowed
    policy; commit `25a310b`, WDD-20260718-001) and the re-run is
    exit 0, 94 s (PASS: 82 documentary identifiers, 48 paper
    identifiers resolved, including the new
    `succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` anchor).
- Recovery patch `docs/internal/B3_M5_WIP.patch` DELETED in this
  bookkeeping commit: the M5 swap is committed at `f1c8af3`, so the
  insurance copy has served its purpose.

# B4 Worklog (provenance hardening over the charged-table route)

Worker B4-01, branch `claude/b1-b2-charged-fringe-tables`, base = B3
candidate HEAD `6e105a5` (`6e105a58872a643d952a3a1e26f5a9ffc60c0c4b`).
Matrix: B4 continuation rows in
`docs/internal/B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` (this commit).
Worklog file decision: `B3_WORKLOG.md` is left frozen as the closed B3
record; B4 milestones log here (recorded in DD-20260718-003, following the
B3 precedent in DD-20260717-005 item 6).

## Design snapshot (fixed at M1)

- W19 coverage finding (session survey, anchors in the matrix): the generic
  occurrence packet (`ReviewerReadOccurrenceReceipt`,
  `..OccurrenceProvenance_checked`,
  `repeated_equal_read_occurrences_have_distinct_receipts`) is
  segment-generic with coverage `segment < 23`, so segment-21/22 reads
  already flow through it.  B4's provenance deliverables are therefore:
  (a) named per-segment corollaries derived from the generic packet
  (REQ-B4-02), (b) closing the segment-21 multi-consumer gap - segment 21
  is read by all three `ReviewerReadLeaf`s but only the
  `(21, .canonicalClose)` successful claim exists; add
  `forall leaf, (claim 21 leaf).HasSuccessfulClosedValidOccurrence`
  (REQ-B4-02), and (c) positional repeated-equal-read witnesses with
  distinct receipts for segments 21 and 22, folded as NEW fields into
  `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`
  (REQ-B4-03; extends the packet the paper chain consumes, no sibling).
- Repeated-read witness plan: singleton query `[7]`, `left = 0, right = 1`.
  The whole-query program runs the select close twice at the same index 0,
  so the two instruction occurrences emit equal component traces; a
  segment-22 (and segment-21) successful read in the component trace at
  local position p yields whole-trace positions `p` (first instruction,
  empty prefix) and `prefixLen + p` (second instruction), distinct because
  `p < prefixLen`.  Position facts via the `ProducesEventAt`
  offset equation and `List.getElem?` append arithmetic (generic lemmas;
  no whole-trace kernel evaluation - `Nat.log2` blocks kernel reduction).
- Chunk-width corners (REQ-B4-04): all-size cap identity
  `bpWordChunkCount (bpFringeChunkBits m) (machineWordBits m) =
  (machineWordBits m - 1) / bpFringeChunkBits m + 1` via
  `bpWordChunkCount_eq` + `machineWordBits_le_8_mul_bpFringeChunkBits`;
  corners at m = 0/1 pinned by the log2 house pattern
  (`simp [Nat.log2]` / sandwich; `decide` cannot reduce `Nat.log2`).
- Direct o(n) (REQ-B4-05): `LittleOLinear` of the SUM OF ACTUAL PAYLOAD
  LENGTHS of the two tables at `c = bpFringeChunkBits (2n)`, transported
  along the `_payload_length` equalities, witness =
  `bpFringeTableOverhead_littleO.add bpChunkSelectTableOverhead_littleO`;
  numeric sanity at n = 4/16/256 (chunk bits 1/1/2) after log2 pinning.
- Whole-query value dependency (REQ-B4-06): witness store pairs mutated
  only at segment 21 (resp. 22) at a consumed address; minimum
  full-TraceResult inequality via the `_ne_of_consumed_read_disagreement`
  pattern; `.value` inequality attempted via the component corruption
  values threaded through the `_eq_of_agree`/`_store_parametric` surface;
  the projection level actually proven is recorded in the matrix row.
- Charge-policy doc (REQ-B4-07) + bookkeeping (REQ-B4-01) +
  navigation audit repair/quarantine (REQ-B4-08) per the matrix rows.

## Milestones

- [x] M1 matrix extension + this worklog + DD-20260718-003 (docs only).
- [x] M2 bookkeeping repairs commit (REQ-B4-01: correspondence-doc alias +
      counts, REQ-B3-07 wording, Register cost-lemma renames, stale
      docstrings, Segments.lean legacy-numeral comment, roadmap counts).
- [x] M3 `ChargedTableRegime.lean` (REQ-B4-04/05): log2 pins; corner pins
      `bpFringeChunkBits 0/1/2/8/32/512 = 1/1/1/1/1/2`,
      `machineWordBits 0/1/2 = 1/1/2`; all-size cap identity
      `bpWordChunkCount_machineWord_eq` + two-sided
      (`one_le_...`, `..._le_eight`, coverage
      `machineWordBits_le_bpWordChunkCount_mul`); corners m = 0/1 (`= 1`)
      and array-size corners n = 0/1 at scale `2*n` (`= 1`/`= 2`);
      payload-length-vs-overhead identities
      `bpFringeChunkTable_payload_length_overhead` /
      `bpChunkSelectTable_payload_length_overhead`; named witness
      `bpNewTableOverheadSum_littleO :=
      bpFringeTableOverhead_littleO.add bpChunkSelectTableOverhead_littleO`;
      direct theorem `bpNewTablePayloadBits_littleO` over the ACTUAL
      stored-table payload lengths; sanity pins at n = 4/16/256
      (rows 8/8/36 and 4/4/12; widths 5/5/7 and 2/2/2; bits 40/40/252 and
      8/8/24; totals 48/48/276).
- [x] M4 W19 per-segment corollaries + segment-21 per-leaf claims
      (REQ-B4-02): named receipt corollaries
      `concreteBPNativeSuccinctRMQFringeChunkTableRead_occurrence_receipt` /
      `concreteBPNativeSuccinctRMQSelectChunkTableRead_occurrence_receipt`
      in `SuccinctFinalRAM.lean`, derived from
      `concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`
      (not re-proved); per-leaf aggregate
      `concreteBPNativeSuccinctRMQFringeChunkTable_every_reader_leaf_successful_occurrence`
      in `ReviewerReachabilitySmall.lean` over new private leg witnesses
      `reviewerSingleton_selectClose_fringeChunk_successful_read` (dense
      select route: before-rank chunk fold on `[true, false]` at limit 1)
      and `reviewerSingleton_rankClose_fringeChunk_successful_read` (rank
      component at pos 2: three seed-value reductions, then the chunk
      fold's head read), plus the existing
      `reviewerIncreasing_fringe_successful_claim` for `.canonicalClose`;
      shared engine = new generic
      `reviewerFringeChunk_rankFold_first_successful_read` (chunk fold
      ALWAYS emits >= 1 read since `bpWordChunkCount >= 1` even at limit 0;
      slot successful via `bpFringeChunkEntries_getElem` +
      `fixedWidthNatTable_word_of_entry`, existence-level only).
      Multi-reader caveat doc-comments extended on
      `ReviewerSource.ProducedReadBy` (SuccinctFinalRAM) and the
      segment-leaf compat map (`ReviewerPhysical.lean`); no code change
      there.
- [x] M5 repeated-equal-read positional witnesses + manifest packet
      extension (REQ-B4-03): public
      `concreteBPNativeSuccinctRMQSelectChunk_repeated_equal_read_distinct_receipts`
      and
      `concreteBPNativeSuccinctRMQFringeChunk_repeated_equal_read_distinct_receipts`
      (singleton `[7]`, `left = 0, right = 1`: both select-close
      instructions evaluate the component at index 0; positions `p` and
      `prefixLen + p` with `p < prefixLen`; receipts via the generic
      occurrence packet), through shared private helper
      `reviewerSingleton_selectComponent_repeated_receipts` (two
      `ProducesEventAt` tuples + `global_getElem`; no whole-trace kernel
      evaluation).  `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`
      gains three fields
      (`fringe_chunk_table_every_reader_leaf_has_successful_closed_valid_occurrence`,
      `fringe_chunk_repeated_equal_read_occurrences_have_distinct_receipts`,
      `select_chunk_repeated_equal_read_occurrences_have_distinct_receipts`)
      discharged by the M4/M5 public theorems; packet doc extended;
      `Headlines/RMQ.lean` untouched (consumed by name, gains strength
      only).
- [x] M6 whole-query value dependency for segments 21/22 (REQ-B4-06):
      engine `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_ne_of_consumed_read_disagreement`
      + logical drop store
      `concreteBPNativeSuccinctRMQDropLogicalAddressStore` (+`_dropped`,
      `_agree_elsewhere`) in `SuccinctFinalStoreParam.lean`; NEW module
      `RMQ/Core/SuccinctFinal/RAM/ChargePolicyDependency.lean` with
      `concreteBPNativeSuccinctRMQ{FringeChunk,SelectChunk}ConsumedDisagreement_changes_wholeQuery`
      (∀-store form over the exhibited consumed read) and
      `...{FringeChunk,SelectChunk}Drop_changes_wholeQuery` (canonical
      store mutated only at the consumed address).  Projection level
      recorded honestly: full-TraceResult inequality with the consumed
      read exhibited; `.value` dependency carried by the closed
      component-level corruption witnesses (REQ-B2-10 / REQ-B3-12); the
      optional compiled value-probe fixture was SKIPPED (recorded; the
      checked theorems above are the row's closure objects, and `#guard`
      output would not be kernel evidence per INV-B4-CATEGORY-SEPARATION).
- [x] M7 charge-policy model doc section + adequacy doc sync (REQ-B4-07)
      and navigation doc repair + quarantine + DD-20260718-004
      (REQ-B4-08).  Nav audit outcome: no inconsistent statements; nav
      store maps 21/22 to the chunk/select tables; profile vs stories are
      two cost models with no registered bridge after the B3 deletion
      (quarantine note in `BP_NAVIGATION_FRONTIER.md`); stale story
      paragraph repaired (`concreteBPCloseNavigationCanonicalCosted`).
- [ ] M8 final battery + matrix closure + report.

## Verification ledger (B4)

(commands, exit codes, durations recorded per milestone)

- M1: docs only.
- M2: renames `concreteBPNativeSelectCloseInterpretedCosted_cost_le_thirteen`
  -> `concreteBPNativeSelectCloseRegisterInterpretedCosted_cost_le_thirteen`
  and `concreteBPNativeRankCloseInterpretedCosted_cost_le_four` ->
  `concreteBPNativeRankCloseRegisterInterpretedCosted_cost_le_four`
  (consumer check: repo-wide grep, zero consumers, no registry hits);
  `PAPER_CLAIM_CORRESPONDENCE.md` row 1 alias `SumLe142` -> `SumLe207`,
  row "typed 20-source universe" -> "22-source universe (23 logical
  segments)" + fresh segment 21 -> 23; REQ-B3-07 evidence wording "23
  sources" -> "22 sources (23 segments)"; stale docstrings
  (`SuccinctFinalRAM.lean` read-segment doc "0 through 20" -> "0 through
  22"; `ReviewerReachabilitySmall.lean` "thirteen" -> "fourteen" with the
  segment-22 witness noted); `RMQ_FINAL_ROADMAP.md` W19 paragraph counts;
  `Segments.lean` legacy `summary.minRel/maxRel := 21/22` shadowing-hazard
  NOTE.  `lake build RMQ` (mutex-held) exit 0, `Build completed
  successfully` (215 jobs).
- M6: `lake env lean RMQ/Core/SuccinctFinalStoreParam.lean` exit 0 first
  iteration (engine + drop store); `lake build
  RMQ.Core.SuccinctFinalStoreParam` exit 0 (136 jobs); `lake env lean
  .../ChargePolicyDependency.lean` exit 0 first iteration; module
  registered in `RMQ.lean` (NOTE: this newly pulls
  `ReviewerReachabilitySmall` into the RMQ root's direct import closure -
  it was previously reached only via the provenance seam; oleans existed,
  build unaffected); mutex-held `lake build RMQ` exit 0 (217 jobs,
  `Build completed successfully`).  M6 executed by B4-01 directly after
  the M6 subagent was aborted pre-edit (clean handover, zero edits;
  coordinator directive).
- M7: docs-only commit `57b4f8f` (PAPER_MODEL_ADEQUACY charge-policy
  section + 207/22-source/readWord-only sync; PAPER_CLAIM_CORRESPONDENCE
  W19 row packet-fields sync; BP_NAVIGATION_FRONTIER repair + quarantine;
  DD-20260718-004).
- M3: `lake env lean .../ChargedTableRegime.lean` exit 0 after 2
  iterations (fix: omega does not see the Nat-div atom's nonnegativity in
  `1 <= a + 1`-shaped goals here - use `Nat.le_add_left`); module
  registered in `RMQ.lean`; `lake build RMQ` exit 0 (216 jobs,
  incremental).  Toolchain note confirmed: `simp [Nat.log2]` evaluates
  concrete log2 literals (equation lemmas); bare `decide`/`rfl` does not.
- M4+M5: `lake build RMQ.Core.SuccinctFinalRAM
  RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical` (mutex-held) exit 0,
  pre-existing linter warnings only; `lake env lean
  RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.lean` exit 1
  (~27 s) then exit 0 (~29 s) after one fix round; `lake build RMQ`
  (mutex-held) exit 0, 216 jobs, 58 s, `Build completed successfully`.
  Toolchain notes for successors: (a) `rw [Nat.min_eq_left/_right]` does
  NOT match the `Nat.min` spelled by `bpWordChunkCount` (pattern is
  instance `min`) - discharge min-positivity term-level via
  `Nat.le_min.mpr` (defeq bridges `Nat.min`/`min`); (b) tactic
  `refine ⟨_, w, ?_⟩` cannot leave the ∃-index as a bare `_` when only a
  later `exact` would determine it - spell the witness slot; (c) after
  `rw [<.value fact>]` inside a `TraceResult.bind` continuation the beta
  step has often already happened, so a following `dsimp only` can fail
  with "no progress" - use `try dsimp only` (the match-iota step after the
  last scrutinee rewrite still needs it).

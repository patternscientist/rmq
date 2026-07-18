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
- [ ] M2 bookkeeping repairs commit (REQ-B4-01: correspondence-doc alias +
      counts, REQ-B3-07 wording, Register cost-lemma renames, stale
      docstrings, Segments.lean legacy-numeral comment, roadmap counts).
- [ ] M3 chunk-width corner + direct o(n) theorems (REQ-B4-04/05).
- [ ] M4 W19 per-segment corollaries + segment-21 per-leaf claims
      (REQ-B4-02).
- [ ] M5 repeated-equal-read positional witnesses + manifest packet
      extension (REQ-B4-03).
- [ ] M6 whole-query value dependency for segments 21/22 (REQ-B4-06).
- [ ] M7 charge-policy model doc section + adequacy doc sync (REQ-B4-07)
      and navigation doc repair + DD (REQ-B4-08).
- [ ] M8 final battery + matrix closure + report.

## Verification ledger (B4)

(commands, exit codes, durations recorded per milestone)

- M1: docs only.

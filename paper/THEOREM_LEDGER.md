# Theorem Ledger

Every mathematical claim in `paper/rmq.tex` carries an invisible
`\ledger{ID}` anchor; this file is the authoritative map from those IDs to
status, exact commit, Lean declaration and file (when formalized), and a
proposition-level statement. `paper/check_paper.ps1` enforces bidirectional
coverage between the manuscript anchors and the IDs below.

Status vocabulary (fixed):

- **ACCEPTED_BASE** -- kernel-checked declaration present on the base commit
  `3849ecbb53bbedfcd679352cc68d095fa5a304c2` and part of the integrated
  mainline theorem surface. Where the project's internal acceptance process
  has a finer status (for example a still-open fresh-blind audit), the row
  says so in its notes; that is a process status, not a kernel status.
  Row `L-PQ-01` keeps this mathematical source pin; its later source-equivalent
  lineage has coordinator acceptance after both-host gates and independent
  audit. Its `Process status` line cites that separate acceptance record.
  The older source pin itself is not presented as an audit or merge receipt.
- **PROVISIONAL_ARCHITECTURE** -- a frozen target statement under an active
  feasibility gate. Not a theorem. May appear in the manuscript only at a
  marked insertion point and in the target-statement environment that quotes
  it as a target. **No row currently holds this status** (the architecture row
  moved to ACCEPTED_BASE on Stage-A acceptance and was absorbed as a theorem in
  the RC-4 round), so this clause describes a shape available to a future
  target rather than anything in the manuscript now; there is no marked
  insertion point at this commit.
- **OPEN** -- a statement the repository does not prove and the manuscript
  asserts only as unproved/unclaimed.

Worker prose, audit narratives, and rejected candidates are process
evidence only; no row below cites them as proof. All file paths and line
references are at the base commit.

---

## Reference semantics

#### L-REF-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.leftmostArgMin_unique`
- File: `RMQ/Core/Spec.lean` (definition of `LeftmostArgMin` at :34,
  uniqueness at :48)
- Proposition: for all `xs : List Int` and naturals `left right i j`, if
  `LeftmostArgMin xs left right i` and `LeftmostArgMin xs left right j`
  then `i = j`. (`LeftmostArgMin xs left right idx` unfolds to:
  `left < right`, `right <= xs.length`, `left <= idx < right`, and there is
  `v` with `xs[idx]? = some v`, `v <= w` for every in-window value `w`, and
  `v < w` for every value at a position strictly left of `idx` in the
  window.)
- Manuscript location: Section 2, Lemma 2.3 (`lem:unique`).

#### L-REF-02
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.scanWindow_cartesianShape_representative_eq`
- File: `RMQ/Core/SuccinctRMQClassic.lean` (:1198); supporting reduction
  layers in `RMQ/Core/Cartesian.lean`, `RMQ/Core/LCA.lean`,
  `RMQ/Core/PlusMinusOne.lean`, `RMQ/Core/Reduction.lean`
- Proposition: for all `xs : List Int` and `left len : Nat` with `0 < len`
  and `left + len <= xs.length`,
  `scanWindow (cartesianShape xs).representative left len =
  scanWindow xs left len`; that is, the canonical representative of the
  Cartesian shape of `xs` has the same reference RMQ answers as `xs`, so a
  representation may discard values and retain shape.
- Manuscript location: Section 2, closing paragraph (shape sufficiency).

## Succinct upper bound: space

#### L-UB-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.buildPayload_length`; public aliases
  `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery`,
  `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`
- File: `RMQ/Core/SuccinctRMQClassic.lean` (:1240); `RMQ/Headlines/RMQ.lean`
- Proposition: for every `xs : List Int`,
  `(buildPayload xs).length <= 2 * xs.length + overhead xs.length`, where
  `overhead` is one closed function of the length and `buildPayload xs :
  List Bool` is the advertised payload. No padding forces an equality; the
  count excludes proof-only fields by construction.
- Manuscript location: Section 1.1 item 2; Section 5.2, Theorem 5.1
  (`thm:payload`).

#### L-UB-02
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.overhead_littleO`; predicate
  `RMQ.SuccinctSpace.LittleOLinear`
- File: `RMQ/Core/SuccinctRMQClassic.lean` (:1233);
  `RMQ/Core/SuccinctSpace/Asymptotics.lean` (:22)
- Proposition: `LittleOLinear overhead`, where
  `LittleOLinear f := forall scale, 0 < scale -> exists threshold,
  forall n, threshold <= n -> scale * f n <= n`. This is the repository's
  Mathlib-free integer form of `overhead = o(n)`.
- Manuscript location: Section 5.2, Theorem 5.2 (`thm:littleo`).

## Succinct upper bound: correctness

#### L-UB-03
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal`;
  packaged by `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`
- File: `RMQ/Core/SuccinctRMQClassic.lean`; `RMQ/Headlines/RMQ.lean`
- Proposition: for every `xs`, `left`, `right` with
  `ValidRange xs left right` (`left < right /\ right <= xs.length`), and
  every supplied store agreeing with the canonical global store
  `SuccinctClassic.globalReadStore xs` on the final checked footprint, the
  supplied-store query erases to `some i` where `i` satisfies
  `LeftmostArgMin xs left right i`. Instantiating the canonical store gives
  the unconditional exactness of the public query.
- Manuscript location: Section 5.3, Theorem 5.3 (`thm:exact`).

#### L-UB-04
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.queryCosted_invalid` (:256),
  `queryCosted_empty_range` (:369), `queryCosted_reversed_range` (:376),
  `queryCosted_out_of_bounds` (:385); plus the corresponding
  trace/supplied-store/physical invalid theorems
- File: `RMQ/Core/SuccinctRMQClassic.lean`
- Proposition: if `not (ValidRange xs left right)` -- in particular for
  empty (`left = right`), reversed (`right < left`), or out-of-bounds
  (`xs.length < right`) ranges -- the query value is `none`, uniformly
  across the plain, costed, trace, and supplied-store surfaces.
- Manuscript location: Section 5.3, Theorem 5.4 (`thm:invalid`).

## Succinct upper bound: modeled cost

#### L-UB-05
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.queryCosted_cost_le` (:1282),
  `RMQ.SuccinctClassic.queryCost_eq : queryCost = 210` (:114);
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
- File: `RMQ/Core/SuccinctRMQClassic.lean`; `RMQ/Core/SuccinctFinalRAM.lean`
- Proposition: for every `xs left right`,
  `(queryCosted xs left right).cost <= queryCost`, and `queryCost = 210`
  by checked equality, uniformly for all sizes (no size premise). Cost is
  in the repository's charged-trace model: attempted payload-word reads
  are charged one tick each and nothing else is charged.
- Manuscript location: Section 5.4, Theorem 5.5 (`thm:cost`).

#### L-UB-06
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.SuccinctClassic.chargedTraceCostAlgebra` (abbrev of
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra`);
  frozen historical identity
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq`
  (`= 207`, `RMQ/Core/SuccinctFinalRAM.lean` :8269)
- File: `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/SuccinctRMQClassic.lean`
- Proposition: the constant satisfies the named component algebra
  `2*35 + (2*11 + 2*37 + 33) + 11 = 210` (two select legs at 35, a
  close/LCA leg with two rank seeds at 11, two fringe windows at 37 and one
  interior pass at 33, plus one final rank at 11), derived from
  per-component cap theorems rather than asserted; the superseded
  event-silent literal `207` remains pinned by a separate frozen equality
  theorem so a later recharge cannot silently rewrite the record.
- Manuscript location: Section 5.4, Theorem 5.6 (`thm:algebra`) and
  Remark 5.10 (`rem:constant-moved`).

#### L-UB-07
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`;
  alias `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`
- File: `RMQ/Core/SuccinctFinalRAM.lean`
- Proposition: for every shape and query, every event of the canonical
  whole-query global word trace is a `WordRAM.TraceEvent.readWord`
  constructor (an attempted read of one word of the modeled store,
  successful or failed); no other event constructor occurs.
- Manuscript location: Section 5.4, Theorem 5.7 (`thm:readword`).

#### L-UB-08
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story`;
  flat-payload strengthening
  `...WholeQueryFlatPayloadStore_noSynthetic_execution_story`; list-facing
  alias `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory`
- File: `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Headlines/RMQ.lean`
- Proposition: the dedicated `TraceEvent.syntheticCostOnlyPrimitive`
  constructor (used historically by `TraceResult.ofCosted` to migrate
  aggregate costs) does not occur anywhere in the canonical all-size global
  query trace.
- Manuscript location: Section 5.4, Theorem 5.8 (`thm:nosynthetic`).

#### L-UB-09
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210`
  with the sum-equals-length and sum-equals-cost companions; counterfactual
  `RMQ.WordRAM.TraceEvent.sum_nonSyntheticWeight_ne_length_of_synthetic_mem`
  (`RMQ/Core/WordRAM.lean` :280)
- File: `RMQ/Core/SuccinctFinalRAM.lean`; `RMQ/Core/WordRAM.lean`
- Proposition: on the canonical no-synthetic trace, the
  `nonSyntheticWeight` certificate sum equals the emitted trace length and
  equals the `Costed` cost of the same execution, and is at most `210`;
  inserting a synthetic event anywhere in any trace makes the certificate
  sum differ from the trace length.
- Manuscript location: Section 5.4, Theorem 5.9 (`thm:weight`).

#### L-UB-19
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `bpChunkedSameBlockCloseSeededCosted_cost_le : cost <= 37`
  (`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedSameBlockChunks.lean`);
  the 33-chunk fringe cap identities
  (`.../ChargedFringeChunks.lean`); the 8-chunks-per-word cap and regime
  identities (`.../ChargedWordChunks.lean`, `.../ChargedTableRegime.lean`)
- File: `RMQ/Core/SuccinctClose/RelativeRmmMacro/`
- Proposition: each endpoint-fringe window is charged at most 4 window-word
  reads plus at most 33 chunk-table reads (cap 37), the chunk counter being
  capped at `Nat.min (relHi / c + 1) 33`; at most 8 chunks fit one machine
  word; the same-block close leg is charged by the same chunk fold with the
  same cap 37, with no size hypothesis (so the caps hold at
  `n = 0, 1, 2`). Consequently every uncharged step on the accepted route
  is a bounded-per-step register computation between charged reads; no
  input-size-dependent event-silent loop remains.
- Manuscript location: Section 3 (charge-policy paragraph); Section 5.4
  (bounded uncharged remainder paragraph).

## Execution-model adequacy

#### L-UB-10
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases`;
  alias `RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload`
- File: `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`
- Proposition: the erasure (flattened bit contents) of the one
  pre-execution physical word list -- assembled from the exhaustive typed
  universe of 22 physical sources covering the 23 logical segments `0..22`,
  BP roles 0 and 19 sharing one physical source -- is exactly the public
  `buildPayload`. This is an equality of payload bit contents, not an
  allocated-cell or padded-capacity statement.
- Manuscript location: Section 6.1.

#### L-UB-11
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical`;
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter`;
  aliases `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical`,
  `RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter`
- File: `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`;
  `RMQ/Core/SuccinctFinalStoreParam.lean`
- Proposition: the supplied-store evaluator reads the caller's flat store
  through a checked address-translation adapter, and canonical
  flat-physical execution refines logical execution preserving decoded
  result, modeled cost, ordered successful and failed reads, repeated
  reads, and the execution-derived footprint.
- Manuscript location: Section 6.2, first paragraph.

#### L-UB-12
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint`;
  list-facing
  `RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
  (:1298)
- File: `RMQ/Core/SuccinctFinalStoreParam.lean`;
  `RMQ/Core/SuccinctRMQClassic.lean`
- Proposition: if two stores agree on the first physical execution's
  consumed ordered read footprint, the complete physical `TraceResult` --
  ordered trace including failures and repetitions, and the returned value
  -- is identical. The footprint is execution-derived (the ordered read
  projection), not an assumed layout.
- Manuscript location: Section 6.2, Theorem 6.1 (`thm:footprint`).

#### L-UB-18
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal`;
  `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal`;
  aliases `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal`,
  `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal`
- File: `RMQ/Core/SuccinctRMQClassic.lean`; `RMQ/Headlines/RMQ.lean`
- Proposition: under footprint agreement with the canonical global store,
  the supplied-store query preserves the exact RMQ answer (valid windows
  erase to the leftmost reference answer) and its modeled cost is at most
  `SuccinctClassic.queryCost` -- i.e. exactness and the `210` bound
  transfer to any footprint-agreeing caller store.
- Manuscript location: Section 6.2, Theorem 6.1 (`thm:footprint`,
  list-facing corollary clause).

#### L-UB-13
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne`
  with `..._value_eq_suppliedStoreEvaluator`; the six validation guards
- File: `RMQ/Core/SuccinctFinalStoreParam.lean`;
  `RMQ/Validation/SuccinctClassic.lean`
- Proposition: the physical answer is exactly the translated
  supplied-store evaluator value at `.value`; differing translated
  evaluator values force differing physical answers; and one checked
  decisive singleton corruption -- consumed logical segment `21`, index
  `3`, five-bit LE encoding of `1` replaced by the five-bit LE encoding of
  `4` -- changes the whole-query answer from `some 0` to `none`. This is
  the anti-vacuity witness that the store is genuinely observed.
- Manuscript location: Section 6.2, Theorem 6.2 (`thm:corruption`).

#### L-UB-14
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global`;
  alias
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal`
- File: `RMQ/Core/SuccinctFinalStoreParam.lean`
- Proposition: under footprint agreement with the canonical global store,
  every successful read event `readWord segment index (some word)` in the
  supplied-store replay has its segment counted in the final flat payload
  and carries explicit flat-payload backing evidence for
  `(segment, index, word)`; answers cannot be fed from proof-only fields or
  uncounted certificates.
- Manuscript location: Section 6.2, Theorem 6.3 (`thm:backing`).

#### L-UB-17
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace_getElem?_producer`,
  `...evalGlobalWordTrace_getElem?_read_invocation`,
  `...WholeQueryOccurrenceProvenance_checked`; alias
  `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance`
- File: `RMQ/Core/SuccinctFinalRAM.lean`;
  `RMQ/Core/SuccinctFinal/RAM/ReviewerReachability*.lean`
- Proposition: for the exact current query, every indexed read of the
  global trace retains its global position, producing program-instruction
  occurrence, folded prefix state, component-local position, exact
  invocation parameters, physical source, and a multiplicity-preserving
  embedding into the composed trace.
- Manuscript location: Section 6.3, first paragraph.

#### L-UB-15
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy`
  with `...ReviewerSource_counted_successful_closed_valid_occurrence`,
  `...ReviewerSharedBPConsumer_successful_closed_valid_occurrence`,
  `ReviewerProducerClaim.hasOperationalProducer_of_successful`,
  `...FreshUnusedCanonicalSource_no_producer`,
  `...ReviewerSource_region_injective`, `...ReviewerSegmentSource?_coverage`;
  alias `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy`
- File: `RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean`;
  `RMQ/Core/SuccinctFinalRAM.lean`
- Proposition: query-independently, every counted source and every named
  shared-BP consumer has a successful occurrence through some actual closed
  whole-query execution under a valid `List Int` query; the successful
  positive predicate implies the common mutation-side predicate; a
  counterfactual fresh segment `23` (with a plausible existing label) fails
  that predicate; source regions are exclusive, logical-segment coverage is
  complete, and legacy duplicate close/interior sources are excluded. The
  packet does not claim the current query reads every source.
- Manuscript location: Section 6.3, second paragraph.

#### L-UB-16
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `concreteBPNativeSuccinctRMQReviewerWordBits` (definition,
  `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean` :1474) with the
  bound theorems behind aliases
  `RMQ.Headlines.succinctRMQReviewerWordBitsLogarithmic`,
  `...ReviewerPhysicalWordsFitLinearCapacity`, `...ReviewerPhysicalWordFits`,
  `...ReviewerSuccessfulReadWordFits`, `...ReviewerPhysicalFootprintAddressFits`
- File: `RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`;
  `RMQ/Headlines/RMQ.lean`
- Proposition: the query-independent width
  `reviewerWordBits n = machineWordBits (400000 * (n + 1))` satisfies the
  checked all-size inequality
  `reviewerWordBits n <= 20 * (Nat.log2 (n + 2) + 1)` and bounds every
  stored/returned word, translated live or dead address, segment encoding,
  query operand, primitive operand/result, and consumed footprint address;
  the whole-query capacity is linear.
- Manuscript location: Section 6.4, first paragraph.

#### L-UB-20
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed`
  (24-field certificate),
  `...ReviewerMachineRequiredFacts` (independent expected-type consumer),
  `RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy` (guarded list packet);
  aliases `RMQ.Headlines.succinctRMQReviewerMachineWellFormed`,
  `...RequiredFacts`, `RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy`
- File: `RMQ/Core/SuccinctFinalModelAdequacy.lean`;
  `RMQ/Core/SuccinctRMQClassic.lean`
- Proposition: the adequacy facts are collected in one 24-field certificate
  over the same payload, physical store, trace, footprint, backing, and
  controller objects, whose cost field is the direct proposition
  `sum (map nonSyntheticWeight trace) <= 210` over the same canonical
  execution; an independent record consumes every certificate field by
  literal projection; a guarded packet lifts the exact objects to the
  `List Int` surface under `ValidRange`; and the paper-facing main theorem
  obtains its cost clause by projecting the certificate, not by restating a
  numeral.
- Manuscript location: Section 6.4, second paragraph.

## Lower bound

#### L-LB-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`
  (:1878); `doubledLogSlackLower` (:1654); alias
  `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack`
- File: `RMQ/Core/EncodingLowerBound.lean`; `RMQ/Headlines/RMQ.lean`
- Proposition: for every `n`: (a) for every `bits` and every
  `ExactRMQStateEncoding n bits`,
  `doubledLogSlackLower n <= 2 * bits`, where
  `doubledLogSlackLower n = 4*n - (3 * Nat.log2 (2*n+1) + 3)`;
  (b) for every encoding whose on-domain built states charge at most
  `budget` payload bits (over all shapes in `shapesOfSize n`),
  `doubledLogSlackLower n <= 2 * budget`; (c) there exists an
  `ExactRMQStateEncoding n (2*n)` whose built state charges exactly `2*n`
  payload bits on every representative shape of size `n`. Halving gives
  the familiar `2n - 1.5 log2 n - O(1)` reading.
- Manuscript location: Section 4, Theorem 4.1 (`thm:lower`); Section 1.1
  item 4.

#### L-LB-02
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound`
  (:1840); `logSlackLower` (:1650)
- File: `RMQ/Core/EncodingLowerBound.lean`
- Proposition: undoubled variant with the weaker slack: every
  `ExactRMQStateEncoding n bits` has
  `logSlackLower n <= bits` where
  `logSlackLower n = 2*n - (2 * Nat.log2 (2*n+1) + 2)`; the same lower
  bound applies to any uniform charged payload budget; and the canonical
  representative decoder witnesses budget `2*n` exactly.
- Manuscript location: Section 4, paragraph after Theorem 4.1.

## Reusable spokes

#### L-RS-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` (:244);
  headline alias `RMQ.Headlines.rankSelectNPlusOConstantQuery`
- File: `RMQ/Core/RankSelectPublic/Capstones.lean`
- Proposition: a standalone plain-bitvector rank/select family with
  stored-bit access, exact rank, exact select, counted payload length
  `n + overhead n` with `LittleOLinear overhead`, and a constant modeled
  query-cost bound.
- Manuscript location: Section 5.5, first spoke.

#### L-RS-02
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile`;
  interpreted replay
  `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile`
- File: `RMQ/Core/RankSelectPublic/Capstones.lean`;
  `RMQ/Core/RankSelectPublicRAM.lean`
- Proposition: for every `bits : List Bool`, a fixed-weight compressed/FID
  rank/select family counting the enumerative fixed-weight primary payload
  plus `o(n)` auxiliary payload, with exact access, rank, and select under
  one uniform modeled constant query bound; the interpreted replay routes
  the charged access/rank/select reads through the first-order word-RAM
  bridge layer with the same payload and profile shape.
- Manuscript location: Section 5.5, second spoke.

#### L-BP-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: `RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile`
  (:1666); headline alias `RMQ.Headlines.concreteBPCloseNavigationProfile`
- File: `RMQ/Core/BPNavigationPublic.lean`
- Proposition: the concrete BP close-navigation layer consumed by the RMQ
  path has `o(n)` auxiliary close-navigation payload, constant modeled
  query cost, exact answer-close semantics for Cartesian-shape RMQ queries
  supplied with exact endpoint close positions, and
  machine-word-bounded component payload reads. It is not a complete
  succinct tree-navigation library.
- Manuscript location: Section 5.5, third spoke.

## Packed cell-probe architecture

#### L-ARCH-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration:
  `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone`
  (39-field structure), discharged for every input list and endpoint pair by
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds`
- File: `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
  (structure at :300, producer at :760)
- Status history: this row was `PROVISIONAL_ARCHITECTURE` while the
  substrate was pinned to base `1490c97b...` and the Stage F feasibility
  gate was open. The gate closed and Stage A was recorded `ACCEPTED` on
  2026-08-07, after a fresh-blind exact-commit audit and a coordinator
  reconstruction in which every finding was independently reproduced.
  Re-pinning this substrate to base `e3362d4f...` is what moves the row to
  `ACCEPTED_BASE`; the mathematics did not change under it.
- Amended 2026-08-09 (repin to `688c54a3...`): this row's reading rules
  previously called the packed `210` "logical fuel (charged trace events)",
  merging it with the charged-trace budget. That wording is **retracted**; the
  two `210`s are distinct and the distinction is now a checked property
  (`scripts/independence_check.lean`, gate step 3b). The amendment corrects a
  gloss, not the proposition, and the row was **not** re-audited -- the
  fresh-blind audit of `audit-v1-rc-1` is what stands behind the proposition.
- Manuscript status (corrected 2026-08-16, RC-4): the accepted statement **is
  absorbed**. `rmq.tex` Section 9 states it as a theorem with the constant
  `427` (`Theorem~\ref{thm:packed}`), there is no
  `ARCHITECTURE_RESULT_PENDING` marker anywhere in the manuscript, and
  `check_paper.ps1` permits at most one rather than requiring exactly one.
  The result appears in exactly two places -- the allocated-bits entry of
  Section 3 and Section 9 -- and nowhere else.

  The previous wording ("not yet absorbed", "the single marked insertion point
  still holds the marker", "an editorial gap") was false at this commit and
  survived the round that performed the absorption: neither correction commit
  touched this file. That is the same defect the round exists to answer,
  standing in the ledger whose job is to bind manuscript claims to Lean
  declarations. Found by audit, not by the round.
- Proposition: for every input list of
  length `n`, preprocessing constructs one read-only array of exact-width
  `w(n)`-bit cells with checked all-size width bounds; the complete
  allocated capacity, including a constant serialized header and final-cell
  padding, is at most `2n + rho(n)` bits for a checked little-o-linear
  `rho`; and for every valid half-open query a closed uniform controller
  with dynamic inputs exactly `n`, the endpoints, and prior probe replies
  returns the leftmost minimum index after at most `C` adaptive probes for
  one exact constant `C` independent of `n`. Computation between probes is
  free (cell-probe convention).
- Scope discipline, unchanged by acceptance: `427` is an upper bound derived
  from the run's own measure, not an attainment claim; and this is a
  cell-probe result, so it is not word-RAM instruction time, not preprocessing
  time, and not measured runtime. Computation between probes is free.
- **The two `210`s are different quantities.** The `210` inside
  `427 = 1 + 2*3 + 2*210` is the packed controller's own **structural
  countdown**, assembled from controller-state counters in
  `ReviewerWholeProtocol.lean` and proved by
  `packedReviewerControllerMeasure_valid_eq_427`. It is **not** the
  charged-trace event budget of `SuccinctFinalRAM.lean`. They are numerically
  equal and independent at declaration and proof-term level: the packed proof
  references neither `SuccinctClassic.queryCost` nor `nonSyntheticWeight`.
  This row previously called the packed `210` "logical fuel (charged trace
  events)", which merged the two; that wording is retired here. Note the
  independence claim is about declarations and proof terms, not module
  closures -- the packed module's compilation closure does transitively reach
  the charged declaration.
- Manuscript location: Section 9, stated as a theorem with label
  `thm:packed`. The Section 9.1 insertion point is gone: the block labelled
  `sec:insertion` now records only that the pending marker previously standing
  there has been removed, and the `ARCHITECTURE_RESULT_PENDING` count in
  `rmq.tex` is zero. No line numbers are given here: this file's `:NNN`
  citations are Lean source pointers, checked by `check_citations.ps1`, and a
  manuscript line number would be parsed as one.

#### L-PACK-01
- Status: ACCEPTED_BASE
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: field 8 `allocation_two_n_plus_rho` of
  `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone`,
  with field 9 `rho_little_o`; inhabited by
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds`
- File: `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
  (field 8 at :356--359, field 9 at :361, producer at :760)
- Proposition: for every `xs : List Int`, letting
  `shape := SuccinctClassic.cartesianShape xs`, the complete allocated
  capacity of the packed memory satisfies
  `(packedReviewerMemory shape).length * packedReviewerCellWidth shape.size
  <= 2 * shape.size + packedReviewerRho shape.size`, with
  `SuccinctSpace.LittleOLinear packedReviewerRho`. The field's own docstring
  names the covered objects as the header cell, every payload cell, and
  final padding at full cell width.
- Supersedes: `L-OPEN-03`, retired at this base. That row asserted that no
  current theorem bounds allocated capacity, which this declaration
  falsifies. Two manuscript sentences anchored to it (the allocated-bits
  entry of Section 3 and limitation 1 of Section 11) were repaired in the
  same edit; the limitation was withdrawn outright.
- Manuscript location: Section 3, allocated-bits item.

## Fully charged packed query

#### L-PQ-01
- Status: ACCEPTED_BASE
- Process status: ACCEPTED. The mathematical declarations are kernel-checked
  at the base pin and exported through `RMQPaper`. The source-equivalent
  repaired lineage `6562ff6` passed the full committed replay and aggregate
  gates under PowerShell 7 and Windows PowerShell 5.1. A fresh blind audit at
  `4c89378` and its narrow tooling correction review support coordinator
  acceptance in `docs/internal/packed_query/PQ1_COORDINATOR_ACCEPTANCE.md`.
  The later follow-up changes terminology and process status only.
  `paper/README.md` editing rule 5 lists the synchronized status surfaces.
- Commit: `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
- Declaration: structure
  `RMQ.SuccinctFinal.PackedWordRAM.FullyChargedPackedQueryCapstone`,
  discharged with no premise by
  `RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds`;
  public alias `RMQ.Headlines.succinctRMQFullyChargedPackedQuery`
- File: `RMQ/Core/WordRAM/Packed/Capstone.lean`; `RMQ/Headlines/RMQ.lean`;
  typed client `RMQ/Validation/PackedQueryContract.lean`. No line numbers are
  given: the declaration names are the stable pointer, and the capstone was
  still gaining fields when this row was written, so a line pointer into it
  would rot on the next edit above it.
- Proposition: fix `xs : List Int`, `n = xs.length`,
  `w = wordWidth n = 32 + 8 * packedReviewerCellWidth n`, the allocation
  `buildMemory xs` (174 metadata words followed by the packed reviewer memory
  of L-ARCH-01, header and padding included, densely repacked into `w`-bit
  words) and the closed program `queryProgram`, which takes no argument.
  (width) `Nat.log2 (n + 2) + 1 <= w <= 192 * (Nat.log2 (n + 2) + 1)`; every
  word of `buildMemory xs` and every address up to its length is below
  `2 ^ w`; every encoded field of every instruction of `queryProgram`,
  dormant ones included, is below `2 ^ wordWidth m` for every `m`.
  (space) `(buildMemory xs).length * w <= 2 * n + allocationRho n` and
  `((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length + (queryRegisterCount + 3)) * w <= 2 * n + queryCompleteRho n`,
  with `LittleOLinear allocationRho` and `LittleOLinear queryCompleteRho`.
  (program) `queryBudget = 837572` and `queryProgram.length = queryBudget`;
  the encoded program has at most `5 * queryBudget` words;
  `queryRegisterCount = 8271` and `queryScratchWords = 8274`; every register
  at index `>= 8271` is `0` after any fuel.
  (inputs) every `ValidRange xs left right` pair is below `2 ^ w` and is
  accepted by `encodeInputs`; the total wrapper satisfies
  `queryNat (buildMemory xs) n left right = if ValidRange xs left right then some (scanWindow xs left (right - left)) else none`,
  and each of its `some` results is a `LeftmostArgMin` index. Endpoints at or
  above `2 ^ w` are rejected by `encodeInputs`, a value-level test with no
  instruction cost.
  (run) for `left` and `right` below `2 ^ w`, the run with fuel `queryBudget`
  from `initialState n left right` halts with value
  `optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value`.
  On every valid range its result is
  `some (scanWindow xs left (right - left) + 1)`, stated on the run itself
  (field `specResult`); on a representable invalid range its result is
  `some 0` and it performs no load; on every invalid range it takes at most
  6 steps (field `invalidGuardSteps`, which has no representability
  premise; for endpoints at or above `2 ^ w` it is a fact about the
  unbounded evaluator, since `encodeInputs` rejects them before the machine
  starts). Its step count is at most `queryBudget` and equals the sum of its
  six category counts; both facts hold for every fuel-bounded run, so the
  budget's content is the halting clause. For representable endpoints every prefix state, every executed
  transition (`Instruction.Safe`: result below `2 ^ w`, no subtraction
  underflow, no zero divisor, no shift amount of `w` or more) and every
  receipt address and reply fits `w`.
  (reads) every receipt comes from a `load` at the actual prefix state whose
  address register holds the receipt address, and its reply is
  `(buildMemory xs)[address]?`; the ordered receipts are the 174 metadata
  reads followed by `logicalTraceReads` of the canonical trace
  `(SuccinctClassic.queryTraceResult xs left right).trace` on valid ranges,
  and empty otherwise; that trace is read-only (`ReadOnlyTrace`); by the
  definitions of `readerReceipts` and `spanAttemptReceipts`, a logical read
  with no stored span or a zero-length one makes no load, and any other
  makes one load, or two when its span crosses a `w`-bit word boundary and
  the first load has a reply; on every valid range every receipt has a
  reply (field `noFailedLoads`); any memory agreeing with `buildMemory xs`
  at every receipt address yields the identical `Run`.
- Model: numeric memory and a register machine with nine instruction
  constructors (`load`, `constant`, `move`, `arithmetic` over
  add/sub/mul/div/mod/shl/shr/and/or/xor, `comparison` over lt/le/eq, `jump`,
  `jumpRegister`, `branchZero`, `halt`) and no store; one step per executed
  instruction; a failed load faults and is logged. Unit-cost multiplication,
  division, remainder, variable shifts and bitwise operations are
  assumptions of the model. Division and remainder go beyond the
  multiplication model of the cited word-RAM literature and are stated as an
  explicit assumption; the span decoder needs them. Sources are in the
  manuscript's Section 9.2 and their receipts in `RELATED_WORK_LEDGER.md`
  (word-RAM instruction-set authority).
- Scope discipline: `837572` is an input-independent upper bound equal to the
  program's length and the run's fuel; it is not an optimized constant and
  not claimed attained (L-OPEN-07). It is a primitive-instruction bound for
  this execution only and must never be attached to the charged-trace bound
  of L-UB-05 or the probe cap of L-ARCH-01, which keep their models. The
  program and register-bank share of the complete capacity is lower order
  only asymptotically: the encoding has at least two words per instruction (a
  tag and an operand, by the definition of `Instruction.encoding`), so that
  share exceeds `n` for every `n` below `2 ^ 28`. That threshold is
  arithmetic from the definitions, not a Lean theorem: `wordWidth n` is at
  least `48 + 8 * Nat.log2 (n + 1)` because `packedReviewerCellWidth n` is
  `machineWordBits` of a bound at least `2 * n + 2`. Preprocessing is
  unbounded and unclaimed (L-OPEN-01). Nothing is claimed about compiled
  code, hardware or the Lean evaluator's wall-clock time.
- Relation to other rows: not independent of them at proof level. The run's
  loads expand the reads of the canonical trace of L-UB-07 and L-UB-09, and
  its allocation repacks the memory of L-ARCH-01; it restates neither. It
  falsifies the first clause of L-OPEN-06 as worded before 2026-09-11; that
  row is amended, not retired, because its remaining clause is still an
  unclaimed statement.
- Manuscript location: Section 1.1, item 6; Section 1.2; Section 3
  (allocated-bits entry, executed-instructions item, model non-claims
  paragraph); Section 9.2, Theorem 9.2 (`thm:fullycharged`) and the fourth
  reading it does not license (the `2 ^ 28` threshold); Section 11, item 1.
  Also summarized without an anchor in the abstract, Section 1.1 (lead-in),
  Section 1.3, Section 7 (import discipline), Section 8, the second reading
  of Theorem 9.1 in Section 9, the rest of Section 9.2 (machine, model
  sources, the other readings and the status paragraph), Section 10
  (mechanized cost analysis paragraph), Section 11 items 3 and 6 and
  Section 12.

## Open statements (asserted only as unproved)

#### L-OPEN-01
- Status: OPEN
- Statement: the construction's preprocessing complexity -- time and
  workspace, in any model -- is unproved; no theorem bounds it and the
  manuscript claims nothing about it.
- Manuscript location: Section 11, item 2.

#### L-OPEN-02
- Status: OPEN
- Statement: global minimality of the constant `210` across component
  correlations is unproved. The repository has component-wise **upper**
  caps and one exact reachable interior-cost-33 witness, but no theorem
  that a smaller whole-query constant is impossible for this
  representation and charge policy. Only the interior `33` is witnessed as
  attained; the select `35`, rank `11`, endpoint-fringe `37`, and the
  aggregate `210` are upper bounds with no attainment witness.
- Amended 2026-08-12: this row said "a tight component-wise cap", claiming
  tightness for four caps never shown tight. The source comment on
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra`
  was corrected on 2026-08-09 without syncing this row or the other two
  surfaces repeating it; the fresh-blind audit of `audit-v1-rc-2` caught
  the gap. The row's OPEN status and proposition are otherwise unchanged.
- Manuscript location: Section 11, item 3.

#### L-OPEN-04
- Status: OPEN
- Statement: the `overhead` envelope of L-UB-01/L-UB-02 is proved
  little-o-linear but not proved tight; no reachable input family is shown
  to attain it, and no comparison with Fischer-Heun redundancy is claimed.
- Manuscript location: Section 5.2 (closing paragraph); Section 11, item 4.

#### L-OPEN-05
- Status: OPEN
- Statement: the cell-probe redundancy lower bounds for succinct RMQ
  (Liu-Yu 2020; Liu 2021) are not mechanized in this repository; the
  mechanized lower bound is the information-theoretic counting bound
  L-LB-01, and the manuscript cites the cell-probe bounds as related work
  only.
- Manuscript location: Section 4 (scope paragraph); Section 11, item 5.

#### L-OPEN-06
- Status: OPEN
- Statement: the charged-trace bound of L-UB-05 and the cell-probe bound of
  L-ARCH-01 charge only attempted reads and attempted probes. Neither counts
  controller dispatch, decoding, arithmetic, comparison or branching steps,
  and neither is claimed as running time in the conventional word-RAM model;
  the `210` bound is a charged-trace bound only. L-PQ-01 counts such steps
  for a different program on a different allocation; it bounds its own run
  and converts neither bound into an instruction count.
- Amended 2026-09-11 (repin to `3849ecbb`): this row said that no
  instruction-level machine charges those steps and simulates the same
  execution, and that consequently no word-RAM running-time claim is made.
  At this base L-PQ-01 is such a machine, for a different program and
  allocation whose loads expand the canonical trace's reads, so that first
  clause is false. The row now states only what remains unclaimed. Its OPEN
  status and its two manuscript anchors are unchanged.
- Manuscript location: Section 3 (model non-claims paragraph); Section 11,
  item 1.

#### L-OPEN-07
- Status: OPEN
- Statement: optimality and attainment of the instruction budget of L-PQ-01
  are unproved. `queryBudget = 837572` is the length of `queryProgram` and
  the fuel of the run; the capstone proves that the run halts within that
  fuel for endpoints below `2 ^ wordWidth n`, `n` the input length (fields
  `halt` and `result`; every valid query's endpoints are below it), but no
  theorem shows that any
  run takes 837572 steps, that a smaller
  uniform budget holds, or that the program is minimal. The program was not
  optimized, and the manuscript claims nothing about the budget beyond the
  upper bound.
- Manuscript location: Section 9.2 (first reading the theorem does not
  license); Section 11, item 3.

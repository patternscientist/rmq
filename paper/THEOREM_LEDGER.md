# Theorem Ledger

Every mathematical claim in `paper/rmq.tex` carries an invisible
`\ledger{ID}` anchor; this file is the authoritative map from those IDs to
status, exact commit, Lean declaration and file (when formalized), and a
proposition-level statement. `paper/check_paper.ps1` enforces bidirectional
coverage between the manuscript anchors and the IDs below.

Status vocabulary (fixed):

- **ACCEPTED_BASE** -- kernel-checked declaration present on the base commit
  `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82` and part of the integrated
  mainline theorem surface. Where the project's internal acceptance process
  has a finer status (for example a still-open fresh-blind audit), the row
  says so in its notes; that is a process status, not a kernel status.
- **PROVISIONAL_ARCHITECTURE** -- a frozen target statement under an active
  feasibility gate. Not a theorem. May appear in the manuscript only at the
  single marked insertion point and in the target-statement environment
  that quotes it as a target.
- **OPEN** -- a statement the repository does not prove and the manuscript
  asserts only as unproved/unclaimed.

Worker prose, audit narratives, and rejected candidates are process
evidence only; no row below cites them as proof. All file paths and line
references are at the base commit.

---

## Reference semantics

#### L-REF-01
- Status: ACCEPTED_BASE
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
- Declaration: `RMQ.SuccinctClassic.chargedTraceCostAlgebra` (abbrev of
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra`);
  frozen historical identity
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq`
  (`= 207`, `RMQ/Core/SuccinctFinalRAM.lean` :9349)
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
- Declaration:
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint`;
  list-facing
  `RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
  (:1324)
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
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
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
- Declaration:
  `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone`
  (39-field structure), discharged for every input list and endpoint pair by
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds`
- File: `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
  (structure at :300, producer at :702)
- Status history: this row was `PROVISIONAL_ARCHITECTURE` while the
  substrate was pinned to base `1490c97b...` and the Stage F feasibility
  gate was open. The gate closed and Stage A was recorded `ACCEPTED` on
  2026-08-07, after a fresh-blind exact-commit audit and a coordinator
  reconstruction in which every finding was independently reproduced.
  Re-pinning this substrate to base `745a3c5b...` is what moves the row to
  `ACCEPTED_BASE`; the mathematics did not change under it.
- Manuscript status: the accepted statement is **not yet absorbed** into a
  theorem environment. Section 9 quotes it and the single marked insertion
  point still holds the `ARCHITECTURE_RESULT_PENDING` marker. That is an
  editorial gap, not a kernel gap. No section other than Section 9 states,
  assumes, or paraphrases the result.
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
  from the run's own measure, not an attainment claim; `210` is logical fuel
  (charged trace events); and this is a cell-probe result, so it is not
  word-RAM instruction time, not preprocessing time, and not measured
  runtime. Computation between probes is free.
- Manuscript location: Section 9, Statement 9.1 (`tgt:packed`) and the
  Section 9.1 insertion point.

#### L-PACK-01
- Status: ACCEPTED_BASE
- Commit: `745a3c5b1fe99fe1072fbcf03f18f5dc9c23cb82`
- Declaration: field 8 `allocation_two_n_plus_rho` of
  `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone`,
  with field 9 `rho_little_o`; inhabited by
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds`
- File: `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
  (field 8 at :356--359, field 9 at :361, producer at :702)
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

## Open statements (asserted only as unproved)

#### L-OPEN-01
- Status: OPEN
- Statement: the construction's preprocessing complexity -- time and
  workspace, in any model -- is unproved; no theorem bounds it and the
  manuscript claims nothing about it.
- Manuscript location: Section 11, item 3.

#### L-OPEN-02
- Status: OPEN
- Statement: global minimality of the constant `210` across component
  correlations is unproved. The repository has a tight component-wise cap
  and an exact reachable interior-cost-33 witness, but no theorem that a
  smaller whole-query constant is impossible for this representation and
  charge policy.
- Manuscript location: Section 11, item 4.

#### L-OPEN-04
- Status: OPEN
- Statement: the `overhead` envelope of L-UB-01/L-UB-02 is proved
  little-o-linear but not proved tight; no reachable input family is shown
  to attain it, and no comparison with Fischer-Heun redundancy is claimed.
- Manuscript location: Section 5.2 (closing paragraph); Section 11, item 5.

#### L-OPEN-05
- Status: OPEN
- Statement: the cell-probe redundancy lower bounds for succinct RMQ
  (Liu-Yu 2020; Liu 2021) are not mechanized in this repository; the
  mechanized lower bound is the information-theoretic counting bound
  L-LB-01, and the manuscript cites the cell-probe bounds as related work
  only.
- Manuscript location: Section 4 (scope paragraph); Section 11, item 6.

#### L-OPEN-06
- Status: OPEN
- Statement: no instruction-level machine charges controller dispatch,
  decoding, arithmetic, comparison, and branching steps and simulates the
  same execution; consequently no running-time claim in the conventional
  word-RAM model is made, and the `210` bound is a charged-trace bound
  only.
- Manuscript location: Section 3 (model non-claims paragraph); Section 11,
  item 2.

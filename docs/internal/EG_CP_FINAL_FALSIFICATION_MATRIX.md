# EG-CP final falsification gate - frozen acceptance matrix

Worker branch: `codex/eg-cp-final-falsification-gate-r1`.
Exact base: `1490c97b399d136bad4e18953441da433d130d4d` (tree `4114fe2544ad0a4af4dce3c002e617a8dd55e64b`).
Workflow governance ref: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified ancestor of the base).
Template: `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.

**This matrix is frozen by this commit, before any implementation edit.** Requirements,
objects, guards, quantifiers, the mutation registry, and expected verdicts may not be
weakened without a coordinator-approved contract amendment. Only the `Evidence obtained`
and `Status / residual gap` columns may change afterwards.

**This document accepts nothing.** It records what would have to be true. A worker may
report at most `CANDIDATE_COMPLETE`; coordinator acceptance and a fresh-blind exact-commit
audit remain separate and are not claimed here.

Roadmap join: the final falsification rung for `docs/internal/RMQ_ENDGAME_ROADMAP.md`
Stage F, feeding but not itself closing Stage A packed-architecture acceptance. This task
does not record `FEASIBILITY_PASS`, accept Stage F or Stage A, synchronize public claims,
or select a publication headline.

---

## 1. Frozen requirement rows `FG-01` .. `FG-15`

Requirement text is copied verbatim from the commissioning prompt's numbered
"Frozen requirements" list.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `FG-01-RAW-PAYLOAD-IDENTITY` | `payloadBits xs` is definitionally equal or theorem-identical to the existing canonical `concreteBPNativeSuccinctRMQPayload` object consumed by the accepted RMQ semantics. There is no parallel payload, internal padding, hidden table, or sibling data store. | Local | A checked equality whose right-hand side is the existing canonical payload object at its existing definition site, not a re-derived copy; plus the absence of any second payload/table constructed by the packed modules. | The packed `memory` definition and the capstone space conjunct must both take their bits from this object. | Substitute a structurally equal but separately defined payload and check whether any committed theorem rejects it (registry `M11-SIBLING-PAYLOAD`). The mutation has **not** been run: the replay harness does not exist. What is available now is that the equality below is `rfl` against the canonical definition site, so a separately defined payload cannot inhabit it even if its bits are equal — but that is an argument about the proof term, not a replayed mutation. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M11-SIBLING-PAYLOAD` rejected at `PackedCellProbe/Payload.lean`: appending `++ []` to `packedPayloadBits` defeats the `rfl` identity, so a structurally equal sibling cannot inhabit it. The clause this row previously had to argue about the proof term is now a replayed mutation.| **Identity clause proved.** `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Payload.lean` defines `packedPayloadBits shape := (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload` and proves `packedPayloadBits_eq_canonical : packedPayloadBits shape = concreteBPNativeSuccinctRMQPayload builtGenericSparseExceptionSelectBPCloseAccessFamily shape` by `rfl`, with the list-facing `packedPayloadBitsOfList_eq_canonical` and the one-level expansion `packedPayloadBits_eq_bpCode_append_aux`. Consumed: `packedSerializedBits shape = packedHeaderBits shape ++ packedPayloadBits shape`, so `packedPaddedBits`, `packedMemory` and every probe theorem take their bits from this object; `packedSerializedBits_drop_header` proves that dropping one header cell recovers it exactly, so nothing else is serialized. Pinned by `packedPayloadIsCanonicalObject`, `packedListPayloadIsCanonicalObject`, `packedSerializedIsHeaderThenCanonicalPayload`. **Which store consumes it (2026-08-04).** The identity is to `concreteBPNativeSuccinctRMQPayload builtGenericSparseExceptionSelectBPCloseAccessFamily shape`, and `ExecutedUniverse.lean` shows the executed word-RAM store reads that object only at segments `0` .. `19`; from segment `20` up it reads the canonical reviewer objects instead.| **Open, ambiguity resolved (`DD-20260804-038`).** This row names two objects -- the identifier `concreteBPNativeSuccinctRMQPayload` and *the object consumed by the accepted RMQ semantics*, which is `concreteBPNativeSuccinctRMQCanonicalReviewerPayload` since `buildPayload` is defined as exactly that. The frozen registry decides between them: under the identifier reading the candidate proves space for one payload while executing another, which is `M11-SIBLING-PAYLOAD`, a commissioned REJECT. So `payloadBits` is the consumed object. The identity currently proved is against the identifier and must be re-pointed; the geometry, probe plan, width and address work transfers, the close half is new, and the segment 20/21/22 deficit disappears. |
| `FG-02-K1-SOURCE-FACTORIZATION` | over the complete closed physical-source type, every live source offset and span used by the packed execution is a checked function only of `n`, `longCount`, typed source/index arguments, and prior packed replies. Cover aliases, empty sources, sentinels, dead slots, and cell crossings. | Local | A theorem universally quantified over the closed source inductive and over all shapes of a given size, concluding that the offset/span equals an application of one fixed function to `(n, longCount, source, index)`. | Consumed by the packed address computation inside the closed controller; the controller may not call the shape-taking offset function. | Add a source whose offset genuinely needs another descriptor and check the theorem fails to elaborate; registry `M10-SPARSE-COUNT-DEPENDENCY`. Coverage is elaborator-enforced: `packedSourceComponentOffset_eq` is proved by `cases source`, so a new constructor fails to elaborate until both sides supply its arm. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M10-SPARSE-COUNT-DEPENDENCY` rejected at `PackedCellProbe/SourceGeometry.lean`: giving `packedSourceStride` a second, content-derived argument breaks the factorization.| **Factorization leaf complete.** `PackedCellProbe.packedSourceComponentOffset : Nat -> Nat -> ConcreteBPNativeSuccinctRMQFlatPayloadSource -> Nat` has no shape argument, and `packedSourceComponentOffset_eq : forall (shape) (source), concreteBPNativeSuccinctRMQFlatPayloadSourceComponentOffset shape source = packedSourceComponentOffset shape.size (longCount shape) source` holds for every shape and every one of the 29 constructors, including the `finalRankBPCodeAlias` alias, the three retired finite-small slots, and the zero/dead arms. Component bases: `closeComponent_flatOffset` (close), `rankAuxPayload_length` (select base). Long-count term: `longSuperRelativeTable_length_eq`. Pinned by `RMQ/Validation/EGCPFinalFalsification.lean` consumers `packedSourceComponentOffsetSignature` (signature) and `packedSourceComponentOffsetAgrees` (proposition). **The one non-size-only count dissolves at unit stride (2026-08-04, `DD-20260804-041`).** `packedSparseExceptionEntries_nil_of_unit_stride` proves `sparseExceptionRelativeEntries bits target = []` whenever `localStride bits.length = 1`, via `packedLocalIsSparseException_false_of_unit_stride`: a slot covering one occurrence has span at most one, so the exception predicate's `wordBits < span` conjunct is refuted by `wordBits_pos`. No property of the bit pattern is used. `localStride (2n) = 1` holds for every size below `2 ^ 96` by measurement, first exceeding one at `m = 2 ^ 97`. Pinned by `packedSparseRelativeTableIsEmptyAtUnitStride`.| **Open.** The offset half of the leaf is complete but nothing executes it: no packed controller exists, so "used by the packed execution" is not yet witnessed. **Spans are still not covered.** `packedSourceProbePlan` and `packedLogicalProbePlan` (2026-08-04) take the width as an explicit argument; the mirror `packedSourceWidth : Nat -> Nat -> Source -> Nat` that would make the span size-only is deliberately not defined, because a mirror without its agreement theorem would make the lowering look closed while the load-bearing step was missing (`DD-20260804-003`). Cell crossings are now covered by the conditional probe plan of `FG-05`. Closes when the width mirror lands and the controller of `FG-07` computes its addresses through `packedSourceComponentOffset`. |
| `FG-03-SPARSE-COUNT-ELIMINATION` | prove that no executed offset requires sparse-count metadata. In particular prove the sparse-relative table is terminal within the select payload for addressing purposes and that access padding makes the subsequent close-component base input-size-only. A finite example list is not universal evidence. | Local | Two checked theorems: (a) terminality of the sparse-relative table inside the select payload concatenation; (b) the close-component flat base equals an `n`-only expression, including the truncated-subtraction side condition that the access directory payload fits its budget. | Feeds `FG-02`; consumed by the close-source address computation. | Attempt to exhibit a shape of some size `n` whose close base differs from another shape of the same size; the theorem must make that impossible for every size, not just sampled ones. The close-base theorem is universally quantified over `shape` with no size side condition, so no such shape exists. The truncated-subtraction side condition is not assumed: it is discharged from the `BPCloseAccessDirectory.payload_length_le_overhead` structure field, which the layout cannot be built without. | **Both clauses proved.** (a) Terminality: `selectPayload_eq_prefix_append_sparseRelative : (sparseExceptionSelectSource shape.bpCode false).payload = packedSelectPrefixBits shape ++ (sparseExceptionRelativeTable shape.bpCode false).payload`, with the addressing consequence `selectSourceComponentOffset_le_prefix`. (b) Close base: `closeComponent_flatOffset : (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).componentFlatOffset .closePayload = 2 * shape.size + packedAccessOverhead shape.size`. Independently, `packedSourceComponentOffset` takes no sparse count, so by `packedSourceComponentOffset_eq` no offset can depend on one. Pinned by `packedSparseRelativeIsTerminal`, `packedSelectOffsetsStayInPrefix`, `packedCloseComponentBaseIsSizeOnly`. | **Open.** The two clauses this row names are proved. It stays Open on the same downstream dependency as `FG-02`: "no executed offset requires sparse-count metadata" quantifies over executed offsets, and no execution exists yet. Closes with `FG-07`. |
| `FG-04-WIDTH-AND-HEADER` | freeze `K = 1`; define `P(n)` as the exact input-size-only canonical payload length; define and justify `w(n) = machineWordBits (P(n) + 2)` or prove a checked equivalence-required correction; encode exactly `longCount` in one `w(n)`-bit cell; prove all-size count fit, decoding, exact arity, and empty/small cases. | Local | `P(n)` all-size theorem; `w(n)` definition; `longCount xs < 2 ^ w n` for every `n` and shape; `decode (encode c) = c` at width `w n`; header bit length exactly `w n`; explicit `n = 0`, `n = 1`, `n = 2` instances. | `headerBits` and the header cell of `memory xs`; the controller's header decode. | Check that the encoding is not silently widened or truncated at small `n`; instantiate `n = 0` where the width is minimal. Done: `packedHeaderBits`/`packedHeaderBits_length`/`packedHeaderBits_decode` instantiated at the empty and singleton shapes as kernel-checked `example`s. At `n = 0` the width is `machineWordBits (P 0 + 2)`, not a byte or a word, so a chunker assuming any minimum cell size is wrong at the bottom of the range. | **Clauses proved.** `packedPayloadLength : Nat -> Nat` with `packedPayloadLength_eq : (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload.length = packedPayloadLength shape.size`. `packedCellWidth n = SuccinctRank.machineWordBits (packedPayloadLength n + 2)`, exactly the commissioned expression, with `packedCellWidth_pos`. All-size count fit: `longCount_lt_two_pow_width : longCount shape < 2 ^ packedCellWidth shape.size`, no size side condition, via `longCount_le_superSlots` and `packedSuperSlots_le`. Exact arity: `packedHeaderBits_length`. Decoding: `packedHeaderBits_decode : bitsToNatLE (packedHeaderBits shape) = longCount shape`. `K = 1` recorded in `DD-20260802-001`. Pinned by `packedPayloadLengthIsSizeOnly`, `packedLongCountFitsOneCell`, `packedHeaderIsExactlyOneCell`, `packedHeaderDecodes`. **Explicit small cases: `n = 0`, `n = 1` and `n = 2` (2026-08-04).** Size two is the first size carrying more than one shape, so both `packedSizeTwoLeft` and `packedSizeTwoRight` are instantiated, proved distinct by `packedSizeTwoShapesDiffer`, and each required to have header arity `packedCellWidth 2` and payload length `packedPayloadLength 2` — the same numeral at the same size, not two coincidentally equal widths. Pinned by `packedSizeTwoLeftHeaderIsExactlyOneCell`, `packedSizeTwoRightHeaderIsExactlyOneCell`, `packedSizeTwoLeftHeaderDecodes`, `packedSizeTwoRightHeaderDecodes`, `packedSizeTwoLeftCountFitsOneCell`, `packedSizeTwoRightCountFitsOneCell`, `packedSizeTwoLeftPayloadLengthIsSizeOnly`, `packedSizeTwoRightPayloadLengthIsSizeOnly`. Also `packedCellWidth_ge_two`, needed so that boundary-crossing reads exist at all. **The header is now read rather than only decodable (2026-08-04).** `packedHeaderProbePlan = [0]`, `packedHeaderFetch` (allocated at every size, returns the header cell), `packedHeaderProbe_decode` (decoding that probe's reply yields exactly `longCount shape`, no side condition), `packedHeaderProbePlan_length = 1` (charged). `packedMemory_cell_zero` is load-bearing: cell zero is the header in full, so the descriptor is not split and the first probe needs no crossing case. Pinned by `packedHeaderProbeCostsOneProbe`, `packedHeaderProbeFetchesTheHeaderCell`, `packedLongCountComesFromAProbe`. | **Open.** Every clause this row lists is proved, including the `n = 0`, `n = 1` and `n = 2` instances; `FG-05` supplies the cell and the header is now obtained by a charged probe rather than supplied. The row's phrase "the controller's header decode" still has no controller: nothing sequences the probe before the address computation and no definition consumes the reply. Closes with `FG-07`. |
| `FG-05-PACKED-MEMORY` | define `headerBits`, `serializedBits = headerBits ++ payloadBits`, fixed-width chunking, exact slice/unpack behavior, boundary crossing, zero final padding, and `memory xs`. Prove round trips and that all execution reads target this one object. | Local | Chunking round-trip theorem (concatenating the cells recovers `serializedBits` up to the counted final padding); an exact bit-slice theorem for an arbitrary aligned and unaligned span, including a span crossing a cell boundary; and a theorem that the executed trace mentions only `memory xs`. | The capstone's execution and space conjuncts. | Mutate the crossing codec bit order and require exact decoded-word failure; registry `M09-WRONG-CELL-CROSSING`. Not run: the replay harness does not exist. What is run instead is the boundary case the earlier draft got wrong. `packedMemory_getElem?_cellCount` proves the address one past the last cell is absent, and `packedProbe_final_cell` proves a positive-width read contained in the last allocated cell issues exactly `[packedCellCount - 1]` and fetches successfully. Under the unconditional pair the second issued address was `packedCellCount`, so the fetch would have returned `none`. Both plan branches are exhibited (`packedProbePlan_of_offset`, `packedProbePlan_of_crossing`), so the conditional is not constant in disguise. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M09-WRONG-CELL-CROSSING` rejected at `PackedCellProbe/Probe.lean`: swapping the two cells of the crossing branch breaks the exact decoded word.| **Definitions and round trip proved; crossing behaviour proved; "all execution reads target this one object" not proved.** `packedSerializedBits = packedHeaderBits ++ packedPayloadBits`, `packedCellCount`, `packedAllocatedBits`, `packedPaddedBits`, `packedMemory`, with `packedMemory_length`, `packedMemory_cell_length` (every allocated cell exactly one full width), `packedMemory_cell_zero` (the header is cell zero in full), `packedMemory_flatten` (the join recovers the padded bits exactly) and `packedMemory_flatten_take`. Exact slice behaviour: `packedSpan_from_two_cells` for an arbitrary aligned or unaligned span of at most one cell, and `packedPayloadSlice` for the header shift. Cell-boundary behaviour is now issued rather than assumed: `packedProbePlan` is executable and conditional (no probe at zero width, one probe when `bit % w + width <= w`, two otherwise), probes go through `packedProbeCell = List.getElem?`, and `packedFetch` returns `some` only when every issued address resolved. `packedProbePlan_lt_cellCount` proves allocation from `bit + width <= packedAllocatedBits n` alone; `packedProbePlan_decode` proves the fetched cells decode to exactly the requested window; `packedProbe_covers_range` proves the window covers the request; `packedProbeWindow_length` gives its exact length. Pinned by `packedMemoryRoundTrips`, `packedMemoryCellsAreFullWidth`, `packedSpanNeedsAtMostTwoCells`, `packedProbeAddressesAreAllocated`, `packedProbeFetchSucceeds`, `packedProbeDecodesExactly`, `packedProbeCoversRequestedRange`, `packedOnePastLastCellIsAbsent`, `packedFinalCellReadIssuesOneAllocatedProbe`, `packedCrossingReadIssuesTwoProbes`, with concrete instances at sizes 0, 1 and 2. | **Open.** The chunking round trip, the exact slice theorem, the crossing behaviour and the allocation of every issued address are proved. The third clause — that the executed trace mentions only `memory xs` — quantifies over an execution that does not exist. Closes with `FG-07`/`FG-08`. |
| `FG-06-ALLOCATED-SPACE` | define allocated bits as `memory.length * w(n)`; include header, canonical payload, every allocated cell, final padding, sentinel/dead material; prove an all-size `2*n + rho(n)` upper bound and `LittleOLinear rho`. Do not count only meaningful bits. | Local | `(memory xs).length * w (xs.length) <= 2 * xs.length + rho (xs.length)` for every `xs`, plus `LittleOLinear rho` with the project's existing definition. | The capstone space conjunct, over the same `memory xs` the execution probes. | Confirm the bound is stated on allocated cells times width, not on `serializedBits.length`; check the two differ whenever padding is nonzero. Done: `packedMemory_length_mul_width_le` is stated on `(packedMemory shape).length * packedCellWidth shape.size`. The chunker was deliberately written to allocate whole cells rather than reuse `SuccinctSpace.chunkPayloadWords`, which leaves a short final word; the difference is exactly the padding this row forbids dropping. | **Clauses proved.** `packedAllocatedBits n = packedCellCount n * packedCellWidth n` counts the header cell, every payload cell and the final padding at full width. `packedAllocatedBits_le : packedAllocatedBits n <= 2 * n + packedRho n` with `packedRho n = concreteBPNativeSuccinctRMQOverhead genericSparseExceptionBPCloseAccessOverhead n + 2 * packedCellWidth n`, and `packedRho_littleO : SuccinctSpace.LittleOLinear packedRho`. The `2 * packedCellWidth` term is the header cell plus the ceiling remainder; its little-o proof needed a new lemma, `littleOLinear_machineWordBits_comp`, because the width is `machineWordBits` of the payload length rather than of the input size. Pinned by `packedAllocatedSpaceBound` and `packedRhoIsLittleOLinear`. | **Open.** The bound is proved over `packedMemory`, but that object is not yet shown to be what any execution probes, so `INV-STORE-IDENTITY` is not discharged. Closes with `FG-07`/`FG-08`. |
| `FG-07-CLOSED-CONTROLLER` | the actual executed controller is one fixed definition whose dynamic inputs are exactly `n`, `left`, `right`, the header reply, and previous replies from `memory xs`. It has no `xs`, semantic `shape`, proof witness, source list, sibling store, precomputed offsets, expected answer, shape-specialized program, or input-dependent code/table outside memory. An exact-type consumer pins the concrete controller, not a mutable wrapper. | Local | The controller's declared signature contains no `List Int`, no `CartesianShape`, and no proof argument; and an independently frozen expected-type consumer elaborates only against that exact signature. | The capstone's `receipt` is produced by this definition. | Restore a `shape` parameter and require exact-signature failure; synthesize a canonical shape from `n` inside a wrapper and require structural failure. Registry `M03-SHAPE-PARAMETER`, `M04-CANONICAL-SHAPE-BY-N`, `M13-HIDDEN-UNCOUNTED-TABLE`. Not run: there is no controller to mutate. A different challenge was run instead and it is the one that decides whether this row is reachable at all — see the evidence cell. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M03-SHAPE-PARAMETER` rejected at `PackedCellProbe/PhysicalRead.lean` -- not at the validation root, because adding a parameter to `packedSourceRead` breaks the library's own uses before the build reaches the exact-signature consumer. The weaker, true claim is recorded rather than the stronger one the harness first made.| **No controller exists. What exists is a checked bound on the remaining work.** The obstacle to reusing the existing supplied-store leaves is that they take `GenericSelect.sparseExceptionSelectData shape.bpCode false`. Whether that argument supplies the *replies* or only the *geometry* decides whether `FG-07` needs a new architecture or a scalar factorization. It supplies only the geometry: `packedSelectEntryRead_content_free` proves that, given the same segment layout, the same supplied store and the same index, two select entry tables with **unrelated entries and unrelated field widths** produce the same trace result — same reads, same order, same replies, same decoded entry. It quantifies over two tables sharing no parameter, so no leaf satisfying it can consult its table for a reply. Supporting: `packedTableReadProgram_content_free`, `packedTableReadProgram_eq_readWord` (the program is `mapOptWordNat (readWord 0 index)`; `PayloadWordStore.readProgram` ignores its store argument). Pinned by `packedTableReadIsAnIndexNotALookup`, `packedSelectEntryReadIsDeterminedByTheStore`. Recorded as `DD-20260804-006`. **That scalar list is now done except one item (`DD-20260804-007`).** `packedSelectWordSize`, `packedSelectSuperStride`, `packedSelectLocalStride` and `packedSelectLocalSlotsPerSuper`, all of type `Nat -> Nat` and all defined at `2 * n`, agree with the corresponding fields of `sparseExceptionSelectData shape.bpCode false`; the mirrors are defined at `2 * n` rather than at `shape.bpCode.length` so that a controller can evaluate them. `packedSelectOccurrenceCount_eq_size` proves the leaf's validity dispatch `idx < occurrenceCount shape.bpCode false` is exactly `idx < n`, so the guard needs no header field and no probe — had it needed one, `K = 1` would have required a second field. Pinned by `packedSelectWordSizeIsSizeOnly`, `packedSelectSuperStrideIsSizeOnly`, `packedSelectLocalStrideIsSizeOnly`, `packedSelectLocalSlotsPerSuperIsSizeOnly`, `packedSelectValidityGuardIsTheInputSize`. | **Open — not started.** No controller definition exists, so every clause of this row is unmet: there is no fixed definition, no signature to pin, and no `receipt`. The evidence above is about the leaves a controller would call, not about a controller. The select-side scalar list is now complete — `packedSelectQueryOccurrence_content_free` shows the last item, `queryOccurrence`, ignores its record — so nothing on the select side needs the shape except through `n`. Remaining elsewhere: the close/LCA leaves have not been examined at all, and `SuccinctClose.bpFringeChunkBits shape.bpCode.length` is supplied beside the select data rather than inside it. |
| `FG-08-PHYSICAL-LOWERING` | every logical read actually used by the query lowers to a fixed bounded sequence of physical cell probes against `memory xs`; prove exact decoded word equality and preserve attempted/successful distinction, order, multiplicity, producing site, and cell-crossing behavior. | Local | For each logical read, a theorem giving the exact probe list and the decoded word equal to the logical word; and a whole-run theorem relating the ordered logical trace to the ordered physical trace with multiplicity. | The capstone's trace conjunct. | Reorder or drop one probe and require the ordered-trace theorem to fail; registry `M07-DISCONNECTED-TRACE`. Not run: there is no trace to reorder. | **Per-read lowering proved for a supplied width; whole-run lowering absent.** `packedSourceProbePlan` and `packedSourceRead_decode` give, for one typed source, one index and one width no wider than a cell, the exact probe list and the equality of the decoded bits with the canonical payload slice at that source's flat offset. `packedLogicalProbePlan` and `packedLogicalRead_decode` do the same starting from a logical address `(segment, index)`, using the already shape-free `concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?`. Pinned by `packedSourceReadDecodesToCanonicalSlice`, `packedLogicalReadDecodesToCanonicalSlice`, `packedLogicalProbePlanSignature`, `packedSegmentSourceSignature`. **One source is lowered completely (2026-08-04).** `packedStridedBitAddress` separates a source's stride from its read width, because `SuccinctSpace.chunkPayloadWords` leaves a short final word and reading it at full width against the packed memory would return foreign bits from the next component rather than truncating. For the BP code, `packedBpCodeWordWidth n = machineWordBits (2 * n)` is the stride, `packedBpCodeReadWidth n index = min (stride) (2 * n - index * stride)` is the exact read width, and `packedBpCodeRead_decode` proves that every word the flat payload store would return is fetched and decoded exactly. `packedBpCodeWord_index_lt` derives the in-range condition from the word's existence rather than assuming it. Pinned by `packedBpCodeReadDecodesToTheStoreWord`, `packedBpCodeWordFitsOneCell`, `packedBpCodeStartsThePayload`, `packedStridedBitAddressSignature`, `packedBpCodeWordWidthSignature`, `packedBpCodeReadWidthSignature`. **All twenty-nine sources lowered, and the read made physical (2026-08-04).** `packedSourceStride n source`, `packedSourceWordCount n longCount source` and `packedSourceBitLength n longCount source` give the word geometry from the input size and the decoded long count alone, and `packedSourceWords_of_some` proves the store's word array agrees with them at every source, by case analysis over the closed source inductive. `packedFixedWidthTable_getElem?` and `packedChunkedSentinelWords_getElem?` are the two generic shapes underneath, the first proved from the table structure's own fields with no positivity hypothesis on the width. `packedSourceRead n longCount memory source index` issues `packedSourceReadPlan` and decodes it, and `packedSourceRead_of_some` proves every successful logical read is reproduced exactly; its zero-width branch is where the sentinel words of the chunked rank directories issue no probe at all. `packedSourceStride_le_cellWidth` supplies the one-cell hypothesis the decode needs. Pinned by `packedSourceReadSignature`, `packedSourceReadPlanSignature`, `packedEverySuccessfulReadLowers`, `packedEveryStoredWordFitsOneCell`, `packedLogicalWordReadIsAtMostTwoProbes`, `packedSourceStrideSignature`, `packedSourceWordCountSignature`, `packedSourceBitLengthSignature` and `packedSparseRelativeIsBoundedNotDetermined`. **The universe gap, measured (2026-08-04).** `ExecutedUniverse.lean` proves by `rfl`, composed with the pre-existing `concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global`, that the executed store and the flat payload store agree at segments `0`, `16` and `19` and **disagree from segment `20` up**: the executed store reads segment `20` from `SuccinctClose.canonicalRelativeRmmInteriorComponentStore`, segment `21` from `bpFringeChunkTable`, segment `22` from `bpChunkSelectTable`, and answers `none` from segment `23` on, while the flat store reads those four segments from the close summary's four columns. **Correction (2026-08-04, `DD-20260804-036`).** The universe gap measured above is a fact about the word-RAM global-store layer, which I had wrongly assumed was the execution this row quantifies over.| **Open.** Clause (a) is discharged for all twenty-nine sources. The correction appended to the evidence cell is itself **retracted** by `DD-20260804-037`: the word-RAM layer *is* the execution the accepted semantics is about, because the public `buildPayload xs` is `concreteBPNativeSuccinctRMQCanonicalReviewerPayload (cartesianShape xs)`. Clause (b) is unreachable under the reading of `FG-01` implemented here, by `packedStoresNotEqual`; it becomes reachable under the reading in which `payloadBits` is the object the accepted semantics consumes. Clause (c)'s segment gap is real under the first reading and does not arise under the second. `selectSparseRelative` still lowers one-directionally. |
| `FG-09-TOTALITY-AND-CAP` | for every required query case, every attempted probe is successful and in range, every address is machine-representable at `w(n)`, and the complete physical trace length is at most one derived constant `C` independent of `n`, contents, and endpoints. Derive `C` from execution; do not freeze an aspirational number first. | Local | Universal theorems: attempted probes are in range and successful; each address `< 2 ^ w n`; `receipt.trace.length <= C` with `C` a literal derived after the lowering exists. | The capstone's totality and cap conjuncts. | Replace derived cap evidence by a stored number or theorem-only field and require consumer failure; registry `M08-FORGED-PROBE-CAP`. Note the recorded F07 concern that some attempted probes currently return `none` into segment 0 under canonical stores at small `n`. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M08-FORGED-PROBE-CAP` rejected at `PackedCellProbe/Probe.lean`: replacing the derived `packedProbeCount` by the literal `2` breaks the exact-count theorems.| **Per-read cap proved; run-level cap absent.** `packedProbeCount n bit width = (packedProbePlan n bit width).length` is the issued plan's length, not a stored numeral, and `packedProbeCount_le_two` bounds it. `packedProbeCount_eq_zero`, `packedProbeCount_eq_one` and `packedProbeCount_eq_two` give the exact conditional value, and `packedProbeCount_pos` shows a positive-width read issues at least one probe. `packedProbePlan_lt_cellCount` plus `packedFetch_plan` give in-range success for every issued address of a fitted read. Pinned by `packedProbeCountIsPlanLength`, `packedProbeCountAtMostTwo`, `packedProbeAddressesAreAllocated`, `packedProbeFetchSucceeds`, `packedLogicalReadIssuesAtMostTwoProbes`. **The charged plan is now the actual read's plan (2026-08-04).** `packedSourceReadPlan_length_le_two` bounds the plan `packedSourceRead` actually issues, at the width the source actually stores, rather than a plan at a supplied width. A zero-width read issues zero probes, which is the exact-count statement `packedProbeCount_eq_zero` already gave abstractly. **The address clause is now discharged for issued probes (2026-08-04).** `packedProbeAddress_lt_two_pow_cellWidth` replaces the host-array bound with `addr < 2 ^ packedCellWidth n`.| **Open.** The address-representability clause is proved for every issued probe address, so the substitution `INV-ADDRESS-WIDTH` rejected is no longer being made. What remains is the whole-run cap: `C` must be derived from an execution, and by `DD-20260804-027` no execution can yet be lowered past segment 19. The totality clause also carries the sparse relative discriminator of `DD-20260804-022`. |
| `FG-10-SAME-RUN-CORRECTNESS` | the packed controller run itself returns the independent project `ReferencePacket`/public RMQ semantics for valid, reversed, empty, and out-of-range cases. Do not obtain a semantic result first and replay decorative reads afterward. | Local | `(runPackedController n l r (memory xs)).result = referencePacket xs l r` for every `xs`, `l`, `r`, with the reference side the project's existing independent semantics. | The capstone's correctness conjunct. | Check the controller body does not call the reference semantics; registry `M06-ANSWER-ORACLE`. | Pending | Open |
| `FG-11-LIVENESS-AND-ANTI-BYPASS` | supply a pinned valid execution where changing only the counted long-count cell changes a later probe address or returned result; bridge the existing consumed-payload-cell witness to the packed run's returned answer; and supply a proved-unread-cell mutation that is an expected accept. Aggregate trace inequality alone is insufficient when the requirement concerns the value. | Local | A checked inequality whose two sides are a later probe ADDRESS or the RETURNED value, not the enclosing record; plus an equality for the proved-unread cell. | The capstone plus the committed replay. | Verify the inequality projection is address/result, not the trace log; registry `M01-WRONG-LONG-COUNT`, `M14-LONG-COUNT-IGNORED`, `A02-UNREAD-CELL-EXPECTED-ACCEPT`. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M01-WRONG-LONG-COUNT` and `M14-LONG-COUNT-IGNORED` both rejected at `PackedCellProbe/SourceGeometry.lean`. Note what that does and does not show: the surface reached is the source-geometry equation, which depends on the decoded header value, not a value-projection liveness witness -- this row still has no `.result` or next-address inequality, and the mutations do not supply one.| Pending | Open |
| `FG-12-REPLAY-AND-CONSUMER` | commit one portable exact-registry replay with the ordered cases and expected verdicts below, named failing surfaces, one unchanged production accept, one unread-cell accept, restoration hashes, clean-tree checks, positive evidence-based subprocess deadlines, owned root-plus-descendant termination on Windows and Ubuntu, selector nonvacuity, and an independent expected-type consumer whose literal type pins the full capstone. | Local | `scripts/eg_cp_final_falsification_replay.ps1` exists, encodes the frozen registry literally, and passes in full mode on the committed clean candidate. | `RMQ/Validation/EGCPFinalFalsification.lean` pins the capstone proposition. | Omit, duplicate and reorder registry IDs; pass unknown, empty and whitespace selectors; all must fail. | `scripts/eg_cp_final_falsification_replay.ps1` exists, encodes the sixteen-entry frozen registry literally and in the commissioned order, and was run once in full mode on the committed clean tree (2026-08-04). Result: 16 cases considered, **9 as commissioned at their named surfaces**, 7 `TARGET-ABSENT`, descendant self-test PASS, every mutation restored with a verified SHA256, terminal tree clean, exit 7. The nine are `A01` (ACCEPT) and `M01`, `M03`, `M05`, `M08`, `M09`, `M10`, `M11`, `M14` (REJECT). Registry integrity, selector nonvacuity and the bounded-stage contracts are exercised on every invocation. | **Open.** The harness is complete and honest but the run is not a pass, and by design: `A02`, `M02`, `M04`, `M06`, `M07`, `M12` and `M13` each name a run, a trace, a controller over `packedMemory`, or a capstone, none of which exist (`DD-20260804-027`, `DD-20260804-029`). Full mode exits non-zero whenever any case is `TARGET-ABSENT`, so this row cannot be closed by the harness reporting success on a partial registry. The row also requires an expected-type consumer whose literal type pins the full capstone; there is no capstone. |
| `FG-13-TRUST-AND-SAME-OBJECT` | no reachable `sorry`, `admit`, axiom, unsafe/opaque/partial/extern implementation, native decision shortcut, Mathlib import, proof-value oracle, semantic callback, or mismatch of payload/store/run/width objects supports the capstone. Proof-only fields may certify but not choose answers, routes, or addresses. | Local | Hygiene scan clean; `lake env lean scripts/headline_axiom_check.lean` clean; and an explicit object-identity chain showing payload, memory, width, run and trace are the same objects in every conjunct. | The capstone. | Conjoin true theorems about different payloads and check the composition row rejects it; registry `M11-SIBLING-PAYLOAD`, `M05-SIBLING-STORE`. | Pending | Open |
| `FG-14-BOUNDARIES` | check empty representation, singleton, size two, each relevant threshold minus one/at/plus one, empty range, reversed range, and out-of-range endpoints. Preserve the half-open contract and leftmost tie policy. The top-level architecture is uniform; total empty tables and guards are allowed, but an undocumented second representation is not. | Local | Kernel-checked instances at each listed case, with the thresholds named explicitly from the geometry (including the recorded `5488/5489` long crossover and the `[1024, 1330]` interior-readiness window). | The capstone instantiated at those cases. | Check no case is discharged by a readiness dispatch that silently selects a different representation. | **Both named thresholds located from the geometry and kernel-checked (2026-08-04), in `PackedCellProbe/Boundaries.lean`.** `decide` cannot do this on its own: `Nat.log2` is defined by well-founded recursion and kernel reduction sticks on it, so `#eval` proves nothing. `packedLog2_eq` pins a logarithm from a pair of power-of-two bounds instead. **Long crossover:** `packedLongCrossover_before/at/after` give the minus-one/at/plus-one triple at `5487/5488/5489`. It is where a superblock's long span stops covering the BP code -- `superLongSpan (2n) = 10976` at all three sizes while `2n` passes it -- so the select layer's relative width stops tracking the input size. Visible in the packed geometry as `packedLocalWidth_at_crossover`. **Interior-readiness window:** `packedInteriorReadinessWindow` checks both endpoints of `[1024, 1330]` with their neighbours. The clause that moves is `macroSize <= blockCount`; the summary base jumps `10 -> 11` at `1024`, so the macro size jumps `100 -> 121` while the raw block count falls `102 -> 93`, and readiness returns exactly at `1331` where `1331 / 11 = 121`. Pinned by `packedLongCrossoverIsAt5488` and `packedInteriorWindowIs1024To1330`. Existing packed representation boundaries at sizes 0, 1, 2 and at the final allocated cell remain. | **Open.** The two thresholds this row names are now located and checked, and neither is a tuning constant: each is where one geometric quantity overtakes another. What is untouched is everything the row asks at *query* level -- empty range, reversed range, out-of-range endpoints, the half-open contract and the leftmost tie policy -- because those quantify over a run, and by `DD-20260804-027` no run can be lowered past executed segment 19. The row also wants the capstone instantiated at each case, and there is no capstone. The `PackedSummaryActive` half of readiness is not kernel-checked here; it does not move across `[1023, 1331]` by evaluation, and the checked clause is the one that does. |
| `FG-15-DURABLE-DECISION` | commit the completed matrix, result report, design rationale, rejected K0/K2/padding/historical alternatives, exact theorem types and object-composition chain, skeptical-reviewer questions, verification ledger, and every remaining assumption. Do not call commissioning prompts or audit prose theorem evidence. | Local | This matrix completed, `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md`, and entries in `DESIGN_DECISIONS.md` / `WORKFLOW_DESIGN_DECISIONS.md`. | Coordinator reconstruction. | Confirm no row cites the A11 prompt, an A10/A11 verdict, worker prose, matrix status, CI, or a bare theorem name as its evidence. | Pending | Open |

---

## 2. Inherited invariant rows

Requirement text is copied verbatim from
`.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md` section 2.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient | Inherited | The space conjunct and the execution conjunct name the same `memory xs` term. | Capstone. | `M05-SIBLING-STORE`, `M11-SIBLING-PAYLOAD`. **Run 2026-08-04** by `scripts/eg_cp_final_falsification_replay.ps1` in full mode: verdict as commissioned, at the named surface. `M05-SIBLING-STORE` rejected at `PackedCellProbe/PhysicalRead.lean`: dropping one cell before the probe breaks `packedBackedStore_of_some`.| Pending | Open |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient | Inherited | An inequality at the `.result` or next-address projection. | `FG-11`. | `M01`, `M06`, `M14`. | `packedSourceFlatOffset_injective_longCount` proves that changing only the decoded long count changes the flat offset of every source placed after the long relative table, because that offset contains `longCount * packedLongBlockBits n` and `packedLongBlockBits_pos` shows the block is never empty. `packedProbeCell_moves_with_longCount` lifts it to the **issued probe cell**: separating two counts by one cell width moves the address by `packedCellWidth n * packedLongBlockBits n`, a whole number of cells, so the cell index the plan issues differs. The inequality is at an address, not at an enclosing trace record -- the substitution this row rejects. Pinned by `packedHeaderCountMovesTheOffset`, `packedHeaderCountMovesTheBitAddress` and `packedHeaderCountMovesTheIssuedCell`. | **Open.** The address projection is now fully witnessed at the issued cell index, with no side condition. What remains is the row's other half, the returned value, which needs a run (`DD-20260804-032`). |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself | Inherited | Liveness derived from emitted probes of the actual run. | `FG-11`. | Replace the liveness predicate by `True` and require failure. | Pending | Open |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe | Inherited | The trace is a projection of the run, not a separately constructed list. | `FG-08`. | `M07-DISCONNECTED-TRACE`. | Pending | Open |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace | Inherited | Agreement on the probed cells determines the run. | `FG-11`, `A02`. | `A02-UNREAD-CELL-EXPECTED-ACCEPT`. | `packedBackedStore_eq_readWord` proves the packed memory answers a logical read exactly as the flat payload store does -- failures included -- away from `.selectSparseRelative` and under the readiness guard on segments 24 and 25. **The excluded source is now known to answer nothing** (2026-08-04): `packedSparseRelativeWords_none_of_unit_stride` shows its word array is empty whenever `localStride bits.length = 1`, which holds for every size below `2 ^ 96`. So the exclusion covers a source with no readable index, and the capacity over-approximation of `DD-20260804-022` is never exercised. Pinned by `packedSparseRelativeSourceAnswersNothingAtUnitStride`. | **Open.** Agreement on the probed cells is proved per address. Lifting it to *determines the run* needs the run, which `DD-20260804-037` leaves waiting on the `FG-01` re-target of `DD-20260804-038`. The `.selectSparseRelative` exclusion is no longer a residual in substance, but it is still written into the theorem's statement and should be discharged there. |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store | Inherited | Each probe reply equals the corresponding cell of `memory xs`. | `FG-08`. | Corrupt a backing cell and require the reply to change. Not run. | `packedFetch_packedMemory` proves that a plan whose addresses are below `packedCellCount` fetches to exactly `plan.map (packedCellAt shape)` — positionally, address by address — and `packedProbeCell` is `List.getElem?` on `packedMemory shape`, so an unallocated address yields `none` rather than a fabricated reply. **Successful store reads are now backed (2026-08-04).** `packedSourceRead_of_some` proves that whenever `concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape source` answers an index, probing `packedMemory shape` at the derived plan and decoding returns the same word. The backing is positional through `packedFetch_packedMemory` and the flat-slice equation of `FlatPayload.lean`, not by re-deriving the word.| **Open.** Backing now covers every successful read of the flat payload store, not only issued probes. It still does not cover an execution, because no execution has been mapped through `packedSourceRead`. The sensitivity direction -- corrupt a backing cell and require the reply to change -- is untouched. |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word | Inherited | Every cell value `< 2 ^ w n`. | `FG-04`, `FG-09`. | Instantiate at `n = 0` where `w 0` is minimal. | `packedSourceStride_le_cellWidth n source hcounted` proves every source's stride is at most `packedCellWidth n`, by case analysis over the closed source inductive. Twenty-six arms are monotonicity of `machineWordBits`. The final rank block width needed the residual arithmetic `k * k <= 2 ^ k + 3` (`packedSq_le_two_pow_add_three`) together with the rank directory the payload already carries, because `w * w` is genuinely larger than `2 * n` at small sizes -- `9` against `4` at `n = 2`. The close summary relative width is bounded by the last conjunct of the summary-activity predicate itself. The close interior offset width is bounded by the `n`-only readiness guard, which is a load-bearing use of the guard `FG-07` requires. **The value clause is now proved too (2026-08-04):** `packedStoredCellValue_lt_two_pow` gives `bitsToNatLE cell < 2 ^ packedCellWidth n` for every cell of `packedMemory` (via `packedMemory_cell_length`, so it is the counted memory's own cells), and `packedDecodedWordValue_lt_two_pow` gives the same bound for every decoded span, since a span is a `List.take` of the fetched cells and so never wider than the request. Pinned by `packedEveryStoredWordFitsOneCell`, `packedStoredCellValuesFitOneWord` and `packedReturnedWordValuesFitOneWord`. | **Open.** Both clauses the row names are proved: stored cell values and returned word values are below `2 ^ w n`, and every source's stride fits one cell. What is missing is not a property of the packed representation but of a run: no execution has been lowered (`DD-20260804-027`), so `FG-04`'s and `FG-09`'s consumers of this row have nothing to consume it at. |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands | Inherited | Every probe address `< 2 ^ w n`, including addresses of dead or sentinel material. | `FG-09`. | Include the dead/sentinel sources named by the source inventory. | `packedCellCount_lt_two_pow_cellWidth` proves `packedCellCount n < 2 ^ packedCellWidth n`, and `packedProbeAddress_lt_two_pow_cellWidth` carries it to every issued probe address: `bit + width <= packedAllocatedBits n` and `addr` in the plan give `addr < 2 ^ packedCellWidth n`. This is the modeled-word bound the row asks for, not the host-array bound it rejects. The `+ 2` in `packedCellWidth n = machineWordBits (packedPayloadLength n + 2)` is what makes it hold at every size, including the singleton cases. Pinned by `packedIssuedAddressesAreMachineRepresentable` and `packedCellCountIsMachineRepresentable`. | **Open.** The issued-probe clause is proved for every address the plan can emit. The row also asks for register identifiers, branch and jump targets, dormant code and arithmetic operands; the packed layer emits none of those yet, because no run has been lowered (`DD-20260804-027`), so the constructor-exhaustive part is untouched. |
| `INV-PROGRAM-ACCOUNTING` | input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation | Inherited | No content-dependent literal in the controller definition. | `FG-07`. | `M13-HIDDEN-UNCOUNTED-TABLE`. | Pending | Open |
| `INV-ORACLE-INDEPENDENCE` | executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested | Inherited | Expected values come from the `List Int` reference semantics. | `FG-10`, `FG-14`. | `M06-ANSWER-ORACLE`. | Pending | Open |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information | Inherited | The controller state carries no proof field consulted for the answer or next address. | `FG-07`. | `M08-FORGED-PROBE-CAP`. | Pending | Open |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim | Inherited | The result is computed from replies, not replayed after a semantic call. | `FG-10`. | `M07`, `M06`. | Pending | Open |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct | Inherited | The result report records the derived probe cap separately from payload bits, allocated bits, proof fields, model probes, and Lean runtime. | `FG-15`. | Confirm the report does not conflate allocated bits with meaningful bits. | Pending | Open |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain | Inherited | Every capstone conjunct quantifies over the same `xs`, `l`, `r` and mentions the same `memory xs`. | Capstone. | `M11`, `M12-PUBLIC-TYPE-WEAKENING`. | Pending | Open |
| `INV-MUTATION-REPRODUCIBILITY` | when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean | Inherited | The committed replay script passes in full mode with restoration hashes verified. | `FG-12`. | Omit/duplicate/reorder registry IDs; require failure. | The versioned runner exists and was run in full mode on the committed clean tree. Every mutation is restored in a `finally` block and its restoration verified by SHA256 against the pre-mutation bytes; the run ends with `git status --porcelain` empty. The byte-exact restoration is not decorative: the first working version restored through `Set-Content -Encoding utf8`, which adds a BOM and rewrites CRLF, and the hash check caught it. | **Open.** Restoration, clean-tree and expected-surface checks pass for the nine runnable cases. Seven claimed cases are not replayed because their surfaces do not exist, so the campaign this row governs is not yet exhaustive. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding | Inherited | One `memory xs` and a translation covering every source in the closed source type. | `FG-08`. | Drop one segment from the translation and require failure. | `ExecutedUniverse.lean` supplies the translation for executed segments `0` .. `19`: those read the flat payload's own sources, and `PhysicalRead.lean` lowers each of them to a probe of the one `packedMemory shape`, failures included away from `.selectSparseRelative`. The same module proves the translation **stops** at segment `20`, and now proves the stop is not cosmetic: `packedStoresNotEqual` shows the flat payload store and the executed store are **not equal** whenever the close summary carries a block, disagreeing at segment `23` where the executed store is silent and the flat store answers. Pinned by `packedExecutedStoreIsNotTheFlatPayloadStore` and `packedExecutedStoreDisagreesAtSegment23`. **Correction (2026-08-04, `DD-20260804-036`).** The deficit recorded above is real for the *word-RAM* global-store layer, but that is not the execution the rest of this gate is about. The public bundle `concreteBPNativeSuccinctRMQ_two_n_plus_o_constant_query_profile` composes space, cost and correctness for the `Costed` query over `concreteBPNativeSuccinctRMQPayload accessFamily shape` -- the object `FG-01` pins and `packedMemory` serializes -- and that query's reads are `PayloadWordStore` word reads of the flat payload's own sources.| **Open.** The correction appended to the evidence cell is **retracted** by `DD-20260804-037`. Three executed segments have no translation -- `20`, `21`, `22` -- under the reading of `FG-01` implemented here, and `packedStoresNotEqual` shows the deficit cannot be closed by finding a bridge. Under the reading in which the packed memory serializes the object the accepted semantics consumes, those three segments are backed and this row's deficit disappears. |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim | Inherited | A single `w n` used everywhere, with the input-size relation proved. | `FG-04`, `FG-09`. | Check no sub-directory computes its own wider logical width. | Pending | Open |
| `INV-VALIDATION-REACH` | executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine | Inherited | `RMQ/Validation/EGCPFinalFalsification.lean` imports and elaborates against the packed capstone. | `FG-12`. | `M12-PUBLIC-TYPE-WEAKENING`. Not run. | The validation root imports `Payload`, `Header`, `Memory`, `Space`, `Address` and `Probe`, and states each dependency's expected type independently before discharging it, so weakening a library theorem breaks this file rather than being absorbed by it. It currently pins the payload identity, the shape-free factorization surface, the header schema including both shapes of size two, the memory round trip and cell arity, the space bound and residual, the bit-address surface, and the conditional probe plan with allocation, coverage, decoding, charged count, and concrete boundary instances at sizes 0, 1 and 2. It now also pins the physical read surface: the read and plan signatures, the one-cell word bound under the controller's own guard, the at-most-two-probe charge, the three geometry signatures, the successful-read lowering, and the sparse relative capacity bound stated as an inequality so the one non-size-only count is visible in the consumer rather than only in the library.| **Open.** There is no packed capstone to elaborate against, so the row's own object is still absent. The file is a real validator for the leaves and for the per-read lowering; it is not yet validation of a new machine. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch | Inherited | Every capstone conjunct is quantified over all `xs` with no size side condition. | Capstone. | Check the interior-readiness non-monotonicity does not force a size guard. | Pending | Open |

---

## 3. Frozen replay registry

Ordered exactly as commissioned. `scripts/eg_cp_final_falsification_replay.ps1` must encode
this list literally and reject missing, duplicate, reordered, or unmapped IDs.

| Order | ID | Mutation | Expected verdict | Named failing surface |
| --- | --- | --- | --- | --- |
| 1 | `A01-PRODUCTION-EXPECTED-ACCEPT` | unchanged final implementation, consumer, matrix, and result | ACCEPT | none |
| 2 | `A02-UNREAD-CELL-EXPECTED-ACCEPT` | mutate exactly one proved-unread allocated cell and preserve the pinned run/result | ACCEPT | none |
| 3 | `M01-WRONG-LONG-COUNT` | alter the header count | REJECT | liveness/consumer |
| 4 | `M02-HOST-LONG-COUNT-MIRROR` | bypass the header reply with preprocessing/host metadata | REJECT | structural consumer |
| 5 | `M03-SHAPE-PARAMETER` | add or restore a semantic `shape` input | REJECT | exact signature |
| 6 | `M04-CANONICAL-SHAPE-BY-N` | synthesize a canonical shape from `n` inside a wrapper | REJECT | structural / same-object |
| 7 | `M05-SIBLING-STORE` | read a logical/source store beside `memory xs` | REJECT | store identity |
| 8 | `M06-ANSWER-ORACLE` | call the reference/semantic answer from controller execution | REJECT | oracle independence |
| 9 | `M07-DISCONNECTED-TRACE` | retain a correct result while forging or replaying an unrelated physical trace | REJECT | trace execution |
| 10 | `M08-FORGED-PROBE-CAP` | replace derived trace length/cap evidence with a stored number or theorem-only field | REJECT | consumer |
| 11 | `M09-WRONG-CELL-CROSSING` | mutate one crossing codec order/bit span | REJECT | exact decoded word |
| 12 | `M10-SPARSE-COUNT-DEPENDENCY` | introduce sparse-count metadata into a live offset | REJECT | K1 source factorization |
| 13 | `M11-SIBLING-PAYLOAD` | prove space for one payload while executing another | REJECT | public / same-object composition |
| 14 | `M12-PUBLIC-TYPE-WEAKENING` | remove one load-bearing capstone conjunct | REJECT | independently frozen expected-type consumer |
| 15 | `M13-HIDDEN-UNCOUNTED-TABLE` | add a content-dependent lookup/program constant outside `memory xs` | REJECT | closed controller / program accounting |
| 16 | `M14-LONG-COUNT-IGNORED` | retain the header read but make downstream offsets independent of its value | REJECT | liveness |

### Replay harness contracts

| ID | Exact frozen requirement | Evidence obtained | Status |
| --- | --- | --- | --- |
| `REPLAY-EXACT-REGISTRY` | encode the complete ordered frozen registry literally, validate uniqueness/order/mappings and exact verdict counts, and reject omission or duplication. | The registry is a literal ordered array in the script. `Test-RegistryIntegrity` runs before any build and checks sixteen entries, ascending orders 1..16, unique IDs, every verdict mapped, and exactly 2 ACCEPT against 14 REJECT; any omission, duplication or reordering fails the run before a single case executes. Verified on every invocation of the 2026-08-04 runs. | **Open.** The integrity checks pass, but the row is part of `FG-12`, which cannot close while seven commissioned cases have no failing surface. |
| `REPLAY-SELECTOR-NONVACUITY` | a valid selector executes exactly one requested case; unknown, explicit empty, and whitespace selectors fail; only omitted selection may mean full mode. | `-Case <ID>` executes exactly one case; the 2026-08-04 runs exercised eight distinct single-case selections. An unknown selector exits 2 (`REPLAY-FAIL: unknown selector`), a whitespace selector exits 2, and `[AllowEmptyString()]` on the parameter routes the explicitly empty selector to the harness's own check rather than to parameter binding. Only omitting the parameter means full mode. | **Open.** The selector contract is satisfied and demonstrated; the row closes with `FG-12`. |
| `REPLAY-SUBPROCESS-DEADLINE` | every external stage has an evidence-based positive deadline, timeout is failure, the owned root and descendants are terminated on every gate OS, cleanup/restoration runs in `finally`, and a cheap descendant sleeper self-test precedes the semantic campaign. | The per-case deadline is derived from a measured clean build of the surface module (four times the measurement, floor 300 s), not guessed; timeout is failure. The harness drives `System.Diagnostics.Process` directly and drains both pipes asynchronously, because `Start-Process -PassThru` reported a non-zero exit code for a build that succeeds when run directly and a full pipe would turn a semantic failure into a spurious timeout. `Stop-ProcessTree` uses `taskkill /T /F` on Windows and negated-pid `kill` on Linux, selected by probing for `$IsWindows` rather than reading it. The descendant self-test spawns a detached grandchild sleeper and requires it dead after the root is killed: PASS on 2026-08-04. Restoration runs in `finally` and is verified by SHA256 against the bytes the harness found. | **Open.** Every listed contract is implemented and exercised on Windows. The Ubuntu branch of `Stop-ProcessTree` is written but has not been run on that gate, and the row asks for termination on every gate OS. The row also closes with `FG-12`. |

---

## 4. Verification command ledger

Roles: D = development-loop, F = final-required, C = conditional.

| ID | Command | Role | Rows covered | Unique failure mode | Tree identity | Expected runtime / chosen deadline | Outcome |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `CHK-00` | `scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a... -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "<actual runtime catalog>"` | F | governance precondition | stale/missing role skill | base `1490c97`, re-run at `6078a29` | seconds / 120s | PASS twice. First run (2026-08-03) declared `rmq-proof-sprint` alone. Re-run (2026-08-04) at checkout `6078a29` declared the complete actual runtime catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; governance verified as an ancestor; expected, checkout, working-tree and runtime sets all equal; `required_mode=role-skills`. |
| `CHK-01` | `lake env lean RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Capstone.lean` | F | `FG-01`..`FG-11`, `FG-13` | capstone does not elaborate | final tree | to be recorded | Pending |
| `CHK-02` | `lake env lean RMQ/Validation/EGCPFinalFalsification.lean` | F | `FG-12`, `INV-VALIDATION-REACH` | expected-type consumer does not pin the capstone | final tree | to be recorded | **PASS** at `c472146` (2026-08-04): `lake build RMQ.Validation.EGCPFinalFalsification` completes. The root now also pins the physical read, the packed-backed store, the address-width bound and both named thresholds. |
| `CHK-03` | `powershell -ExecutionPolicy Bypass -File scripts\eg_cp_final_falsification_replay.ps1` (full mode, exactly once) | F | `FG-12`, `INV-MUTATION-REPRODUCIBILITY` | a mutation is not actually rejected | committed clean candidate | to be recorded | **RAN, INCOMPLETE** at `c472146` (2026-08-04), exactly once in full mode: 16 cases considered, 9 as commissioned at their named surfaces, 7 `TARGET-ABSENT`, descendant self-test PASS, restorations SHA256-verified, terminal tree clean, exit 7. Not a pass, by design -- see `FG-12`. |
| `CHK-04` | `lake build RMQ` | F | whole-library integration | a touched supporting module breaks a consumer | final tree | to be recorded | Pending |
| `CHK-05` | `lake env lean scripts/headline_axiom_check.lean` | F | `FG-13` | a new axiom reaches a headline | final tree | to be recorded | **PASS** at `c472146` (2026-08-04): `lake env lean scripts/headline_axiom_check.lean` exits 0 after `lake build RMQPaper`; only unused-variable linter warnings. |
| `CHK-06` | hygiene scan from `AGENTS.md` over `RMQ lakefile.toml` | F | `FG-13` | forbidden token, including as prose in a comment | final tree | seconds / 120s | **PASS** at `c472146` (2026-08-04): the `AGENTS.md` hygiene scan over `RMQ` and `lakefile.toml` returns no match, including as prose in a comment. |
| `CHK-07` | `rg -n "native_decide\|Lean\.ofReduceBool" RMQ` | F | `FG-13` | native decision shortcut | final tree | seconds / 120s | **PASS** at `c472146` (2026-08-04): `rg -n "native_decide|Lean\.ofReduceBool" RMQ` returns no match. |
| `CHK-08` | `git diff --check` and `git diff --check 1490c97b399d136bad4e18953441da433d130d4d..HEAD` | F | committed whitespace | trailing whitespace in the committed range | post-commit | seconds / 120s | Pending |
| `CHK-09` | `powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 1490c97b399d136bad4e18953441da433d130d4d` | F | `FG-15` | a design-sensitive path changed with no decision entry | final tree | to be recorded | **PASS** at `c472146` (2026-08-04) against base `1490c97`: 21 changed files checked (16 code, 3 workflow, 2 neutral), every design-sensitive path carrying a decision entry. |
| `CHK-10` | `powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | F | `FG-15` | roadmap/result prose overclaims | final tree | to be recorded | **PASS** at `c472146` (2026-08-04): `claim_drift_scan.ps1 -Strict` reports 1498 hits and 0 strict failures. |
| `CHK-11` | `powershell -ExecutionPolicy Bypass -File scripts\gate.ps1` (aggregate, at most once on the unchanged final tree) | F | aggregate certification | anything the focused checks missed | final tree | to be recorded | Pending |
| `CHK-12` | bounded import/startup smoke for the validation and replay roots | D | `FG-12` | replay deadline races Lean startup | development trees | to be recorded | **PASS** at `c472146` (2026-08-04): the replay harness measures a clean build of the surface module before any case runs and derives the per-case deadline from it, so the deadline cannot race Lean startup. |
| `CHK-13` | exact selector `A01-PRODUCTION-EXPECTED-ACCEPT`, then one representative mutation `M01-WRONG-LONG-COUNT` | D | `FG-12` | registry wiring broken before the full run is paid for | development trees | to be recorded | **PASS** at `c472146` (2026-08-04): the exact selector `A01-PRODUCTION-EXPECTED-ACCEPT` accepts and `M01-WRONG-LONG-COUNT` rejects at `PackedCellProbe/SourceGeometry.lean`, each as a single-case run before the full replay was paid for. |

CI note carried from `WDD-20260726-007`: `scripts/design_decision_check.ps1` runs in CI at
`-Base HEAD~1`, one commit at a time. Each commit on this branch must be validated at
`HEAD~1`, not cumulatively.

---

## 5. Explicitly deferred, recorded as non-blocking by the commissioning contract

| Item | Why non-blocking here |
| --- | --- |
| Public theorem/headline synchronization | The frozen target is the private Stage F falsification package, not publication. `README`, `docs/WHAT_IS_PROVED.md`, `docs/FAMILY_SUMMARY.md`, `artifact/CLAIMS.md` and headline prose are out of write scope. |
| Word-RAM refinement (time bounds, operations) | The target is explicitly a cell-probe theorem. Naming the weaker model honestly is required; upgrading it is not in scope. |
| K2 implementation, internal-padding representation, K0 self-delimiting bootstrap | Predetermined coordinator flips, not worker choices. |
| Full historical B3 small-step execution | Superseded as the primary route; supporting research only. |
| `FEASIBILITY_PASS`, Stage F / Stage A acceptance, publication headline selection | Coordinator decisions. This task closes the local rung only. |

---

## 6. Contract amendments

None. Any amendment must be recorded here with the coordinator approval that authorized it,
before the affected row's evidence changes.

---

## 7. Coordinator amendment: `EG-CP-ALLSIZE-R1`

<!-- COORDINATOR-AMENDMENT-EG-CP-ALLSIZE-R1-BEGIN -->

Coordinator authority: delegated task `EG-CP-ALLSIZE-R1`, received 2026-08-04.
Worker branch: `codex/eg-cp-allsize-reviewer-machine-r1`.
Exact base: `6bf28dee32c96da4705b139959fd35e4a782bac4` (tree
`4d173458db3e1ad33186a2f843ee7dd5cbd87d97`).
Workflow-governance ref: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`.
Frozen-matrix ancestor retained: `0a18548539035f69f68c1b44031fba64df8297f3`.

This is an append-only coordinator amendment. Every original `FG-*` row above remains
historical evidence and must remain byte-for-byte identical to the exact base blob. In
particular, the original `FG-01`/`FG-03` wording is not silently repaired. The `R2-*`
rows below are the controlling requirements for this local all-size reviewer-machine
rung. This amendment does not close the complete EG-CP node, record architecture
acceptance, or authorize merge, push, publication, or public-claim synchronization.

### 7.1 Frozen local-rung requirements

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge to attempt | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `R2-01-CONSUMED-PAYLOAD-IDENTITY` | the counted bits are exactly `concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape`, the object used by public `buildPayload` and backed by `concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_eq_global`. The older `concreteBPNativeSuccinctRMQPayload` identifier is a different flat sibling and is not an acceptable machine object. | Local rung | Checked definitional/theorem identity from `buildPayload` through serialized bits, allocated reviewer memory, physical run, and the public/reference result theorem. | `buildPayload xs` = `packedReviewerPayloadBits (cartesianShape xs)` -> serialized reviewer bits -> `packedReviewerMemory` -> `packedReviewerRunAgainstMemory`; logical simulation uses the reviewer read store identified with the global store. | Substitute the flat sibling payload/memory and require an independent exact-type consumer to fail. | `egcpAllSizeConsumedPayloadIdentity`, `egcpAllSizeConsumedPayloadIsBuildPayload`, `egcpAllSizeConsumedStoreIdentity` (`RMQ/Validation/EGCPFinalFalsification.lean:1833-1866`); the same objects flow to `egcpAllSizeSameRunPublicOutcome` and `egcpAllSizePublicCertificateExact`; replay case `M11-SIBLING-PAYLOAD` REJECTs the sibling substitution. | Closed on this rung; coordinator acceptance still required. |
| `R2-02-ALL-SIZE-SPARSE-RESOLUTION` | remove every `localStride ... = 1`, `n &lt; 2^97`, sampled-size, or "any real machine" assumption from the final chain. Either (K1) obtain every sparse-dependent address/count through a fixed bounded sequence of charged prior replies and prove the all-size factorization, or prove a quantifier-matched obstruction showing two canonical reachable executions with identical permitted K1 inputs but a required differing address/length. Inconvenience or a content-varying raw length is not obstruction. If and only if that K1 obstruction is kernel-checked, K2 is pre-authorized on this branch: add exactly one `sparseCount` header cell beside `longCount`, prove both fit/decode at one query-independent width, rebuild exact length/allocation/offsets all-size, and continue the same controller/run target. Do not stop merely to request this already specified choice. | Local rung | Either a quantifier-matched K1 construction, or a kernel-checked K1 obstruction followed by the exact K2 construction. The final controller/run/capstone must have no stride/cutoff hypothesis. | Header probe(s) -> decoded counts -> exact reviewer length/allocation/close offset/source offsets -> every physical request of the same run. | Search for every surviving `localStride ... = 1` premise and attempt two same-size/same-long-count canonical executions with different sparse counts; K2 may be used only after the checked K1 obstruction. | K1 survived: every sparse-dependent address/count is obtained through the fixed bounded prelude reply sequence (`egcpAllSizeSparsePreludeRequestSequence`, `egcpAllSizeSparsePreludeAddressesIndependentOfSparseCount`, `egcpAllSizeSparsePreludeExact`, `egcpAllSizeActualControllerPrelude`, VAL:1963-2015); no `localStride = 1`, finite-cutoff, sampled-size, or readiness hypothesis survives in the capstone chain (all binders are `(n : Nat)`/`(shape)`/`(xs)`); K2 was never needed. | Closed on this rung; coordinator acceptance still required. |
| `R2-03-EXACT-LENGTH-AND-HEADER` | exact payload/serialized length, cell count, allocation and space concern the actual reviewer payload for every shape. No internal padding, sibling payload, or uncharged content count. | Local rung | Exact all-size equations for payload length, serialized length, header arity/decoding, cell count, allocated bits, and memory length, followed by the allocated-space theorem over that same memory. | Reviewer payload -> exact header ++ payload serialization -> padding only to the final allocated cell -> reviewer memory -> same run/capstone. | Mutate the header arity/count, insert internal padding, or replace the payload with the flat sibling; exact-type consumers must fail. | `egcpAllSizeClosedPayloadLengthIdentity`, `egcpAllSizeConsumedPayloadLength`, `egcpAllSizeHeaderHasOneCellWidth`, `egcpAllSizeHeaderDecodesLongCount`, `egcpAllSizeSerializedDropsToConsumedPayload`, `egcpAllSizeSerializedLengthExact`, `egcpAllSizePaddedAllocationLengthExact`, `egcpAllSizeReviewerMemoryCellCountExact`, `egcpAllSizeReviewerAllocatedSpace`, `egcpAllSizeReviewerAllocationResidual` (VAL:1868-1961). | Closed on this rung; coordinator acceptance still required. |
| `R2-04-SEGMENT20-RAGGED-LOWERING` | executed segment 20 is lowered component-by-component across all eight ragged machine-store geometries. Preserve component identity, per-entry chunking, partial final words, word order, and exact decoded equality. A flattening theorem alone is insufficient. | Local rung | One closed component tag/geometry, exact logical-index decomposition for all eight components, physical plan/decode theorem for each, and an aggregate segment-20 lowering theorem whose conclusion is exact word equality. | Executed segment-20 read -> component offset and local index -> entry chunk bit offset/short final width -> interior payload slice -> reviewer-memory probes -> identical reply. | Swap components, flatten across entry boundaries, or force a full final word; the exact lowering/consumer must fail. | `egcpAllSizeInteriorComponentsAreExactlyEight`, `egcpAllSizeInteriorCoordinates`, `egcpAllSizeInteriorWordOrder`, `egcpAllSizeInteriorCanonicalWord`, `egcpAllSizeInteriorPhysicalDecode`, `egcpAllSizeSegment20Exact`, `egcpAllSizeSegment20LogicalPlan`, `egcpAllSizeSegment20LogicalDecode` (VAL:2017-2160): exact decoded word equality across all eight ragged geometries. | Closed on this rung; coordinator acceptance still required. |
| `R2-05-PHYSICAL-REQUEST-REPLY-CONTROLLER` | model the controller as a fixed first-order protocol with proof-free state, `nextRequest`, `consumeReply`, and terminal result. Dynamic data may be only `n`, half-open endpoints, decoded header values, and prior physical replies. It must not contain `CartesianShape`, `List Int`, source/program lists, semantic stores, proof callbacks, expected answers, or precomputed offsets. The external driver may take memory; the controller may not. | Local rung | Concrete inductive/structure definitions and exact signatures for the controller state, request, reply transition, terminal result, and external driver; transitive definitions inspected and pinned. | `packedReviewerController` -> `nextRequest`/`consumeReply` -> `packedReviewerRunAgainstMemory`; only the driver indexes memory. | Attempt shape, list, answer, store, source/program-list, proof-callback, and precomputed-offset fields/signatures; independent consumers must reject them. | `egcpAllSizeValidControllerEntry`, `egcpAllSizeInvalidControllerEntry`, `egcpAllSizeInvalidRunHasZeroTrace`, `egcpAllSizeHeaderNextRequest`, `egcpAllSizeMissingReplyFails` (VAL:2229-2284) pin the proof-free first-order controller; replay case `M03-SHAPE-PARAMETER` REJECTs a semantic shape input at the exact-signature surface. | Closed on this rung; coordinator acceptance still required. |
| `R2-06-REVIEWER-MEMORY-ONLY` | every successful reply in the run comes from `packedReviewerMemory` at the requested physical cell. No `WordRAM.ReadStore` argument, global store, flat memory, or semantic callback may choose a controller result. The existing `packedWholeQueryRun` is only a logical simulation target. | Local rung | Driver-step and whole-run read-backing theorems positionally connecting each successful reply to `packedReviewerMemory[addr]?`; controller result obtained only after consuming those replies. | Physical request/reply run -> driver lookup in reviewer memory -> controller transition; separate theorem relates the completed object to `packedWholeQueryRun`. | Supply a forged logical store, flat memory, or precomputed semantic result; signature/typed consumers must fail. | `egcpAllSizeDriverMemoryOnly`, `egcpAllSizeDynamicStoreAgreement`, `egcpAllSizeEveryLogicalReadFromReviewerMemory` (VAL:2286-2326); replay cases `M05-SIBLING-STORE` and `M06-ANSWER-ORACLE` REJECT the forged store and the precomputed result. | Closed on this rung; coordinator acceptance still required. |
| `R2-07-ORDERED-WHOLE-RUN-LOWERING` | prove a position- and multiplicity-sensitive relation between the logical run and physical trace, retaining producing instruction/site, attempted versus successful reads, request addresses, replies, cell crossings, and computed invocation parameters. | Local rung | An occurrence-indexed relation and whole-run simulation theorem preserving instruction/site, logical occurrence, attempted/successful status, physical addresses/replies, crossing multiplicity, and invocation parameters. | `packedReviewerRunAgainstMemory` physical trace -> ordered lowering relation -> `packedWholeQueryRun` logical trace/result. | Duplicate/equal read occurrences, swap two probes, erase the producing site or invocation parameters, or conflate attempted and successful reads; relation must reject. | `egcpAllSizeLogicalWholeRunSimulation`, `egcpAllSizeLogicalOccurrenceSimulation`, `egcpAllSizeLoweredWholeRunSimulation`, `egcpAllSizePhysicalOccurrenceExpansion`, `egcpAllSizeActualRunLowering`, `egcpAllSizeActualRunGrouping`, `egcpAllSizeActualRunPhysicalOccurrence` (VAL:2328-2437); replay case `M07-DISCONNECTED-TRACE` REJECTs result-preserving trace disconnection. | Closed on this rung; coordinator acceptance still required. |
| `R2-08-TOTALITY-ADDRESS-CAP` | for every list and every machine-representable endpoint pair, every attempted physical request is allocated and `&lt; 2 ^ wordWidth`; the run terminates and its trace length is at most one literal constant derived after the run definition. No stored/aspirational cap. | Local rung | Universal termination, allocation, address-width, and trace-length theorem over the actual run; one literal cap introduced only after the run and proved from trace decomposition. | Same physical run object and trace consumed by correctness and validation. | Last-cell crossing, dead/sentinel address, empty/singleton/two-element inputs, invalid endpoints, and forged stored cap. | `egcpAllSizeActualRunProbeCap` and `egcpAllSizeGroupedActualRunProbeCap` (literal 427 derived from the run trace), `egcpAllSizeActualRunAllocated`, `egcpAllSizeActualRunAddressWidth`, `egcpAllSizeHeaderMeasureIsStructural` (VAL:2439-2485); replay case `M08-FORGED-PROBE-CAP` REJECTs a stored cap. | Closed on this rung; coordinator acceptance still required. |
| `R2-09-SAME-RUN-REFERENCE-CORRECTNESS` | the same physical run object returns the independent project `ReferencePacket`/guarded public semantics for valid, empty, reversed, and out-of-range queries. No semantic result may be computed first and decorated with reads afterward. | Local rung | One capstone theorem whose result projection is the guarded independent reference result and whose trace/cap/read-backing projections are those of the identical `packedReviewerRunAgainstMemory` object. | `buildPayload`/reviewer memory -> physical run -> logical simulation -> established guarded public semantics/`ReferencePacket`. | Corrupt a decisive reply, keep the result while disconnecting the trace, and exercise valid/empty/reversed/out-of-range cases. | `egcpAllSizeSameRunPublicOutcome` (VAL:2563): the identical run object's terminal/failed/state projections equal the guarded independent reference result, with the grouping in the same conjunction; `egcpAllSizeIdenticalObjectPublicConsumer` (VAL:2798) re-consumes the identical objects. | Closed on this rung; coordinator acceptance still required. |
| `R2-10-TYPED-ANTI-BYPASS` | add independent exact-type consumers pinning the concrete controller state/signatures, request/reply transition, driver, trace relation, cap theorem, correctness theorem, and identical payload/memory/run objects. Attempt shape parameter, answer oracle, supplied-store, sibling-memory, and forged-cap mutations; record which consumer fails. | Local rung | Independent expected-type consumers in `RMQ/Validation/EGCPFinalFalsification.lean`, plus replayable mutations only where concrete targets now exist. | Validation root -> exact concrete definitions/theorems -> identical payload/memory/run capstone. | Shape parameter, answer oracle, supplied store, sibling memory, forged cap, weakened trace relation, and public proposition weakening. | The entire frozen validation module elaborates, including the rung-supplied `egcpAllSizeCanonicalLogicalRequestOperandsWidth` (`packedReviewerDriveLogical_210_request_operands_fit`), `egcpAllSizeActualPhysicalRequestOperandsWidth` (`PackedReviewerRunGrouping.request_operands_fit`), `egcpAllSizeInteriorDeadAddressWidth`, `egcpAllSizePublicCertificateExact` (`packedReviewerRunAgainstMemory_public_certificate`, 26 fields), `egcpAllSizeIndependentRunFactsExact` (VAL:2745); replay stage `R2-ALLSIZE` replayed all seven commissioned mutations to commissioned REJECT with SHA-verified restoration (`REPLAY: STAGE R2-ALLSIZE PASS`). | Closed on this rung; coordinator acceptance still required. |

### 7.2 Inherited rows retained by reference

The exact requirement text for the following inherited rows remains the byte-identical
row in sections 1 and 2 above; this amendment neither duplicates nor edits it:

| ID | Local-rung obligation under this amendment | Status / residual gap |
| --- | --- | --- |
| `R2-INHERITED-FG-02` | Re-evaluate original row `FG-02-K1-SOURCE-FACTORIZATION` under the all-size K1/K2 resolution and consume the resulting geometry in the physical controller. | Closed on this rung: the K1 factorization geometry is consumed by the controller through the prelude chain (R2-02 evidence); coordinator acceptance still required. |
| `R2-INHERITED-FG-04` | The historical `FG-04-WIDTH-AND-HEADER` row stays unchanged; the controlling all-size header requirement is `R2-02`/`R2-03`, including the explicitly authorized K2 correction only after a checked K1 obstruction. | Historical row unchanged as commissioned; the controlling requirement is discharged through R2-02/R2-03 (K1 survived, K2 unused); coordinator acceptance still required. |
| `R2-INHERITED-FG-05` | Close original row `FG-05-PACKED-MEMORY` on the reviewer payload/memory actually driven by the physical run. | Closed on this rung by the R2-01/R2-03 evidence; coordinator acceptance still required. |
| `R2-INHERITED-FG-06` | Close original row `FG-06-ALLOCATED-SPACE` on the same all-size reviewer memory the run probes. | Closed on this rung by `egcpAllSizeReviewerAllocatedSpace`/`egcpAllSizeReviewerAllocationResidual` over the same memory; coordinator acceptance still required. |
| `R2-INHERITED-FG-07` | Close original row `FG-07-CLOSED-CONTROLLER` with the concrete first-order request/reply state machine and external memory driver. | Closed on this rung by the R2-05 controller and R2-06 driver evidence; coordinator acceptance still required. |
| `R2-INHERITED-FG-08` | Close original row `FG-08-PHYSICAL-CODEC-AND-CAP` with segment 20 and the ordered whole-run physical lowering, then derive the literal cap from the run trace. | Closed on this rung by the R2-04 segment-20 lowering, R2-07 ordered lowering, and the literal 427 cap of R2-08; coordinator acceptance still required. |
| `R2-INHERITED-FG-09` | Close original row `FG-09-PROBE-TOTALITY-AND-SAME-OBJECT-CORRECTNESS` with totality and correctness on the identical physical run object for all guarded query cases. | Closed on this rung by the R2-08 totality/width and R2-09 same-object correctness evidence; coordinator acceptance still required. |
| `R2-INHERITED-FG-10` | Close the local concrete anti-bypass targets of original row `FG-10-ANTI-VACUITY` required by `R2-10`; deferred full-node mutations remain explicitly open below. | Local concrete anti-bypass targets closed by the `R2-ALLSIZE` replay stage (seven commissioned REJECTs); deferred full-node mutations remain open as commissioned; coordinator acceptance still required. |

### 7.3 Inherited invariant matrix

| ID | Exact inherited requirement | Evidence needed for this rung | Named consumer and object chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands | Every attempted physical address of the request/reply run is `< 2 ^ packedReviewerCellWidth n`; any controller operands are likewise bounded. | `packedReviewerRunAgainstMemory` trace. | Final cell, crossing successor, dead/sentinel and maximal machine-representable endpoints. | `egcpAllSizeActualRunAddressWidth`, `egcpAllSizeActualPhysicalRequestOperandsWidth`, `egcpAllSizeCanonicalLogicalRequestOperandsWidth`, `egcpAllSizeInteriorDeadAddressWidth` (all-size via the realizing-shape generalization), `egcpAllSizeLogicalControlTagsWidth`, `egcpAllSizePhysicalControlTagsWidth`, `egcpAllSizeControllerPhaseTagWidth`, and the reachable envelope `packedReviewerCanonicalReachable_state_machine_fits`. | Closed on this rung; coordinator acceptance still required. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch | No `localStride = 1`, finite cutoff, sampled-size, readiness, or compatibility hypothesis in the capstone chain. | All reviewer length/memory/controller/run/correctness theorems. | Empty, singleton, size two, threshold boundaries, reversed and out-of-range endpoints. | Every theorem in the chain binds `(n : Nat)`/`(shape : CartesianShape)`/`(xs : List Int)` with no stride, cutoff, sampled-size, readiness, or compatibility hypothesis (hygiene scans empty); `egcpAllSizeSameRunPublicOutcome` covers valid/empty/reversed/out-of-range through the guarded reference. | Closed on this rung; coordinator acceptance still required. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding. | One reviewer memory and a translation/lowering for every logical read occurrence, including segment 20 and any failed/dead occurrence. | `packedReviewerMemory` -> driver -> whole physical trace -> logical run. | Remove one segment/component or substitute a sibling memory. | One `packedReviewerMemory shape`, driver-only indexing (`egcpAllSizeDriverMemoryOnly`), and per-occurrence lowering including segment 20 and failed/dead occurrences (R2-04/R2-07 evidence); `M11-SIBLING-PAYLOAD` REJECTs the sibling. | Closed on this rung; coordinator acceptance still required. |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim | Physical trace is generated by repeated `nextRequest`/memory lookup/`consumeReply`; the result is not available earlier. | Same physical run object used by cap and correctness. | Preserve the answer while replacing the trace by decoration or replay. | The trace is generated only by `nextRequest`/memory lookup/`consumeReply` (`egcpAllSizeEveryLogicalReadFromReviewerMemory`, `egcpAllSizeActualRunLowering`); `M07-DISCONNECTED-TRACE` REJECTs decoration. | Closed on this rung; coordinator acceptance still required. |
| `INV-ORACLE-INDEPENDENCE` | executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested | Correctness targets the established independent reference/guarded public semantics. | Physical run result -> logical simulation -> reference packet. | Answer-oracle mutation and implementation-as-expected-value fixture. | `egcpAllSizeSameRunPublicOutcome` targets the independent guarded reference semantics; `M06-ANSWER-ORACLE` REJECTs the oracle mutation. | Closed on this rung; coordinator acceptance still required. |
| `INV-PROGRAM-ACCOUNTING` | input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation | Controller text and state contain only fixed schema, `n`, endpoints, decoded header values and physical replies. | Concrete controller definition and exact-type consumer. | Hidden content-dependent table, shape-derived offset, or source/program list. | The controller state carries only fixed schema, `n`, endpoints, decoded header values and replies (`egcpAllSizeValidControllerEntry` exact signature); `M03-SHAPE-PARAMETER` REJECTs a semantic shape field. | Closed on this rung; coordinator acceptance still required. |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information | Concrete state/request/reply types contain no proof field; the executable result/route depends only on data replies. | `packedReviewerController` and `consumeReply`. | Add proof callback/answer certificate to state. | The concrete state/request/reply types are proof-free (exact-signature consumers); the executable result depends only on consumed replies (`egcpAllSizeMissingReplyFails`). | Closed on this rung; coordinator acceptance still required. |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store | Each successful physical reply equals the addressed reviewer-memory cell at the same occurrence. | Driver trace -> reviewer memory. | Swap equal/repeated replies or erase positions. | `egcpAllSizeEveryLogicalReadFromReviewerMemory` and the occurrence-indexed `egcpAllSizeActualRunPhysicalOccurrence` back every successful reply positionally by the counted store. | Closed on this rung; coordinator acceptance still required. |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace | Agreement on the ordered physical requests/replies determines the controller transcript and terminal result. | Request/reply determinism theorem over the concrete controller. | Stores agree on a set but disagree in ordered/multiplicity-sensitive replies. | `egcpAllSizeDynamicStoreAgreement`: ordered request/reply agreement determines the transcript and terminal result of the concrete controller. | Closed on this rung; coordinator acceptance still required. |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient | Definition/theorem identity from `buildPayload` to reviewer serialization/memory and the exact physical run. | `R2-01` chain. | Flat sibling payload/memory substitution. | The R2-01 identity chain (`egcpAllSizeConsumedPayloadIdentity` through the run and capstone); `M11-SIBLING-PAYLOAD` REJECTs the substitution. | Closed on this rung; coordinator acceptance still required. |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe | Physical trace is accumulated only by actual driver steps; logical relation is occurrence-indexed. | Same run object in lowering/cap/correctness. | Disconnected or reordered trace mutation. | The physical trace accumulates only through driver steps (`egcpAllSizeActualRunLowering`, occurrence-indexed relation of R2-07); `M07-DISCONNECTED-TRACE` REJECTs. | Closed on this rung; coordinator acceptance still required. |
| `INV-VALIDATION-REACH` | executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine | Validation pins and exercises the new controller, driver, trace relation, cap and correctness types. | `RMQ/Validation/EGCPFinalFalsification.lean` -> new controller/run module. | Remove the new import/consumer and ensure validation fails. | `RMQ/Validation/EGCPFinalFalsification.lean` imports the state-proof module and elaborates end-to-end against the new controller, driver, trace relation, cap, correctness, and certificate types; all seven replay REJECTs fail exactly at this surface. | Closed on this rung; coordinator acceptance still required. |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | One `packedReviewerCellWidth n` bounds both header fields, cells, requests, operands and returned words, with the existing size relation retained. | Header/memory/controller/run/capstone. | Introduce a wider subcomponent or content-dependent width. | One `packedReviewerCellWidth n` bounds header fields, cells, requests, operands and returned words across the R2-08/R2-10 width consumers; `egcpAllSizeReviewerWordWidthLogarithmic` retains the size relation. | Closed on this rung; coordinator acceptance still required. |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word | Every reviewer-memory cell and every decoded logical/controller word is bounded by the same width. | Reviewer memory and run result. | Over-wide interior entry and partial-final-word cases. | `egcpAllSizeActualReplyWidth` and `egcpAllSizeActualReplyValueWidth` bound every successful reply by the one declared width; the interior entry-width bound rides in the R2-04 lowering. | Closed on this rung; coordinator acceptance still required. |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient | The transition invariant and correctness refinement trace the terminal result and decisive branches back to consumed physical replies. | `consumeReply` chain -> terminal result -> reference correctness. | Decisive-reply corruption and disconnected-log mutation. | The coupled controller invariant traces the terminal result and decisive branches back to consumed physical replies (`PackedReviewerCanonicalControllerCoupledInvariant.consume` through `egcpAllSizeSameRunPublicOutcome`); `M06-ANSWER-ORACLE` and `M07-DISCONNECTED-TRACE` REJECT the two commissioned mutations. | Closed on this rung; coordinator acceptance still required. |

### 7.4 Verification command ledger for this amendment

| ID | Command | Role | Rows covered | Unique failure mode | Tree identity / expected runtime / deadline | Outcome |
| --- | --- | --- | --- | --- | --- | --- |
| `R2-CHK-00` | `scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a8a52b8d61ead5e96d72a8a849bc094b5 -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"` | Final precondition | governance | stale/missing governed skill | base `6bf28dee`; seconds / 120 s | PASS before edits: expected, checkout, working and runtime catalogs all equal; required role present. |
| `R2-CHK-01` | direct pinned-toolchain compilation of every new segment-20/controller/run module | Development then final-required | `R2-02`..`R2-09` | first local theorem/signature failure | dirty development trees, then frozen final tree; recent focused modules are sub-minute / 300 s | PASS: every implementation commit was preceded by a focused green build of its changed module (state-proof builds 39-52 s each); the frozen final tree is covered by `R2-CHK-03`. |
| `R2-CHK-02` | direct pinned-toolchain compilation of `RMQ/Validation/EGCPFinalFalsification.lean` | Development then final-required | `R2-10`, `INV-VALIDATION-REACH` | typed consumer does not elaborate | dirty development trees, then frozen final tree; recent direct validation build is sub-minute / 600 s | PASS on the frozen final tree: `lake build RMQ.Validation.EGCPFinalFalsification` exit 0 (1 m 54 s cold, 1-2 s warm). |
| `R2-CHK-03` | `lake build RMQ` | Final-required | integration and all Lean rows | transitive consumer failure | unchanged final tree; prior broad builds are multi-minute / 1800 s | PASS: `lake build RMQ` exit 0 in 3 m 38 s on the frozen final tree. |
| `R2-CHK-04` | `powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 6bf28dee32c96da4705b139959fd35e4a782bac4` | Final-required | design-sensitive changes | missing/invalid decision record | unchanged final tree / 300 s | PASS: `DESIGN-CHECK: checked 31 changed files (25 code, 3 workflow, 3 neutral)`, exit 0. |
| `R2-CHK-05` | applicable strict claim-drift scan | Final-required because matrix/result/decision prose changes | evidence prose | overclaim or stale status | unchanged final tree / 300 s | PASS: `CLAIM-DRIFT: scan complete (1511 hits, 0 strict failures)`, exit 0. |
| `R2-CHK-06` | `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml` | Final-required | forbidden shortcuts/trust | forbidden declaration/import | unchanged final tree / 120 s | PASS: zero matches over `RMQ` and `lakefile.toml`. |
| `R2-CHK-07` | `rg -n "native_decide|Lean\.ofReduceBool" RMQ` | Final-required | forbidden computation shortcuts | native decision shortcut | unchanged final tree / 120 s | PASS: zero matches over `RMQ`. |
| `R2-CHK-08` | strict UTF-8 byte comparison of every original `FG-*` row against `6bf28dee32c96da4705b139959fd35e4a782bac4` | Before expensive final verification and final-required | frozen-row integrity | historical row silently changed, duplicated, omitted, or mojibake introduced | candidate versus exact base / 120 s | PASS: the matrix diff against the exact base is append-only (102 insertions inside the amendment markers, 0 deletions) and mojibake-free; every historical row is byte-identical. |
| `R2-CHK-09` | `git diff --check 6bf28dee32c96da4705b139959fd35e4a782bac4..HEAD` plus working-tree `git diff --check` | Final-required after commit | committed-range hygiene | clean worktree hides committed whitespace | final commit / 120 s | PASS: `git diff --check` over the committed base range and the working tree reports nothing (re-run after the final documentation commit). |
| `R2-CHK-10` | clean index and untracked-state check | Final-required | handoff hygiene | unstaged/untracked evidence | final commit / 120 s | PASS: `git status --porcelain` empty on the final candidate commit. |
| `R2-CHK-11` | replay bounded startup, one positive selector, one relevant mutation, then the final registry stage owned by this rung | Conditional: only if concrete targets make a replay edit necessary | concrete `R2-10` cases and inherited replay contracts | selector/deadline/restoration defect | progressively frozen trees; deadline derived from observed startup/full-case runtime | RAN as required by the concrete `R2-10` targets: bounded startup with measured deadline, positive selector `-Case M03-SHAPE-PARAMETER` (SELECTED CASE OK), then `-Stage R2-ALLSIZE` PASS: all seven commissioned mutations REJECT with SHA-verified restoration and terminal clean tree. One recorded harness repair: the never-yet-run stage selector crashed the Windows PowerShell 5.1 dynamic binder (`@(...)` over a generic list); replaced by plain array accumulation, replaying identically. |
| `R2-CHK-12` | aggregate gate | Conditional only if the final changed surface uniquely requires coverage not owned by the mandatory commands above | broad integration | duplicated expensive certification | unchanged final tree; run at most once | Explicitly skipped as redundant: every changed surface is owned by `R2-CHK-01`..`R2-CHK-11` (focused builds, full `lake build RMQ`, direct validation build, and the replay stage); no surface requires additional coverage. |

### 7.5 Explicit deferrals and node boundary

| ID / item | Exact disposition for this rung | Status |
| --- | --- | --- |
| `R2-DEFER-FG-11` | `FG-11` liveness mutations are explicitly deferred except where a new local theorem is an unavoidable prerequisite. | Blocking for the full node, non-blocking for this rung. |
| Full `FG-12` registry completion | Explicitly deferred; preserve `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, and `REPLAY-SUBPROCESS-DEADLINE`, and make any newly reachable local case replayable if replay is edited. | Blocking for the full node, non-blocking for this rung. |
| `R2-DEFER-FG-14` | The complete `FG-14` boundary campaign is explicitly deferred beyond the boundary theorems needed for `R2-08`/`R2-09`. | Blocking for the full node, non-blocking for this rung. |
| `R2-DEFER-FG-15` | The `FG-15` final architecture publication record is explicitly deferred. | Blocking for the full node, non-blocking for this rung. |
| Fresh-blind exact-commit audit and coordinator reconstruction | Required after worker candidate completion; not performed or claimed by this worker. | Required before acceptance; not a worker closure row. |
| Full EG-CP node | Remains open until `FG-01` through `FG-15`, every inherited invariant, exact replay, coordinator reconstruction, and fresh-blind audit close. | Not claimed by this local rung. |

<!-- COORDINATOR-AMENDMENT-EG-CP-ALLSIZE-R1-END -->

<!-- COORDINATOR-REPAIR-EG-CP-ALLSIZE-R2R1-BEGIN -->

## 8. R2R1 repair addendum: semantic replay fidelity, axiom inventory, wording

Append-only repair record commissioned by the coordinator (`R2R1`). Every
original `FG-*` row, every `R2-*` requirement, and every frozen registry row
above remains byte-for-byte unchanged; this addendum records only the repair
evidence. Frozen registry controls (sixteen IDs, order, mutation
descriptions, expected verdicts, selectors, deadline contracts, restoration
contracts, process-tree controls) are untouched.

### 8.1 The defect

The prior `M05-SIBLING-STORE`, `M06-ANSWER-ORACLE`, `M07-DISCONNECTED-TRACE`,
and `M11-SIBLING-PAYLOAD` implementations appended unused optional parameters
to load-bearing signatures. Their REJECT verdicts were produced exclusively by
exact-signature pins, so the replay evidence certified arity sensitivity, not
the frozen semantic requirements. `M03-SHAPE-PARAMETER` legitimately remains a
signature mutation (its frozen requirement is the concrete controller
signature); `M08` and `M12` were already semantic and are unchanged.

### 8.2 The repaired mutants

Each repaired mutant modifies a load-bearing definition body, enacts the
frozen behavior, and is rejected at the module whose guarding theorem
genuinely fails. The runner now performs a mechanical activation check after
writing each mutant: every declared needle must be present in the written
body before any build is attempted, so a signature-only or unused-parameter
edit can no longer produce a REJECT (`WDD-20260805-002`).

| Case | Patched behavior (load-bearing body) | Activation needles | Observed failing consumer |
| --- | --- | --- | --- |
| `M05-SIBLING-STORE` | The external driver `packedReviewerRunAgainstMemory` binds `siblingLogicalStore := memory ++ [[]]` and drives `packedReviewerDriveAgainstMemoryAux` against that sibling store beside the counted memory. | `let siblingLogicalStore := memory ++ [[]]`; `packedReviewerDriveAgainstMemoryAux siblingLogicalStore` | `packedReviewerRunAgainstMemory_memory_only` fails; REJECT at `PackedCellProbe/ReviewerController.lean`. |
| `M06-ANSWER-ORACLE` | The whole-query normalization's completion arm discards the computed value and returns `semanticAnswerOracle := some n`, a metadata-derived answer influencing the returned result. | `let semanticAnswerOracle := some n`; `.done semanticAnswerOracle` | The same-run correctness/driver-structure proofs fail; REJECT at `PackedCellProbe/ReviewerControllerProof.lean`. |
| `M07-DISCONNECTED-TRACE` | The valid-branch of `packedReviewerExpectedPhysicalTrace` is replaced by a disconnected forged trace (`disconnectedForgedTrace := []`) while the result path under challenge is untouched. | `let disconnectedForgedTrace : List PackedReviewerPhysicalEvent := []`; `; disconnectedForgedTrace)` | The grouping/lowering theorems over the expected trace fail; REJECT at `PackedCellProbe/ReviewerControllerProof.lean`. |
| `M11-SIBLING-PAYLOAD` | `packedReviewerSerializedBits` embeds `siblingExecutionPayload := packedReviewerPayloadBits shape ++ [false]`, so execution consumes a sibling payload while the public space/object chain remains pinned to the original. | `let siblingExecutionPayload := packedReviewerPayloadBits shape ++ [false]`; `++ siblingExecutionPayload` | The exact serialized-length/identity theorems fail; REJECT at `PackedCellProbe/ReviewerMemory.lean`. |

Calibration evidence (single-case replay on the pre-freeze tree with
identical Lean and script blobs): all four cases reported the activation
check passed, `REJECT as commissioned` at the surfaces above, and SHA256
restoration verified. The `ExpectFile` of each repaired entry names the
observed failing module, so a rejection caused by unrelated breakage cannot
be recorded as the commissioned verdict. Final certification is the single
`-Stage R2-ALLSIZE` run on the frozen repair commit, recorded in the result
report and the worker terminal response.

### 8.3 Public axiom inventory (`R2R1-02`)

`scripts/axiom_check.lean` gained curated `#print axioms` entries for
`packedReviewerPayloadBits_eq_buildPayload`,
`packedReviewerMemory_length_mul_width_le`, `packedReviewerRho_littleO`,
`packedReviewerRunAgainstMemory_trace_length_le_427`,
`packedReviewerRunAgainstMemory_public_outcome`, and
`packedReviewerRunAgainstMemory_public_certificate`. Receipt
(`lake env lean scripts/axiom_check.lean`, exit 0): every one of the six
depends only on `[propext, Classical.choice, Quot.sound]`, with the trace-cap
theorem on `[propext, Quot.sound]` alone. No custom axiom, `sorryAx`, or
native-reduction axiom appears.

### 8.4 Wording accuracy (`R2R1-03`)

The simulation docstring no longer says "fixed 210-read"; it says "210-fuel
... at most 210 logical attempts, not an exact read count"
(`DD-20260805-075`). The validation header inventory now states that the
controller, whole-run lowering, same-run correctness, and the locally owned
seven-case `R2-ALLSIZE` replay exist and are pinned, while full `FG-11`
liveness and the complete sixteen-case `FG-12` replay remain open full-node
obligations. Nothing describes `210` as an exact read count, nor the theorem
as word-RAM instruction time or `S1` bit-addressed serialized-payload
querying.

<!-- COORDINATOR-REPAIR-EG-CP-ALLSIZE-R2R1-END -->

<!-- COORDINATOR-DISPOSITION-EG-CP-ALLSIZE-INT-R1-BEGIN -->

---

## 9. Coordinator disposition: local rung `EG-CP-ALLSIZE-R1` `ACCEPTED`

Append-only coordinator record (`EG-CP-ALLSIZE-INT-R1`, 2026-08-05). Every
original `FG-*` row, every `R2-*` requirement, every inherited invariant row,
every frozen registry row, and the entire `R2R1` addendum above remain
byte-for-byte unchanged; this section adds only the disposition. It does not
edit, reopen, or re-freeze any row above.

### 9.1 Exact identities, independently reconstructed

Reconstructed from the Git objects, not from any worker or auditor prose.

| Object | Exact value |
| --- | --- |
| Rung base | `6bf28dee32c96da4705b139959fd35e4a782bac4`, tree `4d173458db3e1ad33186a2f843ee7dd5cbd87d97` |
| Frozen `R2R1` proof-bearing repair | `368b828e0711dfd10a04ca90eb19c7b0d6ccfd13`, tree `730a8746240bdf6f705d67f9283f6d9db8f25123` |
| Audited candidate | `a0a0f92b8f9081ee59797affb5045952d9e39fbf`, tree `ffc90f00b3cd864921e9fc23233e30b5432ad3d8`, parent `368b828` |
| Fresh-blind audit report commit | `118284833eb312fc06e794dd0708f48b4909dbd1`, tree `e991ca8317bf26fd1e435e80342935ac61bb7dc0`, parent `a0a0f92` |
| `git rev-list --count 6bf28dee..a0a0f92` | **40** |
| `git diff --name-status 6bf28dee a0a0f92` | **32** changed tracked paths |
| `git rev-list --count 6bf28dee..1182848` | **41** |
| `git diff --name-status a0a0f92 1182848` | exactly one path added: `docs/internal/audit_reports/2026-08-05_EG_CP_ALLSIZE_R2_fresh_blind.md` |
| `git diff --name-status 368b828 a0a0f92` | exactly one path: `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md` (the candidate tip is report-only over the frozen proof bytes) |

The 40-versus-41 distinction is the substance of coordinator correction (a) in
section 9.3: 40 commits were audited; 41 is the distance of the report commit
itself.

### 9.2 What this coordinator reconstructed rather than accepted on report

Acceptance does **not** rest on the auditor's verdict, on Claude prose, on a
green strict scan, or on declaration names. Independently re-derived here:

- **Exact identity and scope arithmetic** -- every row of 9.1, by direct
  `git rev-parse` / `rev-list` / `diff --name-status`.
- **Guarded blob identity.** Every `RMQ.lean`, `RMQ/**/*.lean`,
  `scripts/eg_cp_final_falsification_replay.ps1`, and `scripts/axiom_check.lean`
  blob -- **327 paths** -- is byte-identical between `a0a0f92` and `1182848`,
  compared by Git blob SHA, with no path present on only one side. The audit
  report therefore describes the same proof and executable bytes it was
  committed on top of.
- **Frozen-row byte integrity** (`FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`).
  Both matrix blobs were decoded as **strict** UTF-8 (invalid sequences would
  throw), checked for BOM and for U+FFFD, and every table row was keyed by the
  pair *(section heading, stable ID)* -- the section scope is load-bearing,
  because the fifteen `INV-*` IDs deliberately recur in section 7.3 with
  rung-specific evidence and a global keying would misreport them as
  duplicates. Result: **51 inherited row IDs byte-identical, 0 missing, 0
  duplicated, 0 changed**; the 53 added IDs all lie inside sections 7 and 8.
  The `6bf28dee..1182848` matrix diff is `+175 / -0`, i.e. append-only.
- **Registry enumeration.** The sixteen frozen entries were re-read from the
  runner source and re-partitioned by hand (see 9.4); this is the basis of
  coordinator correction (b).
- **Replay-stage membership.** `$script:Stages['R2-ALLSIZE']` is exactly the
  seven IDs the addendum names.

Relied on as valid prior exact-tree evidence, deliberately **not** repeated
(see 9.7): the independent Lean builds, the axiom run, and the seven-case
`R2-ALLSIZE` replay.

### 9.3 Corrections applied to the fresh-blind audit report

Both are bookkeeping (`P3`) defects in the report's own prose. Neither
disturbs an evidence claim, and both are marked in place as coordinator
corrections so the original text stays recoverable.

| # | Location | Correction |
| --- | --- | --- |
| (a) | Section 1, "Branch audited" | "41 commits above base" -> **40**, with the report commit's own 41-commit distance stated separately. |
| (b) | Section 9, "Best next target" | "the seven outstanding registry cases" -> the exact registry partition of 9.4. Seven is the size of the *replayed* stage, not the remainder. |

### 9.4 Exact frozen-registry state (basis of correction (b))

| Group | Count | IDs |
| --- | --- | --- |
| Replayed by this rung's `R2-ALLSIZE` stage | 7 | `M03`, `M05`, `M06`, `M07`, `M08`, `M11`, `M12` |
| Non-`R2`-stage, `Target = $null` -- commissioned surface does not yet exist, each replays `TARGET-ABSENT` | 4 | `A02-UNREAD-CELL-EXPECTED-ACCEPT`, `M02-HOST-LONG-COUNT-MIRROR`, `M04-CANONICAL-SHAPE-BY-N`, `M13-HIDDEN-UNCOUNTED-TABLE` |
| Non-`R2`-stage, already runnable from the prior registry campaign | 5 | `A01-PRODUCTION-EXPECTED-ACCEPT`, `M01-WRONG-LONG-COUNT`, `M09-WRONG-CELL-CROSSING`, `M10-SPARSE-COUNT-DEPENDENCY`, `M14-LONG-COUNT-IGNORED` |

Outstanding `FG-12` work is therefore: enact targets for the **four** null
entries, then certify all sixteen in one campaign. The five runnable entries
need re-certification against the current tree, not construction.

### 9.5 Disposition of the audit's `P3` findings

- **`P3-1` (title drift), resolved append-only.** Section 7.2 cites three
  inherited rows by titles that do not appear in section 1. The frozen text is
  **not** edited; the mapping is recorded here instead, and the numeric IDs
  make it unambiguous:

  | Cited in 7.2 | Canonical title in section 1 |
  | --- | --- |
  | `FG-08-PHYSICAL-CODEC-AND-CAP` | `FG-08-PHYSICAL-LOWERING` |
  | `FG-09-PROBE-TOTALITY-AND-SAME-OBJECT-CORRECTNESS` | `FG-09-TOTALITY-AND-CAP` |
  | `FG-10-ANTI-VACUITY` | `FG-10-SAME-RUN-CORRECTNESS` |

  Any future amendment should use the canonical titles. No evidence is
  affected: the 7.2 obligation text is self-contained.

- **`P3-2` (scope of the `M06` mutant), recorded without upgrade.** The
  enacted `M06-ANSWER-ORACLE` body substitutes a **metadata-derived**
  precomputed result (`some n`) for the computed completion value. It is
  **not** a literal call to the independent reference semantics, so it does
  not by itself exercise the full smuggle-the-right-answer direction of an
  answer oracle. That is the honest reading of the mutant, and this
  disposition does not silently upgrade it.

  Local acceptance of `R2-06` / `INV-ORACLE-INDEPENDENCE` /
  `INV-VALUE-DEPENDENCY` accordingly rests on **the positive theorems plus the
  scoped mutation evidence**, not on `M06` alone: the closed proof-free
  controller and driver-only memory indexing
  (`egcpAllSizeValidControllerEntry`, `egcpAllSizeDriverMemoryOnly`,
  `egcpAllSizeEveryLogicalReadFromReviewerMemory`), the coupled-invariant
  result dependency carrying the terminal value back to consumed physical
  replies (`PackedReviewerCanonicalControllerCoupledInvariant.consume` through
  `egcpAllSizeSameRunPublicOutcome`), and the joint `M06` (result path is
  live) / `M07` (trace connection is load-bearing) rejections.

  **Obligation carried forward:** the later full-registry campaign must either
  enact the exact answer-oracle predicate -- a mutant that genuinely consults
  the independent reference semantics -- or prove a checked bridge from the
  enacted predicate to it. Until one of those exists, no document may describe
  `M06` as having refuted a reference-semantics oracle.

- **`P3-3` (stale ledger row), annotated.** The pre-repair `R2-ALLSIZE` row in
  `EG_CP_FINAL_FALSIFICATION_RESULT.md` section 9 is now marked
  `SUPERSEDED` in place, pointing to the `R2R1` repair (section 8 above,
  `WDD-20260805-002`) and to the fresh-blind audit's independent rerun.

### 9.6 Disposition

**Local rung `EG-CP-ALLSIZE-R1` is `ACCEPTED`** at exact candidate
`a0a0f92b8f9081ee59797affb5045952d9e39fbf`, on the evidence of fresh-blind
audit report commit `118284833eb312fc06e794dd0708f48b4909dbd1`
(`LOCAL_RUNG_ACCEPTABLE`, no `P0`/`P1`/`P2` finding) together with the
independent coordinator reconstruction of 9.2. No `P0`, `P1`, or `P2` source
defect was found by this coordinator; the three `P3` bookkeeping defects are
corrected or recorded above, before integration.

**Separately, and explicitly still open:**

| Item | Status |
| --- | --- |
| Full EG-CP falsification node (`FG-01`..`FG-15`) | **OPEN.** `FG-11`, full `FG-12`, `FG-14`, `FG-15` are unclosed. |
| `FEASIBILITY_PASS` (Stage F outcome) | **NOT RECORDED.** Requires the residual campaign above plus coordinator review of the exact final evidence. |
| Stage A packed-architecture acceptance (`A01`..`A13`) | **NOT STARTED.** May be frozen only after `FEASIBILITY_PASS`. |
| Public-claim synchronization, headline selection | **OPEN**, untouched by this rung. |
| `S1`, `V1` | **OPEN**, untouched by this rung. |
| Architecture acceptance | **NOT RECORDED.** This is a local rung acceptance only. |

Accepting this rung records that the all-size reviewer machine is a sound
local rung. It does **not** assert that the packed cell-probe architecture is
accepted, and nothing here describes the `210` figure as an exact read count
or as a word-RAM time bound: it is driver fuel bounding logical attempts
(`DD-20260805-075`).

### 9.7 Replay controls and verification economics

The runner controls `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, and
`REPLAY-SUBPROCESS-DEADLINE` are **preserved and not re-certified by this
integration**. They remain inputs to the later full-registry campaign; a
documentation-only integration commit is not evidence for them.

No Lean build, axiom check, or semantic replay was repeated here. The
justification is mechanical rather than economic: every `RMQ.lean`,
`RMQ/**/*.lean`, replay-runner, and axiom-script blob is byte-identical to the
audited objects (9.2, 327 paths), and this integration changes only
documentation. Repeating a multi-minute Lean or replay certification on
bit-identical inputs would add no coverage. Had any such blob differed, that
difference would have been out of scope for this task and grounds to stop
rather than to repair.

<!-- COORDINATOR-DISPOSITION-EG-CP-ALLSIZE-INT-R1-END -->


<!-- COORDINATOR-AMENDMENT-EG-CP-STAGEF-CLOSE-R2-BEGIN -->

---

## 10. Coordinator residual-closure amendment: `EG-CP-STAGEF-CLOSE-R2`

Coordinator authority: delegated task `EG-CP-STAGEF-CLOSE-R1`, received
2026-08-06, reconstructed on clean history by the coordinator-commissioned
repair task `EG-CP-STAGEF-CLOSE-R2` after an external audit rejected
candidate `cefc4efa255d0456c94d217a9819c6dbf0325cff`.
Worker branch: `codex/eg-cp-stagef-close-r2`.
Exact base: `0f386723f56deae5eb39418e535f56e7a2b347dd` (tree
`ec0ab9c96f598ddc81a0e30424410461296abe71`, parent
`118284833eb312fc06e794dd0708f48b4909dbd1`).
Workflow-governance ref: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified
ancestor of the base).

This is an append-only coordinator amendment. Every original `FG-*` row, every
`R2-*` row, every inherited invariant row, the frozen replay registry of
section 3, and the entire sections 7-9 above remain byte-for-byte identical to
the exact base blob. This amendment freezes, **before any Lean or replay
edit**, the accepted predicate `P`, mutation predicate `Q`, quantifiers,
guards, exact consumer, and expected failing surface for every residual case
of the Stage-F falsification campaign. After this commit only the `Evidence
obtained` and `Status / residual gap` columns of section 10 tables may change;
any other change requires a recorded coordinator-approved contract amendment.

This amendment does not record `FEASIBILITY_PASS`, does not accept Stage F or
Stage A, does not authorize merge, push, publication, or public-claim
synchronization, and does not close the coordinator reconstruction or the
mandatory fresh-blind audit that must follow worker candidate completion.

**Coordinator repair amendments (audited, exactly two).** The rejected
candidate `cefc4ef` is retained as source evidence only. This
reconstruction carries exactly two authorized contract corrections relative
to that candidate's frozen section 10, both strengthenings and neither a
retroactive evidence edit: (`R1`) the `SF-FG11-DECISIVE` connection
contract in 10.3 now requires the producing invocation fields and the
reply-transition/continuation chain to survive in the theorem conclusion;
(`R2`) the 10.5 capstone conjunct list replaces the mislabeled
dynamic-input conjunction by an exact-type controller input boundary,
retaining the former facts under accurate names. Every other frozen
requirement, registry row, and harness contract is unchanged.

### 10.1 The residual obligations, original propositions copied verbatim

The controlling requirement text is the byte-identical original row above; it
is repeated here verbatim (requirement cell only) so this amendment is
self-contained. The five `FG` rows:

- `FG-11-LIVENESS-AND-ANTI-BYPASS`: supply a pinned valid execution where changing only the counted long-count cell changes a later probe address or returned result; bridge the existing consumed-payload-cell witness to the packed run's returned answer; and supply a proved-unread-cell mutation that is an expected accept. Aggregate trace inequality alone is insufficient when the requirement concerns the value.
- `FG-12-REPLAY-AND-CONSUMER`: commit one portable exact-registry replay with the ordered cases and expected verdicts below, named failing surfaces, one unchanged production accept, one unread-cell accept, restoration hashes, clean-tree checks, positive evidence-based subprocess deadlines, owned root-plus-descendant termination on Windows and Ubuntu, selector nonvacuity, and an independent expected-type consumer whose literal type pins the full capstone.
- `FG-13-TRUST-AND-SAME-OBJECT`: no reachable `sorry`, `admit`, axiom, unsafe/opaque/partial/extern implementation, native decision shortcut, Mathlib import, proof-value oracle, semantic callback, or mismatch of payload/store/run/width objects supports the capstone. Proof-only fields may certify but not choose answers, routes, or addresses.
- `FG-14-BOUNDARIES`: check empty representation, singleton, size two, each relevant threshold minus one/at/plus one, empty range, reversed range, and out-of-range endpoints. Preserve the half-open contract and leftmost tie policy. The top-level architecture is uniform; total empty tables and guards are allowed, but an undocumented second representation is not.
- `FG-15-DURABLE-DECISION`: commit the completed matrix, result report, design rationale, rejected K0/K2/padding/historical alternatives, exact theorem types and object-composition chain, skeptical-reviewer questions, verification ledger, and every remaining assumption. Do not call commissioning prompts or audit prose theorem evidence.

The seven frozen registry entries whose enactment this amendment freezes,
copied verbatim from section 3 (order, ID, mutation, expected verdict, named
failing surface unchanged; only the runner `Target` bodies are enacted):

| Order | ID | Mutation | Expected verdict | Named failing surface |
| --- | --- | --- | --- | --- |
| 2 | `A02-UNREAD-CELL-EXPECTED-ACCEPT` | mutate exactly one proved-unread allocated cell and preserve the pinned run/result | ACCEPT | none |
| 3 | `M01-WRONG-LONG-COUNT` | alter the header count | REJECT | liveness/consumer |
| 4 | `M02-HOST-LONG-COUNT-MIRROR` | bypass the header reply with preprocessing/host metadata | REJECT | structural consumer |
| 6 | `M04-CANONICAL-SHAPE-BY-N` | synthesize a canonical shape from `n` inside a wrapper | REJECT | structural / same-object |
| 8 | `M06-ANSWER-ORACLE` | call the reference/semantic answer from controller execution | REJECT | oracle independence |
| 15 | `M13-HIDDEN-UNCOUNTED-TABLE` | add a content-dependent lookup/program constant outside `memory xs` | REJECT | closed controller / program accounting |
| 16 | `M14-LONG-COUNT-IGNORED` | retain the header read but make downstream offsets independent of its value | REJECT | liveness |

The three replay harness contracts of section 3 remain controlling verbatim:
`REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`,
`REPLAY-SUBPROCESS-DEADLINE`.

The roadmap Stage-F rows consumed by this rung, copied verbatim from
`docs/internal/RMQ_ENDGAME_ROADMAP.md`:

- `EG-CP-F10-ANTI-BYPASS`: "Reject shape, source-list, proof-oracle,
  uncounted-table, disconnected-trace, forged-count, and sibling-store
  mutations" / minimum evidence "Committed replay with exact expected failures
  and unchanged accept control".
- `EG-CP-F11-BOUNDARIES`: "Empty representation, singleton, threshold, valid,
  reversed, empty-range, and out-of-range query behavior are explicit" /
  "Checked theorem/fixture matrix".
- `EG-CP-F12-RESIDUAL-ESTIMATE`: "Close the dependency inventory and estimate
  the exact remaining theorem surface" / "Coordinator-reviewed path/theorem
  inventory; no unknown dynamic input".
- `EG-CP-F13-NO-ASSUMED-CAPSTONE`: "Every reachable controller state, next
  address, reply, and final result is produced by the packed execution under
  one explicit invariant; final correctness is not stored in a field,
  hypothesis, or precomputed answer" / "Base/step/final invariant,
  decisive-cell corruption rejection, and a proved-unread-cell expected-accept
  control".

Inherited invariant rows retained by reference (requirement text is the
byte-identical section 2 row; this rung must close each at the full-node
objects): `INV-VALUE-DEPENDENCY`, `INV-SEMANTIC-NONVACUITY`,
`INV-STORE-AGREEMENT`, `INV-READ-BACKING`, `INV-PUBLIC-COMPOSITION`,
`INV-MUTATION-REPRODUCIBILITY`, `INV-CATEGORY-SEPARATION`.

`FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` applies as written in
`.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md` section 1,
against exact base `0f386723f56deae5eb39418e535f56e7a2b347dd`.

`COMPLETE-STAGEF-EVIDENCE` (commissioning goal, verbatim): "produce one
full-node falsification candidate with actual address/result liveness,
decisive and unread-cell controls, a semantically faithful portable
sixteen-case replay, complete query-level boundaries, and a durable final
evidence record."

### 10.2 Frozen canonical fixture

All fixture constants below are frozen; the exact witnesses live in
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean` and the
replay registry, and may not drift from this record.

- Input `xs0 = [7, 3, 3]`, query `left0 = 0`, `right0 = 3`,
  `shape0 = SuccinctClassic.cartesianShape xs0` (`n = 3`). This is
  simultaneously the `FG-14` duplicate-minimum fixture: the minimum value `3`
  occurs at indices `1` and `2`, and the guarded leftmost result is `some 1`,
  connected through the established `scanWindow` reference spec
  (`queryCosted_exact` / `queryCosted_leftmost`), never by citing the
  implementation output being tested (`INV-ORACLE-INDEPENDENCE`).
- Canonical objects: `mem0 = packedReviewerMemory shape0` (22 cells at the one
  derived width `packedReviewerCellWidth 3`; `longCount shape0 = 0`,
  `packedReviewerSparseCount shape0 = 0`), canonical run
  `run0 = packedReviewerRunAgainstMemory mem0 shape0.size 0 3` (68 attempted
  probes, terminal `some (some 1)`).
- Decisive consumed cell `c0 = 8`; frozen replacement `v0` = the bitwise
  complement of `mem0[8]`. Expected mutated terminal: `some (some 2)`, i.e.
  the returned answer moves from index `1` to index `2` under a one-cell
  payload corruption, while remaining a proper terminal value.
- Proved-unread allocated cell `u0 = 4` (an interior payload cell, not the
  final padding cell; the canonical run also leaves cells 12-17 and 21
  unprobed, and `4` is frozen as the witness). Frozen committed replacement
  `w0 = List.replicate (packedReviewerCellWidth 3) true`.
- Header mutation: cell `0` replaced by
  `SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size) (longCount shape + packedReviewerCellWidth shape.size)`;
  the universal theorem covers every shape and valid query, and its fixture
  instance is recorded with the concrete moved second address.

Evidence discipline for this section: canonical-side facts are derived from
the existing symbolic theorems (`packedReviewerRunAgainstMemory_public_outcome`,
grouping, `queryCosted_exact`); the mutated-run facts are kernel-checked
evaluations of the same literal objects. `#eval` output is exploration only
and closes nothing.

### 10.3 Frozen `FG-11` liveness targets

| ID | Accepted predicate `P` | Mutation predicate `Q` | Quantifiers and guards | Exact consumer | Expected surface |
| --- | --- | --- | --- | --- | --- |
| `SF-FG11-HEADER` | For every `shape` and endpoints with `left < right /\ right <= shape.size`, the run `packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left right` opens with the header request at cell `0` and its second attempted physical request is the first `.rankSuper` prelude probe; the same run returns the guarded reference result (`packedReviewerRunAgainstMemory_public_outcome`). | Replacing **only** cell `0` of `packedReviewerMemory shape` by `SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size) (longCount shape + packedReviewerCellWidth shape.size)` yields a run whose **second attempted physical address differs**: the conclusion is an inequality between `((packedReviewerRunAgainstMemory mutated shape.size left right).trace[1]?).map (fun event => event.request.address)` and the same projection of the canonical run, both `some`, unequal. The inequality is at the address projection of trace position 1, not at an enclosing record. | Universal over `shape : CartesianShape` and all valid endpoint pairs (strictly stronger than the frozen row's "one pinned valid execution"), plus one pinned instance at the section 10.2 fixture. Guard: `left < right /\ right <= shape.size`. Identical driver, controller, fuel; only memory cell `0` differs. | `RMQ/Validation/EGCPFinalFalsification.lean` independent expected-type consumer `egcpStageFHeaderAddressLiveness`; replay cases `M01-WRONG-LONG-COUNT` and `M14-LONG-COUNT-IGNORED` (10.4). | Theorem in `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean`. |
| `SF-FG11-DECISIVE` | The pinned fixture run returns `some (SuccinctClassic.queryTraceResult xs0 left0 right0).value`; the decisive cell `c0` occurs in its trace at a recorded global position with a successful reply, and the connection theorem's **conclusion** retains, on the identical canonical fixture objects: the global position and event; the exact producing whole-query request with `request.invocation.instruction = .leftSelect`, `request.invocation.argument = 0`, `request.invocation.argument2 = 0`, `request.site = .entryFirstOffset`, `request.segment = 8`, `request.index = 0`; physical address `8`; the successful reply cell; the exact controller pre-state as a checked driver prefix decomposition (`packedReviewerDriveStateAt` at that position); `packedReviewerNextRequest preState = some event.request`; `packedReviewerConsumeReply preState event.reply = postState`; and a checked continuation from `postState` to the same run's `.done (some 1)` state and terminal and the guarded leftmost reference result. A record literal hidden only in the proof term, an unrelated existential, `List.Mem`, or a bare successful-reply-plus-eventual-terminal conjunction does not close this row. | `(packedReviewerRunAgainstMemory ((packedReviewerMemory shape0).set c0 v0) shape0.size left0 right0).terminal` differs from the canonical run's `.terminal`: the conclusion is an inequality at the **returned-answer projection** of the two runs. `v0` is the frozen full-width replacement cell of 10.2. | One pinned canonical valid query (existential witness, as the frozen row demands). Identical `n`, `left0`, `right0`, driver, controller; only memory cell `c0` differs. | Consumers `egcpStageFDecisiveCellLiveness` and the literal expected-type restatement `egcpStageFDecisiveCellConnection`, which must fail if the producer is weakened back to the rejected origin-erasing proposition; the `M06` bridge of 10.4 consumes the same pair; the FG-13 capstone supplies the canonical side's reference connection. | Theorems in `ReviewerCapstone.lean`. |
| `SF-FG11-UNREAD` | The pinned fixture run's trace contains **no** event whose address is `u0`, and `u0 < packedReviewerCellCount shape0.size (longCount shape0) (packedReviewerSparseCount shape0)` (the cell is allocated). | For the frozen replacement cell `w0` of 10.2, `packedReviewerRunAgainstMemory ((packedReviewerMemory shape0).set u0 w0) shape0.size left0 right0 = packedReviewerRunAgainstMemory (packedReviewerMemory shape0) shape0.size left0 right0` -- complete run-record equality (terminal, failed, state, and trace), proved through the ordered agreement route (`packedReviewerRunAgainstMemory_eq_of_agree`), not by computing the mutated run separately. | Same pinned fixture and identical objects; only cell `u0` differs. Equality of complete run records. | Consumer `egcpStageFUnreadCellAccept` in the validation root; replay case `A02-UNREAD-CELL-EXPECTED-ACCEPT` (10.4). | Theorems in `ReviewerCapstone.lean`; this is the implementation and theorem basis for `A02`. |

### 10.4 Frozen registry enactments

The registry itself (sixteen IDs, order, mutation descriptions, verdicts,
named failing surfaces, 2 ACCEPT / 14 REJECT partition) is untouched. This
section freezes only the enacted `Target` bodies, activation needles, and
`ExpectFile` values, following `WDD-20260805-002`: every mutant is a
load-bearing definition-body mutation with mechanical activation needles, and
`ExpectFile` names the module whose guarding theorem genuinely fails first.

| Case | Enacted load-bearing mutation (frozen) | Activation needles | `ExpectFile` (honest first failing consumer) |
| --- | --- | --- | --- |
| `A02-UNREAD-CELL-EXPECTED-ACCEPT` | Patch `ReviewerCapstone.lean`'s frozen unread replacement-cell definition `egcpStageFUnreadReplacementCell`, changing the written replacement bit pattern (replacing `List.replicate (packedReviewerCellWidth 3) true` by `false :: List.replicate (packedReviewerCellWidth 3 - 1) true`). The pinned run/result theorems must still elaborate, because `SF-FG11-UNREAD` is proved through the agreement route and is therefore independent of the replaced value. Expected verdict ACCEPT: the full validation surface builds on the mutated tree. | the replacement literal written by the patch | none (build must pass) |
| `M01-WRONG-LONG-COUNT` | Retarget from the flat source-geometry equation to the actual run: in `ReviewerController.lean`, `packedReviewerConsumeReply`'s header arm binds `let longCount := SuccinctSpace.bitsToNatLE cell + 1`, so the executed controller consumes an altered header count. | `SuccinctSpace.bitsToNatLE cell + 1` | `PackedCellProbe/ReviewerControllerProof.lean` |
| `M02-HOST-LONG-COUNT-MIRROR` | In `ReviewerController.lean`, `packedReviewerRunAgainstMemory` binds `let hostLongCountMirror := SuccinctSpace.bitsToNatLE ((memory[0]?).getD [])` and starts the controller past the header phase from that host-preprocessed mirror, so the header reply is bypassed by preprocessing/host metadata and the charged header read disappears. | `let hostLongCountMirror := SuccinctSpace.bitsToNatLE ((memory[0]?).getD [])`; `hostLongCountMirror` | `PackedCellProbe/ReviewerController.lean` |
| `M04-CANONICAL-SHAPE-BY-N` | In `ReviewerController.lean`, `packedReviewerRunAgainstMemory` binds `let canonicalShapeFromN := packedSpine n` and drives `packedReviewerDriveAgainstMemoryAux` against `packedReviewerMemory canonicalShapeFromN` in place of the supplied memory: a canonical shape synthesized from `n` inside the wrapper. | `let canonicalShapeFromN := packedSpine n`; `packedReviewerDriveAgainstMemoryAux canonicalMemoryFromN` | `PackedCellProbe/ReviewerController.lean` |
| `M06-ANSWER-ORACLE` | The enacted body is unchanged from `R2R1` (the normalize-whole completion arm discards the computed value and returns the metadata-derived `semanticAnswerOracle := some n`). The `P3-2` carry-forward obligation is discharged by the frozen checked bridge below, not by upgrading the mutant's description. | unchanged (`let semanticAnswerOracle := some n`; `.done semanticAnswerOracle`) | `PackedCellProbe/ReviewerControllerProof.lean` |
| `M13-HIDDEN-UNCOUNTED-TABLE` | In `ReviewerController.lean`, `packedReviewerDriveAgainstMemoryAux`'s request branch binds `let hiddenUncountedTable := memory.take 1` -- a content-dependent lookup table outside the counted memory object -- and serves replies from `hiddenUncountedTable[request.address]?` when the address falls inside it. | `let hiddenUncountedTable := memory.take 1`; `hiddenUncountedTable[request.address]?` | `PackedCellProbe/ReviewerController.lean` |
| `M14-LONG-COUNT-IGNORED` | Retarget from the flat source-geometry equation to the actual run: in `ReviewerController.lean`, `packedReviewerConsumeReply`'s header arm binds `let longCount := 0`, retaining the charged header read (the driver still probes cell `0` and records the event) while every downstream offset becomes independent of the decoded value. | `let longCount := 0` | `PackedCellProbe/ReviewerControllerProof.lean` |

**Frozen `M06` bridge (`SF-M06-BRIDGE`).** Accepted predicate `P`: the
canonical fixture pair of `SF-FG11-DECISIVE` -- the identical run object
returns the guarded reference value, and mutating only consumed cell `c0`
changes the returned answer -- together with ordered request/reply
determinism (`packedReviewerRunAgainstMemory_eq_of_agree`). Enacted mutation
predicate `Q`: the run's terminal value is produced by a completion function
of the public metadata alone -- any `f : Nat -> Nat -> Nat -> Option Nat`
applied to `(n, left, right)`, independent of the consumed replies. The
frozen bridge is one checked theorem, `packedReviewerNoMetadataCompletion` in
`ReviewerCapstone.lean`, concluding: for **every** such `f`, it is not the
case that both fixture runs (canonical and `c0`-mutated) have
`.terminal = some (f shape0.size left0 right0)`. Its guards and quantifiers
are identical to `SF-FG11-DECISIVE` (same two pinned run objects, same
endpoints). Coverage: the enacted `M06` body is the instance
`f = fun n _ _ => some n`; the frozen answer-oracle direction -- a
reference/semantic-answer call, which on the packed machine is necessarily a
memory-independent function of the pinned query -- is the instance
`f = fun _ left right => (SuccinctClassic.queryTraceResult xs0 left right).value`.
Both are refuted by the same theorem at the same objects, which is the
checked bridge from the accepted oracle-independence predicate to the enacted
mutation predicate demanded by the `P3-2` carry-forward obligation. A literal
in-controller call to the reference semantics is untypeable without a shape
or list parameter (the state and driver carry neither), so enactment of the
literal oracle is impossible without the already-rejected `M03` signature
mutation; the bridge is therefore the only faithful route, and no document
may cite `M06` alone as having refuted a reference-semantics oracle.

**Runner mode addition (frozen).** The runner gains one additive switch,
`-SelfTestOnly`: it validates selectors, runs `Test-RegistryIntegrity`, runs
`Invoke-DescendantSelfTest`, and exits, building nothing. It changes no
registry entry, selector semantics, deadline contract, restoration contract,
or full-mode semantics; `-SelfTestOnly` combined with `-Case`, `-Stage`, or
`-SkipSelfTest` fails before any action. Purpose: executing the owned
root-plus-descendant termination contract on the Ubuntu gate OS (local
isolated WSL `Ubuntu-24.04`, `pwsh 7.6.4`) without requiring a Linux Lean
toolchain, closing the `REPLAY-SUBPROCESS-DEADLINE` residual recorded in
section 3 ("The Ubuntu branch of `Stop-ProcessTree` is written but has not
been run on that gate").

### 10.5 Frozen `FG-13` capstone shape and consumer

One focused capstone in the new module
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean`:
`structure PackedReviewerStageFCapstone (xs : List Int) (left right : Nat) :
Prop`, every field stated over the identical let-bound objects
`shape := SuccinctClassic.cartesianShape xs`,
`memory := packedReviewerMemory shape`,
`run := packedReviewerRunAgainstMemory memory shape.size left right`, with
exactly these fourteen frozen conjuncts:

1. `payload_is_buildPayload`: `packedReviewerPayloadBits shape = SuccinctClassic.buildPayload xs`.
2. `serialized_header_payload`: `packedReviewerSerializedBits shape = packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape` (definitional split pinned as a proposition).
3. `padded_final_padding`: `packedReviewerPaddedBits shape` is the serialized bits followed by exactly the final-cell `false` padding, with `(packedReviewerPaddedBits shape).length` the allocated bit count.
4. `one_cell_width`: every cell of `memory` has length exactly `packedReviewerCellWidth shape.size`.
5. `allocation_two_n_plus_rho`: `memory.length * packedReviewerCellWidth shape.size <= 2 * shape.size + packedReviewerRho shape.size`.
6. `rho_little_o`: `SuccinctSpace.LittleOLinear packedReviewerRho`.
7. `probes_backed_by_memory`: every trace event's reply is literally `memory[event.request.address]?` (memory-only execution of the literal run object).
8. `probes_allocated_and_successful`: every attempted probe address is `< packedReviewerCellCount shape.size (longCount shape) (packedReviewerSparseCount shape)` and receives `some` cell.
9. `ordered_grouping`: `PackedReviewerRunGrouping shape left right` (order- and multiplicity-sensitive trace identity).
10. `derived_cap_427`: `run.trace.length <= 427`.
11. `guarded_reference_result`: `run.terminal = some (SuccinctClassic.queryTraceResult xs left right).value`, `run.failed = false`, `run.state = .done (...)` -- the guarded half-open leftmost reference result on the same run object.
12. `controller_input_boundary`: the exact-type controller pin `@packedReviewerController = fun (n left right : Nat) => packedReviewerController n left right` -- an equation that elaborates only at the exact public entry type `Nat -> Nat -> Nat -> PackedReviewerControllerState`, so an added shape, list, oracle, or advice parameter (optional or not) makes this capstone field ill-typed -- together with the literal run factorization `packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left right = packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape) (packedReviewerControllerMeasure (packedReviewerController shape.size left right)) (packedReviewerController shape.size left right)`, which exhibits that the controller receives only `(n, left, right)` while memory is supplied only to the physical driver interface.
13. `closed_length_and_memory_arity` (the former length/arity facts under an accurate name; they are NOT an input boundary): the exact payload length equals the closed three-scalar function (`packedReviewerClosedPayloadLength_eq` instance) and `memory.length` equals `packedReviewerCellCount` at `(shape.size, longCount shape, packedReviewerSparseCount shape)`.
14. `store_agreement_determinism` (the former agreement fact under an accurate name): ordered request/reply agreement determines the run (`packedReviewerRunAgainstMemory_eq_of_agree` shape).

Producer: `packedReviewerStageFCapstone_holds : forall xs left right,
PackedReviewerStageFCapstone xs left right`. Consumer: an **independently
written** restatement in `RMQ/Validation/EGCPFinalFalsification.lean`
(`EGCPStageFCapstoneFacts` structure plus `egcpStageFCapstoneFactsExact`)
that writes out every conjunct at the literal objects and discharges it by
projection, so deleting or weakening any capstone conjunct breaks the
validation root. `RMQ.lean` imports the new module.

### 10.6 Frozen `FG-14` boundary campaign

Kernel-checked instances, each obtained from the one universal
`packedReviewerStageFCapstone_holds` (no per-size variant, no readiness or
compatibility dispatch), at exactly:

- empty representation `[]`; singleton `[0]`; both size-two Cartesian shapes
  via `[0, 1]` and `[1, 0]` (connected to the distinct `packedSizeTwoLeft` /
  `packedSizeTwoRight` shapes);
- long crossover sizes `5487`, `5488`, `5489` via `List.replicate`;
- interior-readiness boundaries and neighbours `1023`, `1024`, `1025` and
  `1329`, `1330`, `1331` via `List.replicate` (the `1025` and `1329` interior
  facts are added to `Boundaries.lean` beside the existing four);
- query cases on a pinned shape: one valid half-open query, empty range
  (`left = right`), reversed endpoints (`left > right`), right endpoint out of
  range (`right > n`), left endpoint out of range; invalid cases must return
  the exact `.done none` run with an empty trace;
- the duplicate-minimum fixture `xs0 = [7, 3, 3]` with query `(0, 3)`: minima at indices `1` and `2`, leftmost result `some 1` proving the leftmost tie
  result through the run's terminal value.

No-second-representation obligation: a checked statement that the controller
entry and the memory builder are single uniform definitions -- the capstone
instances at every boundary size instantiate one quantifier, the located
threshold geometry (`Boundaries.lean`) shows the moving clause moves while
the capstone statement is unchanged, and the `M04`/`M11` rejections plus the
uniform-entry pins show no dispatch selects a second representation.

### 10.7 Frozen `FG-15` durable record

Append to `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md`, behind
delimited markers, the Stage-F final falsification record: row-by-row
evidence for every section 10 row; the full-registry replay outcome per ID
and OS; K1 survived / K2 unused; rejected K0 / K2 / internal-padding /
historical alternatives; exact theorem types and the object-composition
chain; live assumptions; the strongest skeptical question; the verification
command ledger with observed durations; all OS receipts (Windows and
Ubuntu); and every still-open downstream node (`FEASIBILITY_PASS`, Stage A,
public synchronization, `S1`, `V1`). A four-part digestion (conceptual
change, plain-English meaning, live assumptions, strongest skeptical
question) is mandatory. No row may cite commissioning prompts, worker prose,
or audit prose as theorem evidence.

### 10.8 Verification command ledger for this amendment

| ID | Command | Role | Rows covered | Outcome |
| --- | --- | --- | --- | --- |
| `SF-CHK-00` | `scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a... -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt, rmq-coordinator, rmq-proof-sprint" -CheckoutRef 0f38672...` | F | governance | PASS before edits (recorded 2026-08-06). |
| `SF-CHK-01` | focused `lake build` of each changed PackedCellProbe module and `RMQ.Validation.EGCPFinalFalsification` | D then F | all Lean rows | Pending |
| `SF-CHK-02` | `lake build RMQ` | F | whole-library integration | Pending |
| `SF-CHK-03` | `lake env lean scripts/axiom_check.lean` | F | `FG-13`, axiom inventory | Pending |
| `SF-CHK-04` | replay bounded startup, exact selector `A01-PRODUCTION-EXPECTED-ACCEPT`, exact selector `M01-WRONG-LONG-COUNT`, then full mode exactly once on the committed frozen candidate | F | `FG-12`, `INV-MUTATION-REPRODUCIBILITY` | Pending |
| `SF-CHK-05` | `-SelfTestOnly` descendant-termination run on WSL `Ubuntu-24.04` under `pwsh` | F | `REPLAY-SUBPROCESS-DEADLINE` (Ubuntu leg) | Pending |
| `SF-CHK-06` | strict UTF-8 section-scoped frozen-row comparison against `0f38672...` | F (before expensive final verification and at final) | `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | Pending |
| `SF-CHK-07` | `powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | F | `FG-15` prose | Pending |
| `SF-CHK-08` | `powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 0f386723f56deae5eb39418e535f56e7a2b347dd` | F | design policy | Pending |
| `SF-CHK-09` | `AGENTS.md` hygiene scan and native-shortcut scan over `RMQ` and `lakefile.toml` | F | `FG-13` | Pending |
| `SF-CHK-10` | UTF-8 inspection of changed docs; exact changed-path allowlist check; `git diff --check` working tree and `git diff --check 0f38672...HEAD` after committing; final `git status --porcelain` cleanliness | F | hygiene, handoff | Pending |
| `SF-CHK-11` | aggregate `scripts/gate.ps1` | C | only if a final changed surface is not owned above | Pending |

CI note carried from `WDD-20260726-007`: each commit on this branch must
validate `design_decision_check.ps1` at `-Base HEAD~1`.

### 10.9 Node boundary and deferrals

| Item | Disposition |
| --- | --- |
| Coordinator `FEASIBILITY_PASS` decision | Deferred to the coordinator; requires reconstruction of the exact final candidate commit plus mandatory fresh-blind audit. Not recordable by this worker. |
| Stage A `A01`..`A13` campaign and matrix freeze | Deferred; may follow only `FEASIBILITY_PASS`. Existing facts resembling `A01`..`A12` do not start Stage A early. |
| Public-claim synchronization, headline promotion, manuscript/artifact work | Deferred; out of write scope. |
| `S1` bit-addressed querying, `V1`, Word-RAM instruction-time claim, preprocessing-time claim | Deferred; not claimed. |
| `FG-11` / full `FG-12` / `FG-14` / `FG-15` | **Not deferrable in this task.** |

<!-- COORDINATOR-AMENDMENT-EG-CP-STAGEF-CLOSE-R2-END -->

# EG-CP Stage A packed-architecture acceptance - frozen matrix

Worker handle: `EG-CP-STAGEA-CLOSE-R1`.
Worker branch: `codex/eg-cp-stagea-close-r1`.
Exact base: `270d78559adc33fe872b6d17bd54d8e51567a605` (tree
`7b872cf144503cebf61097f857fa779081076107`), the coordinator-accepted and
locally merged Stage-F `FEASIBILITY_PASS` tree.
Workflow-governance ref: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified
ancestor of the base; skill preflight PASS recorded in the evidence ledger).
Template: `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.

**This matrix is frozen by this commit, before any Lean or replay edit.**
Requirement rows, inherited-invariant rows, harness-contract rows, the frozen
combined-proposition shape of section 1.1, the frozen fixture of section 1.2,
and the ordered replay registry of section 4 are byte-frozen in their
entirety: no table row or frozen-section line above section 8 may be edited
after this commit. All evidence, outcomes, statuses, and command receipts are
recorded exclusively in the append-only evidence ledger (section 8), keyed by
row ID. This is a deliberate strengthening of the template's mutable-cell
allowance so that `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` can compare complete
row bytes with no column exception. Any other change requires a recorded
coordinator-approved contract amendment in section 7.

**This document accepts nothing.** It records what would have to be true. The
worker may report at most `CANDIDATE_COMPLETE`; `EG-CP-A13-CAPSTONE-AUDIT`,
coordinator reconstruction, architecture acceptance, integration, push,
public-claim synchronization, `S1`, and `V1` are not claimed here and cannot
be closed by this worker.

Roadmap join: `docs/internal/RMQ_ENDGAME_ROADMAP.md`, Stage A packed
architecture acceptance, authorized by the `FEASIBILITY_PASS` recorded
2026-08-06 at repaired proof tree `174989f26a681a3a04a74e0f3d8f2d414f915075`.
This task closes the Stage-A worker rung `A01`-`A12` only; the downstream
consumer is the independent `A13` fresh-blind audit and coordinator
reconstruction.

Frozen identities used throughout ("the objects"): for `xs : List Int` and
endpoints `left right : Nat`, write `shape := SuccinctClassic.cartesianShape
xs`, `n := shape.size`, `w := packedReviewerCellWidth n`, `memory :=
packedReviewerMemory shape`, `run := packedReviewerRunAgainstMemory memory n
left right`, `controller := packedReviewerController n left right`, and
`reference := SuccinctClassic.queryTraceResult xs left right`. The validity
guard is everywhere `left < right /\ right <= n`. All names are the accepted
reviewer-universe objects; the flat `packed*` universe (`packedMemory`,
`packedCellWidth`, `packedRho`, ...) is a different object family and is
forbidden in every Stage-A evidence cell (`DD-20260804-027`,
`packedStoresNotEqual`).

---

## 1. Frozen requirement rows `EG-CP-A01` .. `EG-CP-A13`

Requirement text is copied verbatim from the Stage-A table of
`docs/internal/RMQ_ENDGAME_ROADMAP.md` at the exact base. Anti-vacuity cells
record the challenge to attempt with its accepted predicate `P`, challenged
predicate `Q`, and bridge obligation; attempted outcomes are appended in
section 8.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge to attempt (P / Q / bridge) | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `EG-CP-A01-ONE-OBJECT` | Space, query, trace, and result use the identical `header ++ buildPayload ++ padding` packed memory object | Local rung | Capstone fields 1-5 of section 1.1 over the objects: `packedReviewerPayloadBits shape = SuccinctClassic.buildPayload xs`; `packedReviewerSerializedBits shape = packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape`; `packedReviewerPaddedBits shape` is serialized bits plus exactly the final `false` padding with length `packedReviewerAllocatedBits`; `memory` is the literal uniform chunking of those padded bits; `run` is the literal drive of `controller` against that `memory`. The composition chain is quoted in full in section 1.3. | `PackedReviewerArchitectureCapstone` fields 1-5, produced by `packedReviewerArchitectureCapstone_holds`, restated literally by `EGCPStageAArchitectureFacts`/`egcpStageAArchitectureFactsExact` in `RMQ/Validation/EGCPStageA.lean`; space (field 8), probes (fields 20-23), and result (field 28) all name the same `memory`/`run` terms. | P: every capstone field names the identical `memory`/`run` terms. Q: a sibling, supplied, prefix-only, or separately reconstructed store inhabits some field. Bridge: P = Q domain (same literal terms). Replay `SA-M01-SIBLING-STORE`, `SA-M02-SIBLING-PAYLOAD`, `SA-M03-CANONICAL-SHAPE-BY-N` must REJECT. | Append-only ledger `EV-A01` | Open at freeze; final status in ledger |
| `EG-CP-A02-SPACE` | Complete allocated capacity is `2n + o(n)` | Local rung | Capstone fields 6-10: every cell of `memory` has length exactly `w`; `memory.length = packedReviewerCellCount n (longCount shape) (packedReviewerSparseCount shape)` (header cell, every payload cell, final padding cell all counted); `memory.length * w <= 2 * n + packedReviewerRho n`; `SuccinctSpace.LittleOLinear packedReviewerRho`; the closed-length identity. Footprint-address bounds against `2 ^ w` are fields 22 and the dead-address bound cited under A03/A05. Payload-only length or a proof-only field is insufficient. | Capstone fields 6-10 -> `egcpStageAArchitectureFactsExact`; allocation term is `(packedReviewerMemory shape).length * packedReviewerCellWidth shape.size`, the same `memory` probed by `run`. | P: the bound is on allocated cells times width of the probed memory. Q: the bound is on `serializedBits.length`, a payload-only length, or a sibling memory. Bridge: padding makes the two differ; `SA-M04-ALLOCATION-HEADER-CELL-DROP` and `SA-M02-SIBLING-PAYLOAD` must REJECT. | Append-only ledger `EV-A02` | Open at freeze; final status in ledger |
| `EG-CP-A03-WIDTH` | One exact query-independent width function satisfies the frozen explicit all-size lower/upper bounds for cells, fields, and addresses | Local rung | Capstone fields 11-15 with the one function `packedReviewerCellWidth : Nat -> Nat` (size-only by signature): `0 < w`; `n < 2 ^ w`; `w <= 20 * (Nat.log2 (n + 2) + 1)`; header exactly one `w`-bit cell; `longCount shape < 2 ^ w /\ packedReviewerSparseCount shape < 2 ^ w`. Cells: field 6. Addresses: field 22 and the interior dead-address bound `(packedInteriorOffsets n).deadAddress < 2 ^ w` (certificate field, re-pinned by the consumer). Allocation: field 8. Small sizes pinned: kernel-checked width literals at `n = 0, 1, 2, 3` in `RMQ/Validation/EGCPStageA.lean` (the `n = 3` literal is the existing `15`). | Fields 11-15 -> `egcpStageAArchitectureFactsExact`; width signature pin `Nat -> Nat` in the validation root. | P: one exact size-only `packedReviewerCellWidth` is used by header, cells, addresses, and allocation. Q: a query-, content-, or segment-dependent width substitution, or a different size-only value. Bridge: the signature pin rejects added parameters (structural, with `SA-M14-SHAPE-PARAMETER` as the signature-family control); `SA-M05-WIDTH-SUBSTITUTION` must REJECT the value substitution (semantic). | Append-only ledger `EV-A03` | Open at freeze; final status in ledger |
| `EG-CP-A04-HEADER-SUFFICIENCY` | All controller geometry is decoded from counted header/probe data | Local rung | Capstone fields 16-19: `memory[0]? = some (packedReviewerHeaderBits shape)`; `SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) = longCount shape`; under the guard the run's first attempted address is `0` (the header probe); under the guard the universal header-liveness proposition: the canonical second attempted address is the `.rankSuper` cell at `longCount shape`, the header-mutated second attempted address is the `.rankSuper` cell at `longCount shape + w`, and they differ. The accepted `[7, 3, 3]`, `(0, 3)`, `10 -> 37` fixture instance is field F3 of section 1.2, re-pinned by the consumer. The sparse count is recovered by the charged three-read prelude (K1 chain, `DD-20260805-071`). A header equality or decorative header read is insufficient. | Fields 16-19 -> `egcpStageAArchitectureFactsExact`; fixture re-pin `egcpStageAHeaderLivenessFixture` (10 -> 37) in the validation root; producing chain `packedReviewerMemory_header_cell` -> `packedReviewerConsumeReply_header` -> `packedReviewerHeaderCellAddressLiveness_exact`. | P: the decoded header value determines a later attempted address, universally, at the address projection of trace position 1. Q: the header is read but ignored, mirrored from host metadata, or decoded wrongly. Bridge: same run objects; `SA-M06-WRONG-LONG-COUNT`, `SA-M07-HOST-LONG-COUNT-MIRROR`, `SA-M08-LONG-COUNT-IGNORED` must REJECT. | Append-only ledger `EV-A04` | Open at freeze; final status in ledger |
| `EG-CP-A05-PROBE-SEMANTICS` | Every attempted probe is one aligned fixed-width indexed read of the same memory; cell crossings cost multiple probes | Local rung | Capstone fields 20-25: every trace event's reply is literally `memory[event.request.address]?`; every attempted address is `< packedReviewerCellCount ...` and receives `some` cell (in-range totality; the invalid branch has an empty trace, so this covers every valid query's attempted probes); every address `< 2 ^ w`; every reply cell has length exactly `w`; `PackedReviewerRunGrouping shape left right` (order- and multiplicity-sensitive trace identity); and the probe-plan pin `packedReviewerProbePlan n bit width = if width = 0 then [] else if bit % w + width <= w then [bit / w] else [bit / w, bit / w + 1]` (an unaligned logical word crossing a cell boundary contributes exactly two ordered probes). Provenance level: event values, occurrence positions, and multiplicity by the grouping; instruction/folded pre-state and computed invocation parameters by field 35 and the decisive-connection re-pin under A10. | Fields 20-25 -> `egcpStageAArchitectureFactsExact`; grouping producer `packedReviewerRunAgainstMemory_public_outcome`/`_certificate`; crossing producers `packedReviewerProbePlan_of_offset`/`_of_crossing`. | P: attempted probes are aligned `w`-bit indexed reads with the exact conditional crossing expansion. Q: a crossing is served in the wrong cell order, counted as one probe, or the trace is forged while the result survives. Bridge: same plan/run objects; `SA-M09-CROSSING-SWAP` and `SA-M10-DISCONNECTED-TRACE` must REJECT. | Append-only ledger `EV-A05` | Open at freeze; final status in ledger |
| `EG-CP-A06-PROBE-CAP` | Exact derived numeral `C`, preserving order and multiplicity | Local rung | Capstone fields 26-27: `run.trace.length <= 427`, plus the checked structural derivation under the guard: `packedReviewerControllerMeasure controller = 1 + 2 * packedReviewerSparsePreludeRemaining (packedReviewerSparsePreludeInit n 0) + 2 * packedReviewerWholeRemaining (packedReviewerWholeStart n left right)`, with `packedReviewerSparsePreludeRemaining (packedReviewerSparsePreludeInit n 0) = 3`, `packedReviewerWholeRemaining (packedReviewerWholeStart n left right) = 210`, and `packedReviewerControllerMeasure controller = 427` -- the exact numeral `427 = 1 + 2*3 + 2*210` derived from the physical run's own fuel measure, not stored in an input, hypothesis, or precomputed result. Order and multiplicity are retained by field 24. Honest category note: `427` is an upper bound on attempted physical probes (the fixture run issues 68); `210` is logical fuel bounding attempts (`DD-20260805-075`); no attainment claim is made (`B7-UPPER-BOUND-IS-NOT-ATTAINMENT`). | Fields 26-27 -> `egcpStageAArchitectureFactsExact`; producers `packedReviewerRunAgainstMemory_trace_length_le_427`, `packedReviewerControllerMeasure_valid_eq_427`, and the structural `rfl` decomposition. | P: the cap is the derived measure of the executed run. Q: the cap is a stored numeral in the measure arm. Bridge: the structural-derivation conjunct elaborates only against the derived form; `SA-M11-FORGED-PROBE-CAP` must REJECT at its commissioned structural surface. | Append-only ledger `EV-A06` | Open at freeze; final status in ledger |
| `EG-CP-A07-CORRECTNESS` | All valid half-open queries return the leftmost reference RMQ answer | Local rung | Capstone fields 28-29, universally quantified over every `xs`, `left`, `right` by the producer: `run.terminal = some reference.value /\ run.failed = false /\ run.state = .done reference.value` through the canonical packed controller/run/lowering/simulation/reference chain (`packedReviewerRunAgainstMemory_eq_lowered` -> `packedReviewerDriveLoweredWhole_eq_logical` -> `packedReviewerDriveLogical_210_simulates_packedWholeQueryRun` -> `packedWholeQueryRun_eq` -> `packedReviewerPackedReference_eq_public`); plus the leftmost-tie connection: under the guard, `forall index, run.terminal = some (some index) -> LeftmostArgMin xs left right index` (via `SuccinctClassic.queryCosted_exact`/`queryCosted_leftmost` and `scanWindow`). The Stage-F `F09` slice is a witness only; a finite fixture set, aggregate-trace inequality, or post-hoc answer comparison is insufficient. | Fields 28-29 -> `egcpStageAArchitectureFactsExact`; the duplicate-minimum fixture (`some 1` at `[7, 3, 3]` `(0, 3)`) is a boundary instance, not the closure. | P: the identical run object returns the guarded leftmost reference result for every valid query. Q: the returned index is offset, or produced by an oracle before the reads. Bridge: same run/result projection; `SA-M12-RESULT-OFFSET` and `SA-M16-ANSWER-ORACLE` must REJECT. | Append-only ledger `EV-A07` | Open at freeze; final status in ledger |
| `EG-CP-A08-INVALID-DOMAIN` | Invalid/reversed/empty/out-of-range behavior is stated without weakening A07 | Local rung | Capstone fields 30-31: `not (left < right /\ right <= n) -> run.terminal = some none /\ run.failed = false /\ run.state = .done none /\ run.trace = []`, and `not (left < right /\ right <= n) -> reference.value = none` (the reference agrees, so A07's unconditional field 28 is not weakened and every combined field uses the same guard). Boundary instances consumed in the validation root: empty representation `[] 0 0`; singleton `[0] 0 1`; both size-two shapes `[0,1] 0 2`, `[1,0] 0 2`; long-crossover triple `5487/5488/5489`; interior-readiness six `1023/1024/1025/1329/1330/1331`; on `[7, 3, 3]`: empty range `(1,1)`, reversed `(2,1)`, right out of range `(0,4)`, left out of range `(5,7)`; duplicate-minimum `(0,3)`. | Fields 30-31 -> `egcpStageAArchitectureFactsExact`; instance consumers in `RMQ/Validation/EGCPStageA.lean` instantiate the one universal producer (no per-size variant, readiness, or compatibility dispatch). | P: invalid endpoints yield the exact `.done none` run with empty trace under the same guard as every other field. Q: the invalid arm returns a fabricated answer, or a second representation is dispatched at a threshold. Bridge: same guard/objects; `SA-M13-INVALID-GUARD-RESULT` must REJECT; threshold instances instantiate the single quantifier. | Append-only ledger `EV-A08` | Open at freeze; final status in ledger |
| `EG-CP-A09-UNIFORMITY` | Closed controller has no semantic shape, input list, proof oracle, uncounted advice, or hidden table | Local rung | Capstone fields 32-34: the exact-type input boundary `@packedReviewerController = (fun (n left right : Nat) => packedReviewerController n left right)` (elaborates only at `Nat -> Nat -> Nat -> PackedReviewerControllerState`; an added shape, list, oracle, or advice parameter makes it ill-typed); the uniform entry `rfl` pin; the run factorization (field 5) exhibiting that memory is supplied only to the physical driver; and ordered store-agreement determinism `forall memoryB, (agreement on the run's trace) -> run = packedReviewerRunAgainstMemory memoryB n left right` (cross-shape/store-agreement evidence: equal allowed inputs and probe replies determine the transcript and result). The controller state family is proof-free (accepted `R2-05`). | Fields 32-34 -> `egcpStageAArchitectureFactsExact`; signature pins in the validation root. | P: the controller's dynamic inputs are exactly `n`, endpoints, and prior replies of `memory`. Q: reintroduction of any forbidden input family (shape parameter, canonical shape from `n`, hidden table, host mirror). Bridge: exact-signature pin (structural; `SA-M14-SHAPE-PARAMETER`, labeled) paired with the semantic rejections `SA-M03-CANONICAL-SHAPE-BY-N`, `SA-M07-HOST-LONG-COUNT-MIRROR`, and the value-preserving but structurally honest `SA-M15-HIDDEN-UNCOUNTED-TABLE`. | Append-only ledger `EV-A09` | Open at freeze; final status in ledger |
| `EG-CP-A10-NO-ASSUMED-CAPSTONE` | Reachable-state invariant and corruption/nonvacuity theorems show that packed execution, not an assumed answer or shape-generated replay, produces the result | Local rung | Capstone fields 35-38: the explicit reachable-state base/step/final invariant instantiated at the literal run -- for every trace position `i < run.trace.length`, the driver prefix fold `packedReviewerDriveStateAt memory controller i` is live, computes the emitted request, the recorded event is that request with the driver's own memory lookup, and the drive restarted at the fold reproduces the run's terminal, state, and trace suffix (base `i = 0`, step `i -> i+1`, final continuation); decisive-cell corruption rejection at the frozen fixture (mutating consumed cell `8` moves the returned answer `some 1 -> some 2`, an inequality at the `.terminal` projection); the proved-unread-cell expected-ACCEPT control (cell `4` is allocated, never probed, and every replacement leaves the complete run record unchanged through the ordered agreement route); and the metadata-completion bridge (`forall f : Nat -> Nat -> Nat -> Option Nat`, no completion of the public metadata alone produces both fixture terminals -- the checked `SF-M06-BRIDGE`). Occurrence-level provenance (position 11, `leftSelect`, `entryFirstOffset`, segment 8, pre/post state, continuation) is re-pinned from `packedReviewerDecisiveCellConnection`. A theorem that stores the desired answer, replays a shape-generated trace, or assumes the final correctness relation does not close this row. | Fields 35-38 -> `egcpStageAArchitectureFactsExact`; connection re-pin `egcpStageADecisiveCellConnection` in the validation root; producers `packedReviewerDriveAux_decompose`, `packedReviewerDecisiveCellLiveness`, `packedReviewerUnreadCellAccept`, `packedReviewerNoMetadataCompletion`. | P: each next address, reply, state, and result is produced by the packed execution under one explicit invariant. Q: the result is stored, precomputed from metadata, or the trace is replayed disconnected from the result. Bridge: same fixture objects and quantifiers as `SF-FG11-DECISIVE`; `SA-M16-ANSWER-ORACLE`, `SA-M17-DECISIVE-MUTANT-NEUTRALIZED`, `SA-M10-DISCONNECTED-TRACE` must REJECT; `SA-A02-UNREAD-CELL-EXPECTED-ACCEPT` must ACCEPT. | Append-only ledger `EV-A10` | Open at freeze; final status in ledger |
| `EG-CP-A11-PUBLIC-CONSUMER` | Independent expected-type consumer pins the full combined proposition | Local rung | `RMQ/Validation/EGCPStageA.lean` contains: the signature pin `egcpStageACapstoneSignature : List Int -> Nat -> Nat -> Prop := @PackedReviewerArchitectureCapstone`; the independently written structure `EGCPStageAArchitectureFacts xs left right : Prop` restating every one of the 38 frozen fields at its literal expected type (object, guards, width, space, header, physical semantics, exact `427`, correctness, invalid behavior, uniformity, no-assumed-capstone); and `egcpStageAArchitectureFactsExact : forall xs left right, EGCPStageAArchitectureFacts xs left right` discharged by projection from `packedReviewerArchitectureCapstone_holds`. The consumer is written out literally and does not print or query the capstone theorem's current type. A mutation that weakens, deletes, swaps, or reguards a public conjunct must break this committed consumer at the named surface. | `RMQ.lean` imports the new modules; the consumer is the downstream anchor for the `A13` audit. | P: the committed consumer pins the entire combined proposition independently. Q: a public conjunct is weakened/deleted while the consumer still elaborates. Bridge: `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` (upstream certificate) and `SA-M19-ARCHITECTURE-PROPOSITION-WEAKENING` (the capstone producer itself, M12-style) must REJECT, the latter at `RMQ/Validation/EGCPStageA.lean`. | Append-only ledger `EV-A11` | Open at freeze; final status in ledger |
| `EG-CP-A12-REPLAY` | Exact registry, selectors, mutations, deadlines, restoration, and clean-state controls | Local rung | `scripts/eg_cp_stagea_replay.ps1` committed, encoding the section-4 registry literally (21 ordered cases, 2 ACCEPT / 19 REJECT), with: registry integrity validation before any build (count, ascending order, unique IDs, mapped verdicts, exact verdict totals, nonempty row/field mappings); selector nonvacuity (`-Case` executes exactly one ID; unknown, explicitly empty, and whitespace selectors fail at the script boundary; only omission means full mode; `-IntegrityProbe OmitMiddle|DuplicateMiddle` exercises the omitted/duplicate middle-ID rejections at the script boundary); evidence-based subprocess deadlines (measured clean build plus a representative mutated-chain probe, times four, floor 300 s); owned root-plus-descendant termination with the sleeper self-test on Windows (the required gate platform; the non-Windows branch is present but not certified -- stated as a limitation, not cross-platform evidence); mechanical activation needles on every semantic mutant (`WDD-20260805-002`); SHA256-verified byte restoration in `finally`; and a terminal clean-tree check. Inherited Stage-F mutation bodies are reused only where their exact P/Q, decoder, objects, guards, and quantifiers match the reviewer-universe Stage-A rows (they do: every reused body targets the reviewer controller/memory/run); each is re-executed by this campaign against the Stage-A surface `RMQ.Validation.EGCPStageA` (`NAMED-REGRESSION-REALITY`), and structural or value-preserving cases are labeled honestly in section 4 with semantic pairs where the row requires semantic rejection. | Runner -> frozen registry -> `RMQ.Validation.EGCPStageA` surface builds; `scripts/eg_cp_final_falsification_replay.ps1` is not edited and must remain byte-identical to the base (conditional check `SA-CHK-12`). | P: the committed runner replays every claimed case with expected verdict, named failing surface, restoration, and clean state. Q: a case is skipped, mis-surfaced, or passes vacuously. Bridge: registry integrity plus activation needles plus expected-surface matching; the selector and integrity probes must fail closed. | Append-only ledger `EV-A12` | Open at freeze; final status in ledger |
| `EG-CP-A13-CAPSTONE-AUDIT` | Fresh-blind exact-commit audit and coordinator reconstruction pass | Roadmap node (AUDITOR_OWNED) | This worker produces only the verdict-free evidence packet `docs/internal/audit_packets/EG_CP_STAGEA_AUD1_PACKET.md` naming the final candidate SHA/tree/parent, theorem/type inventory, matrix and replay registry, object/composition chain, check receipts, and open audit questions. No auditor prompt is written, no fresh-blind verdict is simulated, and the result report is not included before the auditor reconstructs the proof surface. | The coordinator's next launch; not this worker. | Not applicable to this worker: the row's anti-vacuity is the fresh-blind audit itself. | Append-only ledger `EV-A13` (packet identity only) | **OPEN / AUDITOR_OWNED at freeze and at completion; never marked satisfied by this worker** |

### 1.1 Frozen combined proposition shape

One new module
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
defines `structure PackedReviewerArchitectureCapstone (xs : List Int) (left
right : Nat) : Prop` whose every field is stated over the identical objects
of the preamble (`shape`, `memory`, `run`, `controller`, `w`, `reference`),
with exactly these 38 frozen fields, and the producer
`packedReviewerArchitectureCapstone_holds : forall xs left right,
PackedReviewerArchitectureCapstone xs left right`. The module contains only
the structure, its direct proof helpers, and the producer; every instance
consumption lives in the validation root so that an M12-style producer
weakening surfaces at `RMQ/Validation/EGCPStageA.lean`.

1. `payload_is_buildPayload` : `packedReviewerPayloadBits shape = SuccinctClassic.buildPayload xs`.
2. `serialized_header_payload` : `packedReviewerSerializedBits shape = packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape`.
3. `padded_final_padding` : `packedReviewerPaddedBits shape = packedReviewerSerializedBits shape ++ List.replicate (packedReviewerAllocatedBits n (longCount shape) (packedReviewerSparseCount shape) - (packedReviewerSerializedBits shape).length) false` and `(packedReviewerPaddedBits shape).length = packedReviewerAllocatedBits n (longCount shape) (packedReviewerSparseCount shape)`.
4. `memory_uniform_builder` : `memory = (List.range (packedReviewerCellCount n (longCount shape) (packedReviewerSparseCount shape))).map fun i => ((packedReviewerPaddedBits shape).drop (i * w)).take w`.
5. `run_factorization` : `run = packedReviewerDriveAgainstMemoryAux memory (packedReviewerControllerMeasure controller) controller`.
6. `one_cell_width` : every `cell` in `memory` has `cell.length = w`.
7. `memory_length_arity` : `memory.length = packedReviewerCellCount n (longCount shape) (packedReviewerSparseCount shape)`.
8. `allocation_two_n_plus_rho` : `memory.length * w <= 2 * n + packedReviewerRho n`.
9. `rho_little_o` : `SuccinctSpace.LittleOLinear packedReviewerRho`.
10. `closed_length` : `forall n' lc sc, packedReviewerClosedPayloadLength n' lc sc = packedReviewerPayloadLength n' lc sc`.
11. `width_positive` : `0 < w`.
12. `input_size_fits_width` : `n < 2 ^ w`.
13. `width_logarithmic` : `w <= 20 * (Nat.log2 (n + 2) + 1)`.
14. `header_exactly_one_cell` : `(packedReviewerHeaderBits shape).length = w`.
15. `header_fields_fit` : `longCount shape < 2 ^ w` and `packedReviewerSparseCount shape < 2 ^ w`.
16. `header_cell_zero` : `memory[0]? = some (packedReviewerHeaderBits shape)`.
17. `header_decodes` : `SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) = longCount shape`.
18. `run_opens_with_header` : under the guard, `(run.trace.map (fun event => event.request.address))[0]? = some 0`.
19. `header_liveness` : under the guard, the exact three-conjunct universal of `packedReviewerHeaderCellAddressLiveness_exact` (canonical second address, mutated second address at `longCount shape + w`, inequality).
20. `memory_only` : every `event` in `run.trace` has `event.reply = memory[event.request.address]?`.
21. `probes_allocated_and_successful` : every `event` in `run.trace` has `event.request.address < packedReviewerCellCount n (longCount shape) (packedReviewerSparseCount shape)` and some reply cell.
22. `address_machine_width` : every `event` in `run.trace` has `event.request.address < 2 ^ w`.
23. `reply_exact_width` : every replied cell in `run.trace` has length exactly `w`.
24. `ordered_grouping` : `PackedReviewerRunGrouping shape left right`.
25. `probe_plan_crossing` : `forall bit width, packedReviewerProbePlan n bit width = if width = 0 then [] else if bit % w + width <= w then [bit / w] else [bit / w, bit / w + 1]`.
26. `derived_cap_le_427` : `run.trace.length <= 427`.
27. `cap_structural_derivation` : under the guard, `packedReviewerControllerMeasure controller = 1 + 2 * packedReviewerSparsePreludeRemaining (packedReviewerSparsePreludeInit n 0) + 2 * packedReviewerWholeRemaining (packedReviewerWholeStart n left right)` and `packedReviewerSparsePreludeRemaining (packedReviewerSparsePreludeInit n 0) = 3` and `packedReviewerWholeRemaining (packedReviewerWholeStart n left right) = 210` and `packedReviewerControllerMeasure controller = 427`.
28. `guarded_reference_result` : `run.terminal = some reference.value` and `run.failed = false` and `run.state = .done reference.value`.
29. `leftmost_tie_universal` : under the guard, `forall index, run.terminal = some (some index) -> LeftmostArgMin xs left right index`.
30. `invalid_run_exact` : `not (left < right /\ right <= n) -> run.terminal = some none /\ run.failed = false /\ run.state = .done none /\ run.trace = []`.
31. `invalid_reference_none` : `not (left < right /\ right <= n) -> reference.value = none`.
32. `controller_exact_input_boundary` : `@packedReviewerController = (fun (n left right : Nat) => packedReviewerController n left right)`.
33. `controller_uniform_entry` : `forall n' l' r', packedReviewerController n' l' r' = if l' < r' /\ r' <= n' then .header n' l' r' else .done none`.
34. `store_agreement_determinism` : `forall memoryB, (forall event in run.trace, memoryB[event.request.address]? = event.reply) -> run = packedReviewerRunAgainstMemory memoryB n left right`.
35. `reachable_state_invariant` : `forall i, i < run.trace.length ->` the prefix fold `packedReviewerDriveStateAt memory controller i` is live (`packedReviewerControllerResult ... = none`), computes the emitted request (`exists request, packedReviewerNextRequest ... = some request /\ run.trace[i]? = some { request := request, reply := memory[request.address]? }`), and the drive restarted at the fold with the remaining measure reproduces `run.terminal`, `run.state`, and `run.trace.drop i`.
36. `decisive_cell_liveness` : the frozen fixture triple of `packedReviewerDecisiveCellLiveness` (canonical terminal `some (some 1)`, cell-8-mutated terminal `some (some 2)`, inequality at the `.terminal` projection).
37. `unread_cell_accept` : the frozen fixture triple of `packedReviewerUnreadCellAccept` (cell `4` allocated, never probed, and every replacement yields complete run-record equality).
38. `no_metadata_completion` : the frozen `packedReviewerNoMetadataCompletion` bridge (`forall f : Nat -> Nat -> Nat -> Option Nat`, not both fixture terminals equal `some (f 3 0 3)`).

Fields 36-38 are constant in the binders by design: they pin the frozen
fixture controls inside the combined proposition exactly as
`EG-CP-A04`/`EG-CP-A10` demand. No field may be weakened, reguarded, split
into a sibling object, or discharged from the flat `packed*` universe.

### 1.2 Frozen fixture (inherited verbatim from matrix section 10.2 of the Stage-F campaign)

- F1: `xs0 = [7, 3, 3]`, query `left0 = 0`, `right0 = 3`, `shape0 = SuccinctClassic.cartesianShape xs0` (`n = 3`, `w = 15`, 22 cells, `longCount shape0 = 0`, `packedReviewerSparseCount shape0 = 0`); duplicate minimum at indices 1 and 2; guarded leftmost result `some 1` from the independent `scanWindow` reference (`INV-ORACLE-INDEPENDENCE`).
- F2: canonical run `run0` = 68 attempted probes, terminal `some (some 1)`, controller measure exactly `427`.
- F3: header mutation: cell `0` replaced by the same-width encoding of `longCount shape + w`; the fixture's second attempted address moves `10 -> 37`.
- F4: decisive consumed cell `c0 = 8`, frozen replacement `egcpDecisiveMutantCell` (bitwise complement); mutated terminal `some (some 2)`.
- F5: proved-unread allocated cell `u0 = 4`, frozen committed replacement `egcpStageFUnreadReplacementCell = List.replicate (packedReviewerCellWidth 3) true`.

### 1.3 Frozen object-composition chain (quoted for `EG-CP-A01`)

`xs` -> `SuccinctClassic.cartesianShape xs` -> `packedReviewerPayloadBits
shape` (`= SuccinctClassic.buildPayload xs`, `rfl`-bridged) ->
`packedReviewerSerializedBits shape` (`= headerBits ++ payloadBits`) ->
`packedReviewerPaddedBits shape` (final-cell `false` padding only) ->
`packedReviewerMemory shape` (uniform `w`-bit chunking; header is cell 0 in
full) -> `packedReviewerRunAgainstMemory memory n left right` (replies are
literally `memory[address]?`; controller receives only `n, left, right`) ->
`packedReviewerRunAgainstMemory_eq_lowered` -> logical drive against
`concreteBPNativeSuccinctRMQGlobalReadStore shape` ->
`packedReviewerDriveLogical_210_simulates_packedWholeQueryRun` ->
`packedWholeQueryRun_eq` -> `packedReviewerPackedReference_eq_public` ->
`SuccinctClassic.queryTraceResult xs left right` (half-open, leftmost-tie
`List Int` reference). Space (fields 6-10) and probes (fields 20-25) name the
same `memory`; the result fields (28-29) name the same `run`.

---

## 2. Inherited invariant rows

Requirement text is copied verbatim from
`.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md` section 2.
These are the seven invariants frozen for this rung by the commissioning
contract.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge to attempt | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient | Inherited | Fields 36 (inequality at the `.terminal` projection), 19 (inequality at the trace-position-1 address projection), 38 (no metadata completion), and 35 (the terminal is reproduced from the consumed replies). | Capstone fields -> `egcpStageAArchitectureFactsExact`. | `SA-M06`, `SA-M08`, `SA-M12`, `SA-M16`, `SA-M17` REJECT; projections are value/address, never enclosing records. | Append-only ledger `EV-INV-VALUE` | Open at freeze; final status in ledger |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself | Inherited | The liveness propositions (fields 19, 36) are inequalities of computed projections of actual runs, not defined predicates; the grouping (field 24) is a trace identity of the executed run; `SA-M10` rejects a forged trace; `SA-M17` rejects a neutralized decisive mutant (the corruption evidence cannot be vacuously true). | Capstone -> validation root. | `SA-M10-DISCONNECTED-TRACE`, `SA-M17-DECISIVE-MUTANT-NEUTRALIZED` REJECT. | Append-only ledger `EV-INV-NONVAC` | Open at freeze; final status in ledger |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace | Inherited | Field 34: ordered request/reply agreement on the run's trace determines the complete run record; the unread-cell control (field 37) is its expected-ACCEPT instance. | Capstone field 34/37 -> `egcpStageAArchitectureFactsExact`; producer `packedReviewerRunAgainstMemory_eq_of_agree`. | `SA-A02-UNREAD-CELL-EXPECTED-ACCEPT` must ACCEPT; `SA-M17` must REJECT. | Append-only ledger `EV-INV-AGREE` | Open at freeze; final status in ledger |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store | Inherited | Fields 20-21: every trace event's reply is literally `memory[event.request.address]?` and successful; field 35 gives the positional (occurrence-indexed) form via `run.trace[i]?`. | Capstone -> validation root. | `SA-M01-SIBLING-STORE`, `SA-M15-HIDDEN-UNCOUNTED-TABLE` REJECT. | Append-only ledger `EV-INV-BACK` | Open at freeze; final status in ledger |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain | Inherited | Every capstone field quantifies over the same `xs`, `left`, `right` and names the same `memory`/`run`/`controller`/`w` terms; the guard `left < right /\ right <= n` is identical wherever a guard appears; unguarded fields (28) are consistent with the guarded invalid case by field 31. | The single structure `PackedReviewerArchitectureCapstone`. | `SA-M02-SIBLING-PAYLOAD`, `SA-M18`, `SA-M19` REJECT. | Append-only ledger `EV-INV-COMP` | Open at freeze; final status in ledger |
| `INV-MUTATION-REPRODUCIBILITY` | when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean | Inherited | `scripts/eg_cp_stagea_replay.ps1` committed with the section-4 registry; full mode passes on the committed clean candidate with zero target-absent cases; SHA256 restoration and terminal clean tree on every case. | `EG-CP-A12` chain. | Registry integrity, activation needles, expected-surface matching, `-IntegrityProbe` controls. | Append-only ledger `EV-INV-MUT` | Open at freeze; final status in ledger |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct | Inherited | The result report records separately: payload bits (`buildPayload`, `<= 2n + o(n)` logical), allocated bits (`cellCount * w`), proof-only fields (none carry answers/routes -- proof-free controller state), the model probe cap (`427` attempted physical probes, upper bound), logical fuel (`210`, attempts not reads, `DD-20260805-075`), and Lean wall-clock (never a claim). No cell conflates allocated bits with meaningful bits. | `docs/internal/EG_CP_STAGEA_RESULT.md`. | Report review against this row; the ledger records the category table. | Append-only ledger `EV-INV-CAT` | Open at freeze; final status in ledger |

---

## 3. Replay-harness and integrity contract rows

Requirement text is copied verbatim from the commissioning prompt's
acceptance contract.

| ID | Exact frozen requirement | Evidence needed | Evidence obtained | Status |
| --- | --- | --- | --- | --- |
| `REPLAY-EXACT-REGISTRY` | the runner must declare the exact ordered frozen case registry, reject missing/duplicate IDs, verify ID-to-field/object mappings, and check exact ACCEPT/REJECT totals. A total pass count alone is insufficient. | `Test-RegistryIntegrity` in `scripts/eg_cp_stagea_replay.ps1` validates, before any build: exactly 21 entries; ascending orders 1..21; unique IDs; every verdict mapped ACCEPT/REJECT; exactly 2 ACCEPT and 19 REJECT; and a nonempty frozen row/field mapping on every entry matching section 4. | Append-only ledger `EV-REPLAY-REG` | Open at freeze; final status in ledger |
| `REPLAY-SELECTOR-NONVACUITY` | focused selection executes exactly one requested frozen ID and rejects unknown IDs. Add cheap controls for an omitted middle ID, duplicate middle ID, valid ID, unknown ID, omitted selector, and explicit empty/whitespace selector at the real script boundary. Only omission may select the full registry when the frozen contract permits it. | Script-boundary invocations: `-Case <valid>` runs exactly one case; `-Case <unknown>`, `-Case ''`, `-Case '   '` exit 2 before any build; omission means full mode; `-IntegrityProbe OmitMiddle` and `-IntegrityProbe DuplicateMiddle` corrupt an in-memory registry copy and require `Test-RegistryIntegrity` to fail (exit 3), exercising the omitted/duplicate middle-ID rejections at the real script boundary. | Append-only ledger `EV-REPLAY-SEL` | Open at freeze; final status in ledger |
| `REPLAY-SUBPROCESS-DEADLINE` | every external compiler/tool stage has a positive evidence-based deadline, timeout is failure, the owned process tree is terminated, and cleanup plus live-tree integrity run in `finally`. Exercise the root-plus-descendant sleeper self-test on Windows, the required gate platform. State any non-Windows limitation without implying cross-platform certification. | Per-case deadline = max(clean-build seconds, mutated-chain-probe seconds) * 4 with floor 300 s, both measured on this tree before any case; timeout is failure; `Stop-ProcessTree` (taskkill /T /F on Windows); detached-grandchild sleeper self-test PASS on Windows required before the campaign; restoration in `finally` with SHA256 verification; the non-Windows branch is present but uncertified on this task (limitation stated, no cross-platform claim). | Append-only ledger `EV-REPLAY-DL` | Open at freeze; final status in ledger |
| `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | decode the exact base matrix-freeze blob and final candidate as strict UTF-8 and compare complete row bytes for every frozen requirement and registry ID. Reject missing/duplicate IDs and report exact changed IDs. Include a mojibake negative control; normalized text, row counts, or visual inspection are insufficient. | A strict-UTF-8 checker (run from outside the repository, not committed) decodes this file's blob at the matrix-freeze commit and at the final candidate, keys every table row of sections 1-4 by (section, ID), requires exact byte equality per row, rejects missing/duplicate IDs, reports exact changed IDs, and is itself shown to detect injected mojibake (`Â¬`, `â€œ...â€`) in a corrupted temporary copy (negative control). All post-freeze additions must lie in sections 7-8. | Append-only ledger `EV-BYTE` | Open at freeze; final status in ledger |
| `NAMED-REGRESSION-REALITY` | before relying on an immutable negative fixture, reproduce the failure with the same decoder, predicate, guards, objects, and quantifiers. If a legacy case does not discriminate its named property, fix the new Stage-A registry contract before freeze or add a matching case; never overclaim an inherited fixture. | Every inherited Stage-F mutation body reused in section 4 targets the reviewer controller/memory/run -- the same objects the Stage-A rows govern -- and is re-executed by this campaign against the Stage-A surface with its expected failing surface re-observed. The flat-universe legacy case `M09-WRONG-CELL-CROSSING` (targets `Probe.lean`, the flat codec) does NOT discriminate the reviewer probe plan, so section 4 adds the matching reviewer case `SA-M09-CROSSING-SWAP` targeting `ReviewerProbe.lean` instead of overclaiming the inherited fixture. | Append-only ledger `EV-REGRESSION` | Open at freeze; final status in ledger |

---

## 4. Frozen ordered replay registry

`scripts/eg_cp_stagea_replay.ps1` must encode this list literally and reject
missing, duplicate, reordered, or unmapped IDs. Surface module for every
case: `RMQ.Validation.EGCPStageA` (its import closure contains every named
failing file). Verdict totals: exactly **2 ACCEPT / 19 REJECT / 21 cases**.
"Inherited" means the enacted mutation body is byte-reused from the frozen
Stage-F registry of `docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md`
sections 3/10.4 (same P/Q, decoder, objects, guards, quantifiers); the
Stage-F runner itself is not edited. Labels are honest per the audited
`M13`/`M03` dispositions.

| Order | ID | Mutation (frozen intent) | Expected verdict | Named failing surface (`ExpectFile`) | Covered rows | Capstone fields / objects | Label |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `SA-A01-PRODUCTION-EXPECTED-ACCEPT` | unchanged final implementation, consumer, matrix, and result | ACCEPT | none (surface must build) | all rows (control) | all fields | control |
| 2 | `SA-A02-UNREAD-CELL-EXPECTED-ACCEPT` | patch the frozen unread replacement value `egcpStageFUnreadReplacementCell` (inherited Stage-F `A02` body) | ACCEPT | none (surface must build; agreement route is value-independent) | `EG-CP-A10`, `INV-STORE-AGREEMENT` | field 37 / fixture cell `u0 = 4` | control (value-preserving by design) |
| 3 | `SA-M01-SIBLING-STORE` | driver binds `siblingLogicalStore := memory ++ [[]]` and drives against it (inherited `M05` body) | REJECT | `PackedCellProbe/ReviewerController.lean` | `EG-CP-A01`, `INV-READ-BACKING` | fields 5, 20 / `memory` vs sibling | semantic |
| 4 | `SA-M02-SIBLING-PAYLOAD` | serialized bits embed `siblingExecutionPayload := packedReviewerPayloadBits shape ++ [false]` (inherited `M11` body) | REJECT | `PackedCellProbe/ReviewerMemory.lean` | `EG-CP-A01`, `EG-CP-A02`, `INV-PUBLIC-COMPOSITION` | fields 1-3 / payload identity | semantic |
| 5 | `SA-M03-CANONICAL-SHAPE-BY-N` | run drives `packedReviewerMemory (packedSpine n)` synthesized from `n` (inherited `M04` body) | REJECT | `PackedCellProbe/ReviewerController.lean` | `EG-CP-A01`, `EG-CP-A09` | field 5 / supplied vs synthesized memory | semantic |
| 6 | `SA-M04-ALLOCATION-HEADER-CELL-DROP` | `packedReviewerCellCount` drops the `1 +` header cell (new Stage-A body) | REJECT | `PackedCellProbe/ReviewerMemory.lean` | `EG-CP-A02` | fields 3, 7, 8 / allocated capacity | semantic |
| 7 | `SA-M05-WIDTH-SUBSTITUTION` | `packedReviewerCellWidth n` redefined to `SuccinctRank.machineWordBits (n + 2)` (new Stage-A body) | REJECT | `PackedCellProbe/ReviewerWidth.lean` | `EG-CP-A03` | fields 11-15 / the one width function | semantic |
| 8 | `SA-M06-WRONG-LONG-COUNT` | header consume arm binds `longCount := SuccinctSpace.bitsToNatLE cell + 1` (inherited `M01` body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A04`, `INV-VALUE-DEPENDENCY` | fields 17, 19 / decoded header value | semantic |
| 9 | `SA-M07-HOST-LONG-COUNT-MIRROR` | run bypasses the header reply with a host-preprocessed mirror (inherited `M02` body) | REJECT | `PackedCellProbe/ReviewerController.lean` | `EG-CP-A04`, `EG-CP-A09` | fields 16, 18 / charged header read | semantic |
| 10 | `SA-M08-LONG-COUNT-IGNORED` | header consume arm binds `longCount := 0`, read retained (inherited `M14` body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A04`, `INV-VALUE-DEPENDENCY` | field 19 / downstream address dependency | semantic |
| 11 | `SA-M09-CROSSING-SWAP` | `packedReviewerProbePlan` crossing branch swapped to `[bit / w + 1, bit / w]` (new Stage-A body; reviewer analog of flat `M09`) | REJECT | `PackedCellProbe/ReviewerProbe.lean` | `EG-CP-A05` | field 25 / crossing expansion order | semantic |
| 12 | `SA-M10-DISCONNECTED-TRACE` | expected-physical-trace valid branch forged empty while the result path is untouched (inherited `M07` body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A05`, `EG-CP-A10`, `INV-SEMANTIC-NONVACUITY` | field 24 / ordered grouping | semantic |
| 13 | `SA-M11-FORGED-PROBE-CAP` | measure header arm replaced by the stored literal `427` (inherited `M08` body) | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | `EG-CP-A06` | field 27 / derived measure | structural (the commissioned structural surface) |
| 14 | `SA-M12-RESULT-OFFSET` | whole-result completion arm returns `value.map (fun index => index + 1)` (new Stage-A body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A07`, `INV-VALUE-DEPENDENCY` | fields 28-29 / returned index | semantic |
| 15 | `SA-M13-INVALID-GUARD-RESULT` | controller invalid entry arm returns `.done (some 0)` instead of `.done none` (new Stage-A body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A08` | fields 30-31 / invalid-domain result | semantic |
| 16 | `SA-M14-SHAPE-PARAMETER` | controller gains an optional `CartesianShape` parameter (inherited `M03` body) | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | `EG-CP-A09` | field 32 / exact input boundary | structural (exact signature; the frozen requirement is the signature) |
| 17 | `SA-M15-HIDDEN-UNCOUNTED-TABLE` | driver serves replies from `hiddenUncountedTable := memory.take 1` when in range (inherited `M13` body) | REJECT | `PackedCellProbe/ReviewerController.lean` | `EG-CP-A09`, `INV-READ-BACKING` | field 20 / reply provenance | value-preserving, structurally honest (audited `P3` disposition; paired semantic rejections: `SA-M03`, `SA-M07`) |
| 18 | `SA-M16-ANSWER-ORACLE` | completion arm discards the computed value and returns the metadata oracle `some n` (inherited `M06` body) | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | `EG-CP-A07`, `EG-CP-A10` | fields 28, 38 / metadata completion; the frozen `SF-M06-BRIDGE` covers the reference-oracle direction | semantic (metadata-derived; bridge-covered, never described as having refuted a literal reference-semantics oracle) |
| 19 | `SA-M17-DECISIVE-MUTANT-NEUTRALIZED` | `egcpDecisiveMutantCell` set to the canonical cell-8 value, so the decisive corruption becomes a no-op (new Stage-A body) | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | `EG-CP-A10`, `INV-SEMANTIC-NONVACUITY` | field 36 / decisive corruption reality | semantic |
| 20 | `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` | `packedReviewerRunAgainstMemory_public_certificate` weakened to `True`, original kept private (inherited `M12` body) | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | `EG-CP-A11`, `INV-PUBLIC-COMPOSITION` | certificate-projected fields | semantic (public proposition weakening) |
| 21 | `SA-M19-ARCHITECTURE-PROPOSITION-WEAKENING` | `packedReviewerArchitectureCapstone_holds` weakened to `True`, original kept private (new Stage-A body, M12-style) | REJECT | `RMQ/Validation/EGCPStageA.lean` | `EG-CP-A11` | the entire combined proposition | semantic (public proposition weakening at the committed consumer) |

Runner contract (frozen): parameters `-Case <ID>`, `-SelfTestOnly`,
`-IntegrityProbe <OmitMiddle|DuplicateMiddle>`, `-SkipSelfTest` (development
only; full mode refuses it); `-SelfTestOnly` and `-IntegrityProbe` are
exclusive with `-Case` and with each other; full mode = omission of every
selector. Deadline calibration probes
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean` (the
deepest common import of every mutation target). Every mutation is applied
byte-exactly, activation-checked, built, surface-matched against
`ExpectFile`, restored in `finally`, and SHA256-verified; the run ends with a
`git status --porcelain` clean check. A full-mode run with any
`TARGET-ABSENT` case exits non-zero.

---

## 5. Verification command ledger (frozen plan; outcomes in section 8)

Roles: D = development-loop, F = final-required, C = conditional.

| ID | Command | Role | Rows covered | Unique failure mode |
| --- | --- | --- | --- | --- |
| `SA-CHK-00` | `scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a... -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"` | F (precondition) | governance | stale/missing role skill |
| `SA-CHK-01` | focused `lake build` of each changed Lean module during development; final `lake build RMQ.Validation.EGCPStageA` on the frozen tree | D then F | all Lean rows | first local theorem/signature failure |
| `SA-CHK-02` | `lake build RMQ` | F | whole-library integration | transitive consumer failure |
| `SA-CHK-03` | `lake env lean scripts/axiom_check.lean` | F | trust boundary; new curated Stage-A entries | forbidden axiom reaches a capstone |
| `SA-CHK-04` | replay: bounded startup/shape smoke (measured clean surface build), exact selector `SA-A01-PRODUCTION-EXPECTED-ACCEPT`, then the full 21-case registry exactly once on the committed frozen candidate | D then F | `EG-CP-A12`, `INV-MUTATION-REPRODUCIBILITY` | a mutation is not rejected at its named surface |
| `SA-CHK-05` | runner boundary controls: `-Case` valid/unknown/empty/whitespace; `-IntegrityProbe OmitMiddle`/`DuplicateMiddle`; Windows `-SelfTestOnly` | F | `REPLAY-SELECTOR-NONVACUITY`, `REPLAY-SUBPROCESS-DEADLINE` | selector or termination contract fails open |
| `SA-CHK-06` | `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml` | F | hygiene | forbidden token |
| `SA-CHK-07` | `rg -n "native_decide|Lean\.ofReduceBool" RMQ` | F | hygiene | native decision shortcut |
| `SA-CHK-08` | `git diff --check` (working tree) and `git diff --check 270d78559adc33fe872b6d17bd54d8e51567a605..HEAD` (after committing) | F | committed hygiene | committed whitespace |
| `SA-CHK-09` | `powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 270d78559adc33fe872b6d17bd54d8e51567a605`; additionally each commit validates at `-Base HEAD~1` (`WDD-20260726-007`) | F | design policy | design-sensitive path with no decision entry |
| `SA-CHK-10` | `powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | F (policy gate; public prose is out of write scope -- any new hit is fixed only within owned evidence paths or reported as a scope blocker) | claim policy | overclaim in owned prose |
| `SA-CHK-11` | strict UTF-8 decode of changed docs; frozen-row byte-integrity of this matrix against the freeze-commit blob, keyed by (section, ID), with the mojibake negative control | F | `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | silent row edit or encoding corruption |
| `SA-CHK-12` | byte-identity of `scripts/eg_cp_final_falsification_replay.ps1` against the exact base blob | F (C: its full inherited registry reruns only if it were changed -- it must not be) | `EG-CP-A12` | accidental edit of the inherited frozen campaign |
| `SA-CHK-13` | M03-style expected-failure probes outside Git during development (literal consumer and decisive semantic fields), restored and byte-verified immediately | D | anti-vacuity of the consumer | consumer fails to discriminate |
| `SA-CHK-14` | aggregate `scripts/gate.ps1` | C | only if a final changed surface is not owned by `SA-CHK-01`..`SA-CHK-12`; not frozen as the aggregate owner, so the default is a recorded skip | duplicated expensive certification |

Heavy-process discipline: one heavy Lean/Lake process at a time in this build
tree; `Global\RMQHeavyVerification` acquired for any command expected to
exceed five minutes; deadlines chosen from observed runtimes with cold-cache
margin (closest observed: Stage-F full replay 1430.4 s, clean surface build
2-228 s, `lake build RMQ` 16-266 s, axiom check 190-257 s); no unchanged
expensive rerun after a wrapper timeout without a material change.

---

## 6. Explicitly deferred, recorded as non-blocking by the commissioning contract

| Item | Why non-blocking here |
| --- | --- |
| `EG-CP-A13-CAPSTONE-AUDIT` | Deliberately the next independent consumer; this worker produces the verdict-free packet only. |
| Coordinator reconstruction/acceptance, branch integration/push | Coordinator decisions; not required for the A01-A12 candidate to be true. |
| Current/public claim synchronization; README/family/paper/model-adequacy surfaces | Out of write scope; the 18-surface registry is untouched. |
| `S1` bit-offset probe semantics and accounting; `V1`; publication; full EG-CP closure | Downstream roadmap nodes; not claimed. |
| Non-Windows deadline/process-tree certification | The required gate platform is Windows; the limitation is stated, not silently promoted. |

---

## 7. Contract amendments

### `CA-20260807-001` — field 39 `valid_answer_is_index` (strengthening)

Coordinator amendment, 2026-08-07, in response to fresh-blind audit `AUD1`
finding `P3-3` (report
`docs/internal/audit_reports/2026-08-06_EG_CP_STAGEA_CLOSE_R1_fresh_blind.md`,
audit commit `60827a13d38de0a74fc2ae861c5526deae012ff2`).

**Finding.** The frozen 38-field proposition of section 1.1 never states that
a *valid* query is answered with an index. Field 28 pins
`run.terminal = some reference.value` unconditionally and field 29 is
conditional on the terminal already being `some (some index)`. A reader of
the combined proposition alone therefore cannot conclude that the packed
machine answers valid queries at all. The invalid domain has its companion
(field 31, `invalid_reference_none`); the valid domain had none. This is an
asymmetry in what the proposition *displays*, not a soundness defect: the
fact is a short consequence of the untouched accepted reference theorem
`SuccinctClassic.queryCosted_exact` composed with field 28.

**Amendment.** Section 1.1 is extended by exactly one field, appended as
field 39 and changing no existing field:

39. `valid_answer_is_index` : under the guard `left < right /\ right <= n`,
    `∃ index, run.terminal = some (some index) /\ (SuccinctClassic.queryTraceResult xs left right).value = some index /\ LeftmostArgMin xs left right index`.

Producer: `packedReviewerValidRunAnswersIndex` in
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`,
proved from `SuccinctClassic.queryCosted_exact` / `scanWindow` (the
independent specification, never the implementation under test) composed
with the public run certificate's `terminal_eq`. Consumer: the matching
field of `EGCPStageAArchitectureFacts` in `RMQ/Validation/EGCPStageA.lean`.

**Authority and scope.** This is a strengthening: no frozen row, field,
registry entry, guard, object, or quantifier is removed, renamed, narrowed,
or weakened, and every one of the original 38 fields is byte-unchanged.
Sections 1-4 outside this amendment remain byte-frozen against the
matrix-freeze commit `f4107cd15173fef690ba05e51becb9c65b6c7d60`, and the
`FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` check is re-run against that blob
after the repair. `EG-CP-A07`'s frozen requirement sentence is unchanged;
the amendment makes the row self-contained rather than closing it by
composition with an external theorem.

**Effect on the audit.** `AUD1` audited exact commit
`ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23`, whose 38 fields are untouched by
this amendment. The repair adds Lean, so every check that transitively
consumes it is re-run on the repaired tree — including the full 21-case
replay campaign, which is re-certified once rather than inherited.

---

## 8. Append-only evidence ledger

Entries are appended below during the campaign, keyed `EV-<row>` /
`CHK-<id>`. No entry edits a frozen row above.

- `EV-GOV` (2026-08-06, at freeze): `project_skill_preflight.ps1` PASS at
  checkout `270d78559adc33fe872b6d17bd54d8e51567a605` with governance
  `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`; expected, checkout,
  working-tree, and runtime catalogs all equal
  (`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`);
  `required_mode=role-skills`. Branch `codex/eg-cp-stagea-close-r1` created
  at the exact base on a clean fresh worktree
  (`C:\Users\poin\Documents\RMQ\.claude\worktrees\loving-euclid-57578a`).

- `EV-A01`..`EV-A10` (2026-08-06, frozen proof/replay candidate
  `1198ff6fbd66a4de991ad7e8fe1235a452d4b337`, tree `35327c30...`, parent
  `08dd29d4d72047c9da1f938d411d65264bdfd2b2`): every capstone field of
  section 1.1 is enacted verbatim in
  `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`
  and produced by `packedReviewerArchitectureCapstone_holds`; the complete
  requirement-to-evidence table with P/Q outcomes, provenance levels, and
  replay verdicts is `docs/internal/EG_CP_STAGEA_RESULT.md` section 3.
  Worker status per row: CANDIDATE_COMPLETE; coordinator acceptance pending.
- `EV-A11` (2026-08-06): `RMQ/Validation/EGCPStageA.lean` commits the
  signature pin, the literal 38-field restatement
  `EGCPStageAArchitectureFacts`/`egcpStageAArchitectureFactsExact`, width
  literals `10/14/14/15`, the boundary campaign, and the fixture re-pins;
  M03-style probes (cap `427 -> 428`, decisive `some 2 -> some 3`) each
  failed the build at `RMQ/Validation/EGCPStageA.lean` with SHA-verified
  restoration; replay `SA-M19` REJECTs at that file.  CANDIDATE_COMPLETE
  (worker).
- `EV-A12` / `EV-INV-MUT` (2026-08-06): certification full campaign on
  `1198ff6`: `FULL MODE PASS`, exit 0, 1100 s, 21/21 as commissioned
  (2 ACCEPT / 19 REJECT) at the frozen surfaces, 0 target-absent,
  calibration 5 s / 156 s, deadline 624 s, self-test PASS, 20 SHA-verified
  restorations, terminal clean.  Diagnostic run on `08dd29d` (20/21 plus the
  runner's own `SA-M13` needle-encoding defect) retained as evidence;
  repair `WDD-20260806-010` (ASCII-only needle; frozen registry rows
  untouched; single-case verification REJECT-as-commissioned before the
  rerun).  CANDIDATE_COMPLETE (worker).
- `EV-A13` (2026-08-06): verdict-free packet
  `docs/internal/audit_packets/EG_CP_STAGEA_AUD1_PACKET.md` committed in the
  report commit (parent `1198ff6`).  Row remains OPEN / AUDITOR_OWNED.
- `EV-INV-VALUE`, `EV-INV-NONVAC`, `EV-INV-AGREE`, `EV-INV-BACK`,
  `EV-INV-COMP`, `EV-INV-CAT` (2026-08-06): closed at worker level by the
  capstone fields and replay cases named in their frozen rows; details in
  `docs/internal/EG_CP_STAGEA_RESULT.md` section 4 and the category table in
  section 7.
- `EV-REPLAY-REG`, `EV-REPLAY-SEL`, `EV-REPLAY-DL` (2026-08-06): registry
  integrity validated on every invocation (21 ordered entries, 2/19 totals,
  nonempty mappings); selector receipts (unknown/empty/whitespace/bogus/
  combined fail closed; `-IntegrityProbe OmitMiddle`/`DuplicateMiddle`
  reject corrupted copies; omission = full mode); measured deadlines
  (860 s / 780 s / 604 s / 624 s across the four calibrated runs); Windows
  sleeper self-test PASS (the required gate platform; non-Windows branch
  carried, uncertified).
- `EV-BYTE` (2026-08-06): strict-UTF-8 frozen-row comparison, freeze blob
  `719c01d1e182d3288eebc9427bb21f16b4d414f7` vs candidate: 46/46 row IDs
  byte-identical, 0 missing/duplicated/changed/added-in-frozen-sections;
  injected-row-edit and injected-mojibake negative controls both fire.
  Rerun after the report commit; receipt in the worker terminal response.
- `EV-REGRESSION` (2026-08-06): all thirteen inherited bodies re-executed
  against the Stage-A surface with frozen first-failing files re-observed;
  the reviewer crossing case `SA-M09` replaced the non-discriminating flat
  legacy `M09` as frozen in section 3.
- `CHK` receipts (2026-08-06): `SA-CHK-00` PASS; `SA-CHK-01` capstone cold
  chain 1060 s (one proof-goal repair: guard `simp` replaced by
  `rw [if_pos hvalid]` after the `@[simp]` size lemma rewrote the goal),
  then 15 s / 6 s / 8 s warm receipts; `SA-CHK-02` exit 0, 198 s;
  `SA-CHK-03` exit 0, 176 s, four Stage-A entries on
  `[propext, Classical.choice, Quot.sound]` only; `SA-CHK-04` selector
  ACCEPT 421 s, diagnostic 1400 s, certification PASS 1100 s; `SA-CHK-05`
  all boundary controls as expected; `SA-CHK-06`/`07` zero matches;
  `SA-CHK-08` clean at the frozen candidate; `SA-CHK-09` per-commit PASS at
  every commit and full-range PASS (9 changed files); `SA-CHK-10` PASS
  (1525 hits, 0 strict failures); `SA-CHK-11` PASS as `EV-BYTE`;
  `SA-CHK-12` byte-identical (`3420c76c...`), inherited registry not rerun;
  `SA-CHK-13` both probes fail at the consumer file with SHA-verified
  restoration; `SA-CHK-14` recorded skip (not the frozen aggregate owner;
  no unowned surface).  One heavy Lean/Lake process at a time throughout;
  the concurrent early hygiene preview was discarded and re-run on the
  quiet frozen tree.

- `EV-A13` correction (2026-08-06, append-only): the report record's first
  landing `ea08f28` was reverted by `c38e885` for the missing same-commit
  workflow-ledger pairing (`WDD-20260806-011`) and re-landed identically in
  the final report commit; the packet's exact commit identity is therefore
  the final report commit, whose proof-bearing parent remains `1198ff6`.

### `AUD1` fresh-blind audit and coordinator dispositions (2026-08-07, append-only)

- `EV-A13` **audit performed, row still AUDITOR_OWNED.** Fresh-blind
  report-only audit `EG-CP-STAGEA-AUD1` of exact candidate
  `ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23`; report committed as
  `60827a13d38de0a74fc2ae861c5526deae012ff2` (one file added, directly on the
  audited candidate) at
  `docs/internal/audit_reports/2026-08-06_EG_CP_STAGEA_CLOSE_R1_fresh_blind.md`.
  Auditor recommendation: **merge-ready with follow-up**, no `P0`, no `P1`,
  one `P2`, five `P3`. An auditor may only recommend; this entry records the
  audit's occurrence and the coordinator's dispositions, not acceptance.
- `EV-A13` **correction to the earlier `EV-A13` correction** (`AUD1` `P3-5`):
  the phrase "re-landed identically" is exact for four of the six report
  files (packet, worklog, round-log, digestion) and inexact for two
  (`EG_CP_STAGEA_RESULT.md`, this matrix), whose `ea08f28..ec35b5d`
  differences are precisely the disclosure of the repair being described,
  alongside `WORKFLOW_DESIGN_DECISIONS.md`. The result report's identity row
  now states this precisely. No concealed change exists.
- **`P2-1` disposition (integration-gating, owner action required).** Commit
  `ea08f2851e8be9951dceb56a1c021ab170de80b8` fails
  `design_decision_check.ps1 -Strict -Base HEAD~1` at its own parent;
  independently reproduced by the coordinator in a detached worktree (exit 1,
  naming `AUDIT_AND_A_DESIGN.md`, `audit_packets/EG_CP_STAGEA_AUD1_PACKET.md`,
  `EG_CP_STAGEA_RESULT.md`). Disposition: **integrate this branch into `main`
  as a squash merge**, so no commit failing the per-commit gate ever enters
  `main`'s history while the tree remains byte-identical. Branch history is
  deliberately *not* rewritten: `ea08f28` is the parent chain of the audited
  commit `ec35b5d` and of the audit report commit `60827a1`, and rewriting it
  would destroy the exact objects those audits name. Recorded as
  `WDD-20260807-012`. Execution requires explicit owner authority (roadmap
  workflow rule 9) and is not performed here.
- **`P3-1` disposition: fixed.** The `AUD1` packet's `SA-CHK-09` receipt now
  scopes its per-commit claim to the frozen candidate and states the
  `ea08f28` exception explicitly, so the auditor-facing surface carries the
  same disclosure as the result report.
- **`P3-2` disposition: fixed.** `SA-M04-ALLOCATION-HEADER-CELL-DROP`,
  `SA-M09-CROSSING-SWAP`, and `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` now
  declare activation needles, so every entry the frozen section-4 label calls
  semantic carries one and the `EG-CP-A12` evidence cell's literal claim
  holds. The only needle-less entries are `SA-A01` (patches nothing) and the
  two entries frozen as structural (`SA-M11`, `SA-M14`). No frozen registry
  row changed: section 4 freezes mutation intent, verdict, surface, and
  mappings, not needle bytes.
- **`P3-3` disposition: fixed by contract amendment `CA-20260807-001`** —
  field 39 `valid_answer_is_index`, with producer
  `packedReviewerValidRunAnswersIndex`. `EG-CP-A07` is now self-contained
  rather than closed by composition with an external reference theorem.
- **`P3-4` disposition: recorded, no edit possible.** Section 3's
  `REPLAY-SELECTOR-NONVACUITY` cell froze "`-Case ''` ... exit 2". On Windows
  PowerShell 5.1 the `powershell -File` argument parser consumes a truly
  empty argument before the script runs, so that form exits **1** at the
  binder; every other form (unknown, whitespace, `-Case ''` invoked
  in-process, `'""'`, and all combined selectors) exits 2 at the script's own
  guard. Every form fails closed before any build, so the contract's
  substance holds; the frozen cell is byte-frozen and is to be read with this
  qualification. The result report and worklog already record it accurately.
- **Re-certification after the repair.** The `CA-20260807-001` repair changes
  Lean, so the checks that transitively consume it were re-run on the
  repaired tree rather than inherited from the audited commit; receipts are
  appended below and in the result report's ledger.

### Re-certification receipts on the repaired tree (2026-08-07, append-only)

All observed on the `CA-20260807-001` repair commit
`a8d2a5c2881564abd85d651041f7d9953c4054f0` (tree
`d0f6aef5bf27f7cdda03f63720f1dbe780bfea5e`, parent `ec35b5d...`). Nothing was
inherited from the audited commit: the repair changes Lean, so every
transitively dependent check was re-run.

| Check | Receipt |
| --- | --- |
| `lake build RMQ.Validation.EGCPStageA` | exit 0, 9 s |
| `lake build RMQ RMQUnionFind` | exit 0, 3 s (warm) |
| `lake env lean scripts/axiom_check.lean` | exit 0, 176 s; zero `sorryAx`/`ofReduceBool`/`trustCompiler`; `egcpStageAArchitectureFactsExact` (now projecting field 39) on `[propext, Classical.choice, Quot.sound]` |
| Full 21-case campaign, exactly once | **`FULL MODE PASS`, exit 0, 1214 s**: 21/21 as commissioned, 0 target-absent, calibration 1 s clean / 142 s probe, deadline 568 s, self-test PASS, 20 SHA256-verified restorations, terminal tree clean, zero `REPLAY-FAIL` lines |
| Repaired needles | `SA-M04`, `SA-M09`, `SA-M18` each log `activation check passed (1 needles present and used)` before their build -- the `P3-2` fix is live, not merely declared |
| Forbidden-token and native scans | zero matches over `RMQ` and `lakefile.toml` |
| `git diff --check` (working tree and `270d7855..HEAD`) | clean, exit 0 |
| `design_decision_check.ps1 -Strict -Base 270d7855...` | PASS exit 0 (`checked 13 changed files (4 code, 5 workflow, 5 neutral)`); the repair commit also passes at `-Base HEAD~1` |
| `claim_drift_scan.ps1 -Strict` | PASS exit 0 (`1531 hits, 0 strict failures`) |
| `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | **PASS**: 46/46 frozen row IDs byte-identical to freeze blob `719c01d1...`, 0 missing/duplicated/changed; both negative controls fire. This is the mechanical evidence that `CA-20260807-001` added field 39 without disturbing any audited row. |
| `scripts/eg_cp_final_falsification_replay.ps1` | still byte-identical to the exact base (`3420c76c...`); inherited registry not rerun |

### Coordinator disposition: Stage A `ACCEPTED` (2026-08-07, append-only)

`EG-CP-A13-CAPSTONE-AUDIT` is **CLOSED**, and the coordinator records **local
Stage-A packed-architecture acceptance**. Both halves of the row are
satisfied:

- *Fresh-blind exact-commit audit:* `EG-CP-STAGEA-AUD1` against
  `ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23`, report commit
  `60827a13d38de0a74fc2ae861c5526deae012ff2`, verdict **merge-ready with
  follow-up**, no `P0`, no `P1`. The report is carried onto `main` with this
  integration as durable evidence (blob `fbcf778a...`, byte-identical to the
  audit branch).
- *Coordinator reconstruction:* every finding independently reproduced from
  Git and source before disposition, and the auditor's positive claims
  spot-checked (no flat-universe leakage, `LeftmostArgMin` a genuine
  `List Int` specification, no acceptance overclaim in the candidate). All
  six findings disposed; the substantive one (`P3-3`) repaired by amendment
  `CA-20260807-001` and re-certified from scratch.

Acceptance covers `EG-CP-A01`..`EG-CP-A13`, the seven inherited invariants,
and the five harness/integrity contracts of this matrix, at the repaired
lineage. It covers nothing else: public-claim synchronization, the 18-surface
fact registry, `S1`, `V1`, publication, and full EG-CP closure remain open and
unclaimed, and no headline is promoted by this record.

Integration: squash merge into local `main` under `WDD-20260807-012`, with
explicit owner authorization given 2026-08-07. No push is performed or
authorized by this record; `origin/main` remains behind and is a separate
owner decision.

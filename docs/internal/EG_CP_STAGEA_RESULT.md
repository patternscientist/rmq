Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# EG-CP Stage A result: the packed-architecture worker rung `A01`-`A12`

Worker handle: `EG-CP-STAGEA-CLOSE-R1`.
Requested title: `(EG-CP-STAGEA-CLOSE-R1) Freeze Stage A and close A01-A12`.
Branch: `codex/eg-cp-stagea-close-r1`, fresh worktree
`C:\Users\poin\Documents\RMQ\.claude\worktrees\loving-euclid-57578a`.

This report begins with the exact worker status above. It claims the Stage-A
worker rung `A01`-`A12` as a candidate only. It does not claim
`EG-CP-A13-CAPSTONE-AUDIT`, architecture acceptance, merge readiness,
integration, push, publication, public-claim synchronization, `S1`, `V1`, or
full EG-CP closure; `EG-CP-A13` is OPEN and auditor-owned by design.

## 1. Exact identity and provenance

| Object | Exact value |
| --- | --- |
| Exact accepted base | `270d78559adc33fe872b6d17bd54d8e51567a605` (tree `7b872cf144503cebf61097f857fa779081076107`) -- the coordinator-accepted, locally merged Stage-F `FEASIBILITY_PASS` tree |
| Workflow-governance ref | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified ancestor; preflight PASS with runtime catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`) |
| Matrix-freeze commit | `f4107cd15173fef690ba05e51becb9c65b6c7d60` (tree `9f67cb4162fac12fab59a09d5941f208fdd4f123`, parent `270d7855...`) |
| Implementation commit | `08dd29d4d72047c9da1f938d411d65264bdfd2b2` (tree `21c121e3931eab3192abe9a62f61fa4da78de22f`, parent `f4107cd...`) -- capstone, consumer, runner, registrations |
| Frozen proof/replay commit | `1198ff6fbd66a4de991ad7e8fe1235a452d4b337` (tree `35327c3077ef3d6d5111159668518d960d1467bd`, parent `08dd29d...`) -- the `SA-M13` ASCII-needle repair (`WDD-20260806-010`) plus worklog checkpoint; the certification campaign and every final gate ran on this tree |
| Report-record chain (documentation-only) | first landed as `ea08f2851e8be9951dceb56a1c021ab170de80b8`, which lacked its same-commit workflow-ledger pairing and was therefore reverted by `c38e885be1bffe624919f2350e6fb31c1ec0660e` (`WDD-20260806-011`); the final report commit re-lands the report record paired with that entry's completion line. **Precisely** (`AUD1` `P3-5`): four of the six report files -- the `AUD1` packet, the worklog, the round-log entry, and the digestion entry -- are byte-identical across `ea08f28..ec35b5d`; two are not, and their differences are exactly the disclosure of this repair: `EG_CP_STAGEA_RESULT.md` (this identity row and the `SA-CHK-09` row) and `EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` (the `EV-A13` correction), alongside `WORKFLOW_DESIGN_DECISIONS.md` (`WDD-20260806-011` itself). Nothing else changed.  Every commit above the frozen proof/replay commit `1198ff6...` changes documentation only (`git diff 1198ff6..<final> --name-only` verifies this mechanically), so the exact proof-bearing parent of the report record is the frozen proof/replay commit above.  The final report commit's own hash is reported in the worker terminal response, never embedded here. |

Changed paths across `270d7855..` the frozen proof/replay commit, computed
from Git: `docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md`,
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`,
`docs/internal/DESIGN_DECISIONS.md`, `docs/internal/EG_CP_STAGEA_WORKLOG.md`,
`RMQ.lean`,
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`,
`RMQ/Validation/EGCPStageA.lean`, `scripts/axiom_check.lean`,
`scripts/eg_cp_stagea_replay.ps1`.  The report commit adds only
`docs/internal/EG_CP_STAGEA_RESULT.md`,
`docs/internal/audit_packets/EG_CP_STAGEA_AUD1_PACKET.md`,
`docs/internal/AUDIT_AND_A_DESIGN.md`, `docs/DIGESTION_LOG.md`, the worklog
checkpoint, and the matrix evidence ledger (section 8 appends only).
`scripts/eg_cp_final_falsification_replay.ps1` and
`scripts/gate.ps1` are untouched (base-blob identity verified:
`3420c76c3d232119052b49aa0577f7b1df169afe`).

## 2. The combined proposition, quoted

The capstone theorem is

```
theorem packedReviewerArchitectureCapstone_holds
    (xs : List Int) (left right : Nat) :
    PackedReviewerArchitectureCapstone xs left right
```

whose proposition is the structure (thirty-eight frozen fields, plus field
39 appended by coordinator amendment `CA-20260807-001` after the fresh-blind
audit -- see section 11)
`PackedReviewerArchitectureCapstone (xs : List Int) (left right : Nat) :
Prop` of
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`,
with every field stated over `shape := SuccinctClassic.cartesianShape xs`,
`packedReviewerMemory shape`, and the literal
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right`, and the guard `left < right /\ right <= shape.size` wherever a guard
appears.  The complete field list, byte-frozen in matrix section 1.1 before
implementation and enacted verbatim:

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

The independent expected-type consumer is

```
theorem egcpStageAArchitectureFactsExact
    (xs : List Int) (left right : Nat) :
    EGCPStageAArchitectureFacts xs left right
```

where `EGCPStageAArchitectureFacts` in `RMQ/Validation/EGCPStageA.lean`
restates all thirty-nine field types literally and independently (field
names and full types written out; nothing is derived from the capstone
declaration), discharged by projection from
`packedReviewerArchitectureCapstone_holds`.  The validation root also pins
the exact signatures `egcpStageACapstoneSignature : List Int -> Nat -> Nat ->
Prop := @PackedReviewerArchitectureCapstone`, `egcpStageAWidthSignature :
Nat -> Nat`, `egcpStageAControllerSignature : Nat -> Nat -> Nat ->
PackedReviewerControllerState`, `egcpStageARunSignature : List (List Bool) ->
Nat -> Nat -> Nat -> PackedReviewerRun`, and `egcpStageAMemorySignature :
CartesianShape -> List (List Bool)`; the small-size width literals
`packedReviewerCellWidth 0 = 10`, `1 = 14`, `2 = 14`, `3 = 15`
(kernel-checked); the boundary campaign (empty, singleton, both size-two
shapes, crossover triple `5487/5488/5489`, readiness six
`1023/1024/1025/1329/1330/1331`, four invalid queries on `[7, 3, 3]`, the
duplicate-minimum fixture); and the frozen fixture re-pins
(`egcpStageAHeaderLivenessFixture` `10 -> 37`,
`egcpStageADecisiveCellConnection` at its full literal expected type,
`egcpStageAUnreadCellAcceptPinned`, `egcpStageAInvalidRunExact`,
`egcpStageADuplicateMinimum`, `egcpStageANoSecondRepresentation`,
`egcpStageADeadAddressWidth`).

## 3. Requirement-to-evidence: `EG-CP-A01` .. `EG-CP-A13`

| ID | Requirement (verbatim) | Evidence: theorem/check and composition chain | P / Q / bridge and anti-vacuity outcome | Provenance level | Replay cases (verdict at frozen surface) | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `EG-CP-A01-ONE-OBJECT` | Space, query, trace, and result use the identical `header ++ buildPayload ++ padding` packed memory object | Capstone fields 1-5 (`payload_is_buildPayload` = `buildPayload xs` by `rfl`-bridge; `serialized_header_payload`; `padded_final_padding` with length = `packedReviewerAllocatedBits`; `memory_uniform_builder` `rfl` pin; `run_factorization` `rfl` pin), consumed by `egcpStageAArchitectureFactsExact`; the full chain is result section 2 / matrix section 1.3, ending at `SuccinctClassic.queryTraceResult` | P: every field names the literal `packedReviewerMemory shape` / `packedReviewerRunAgainstMemory ...` terms.  Q: sibling/supplied/prefix-only/reconstructed store.  Same-term domain; attempted via three replay mutations, all REJECT | object identity is definitional (`rfl` pins) | `SA-M01` REJECT @ ReviewerController.lean; `SA-M02` REJECT @ ReviewerMemory.lean; `SA-M03` REJECT @ ReviewerController.lean | CANDIDATE_COMPLETE (worker); coordinator acceptance pending |
| `EG-CP-A02-SPACE` | Complete allocated capacity is `2n + o(n)` | Fields 6-10: `one_cell_width`, `memory_length_arity` (= `packedReviewerCellCount`, header + payload cells + final padding), `allocation_two_n_plus_rho` (`memory.length * w <= 2*n + packedReviewerRho n`), `rho_little_o` (`LittleOLinear packedReviewerRho`), `closed_length`; footprint addresses against `2 ^ w` by field 22 and `egcpStageADeadAddressWidth` | P: bound on allocated cells times width of the probed memory.  Q: serialized-length or sibling-payload bound.  Padding makes them differ; both mutations REJECT | kernel theorems over the counted memory | `SA-M04` REJECT @ ReviewerMemory.lean; `SA-M02` REJECT @ ReviewerMemory.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A03-WIDTH` | One exact query-independent width function satisfies the frozen explicit all-size lower/upper bounds for cells, fields, and addresses | Fields 11-15 (`0 < w`; `n < 2 ^ w`; `w <= 20 * (Nat.log2 (n + 2) + 1)`; header exactly one `w`-cell; `longCount < 2 ^ w /\ sparseCount < 2 ^ w`) + fields 6/22; `egcpStageAWidthSignature : Nat -> Nat`; small sizes pinned kernel-checked: `w(0)=10`, `w(1)=14`, `w(2)=14`, `w(3)=15` | P: one size-only `packedReviewerCellWidth` used by header/cells/addresses/allocation.  Q: value substitution (semantic) or added parameter (structural).  Value substitution REJECTs; parameter family REJECTs via `SA-M14` | kernel theorems; literals kernel-checked | `SA-M05` REJECT @ ReviewerWidth.lean; `SA-M14` REJECT @ ReviewerCapstone.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A04-HEADER-SUFFICIENCY` | All controller geometry is decoded from counted header/probe data | Fields 16-19: `header_cell_zero`, `header_decodes`, `run_opens_with_header`, `header_liveness` (universal second-address movement); fixture `10 -> 37` re-pinned by `egcpStageAHeaderLivenessFixture`; sparse count from the charged three-read K1 prelude (accepted `R2-02` chain) | P: the decoded header value determines a later attempted address, universally, at the trace-position-1 address projection.  Q: header read wrong / mirrored / ignored.  All three mutations REJECT | address-projection inequality (not aggregate-record); universal + pinned instance | `SA-M06` REJECT @ ReviewerControllerProof.lean; `SA-M07` REJECT @ ReviewerController.lean; `SA-M08` REJECT @ ReviewerControllerProof.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A05-PROBE-SEMANTICS` | Every attempted probe is one aligned fixed-width indexed read of the same memory; cell crossings cost multiple probes | Fields 20-25: `memory_only` (reply literally `memory[address]?`), `probes_allocated_and_successful` (in-range totality; invalid trace empty), `address_machine_width` (`< 2 ^ w`), `reply_exact_width`, `ordered_grouping` (`PackedReviewerRunGrouping`, order/multiplicity trace identity), `probe_plan_crossing` (`rfl` pin of the exact one/two-probe conditional) | P: aligned `w`-bit indexed reads with the exact crossing expansion.  Q: swapped crossing order / forged trace.  Both REJECT | event values + occurrence positions + multiplicity by grouping; instruction/pre-state by field 35 and the connection re-pin | `SA-M09` REJECT @ ReviewerProbe.lean; `SA-M10` REJECT @ ReviewerControllerProof.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A06-PROBE-CAP` | Exact derived numeral `C`, preserving order and multiplicity | Fields 26-27: `derived_cap_le_427` plus the structural derivation under the guard (`measure = 1 + 2*preludeRemaining(init) + 2*wholeRemaining(start)`, `= 3`, `= 210`, `measure = 427`); order/multiplicity by field 24; `427` never stored in an input, hypothesis, or precomputed result; upper bound, not attainment | P: cap is the derived measure of the executed run.  Q: stored numeral in the measure arm.  REJECT at the commissioned structural surface | derived from the run's own fuel measure; fixture run issues 68 attempted probes | `SA-M11` REJECT @ ReviewerCapstone.lean (structural, as commissioned) | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A07-CORRECTNESS` | All valid half-open queries return the leftmost reference RMQ answer | Fields 28-29 quantified over every `xs, left, right` by the producer: `guarded_reference_result` through the chain `packedReviewerRunAgainstMemory_eq_lowered -> packedReviewerDriveLogical_210_simulates_packedWholeQueryRun -> packedWholeQueryRun_eq -> packedReviewerPackedReference_eq_public`; `leftmost_tie_universal` via `packedReviewerRunLeftmostTie` (`queryCosted_exact`/`queryCosted_leftmost`/`scanWindow`, `INV-ORACLE-INDEPENDENCE`).  The Stage-F `F09` slice and the duplicate-minimum fixture are witnesses only | P: identical run returns the guarded leftmost reference for every valid query.  Q: offset index / metadata oracle.  Both REJECT | universal kernel theorem; reference side independent | `SA-M12` REJECT @ ReviewerControllerProof.lean; `SA-M16` REJECT @ ReviewerControllerProof.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A08-INVALID-DOMAIN` | Invalid/reversed/empty/out-of-range behavior is stated without weakening A07 | Fields 30-31: `invalid_run_exact` (`terminal = some none`, `failed = false`, `.done none`, `trace = []`) and `invalid_reference_none` (the reference agrees, so the unconditional field 28 shares one guard); boundary instances at empty/singleton/size-two/crossover-triple/readiness-six/four invalid queries/duplicate-minimum, all instantiating the one universal producer | P: invalid endpoints yield the exact `.done none` empty-trace run under the same guard.  Q: fabricated invalid answer / threshold dispatch.  REJECT; thresholds instantiate one quantifier (`egcpStageANoSecondRepresentation` `rfl` pins) | kernel theorems + kernel-checked instances | `SA-M13` REJECT @ ReviewerControllerProof.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A09-UNIFORMITY` | Closed controller has no semantic shape, input list, proof oracle, uncounted advice, or hidden table | Fields 32-34: `controller_exact_input_boundary` (elaborates only at `Nat -> Nat -> Nat -> PackedReviewerControllerState`), `controller_uniform_entry` (`rfl`), `run_factorization` (memory only at the driver), `store_agreement_determinism` (ordered request/reply agreement determines the run -- the cross-shape/store-agreement evidence); proof-free controller state family (accepted `R2-05`) | P: dynamic inputs exactly `n`, endpoints, prior replies.  Q: each forbidden input family.  Signature family REJECTs structurally (`SA-M14`, labeled); semantic pairs REJECT (`SA-M03`, `SA-M07`); value-preserving `SA-M15` REJECTs structurally-honestly | exact-type pins + kernel theorems | `SA-M14` REJECT @ ReviewerCapstone.lean (structural); `SA-M15` REJECT @ ReviewerController.lean (value-preserving, honest label); `SA-M03`, `SA-M07` semantic REJECTs | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A10-NO-ASSUMED-CAPSTONE` | Reachable-state invariant and corruption/nonvacuity theorems show that packed execution, not an assumed answer or shape-generated replay, produces the result | Fields 35-38: `reachable_state_invariant` (base/step/final: every trace position produced by the live driver prefix fold, continuation reproduces terminal/state/suffix -- `packedReviewerDriveAux_decompose` at the literal run); `decisive_cell_liveness` (cell 8: `some 1 -> some 2`, `.terminal` projection); `unread_cell_accept` (cell 4 allocated, never probed, all replacements run-record-equal); `no_metadata_completion` (`SF-M06-BRIDGE`); occurrence chain re-pinned (`egcpStageADecisiveCellConnection`: position 11, `leftSelect`, `entryFirstOffset`, segment 8, pre/post state, continuation to `.done (some 1)`) | P: each next address/reply/state/result produced by packed execution under one invariant.  Q: stored/precomputed result or disconnected replay.  `SA-M16`/`SA-M17`/`SA-M10` REJECT; `SA-A02` ACCEPTs (expected-accept control) | occurrence-indexed with instruction, invocation parameters, and folded pre-state | `SA-M16`, `SA-M17` REJECT; `SA-M10` REJECT; `SA-A02` ACCEPT | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A11-PUBLIC-CONSUMER` | Independent expected-type consumer pins the full combined proposition | `egcpStageACapstoneSignature` + `EGCPStageAArchitectureFacts` (all 38 field types written out literally, never printed/queried from the capstone) + `egcpStageAArchitectureFactsExact`; development probes: weakening the consumer's cap restatement (`427 -> 428`) and the decisive expectation (`some 2 -> some 3`) each broke the build at `RMQ/Validation/EGCPStageA.lean`, byte-restored and SHA-verified | P: the committed consumer pins the entire proposition.  Q: weakened/deleted public conjunct absorbed silently.  Producer weakening REJECTs at the consumer file; certificate weakening REJECTs upstream | committed literal expected types | `SA-M18` REJECT @ ReviewerCapstone.lean; `SA-M19` REJECT @ Validation/EGCPStageA.lean | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A12-REPLAY` | Exact registry, selectors, mutations, deadlines, restoration, and clean-state controls | `scripts/eg_cp_stagea_replay.ps1`: frozen 21-case registry with row/field mappings validated pre-build; selector nonvacuity incl. `-IntegrityProbe` middle-ID controls at the script boundary; evidence-based deadline (clean 1 s / probe 215 s -> 860 s); Windows sleeper self-test; activation needles; SHA256 `finally` restoration; terminal clean tree; inherited Stage-F runner byte-identical (`3420c76c...`); `NAMED-REGRESSION-REALITY` by re-execution and by the added reviewer crossing case | P: every claimed case replays with expected verdict at its named surface.  Q: skipped/mis-surfaced/vacuous case.  Registry integrity + activation + surface matching fail closed | committed versioned runner | full campaign receipts in section 5 | CANDIDATE_COMPLETE (worker) |
| `EG-CP-A13-CAPSTONE-AUDIT` | Fresh-blind exact-commit audit and coordinator reconstruction pass | This worker produced only the verdict-free packet `docs/internal/audit_packets/EG_CP_STAGEA_AUD1_PACKET.md` (candidate lineage, theorem/type inventory, matrix/registry, composition chain, receipts, open questions).  No auditor prompt, no simulated verdict, result report withheld from the packet | not a worker row | -- | -- | **OPEN / AUDITOR_OWNED** |

## 4. Inherited invariants and harness contracts

| ID | Evidence and disposition |
| --- | --- |
| `INV-VALUE-DEPENDENCY` | Value/address projections only: field 36 (`.terminal` inequality), field 19 (trace-position-1 address inequality), field 38 (no metadata completion), field 35 (terminal reproduced from consumed replies).  No enclosing-record inequality is cited anywhere.  `SA-M06`/`SA-M08`/`SA-M12`/`SA-M16`/`SA-M17` REJECT. |
| `INV-SEMANTIC-NONVACUITY` | The liveness propositions are inequalities of computed projections of actual runs; the grouping is a trace identity of the executed run; no predicate is defined `True`.  `SA-M10` (forged trace) and `SA-M17` (neutralized decisive mutant -- the corruption evidence cannot be vacuous) REJECT. |
| `INV-STORE-AGREEMENT` | Field 34 (`packedReviewerRunAgainstMemory_eq_of_agree` at the literal run); the unread-cell control (field 37) is its expected-ACCEPT instance, and `SA-A02` replays it. |
| `INV-READ-BACKING` | Fields 20-21 back every reply literally and positionally (`memory[event.request.address]?`); field 35 gives the occurrence-indexed form via `run.trace[i]?`.  `SA-M01`/`SA-M15` REJECT. |
| `INV-PUBLIC-COMPOSITION` | One structure, one binder triple, identical `memory`/`run`/`controller`/`w` terms in every field, one guard wherever a guard appears, and the invalid case consistent by field 31.  `SA-M02`/`SA-M18`/`SA-M19` REJECT. |
| `INV-MUTATION-REPRODUCIBILITY` | The versioned runner replays all 21 frozen cases with expected verdicts, named failing surfaces, activation needles, SHA256 restoration, and terminal clean tree; full-mode receipts in section 5.  Report prose cites no unreplayed mutation. |
| `INV-CATEGORY-SEPARATION` | Result section 7 table: payload bits / allocated bits / proof-only fields / model probes (427 cap) / logical fuel (210) / Lean wall-clock, each kept distinct; allocated bits never conflated with meaningful bits; no attainment claim. |
| `REPLAY-EXACT-REGISTRY` | `Test-RegistryIntegrity` validates count 21, ascending orders, unique IDs, mapped verdicts, exact 2/19 totals, and nonempty row/field mappings before any build, on every invocation. |
| `REPLAY-SELECTOR-NONVACUITY` | Script-boundary receipts: unknown/whitespace/empty (external binding fail-closed exit 1; in-process own-check exit 2) selectors rejected; valid selector ran exactly one case; omission = full mode; `-IntegrityProbe OmitMiddle`/`DuplicateMiddle` rejected the corrupted registry copies (count/order/duplicate/total diagnostics) while the frozen registry passed. |
| `REPLAY-SUBPROCESS-DEADLINE` | Deadline = max(1, 215) * 4 = 860 s from measured builds; timeout is failure; `taskkill /T /F` tree termination; detached-grandchild sleeper self-test PASS on Windows (the required gate platform), pid-verified; restoration in `finally` SHA-verified; non-Windows branch carried but explicitly uncertified. |
| `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | Strict-UTF-8 checker (scratchpad-run, not committed) over the freeze blob `719c01d1e182d3288eebc9427bb21f16b4d414f7` vs the candidate: 46 frozen row IDs, 0 missing, 0 duplicated, 0 changed, 0 added in frozen sections; mojibake scan scoped outside backtick-quoted examples; both negative controls (injected row edit, injected mojibake) fire. |
| `NAMED-REGRESSION-REALITY` | Every inherited body re-executed by this campaign against the Stage-A surface with its frozen first-failing file re-observed; the flat-universe `M09` legacy case was NOT reused for the reviewer plan -- the matching reviewer case `SA-M09-CROSSING-SWAP` was added instead. |

## 5. Replay campaign receipts

**Certification run (the one full-mode certification, frozen proof/replay
tree `1198ff6`):** `FULL MODE PASS`, exit 0, **1100 s**; clean surface build
5 s; mutated-chain calibration probe 156 s; per-case deadline 624 s;
descendant-termination self-test PASS; registry integrity 21 ordered
entries, 2 ACCEPT / 19 REJECT, every entry carrying its frozen row and
field/object mapping; **21 of 21 cases as commissioned, 0 target-absent**;
20 SHA256-verified restorations (every patch case); terminal
`git status --porcelain` clean.

| # | ID | Verdict | Frozen first-failing surface reached |
| --- | --- | --- | --- |
| 1 | `SA-A01-PRODUCTION-EXPECTED-ACCEPT` | ACCEPT | (unchanged candidate builds) |
| 2 | `SA-A02-UNREAD-CELL-EXPECTED-ACCEPT` | ACCEPT | (frozen replacement-value patch; whole surface elaborates via the agreement route) |
| 3 | `SA-M01-SIBLING-STORE` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 4 | `SA-M02-SIBLING-PAYLOAD` | REJECT | `PackedCellProbe/ReviewerMemory.lean` |
| 5 | `SA-M03-CANONICAL-SHAPE-BY-N` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 6 | `SA-M04-ALLOCATION-HEADER-CELL-DROP` | REJECT | `PackedCellProbe/ReviewerMemory.lean` |
| 7 | `SA-M05-WIDTH-SUBSTITUTION` | REJECT | `PackedCellProbe/ReviewerWidth.lean` |
| 8 | `SA-M06-WRONG-LONG-COUNT` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 9 | `SA-M07-HOST-LONG-COUNT-MIRROR` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 10 | `SA-M08-LONG-COUNT-IGNORED` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 11 | `SA-M09-CROSSING-SWAP` | REJECT | `PackedCellProbe/ReviewerProbe.lean` |
| 12 | `SA-M10-DISCONNECTED-TRACE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 13 | `SA-M11-FORGED-PROBE-CAP` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (derived-measure consumer) |
| 14 | `SA-M12-RESULT-OFFSET` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 15 | `SA-M13-INVALID-GUARD-RESULT` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 16 | `SA-M14-SHAPE-PARAMETER` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (exact-type input boundary) |
| 17 | `SA-M15-HIDDEN-UNCOUNTED-TABLE` | REJECT | `PackedCellProbe/ReviewerController.lean` |
| 18 | `SA-M16-ANSWER-ORACLE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` |
| 19 | `SA-M17-DECISIVE-MUTANT-NEUTRALIZED` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` |
| 20 | `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` (certificate-projecting producer) |
| 21 | `SA-M19-ARCHITECTURE-PROPOSITION-WEAKENING` | REJECT | `RMQ/Validation/EGCPStageA.lean` (the committed Stage-A consumer) |

Activation checks passed on every semantic mutant (`WDD-20260805-002`
needles present and used).  Labels as frozen: `SA-M11`/`SA-M14` structural
(the commissioned structural surfaces), `SA-M15` value-preserving but
structurally honest (audited `P3` disposition), all others semantic.

**Diagnostic run (retained as evidence, implementation tree `08dd29d`,
1400 s, deadline 780 s from a 195 s probe):** 20 of 21 as commissioned at
the same surfaces; one defect, `SA-M13` `ANCHOR-DRIFT` -- the runner's own
needle contained the Unicode conjunction and Windows PowerShell 5.1 decodes
a BOM-free script as ANSI.  Repaired by the ASCII-only anchor of
`WDD-20260806-010` (frozen registry rows untouched -- they freeze mutation
intent, verdict, surface, and mappings, not needle bytes); the repaired case
was verified alone (REJECT as commissioned at
`PackedCellProbe/ReviewerControllerProof.lean`, activation check passed,
362 s) before the certification rerun.  The Lean bytes of the two trees are
identical; only the runner and two ledgers differ.

**Boundary controls (script-boundary receipts):** unknown selector exit 2;
external empty argument fails closed at parameter binding (exit 1, before
any action) and the in-process explicitly bound empty and whitespace
selectors exit 2 at the harness's own check; bogus `-IntegrityProbe` exit 2;
`-Case` + `-IntegrityProbe` combined exit 2; `-IntegrityProbe OmitMiddle`
and `DuplicateMiddle` reject the corrupted in-memory registry copies
(count/order/duplicate/verdict-total diagnostics) while the frozen registry
passes, exit 0 each; Windows `-SelfTestOnly` PASS (registry integrity plus
pid-verified root-and-grandchild termination).  Exact selector `SA-A01` run:
ACCEPT, exit 0, 421 s (calibration 1 s clean / 215 s probe, deadline 860 s,
self-test PASS, terminal clean).

## 6. Verification command ledger

| ID | Command | Tree | Outcome / duration |
| --- | --- | --- | --- |
| `SA-CHK-00` | `project_skill_preflight.ps1` (governance `f0c7232a...`, required `rmq-proof-sprint`, runtime catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`) | base `270d7855`, clean | PASS (all four skill sets equal; `required_mode=role-skills`) |
| `SA-CHK-01` | focused builds during development; final `lake build RMQ.Validation.EGCPStageA` | dev trees, then frozen `1198ff6` | Capstone cold chain 1060 s (one proof goal repaired: the `@[simp]` size lemma broke a guard `simp`, replaced by `rw [if_pos hvalid]`), then 15 s warm; validation root 6 s; final receipt on the frozen tree in section 6 text |
| `SA-CHK-02` | `lake build RMQ RMQUnionFind` | frozen `1198ff6` | PASS exit 0, 198 s (`lake build RMQ RMQUnionFind`; preceded by the focused surface receipt exit 0, 8 s) |
| `SA-CHK-03` | `lake env lean scripts/axiom_check.lean` | frozen `1198ff6` | PASS exit 0, 176 s: all four curated Stage-A entries (`packedReviewerArchitectureCapstone_holds`, `packedReviewerRunLeftmostTie`, `packedReviewerRunReachableInvariant`, `Validation.egcpStageAArchitectureFactsExact`) depend only on `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`/`ofReduceBool`/`trustCompiler` occurrences in the printed inventory |
| `SA-CHK-04` | replay: startup/shape smoke + exact `SA-A01` selector, then the full 21-case registry | `08dd29d` (diagnostic), `1198ff6` (certification) | selector ACCEPT 421 s; diagnostic 1400 s (20/21 + runner defect); certification `FULL MODE PASS` exit 0, 1100 s, 21/21 |
| `SA-CHK-05` | runner boundary controls (selectors, integrity probes, self-test) | `08dd29d`/`1198ff6` | all as expected (replay section above) |
| `SA-CHK-06` | forbidden-token scan over `RMQ` and `lakefile.toml` | frozen `1198ff6`, quiet | zero matches (rg exit 1) |
| `SA-CHK-07` | native-shortcut scan over `RMQ` | frozen `1198ff6`, quiet | zero matches (rg exit 1) |
| `SA-CHK-08` | `git diff --check` (working tree) and `git diff --check 270d7855..HEAD` | frozen `1198ff6`, then after the report commit | clean (exit 0) on both the working tree and the committed range at the frozen candidate; rerun after the report commit with receipts in the worker terminal response |
| `SA-CHK-09` | `design_decision_check.ps1 -Strict -Base 270d7855...` (full range) plus per-commit `-Base HEAD~1` at every commit | each exact commit | per-commit: PASS at `f4107cd` (neutral-only), `08dd29d` (8 files, 4 code / 2 workflow / 2 neutral), `1198ff6` (3 files, 0 code / 1 workflow / 2 neutral), `c38e885` (7 files, 0 code / 3 workflow / 4 neutral), and the final report commit (receipt in the worker terminal response).  The first report landing `ea08f28` FAILED this per-commit check (workflow-sensitive report surfaces without a same-commit workflow-ledger change) and was repaired by the paired revert-and-reland of `WDD-20260806-011` -- not excused.  Full range at the frozen candidate: PASS exit 0, `DESIGN-CHECK: checked 9 changed files (4 code, 2 workflow, 4 neutral)`; full range rerun after the final report commit: receipt in the worker terminal response |
| `SA-CHK-10` | `claim_drift_scan.ps1 -Strict` | frozen `1198ff6`, rerun after the report commit | PASS exit 0: `CLAIM-DRIFT: scan complete (1525 hits, 0 strict failures)`; rerun after the report commit with receipts in the worker terminal response |
| `SA-CHK-11` | strict-UTF-8 frozen-row byte-integrity of the matrix vs the freeze blob, with negative controls; strict UTF-8 decode of changed docs | freeze `f4107cd` vs candidate | 46/46 row IDs byte-identical, 0 missing/duplicated/changed/added-in-frozen-sections; injected-row-edit and injected-mojibake negative controls both fire; rerun after the report commit: receipts in the worker terminal response |
| `SA-CHK-12` | base-blob identity of `scripts/eg_cp_final_falsification_replay.ps1` | any | byte-identical (blob `3420c76c3d232119052b49aa0577f7b1df169afe`); its inherited frozen registry was therefore NOT rerun (conditional not triggered) |
| `SA-CHK-13` | M03-style consumer probes outside Git (cap `427 -> 428`; decisive `some 2 -> some 3`) | dev tree `08dd29d` bytes | both FAIL at `RMQ/Validation/EGCPStageA.lean` as required; byte restoration SHA256-verified; clean rebuild green |
| `SA-CHK-14` | aggregate `scripts/gate.ps1` | -- | skipped as frozen: every changed surface and acceptance row is owned by `SA-CHK-01`..`SA-CHK-12`; the matrix did not freeze the aggregate as owner and it is not authorized for editing |

Heavy-process receipts: one heavy Lean/Lake process at a time throughout;
`Global\RMQHeavyVerification` acquired around every multi-minute command;
the only wrapper anomaly was the first cold chain build finishing at 1060 s
under a background wrapper (child completed; no duplicate launched).  The
early hygiene/diff preview that ran concurrently with the selector's
calibration probe was discarded and re-run on the quiet frozen tree (the
receipts above are the quiet-tree runs).

## 7. Category separation (`INV-CATEGORY-SEPARATION`)

| Category | Value here | Never conflated with |
| --- | --- | --- |
| Logical payload bits | `SuccinctClassic.buildPayload xs`, length `<= 2n + o(n)` | allocated capacity |
| Allocated bits | `(packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <= 2*n + packedReviewerRho n`, counting header cell, every payload cell, and final padding at full width | meaningful/logical bits |
| Proof-only fields | none on the reviewer path: the controller state family is proof-free; proof-only theorems certify but never choose answers, routes, or addresses | answers or routing |
| Model probes | `run.trace.length <= 427` attempted physical probes; the fixture run issues 68; `427` is an upper bound derived from the run's own fuel measure (`1 + 2*3 + 2*210`), not an attained count (`B7-UPPER-BOUND-IS-NOT-ATTAINMENT`) | wall-clock or Lean runtime |
| Logical fuel | `210` bounds logical attempts, not exact reads (`DD-20260805-075`); `3` is the charged sparse-prelude budget; `1` is the header probe | physical probe counts (the physical bound is separate: at most two probes per logical word) |
| Lean runtime | build/replay durations recorded in the ledger as engineering data | any theorem claim |

## 8. Standing dispositions restated

- **K1 survived; K2 unused; K0 not selected.** The one-cell header plus the
  charged three-read prelude recovers both decoded counts all-size
  (`DD-20260805-071`); no `sparseCount` header cell exists, and the
  self-delimiting bootstrap remains a coordinator flip.  The Stage-A capstone
  quantifies over all `xs` with no stride, cutoff, sampled-size, readiness,
  or compatibility hypothesis.
- **Internal padding and sibling layouts remain rejected.** The one accepted
  object is the final-cell-padded `header ++ buildPayload ++ padding`
  reviewer memory; `SA-M02-SIBLING-PAYLOAD` and `SA-M01-SIBLING-STORE`
  re-certify the rejection on this campaign.
- **The historical B3 small-step route remains superseded** as the primary
  route; nothing from it is smuggled into the packed controller.
- **`SA-M15-HIDDEN-UNCOUNTED-TABLE` (M13) remains a value-preserving but
  structurally honest mutation**, exactly as audited (`P3` disposition of the
  Stage-F fresh-blind report); no stronger semantic-mutation claim is made,
  and its row is paired with the semantic rejections `SA-M03` and `SA-M07`.
- **`SA-M16-ANSWER-ORACLE` (M06) is metadata-derived**; the checked
  `SF-M06-BRIDGE` (`packedReviewerNoMetadataCompletion`, capstone field 38)
  covers the reference-oracle direction, and no document describes `M06`
  alone as having refuted a literal reference-semantics oracle.
- **Windows-only deadline/process-tree certification.** The required gate
  platform for this task is Windows; the descendant sleeper self-test passed
  there.  The non-Windows branch of `Stop-ProcessTree` is carried but
  explicitly uncertified here -- a stated limitation, not cross-platform
  evidence.
- **`427` and `210` wording.** `427` is the derived upper bound on attempted
  physical probes; `210` is logical fuel; neither is an exact read count, a
  word-RAM time bound, or an attainment claim.

## 9. Proof digestion

**What changed conceptually.** Stage F ended with feasibility: the packed
reviewer machine exists, is space-accounted, and answers one fixture
correctly with all its parts proved separately.  Stage A's change is
consolidation into one public object: a single thirty-nine-field
proposition, quantified over every input list and every endpoint pair, in
which the same literal `header ++ buildPayload ++ padding` memory carries the
allocation bound, the width bounds, the header decoding and its liveness, the
aligned probe semantics with crossing expansion, the derived `427` cap, the
guarded leftmost correctness with a universal leftmost-tie connection, the
exact invalid-domain behavior, the closed controller boundary, and the
reachable-state invariant with the frozen corruption/unread controls -- plus
one committed consumer that restates every field literally, so no conjunct
can be weakened or swapped without a build failure at a named file.

**What it means in plain English.** For any integer list, build one packed
bit-array (a one-cell header, the canonical payload, padding to a whole
cell).  A fixed controller that sees only the length, the two query
endpoints, and the words its probes return answers any valid range-minimum
query with the leftmost minimum's index, using at most 427 probes into that
one array, whose total size is 2n plus a checked lower-order term.  Invalid
queries return "no answer" without probing at all.  Nothing else -- no shape,
no list, no table, no oracle -- feeds the controller, and mutating what it
actually read changes its answer while mutating an unread cell changes
nothing.

**Live assumptions and model boundaries.** The claim is cell-probe: probes
are charged, computation between probes is free, and `427` bounds attempted
probes -- it is not word-RAM instruction time, not preprocessing time, and
not a measured-runtime claim.  The cost model is the project's charged-event
model; the trust base is Lean/Std plus `omega` (Mathlib-free), and the
curated axiom inventory pins every new public theorem to
`[propext, Classical.choice, Quot.sound]`.  The `o(n)` envelope is proved
but loose; tightness is not claimed.  `S1` bit-addressed probe semantics and
`V1` remain open downstream nodes.

**Downstream consumer.** The independent `EG-CP-A13` fresh-blind audit of
this exact candidate lineage, followed by coordinator reconstruction; only
after those may public-claim synchronization, `S1`, and `V1` proceed.

**What a skeptical graduate student should ask next.** Whether the
thirty-nine conjuncts are the RIGHT closure of "architecture acceptance" --
specifically, whether any reviewer-facing property of the packed machine is
true but absent from the combined proposition (the audit's reconstruction
question), and whether the `o(n)` envelope and the `427` cap are tight
enough to survive comparison with Fischer's constants once `S1` fixes
bit-level probe accounting.

## 10. Lifecycle request

Requested disposition: commission the fresh-blind
`EG-CP-A13-CAPSTONE-AUDIT` against the exact candidate proof/report lineage
identified in section 1, followed by coordinator reconstruction if and only
if the audit is clean.

---

## 11. Post-audit coordinator repair round (2026-08-07)

This section is appended after the fresh-blind audit of
`ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23`. It does not restate the worker
status above, which stood at the audited commit and stands now.

**Audit.** `EG-CP-STAGEA-AUD1`, fresh-blind report-only, recommendation
**merge-ready with follow-up**, no `P0`, no `P1`, one `P2`, five `P3`. Report
commit `60827a13d38de0a74fc2ae861c5526deae012ff2`. Every finding was
independently reproduced by the coordinator before disposition.

**Repairs landed on top of the audited candidate.**

| Finding | Disposition |
| --- | --- |
| `P2-1` (`ea08f28` fails the per-commit design gate at its own parent) | **Squash integration** (`WDD-20260807-012`). Tree byte-identical; `main` receives one passing commit; branch history preserved because `ea08f28` is in the parent chain of both the audited candidate and the audit report. Owner authority required; not executed here. |
| `P3-1` (disclosure absent from the auditor-facing packet) | **Fixed.** The packet's `SA-CHK-09` receipt now scopes its per-commit claim to the frozen candidate and states the `ea08f28` exception. |
| `P3-2` (`SA-M04`/`SA-M09`/`SA-M18` labelled semantic, no activation needle) | **Fixed.** All three declare needles; the only needle-less entries are `SA-A01` (patches nothing) and the two frozen as structural. No frozen registry row changed. |
| `P3-3` (no conjunct says a valid query returns an index) | **Fixed by amendment `CA-20260807-001`**: field 39 `valid_answer_is_index`, producer `packedReviewerValidRunAnswersIndex` (`DD-20260807-080`). |
| `P3-4` (`-Case ''` exits 1 at the PowerShell binder, not the frozen 2) | **Recorded.** Frozen cell cannot be edited; every selector form still fails closed before any build. Read the cell with this qualification. |
| `P3-5` ("re-landed identically" imprecise) | **Fixed.** Section 1's identity row now names exactly which four of six report files are byte-identical and which two differ, and why. |

**The added conjunct.** Field 39, appended so that all 38 audited fields are
byte-unchanged:

```
valid_answer_is_index :
  let shape := SuccinctClassic.cartesianShape xs
  left < right -> right <= shape.size ->
    ∃ index,
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).terminal = some (some index) /\
        (SuccinctClassic.queryTraceResult xs left right).value = some index /\
        LeftmostArgMin xs left right index
```

It closes the asymmetry the audit identified: the invalid domain already had
`invalid_reference_none` (field 31), while the valid domain had only an
equality to the reference and a conditional tie statement. `EG-CP-A07` is now
self-contained rather than closed by composition with a theorem outside the
proposition. The index comes from `SuccinctClassic.queryCosted_exact` and
`scanWindow` — the independent specification, not the implementation under
test.

**Re-certification on the repaired tree.** The repair changes Lean, so no
check was inherited from the audited commit. Receipts are in the matrix
section-8 ledger and summarized in the terminal response for this round.

**Unchanged by this round:** `EG-CP-A13` remains the coordinator's acceptance
decision; architecture acceptance, integration, public-claim synchronization,
`S1`, and `V1` remain open and unclaimed. `427` remains an upper bound on
attempted probes with no attainment claim; `210` remains logical fuel.

**Re-certification receipts** (repair commit
`a8d2a5c2881564abd85d651041f7d9953c4054f0`, nothing inherited): focused build
exit 0 (9 s); `lake build RMQ RMQUnionFind` exit 0; curated axiom inventory
exit 0 (176 s) with zero forbidden axioms and field 39's consumer on the
standard axioms; the full 21-case campaign **`FULL MODE PASS`, exit 0,
1214 s**, 21/21 as commissioned with 0 target-absent, 20 SHA256-verified
restorations and a clean terminal tree, with `SA-M04`/`SA-M09`/`SA-M18` now
logging their activation checks; hygiene and native scans clean; both
`git diff --check` runs clean; strict design check PASS (full range and
per-commit); strict claim drift PASS (1531 hits, 0 strict failures); and
frozen-row byte integrity **46/46 identical to the freeze blob** with both
negative controls firing -- the mechanical proof that the amendment disturbed
no audited row.

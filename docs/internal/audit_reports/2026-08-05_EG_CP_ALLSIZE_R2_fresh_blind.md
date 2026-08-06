# (EG-CP-ALLSIZE-AUD1) Fresh-blind audit of the repaired all-size reviewer machine

## 1. Scope

| Item | Value |
| --- | --- |
| Mode | Fresh blind, report-only. Reconstruction preceded any read of the worker result report. |
| Auditor | `EG-CP-ALLSIZE-AUD1` (fresh session, isolated worktree, no worker transcript). |
| Exact base | `6bf28dee32c96da4705b139959fd35e4a782bac4` (tree `4d173458db3e1ad33186a2f843ee7dd5cbd87d97`). |
| Exact target | `a0a0f92b8f9081ee59797affb5045952d9e39fbf` (report-only child of frozen repair `368b828e0711dfd10a04ca90eb19c7b0d6ccfd13`, tree `730a8746240bdf6f705d67f9283f6d9db8f25123`; proof-bearing ancestor `5bca709ad64fb4d8971db76c75da2baa24b5b214`, tree `cc75bcb8b334d2de39007a4213affa0a38deafd7`). |
| Branch audited | `codex/eg-cp-allsize-reviewer-machine-r1` (41 commits above base). |
| Audit worktree | fresh isolated checkout of the exact target; report branch `audit/eg-cp-allsize-aud1-fresh-blind`; only this report file added. |
| Governance | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`, verified ancestor of the target. `scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a... -AllowNoRequiredSkills -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"`: PASS, `required_mode=explicit-no-role`, checkout/working/runtime catalogs all equal. No proof or prompt-authoring role skill was substituted for the audit-worker role. |
| Acceptance criteria | The frozen coordinator amendment `EG-CP-ALLSIZE-R1` (`docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md` section 7): rows `R2-01`..`R2-10`, inherited rows `R2-INHERITED-FG-02/04/05/06/07/08/09/10`, the fifteen inherited invariant rows of section 7.3, ledger `R2-CHK-00`..`R2-CHK-12`, deferral boundary 7.5, and the `R2R1` repair addendum (section 8). |
| Out of local scope | `FG-11`, full `FG-12` registry completion, `FG-14`, `FG-15`, the full EG-CP node, public-claim synchronization, `S1`, `V1`. Nothing in this report accepts or closes any of those. |

## 2. Verdict

**LOCAL_RUNG_ACCEPTABLE** for `EG-CP-ALLSIZE-R1` including the `R2R1` repair.

Every frozen `R2-*` requirement, every inherited invariant obligation scoped to
this rung, and every `R2R1` repair obligation is discharged by checked theorems,
exact-type consumers, or replayed mutations that this audit reproduced
independently on the exact target. No P0, P1, or P2 finding survived. The
verdict concerns only the local rung; coordinator acceptance, the deferred
full-node rows, and public synchronization remain open exactly as the frozen
matrix records them.

## 3. Independent reconstruction (performed blind, before the result report)

All items below were reconstructed from the frozen matrix and source only; the
worker result report was opened afterwards and checked against them.

1. **Frozen IDs.** `R2-01`..`R2-10` enumerated verbatim from section 7.1;
   inherited FG rows literally present in the amendment: `FG-02`, `FG-04`,
   `FG-05`, `FG-06`, `FG-07`, `FG-08`, `FG-09`, `FG-10` (section 7.2);
   inherited invariant rows (section 7.3, fifteen): `INV-ADDRESS-WIDTH`,
   `INV-ALL-SIZE`, `INV-GLOBAL-PHYSICAL-MACHINE`, `INV-NO-SYNTHETIC`,
   `INV-ORACLE-INDEPENDENCE`, `INV-PROGRAM-ACCOUNTING`, `INV-PROOF-SEPARATION`,
   `INV-READ-BACKING`, `INV-STORE-AGREEMENT`, `INV-STORE-IDENTITY`,
   `INV-TRACE-EXECUTION`, `INV-VALIDATION-REACH`, `INV-WIDTH-SCALING`,
   `INV-WORD-WIDTH`, `INV-VALUE-DEPENDENCY`.
2. **Object chain.** `SuccinctClassic.buildPayload xs` is definitionally
   `concreteBPNativeSuccinctRMQCanonicalReviewerPayload (cartesianShape xs)`
   (`RMQ/Core/SuccinctRMQClassic.lean:170`, pre-existing);
   `packedReviewerPayloadBits` equals it (`egcpAllSizeConsumedPayloadIdentity`,
   `egcpAllSizeConsumedPayloadIsBuildPayload`); serialization is one header
   cell (`natToBitsLE` of `longCount` at `packedReviewerCellWidth`) prepended
   to the payload; padding is only the final allocation suffix; memory is the
   exact-width chunking (`ReviewerMemory.lean:54-149`); the run is
   `packedReviewerRunAgainstMemory`, whose driver alone indexes memory
   (`ReviewerController.lean:311-347`); the logical simulation target
   `packedWholeQueryRun` and the guarded reference
   `SuccinctClassic.queryTraceResult` (guarded by `withValidRange`, invalid
   ranges return `pure none`) both predate the branch and are unchanged by it.
3. **K1.** Exactly three charged prelude reads, in order `.rankSuper`,
   `.rankBlock`, `.flagWord` (`ReviewerSparsePrelude.lean:408`, pinned by an
   `rfl` consumer), reading `selectSparseRankSuperTrue`,
   `selectSparseRankBlockTrue`, `selectSparseFlagBits`; the decoded count is
   `(super + block + in-word flag rank) * packedSelectLocalStride n`, a pure
   function of the three replies and `n`. `packedReviewerSparseCount` is the
   length of the actual sparse-exception entry list, i.e. content-derived, so
   the recovery is not vacuous. Prelude addresses are sparse-count-independent
   and the actual controller executes the same three plans before entering the
   whole-query phase with fuel 210 (`egcpAllSizeActualControllerPrelude`).
4. **Segment 20.** Exactly eight ragged components -- `baseline`, `minRel`,
   `maxRel`, `argOffset`, `localOffset`, `globalBlock`, `localLevel`,
   `globalLevel` (`ReviewerInteriorRead.lean:29`; exhaustive `cases` consumer)
   -- with per-entry chunking, chunk/entry coordinates, short final words
   (`readWidth = min (width - chunk * wordSize) wordSize`), word order via
   component word prefixes, canonical-word slices, physical decode against
   `packedReviewerMemory`, and the aggregate exactness
   `packedReviewerInteriorRead ... = globalReadStore.readWord? 20 index`
   including the `none` cases.
5. **Controller and driver.** The controller state carries only `Nat`s,
   reply lists, and protocol sub-states whose transitive field types are
   `Nat`s, reply lists, and one four-`Nat` decoded entry record; there is no
   shape, list, store, proof, or oracle field. `consumeReply` is a pure
   function of state and reply; a missing reply is terminal failure. Only the
   external driver receives the cell array and every recorded reply is the
   literal `memory[address]?` lookup. Ordered reply agreement determines the
   whole run object.
6. **Ordered lowering.** The actual valid run decomposes as header trace ++
   K1 trace ++ lowered whole-query trace; occurrence positions, ordinals,
   plan lengths (crossing multiplicity), producing instruction/site, and
   invocation parameters are retained by position-indexed theorems, and the
   grouping equality is stated on the actual run's trace.
7. **Totality, width, cap.** Every trace event of the canonical run carries a
   successful reply; every attempted address is below the cell count and below
   `2 ^ packedReviewerCellWidth n`; request operands, control tags, phase
   tags, reply lengths, and reply values are bounded by the one declared
   width, which is itself logarithmically bounded. The physical budget is the
   structural measure `1 + 2*3 + 2*210 = 427` at the header state (the select
   tower starts at 35 = 4 + 31 remaining logical reads, plus 175; 35 + 175 =
   210), the literal `427` first appears in theorems proved after the run
   definition, and `packedReviewerSelectStart` contains an open-term `if`, so
   the structural `rfl` consumer cannot be satisfied by a stored literal --
   the audit verified this mechanism directly against the `M08` mutant body.
8. **210 fuel versus attempts.** 210 is driver fuel bounding logical
   attempts; zero-cell attempts advance without physical events; the repaired
   docstring and `DD-20260805-075` state exactly this, and nothing in the
   tree describes 210 as an exact read count.
9. **Axiom inventory.** Exactly six permanent curated entries appended at
   `scripts/axiom_check.lean:1206-1211` for the payload identity, allocated
   space, little-o residual, 427 trace cap, public outcome, and public
   certificate.
10. **Replay mutant bodies.** The `R2-ALLSIZE` stage is the literal ordered
    view `M03, M05, M06, M07, M08, M11, M12` over the unchanged sixteen-entry
    frozen registry. Each patched body was read and classified before replay:
    `M05` re-binds the driver to a sibling store `memory ++ [[]]`; `M06`
    discards the computed completion value for a metadata-derived `some n`
    (the frozen `R2-06` challenge's "precomputed semantic result"); `M07`
    replaces the expected physical trace's valid branch with a forged empty
    trace while leaving the result path untouched; `M11` serializes a sibling
    execution payload `payload ++ [false]` behind the pinned public object;
    `M08` replaces the derived structural measure arm with a stored literal;
    `M12` weakens the public certificate theorem's type to a trivial
    proposition. Each of `M05`/`M06`/`M07`/`M11` performs its frozen semantic
    substitution inside a load-bearing definition body -- none is an unused
    parameter or an arity-only edit -- and the runner's activation check
    (needle presence including the usage site) mechanically excludes the
    arity-only failure mode that `R2R1` repaired. `M03` alone remains a
    signature mutation, which is its commissioned content (the exact-signature
    pin of `R2-05`): its defaulted `Option` shape argument leaves every
    library use elaborating so the failure lands exactly at the
    `@packedReviewerController` expected-type pin in the validation root.

## 4. Commands run and outcomes (this audit, exact target, one heavy process at a time)

| Command | Outcome |
| --- | --- |
| Project-skill preflight (explicit no-role, governance `f0c7232a...`) | PASS. |
| `lake build RMQ.Validation.EGCPFinalFalsification` (cold isolated tree) | PASS, exit 0, 16 m 12 s. |
| `lake build RMQ` | PASS, exit 0, 4 m 47 s. |
| `lake env lean scripts/axiom_check.lean` | PASS, exit 0, 3 m 30 s. Independently reproduced receipts: all six reviewer entries depend on exactly `[propext, Classical.choice, Quot.sound]`, except the 427 trace-cap theorem on `[propext, Quot.sound]` alone. No `sorryAx`, no native-reduction axiom. |
| Hygiene scan (forbidden tokens / Mathlib import over `RMQ`, `lakefile.toml`) | Zero matches. |
| `native_decide` / `Lean.ofReduceBool` scan over `RMQ` | Zero matches. |
| `scripts/claim_drift_scan.ps1 -Strict` | PASS: 1513 hits, 0 strict failures. |
| `scripts/design_decision_check.ps1 -Strict -Base 6bf28dee...` | PASS: 32 changed files (26 code, 4 workflow, 3 neutral). |
| `git diff --check` (committed range `6bf28dee..a0a0f92` and working tree) | Clean. |
| Frozen-row integrity: matrix diff against exact base | Single appended hunk, +175/-0; every historical row byte-identical; strict UTF-8, no BOM, no mojibake (also checked for the result report, worklog, replay script, axiom script). |
| `scripts/eg_cp_final_falsification_replay.ps1 -Stage R2-ALLSIZE` (exactly once) | **PASS, exit 0**: registry integrity OK (16 ordered entries, 2 ACCEPT / 14 REJECT mapping), measured deadline (300 s floor), descendant-termination self-test PASS, activation checks passed for `M05`/`M06`/`M07`/`M11` (2 needles each), all seven commissioned REJECTs at their commissioned surfaces (`M03` and `M08` and `M12` at `Validation/EGCPFinalFalsification.lean`; `M05` at `ReviewerController.lean`; `M06` and `M07` at `ReviewerControllerProof.lean`; `M11` at `ReviewerMemory.lean`), SHA256-verified byte restoration per case, terminal `git status --porcelain` empty. Audit-side re-verification of cleanliness after the run: clean. |
| Aggregate `gate.ps1` | Skipped, matching ledger row `R2-CHK-12`: every changed surface is owned by the commands above; a duplicate aggregate run on the unchanged tree adds no coverage. |

## 5. Findings

No P0. No P1. No P2.

- **P3-1 (frozen contract, coordinator-side).** Matrix section 7.2 cites the
  original rows by names that do not exist in section 1:
  `FG-08-PHYSICAL-CODEC-AND-CAP`, `FG-09-PROBE-TOTALITY-AND-SAME-OBJECT-CORRECTNESS`,
  and `FG-10-ANTI-VACUITY` versus the actual `FG-08-PHYSICAL-LOWERING`,
  `FG-09-TOTALITY-AND-CAP`, and `FG-10-SAME-RUN-CORRECTNESS`. The numeric IDs
  make the mapping unambiguous and the 7.2 obligation text is self-contained,
  so no evidence is affected; the coordinator should reconcile the titles in
  any future amendment rather than editing the frozen text silently.
- **P3-2 (observation, no overclaim found).** The enacted `M06` body
  substitutes a metadata-derived constant for the computed completion value;
  it does not literally consult the reference semantics. This matches the
  frozen `R2-06` challenge wording ("precomputed semantic result") and the
  addendum describes the body accurately, but the smuggle-the-right-answer
  direction of an answer oracle is covered jointly by `M06` (result path is
  live) and `M07` (trace connection is load-bearing) rather than by `M06`
  alone. The result report's own "threefold defense" paragraph states this
  composition correctly.
- **P3-3 (report clarity).** The worker-side ledger row "`R2-ALLSIZE` replay
  stage PASS" in result-report section 9 describes the pre-repair run whose
  `M05`/`M06`/`M07`/`M11` bodies were later found arity-only; the defect is
  disclosed in the same section's `R2R1` receipts, but the row itself carries
  no annotation. A reader stopping at the first table could over-trust the
  pre-repair run. Cosmetic; the repaired run and this audit's independent
  rerun supersede it.

## 6. Result-report claim audit

Every material claim of `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md`
was checked against the blind reconstruction and the audit's own runs:
identity table (base/trees/parents/commit and path counts) verified against
Git; construction paragraph and 427 accounting verified against
`ReviewerController.lean`; composition chain verified name-by-name (including
`packedReviewerMemory_header_cell`,
`packedReviewerCanonicalReachable_state_machine_fits`,
`packedReviewerReachableStateCertificate_of_reachable`); row dispositions
verified against matrix section 7 and the validation consumers; K1 digestion
verified against the prelude module; cited decision entries
(`DD-20260805-071`..`075`, `WDD-20260805-001`/`002`) present and accurate;
`R2R1` receipts (six axiom entries and their exact axiom lists, seven-case
stage semantics, activation checks, restoration and clean-state contracts)
independently reproduced. The report claims only `CANDIDATE_COMPLETE` and
repeatedly reserves acceptance; the deferral boundary matches matrix 7.5.

Positive-evidence tiers: the payload/memory/run/correctness/cap claims are
checked kernel theorems consumed by exact-type validation consumers (tiers
1-3); the replay stage and restoration contracts are executable artifact
evidence (tiers 3-4); worker/coordinator ledger prose is process evidence
(tier 5) and was relied on only where this audit reproduced the underlying
command itself.

## 7. Stale or rejected objections

- The pre-repair objection that the `R2-ALLSIZE` REJECT verdicts certified
  arity sensitivity rather than the frozen semantic requirements is stale:
  `368b828` moved the four mutants into load-bearing definition bodies, added
  the mechanical activation check, and this audit re-read each patched body
  and re-ran the stage to seven commissioned semantic REJECTs.
- The historical `FG-01` two-object ambiguity (`DD-20260804-038`) is resolved
  on this branch in the commissioned direction: the counted, serialized, and
  executed object is the canonical reviewer payload equal to public
  `buildPayload`, and the flat sibling is excluded by both the identity
  theorems and the `M11` REJECT.

## 8. Roadmap alignment

In letter: every `R2-*` row and rung-scoped inherited obligation is
discharged with the exact evidence forms the amendment demands. In spirit:
the rung removes precisely the abstraction defects the amendment targeted --
the finite-cutoff sparse assumption is gone at every size, the executed and
counted objects are the same construction, the controller is a proof-free
request/reply machine, and the anti-bypass surface is enforced by replayable
semantic mutations rather than by prose. The explicitly deferred full-node
rows remain open and are correctly labeled blocking for the node, not this
rung.

## 9. Best next target

Coordinator disposition of this rung (acceptance decision and lifecycle
update), then the full-node falsification remainder in the frozen order:
the `FG-11` liveness mutation campaign and the seven outstanding registry
cases toward full `FG-12`, followed by the `FG-14` boundary campaign and the
`FG-15` durable record.

## 10. Durable report path

`docs/internal/audit_reports/2026-08-05_EG_CP_ALLSIZE_R2_fresh_blind.md` on
branch `audit/eg-cp-allsize-aud1-fresh-blind` (exact parent
`a0a0f92b8f9081ee59797affb5045952d9e39fbf`). Report-only: no other file is
touched. Post-report checks rerun on the report commit are recorded in the
round log by the coordinator on disposition; this audit reran strict claim
drift, the strict design-decision check, `git diff --check`, UTF-8
inspection, and cleanliness on the tree containing this report before
committing, as required.

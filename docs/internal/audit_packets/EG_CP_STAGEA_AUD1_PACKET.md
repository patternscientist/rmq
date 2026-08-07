# EG-CP Stage A: `AUD1` fresh-blind evidence packet (verdict-free)

This packet identifies the exact Stage-A candidate for the independent
`EG-CP-A13-CAPSTONE-AUDIT`.  It contains identities, inventories, and check
receipts only.  It contains **no** audit verdict, **no** auditor prompt, and
**no** simulation of an audit outcome; `EG-CP-A13` is OPEN and
auditor-owned.  Per the frozen contract, the auditor receives the frozen
acceptance contract, not the worker's narrative: the worker's result report
(`docs/internal/EG_CP_STAGEA_RESULT.md`) should be withheld until the
auditor has independently reconstructed the proof surface.

## 1. Exact candidate lineage

| Object | Exact value |
| --- | --- |
| Exact accepted base (Stage-F `FEASIBILITY_PASS`) | `270d78559adc33fe872b6d17bd54d8e51567a605`, tree `7b872cf144503cebf61097f857fa779081076107` |
| Matrix-freeze commit | `f4107cd15173fef690ba05e51becb9c65b6c7d60`, tree `9f67cb4162fac12fab59a09d5941f208fdd4f123`, parent `270d7855...` |
| Implementation commit | `08dd29d4d72047c9da1f938d411d65264bdfd2b2`, tree `21c121e3931eab3192abe9a62f61fa4da78de22f`, parent `f4107cd...` |
| Frozen proof/replay candidate | `1198ff6fbd66a4de991ad7e8fe1235a452d4b337`, tree `35327c3077ef3d6d5111159668518d960d1467bd`, parent `08dd29d...` (the `SA-M13` ASCII-needle runner repair; Lean bytes identical to the implementation commit) |
| Report commit (documentation-only) | parent is the frozen proof/replay candidate; contains this packet, the result report, the round-log entry, the digestion note, the worklog checkpoint, and the matrix evidence ledger |
| Branch | `codex/eg-cp-stagea-close-r1` |
| Workflow-governance ref | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` |

## 2. Frozen contract

- `docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` at the matrix-freeze
  commit: requirement rows `EG-CP-A01`..`EG-CP-A13` (roadmap sentences
  verbatim), seven inherited invariants, five harness/integrity contracts,
  the 38-field combined-proposition shape (section 1.1; extended to 39 by
  coordinator amendment `CA-20260807-001`, section 7), the frozen fixture
  (section 1.2), the composition chain (section 1.3), and the ordered
  21-case replay registry (section 4; 2 ACCEPT / 19 REJECT).  Frozen rows
  are byte-frozen in their entirety; evidence lives only in the append-only
  section-8 ledger.
- The roadmap Stage-A table at the exact base
  (`docs/internal/RMQ_ENDGAME_ROADMAP.md`) is the requirement source.

## 3. Theorem/type inventory (candidate surface)

New module
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`:

- `PackedReviewerArchitectureCapstone (xs : List Int) (left right : Nat) :
  Prop` -- the combined proposition: 38 fields byte-frozen in matrix
  section 1.1 before implementation, plus field 39 `valid_answer_is_index`
  appended by coordinator amendment `CA-20260807-001` (audit finding `P3-3`),
  which changes no frozen field.
- `packedReviewerArchitectureCapstone_holds : forall xs left right,
  PackedReviewerArchitectureCapstone xs left right` -- the producer, by
  projection from the accepted public run certificate and Stage-F theorems.
- New bridges owned by the module:
  `packedReviewerPreludeRemaining_init_eq_three`,
  `packedReviewerWholeRemaining_start_eq_210` (structural
  `1 + 2*3 + 2*210 = 427` decomposition),
  `packedReviewerInvalidReferenceNone`,
  `packedReviewerRunLeftmostTie` (universal leftmost-tie connection through
  `queryCosted_exact`/`queryCosted_leftmost`/`scanWindow`),
  `packedReviewerRunReachableInvariant`
  (`packedReviewerDriveAux_decompose` at the literal run),
  `packedReviewerValidRunAnswersIndex` (field 39's producer: a valid query is
  answered with an index, from `queryCosted_exact`/`scanWindow`).

New validation root `RMQ/Validation/EGCPStageA.lean`:

- Signature pins: `egcpStageACapstoneSignature`, `egcpStageAWidthSignature`,
  `egcpStageAControllerSignature`, `egcpStageARunSignature`,
  `egcpStageAMemorySignature`.
- `EGCPStageAArchitectureFacts` + `egcpStageAArchitectureFactsExact` -- the
  independent literal 39-field restatement and its projection producer.
- Width literals: `egcpStageAWidthPinZero/One/Two/Three`
  (`10`, `14`, `14`, `15`).
- Boundary campaign: `egcpStageACapstoneEmpty`, `...Singleton`,
  `...SizeTwo`, `egcpStageASizeTwoDistinct`, `...Crossovers` (5487/5488/5489),
  `...ReadinessWindow` (1023/1024/1025/1329/1330/1331),
  `...InvalidQueries` ((1,1),(2,1),(0,4),(5,7) on `[7,3,3]`),
  `...DuplicateMin`, `egcpStageAInvalidRunExact`,
  `egcpStageADuplicateMinimum`, `egcpStageANoSecondRepresentation`.
- Fixture re-pins: `egcpStageAHeaderLivenessFixture` (`10 -> 37`),
  `egcpStageADecisiveCellConnection` (full literal occurrence chain),
  `egcpStageAUnreadCellAcceptPinned`, `egcpStageADeadAddressWidth`.

Registrations: `RMQ.lean` imports both modules;
`scripts/axiom_check.lean` adds four curated entries
(`packedReviewerArchitectureCapstone_holds`, `packedReviewerRunLeftmostTie`,
`packedReviewerRunReachableInvariant`,
`Validation.egcpStageAArchitectureFactsExact`).

Replay: `scripts/eg_cp_stagea_replay.ps1` -- the frozen 21-case registry
with `-Case`/`-SelfTestOnly`/`-IntegrityProbe` boundary semantics.
`scripts/eg_cp_final_falsification_replay.ps1` is byte-identical to the base
(blob `3420c76c3d232119052b49aa0577f7b1df169afe`).

## 4. Object/composition chain

`xs` -> `SuccinctClassic.cartesianShape xs` -> `packedReviewerPayloadBits
shape = SuccinctClassic.buildPayload xs` -> `packedReviewerSerializedBits
shape = headerBits ++ payloadBits` -> `packedReviewerPaddedBits shape`
(final-cell `false` padding; length = `packedReviewerAllocatedBits`) ->
`packedReviewerMemory shape` (uniform `w`-cell chunking; header is cell 0) ->
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right` (replies literally `memory[address]?`; controller receives only
`(n, left, right)`) -> `packedReviewerRunAgainstMemory_eq_lowered` ->
`packedReviewerDriveLogical_210_simulates_packedWholeQueryRun` ->
`packedWholeQueryRun_eq` -> `packedReviewerPackedReference_eq_public` ->
`SuccinctClassic.queryTraceResult xs left right` (half-open, leftmost-tie
`List Int` reference), with `LeftmostArgMin` reached universally through
`queryCosted_exact`/`queryCosted_leftmost`.

## 5. Check receipts on the frozen candidate

All receipts observed on the frozen proof/replay candidate
`1198ff6fbd66a4de991ad7e8fe1235a452d4b337` (Windows 11, Windows
PowerShell 5.1, pinned toolchain `leanprover/lean4:v4.22.0`):

| Check | Receipt |
| --- | --- |
| `lake build RMQ.Validation.EGCPStageA` | exit 0, 8 s (post-campaign; the cold chain build was 1060 s earlier in development) |
| `lake build RMQ RMQUnionFind` | exit 0, 198 s |
| `lake env lean scripts/axiom_check.lean` | exit 0, 176 s; the four curated Stage-A entries each depend only on `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`/`ofReduceBool`/`trustCompiler` in the inventory |
| Certification full replay (exactly once) | `FULL MODE PASS`, exit 0, 1100 s: 21/21 as commissioned (2 ACCEPT / 19 REJECT) at the frozen surfaces, 0 target-absent, calibration 5 s clean / 156 s probe, deadline 624 s, descendant self-test PASS, 20 SHA256-verified restorations, terminal tree clean |
| Prior diagnostic full replay (implementation tree `08dd29d`) | 20/21 as commissioned + the runner's own `SA-M13` needle-encoding defect, repaired by `WDD-20260806-010`; Lean bytes identical between the two trees |
| Selector/boundary controls | exact `SA-A01` selector ACCEPT (421 s); unknown/empty/whitespace/bogus/combined selectors fail closed; `-IntegrityProbe OmitMiddle`/`DuplicateMiddle` reject corrupted registry copies; Windows `-SelfTestOnly` PASS |
| Consumer anti-vacuity probes (outside Git) | cap `427 -> 428` and decisive `some 2 -> some 3` each fail the build at `RMQ/Validation/EGCPStageA.lean`; byte restoration SHA256-verified |
| Forbidden-token and native-shortcut scans | zero matches over `RMQ` and `lakefile.toml` |
| `git diff --check` (working tree and `270d7855..HEAD`) | clean, exit 0 |
| `design_decision_check.ps1 -Strict -Base 270d7855...` | PASS exit 0 (`checked 9 changed files (4 code, 2 workflow, 4 neutral)`); per-commit `-Base HEAD~1` PASS at every commit **up to and including this frozen candidate**. **Known exception above this candidate:** the first report landing `ea08f28` FAILS the per-commit check at its own parent (three workflow-sensitive report paths without a same-commit workflow-ledger entry). It was reverted by `c38e885` and re-landed paired by `ec35b5d` (`WDD-20260806-011`), so the branch tip passes, but the failing commit stays reachable in branch history. See `EG_CP_STAGEA_RESULT.md` section 1 and the `SA-CHK-09` ledger row. |
| `claim_drift_scan.ps1 -Strict` | PASS exit 0 (`1525 hits, 0 strict failures`) |
| Frozen-row byte-integrity (matrix vs freeze blob `719c01d1...`) | 46/46 row IDs byte-identical under strict UTF-8, 0 missing/duplicated/changed; injected-row-edit and injected-mojibake negative controls both fire |
| `scripts/eg_cp_final_falsification_replay.ps1` | byte-identical to the exact base (blob `3420c76c3d232119052b49aa0577f7b1df169afe`); its inherited registry not rerun (conditional not triggered) |
| `scripts/gate.ps1` | not run: not frozen as aggregate owner; every changed surface owned by the checks above (recorded skip) |

## 6. Open audit questions (no verdict expressed)

1. Do the conjuncts of matrix section 1.1 (as amended) entail each frozen
   `EG-CP-A01`..`EG-CP-A10` sentence at the named objects, or is any row
   satisfied only by a weaker projection?
2. Is `EGCPStageAArchitectureFacts` genuinely independent -- i.e., would
   every commissioned weakening of the capstone break it at
   `RMQ/Validation/EGCPStageA.lean` rather than being absorbed?
3. Does any capstone field quantify over an object other than the literal
   `packedReviewerMemory shape` / `packedReviewerRunAgainstMemory ...` pair
   (sibling, supplied, prefix-only, or flat-universe substitution)?
4. Are the seven new Stage-A mutation bodies discriminating at their frozen
   surfaces, and are the honest labels (structural `SA-M11`/`SA-M14`,
   value-preserving `SA-M15`) accurate?
5. Is the `1 + 2*3 + 2*210` decomposition genuinely structural -- would a
   stored `427` break the committed consumers?
6. Does the universal leftmost-tie field add real content over the guarded
   reference equality (i.e., is `queryCosted_leftmost`'s domain aligned with
   the run guard)?
7. Is anything reviewer-facing true of the packed machine but absent from
   the combined proposition (completeness of the closure)?

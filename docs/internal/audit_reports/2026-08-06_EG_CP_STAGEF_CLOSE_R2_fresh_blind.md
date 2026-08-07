# Fresh-blind audit: Stage-F residual candidate `EG-CP-STAGEF-CLOSE-R2` (AUD1)

Auditor: `EG-CP-STAGEF-AUD1` (fresh-blind delta, report-only).
Date: 2026-08-06.
Durable report: `docs/internal/audit_reports/2026-08-06_EG_CP_STAGEF_CLOSE_R2_fresh_blind.md`.

This report records what an independent fresh session observed on the exact
target. It is an audit recommendation, not coordinator acceptance; nothing
here records `FEASIBILITY_PASS`, Stage-A state, integration, publication, or
public-claim synchronization.

## 1. Findings, P0 -> P3

### P0 — none

No proof or trust invalidity and no artifact corruption was found.

### P1 — none

No material claim overstatement, failed required gate, or misleading theorem
surface was found. Every factual claim checked in
`docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md` sections 1-9 reproduced
against Git, Lean, and the replay harness on the exact target.

### P2

- **P2-1: the frozen `SF-FG11-HEADER` pinned-fixture instance is not
  committed.** Matrix section 10.3's `SF-FG11-HEADER` "Quantifiers and
  guards" cell freezes "Universal over `shape : CartesianShape` and all
  valid endpoint pairs ..., plus one pinned instance at the section 10.2
  fixture", and section 10.2 says the header mutation's "fixture instance is
  recorded with the concrete moved second address". No committed declaration
  instantiates `packedReviewerHeaderCellAddressLiveness` at
  `[7, 3, 3]`/`(0, 3)`, and no concrete mutated-run second address appears
  in `ReviewerCapstone.lean`, `RMQ/Validation/EGCPFinalFalsification.lean`,
  or the final record (exhaustive search; the canonical run's concrete
  second address `10` IS committed inside `egcpFixtureTraceAddresses`).
  Mitigations, verified: the universal theorem strictly subsumes the
  instance's existence (it instantiates at the fixture with
  `0 < 3 /\ 3 <= 3`), and the record's section 3 row honestly claims only
  the universal theorem, the `_proj` corollary, and the opening pin — it
  does not claim a pinned instance. Consequences: (a) one frozen-cell item
  is undischarged; (b) the `EG-CP-F12` "zero focused proof-days, closed
  inventory" claim in record section 5 is exact only up to this residue (a
  one-line instantiating corollary plus one kernel-checked literal — well
  under a day, still inside the ten-day `FEASIBILITY_PASS` ceiling with
  margin). Suggested discharge: commit the fixture instantiation together
  with the kernel-checked mutated-trace second-address literal, or record a
  coordinator note that the universal theorem supersedes the
  pinned-instance cell.

### P3

- **P3-1: stale conjunct count in the validation docstring.**
  `RMQ/Validation/EGCPFinalFalsification.lean:2881` reads "Independent
  restatement of the twelve frozen Stage-F conjuncts"; the structure has
  fourteen fields, and matrix section 10.5 and record section 3 both
  correctly say fourteen. Doc comment only; no proposition affected.
- **P3-2: the Stage-F record's K-alternative disposition is by reference,
  not restated.** Frozen section 10.7 requires the record to carry "K1
  survived / K2 unused; rejected K0 / K2 / padding / historical
  alternatives". The appended Stage-F record mentions the K1 chain (its
  section 5) but relies on the same file's prior-rung "K1 digestion"
  section, the `DESIGN_DECISIONS.md` "Rejected alternatives" block
  (line 9653), and matrix section 5's deferral rows (K0 self-delimiting
  bootstrap, K2, internal padding = predetermined coordinator flips) for
  the rest. All content exists in the same durable files; nothing is
  missing substantively, but the record neither restates nor explicitly
  cites it.
- **P3-3: latent non-Windows kill gap on the build path.** In
  `scripts/eg_cp_final_falsification_replay.ps1`, `Invoke-BoundedLake`'s
  timeout path calls `Stop-ProcessTree`, whose Unix branch addresses the
  negated pid as a process group; the lake child is not started as a group
  leader (no `setsid` on the build path), so a timed-out build on Linux
  could outlive its kill. This is outside the frozen contract's exercised
  paths: the Ubuntu gate leg is the build-free `-SelfTestOnly`, whose
  sleeper root IS `setsid`-wrapped, and every build-carrying run happens on
  Windows where `taskkill /T /F` walks the real tree. Note for any future
  Linux Lean gate.
- **P3-4: `M13`'s frozen mutant is value-preserving.**
  `hiddenUncountedTable := memory.take 1` serves
  `hiddenUncountedTable[a]?` only for `a < 1`, which equals `memory[a]?` —
  the mutant changes the reply plumbing, not any reply value. Its
  commissioned REJECT is therefore carried by the structural read-backing
  surface (the `memory_only` theorems in `ReviewerController.lean`), which
  is exactly the load-bearing guard for
  `INV-READ-BACKING`/`INV-PROGRAM-ACCOUNTING`, so the rejection is honest
  for the claim it guards. Recorded because a value-diverging table variant
  would be the stronger mutant. The enacted body matches the section 10.4
  freeze.

## 2. Scope, mode, identity, and independence protocol

- Mode: FRESH BLIND DELTA, report-only, per
  `docs/internal/AUDIT_PROTOCOL.md`. Fresh session; no role skill used.
- Base `0f386723f56deae5eb39418e535f56e7a2b347dd` (tree
  `ec0ab9c96f598ddc81a0e30424410461296abe71`, independently re-derived by
  `git rev-parse 0f38672^{tree}`).
- Target `9687b4ad4f3cb8c843625dc2ffbb486cdecb6b5f` (tree
  `aff13b35f3e6e8d5d63ecffe8246fe506f0836c4`, re-derived likewise). Source
  branch `codex/eg-cp-stagef-close-r2`; the exact commit controls; no
  descendant of the target was inspected.
- Chain verified (`git log --format='%H %P %T'`): five commits, each
  single-parent —
  `0f38672 -> 8d22684 -> c1eada6 -> 37764ad -> f105971 -> 9687b4a`.
- Changed paths: exactly the twelve-path allowlist, overall and per commit
  (`git diff --name-status`, `git log --name-status`): `RMQ.lean`;
  `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Boundaries.lean`;
  `RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean` (new);
  `RMQ/Validation/EGCPFinalFalsification.lean`; the six
  `docs/internal/` records; `scripts/axiom_check.lean`;
  `scripts/eg_cp_final_falsification_replay.ps1`.
- Worktrees: audit worktree `.claude/worktrees/stagef-aud1-fresh-blind` on
  branch `audit/eg-cp-stagef-close-r2-aud1-fresh-blind` created directly at
  the exact target (clean through every read-only phase and after the
  replay); a disposable mutation worktree
  `.claude/worktrees/stagef-aud1-mutation` (detached at the target) for the
  two counterfactual probes only, restored byte-exactly and left clean; a
  detached lifecycle worktree for the per-commit checks.
- Independence: no chat transcript, worker response, coordinator verdict,
  same-session audit narrative, or post-target commit was read. The frozen
  requirements, exact theorem types, consumers, replay registry, history,
  and proof obligations were reconstructed from the base blob, the target
  delta, the matrix, the roadmap, the Lean sources, and the scripts BEFORE
  `docs/internal/EG_CP_FINAL_FALSIFICATION_RESULT.md`,
  `docs/internal/R2_ALLSIZE_WORKLOG.md`, or the new Stage-F portion of
  `docs/internal/AUDIT_AND_A_DESIGN.md` were opened; those records were then
  audited for factual accuracy. Prior reports and ledgers were treated as
  process evidence (tier 5), never theorem evidence; no prior verdict,
  disposition, or label was inherited.
- Skill preflight (`scripts/project_skill_preflight.ps1`, governance
  `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`, checkout the exact target,
  runtime catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`,
  `-AllowNoRequiredSkills`): PASS; governance verified an ancestor;
  expected, checkout, working-tree, and runtime skill sets all equal;
  `required_mode=explicit-no-role`.

## 3. Verdict

**Merge-ready with follow-up** (audit recommendation for coordinator
acceptance of this exact Stage-F candidate; not itself acceptance). The one
follow-up is `P2-1` — commit the pinned `SF-FG11-HEADER` fixture instance
with its concrete moved second address, or record the coordinator's
supersession of that frozen cell by the universal theorem — plus the P3
polish items at the coordinator's discretion. Every load-bearing semantic
obligation checks out on the exact target: decisive-connection information
preservation, the exact-type controller input boundary, value dependency at
the terminal projection, the unread-cell accept, the `M06` bridge, replay
fidelity on all sixteen cases, boundary coverage, trust hygiene, frozen-row
byte integrity, and per-commit lifecycle discipline.

## 4. ID-by-ID requirement-to-evidence reconstruction

Evidence tiers per `AUDIT_PROTOCOL.md`: T1 kernel theorem; T2 model/store/
trace theorem; T3 executable validation; T4 reproducible artifact; T5
process evidence.

### Section-10 Stage-F rows (this rung's controlling contract)

| ID | Disposition | Evidence (tier) |
| --- | --- | --- |
| `COMPLETE-STAGEF-EVIDENCE` | Delivered up to P2-1 | Address liveness universal (T1); result liveness at `.terminal` (T1); decisive and unread controls (T1); semantically faithful sixteen-case replay (T3/T4, section 7); query-level boundaries (T1); durable record factually accurate (T5, sections 2 and 7 of this report). |
| `SF-FG11-HEADER` | Substantively closed; P2-1 residue | `packedReviewerHeaderCellAddressLiveness` + `_proj` + `packedReviewerRunOpensWithHeader` (T1); consumer `egcpStageFHeaderAddressLiveness` (T3); replay `M01`/`M14` REJECT at `PackedCellProbe/ReviewerControllerProof.lean` (T4). Missing: committed pinned fixture instance + concrete moved second address (P2-1). |
| `SF-FG11-DECISIVE` | Closed | `packedReviewerDecisiveCellLiveness` (T1, `.terminal` projection: `some (some 1)` vs `some (some 2)`, unequal); `packedReviewerDecisiveCellConnection` (T1, all `R1` conjuncts in the conclusion — section 5); consumers `egcpStageFDecisiveCellLiveness`, `egcpStageFDecisiveCellConnection` (T3); probe 1 fails at the literal consumer (section 6). |
| `SF-FG11-UNREAD` | Closed | `packedReviewerUnreadCellAccept` (T1: `4 < 22` allocation; no trace event at address 4; complete run-record equality for EVERY replacement via `packedReviewerRunAgainstMemory_eq_of_agree`) + pinned instance at the frozen `w0` (T1); consumers (T3); replay `A02` expected-accept on the frozen replacement-value patch (T4). |
| `SF-M06-BRIDGE` | Closed | `packedReviewerNoMetadataCompletion` (T1): refutes every `f : Nat -> Nat -> Nat -> Option Nat` explaining both fixture terminals; covers the enacted `f = fun n _ _ => some n` and the reference-oracle `f = fun _ l r => (queryTraceResult xs0 l r).value`; consumer `egcpStageFNoMetadataCompletion` (T3). A literal in-controller reference call is untypeable — the controller state and driver carry no `xs` or shape (verified from the inductive definitions) — so the bridge is the faithful route; the prior rung's `P3-2` carry-forward is discharged. |
| `FG-11-LIVENESS-AND-ANTI-BYPASS` | Closed at this rung's objects (P2-1 residue) | The three `SF-FG11` rows; inequalities at the address projection (`trace[1]`) and the returned-value projection (`.terminal`), never an enclosing record. |
| `FG-12-REPLAY-AND-CONSUMER` | Closed | Independent full replay on the exact target: `FULL MODE PASS`, exit 0, 1494 s, 16 considered / 16 as commissioned / 0 target-absent, 2 ACCEPT / 14 REJECT (T4, section 7). Independent expected-type consumers `EGCPStageFCapstoneFacts`/`egcpStageFCapstoneFactsExact` + `egcpStageFCapstoneSignature` pin the full capstone (T3; probe 2 confirms). |
| `FG-13-TRUST-AND-SAME-OBJECT` | Closed | Hygiene scan 0 matches over `RMQ` + `lakefile.toml`; native-shortcut scan 0 matches (T4); axiom inventory: all six Stage-F entries exactly `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`/`ofReduceBool`/`trustCompiler` in the 1156-entry inventory (T4); the capstone's fourteen conjuncts all range over the identical let-bound `shape`/`memory`/`run` (T1, verified field-by-field); the capstone is `Prop`-valued and cannot route execution. |
| `FG-14-BOUNDARIES` | Closed | One universal `packedReviewerStageFCapstone_holds` instantiated at `[]`, `[0]`, `[0, 1]`, `[1, 0]` (distinctness proved by diverging answers), `5487/5488/5489`, `1023/1024/1025/1329/1330/1331`; invalid queries return exactly the `.done none` run with empty trace (T1); duplicate-minimum `[7, 3, 3]`/`(0, 3)` leftmost `some 1` through `scanWindow`/`queryCosted_exact`/`queryCosted_leftmost` (T1, oracle-independent); uniform-entry and uniform-builder `rfl` pins plus `M04`/`M11` REJECTs close no-second-representation; `Boundaries.lean` adds the frozen `1025`/`1329` neighbour facts. |
| `FG-15-DURABLE-DECISION` | Closed (P3-2 nuance) | Record sections 1-9, matrix 10.8 outcome cells, worklog entry, round-log records; no row cites commissioning prompts or audit prose as theorem evidence (checked); K-alternatives dispositioned by reference (P3-2). |
| `EG-CP-F10-ANTI-BYPASS` | Closed | Replay REJECTs at committed exact expected surfaces for shape (`M03`), sibling store (`M05`), proof-oracle (`M06` via the bridge), uncounted table (`M13`), disconnected trace (`M07`), forged count (`M08`), sibling payload (`M11`); unchanged accept `A01` and unread-cell accept `A02` control (T4). |
| `EG-CP-F11-BOUNDARIES` | Closed | The `FG-14` checked theorem/fixture matrix (T1). |
| `EG-CP-F12-RESIDUAL-ESTIMATE` | Closed up to P2-1 | Record section 5's inventory verified item-by-item against committed bytes (every named theorem/consumer exists and is consumed; independent enumeration in section 8 of this report); the zero-day estimate is exact up to the P2-1 one-liner, well under the ten-day `FEASIBILITY_PASS` ceiling; no unknown dynamic input (exact-type pin + run factorization + charged `longCount`/`sparseCount` decodes — checked propositions). |
| `EG-CP-F13-NO-ASSUMED-CAPSTONE` | Closed | Controller state constructors carry only `Nat` counters, protocol sub-states, and already-supplied replies (verified at the inductive definitions, including `PackedReviewerSparsePreludeState` and `PackedReviewerWholeState`); replies are literally `memory[request.address]?` in the driver; the reference result is a proved theorem about the executed run (`packedReviewerRunAgainstMemory_public_outcome`), not a field or hypothesis; the `427` cap is the proved structural-measure bound; decisive-cell corruption rejected and unread-cell accept controls (T1/T2). |
| `REPLAY-EXACT-REGISTRY` | Closed | Literal ordered sixteen-entry array matching matrix section 3 in ID, order, mutation description, verdict, and named-surface category; `Test-RegistryIntegrity` enforces count/order/uniqueness/verdict-mapping/2-14 partition before any build; exercised on every invocation (T3/T4). |
| `REPLAY-SELECTOR-NONVACUITY` | Closed | Unknown selector: `REPLAY-FAIL: unknown or non-unique case selector`, nonzero exit before any build (exercised); whitespace selector: `REPLAY-FAIL: ... must not be empty or whitespace` (exercised; the explicit-empty branch is the same `Trim()` check, code-verified with `[AllowEmptyString()]`); `-SelfTestOnly` refuses `-Case`/`-Stage`/`-SkipSelfTest` (exercised); only omission means full mode (code-verified; full mode exercised once). |
| `REPLAY-SUBPROCESS-DEADLINE` | Closed (P3-3 note) | Deadline `max(max(clean, probe) * 4, 300)` from a genuine artifact-changing mutated-chain probe (appends `private def egcpDeadlineCalibrationProbe`, SHA-restored, clean rebuild follows); observed on this run: clean 2 s, probe 348 s, deadline 1392 s; timeout is failure; owned-tree termination `taskkill /T /F` on Windows and negated-pid + `setsid` on Linux; pid-verified root+grandchild self-test PASS on Windows PowerShell 5.1 (exit 0, 6 s) and WSL `Ubuntu-24.04` `pwsh 7.6.4` (exit 0, 14 s) on the same committed bytes; cleanup/restoration in `finally` (T3/T4). |
| `SF-CHK-00` .. `SF-CHK-11` | Outcome cells verified as the only post-freeze matrix change | The substantive ones reproduced independently on the exact target (section 7); `SF-CHK-11`'s skip reasoning re-derived and adopted (section 7, last item). |
| `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | Closed | Section 7: strict UTF-8, pure append, 0 missing / 0 changed rows. |

### Inherited invariant rows retained by section 10

| ID | Disposition |
| --- | --- |
| `INV-VALUE-DEPENDENCY` | Closed at the full-node objects: address projection (universal header theorem) AND returned-value projection (`.terminal`, decisive pair); never an enclosing record. |
| `INV-SEMANTIC-NONVACUITY` | Closed: liveness derives from emitted probes of the actual run (kernel-checked trace literals transported to the public objects; `packedReviewerDriveAux_decompose` ties the prefix fold to the emitted trace). |
| `INV-STORE-AGREEMENT` | Closed: `store_agreement_determinism` conjunct (ordered agreement on the probed cells determines the whole run record) consumed by the unread-cell route. |
| `INV-READ-BACKING` | Closed: `probes_backed_by_memory` conjunct — every reply is literally `memory[event.request.address]?`; `M13`'s REJECT guards it. |
| `INV-PUBLIC-COMPOSITION` | Closed: all fourteen conjuncts quantify over the same `xs`, `left`, `right` and mention the same let-bound `shape`/`memory`/`run` (field-by-field check against matrix 10.5). |
| `INV-MUTATION-REPRODUCIBILITY` | Closed: versioned runner; full-mode 16/16 with SHA-verified restorations and terminal clean tree, reproduced independently. |
| `INV-CATEGORY-SEPARATION` | Closed: the record separates the derived 427 physical cap from the 210 logical fuel, payload bits from allocated bits, proof fields from machine state, and OS receipts from Lean claims. |

The remaining base-matrix rows (`FG-01`..`FG-10` original rows, the other
`INV-*` rows, `R2-01`..`R2-10`, `R2-INHERITED-*`, `R2-DEFER-*`, `CHK-*`,
`R2-CHK-*`, and sections 7-9) are inherited history: byte-identical to the
exact base blob (section 7) and not re-audited beyond that integrity check,
per the fresh-blind-delta scope.

## 5. The two repaired surfaces: complete checked types

### `packedReviewerDecisiveCellConnection` (producer, `ReviewerCapstone.lean`)

Conclusion (existential over `position`, `event`, `request`, `replyCell`,
`preState`, `postState`, every binder pinned by a conjunct), with
`shape0 := SuccinctClassic.cartesianShape [7, 3, 3]`,
`mem0 := packedReviewerMemory shape0`,
`run0 := packedReviewerRunAgainstMemory mem0 shape0.size 0 3`:

1. `run0.trace[position]? = some event`;
2. `position = 11`;
3. `event.request.origin = PackedReviewerPhysicalOrigin.wholeQuery request`;
4. `request.invocation.instruction = PackedReviewerInstructionSite.leftSelect`;
5. `request.invocation.argument = 0`;
6. `request.invocation.argument2 = 0`;
7. `request.site = PackedReviewerReadSite.entryFirstOffset`;
8. `request.segment = 8`;
9. `request.index = 0`;
10. `event.request.address = 8`;
11. `event.reply = some replyCell`;
12. `event.reply = mem0[event.request.address]?`;
13. `preState = packedReviewerDriveStateAt mem0 (packedReviewerController shape0.size 0 3) position`;
14. `packedReviewerNextRequest preState = some event.request`;
15. `packedReviewerConsumeReply preState event.reply = postState`;
16. `(packedReviewerDriveAgainstMemoryAux mem0 (packedReviewerControllerMeasure (packedReviewerController shape0.size 0 3) - (position + 1)) postState).terminal = some (some 1)`;
17. the same continuation's `.state = .done (some 1)`;
18. `run0.terminal = some (some 1)`;
19. `run0.state = .done (some 1)`;
20. `(SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1`.

Information survival: every `R1` component is a CONCLUSION conjunct, not a
proof-term artifact. The pre-state is not free-floating:
`packedReviewerDriveStateAt` is the fold of `packedReviewerDriveStep`, which
is definitionally the driver's own transition (result check, `nextRequest`,
single memory lookup, `consumeReply`), and `packedReviewerDriveAux_decompose`
proves — for every memory, fuel, state, and position below the trace
length — that the fold is live at `i`, that its computed request IS the
recorded event's request with the driver's own lookup as reply, and that
restarting the driver at the fold with the remaining fuel reproduces the
whole run's terminal, state, and exact trace suffix (`trace.drop i`). A
separately invented state cannot satisfy those equations anywhere a trace
event exists, and the continuation conjuncts consume the same fuel
arithmetic (`measure - (position + 1)`) the driver itself uses. The
continuation's terminal and the run's terminal are separately pinned to the
same literal `some (some 1)`, so the continuation reaches the same run's
terminal.

### `PackedReviewerStageFCapstone.controller_input_boundary` (conjunct 12)

Checked content, over `shape := SuccinctClassic.cartesianShape xs` for all
`xs left right`:

- `@packedReviewerController = (fun (n left right : Nat) => packedReviewerController n left right)`, and
- `packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left right = packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape) (packedReviewerControllerMeasure (packedReviewerController shape.size left right)) (packedReviewerController shape.size left right)`.

Why this genuinely pins the input boundary: the eta-expanded right-hand side
elaborates only if `packedReviewerController n left right` is a complete
application yielding `PackedReviewerControllerState` at three `Nat`
arguments. Any added parameter — explicit, implicit, `optParam`, shape,
list, oracle, or advice — changes `@packedReviewerController`'s type away
from `Nat -> Nat -> Nat -> PackedReviewerControllerState` and makes the
equation ill-typed. Confirmed empirically: replay case `M03` (which adds
the weakest possible parameter, `(_shape : Option Cartesian.CartesianShape
:= none)`) REJECTs at `PackedCellProbe/ReviewerCapstone.lean`, surface
`exact signature`. The factorization conjunct separately pins that the
public run is THIS controller driven by THIS driver on THIS memory, so a
wrapper that recovers a shape from `n` (`M04`) or drives a sibling store
(`M05`) breaks it. The former length/arity and store-agreement facts
survive as conjuncts 13 (`closed_length_and_memory_arity`) and 14
(`store_agreement_determinism`) under accurate names and are NOT called an
input boundary — correctly, since an added parameter leaves all three of
the old facts provable, which is exactly why the rejected `R2` form was
inadequate and the repaired form is not.

## 6. `P`/`Q` comparisons and the two counterfactual probes

### `P`/`Q`/guard/quantifier identity (frozen 10.3/10.4 vs checked Lean)

- `SF-FG11-HEADER`. Frozen `P` (run opens with the header request at cell
  `0`; second attempt is the first `.rankSuper` prelude probe; same run
  returns the guarded reference result) = committed
  `packedReviewerRunOpensWithHeader` + the universal theorem's two-step
  opening + `packedReviewerRunAgainstMemory_public_outcome`. Frozen `Q`
  (replace ONLY cell `0` by `natToBitsLE (packedReviewerCellWidth
  shape.size) (longCount shape + packedReviewerCellWidth shape.size)`; the
  two `trace[1]?` address projections both `some` and unequal) = the
  committed conclusion verbatim, including the exact mutation formula, in
  both the map form and the `_proj` exact form. Guards
  `left < right /\ right <= shape.size` identical. Quantifier: universal
  (frozen as strictly stronger than the row's "one pinned valid
  execution"); the pinned-instance residue is P2-1.
- `SF-FG11-DECISIVE`. Frozen `P` conjunct list = committed conclusion,
  item for item (section 5). Frozen `Q` (`v0` = bitwise complement of
  `mem0[8]`; the two runs' `.terminal` differ) = committed
  `packedReviewerDecisiveCellLiveness` with `egcpDecisiveMutantCell`
  checked equal to the complement of the committed cell-8 literal; expected
  mutated terminal `some (some 2)` as frozen in 10.2. One pinned canonical
  valid query; identical `n`, endpoints, driver, controller; only cell `8`
  differs.
- `SF-FG11-UNREAD`. Frozen `P` (cell `4` allocated; absent from the pinned
  trace) and `Q` (complete run-record equality under the frozen `w0`,
  proved through the ordered agreement route, not by computing the mutated
  run separately) = committed theorem exactly; the committed form is
  universal over ALL replacements with the frozen `w0` instance pinned
  separately (`packedReviewerUnreadCellAcceptPinned`), and the proof goes
  through `packedReviewerRunAgainstMemory_eq_of_agree`.
- `SF-M06-BRIDGE`. Frozen `P`/`Q` = committed
  `packedReviewerNoMetadataCompletion` verbatim; quantifier
  `forall f : Nat -> Nat -> Nat -> Option Nat`; guards identical to the
  decisive pair (same two run objects, same endpoints); direction verified
  against the enacted `M06` oracle (`some n`) and the reference-semantics
  oracle — both are instances of the refuted `f`.
- Repaired interfaces: section 5; conjuncts 13/14 checked against the base
  `R2` theorems as the former facts under accurate names.

### Probe 1 — weaken the decisive producer (disposable mutation worktree)

Mutation: `packedReviewerDecisiveCellConnection`'s statement and proof
replaced by the rejected origin-erasing shape — existential position/event
with address `8`, a successful-reply existential, and the run terminal
`some (some 1)`; no invocation fields, no site/segment/index, no pre-state
fold, no transition, no continuation. The weakened producer elaborates
(`ReviewerCapstone` built, 193/194). The independent consumer was left
unchanged. Command: `lake build RMQ.Validation.EGCPFinalFalsification`.
Result: **failure at the literal consumer** —
`error: RMQ/Validation/EGCPFinalFalsification.lean:3236:2: type mismatch`
(the `egcpStageFDecisiveCellConnection` discharge), exit 1 in 172 s.
Restoration: `git checkout` of the file; on-disk SHA256 returned to the
recorded pre-mutation value
(`c0f9a912425827d9337cf061b2520b976cda714c678d5161d32ebe26a75cd1c2`);
`git status --porcelain` empty.

### Probe 2 — reduce `controller_input_boundary` (same worktree)

Mutation: the capstone field reduced to an old-style arity fact
(`(packedReviewerMemory shape).length = packedReviewerCellCount ...`), the
producer's `⟨rfl, rfl⟩` replaced by `packedReviewerMemory_length`; the
validation surface left unchanged. The weakened capstone elaborates
(`ReviewerCapstone` built, 193/194). Result: **failure at the exact-type
consumer** —
`error: RMQ/Validation/EGCPFinalFalsification.lean:2989:35: type mismatch`
(the `controller_input_boundary := capstone.controller_input_boundary`
projection in `egcpStageFCapstoneFactsExact`), exit 1 in 73 s. Restoration:
as probe 1; SHA256 back to the same pre-mutation value;
`git status --porcelain` empty. The added-shape-parameter direction of this
probe was exercised by the replay's own `M03` case on the exact target
(REJECT at `ReviewerCapstone.lean`, surface `exact signature`).

## 7. Executable receipts (all on the exact target, audit worktree, unless stated)

- Registry reconstruction: the runner's sixteen-entry literal array matches
  matrix section 3 in ID, order, mutation description, verdict, and
  named-surface category; the enacted bodies and activation needles match
  section 10.4's frozen cells byte-for-byte on every checked column; the
  base-to-target script delta is exactly the frozen enactments
  (`A02`/`M02`/`M04`/`M13` targets, `M01`/`M14` retargeted from the flat
  source-geometry equation to the executed controller's header decode,
  `M03`/`M08`/`M12` `ExpectFile` moves disclosed in
  `WDD-20260806-003`/`004`, the additive `-SelfTestOnly` mode, and the
  artifact-changing deadline probe). `M05`/`M07`/`M09`/`M10`/`M11` bodies
  are unchanged from the audited base.
- **Full replay, exactly once, on the verified-clean exact target:**
  `FULL MODE PASS`, exit 0, 1494 s. Registry integrity OK (16 ordered, 2
  ACCEPT / 14 REJECT); clean build 2 s; mutated-chain probe 348 s;
  per-case deadline 1392 s; descendant self-test PASS; 16 considered, 16
  as commissioned, 0 target absent. Per-case: `A01` ACCEPT; `A02` ACCEPT
  (activation needle present); REJECTs at exactly the commissioned
  surfaces — `M01` `ReviewerControllerProof.lean`; `M02`
  `ReviewerController.lean`; `M03` `ReviewerCapstone.lean`; `M04`
  `ReviewerController.lean`; `M05` `ReviewerController.lean`; `M06`
  `ReviewerControllerProof.lean`; `M07` `ReviewerControllerProof.lean`;
  `M08` `ReviewerCapstone.lean`; `M09` `Probe.lean`; `M10`
  `SourceGeometry.lean`; `M11` `ReviewerMemory.lean`; `M12`
  `ReviewerCapstone.lean`; `M13` `ReviewerController.lean`; `M14`
  `ReviewerControllerProof.lean`. Activation checks passed on all eleven
  needle-carrying mutants; every mutation restored with a verified SHA256;
  terminal clean-state check passed and `git status --porcelain` empty
  after the run. This independently reproduces the record's section 4
  table surface-for-surface (that run was on the frozen proof/script tree
  `f105971`, whose Lean and script blobs are byte-identical to the
  target's; the target adds documentation only).
- OS self-tests (same committed bytes): Windows PowerShell 5.1
  `-SelfTestOnly` exit 0 in 6 s; WSL `Ubuntu-24.04` under `pwsh 7.6.4`
  `-SelfTestOnly` exit 0 in 14 s; both verified registry integrity and
  pid-verified root-plus-descendant termination. Negative selector probes:
  unknown ID, whitespace selector, and the `-SelfTestOnly`+`-Case`
  combination each fail with the commissioned `REPLAY-FAIL` message and a
  nonzero exit before any build.
- Builds: `lake build RMQ.Validation.EGCPFinalFalsification` exit 0 in
  1396 s (cold worktree; linter notes only); `lake build RMQ` exit 0 in
  377 s (312 targets).
- Axiom inventory: `lake env lean scripts/axiom_check.lean` exit 0 in
  260 s. All six Stage-F entries —
  `packedReviewerStageFCapstone_holds`,
  `packedReviewerHeaderCellAddressLiveness`,
  `packedReviewerDecisiveCellLiveness`,
  `packedReviewerDecisiveCellConnection`,
  `packedReviewerUnreadCellAccept`,
  `packedReviewerNoMetadataCompletion` — depend on exactly
  `[propext, Classical.choice, Quot.sound]`; zero `sorryAx`,
  `ofReduceBool`, or `trustCompiler` occurrences anywhere in the
  1156-entry inventory. The script delta adds exactly these six
  `#print axioms` lines.
- Strict scans: `design_decision_check.ps1 -Strict -Base 0f38672...` PASS
  ("checked 12 changed files (5 code, 5 workflow, 3 neutral)");
  `claim_drift_scan.ps1 -Strict` "1517 hits, 0 strict failures" (the
  policy/allowlist classifications on Stage-F wording were inspected, not
  trusted from the exit code; all Stage-F-relevant hits are
  `[allowed]`/`[review]` classifications, none a strict violation);
  hygiene scan (`sorry|admit|axiom|unsafe|opaque|implemented_by|partial|`
  `extern|noncomputable` + `import Mathlib`) 0 matches over `RMQ` and
  `lakefile.toml`; `native_decide|Lean.ofReduceBool` 0 matches over `RMQ`;
  `git diff --check 0f38672..9687b4a` exit 0.
- Frozen-row bytes (strict, per `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`):
  base matrix blob 119,297 bytes (SHA256
  `d8e41cde45542f1af9fb09104f4c232d2d1ac42d9a15047d69454123edd188d7`),
  target 152,169 bytes (SHA256
  `94e48379aaaa562f6594e591deac0e7c03e9196ad5e4866b9229eb8e695706b2`);
  both strict-UTF-8 decodable, BOM-free, LF-only, no mojibake; the base's
  508 lines are a byte-exact prefix of the target; row mapping by stable
  ID: 0 missing, 0 duplicated beyond the pre-existing section 7.3 pattern,
  0 changed; every added row inside the appended section 10 (lines
  509-830). Post-freeze matrix delta (`8d22684..9687b4a`): exactly the
  eleven `SF-CHK-01`..`SF-CHK-11` outcome cells. The two authorized
  semantic corrections (`R1` in 10.3, `R2` in 10.5) are declared in the
  section 10 preamble and live entirely inside the appended amendment;
  within this repository the matrix change is pure append plus the 10.8
  outcome column. No unauthorized drift.
- Per-commit lifecycle: strict design-decision check at each exact parent
  PASS for all five commits (`8d22684`: 3 files 0/2/1; `c1eada6`: 5 files
  2/1/2; `37764ad`: 7 files 4/2/2; `f105971`: 2 files 0/1/1; `9687b4a`:
  4 files 0/2/2, run detached). The contract precedes proof code (matrix
  section 10 frozen in the first commit; Lean lands in commits two and
  three). Every workflow-sensitive commit carries its own same-commit
  entry: `WDD-20260806-001`..`005` in order, each accurate against the
  diff it governs; `DD-20260806-076`/`077` land with their code. No late
  ledger entry exists on this branch.
- Aggregate `scripts/gate.ps1`: not run. Every changed surface and
  acceptance row above is covered by a named focused check (builds, axiom
  inventory, replay, scans, byte comparison, lifecycle checks); a
  duplicate aggregate run on the unchanged tree adds no unique coverage.
  This reasoning was re-derived independently and happens to coincide with
  ledger row `SF-CHK-11`.

## 8. `EG-CP-F12` independent inventory

Independent enumeration of the Stage-F theorem surface from the delta (not
from the record): `ReviewerCapstone.lean` contributes the capstone
structure and producer; nine header-liveness lemmas plus the universal
theorem, its `_proj` corollary, and the opening pin; twelve
boundary-instance theorems; two uniformity `rfl` pins; the fixture literal
pins (shape, size, bpCode, longCount, sparseCount, width, chunk bits, cell
count, allocation, measure, fringe/select/access/close-directory tables,
payload, header, padded bits, memory); the five fixture deliverables
(memory literal, terminal, 68-address trace, decisive event 11, mutant
terminal); the drive-step/prefix-fold apparatus (five declarations plus
`packedReviewerDriveAux_decompose`); the decisive liveness/connection pair;
the unread-cell pair plus the frozen replacement-cell definition; and the
`M06` bridge. `RMQ/Validation/EGCPFinalFalsification.lean` adds the
signature pin, the fourteen-field facts structure with its exact projection
discharge, and twelve `egcpStageF*` consumers. `Boundaries.lean` adds five
neighbour facts. Every declaration exists on committed bytes and has a
named consumer (validation root, replay case, or the connection theorem).
Remaining focused proof-days: **zero up to the P2-1 one-liner**. Non-proof
downstream consumers, separately: coordinator reconstruction of this exact
candidate; this fresh-blind audit; the `FEASIBILITY_PASS` decision; the
Stage-A matrix freeze and campaign; public-claim synchronization; `S1` and
`V1`. No unknown dynamic input: the controller receives exactly
`(n, left, right)` (exact-type pin), memory enters only at the driver (run
factorization), and both decoded counts are charged reads of the counted
memory.

## 9. Stale or rejected objections

- "The decisive theorem hides its provenance in the proof term." Rejected:
  every `R1` component is a conclusion conjunct (section 5); probe 1 shows
  the origin-erasing form no longer inhabits the consumer's literal type.
- "The capstone's boundary conjunct is the old length/store facts under a
  new name." Rejected: conjunct 12 is the eta-equation plus the run
  factorization; the former facts are conjuncts 13/14 under accurate
  names; probe 2 and replay `M03` fail exactly where they must.
- "`M06` never refuted a real reference oracle." Rejected as stated: the
  literal oracle is untypeable in the closed controller (no `xs` or shape
  in state or driver — verified at the inductive definitions), and the
  committed bridge refutes EVERY metadata-only completion including the
  reference instance; matrix 10.4 itself forbids citing `M06` alone.
- "Aggregate trace inequality stands in for value liveness." Rejected: the
  decisive inequality is at `.terminal`; the header inequality is at the
  `trace[1]` address projection; the unread accept is complete run-record
  equality.
- "The 16/16 pass could rest on vacuous mutants or wrong surfaces."
  Rejected: every mutation body was read against its frozen 10.4 cell;
  activation needles are mechanical and checked in the written bytes;
  the `ExpectFile` moves are disclosed and correct — the capstone IS the
  honest first failing consumer of `M03`/`M08`/`M12` once the validation
  root imports it (`M08`'s fuel lemma diverges under a stored `427`;
  `M12`'s certificate-projecting producer fails on `True` projections);
  the independent full replay reproduced all sixteen commissioned
  outcomes at their surfaces. Residual nuance: P3-4.
- "`427` is a stored cap." Rejected: it is the proved bound of the
  structural measure (`packedReviewerControllerMeasure_start_le_427`), and
  replay `M08` REJECTs the stored-number substitution.
- "The boundary campaign might dispatch to a second representation."
  Rejected: one universal quantifier instantiates every boundary case; the
  controller entry and memory builder are single `rfl`-pinned definitions;
  the readiness clause moves across `[1024, 1330]` (including the new
  interior neighbours `1025`/`1329`) while the capstone statement does not.
- "The certification replay ran on `f105971`, not the final commit."
  Not an objection after checking: the final commit is documentation-only
  over byte-identical Lean/script blobs, and this audit's own full replay
  ran on the exact target `9687b4a` and passed 16/16.

## 10. Roadmap alignment and best next action

Letter: the candidate executes exactly step 1 of the roadmap's "exact next
sequencing" (`FG-11`; full `FG-12` with the four previously-null targets
`A02`/`M02`/`M04`/`M13` enacted and all sixteen certified in one campaign;
`FG-14`; `FG-15`), and this audit is part of step 2. Spirit: the repair
addresses precisely the defects the rejection commissioned (`R1`-`R4`) by
strengthening propositions rather than relabeling evidence; the two
contract corrections are strengthenings landed before any proof code.
Local-candidate completion is kept strictly separate from Stage-F/EG-CP
closure everywhere (record section 8, worklog boundary, matrix 10.9);
nothing records `FEASIBILITY_PASS`, Stage-A state, publication, or
public-claim changes.

Best next coordinator action: reconstruct this exact candidate and
disposition `P2-1` — either commission the one-line pinned-instance
corollary plus the concrete moved-second-address literal as a
micro-follow-up, or record the universal theorem as superseding that frozen
cell — then, if accepted, record the Stage-F outcome under the
`FEASIBILITY_PASS` rule and only then freeze the Stage-A matrix.

## 11. Report identity

This report is the single permitted write of audit
`EG-CP-STAGEF-AUD1`, committed alone on branch
`audit/eg-cp-stagef-close-r2-aud1-fresh-blind` with parent exactly
`9687b4ad4f3cb8c843625dc2ffbb486cdecb6b5f`. Post-commit checks (strict
claim drift, strict design-decision check against the exact target,
`git diff --check 9687b4a..HEAD`, UTF-8 inspection, final cleanliness) are
run after the commit and reported to the coordinator with the exact commit,
tree, and parent identities; per protocol, the report does not embed its
own commit hash.

# Fresh-blind audit: Stage-A packed-architecture capstone `EG-CP-STAGEA-CLOSE-R1` (AUD1)

Auditor: `EG-CP-STAGEA-AUD1` (fresh blind delta, report-only).
Date: 2026-08-06 (reconstruction and all Lean/replay evidence); the final
report-sensitive gate receipts in section 7 were taken 2026-08-07, when the
session crossed midnight. The filename keeps the commissioned 2026-08-06 date.
Durable report: `docs/internal/audit_reports/2026-08-06_EG_CP_STAGEA_CLOSE_R1_fresh_blind.md`.

This report records what an independent fresh session observed on the exact
target. It is an audit recommendation only. It records no coordinator or owner
action: no acceptance, no architecture acceptance, no merge-readiness
decision, no integration, no `FEASIBILITY_PASS`-style status, no public-claim
synchronization, no `S1`, no `V1`, and no roadmap closure.

---

## 1. Scope

| Item | Value |
| --- | --- |
| Mode | FRESH BLIND DELTA, report-only |
| Auditor handle | `EG-CP-STAGEA-AUD1` |
| Base | `270d78559adc33fe872b6d17bd54d8e51567a605`, tree `7b872cf144503cebf61097f857fa779081076107` (verified) |
| Target | `ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23`, tree `d1cb298705b41094c8dad3b7efa23bb6698fc7e5` (verified) |
| Frozen proof/replay tree | `1198ff6fbd66a4de991ad7e8fe1235a452d4b337`, tree `35327c3077ef3d6d5111159668518d960d1467bd` (verified) |
| Matrix-freeze commit | `f4107cd15173fef690ba05e51becb9c65b6c7d60`, matrix blob `719c01d1e182d3288eebc9427bb21f16b4d414f7` |
| Branch | `codex/eg-cp-stagea-close-r1` (unmerged, unpushed) |
| Roadmap node | `docs/internal/RMQ_ENDGAME_ROADMAP.md`, Stage A packed architecture acceptance |
| Audit worktree | detached copy of the target at `C:\Users\poin\Documents\RMQ\.claude\worktrees\stagea-packed-arch-audit-3f7f78` (the worker's worktree was never touched) |
| Platform | Windows 11, Windows PowerShell 5.1, `leanprover/lean4:v4.22.0` |

Load-bearing surfaces audited:
`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean`,
`RMQ/Validation/EGCPStageA.lean`, `scripts/eg_cp_stagea_replay.ps1`,
`RMQ.lean`, `scripts/axiom_check.lean`,
`docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md`, and the two decision
ledgers (`DD-20260806-079`, `WDD-20260806-008`..`-011`).

Acceptance criteria applied: the thirteen criteria of the commissioning
prompt (one object; complete allocation; one query-independent width; header
sufficiency and liveness; probe semantics with the two-probe crossing; a
derived, upper-bound-only `427`; universal valid-query correctness through
the canonical chain with an independent leftmost-tie specification;
invalid-domain behaviour under one shared guard; uniformity; no assumed
capstone; a consumer that really pins the proposition; a real campaign; and a
contract frozen first).

**Two-phase reading order: followed.** Phase 1 reconstructed the
requirement-to-evidence matrix from the frozen contract
(`EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` sections 1-7, plus section 8 read as a
permitted evidence location whose worker status words were treated as
self-assessment), the Stage-A table of `RMQ_ENDGAME_ROADMAP.md`, the Lean
source, the runner, and the Git objects. Every Phase-1 disposition and every
residual named in section 3 below was written down (auditor scratchpad
`phase1_dispositions.md`, outside the repository) **before**
`EG_CP_STAGEA_RESULT.md`, `EG_CP_STAGEA_WORKLOG.md`,
`audit_packets/EG_CP_STAGEA_AUD1_PACKET.md`, and the Stage-A entries in
`AUDIT_AND_A_DESIGN.md` / `DIGESTION_LOG.md` were opened. Those five
narrative surfaces were then read in Phase 2 and audited for overstatement;
`P2-1` below is a Phase-2 finding and could not have influenced the Phase-1
matrix.

Project-skill preflight (run before substantive work, from the repository
root, at the target checkout):

```
SKILL-PREFLIGHT: governance=f0c7232a8a52b8d61ead5e96d72a8a849bc094b5
SKILL-PREFLIGHT: checkout=ec35b5d9f513f639cb75044a5d1ea52e8dfc3d23
SKILL-PREFLIGHT: expected=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: checkout_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: working_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: runtime_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: required=<none>
SKILL-PREFLIGHT: required_mode=explicit-no-role
SKILL-PREFLIGHT: PASS
```

`-RuntimeProjectSkills` listed this session's actual RMQ catalog. No skill was
named to satisfy the check; `-AllowNoRequiredSkills` was used because an audit
worker has no repo-local role skill.

---

## 2. Verdict

**`merge-ready with follow-up`.**

The proof surface, the consumer, the frozen contract, and the replay harness
reconstruct independently. No rejection condition of the commissioning prompt
holds: no capstone field quantifies over a different object; the allocation
bound charges the header cell and the padding; the cap is derived, never
stored, and no document promotes it to attainment; correctness is universal
and its leftmost-tie connection routes through an independent specification;
the consumer does **not** survive a weakening of a public conjunct (I broke it
myself); no frozen matrix row differs by a byte from `f4107cd`; no forbidden
token is reachable; and the candidate claims nothing beyond
`CANDIDATE_COMPLETE` for `A01`-`A12`.

The follow-up touches governance and documentation, never the proof. The one
`P2` is that a documentation-only commit in the candidate lineage (`ea08f28`)
fails the per-commit design-decision gate at its own parent; the worker
disclosed this without excuse and repaired the tip, but the failing commit
remains reachable, so a coordinator must choose a remedy **before**
integration rather than after. The five `P3` items are precision and
completeness defects, one of which (`P3-3`) names a short corollary that would
make `EG-CP-A07` readable from the combined proposition alone. Consistent with
`WDD-20260805-003` (report defects are corrected before integration), all six
should be dispositioned before any acceptance record.

---

## 3. Findings, `P0` -> `P3`

### `P0` — none

No proof or trust invalidity, and no artifact corruption. `lake build RMQ`,
`lake build RMQ.Validation.EGCPStageA`, and
`lake env lean scripts/axiom_check.lean` all pass on the exact target; the
curated inventory contains zero non-standard axioms across all 1191 entries.

### `P1` — none

No material overstatement of a proof claim, no failed required Lean gate, and
no misleading theorem surface. Every field of the 38-field proposition is
enacted verbatim as frozen in matrix section 1.1, over the identical objects,
and each is a real consequence rather than a weaker projection (section 5).

### `P2`

**`P2-1`: the per-commit design-decision requirement is violated by a commit
in the candidate lineage.**

The governing rule (`WDD-20260726-007`, restated in the frozen matrix's
`SA-CHK-09`) is that each commit on the branch passes
`scripts/design_decision_check.ps1 -Strict -Base HEAD~1` at its own parent.
Running that at each commit of `270d7855..ec35b5d` in a detached worktree:

| Commit | Result |
| --- | --- |
| `f4107cd` | PASS (`only neutral decision/evidence/history/report paths changed`) |
| `08dd29d` | PASS (`checked 8 changed files (4 code, 2 workflow, 3 neutral)`) |
| `1198ff6` | PASS (`checked 3 changed files (0 code, 1 workflow, 2 neutral)`) |
| `ea08f28` | **FAIL, exit 1** (`workflow/process-sensitive paths changed; update docs/internal/WORKFLOW_DESIGN_DECISIONS.md` — `AUDIT_AND_A_DESIGN.md`, `audit_packets/EG_CP_STAGEA_AUD1_PACKET.md`, `EG_CP_STAGEA_RESULT.md`; `strict mode found 1 missing design-log updates`) |
| `c38e885` | PASS (`checked 7 changed files (0 code, 3 workflow, 4 neutral)`) |
| `ec35b5d` | PASS (`checked 7 changed files (0 code, 3 workflow, 4 neutral)`) |

`ea08f28` is an ancestor of the target (`git merge-base --is-ancestor
ea08f28 ec35b5d` succeeds), so the failure is in the candidate's own history,
not in a discarded branch. The repair was a paired revert (`c38e885`) plus
re-land (`ec35b5d`), which fixes the tip but leaves the failing commit
reachable: merging the branch as it stands puts a commit into permanent
history that does not satisfy a stated per-commit requirement.

This is `P2` and not higher because it is documentation-only (the three
commits above `1198ff6` change no Lean, no script, and no frozen matrix row),
because the worker disclosed it prominently and without excuse in
`EG_CP_STAGEA_RESULT.md:251` ("The first report landing `ea08f28` FAILED this
per-commit check ... -- not excused") and recorded the `EV-A13` correction and
`WDD-20260806-011`, and because it has a clean merge-time remedy: squashing
the three documentation-only commits leaves the tree identical and removes the
failing commit. It is `P2` and not `P3` because it is a violated hard
requirement of the branch contract rather than a wording defect, and because
the remedy must be chosen *before* integration — afterwards it needs a history
rewrite.

### `P3`

**`P3-1`: the disclosure of `P2-1` did not propagate to the auditor-facing
packet.** The packet blob is byte-identical between `ea08f28` and `ec35b5d`
(`e59c53eb3f436e53e3d0c2d82fc833ea96ce4f16`): the correction landed in
`EG_CP_STAGEA_RESULT.md` and matrix section 8 but not in
`docs/internal/audit_packets/EG_CP_STAGEA_AUD1_PACKET.md`, which still reads

> `design_decision_check.ps1 -Strict -Base 270d7855...` | PASS exit 0 ...;
> per-commit `-Base HEAD~1` PASS at every commit

To be fair to the worker: that row sits under the heading "5. Check receipts
**on the frozen candidate**", whose preamble scopes every receipt to
`1198ff6`, and every commit up to and including `1198ff6` does pass. Read with
its scope, the sentence is true. The defect is one of completeness, not
accuracy — and it matters because the packet's own opening tells the auditor
that "the worker's result report ... should be withheld until the auditor has
independently reconstructed the proof surface". An auditor who follows that
instruction and reads only the packet gets no signal that a commit in the
lineage the packet itself identifies (section 1 names the report commit) fails
a governance gate. `EG_CP_STAGEA_WORKLOG.md:105` ("strict design check PASS
(full range and per-commit)") and the round-log entry in
`AUDIT_AND_A_DESIGN.md` carry the same unqualified wording.

In practice this did not mislead me: a fresh-blind reconstruction reads the
frozen contract and the Git objects, and I found the failure independently
before opening any narrative surface. But the packet should carry the same
sentence the result report does.

**`P3-2`: three registry entries the frozen contract labels *semantic* carry
no activation needle, contradicting the frozen `EG-CP-A12` evidence cell.**

Matrix section 1's `EG-CP-A12-REPLAY` evidence cell requires "mechanical
activation needles on every semantic mutant (`WDD-20260805-002`)", and
`EG_CP_STAGEA_RESULT.md:209` reports "Activation checks passed on every
semantic mutant (`WDD-20260805-002` needles present and used)". Extracting the
runner's registry literal and tabulating it:

| Entry | Section-4 label | `Activation` needles |
| --- | --- | --- |
| `SA-M04-ALLOCATION-HEADER-CELL-DROP` | semantic | **none** |
| `SA-M09-CROSSING-SWAP` | semantic | **none** |
| `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` | semantic (public proposition weakening) | **none** |
| `SA-M11-FORGED-PROBE-CAP` | structural | none (consistent with its label) |
| `SA-M14-SHAPE-PARAMETER` | structural | none (consistent with its label) |
| the other 15 patch entries | semantic / control | 1-2 needles each |

(21 entries = `SA-A01`, which patches nothing, plus the 5 needle-less entries
above, plus 15 with needles.)

This is directly observable in my own full-mode run: the log emits
`activation check passed (N needles present and used)` before the build for
every entry that declares needles, and emits no such line for `SA-M04`,
`SA-M09`, `SA-M18`, `SA-M11`, or `SA-M14`.

It cannot produce a false PASS. `Invoke-RegistryCase` requires the anchor to
occur **exactly once** (`ANCHOR-DRIFT` otherwise), the replacement text
differs from the anchor in all three cases (I checked each), an inert mutation
would build and be recorded `UNEXPECTED-ACCEPT`, and the verdict is further
gated on the diagnostic naming the frozen `ExpectFile`. So the *safety*
property the needles exist to protect is delivered by other means. What is not
delivered is the frozen cell's literal claim, and `SA-M09` in particular has
an obvious distinctive needle (`[bit / packedReviewerCellWidth n + 1, bit /
packedReviewerCellWidth n]`) that was simply not declared.

**`P3-3`: the combined proposition never states that a *valid* query's answer
is an index.** Field 28 pins `run.terminal = some (SuccinctClassic.queryTraceResult
xs left right).value` unconditionally, and field 29 is conditional:

```
leftmost_tie_universal :
  left < right -> right <= shape.size ->
    ∀ index, run.terminal = some (some index) -> LeftmostArgMin xs left right index
```

Nothing in the 38 fields, and nothing in `EGCPStageAArchitectureFacts`, says
that for a valid query the terminal *is* `some (some index)`. A reader of the
capstone alone therefore cannot conclude that the packed machine answers valid
queries at all; the machine could, as far as the combined proposition is
concerned, answer `none` everywhere provided the reference did too.

This is a legibility gap, **not** a soundness gap. The reference
`SuccinctClassic.queryTraceResult` is the accepted classic reference, untouched
by this candidate, and `SuccinctClassic.queryCosted_exact` /
`scanWindow_leftmost` (`RMQ/Core/SuccinctRMQClassic.lean:1486`) already give
`(queryCosted xs left (left+len)).erase = some (scanWindow xs left len)` for
`0 < len` and `left + len <= xs.length`. Composing that with field 28 yields
the completeness statement in a few lines. But no registry case would catch a
regression here, and no conjunct displays it.

It is worth recording that this is a direct answer to the worker's own open
audit question 7 ("Is anything reviewer-facing true of the packed machine but
absent from the combined proposition?") and to the result report's own
"what a skeptical graduate student should ask next". Per the commissioning
prompt's rule, that language is presumptive evidence of incomplete closure for
the criterion it concerns — here, `EG-CP-A07` read as a self-contained
statement.

**`P3-4`: `REPLAY-SELECTOR-NONVACUITY`'s frozen "exit 2" is not reproducible
for `-Case ''` under the literally documented invocation form.** Matrix
section 3 freezes "`-Case <unknown>`, `-Case ''`, `-Case '   '` exit 2 before
any build". Observed on this platform:

| Invocation | Result |
| --- | --- |
| `powershell -File ...replay.ps1 -Case 'SA-M99-NOT-A-CASE'` | exit 2, `unknown or non-unique case selector` |
| `powershell -File ...replay.ps1 -Case '   '` | exit 2, script's own guard |
| `powershell -File ...replay.ps1 -Case ''` | **exit 1**, PowerShell's binder: `Missing an argument for parameter 'Case'` |
| `& ...replay.ps1 -Case ''` (direct) | exit 2, script's own guard |
| `powershell -File ...replay.ps1 -Case '""'` | exit 2, script's own guard |
| `-Case` + `-IntegrityProbe`, `-SelfTestOnly` + `-Case`, bogus probe | exit 2 each |

Every form fails closed before any build, so the substance of the contract
holds; PowerShell 5.1's `-File` argument parser simply consumes a truly empty
argument before the script sees it. The worker reports this accurately
(`EG_CP_STAGEA_RESULT.md:169` and `:226-229`, worklog checkpoint 3). The
imprecision is in the frozen cell's wording, which cannot now be edited, so it
should be read with the worker's qualification attached.

**`P3-5`: matrix section 8's `EV-A13` correction says the report record was
"re-landed identically", which is true of four of the six report files but not
all.** `git diff ea08f28..ec35b5d` shows three changed files:
`EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` (the `EV-A13` correction itself),
`EG_CP_STAGEA_RESULT.md` (two rows: the report-record-chain row and
`SA-CHK-09`), and `WORKFLOW_DESIGN_DECISIONS.md` (`WDD-20260806-011`). The
packet, worklog, round-log, and digestion entries **are** byte-identical. The
differences are precisely the disclosure of the correction being described, so
this is self-referential wording rather than a concealed change — but "re-landed
identically" is literally false and a reader checking it will find a diff.

---

## 4. Evidence tier for every positive claim

| Claim | Tier |
| --- | --- |
| All 38 fields hold over the identical `memory`/`run`/`controller`/`w` terms | kernel theorem (`packedReviewerArchitectureCapstone_holds`, axiom-checked) |
| The independent consumer restates and is discharged by all 38 fields | kernel theorem (`egcpStageAArchitectureFactsExact`) |
| `memory.length * w <= 2 * n + packedReviewerRho n` with `LittleOLinear packedReviewerRho` | kernel theorem (`packedReviewerMemory_length_mul_width_le`, `packedReviewerRho_littleO`) |
| `packedReviewerCellWidth 0/1/2/3 = 10/14/14/15` | kernel theorem (kernel-checked literals, `simp +decide`) |
| Universal header-address liveness at trace position 1 | kernel theorem (`packedReviewerHeaderCellAddressLiveness_exact`) |
| `run.trace.length <= 427` and `measure = 1 + 2*3 + 2*210 = 427` | kernel theorem (`..._trace_length_le_427`, `packedReviewerControllerMeasure_valid_eq_427`, plus a definitional `rfl` decomposition) |
| Leftmost tie via the independent `LeftmostArgMin`/`scanWindow` specification | kernel theorem (`packedReviewerRunLeftmostTie` -> `queryCosted_leftmost` -> `scanWindow_leftmost`) |
| Reachable-state base/step/final invariant at the literal run | kernel theorem (`packedReviewerRunReachableInvariant` via `packedReviewerDriveAux_decompose`) |
| Decisive-cell corruption at `.terminal`; unread cell 4 accept; metadata bridge | kernel theorem at the frozen fixture (`packedReviewerDecisiveCellLiveness`, `..._UnreadCellAccept`, `..._NoMetadataCompletion`) |
| No non-standard axiom reaches any curated entry | artifact (`lake env lean scripts/axiom_check.lean`, exit 0, 1191 entries parsed) |
| Consumer discriminates a single weakened public conjunct | executable validation (auditor probes `AUD-CF-1`, `AUD-CF-2`, `AUD-CF-5b`) |
| Padding and the two-probe crossing are load-bearing | executable validation (auditor probes `AUD-CF-3`, `AUD-CF-4`) |
| Frozen rows byte-identical to `f4107cd`; whole prefix above section 8 identical | executable validation (auditor's own strict-UTF-8 checker + 6 firing negative controls) |
| Runner registry equals matrix section 4 (IDs, order, verdicts, `ExpectFile`) | executable validation (registry literal extracted and tabulated) |
| 21/21 replay verdicts at the frozen surfaces | executable validation (auditor's own full-mode run — section 7) |
| Selector, integrity-probe, and descendant-termination controls | executable validation (auditor-run) |
| Freeze-before-code; documentation-only above `1198ff6`; Stage-F runner and claim policy untouched | artifact (Git object identities) |
| Per-commit design-decision discipline | artifact (per-commit runs; one FAIL, see `P2-1`) |
| Category separation, honest labels, lifecycle wording | process (report review against the frozen rows) |

---

## 5. Independent ID-by-ID reconstruction

### 5.1 Requirement rows

**`EG-CP-A01-ONE-OBJECT` — SATISFIED.** Every one of the 38 fields opens with
`let shape := SuccinctClassic.cartesianShape xs` and names the literal
`packedReviewerMemory shape` and
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left right`.
Fields 1-5 are the composition chain: `payload_is_buildPayload`
(`= SuccinctClassic.buildPayload xs`), `serialized_header_payload` (`rfl`),
`padded_final_padding` (final `false` padding plus the length identity),
`memory_uniform_builder` (the single uniform chunking expression), and
`run_factorization` (`rfl`: the run *is* the drive of the closed controller
against that memory). I searched both new modules for the flat universe —
`packedMemory`, `packedCellWidth`, `packedRho`, `packedPayloadBits`,
`packedCellCount`, `packedSerializedBits`, `packedPaddedBits` — and found zero
occurrences (`rg` exit 1). My probe `AUD-CF-2` confirms the separation is
enforced, not merely observed: substituting the flat `packedRho` for
`packedReviewerRho` in field 9 breaks the committed consumer.

**`EG-CP-A02-SPACE` — SATISFIED.** `packedReviewerCellCount n lc sc = 1 +
selectCeilDiv (packedReviewerPayloadLength n lc sc) (packedReviewerCellWidth n)`
— the `1 +` is the header cell and the ceiling division charges the final
partial cell at full width, so the bound is on allocated capacity, not a
serialized length. `packedReviewerAllocatedBits = cellCount * w`, field 8 is
`memory.length * w <= 2 * shape.size + packedReviewerRho shape.size`, and
`shape.size = xs.length` by `packedReviewerCartesianShape_size`. The residual
`packedReviewerRho n = concreteBPNativeSuccinctRMQCanonicalReviewerOverhead n
+ 2 * packedReviewerCellWidth n` is proved `LittleOLinear`, and
`LittleOLinear` (`RMQ/Core/SuccinctSpace/Asymptotics.lean:22`) is a genuine
`forall scale, 0 < scale -> exists threshold, forall n >= threshold, scale *
f n <= n`, not a placeholder. Probe `AUD-CF-3` (deleting the padding term from
`packedReviewerPaddedBits`) fails at
`PackedCellProbe/ReviewerMemory.lean:135` and `:196`.

**`EG-CP-A03-WIDTH` — SATISFIED.** `packedReviewerCellWidth : Nat -> Nat` is
size-only by signature, and the validation root pins that signature
(`egcpStageAWidthSignature`). Fields 11-15 give the explicit all-size bounds:
`0 < w`, `n < 2 ^ w`, `w <= 20 * (Nat.log2 (n + 2) + 1)`, header exactly one
`w`-bit cell, and both decoded header fields `< 2 ^ w`. Cells are field 6;
allocation is field 8; trace addresses are field 22 (`< 2 ^ w`, the modelled
word, not a host array bound); the dead/sentinel address is the certificate
field `dead_address_width`
(`(packedInteriorOffsets shape.size).deadAddress < 2 ^ w`) re-pinned by
`egcpStageADeadAddressWidth`. Small sizes are kernel-checked at `10/14/14/15`.

**`EG-CP-A04-HEADER-SUFFICIENCY` — SATISFIED.** Field 19 is the universal
three-conjunct liveness, not a header equality and not a decorative read: for
every shape and every valid endpoint pair, the canonical run's *second*
attempted address (`trace.map (·.request.address))[1]?`) is the `.rankSuper`
cell at `longCount shape`, the run against the memory with **only cell 0
replaced** by the same-width encoding of `longCount + w` has second address
the `.rankSuper` cell at `longCount + w`, and the two differ. The inequality
is at the address projection, never at an enclosing run record. Fields 16-18
supply the header cell, its decoding, and the opening probe at address `0`.
The `10 -> 37` fixture instance is re-pinned in the validation root as
`egcpStageAHeaderLivenessFixture`, and I cross-checked it against the
kernel-evaluated literal trace: `egcpAddrsLit[1] = 10`.

**`EG-CP-A05-PROBE-SEMANTICS` — SATISFIED.** Field 20 makes every reply
literally `memory[event.request.address]?`; field 21 gives in-range totality
(the invalid branch has an empty trace, so this covers every valid query's
attempted probes); fields 22-23 bound the address and pin the exact reply
width; field 24 (`PackedReviewerRunGrouping`) is a full trace **identity**
against `packedReviewerExpectedPhysicalTrace`, so order and multiplicity are
preserved, not merely counted. Field 25 pins the conditional plan exactly:
zero-width issues nothing, a contained span issues `[bit / w]`, and a span
crossing a boundary issues `[bit / w, bit / w + 1]` — two ordered probes. I
verified that the plan is not decorative: every branch of the controller's
plan functions routes through `packedReviewerProbePlan` (prelude via
`packedReviewerSparsePreludeRequestPlan`; logical segment 20 via
`packedReviewerInteriorLocationPlan`; segments 21/22 directly; segments < 20
via `packedReviewerLegacyRawPlan`). Probe `AUD-CF-4` (collapsing the crossing
branch to one probe) fails at `PackedCellProbe/ReviewerProbe.lean:139`, `:220`,
`:332`, `:380`.

**`EG-CP-A06-PROBE-CAP` — SATISFIED as an upper bound only.** The cap is
derived, not stored. `packedReviewerControllerMeasure` at
`.header n left right` is *definitionally*
`1 + 2 * packedReviewerSparsePreludeRemaining (packedReviewerSparsePreludeInit n 0)
+ 2 * packedReviewerWholeRemaining (packedReviewerWholeStart n left right)`;
field 5 shows that this measure is the fuel actually supplied to the driver;
`packedReviewerDriveAgainstMemoryAux_trace_length_le` bounds the trace by the
fuel; and field 27's four conjuncts pin the decomposition, `= 3`, `= 210`, and
`= 427`. The first conjunct is closed by `rw [hcontroller]; rfl`, so it holds
only against the derived form. I checked every candidate document for
promotion of `<= 427` to attainment, tightness, or impossibility of a smaller
cap: none. The matrix, the result report, the digestion entry, and the module
docstring all state explicitly that `427` is an upper bound (the fixture run
issues 68), that `210` is logical fuel, and that no attainment is claimed
(`B7-UPPER-BOUND-IS-NOT-ATTAINMENT`). `EG_CP_STAGEA_RESULT.md:342` says the
`o(n)` envelope is "proved but loose; tightness is not claimed".

**`EG-CP-A07-CORRECTNESS` — SATISFIED in letter; see `P3-3` for the one
statement-level residual.** Field 28 is universal in `xs, left, right`
(the producer quantifies over all three) and runs through the named chain
`packedReviewerRunAgainstMemory_eq_lowered` ->
`packedReviewerDriveLoweredWhole_210_simulates_packedWholeQueryRun` ->
`packedWholeQueryRun_eq` -> `packedReviewerPackedReference_eq_public` ->
`SuccinctClassic.queryTraceResult`. It is not a fixture set, not an
aggregate-trace inequality, and not a post-hoc answer comparison. Field 29
connects to `LeftmostArgMin` (`RMQ/Core/Spec.lean:34`), a purely list-based
specification with no dependence on the implementation under test, via
`queryCosted_leftmost` -> `scanWindow_leftmost`. The duplicate-minimum fixture
`[7, 3, 3] (0, 3) -> some 1` is a boundary instance, correctly described as a
witness only.

**`EG-CP-A08-INVALID-DOMAIN` — SATISFIED.** Field 30 gives the exact invalid
run (`terminal = some none`, `failed = false`, `.done none`, `trace = []`) and
field 31 gives the reference's agreement, so the unconditional field 28 is not
weakened and every guarded field uses the identical guard
`left < right /\ right <= shape.size`. The boundary campaign in the validation
root instantiates the one universal producer at the empty representation, the
singleton, both size-two shapes (with `egcpStageASizeTwoDistinct` witnessing
that they really are distinct shapes), the long-crossover triple
`5487/5488/5489`, the interior-readiness six, four invalid queries, and the
duplicate-minimum fixture — no per-size variant or readiness dispatch exists
to select, and `egcpStageANoSecondRepresentation` pins that.

**`EG-CP-A09-UNIFORMITY` — SATISFIED.** I expanded
`PackedReviewerControllerState`: its constructors carry only `n`, the
endpoints, decoded counts, fixed-protocol counters, and replies already
supplied. No shape, no list, no store, no oracle, no proof field. Memory
appears only in `packedReviewerDriveAgainstMemoryAux`, and field 5 exhibits
that factorization. Field 32 is the exact-type input boundary (it elaborates
only at `Nat -> Nat -> Nat -> PackedReviewerControllerState`), field 33 the
uniform entry, field 34 ordered store-agreement determinism. Five signature
pins in the validation root back this structurally.

**`EG-CP-A10-NO-ASSUMED-CAPSTONE` — SATISFIED.** Field 35 is the explicit
reachable-state invariant at the literal run, instantiating
`packedReviewerDriveAux_decompose`: at every trace position the *driver's own*
prefix fold `packedReviewerDriveStateAt` is live, emits the request, the
recorded event is that request paired with the driver's own lookup, and the
drive restarted at the fold reproduces the terminal, state, and trace suffix
(base, step, and continuation). Field 36 is corruption rejection at the
`.terminal` projection specifically. Field 37 is the proved-unread-cell
expected-ACCEPT control, discharged through the *ordered agreement route*, so
it is value-independent — which is exactly why patching the replacement value
(`SA-A02`) must still ACCEPT. Field 38 is the metadata-completion bridge over
all `f : Nat -> Nat -> Nat -> Option Nat`.

I cross-checked the fixture literals rather than trusting the labels:
`egcpMemLit` has 22 cells of exactly 15 bits; `egcpAddrsLit` has 68 entries
(matching the "68 attempted probes" claim), its entry 1 is `10` and its entry
11 is `8`, and it never contains `4` (so cell 4 really is unread);
`egcpDecisiveMutantCell = [true×10, false, true×4]` is the exact bitwise
complement of canonical cell 8 (`[false×10, true, false×4]`), so
`SA-M17`'s "set the mutant to the canonical value" is a real neutralization
that must be rejected. `egcpStageADecisiveCellConnection` re-pins the
occurrence-level provenance in the *conclusion*: position 11, the
`wholeQuery` origin, the `leftSelect` instruction with both invocation
arguments `0`, the `entryFirstOffset` read site, segment `8`, index `0`,
address `8`, the reply as the driver's own lookup, the folded pre-state, the
`nextRequest`/`consumeReply` transition, and the checked continuation to
`.done (some 1)`. That is instruction, invocation parameters, folded pre-state,
and position — not `List.Mem` alone.

**`EG-CP-A11-PUBLIC-CONSUMER` — SATISFIED, and independently stress-tested.**
`EGCPStageAArchitectureFacts` writes out all 38 field types literally and
`egcpStageAArchitectureFactsExact` discharges them one projection at a time
(`capstone.<field>`), so a weakened capstone field cannot typecheck into the
consumer's stronger field. The file contains no `#print`, no `#check`, and no
elaboration query of the capstone's current type. Beyond the committed
registry I ran my own probes:

| Probe | Mutation | Result |
| --- | --- | --- |
| `AUD-CF-1` | field 29 `leftmost_tie_universal` weakened to `True` (producer `trivial`) — one conjunct only, all others intact | capstone module still elaborates; **build fails at `RMQ/Validation/EGCPStageA.lean:423:32`, type mismatch** |
| `AUD-CF-2` | field 9 `rho_little_o` restated over the flat `packedRho`, discharged by `packedRho_littleO` | **fails at `RMQ/Validation/EGCPStageA.lean:402:22`, type mismatch** |
| `AUD-CF-5b` | guard dropped from field 18 `run_opens_with_header` | **fails at `ReviewerArchitectureCapstone.lean:664:31`, type mismatch** (the guards are load-bearing, not decorative) |

Each mutation was restored from the original bytes in a `finally` block, the
restoration verified by SHA256, and `git status --porcelain` confirmed clean
afterwards. The `EGCPStageA.lean` line numbers above are exact, because that
file is not the mutated one in either probe: `423` is
`leftmost_tie_universal := capstone.leftmost_tie_universal` and `402` is
`rho_little_o := capstone.rho_little_o`, the two projections whose source
field was weakened. (`AUD-CF-5b`'s `664:31` is a line number in the *mutated*
copy of `ReviewerArchitectureCapstone.lean`, which is one line shorter than
the committed file; it is the
`run_opens_with_header := fun hleft hright => ...` producer line, now supplied
with two arguments its de-guarded field type no longer takes.)

`AUD-CF-1` is strictly stronger evidence than the committed `SA-M19`, which
weakens the whole producer: it shows the consumer discriminates a *single*
conjunct while the other 37 stay intact and the capstone module itself still
elaborates.

**`EG-CP-A12-REPLAY` — SATISFIED, with `P3-2` and `P3-4`.** I extracted the
runner's registry literal and compared it to matrix section 4 mechanically:
21 entries, orders 1..21 ascending, unique IDs, verdicts matching row by row
(2 ACCEPT / 19 REJECT), and every `ExpectFile` matching the frozen named
failing surface (`SA-M19`'s `Validation/EGCPStageA.lean` is the tail of the
matrix's `RMQ/Validation/EGCPStageA.lean` and matches by substring, which is
how the diagnostic check works). `Test-RegistryIntegrity` runs before any
build on every invocation. Mutations are applied byte-exactly with an
anchor-must-occur-exactly-once guard, restored in `finally` with SHA256
verification, and the run ends with a clean-tree check; a `TARGET-ABSENT` case
exits non-zero. Deadlines are measured (clean build and a real mutated-chain
probe on the deepest common import), times four, floor 300 s. The Windows
descendant-termination self-test spawns a detached grandchild sleeper,
records its pid, kills the tree, and verifies both root and grandchild are
gone; the non-Windows branch is present and explicitly uncertified.

**`EG-CP-A13-CAPSTONE-AUDIT` — OPEN / AUDITOR-OWNED.** This audit occupies the
row. It is correctly left open by the candidate everywhere; the packet
contains no verdict and no simulated audit outcome. Its openness is not a
defect.

### 5.2 Inherited invariants

| ID | Disposition |
| --- | --- |
| `INV-VALUE-DEPENDENCY` | SATISFIED. Every liveness inequality is at a value or address projection: field 36 at `.terminal`, field 19 at the trace-position-1 address, field 38 at the terminal pair. No enclosing-record inequality is used anywhere. Field 35 reproduces the terminal from the consumed replies. |
| `INV-SEMANTIC-NONVACUITY` | SATISFIED. No predicate is defined `True`; the liveness statements are inequalities of computed projections of real runs, and field 24 is a trace identity. `SA-M17` exists precisely so the corruption evidence cannot be vacuously true, and the mutant cell is a genuine complement of the canonical cell. |
| `INV-STORE-AGREEMENT` | SATISFIED. Field 34 is `packedReviewerRunAgainstMemory_eq_of_agree` at the literal run; field 37 is its expected-ACCEPT instance, discharged through the same agreement route. |
| `INV-READ-BACKING` | SATISFIED. Fields 20-21 back every reply literally and positionally; field 35 gives the occurrence-indexed form `run.trace[i]? = some { request, reply := memory[request.address]? }`. |
| `INV-PUBLIC-COMPOSITION` | SATISFIED. One structure, one binder triple, identical object terms in every field, and one guard wherever a guard appears; field 31 keeps the unguarded field 28 consistent on the invalid domain. |
| `INV-MUTATION-REPRODUCIBILITY` | SATISFIED. Verified by my own full-mode run (section 7), not by reading the worker's receipt. |
| `INV-CATEGORY-SEPARATION` | SATISFIED. `EG_CP_STAGEA_RESULT.md` section 7 separates logical payload bits, allocated bits, proof-only fields, model probes (`427`), logical fuel (`210`), and Lean wall-clock, and states the "never conflated with" column for each. I found no cell that conflates allocated with meaningful bits and no place where `427` becomes a time bound. |

### 5.3 Harness and integrity contracts

| ID | Disposition |
| --- | --- |
| `REPLAY-EXACT-REGISTRY` | SATISFIED. Count, ascending order, unique IDs, mapped verdicts, exact 2/19 totals, and nonempty row/field mappings, all validated before any build; observed firing on both integrity probes. |
| `REPLAY-SELECTOR-NONVACUITY` | SATISFIED in substance; see `P3-4` for the one invocation-form imprecision. `-Case <valid>` runs exactly one case; unknown, whitespace, bogus-probe, and combined selectors exit 2; omission alone means full mode; both `-IntegrityProbe` variants reject the corrupted in-memory copy while the frozen registry passes. |
| `REPLAY-SUBPROCESS-DEADLINE` | SATISFIED. Deadline measured on this tree from a clean build and a real mutated-chain probe, `* 4`, floor 300 s; timeout is failure; owned tree terminated with `taskkill /T /F`; sleeper self-test PASS on Windows; restoration and the clean check in `finally`. The non-Windows limitation is stated and not promoted. |
| `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY` | SATISFIED, verified with my own checker (section 7). |
| `NAMED-REGRESSION-REALITY` | SATISFIED. All thirteen inherited bodies (the `A02` patch plus twelve REJECT bodies) target the reviewer controller/memory/run — the same objects the Stage-A rows govern — and were re-executed against the Stage-A surface in my own run. The flat-universe legacy `M09` was *not* reused for the reviewer probe plan; the matching reviewer case `SA-M09-CROSSING-SWAP` was added instead, and my `AUD-CF-4` independently confirms the reviewer plan is discriminating. |

### 5.4 Replay registry, ID by ID

All 21 frozen IDs were executed by me in one full-mode run on the exact target
tree (not read off the worker's receipt). Observed verdicts and observed
first-failing surfaces:

| # | ID | Verdict | Observed first-failing surface | Activation check emitted |
| --- | --- | --- | --- | --- |
| 1 | `SA-A01-PRODUCTION-EXPECTED-ACCEPT` | ACCEPT | (unchanged candidate builds) | n/a (patches nothing) |
| 2 | `SA-A02-UNREAD-CELL-EXPECTED-ACCEPT` | ACCEPT | (surface still builds) | yes |
| 3 | `SA-M01-SIBLING-STORE` | REJECT | `PackedCellProbe/ReviewerController.lean` | yes |
| 4 | `SA-M02-SIBLING-PAYLOAD` | REJECT | `PackedCellProbe/ReviewerMemory.lean` | yes |
| 5 | `SA-M03-CANONICAL-SHAPE-BY-N` | REJECT | `PackedCellProbe/ReviewerController.lean` | yes |
| 6 | `SA-M04-ALLOCATION-HEADER-CELL-DROP` | REJECT | `PackedCellProbe/ReviewerMemory.lean` | **no** (`P3-2`) |
| 7 | `SA-M05-WIDTH-SUBSTITUTION` | REJECT | `PackedCellProbe/ReviewerWidth.lean` | yes |
| 8 | `SA-M06-WRONG-LONG-COUNT` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 9 | `SA-M07-HOST-LONG-COUNT-MIRROR` | REJECT | `PackedCellProbe/ReviewerController.lean` | yes |
| 10 | `SA-M08-LONG-COUNT-IGNORED` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 11 | `SA-M09-CROSSING-SWAP` | REJECT | `PackedCellProbe/ReviewerProbe.lean` | **no** (`P3-2`) |
| 12 | `SA-M10-DISCONNECTED-TRACE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 13 | `SA-M11-FORGED-PROBE-CAP` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | no (labelled structural) |
| 14 | `SA-M12-RESULT-OFFSET` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 15 | `SA-M13-INVALID-GUARD-RESULT` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 16 | `SA-M14-SHAPE-PARAMETER` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | no (labelled structural) |
| 17 | `SA-M15-HIDDEN-UNCOUNTED-TABLE` | REJECT | `PackedCellProbe/ReviewerController.lean` | yes |
| 18 | `SA-M16-ANSWER-ORACLE` | REJECT | `PackedCellProbe/ReviewerControllerProof.lean` | yes |
| 19 | `SA-M17-DECISIVE-MUTANT-NEUTRALIZED` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | yes |
| 20 | `SA-M18-PUBLIC-CERTIFICATE-WEAKENING` | REJECT | `PackedCellProbe/ReviewerCapstone.lean` | **no** (`P3-2`) |
| 21 | `SA-M19-ARCHITECTURE-PROPOSITION-WEAKENING` | REJECT | `Validation/EGCPStageA.lean` | yes |

Every observed verdict and every observed first-failing surface matches the
frozen matrix section 4 row for row: 2 ACCEPT, 19 REJECT, 0 target-absent, no
case skipped, mis-surfaced, or vacuous. `SA-M13` — the case the worker's own
diagnostic run caught as `ANCHOR-DRIFT` before the `WDD-20260806-010` ASCII
repair — applied cleanly here with its activation check passing, so the repair
reproduces independently.

---

## 6. Objections considered and dropped

- **"Field 28 is implementation-to-implementation, so `A07` is circular."**
  Dropped. Field 28 alone would be, but field 29 routes the returned index to
  `LeftmostArgMin`, which is defined in `RMQ/Core/Spec.lean` purely over
  `List Int` with no reference to the packed machine, and reaches it through
  `scanWindow_leftmost`. The specification side is genuinely independent.
- **"`SA-M11` is only structural, so the derived cap is not really tested."**
  Dropped as a defect claim, but the reasoning is worth recording because it
  is the sharpest thing an adversary can say about `A06`. Note that
  `1 + 2*3 + 2*210` *equals* `427`, so field 27's first conjunct would remain
  numerically true if the measure's header arm stored the literal: the
  rejection cannot be a false-equation rejection, and must instead come from
  the conjunct no longer holding in the reduced form the proof relies on. That
  is precisely why the frozen registry labels this case
  `structural (the commissioned structural surface)` rather than semantic, and
  the matrix, the result report, and the runner all say so. The label is
  honest and no stronger claim is made anywhere. The semantic content of `A06`
  does not rest on `SA-M11`: it rests on field 5 (the run *is* the drive with
  that measure as fuel) plus
  `packedReviewerDriveAgainstMemoryAux_trace_length_le` (the trace is bounded
  by the fuel), both of which are ordinary kernel theorems.
- **"Fields 36-38 are constant in the binders, so they are fixture-only
  evidence smuggled into a universal proposition."** Dropped. The matrix
  freezes this deliberately (section 1.1, closing paragraph) and both the
  matrix and the result report say so plainly; the universal content of `A10`
  lives in field 35, which *is* quantified over the binders and over every
  trace position.
- **"`SA-M15` is value-preserving, so it proves nothing."** Dropped. The
  registry labels it `value-preserving, structurally honest` and pairs it with
  the semantic rejections `SA-M03` and `SA-M07`, exactly as the earlier
  Stage-F audit's `P3` disposition required. No stronger claim is made
  anywhere.
- **"`WDD-20260806-008` miscounts the inherited/new registry split."** Dropped
  as a new finding. The count is indeed wrong in that entry (it says ten and
  nine; the true split is thirteen inherited — the `A02` patch plus twelve
  REJECT bodies — and seven new, which I recounted independently from matrix
  section 4). But the worker corrected it properly and append-only, both in
  `EG_CP_STAGEA_WORKLOG.md:35-40` and, more importantly, inside the ledger
  itself: `WDD-20260806-009` carries an explicit "Correction to
  `WDD-20260806-008`'s prose (append-only, the entry itself is not edited)"
  paragraph with the right numbers, and records "editing the committed
  `WDD-20260806-008` text in place" as a rejected alternative. That is exactly
  the discipline one wants; it also shows that the non-propagation in `P3-1`
  is an oversight rather than a policy.
- **"`SA-CHK-02` was run as `lake build RMQ RMQUnionFind`, not the frozen
  `lake build RMQ`."** Dropped. The executed command is a strict superset, the
  deviation is disclosed in the result report, and I ran the frozen command
  exactly (exit 0).
- **"The candidate touched public-claim surfaces."** Dropped. I applied
  `CLAIM_DRIFT_POLICY.json`'s own `currentFactSurfacePathRegex` (version 23,
  blob `437e37e171d974c4821d6e38c0115025a2fe4e02`, unchanged by the candidate)
  to the 13 changed paths: zero matches. The 18-surface registry is untouched.

---

## 7. Verification outcomes

Every command below was run by me on the exact target tree
(`ec35b5d`, tree `d1cb2987`) in a dedicated detached audit worktree, except
the per-commit design checks, which were run at each named commit in a second
detached worktree.

### Identity and hygiene

| Command | Outcome |
| --- | --- |
| `git status --short --branch` | clean at the target |
| `git diff --stat 270d7855..ec35b5d` | 13 files, 3758 insertions, 0 deletions |
| `git diff --name-only 1198ff6..ec35b5d` | 7 paths, all under `docs/` — documentation-only above the frozen proof/replay tree, as claimed |
| `git diff --check 270d7855..ec35b5d` | exit 0 |
| `git rev-parse` on all declared commits/trees | base, target, frozen, and freeze trees all match the commissioning prompt exactly |
| `f4107cd` file inventory | only `EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` and `WORKFLOW_DESIGN_DECISIONS.md` — the contract was frozen before any Lean or replay edit |
| Stage-F runner blob | `3420c76c3d232119052b49aa0577f7b1df169afe` at both base and target — byte-identical, its registry correctly not rerun |
| `CLAIM_DRIFT_POLICY.json` blob | `437e37e171d974c4821d6e38c0115025a2fe4e02`, version 23, unchanged |
| Roadmap-to-matrix verbatim check | 13/13 Stage-A requirement sentences byte-identical between the roadmap at the base and matrix section 1 (programmatic) |

### Lean and trust (one heavy Lean/Lake process at a time throughout)

| Command | Outcome | Duration |
| --- | --- | --- |
| `lake build RMQ.Validation.EGCPStageA` | exit 0 (cold chain, 195 targets) | 834.9 s |
| `lake build RMQ` | exit 0 (314 targets) | 250.3 s |
| `lake env lean scripts/axiom_check.lean` | exit 0; 1191 curated entries parsed; **zero** entries depending on anything outside `[propext, Classical.choice, Quot.sound]`; the four Stage-A entries (`packedReviewerArchitectureCapstone_holds`, `packedReviewerRunLeftmostTie`, `packedReviewerRunReachableInvariant`, `Validation.egcpStageAArchitectureFactsExact`) each on exactly those three | 225.6 s |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib" RMQ lakefile.toml` | no matches (exit 1) | — |
| `rg -n "native_decide\|Lean\.ofReduceBool" RMQ` | no matches (exit 1) | — |

### Auditor counterfactual probes (beyond the committed registry)

Each applied one textual mutation, rebuilt `RMQ.Validation.EGCPStageA`,
restored the original bytes in `finally`, verified SHA256, and confirmed
`git status --porcelain` clean.

| Probe | Result |
| --- | --- |
| `AUD-CF-1` single public conjunct (field 29) weakened to `True` | REJECT at `RMQ/Validation/EGCPStageA.lean:423:32`; restored, SHA verified, tree clean (7.7 s) |
| `AUD-CF-2` flat `packedRho` substituted for `packedReviewerRho` (field 9) | REJECT at `RMQ/Validation/EGCPStageA.lean:402:22`; restored, SHA verified, tree clean (8.2 s) |
| `AUD-CF-3` padding term deleted from `packedReviewerPaddedBits` | REJECT at `PackedCellProbe/ReviewerMemory.lean:135` and `:196`; restored, SHA verified, tree clean (3.1 s) |
| `AUD-CF-4` crossing branch collapsed to one probe | REJECT at `PackedCellProbe/ReviewerProbe.lean:139`, `:220`, `:332`, `:380`; restored, SHA verified, tree clean (3.9 s) |
| `AUD-CF-5` guard dropped from field 27 | **INCONCLUSIVE** — my edit left malformed Lean, so the build failed on a parse error rather than a type error. Not counted as evidence; superseded by `AUD-CF-5b`. |
| `AUD-CF-5b` guard dropped from field 18 (syntactically clean) | REJECT at `ReviewerArchitectureCapstone.lean:664:31`; restored, SHA verified, tree clean (5.1 s) |

### Replay harness

| Invocation | Outcome |
| --- | --- |
| `-SelfTestOnly` | PASS, exit 0, 6.2 s: registry OK (21 ordered entries, 2 ACCEPT / 19 REJECT, every entry carrying its row and field mapping) and pid-verified root-plus-grandchild termination |
| `-IntegrityProbe OmitMiddle` | exit 0: the corrupted copy (middle ID `SA-M09-CROSSING-SWAP` dropped) is rejected on count, order, and REJECT-total, while the frozen registry passes |
| `-IntegrityProbe DuplicateMiddle` | exit 0: the corrupted copy is rejected on count, duplicate IDs, order, and REJECT-total, while the frozen registry passes |
| `-Case 'SA-M99-NOT-A-CASE'` | exit 2 before any build |
| `-Case '   '` | exit 2 before any build |
| `-Case ''` via `-File` | exit 1 at PowerShell's binder before any action (see `P3-4`); exit 2 from the script's own guard under direct invocation and under `-Case '""'` |
| `-Case ... -IntegrityProbe ...` | exit 2, mutually exclusive |
| `-SelfTestOnly -Case ...` | exit 2, exclusive |
| `-IntegrityProbe 'Bogus'` | exit 2, unknown probe |
| Full 21-case registry | 1295.1 s. Calibration 6 s clean / 175 s mutated-chain probe -> per-case deadline 700 s; descendant self-test PASS; registry integrity OK before any build; **21/21 as commissioned (2 ACCEPT / 19 REJECT), 0 target-absent**, at the frozen surfaces (table in section 5.4); 20 SHA256-verified restorations. **Process exit was 1, for a reason of my own making** — see below. |

**Auditor contamination of the full-mode run, disclosed in full.** I had
already written this report into `docs/internal/audit_reports/` while the
campaign was running, so the runner's terminal `git status --porcelain` check
found an untracked file and the run ended `FULL MODE FAILED (1 failures)`,
exit 1. The single failure line was:

```
REPLAY-FAIL: tree is not clean after replay: ?? docs/internal/audit_reports/2026-08-06_EG_CP_STAGEA_CLOSE_R1_fresh_blind.md
```

This is my error, not a candidate defect, and it is worth stating precisely
what it does and does not leave unverified:

- All 21 semantic outcomes were observed and are unaffected — the clean check
  runs *after* the case loop.
- The porcelain output contained **exactly that one path and nothing else**:
  no ` M ` entry for any tracked file. Since 20 cases had each mutated a
  tracked Lean file, that is direct evidence that all 20 restorations were
  byte-exact, which is stronger than a bare "clean" would have been.
- It also demonstrates the clean-tree check is **not vacuous**: it detected a
  real untracked file and failed the run closed, exactly as
  `INV-MUTATION-REPRODUCIBILITY` requires.
- What it left unverified was only "the terminal clean check passes on a
  genuinely clean tree". I closed that separately below rather than paying
  ~22 minutes to rerun 21 unchanged cases, since no case input or outcome
  would differ.

| Follow-up run (report moved out of the repository first; `git status --porcelain` empty before starting) | Outcome |
| --- | --- |
| `-Case SA-A01-PRODUCTION-EXPECTED-ACCEPT` | **exit 0**, 346.2 s. `REPLAY-SUMMARY: cases considered 1, as commissioned 1, target absent 0` -> the selector executes **exactly one** frozen ID (the positive half of `REPLAY-SELECTOR-NONVACUITY`); calibration 13 s clean / 172 s probe -> deadline 688 s; self-test PASS; `terminal clean-state check` produced no failure and `SELECTED CASE OK` -> the clean check passes on a clean tree. |

### Policy gates

| Command | Outcome |
| --- | --- |
| `design_decision_check.ps1 -Strict -Base 270d7855...` (full range) | exit 0, `checked 14 changed files (4 code, 5 workflow, 6 neutral)` — 14 rather than the worker's 9 because this run was taken with my own report present in the tree |
| `design_decision_check.ps1 -Strict -Base HEAD~1` per commit | `f4107cd` PASS, `08dd29d` PASS, `1198ff6` PASS, **`ea08f28` FAIL (exit 1)**, `c38e885` PASS, `ec35b5d` PASS — see `P2-1` |
| `claim_drift_scan.ps1 -Strict` | exit 0, 18.1 s, `CLAIM-DRIFT: scan complete (1531 hits, 0 strict failures)`. My report contributes **zero** hits of any category; the delta from the worker's 1525 is unrelated pre-existing prose. |

### Report-sensitive gates rerun on the tree that contains this report

A gate run from before the report existed does not certify the report commit,
so after committing this file as `ddec8e2` (parent `ec35b5d`, the audit branch
`claude/stagea-packed-arch-audit-3f7f78`; not pushed, not merged) I reran:

| Command | Outcome |
| --- | --- |
| `git diff --check` (working tree) | exit 0 |
| `git diff --check 270d7855..HEAD` | exit 0 |
| `design_decision_check.ps1 -Strict -Base HEAD~1` | exit 0, `only neutral decision/evidence/history/report paths changed` — `docs/internal/audit_reports/*.md` is a neutral evidence path, so the report commit needs no ledger entry and passes at its own parent |
| `claim_drift_scan.ps1 -Strict` | exit 0, `CLAIM-DRIFT: scan complete (1531 hits, 0 strict failures)` |

These four receipts were taken on a commit whose report text differs from the
final text only by this subsection and the two policy rows above it; the
commit was then amended to include them and the same four checks re-run to
confirm they still pass. Outcomes were identical on both runs.

### Frozen-row byte integrity (`FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`)

Checker written outside the repository (auditor scratchpad, not committed).
Both blobs were extracted with `git cat-file blob` and round-tripped through
`git hash-object` to prove no encoding mangling: freeze blob
`719c01d1e182d3288eebc9427bb21f16b4d414f7`, candidate blob
`0b5fdeff1da14cc8ae58ae84ea19af07a5a2ef0b`. Both were decoded as **strict**
UTF-8 (invalid sequences raise), every markdown table row of sections 1-4 was
keyed by `(section, ID)`, and complete row bytes were compared.

```
freeze rows=46  target rows=46
  section 1: 13 rows   section 2: 7 rows   section 3: 5 rows   section 4: 21 rows
missing: []   added: []   changed: []   duplicate: []   problems: []
prefix above section 8 byte-identical: True
VERDICT: PASS
```

The last line is a check stronger than the contract requires: not only is
every keyed row byte-identical, the **entire document above section 8** is,
so no post-freeze edit landed outside the append-only ledger.

Negative controls, all six firing (a control that did not fire would itself be
a finding):

| Control | Fires as |
| --- | --- |
| single-byte row corruption in the `EG-CP-A06` row | `changed: [('1','EG-CP-A06-PROBE-CAP')]` |
| mojibake injection (`Â¬`, `â€œ`, `â€`) in a non-ID cell of the `SA-M11` row | `changed: [('4','SA-M11-FORGED-PROBE-CAP')]` |
| invalid UTF-8 bytes (`0x93 0x94`) in the `EG-CP-A02` row | strict decode raises: `'utf-8' codec can't decode byte 0x93 ... invalid start byte` |
| deleted `INV-READ-BACKING` row | `missing: [('2','INV-READ-BACKING')]` |
| duplicated `SA-A01` row | `duplicates: [('4','SA-A01-PRODUCTION-EXPECTED-ACCEPT')]` |
| post-freeze edit in section 7 prose | `prefix_above_section8_equal: False` |

### Skipped, with reason

- `scripts/gate.ps1`: not run. The frozen matrix records it as a conditional
  whose default is a recorded skip, every changed surface is owned by
  `SA-CHK-01`..`SA-CHK-12`, and I ran those directly. Running it would
  duplicate expensive certification without covering a new surface.
- The inherited Stage-F campaign `scripts/eg_cp_final_falsification_replay.ps1`:
  not rerun, as instructed. Byte-identity to the base blob was verified
  instead, which is the condition that makes the rerun unnecessary.
- No expensive command was rerun after a wrapper timeout. The one long build
  (`lake build RMQ.Validation.EGCPStageA`, 834.9 s) produced no interim
  output because the wrapper buffered its pipeline; I confirmed progress by
  inspecting live `lean.exe` processes and `.lake/build` artifact timestamps
  rather than relaunching.

---

## 8. Roadmap alignment, in letter and in spirit

**In letter: yes.** The candidate freezes a Stage-A matrix whose requirement
sentences are byte-verbatim from the roadmap's Stage-A table at the exact
base, freezes it *before* any Lean or replay edit (`f4107cd` touches only the
matrix and the workflow ledger), and then closes `EG-CP-A01` through
`EG-CP-A12` on **one** literal combined proposition over the accepted Stage-F
objects, with an independent expected-type consumer and a replayable mutation
campaign. `EG-CP-A13` is left open and auditor-owned throughout. The lineage
is exact and single: `f4107cd` -> `08dd29d` -> `1198ff6`, with everything
above `1198ff6` documentation-only (mechanically verified).

**In spirit: yes, with one legibility caveat.** The abstraction defect Stage A
exists to remove is the Stage-F situation where space, width, header, probes,
cost, and result were each true but *separately*, so that nothing forbade them
being about different objects. That defect is genuinely removed here, not
merely papered over: all 38 fields are stated over the identical `memory` and
`run` terms in a single structure; the flat `packed*` universe — which
`packedStoresNotEqual`
(`RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ExecutedUniverse.lean:186`)
shows is a genuinely different object family, its committed witness
disagreeing at segment 23 — does not appear anywhere in the two new modules;
and I confirmed by my own
mutation (`AUD-CF-2`) that substituting a flat-universe theorem for a reviewer
one breaks the committed consumer rather than being absorbed. The consumer is
not a rubber stamp: weakening a *single* conjunct breaks it (`AUD-CF-1`), and
the guards are load-bearing rather than decorative (`AUD-CF-5b`).

The caveat is `P3-3`: read as a self-contained document, the combined
proposition establishes that the packed run's answer *equals the reference's*
and that any index it returns is the leftmost argmin, but never that a valid
query's answer is an index at all. That is exactly the class of gap the
worker's own open question 7 anticipates, and closing it is a short corollary
rather than new work. It does not prevent the rung from having been closed;
it is the one place where a reviewer must step outside the capstone to finish
the reading.

Nothing out of scope was claimed. Word-RAM time, preprocessing time, and
measured runtime are explicitly disclaimed; `S1`, `V1`, publication, and
public-claim synchronization are named as separate open nodes; the
18-surface fact registry is untouched.

---

## 9. Best next target

**Coordinator disposition of `P2-1`, then `EG-CP-A13` closure and coordinator
reconstruction.** Concretely, in order:

1. Decide `P2-1` at merge time, before integration: squash the three
   documentation-only commits (`ea08f28`, `c38e885`, `ec35b5d`) so that no
   commit in merged history fails `-Strict -Base HEAD~1` — the resulting tree
   is byte-identical — or record a deliberate, reasoned exception. After
   integration this needs a history rewrite.
2. Propagate the disclosure of `P2-1` into the auditor packet, worklog, and
   round-log (`P3-1`) so the packet says what `EG_CP_STAGEA_RESULT.md:251`
   already says. One documentation commit, paired with its workflow-ledger
   entry so the per-commit gate passes at its own parent.
3. Add the `A07` completeness corollary of `P3-3` — under the guard,
   `exists index, run.terminal = some (some index) /\ LeftmostArgMin xs left
   right index` — as a 39th field or as a validation-root theorem, and add a
   registry case that a `none`-everywhere completion arm would fail. This is
   the single highest-value addition to the combined proposition and directly
   answers the worker's own open question 7.
4. Declare activation needles for `SA-M04`, `SA-M09`, and `SA-M18` (`P3-2`),
   or amend the frozen `A12` evidence wording through matrix section 7 with
   coordinator approval. `SA-M09`'s needle is one line.
5. Note `P3-4` and `P3-5` as wording corrections; neither changes any
   observed behaviour.

After those, `S1` bit-addressed probe semantics remains the substantive
frontier, since the `427` constant cannot be compared with Fischer-style
constants until bit-level probe accounting is fixed.

---

## 10. Durable report path

`docs/internal/audit_reports/2026-08-06_EG_CP_STAGEA_CLOSE_R1_fresh_blind.md`
(this file). No other file was created or modified by this audit. The branch
was not pushed, merged, or deleted, and the worker's worktree was never
touched.

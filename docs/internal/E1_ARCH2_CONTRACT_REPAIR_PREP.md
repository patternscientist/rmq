# E1-ARCH2 contract repair preparation

Prepared: 2026-07-24 by C06 (Claude runtime, disclosed fallback — cannot
record `ACCEPTED`).
Governance base: `a154983ae465b25ae6d8118b56abfa95ddf5b409`.

**Classification: coordinator preparation. Not a freeze, not launch
authority, not an acceptance.** The B3 R2 and B2 R4-successor prompts derived
from this document still owe `worker_prompt_preflight.ps1`, a fresh governed
base check, and their own freeze commits. Every citation below names its
exact source so a successor can re-derive it independently.

Companion evidence: C06 handoff audit
`docs/internal/audit_reports/2026-07-24_C06_e1_arch_handoff_package.md`
(commit `b6b6e02` on `claude/rmq-formalization-audit-6d835f`).

---

## 1. Owner decision of record

**On 2026-07-24 the owner adopted Option 1 for the B3 subtraction
architecture question: the bounded target's `.sub` is truncated natural
subtraction (monus), matching the accepted source ISA. The ordered/no-wrap
subtraction side condition is removed from the route contracts and the width
clause is restated as: every arithmetic result is `< 2^w`.**

Decision chain:

1. Worker terminal report `E1-ARCH2-B3ROUTE-R1` posed the three-way choice
   (archived at `docs/internal/E1_ARCH2_B3ROUTE_R1_WORKER_TERMINAL_REPORT.md`
   on `claude/e1-arch-handoff-durable`).
2. C05 addendum §3 recommended Option 1 and recorded the PREHIST-disjunction
   transcription finding.
3. C06 independently re-derived that finding from the accepted blobs
   (audit report §"Independent re-derivations", item 1).
4. The owner accepted Option 1 in the 2026-07-24 coordinator session.

This is recorded as `DD-20260724-001` in `docs/internal/DESIGN_DECISIONS.md`.
Per the finding re-derived twice, this is a **contract repair** (restoring a
branch the accepted PREHIST input explicitly authorized), not a requirement
amendment.

## 2. New evidence obtained during preparation

All runs executed 2026-07-24 in the clean B3 candidate worktree
`C:\Users\poin\.codex\worktrees\bb61\RMQ` at HEAD
`bc71cad140956477f4de7e513529ae15d381aa13`.

1. **Committed replay, upstream stages: PASS.** Running
   `scripts\e1_arch2_b3_historical_route_replay.ps1` passed branch identity,
   exact two-commit history and parents, matrix-only freeze, exact five-path
   scope, immutable source-port blob identity, frozen-byte comparison, and
   the 42-case registry identity (41 `REJECT` / 1 `ACCEPT`) checks.
2. **`OBSTRUCTION-BUILD PASS duration=1.369s`.** The focused Lake build of
   `RMQ.Validation.E1Architecture.B3HistoricalRoute.Obstruction` succeeds
   warm with no network access. The R1 worker's sandbox network block does
   not reproduce on the owner host.
3. **The seven-field observation reproduces exactly.** Via
   `lake env lean` on a probe importing the committed module:

   ```text
   #eval pinnedFirstSubUnderflow
   some { tick := 71, pc := 73, dst := 19, leftReg := 22,
          rightReg := 23, leftValue := 5, rightValue := 19 }
   ```

   This matches the replay's pinned expected string byte-for-byte and closes
   the audit's P3-1 at the executable tier: the underflow at source PC 73 is
   an actually reached state of the accepted pinned execution.
4. **New defect: the committed replay cannot go green as written.** Its
   probe stage invokes the bare `lean` binary on the generated probe file
   without `lake env` or `LEAN_PATH`, and fails with
   `unknown module prefix 'RMQ'`. The R1 worker never reached this stage
   (its run died earlier at the then-blocked Lake fetch), so the defect was
   latent in the committed script. Consequence: the terminal green replay
   the R1 candidate owes is unattainable without a script repair. Proposed
   named regression: `REPLAY-PROBE-TOOLCHAIN-ENV` (see §6).

Not run: no mutation campaign exists for the obstruction replay (its 42-case
check is registry-identity only), and no broad build was attempted.

## 3. Disjunction sweep: full disposition

Method: manual comparison of every frozen B3 matrix surface (25 inherited
rows, 15 local rows' requirement and evidence cells, construction choices,
six pinned choices, predicates block, 42-row mutation registry, stop
conditions, replay controls) and the R1 prompt against the accepted PREHIST
blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f` (obligations §§1-11 at lines
523-560; contract at lines 815-1147).

**Key sharpening of the addendum's finding: PREHIST's own `B3-HIST-04` row
(line 881) never mentions ordered subtraction.** The requirement cell demands
width closure only. The collapse was introduced in matrix-/prompt-authored
text. The precise defect inventory:

| # | Surface | Text | Disposition |
|---|---|---|---|
| 1 | Matrix `B3-HIST-04` **evidence cell** (matrix line 201) | "…raw decode, **ordered subtraction**, and dormant-field coverage" | **COLLAPSE — repair.** PREHIST §6 (lines 543-545) reads "establish every *required* subtraction ordering **or an explicit checked-underflow behavior**"; both the disjunct and the qualifier "required" were dropped. |
| 2 | R1 prompt line 57 (`B3-HIST-04` gloss) | "prove **subtraction order/no-wrap** and complete image/ROM capacity" | **COLLAPSE — repair** in the R2 prompt. |
| 3 | Matrix construction choice (lines 113-115) | "Source truncated subtraction is lowered by compare/branch/zero **or** an ordered target subtraction, so every executed target subtraction is no-wrap" | **NARROWING — repair.** Keeps a disjunction but excludes PREHIST's checked-underflow arm *as a target primitive* (a truncated target `.sub` **is** an explicit checked-underflow behavior). Both permitted arms force no-wrap target execution. |
| 4 | `MUT-HIST-06G-SUBTRACTION-UNDERFLOW` (matrix line 415 = PREHIST line 1094) | "At `pinnedSubPhase`, swap the **proved ordered operands**" | **DEFECT IN THE ACCEPTED INPUT — governed deviation required.** The row presumes the ordered branch; PREHIST is internally inconsistent (its §6 vs. its own registry row). R1 prompt line 64 mandated verbatim inheritance "without removal or weakening", propagating it. R2 must re-specify this row and record the deviation from the accepted registry explicitly (§4, delta 4). |
| 5 | `pinnedTargetSubPhase` choice text (matrix line 126) | "establish operand order **or** take the explicit zero branch" | Disjunction preserved, but wording is obsolete under monus; rewrite (§4, delta 3). |
| 6 | Mul/div lowering (PREHIST sim-contract item 4 ↔ matrix choices + stop condition 4) | "fixed proved register-driven microprogram **or** triggers the model-choice stop" | **PRESERVED.** No repair. |
| 7 | Raw-vs-option-shift load obligation (PREHIST §5 ↔ matrix `readMem` choice) | — | **PRESERVED.** No repair. |
| 8 | All other rows, predicates, stop conditions, replay controls | — | **No further narrowed disjunction found.** |

Limit: the sweep is a manual reading by one coordinator. The R2 freeze worker
must re-run it against the exact frozen source ranges before committing the
repaired matrix.

## 4. B3 R2 contract repair deltas (exact old → new)

These deltas define the repaired contract the R2 prompt must freeze. Nothing
here edits the R1 candidate branch, the accepted PREHIST blob, or any
accepted input.

**Delta 1 — construction choice sentence.**
Old (matrix lines 113-115):

> Source truncated subtraction is lowered by compare/branch/zero or an
> ordered target subtraction, so every executed target subtraction is
> no-wrap.

New:

> Target `.sub` is truncated natural subtraction, definitionally matching
> the accepted source ISA (`B3SourcePort/E1Machine.lean:94`: "truncated
> natural subtraction, matching the route's `Nat` arithmetic"). Source
> `.sub` lowers directly to target `.sub`. Width closure for subtraction is
> definitional: `left - right ≤ left < 2^w`. This restores the accepted
> PREHIST §6 disjunct "or an explicit checked-underflow behavior" (blob
> `be80468e…`, lines 543-545), which the R1 contract dropped in
> transcription (DD-20260724-001).

**Delta 2 — `B3-HIST-04` evidence cell.**
Old: "…ROM/image capacity, raw decode, ordered subtraction, and
dormant-field coverage."
New: "…ROM/image capacity, raw decode, truncated-subtraction result bounds
(every arithmetic result `< 2^w`; for `.sub` via `left - right ≤ left`), and
dormant-field coverage."
The requirement cell (copied from PREHIST line 881) is unchanged.

**Delta 3 — pinned sub-phase witnesses.**
Old `pinnedTargetSubPhase` rationale: "Source PC 32 is the live
`.sub 23 32 24`; its lowering must establish operand order or take the
explicit zero branch."
New rationale: "Source PC 32 is the live `.sub 23 32 24`; its lowering
preserves the truncated source result."
**Additionally freeze a seventh port-deferred choice:**
`pinnedUnderflowSubPhase = (sourcePC := 73, microPC := 0)` — source PC 73 is
the first reachable underflowing subtraction (`.sub 19 22 23`, tick 71,
operands 5/19; kernel-checked slot/PC theorems and the reproduced probe at
`bc71cad`). This gives the re-specified MUT-HIST-06G an anti-vacuous target:
the truncation branch is exercised by an actually reached state, not a
hypothetical. Whether PC 32's subtraction is ordered in the pinned run is
currently undetermined; the R2 freeze should determine it (one probe) and
document the pair as ordered-case and underflow-case witnesses.

**Delta 4 — `MUT-HIST-06G` re-specification.**
Old (PREHIST line 1094, inherited verbatim):

> | `MUT-HIST-06G-SUBTRACTION-UNDERFLOW` | At `pinnedSubPhase`, swap the
> proved ordered operands | `REJECT`; `consumeDynamicWidth` |

New:

> | `MUT-HIST-06G-SUBTRACTION-UNDERFLOW` | At `pinnedUnderflowSubPhase`,
> mutate the target `.sub` evaluator branch to produce the wrapping value
> `(2^width + left) - right` instead of the truncated `0` on underflow |
> `REJECT`; `consumeSourceSimulation` |

Failing-surface analysis: the wrapping value **fits the width** (for the
pinned observation, `2^24 + 5 - 19 < 2^24` is false — it equals
`2^24 - 14 < 2^24` — so `consumeDynamicWidth` cannot be the rejecting
surface). The correct surface is the phase-indexed source-step preservation
theorem: the historical successor writes `0`, so simulation fails at the
mutated step. Registry totals remain exactly 42 cases, 41 `REJECT`,
1 `ACCEPT`; only this row's object and failing surface change. The R2 matrix
must mark this row as a governed deviation from the accepted PREHIST
registry, citing DD-20260724-001 — it may **not** claim verbatim
inheritance.

**Delta 5 — prompt language.**
The R2 prompt replaces R1's line-57 gloss ("prove subtraction order/no-wrap")
with "prove every arithmetic result fits the width; subtraction is
truncated, matching the source ISA", and replaces R1's line-64 inheritance
clause ("without removal or weakening") with "inherit all rows verbatim
except `MUT-HIST-06G`, re-specified per DD-20260724-001; no other row may
change."

**Delta 6 — replay toolchain environment.**
The R2 replay (and any repair of the R1 obstruction replay) must invoke
Lean probes under the project toolchain environment (`lake env lean …` or
explicit `LEAN_PATH`), and must include a cheap self-test that a probe
importing an `RMQ` module elaborates before the evidence-bearing stages run
(§2 item 4; `REPLAY-PROBE-TOOLCHAIN-ENV`).

## 5. B2 descriptor re-freeze draft

Corrections to apply when re-freezing the descriptor contract for the B2 R4
successor. R3 (candidate `250fba1685411089825cbb8245a4fc3180678e77`) proved
the old frozen conjunction false; these clauses restate the geometry against
the exact accepted current definitions at governance `a154983`.

| Clause | Old frozen text (R3 freeze blob `a15b723f…`) | Corrected clause and exact current citation |
|---|---|---|
| G06 | `blockCount := N/blockSize` | `blockCount := N / b` (division by **base**, not block size). Current: `canonicalBPRelativeSummaryBlockCountRaw shape = shape.size / canonicalBPRelativeSummaryBase shape` (`RMQ/Core/SuccinctClose/RelativeSummary.lean:1248-1250`). The old `blocksPerSuper := b` clause is consistent with current (`…BlocksPerSuperRaw = …Base`, lines 1244-1246) and stands. |
| G10 | `longBlocksPerSuper := longRankWord` | `longBlocksPerSuper := 1`. Current: `def longFlagRankBlocksPerSuper (_bits) (_target) : Nat := 1` (`RMQ/Core/GenericSelect/Source.lean:351`), consumed by `longFlagRankData` (same file, line 411). R3's size-50 witness (current value `1` vs. demanded rank word width `2`) is the accepted refutation. Block width is `longFlagRankBlockWidth := longFlagRankWordSize` (line 353), **not** the generic `machineWordBits (blocksPerSuper * wordSize)`. |
| G12 | "set blocks-per-super to rank word" | `sparseBlocksPerSuper := 1`. Current: `def sparseExceptionEffectiveFlagRankBlocksPerSuper (_bits) (_target) : Nat := 1` (`RMQ/Core/GenericSelect/FlagRank.lean:213`), with `…_pos` at line 234. Block width is `sparseExceptionEffectiveFlagRankBlockWidth := sparseExceptionEffectiveFlagRankWordSize` (line 216). Structurally identical to G10 but a **different declaration in a different file** — cite this one, not G10's. |

### 5.1 The mechanism behind the G10/G12 defect — cite the live declaration, not the generic one

Resolved on 2026-07-24 (this closes the citation gap §5 previously left open, and
supersedes the earlier characterization of the defect as simply "copied the wrong
geometry").

`RMQ/Core/GenericSelect/FlagRank.lean:24-25` defines a **generic**

```lean
def flagRankBlocksPerSuper (flagBits : List Bool) : Nat :=
  flagRankWordSize flagBits
```

— blocks-per-super **is** the rank word size, exactly what old G10/G12 demanded.
So those clauses were not invented; they were copied from a real declaration.
But that generic layer's consumer, `flagRankData`, **is referenced nowhere
outside `FlagRank.lean`** (verified by grep over `RMQ/` at governance
`d16adfc`). The live long and sparse routes use the specialized constant-`1`
declarations cited in the table above.

So the precise defect is: **the frozen contract cited a real but
route-unconsumed generic declaration instead of the specialized declaration the
accepted route actually uses.** The same trap applies to the block-width cells,
where generic and specialized formulas also disagree
(`machineWordBits (blocksPerSuper * wordSize)` vs. plain `wordSize`).

Consequence for the re-freeze: for every geometry cell, cite the declaration
**reachable from the accepted route's own data constructor**, and record that
reachability. A same-named-family declaration is not evidence.
| G14 | universal `L[19] = ceil(m/w) = L[0]` | Split the row. The **physical offset alias `O[19] = O[0]` stays universal** — R3 records it as "a distinct true statement." The **word-length equality must not be universal**: at the empty shape the BP payload has length zero while the shared rank store is one sentinel-bearing word, so `L[19] ≠ L[0]` there. Re-freeze the length clause either with an explicit non-empty guard or with the empty-shape value stated separately, and keep the alias clause unguarded. Exact source: R3 final matrix blob `12eafa12e6e8905d322f3ece7b8a1f5fe2251829` lines 886-888 (also at `codex/e1-arch2-b2-descriptor-closure-r3:docs/internal/E1_ARCH2_B2_DESCRIPTOR_CLOSURE_MATRIX.md:886`). **Not** the closure blob `58323fac…`, which contains no G14 reasoning — correcting the pointer this document previously carried. |

**Central subtraction/truncation clause (all route contracts, B2/B3/B4):**

> Every arithmetic result is `< 2^w`. Where an accepted source or current
> definition uses `Nat` truncation (B3: `E1Machine` `.sub`; B2:
> `decodePacket = if v = 0 then none else some (v - 1)`, DD-20260719-205,
> `E1QueryProgram.lean:93`), the route contract adopts that truncated
> semantics. No route contract may impose an ordered/no-wrap side condition
> that is absent from the accepted definition it constrains, and any frozen
> clause about operation semantics must cite the accepted definition it
> constrains.

(Location note: DD-20260719-205 lives at `DESIGN_DECISIONS.md:7554` on
`claude/b1-b2-charged-fringe-tables`, not on `main` — C06 audit finding
P2-2.)

The R4-successor prompt additionally owes, unchanged from the runbook: the
three named B2 regressions (R1 proxy obstruction, R2 disconnected
programs/host projection, R3 stale contract) wired into its replay as
required rejects; a fresh governed base; and `worker_prompt_preflight.ps1`.

## 6. Named workflow regressions

Recorded as `WDD-20260724-001` in
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`:

1. `FROZEN-CLAUSE-CONTRADICTS-ACCEPTED-DEFINITION` (C05 proposal, adopted):
   a frozen contract clause about operation semantics must cite the accepted
   source definition it constrains and preserve the full form of any
   disjunction it inherits.
2. `INHERITED-MUTATION-ROW-PRESUMES-REFUTED-BRANCH` (new): a mutation
   registry row inherited from an accepted input is not exempt from
   consistency with the repaired requirement it tests. "Inherit verbatim
   without weakening" is not satisfiable when the inherited row presumes a
   branch the accepted execution refutes; the prompt must name the governed
   deviation instead.
3. `REPLAY-PROBE-TOOLCHAIN-ENV` (new): any replay stage that invokes
   `lean`/`lake` on generated files must run under the project toolchain
   environment and self-test module resolution before evidence-bearing
   stages. The R1 obstruction replay's probe stage is the concrete instance
   (§2 item 4).
4. `FROZEN-CLAUSE-CITES-UNCONSUMED-GENERIC-DECLARATION` (new, §5.1): a frozen
   geometry or semantics clause must cite the declaration reachable from the
   accepted construction's own data constructor, and must record that
   reachability. Where a generic and a specialized declaration share a name
   family, the generic one may be real, compile, and still be route-dead —
   citing it produces a contract that contradicts the accepted route while
   looking well-sourced. This is the mechanism behind the B2 R3 refutation and
   is a sibling of regression 1: both are failures to bind a clause to the
   definition it actually constrains.

## 7. What this document does not establish

- No freeze, no launch, no acceptance, no route verdict. B3 remains
  `OBSTRUCTED / architecture-choice-resolved-pending-refreeze`; B2 remains
  contract-refuted pending re-freeze.
- The R1 candidate's mutation campaign remains unexecuted, and its committed
  replay remains non-green (now for the known probe-stage reason).
- Whether PC 32's pinned subtraction is ordered is undetermined (delta 3). The
  R2 prompt delegates this to the R2 freeze as an explicit obligation rather
  than leaving it assumed.
- ~~The exact sparse (G12) declaration citation is owed at re-freeze.~~
  Closed 2026-07-24 in §5.1, together with the mechanism that produced the
  defect.
- ~~The corrected G14 clause is owed.~~ Closed 2026-07-24 from R3's final matrix
  blob: split the alias (universal) from the word-length equality (not
  universal at the empty shape). All four B2 geometry clauses (G06, G10, G12,
  G14) now have exact corrected text and exact citations. **What remains owed
  for B2 is the executable descriptor-closure work itself** — operand-bearing
  instructions, machine state, evaluator, run relation, charged B1
  initialization, G24/G25 semantic correspondence, trace/count facts, and typed
  consumers — plus the three named R1/R2/R3 regressions wired into the new
  replay. The re-freeze is now a transcription task; the implementation is not.
- This runtime cannot record `ACCEPTED`; the R2/R4 launches and any registry
  deviation remain owner/coordinator actions at their own gates.

## 8. B3 R2 launch package — prepared, not launched

**Governed base:** `5ad7e4876fed1d78bd76012e28d327d2d78b838c` on branch
`codex/e1-arch2-b3-historical-route-r2-governed-base-v2`. Ordered parents are
the accepted source port `c19061629ce8cf1e78992a99346170edd84b4971` and current
governance `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`.

This **supersedes** the first base `348d351…` (parents `c190616` +
`d16adfc…`). That base was correct when built but became unusable once the
gating blocker was diagnosed: it predates the `.claude/skills` port, so a
Claude-runtime worker checked out there would still expose no RMQ project
skills and would hard-stop on `runtime_catalog_omitted`. A worker base must
contain the runtime surface its own startup gate requires.

Both bases were built the same way and share the same append-union resolution
discipline. The v2 union additionally leaves two distinct entries sharing
`DD-20260723-001` and two sharing `WDD-20260723-001`, because the source-port
and handoff lineages allocated the same date-sequence IDs independently;
`WDD-20260719-001` was already duplicated on both sides. These IDs must be
resolved by lineage and line number.

The base was required because `c190616` predates the CI repair, so an R2
checkout rooted at the source port alone would fail the project-skill
preflight's governance-ancestry condition. The merge's only conflict was an
append collision in `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (the source
port and the CI fix each appended after governance `a154983`), resolved as the
exact union in date order. Verified mechanically: the source-port file is a
byte-exact prefix of the result, and the appended tail equals the CI-fix entry
byte-for-byte. Every accepted Lean, matrix, replay, and fixture blob equals
`c190616`.

**Prompt:** `docs/internal/e1_arch_prompts/E1_ARCH2_B3ROUTE_R2_PROMPT.md`,
handle `E1-ARCH2-B3ROUTE-R2`, worker branch
`codex/e1-arch2-b3-historical-route-r2`, required skill `rmq-proof-sprint`.

It applies deltas 1-6 of §4 and adds three things the R1 contract lacked:

1. **`B3-HIST-16-TRUNCATED-SUBTRACTION-FIDELITY`**, a new frozen row. This is
   what keeps the repair from reading as a weakening: the old ordered clause
   was refuted by the accepted execution, so it was impossible rather than
   strong, and the replacement is both definitionally satisfied for width
   *and* carries an exercised-at-PC-73 obligation. A fidelity theorem that
   holds only because underflow is assumed unreachable explicitly fails the
   row.
2. **`REPLAY-PROBE-TOOLCHAIN-ENV` and `REPLAY-CLEAN-BASELINE-OUTSIDE-TREE`**
   as frozen replay controls, closing the two harness defects found on
   2026-07-24 (R1's bare-`lean` probe stage, and the CI workflow that wrote
   its log into the checked working tree).
3. **The `pinnedTargetSubPhase` obligation** — determine PC 32's operand order
   by execution at freeze time and record it either way, instead of
   inheriting the accepted port's unexamined assumption.

**Preflight:** `scripts/worker_prompt_preflight.ps1` returned
`WORKER-PROMPT-PREFLIGHT: PASS` with `status=READY_TO_SEND`,
`feedback=COMPLETE`, `semantic_review=COMPLETE`,
`destination_task=FRESH_GOVERNED_WORKTREE`,
`destination_runtime=GOVERNED_START`, `TaskMode=WRITE`.

**Startup gate now passes honestly.** With the wrappers ported
(`DD-20260725-001`, `WDD-20260725-001`), `project_skill_preflight.ps1` at
governance `f0c7232` against the v2 base returns `PASS` with expected,
checkout, working, and runtime inventories all equal to
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint` — for both
`-RequiredSkills rmq-coordinator` and `-RequiredSkills rmq-proof-sprint`. This
is the first point in the E1 architecture campaign at which a Claude-runtime
coordinator or worker satisfies the gate directly rather than as a disclosed
fallback.

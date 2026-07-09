# A02 — Adversarial Pre-W10 RMQ Frontier Audit

- Auditor handle: `A02-rmq-pre-w10-frontier-audit`
- Chat/thread title: `(A02-rmq-pre-w10-frontier-audit) adversarial pre-W10 RMQ frontier audit`
- Date: 2026-07-09
- Report path: `docs/internal/audit_reports/2026-07-09_A02_rmq_pre_w10_frontier_audit.md`

## 1. Scope

- **Target branch/commit:** `origin/codex/add-audit-decision-log`, HEAD `37abaf8` (matches
  expected). Verified: `git rev-parse origin/codex/add-audit-decision-log` → `37abaf8…`.
- **Pre-integration base:** `c49f4a4` (confirmed).
- **Worker commits integrated:**
  - `8e22594` "Add theorem-backed Cartesian stack builder"
  - `e7fe784` "Split final RAM segment and flat payload modules"
- **Integration commits:**
  - `42c0115` merge Cartesian stack builder (parents `c49f4a4`, `8e22594`)
  - `37abaf8` merge final RAM flat-payload refactor (parents `42c0115`, `e7fe784`);
    also adds coordinator workflow content (WDD-014, worker-prompt skill section).
- **Diff size:** `git diff --stat c49f4a4..37abaf8` = 14 files, +2624 / −1993. `git diff --check`
  clean (no whitespace errors).
- **Theorem/trust surfaces reviewed:** `RMQPaper.lean` closure, `RMQ/Headlines/RMQ.lean`,
  `RMQ/Core/SuccinctRMQClassic.lean`, `RMQ/Core/Shape.lean`, `RMQ/Core/SuccinctFinalRAM.lean`,
  `RMQ/Core/SuccinctFinal/RAM/Segments.lean`, `RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean`,
  `RMQ/Validation/SuccinctClassicCostHarness.lean`.
- **Docs reviewed:** `RMQ_FINAL_ROADMAP.md`, `AUDIT_PROTOCOL.md`, `DESIGN_DECISIONS.md`,
  `WORKFLOW_DESIGN_DECISIONS.md`, `WORKER_PROMPT.md`, `RMQ_IMPORT_CLOSURE.md`, `CODE_MAP.md`,
  `RMQ_EXTRACTION_FRONTIER.md`, `FAMILY_SUMMARY.md`.
- **Roadmap slice:** R4 (reviewer-grade architecture refactor — partial) and R5-preparatory
  (executable prepared-path Cartesian construction).

## 2. Verdict

**MERGE-READY WITH FOLLOW-UP.**

The integrated branch genuinely advances the roadmap in spirit, not merely to the letter. The
Cartesian stack builder is theorem-backed by a **hypothesis-free** equality to the canonical
shape and is genuinely consumed by `prepareInput`; the final-RAM split is a verified
**name-preserving, semantics-preserving move** that does not bury any accounting obligation; the
public theorem surfaces survive axiom-clean; and every executable/performance improvement is
explicitly labeled as runtime engineering evidence, never as a model-cost, compiler, extraction,
or scalability theorem. No P0 or P1 findings. Follow-ups are architecture-completion (R4 is only
partially done) and a next-target recommendation (§4, §8).

## 3. Findings (P0 → P3)

### P0 — none
No checked-proof invalidity, no artifact corruption. Hygiene scans for
`sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable|import Mathlib` and
`native_decide|Lean.ofReduceBool` over `RMQ RMQExamples lakefile.toml` returned **no matches**.
Headline and Word-RAM axiom checks show only `propext, Classical.choice, Quot.sound`
(and, for the zero-block same-block surfaces, only `propext, Quot.sound`).

### P1 — none
No public overclaim, no gate failure, no misleading theorem surface, no roadmap-invalid
"correct but wrong target" work. See §4 and §6 for the adversarial checks that could have
produced a P1 and why each was cleared.

### P2 — architecture / plan-alignment

**P2-1 (architecture): R4 is only partially achieved; the compatibility root is still very
large.** The refactor moved `concreteBPNativeSuccinctRMQGlobalReadStore` + segment layout to
`RMQ/Core/SuccinctFinal/RAM/Segments.lean` (160 non-blank / 174 total lines) and the flat-payload
layout/manifest/backing to `RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean` (1738 non-blank / 1806
total). But `RMQ/Core/SuccinctFinalRAM.lean` only shrank **7863 → 5990 non-blank lines**
(8230 → 6284 total; ~24%) and remains the single largest proof file. R4's candidate split named ~5 role modules ("payload layout, trace
execution, cost bounds, flat payload backing, execution-story surfaces"); only *flat-payload
backing* and *segment layout* were extracted. This is honestly scoped — `DD-20260709-006` states
"the next safe reviewer-legibility split is likely the whole-query interpreter/program layer or
the bounded-event/no-synthetic execution-story packets" — so it is disclosed partial progress,
not overclaim. Impact: the roadmap pressure point "some implementation files are large enough
that proof architecture is harder to see than it should be" is only marginally relieved.

**P2-2 (roadmap-alignment): W10 as "more prepared payload/store executable path" is on-ladder
but is probably not the highest-value next rung.** The integrated work advances R4-partial and
R5-prep. Continuing straight into more R5 executable-path plumbing is defensible, but the
roadmap's Success Standard is about the **public theorem surface** a reviewer reads, and R3
("retire remaining model blemishes") is still open: the harness output still surfaces a
`route=zero-block` guard, an all-size constant `cleanAllSizeBound=4144` distinct from
`fastRegimeBound=118`, and conservative footprint bounds — exactly the "blemishes that invite
unnecessary questions" R3 targets. The claim-drift scan still tracks `[review]` churn for
`fast-regime-118`, `all-size-196727`→`4144`, and `legacy-2pow128`. Shrinking that public surface
(R3: internalize the zero-block guard behind a supplied-store equality; replace conservative
"safe footprint" with an exact dynamic read-set theorem; push word-width/address side conditions
into named machine-precondition predicates) is higher paper leverage than another builder. If the
team does pursue R5 next, W10 should be scoped to the concrete R5 deliverable
(`rmq_trace_validate`: differential checks, trace/no-synthetic/payload-coverage checks, and a
benchmark mode that separates wall-clock from model ticks), **not** to another "faster builder"
performance artifact — the roadmap's "What Not To Work On Next" cautions against optimizing an
off-critical-path artifact. See §8.

### P3 — process / polish

**P3-1: Parallel DD-ID collision, resolved at integration.** Both worker branches independently
authored `## DD-20260709-005` with different titles (Cartesian builder vs RAM split). The merge
`37abaf8` renumbered the RAM entry to `DD-20260709-006`; the integrated
`docs/internal/DESIGN_DECISIONS.md` now has 005 (Cartesian, line 221) and 006 (RAM, line 1058)
with consistent cross-references and no dangling IDs. Fixed, but the DD numbering scheme has no
collision-avoidance for concurrent branches; a date+topic slug or reserved-range convention would
prevent recurrence.

**P3-2: `RMQ_IMPORT_CLOSURE.md` is accurate at HEAD (corrects an earlier draft of this
report).** The doc counts **non-blank** Lean lines. At the integrated HEAD `37abaf8` it reports
`import RMQPaper` **126 files / 105607** and whole-workspace **254 files / 164618**; at base
`c49f4a4`, **124 / 104190** and **247 / 162089**. Independent verification at base gives **163436**
non-blank Lean lines over **248 tracked `.lean` files** — within ~0.8% of the doc's 162089 — so the
base doc was **accurate, not stale**, and the HEAD deltas are small and plausible (RMQPaper +1417,
whole-workspace +2529 non-blank, consistent with the ~354-line Cartesian additions plus the
closure-neutral move). Correction of the prior draft: it claimed a ~12k-line staleness, which was
two mistakes — (i) comparing the doc's non-blank metric against a **total-line** `wc -l` count
(174197 at base; the ~12k gap was blank lines, 174197 − 163436 = 10761), and (ii) reading the
**pre-merge worker commit** `e7fe784`'s doc (111555 / 174230), not the integrated HEAD. The worker
commit had regenerated with a total-line count; the merge `37abaf8` correctly **re-regenerated with
the non-blank metric**, restoring consistency with base — a point in favor of the integration.
Minor residual worth a follow-up: the doc's whole-workspace file count is **254 vs 250 tracked
`.lean` files** at HEAD (247 vs 248 at base), so that catch-all figure was generated in a worktree
carrying a few transient/untracked `.lean` files and is not exactly reproducible from a clean
checkout; pin it to `git ls-tree` tracked files. (The reviewer-facing `RMQPaper` closure file
count, 124 → 126, matches the two committed files exactly.)

**P3-3: `design_decision_check.ps1` did not actually exercise the new DD entries.** Run in the
integrated (committed, clean) checkout it reported "no changed files detected" and exited 0
because it diffs the working tree against HEAD rather than a branch against its base. The DD
entries were instead verified by manual reading (they are well-formed; see §5). Minor tooling gap:
the advisory script gives no signal on an already-committed branch.

## 4. Plan-alignment assessment

**Rungs genuinely advanced:**

- **R4 (reviewer-grade architecture): partially.** A verified pure move (P2-1) that establishes
  the `RAM/Segments` + `RAM/FlatPayload` boundary with stable public names and a compatibility
  root. Real but incomplete.
- **R5 (executable Lean artifact path): preparatory step genuinely landed.** The prior frontier
  doc named an explicit prerequisite: "A genuinely faster array/stack-based Cartesian builder
  remains future work and must be proved extensionally equal to `Cartesian.shape xs` before the
  executable harness uses it." That prerequisite is now discharged with source + theorem +
  executable evidence: `stackCartesianShape_eq_shape` proves it, `prepareInput` uses it, and the
  `--shape-profile-size 32768` run builds a 32768-element shape in **0.77 s** where the reference
  builder previously timed out at n=2048. This is a genuine, not stale-papered, retirement of that
  objection.

**Rungs not advanced (and open):** R2 exact all-size (`118` remains false; `4144` alias stands),
**R3 (blemish retirement — untouched)**, R6/R7/R8.

**Is W10 the right next target?** On-ladder yes, but not clearly optimal. The higher-value
paper-legibility move is R3 (shrink the public theorem surface), or — if R5 is the deliberate
target — the concrete `rmq_trace_validate` artifact rather than more builder performance. See
P2-2 and §8.

## 5. Evidence tier for every positive claim

| # | Positive claim | Tier | Basis |
|---|---|---|---|
| 1 | `stackCartesianShape xs = shape xs` is correct with **no hypotheses** | Kernel theorem | `Shape.lean:946` `stackCartesianShape_eq_shape`; proved via `shape_eq_shape_values` + `buildTree_values`/`buildTree_valid`; axiom-clean |
| 2 | `prepareInput` genuinely consumes the builder; `PreparedInput.shape_eq` invariant holds | Kernel theorem | `SuccinctRMQClassic.lean:44-49` (`shape := Cartesian.stackCartesianShape xs`, `shape_eq := … stackCartesianShape_eq_shape`); `cartesianShape := Cartesian.shape` (line 19) so the equality targets the canonical object |
| 3 | Final-RAM split is a pure, name-preserving, semantics-preserving move | Kernel + artifact | Declaration-name set identical: 225 names old vs 225 new, **0 dropped / 0 added** across `{SuccinctFinalRAM, Segments, FlatPayload}`; builds pass; axiom checks unchanged |
| 4 | Public surfaces preserved (flat-payload, no-synthetic, supplied-store/footprint, all-size, fast-regime) | Kernel theorem | `headline_axiom_check` + `wordram_axiom_check` list `succinctRMQFlatPayloadStoreNoSyntheticExecutionStory`, `…FinalFullModelSoundnessExactOfFootprintGlobal`, `…FastRegimeFinalFullModelCostLeOfFootprintGlobal`, `…GlobalPayloadStoreNoSyntheticExecutionStory` — all axiom-clean |
| 5 | Harness runs correctly; model/runtime and all-size/fast-regime distinctions live | Executable validation | `rmq_succinct_classic_cost_harness`: "all reported windows agree"; output carries `modeledTraceCost … is not wall-clock runtime`, `cleanAllSizeBound=4144`, `fastRegimeBound=118`, `route=…` |
| 6 | New builder is scalable enough to unblock R5 profiling | Executable validation | `--shape-profile-size 32768` → `route=ready` in 0.77 s (vs prior reference-builder timeout at n=2048) |
| 7 | Executable gains not misrepresented as theorems | Process + artifact | DD-005 + harness banner + `RMQ_EXTRACTION_FRONTIER.md`: "runtime engineering evidence rather than a Lean runtime-complexity theorem or a change to model-cost claims"; docs *under*-claim the measured speedup |
| 8 | Design decisions logged with rationale + rejected alternatives | Process evidence | `DD-20260709-005` (3 options incl. the rejected "unproved executable shortcut"), `DD-20260709-006` (3 options incl. rejected "rename public surfaces"), `WDD-20260709-014` |
| 9 | Worker-prompt / coordinator process enforcement | Process evidence | `WORKER_PROMPT.md` now names skill + already enforces branch/base/worktree/final-commit reporting, DD checks ("clear enough that a future paper writer can reconstruct the design"), verification; `rmq-coordinator/SKILL.md` mirror |

## 6. To-the-letter / not-in-spirit risks considered

- **"A theorem whose hypotheses already contain the answer."** *Rejected.*
  `stackCartesianShape_eq_shape (xs : List Int) : stackCartesianShape xs = shape xs` has **zero
  hypotheses**; validity/inorder invariants are *proved* for `buildTree` (`buildTree_valid`,
  `buildTree_values`), not assumed at the boundary.
- **"A renamed wrapper that leaves the real public path unchanged."** *Rejected.* `prepareInput`
  actually swaps its stored `shape` field from `cartesianShape xs` to
  `Cartesian.stackCartesianShape xs` and re-discharges the `shape_eq` invariant; it is not a
  rename around an unchanged call.
- **"Executable evidence presented as theorem evidence."** *Rejected.* Every performance
  statement is explicitly demoted to runtime evidence in the harness banner, DD-005, and the
  frontier doc. `FAMILY_SUMMARY` lists the builder in a "proved" column, but the thing proved
  (`stackCartesianShape_eq_shape`) is a genuine theorem stated as such.
- **"A refactor that hides semantic debt instead of clarifying it."** *Rejected.* The retired
  segments (26/27 "resolve to no words", 28 "not counted") keep verbatim accounting comments and
  the `…retiredFiniteSmallInterior_none` theorem; the split isolates the storage story from the
  query-replay proof without altering it (225→225 declarations).
- **"Docs that overstate branch progress."** *Rejected.* The import-closure counts are non-blank
  Lean lines, verified approximately accurate at both base and HEAD (see P3-2), with small
  plausible deltas — not bloat and not stale. The frontier doc removed the old concrete thresholds
  and *under*-claims the real speedup rather than overstating it.
- **"Design logs recorded too vaguely for future paper exposition."** *Rejected.* Both DD entries
  record the proof device (valued executable Cartesian tree; root-is-leftmost-minimum invariant)
  and named rejected alternatives — reconstructable for a CPP design-choices section.
- **"Correct but advances a different plan."** *Partially flagged (P2-2), not a P1.* The work is
  on the roadmap ladder (R4/R5), and the R5 prerequisite it clears was explicitly named in-repo;
  the concern is only *which* rung is most valuable next, not that the work is off-plan.

## 7. Verification commands (run / skipped)

**Run — all passed:**

- `git fetch origin`; `git status --short --branch`; `git log --oneline --decorate -20`
- `git diff --stat c49f4a4..37abaf8` (14 files, +2624/−1993); `git diff --check` (clean)
- `lake build RMQPaper` — success
- `lake build RMQ.Core.SuccinctRMQClassic` — success
- `lake build RMQ.Core.SuccinctFinalRAM` — success
- `lake build RMQ.Validation.SuccinctClassicCostHarness` — success
- `lake exe rmq_succinct_classic_cost_harness` — "all reported windows agree"
- `lake exe rmq_succinct_classic_cost_harness -- --shape-profile-size 32768` — `route=ready`, 0.77 s
- `lake env lean scripts/headline_axiom_check.lean` — clean axioms, exit 0
- `lake env lean scripts/wordram_axiom_check.lean` — clean axioms, exit 0
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples lakefile.toml` — no matches
- `rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples` — no matches
- `scripts/design_decision_check.ps1` — exit 0 ("no changed files detected"; see P3-3)
- `scripts/claim_drift_scan.ps1` — "164 hits, 0 strict failures", exit 0
- Independent non-blank line verification of `RMQ_IMPORT_CLOSURE.md`: per-file non-blank counts
  (`SuccinctFinalRAM` 7863→5990, `FlatPayload` 1738, `Segments` 160) and base whole-workspace
  163436 non-blank over 248 tracked files vs doc 162089 — confirms the non-blank metric and that
  the doc is accurate (see P3-2)
- Declaration-name diff old-vs-new for the RAM refactor (225 = 225, 0 drift)

**Note on execution environment:** builds/executables/axiom checks/scripts were run in the
existing repo worktree already checked out at `37abaf8`
(`.worktrees/main-merge-rmq-paper-import-surface`), which had current build artifacts; this is
read-only w.r.t. tracked source. The report itself is written on a fresh branch
`audit/A02-rmq-pre-w10-frontier` in a dedicated worktree.

**Skipped (optional):** `lake build RMQ` and `lake build RMQExamples` (full-tree builds) — not
run to bound audit time; the targeted builds plus both axiom checks already exercise the changed
modules and the paper closure. `lake build RMQPaper` transitively covers the paper-facing surface.

## 8. Best next theorem / docs / artifact / workflow target

**Recommended primary (highest paper leverage): R3 — retire model blemishes to shrink the public
theorem surface.** Concretely: (a) internalize or remove the zero-block guard behind a
supplied-store equality theorem so the public alias no longer exposes it; (b) replace the
conservative "safe footprint" bound with an exact dynamic read-set theorem; (c) fold word-width
and bounded-address side conditions into named well-formedness predicates consumed by the headline
theorem. This directly serves the Success Standard (a reviewer reading the theorem surface) and
removes the `route=zero-block` / `4144`-vs-`118` friction still visible in the harness output and
claim-drift log.

**If R5 is the deliberate sprint target instead:** scope W10 to the *named* R5 artifact
`rmq_trace_validate` — differential checks against `List Int` semantics, trace checks for cost
bounds / no-synthetic events / payload-read coverage, and a benchmark mode reporting wall-clock
separately from model ticks — reusing the now-theorem-backed `prepareInput` path. Do **not** spend
the sprint on another builder-performance artifact; the shape-construction bottleneck is already
retired, and the doc correctly flags payload/query as the remaining runtime cost.

**Secondary (opportunistic): finish R4** by splitting the still-large `SuccinctFinalRAM.lean`
(5990 non-blank / 6284 total lines) along
the boundary DD-006 already names (whole-query interpreter/program layer; bounded-event /
no-synthetic execution-story packets), keeping public aliases stable.

**Workflow polish:** add DD-ID collision-avoidance for concurrent branches (P3-1); make
`design_decision_check.ps1` able to diff a committed branch against its base (P3-3); pin the
`RMQ_IMPORT_CLOSURE.md` whole-workspace count to `git ls-tree` tracked `.lean` files (and label it
as a non-blank-line metric) so the catch-all figure is reproducible and excludes transient files
(P3-2).

## 9. Report file path

`docs/internal/audit_reports/2026-07-09_A02_rmq_pre_w10_frontier_audit.md`, committed on branch
`audit/A02-rmq-pre-w10-frontier` (fresh worktree from `origin/codex/add-audit-decision-log` @
`37abaf8`). Only this file was written; no source/proof/artifact docs were edited.

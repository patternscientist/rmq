# RMQ program plan — paper root, E1, preprocessing, S1

**Date:** 2026-08-13. **Coordinator plan for owner review.**
**Basis:** two multi-agent analyses (17 agents) over the read-only tree at
`audit-v1-rc-3` = `85f3eb9`: a 5-reader fact base + 3 designs + 2 judges + 1
completeness critic for the paper root and E1; a 3-reader fact base + 2 designs
+ 1 adversarial judge for preprocessing and S1. Both judges independently
selected the same winning design in each track; this document is the synthesis
of the winners plus every judge graft-in and critic gap.

**This document deliberately lives outside the repository.** `docs/internal/`
ships in the audit packet (`make_audit_packet.ps1:83-90`), so committing plans
or DDs now would leak coordinator material to the next fresh-blind auditor.
Everything here lands in-repo only at verdict intake, as the DDs and amendments
it schedules.

---

## 0. The four measured verdicts that shape everything

**V1 — Closure minimization is dead. Stop treating file count as the lever.**
The current `RMQPaper` closure (203 files / 202,083 lines) is within **0.4%**
of its import-graph floor (201 / 201,253): re-rooting on the 29 files defining
all 136 referenced identifiers drops exactly 2 files, because the paper's
*statements* (not proofs) reference `buildPayload`, `queryCost`, and the
whole-query trace object, whose defining files sit atop the full construction
tower. The capstone's file alone pins 196 of 202 files; every audited
chokepoint edge is statement-load-bearing. The long-standing "separate minimal
packed root" idea is **measured dead**: a packed-only root is 196 files /
198,880 lines — 3% smaller than today — because the packed statement is
anchored to `buildPayload`'s full classical tower. The only large lever is
dropping the packed claim (−27%), which recreates the exact RC-11 defect
DD-20260809-097 fixed.
→ **What the audits actually punished was never closure size — it was command
time.** Both fresh-blind auditors verified everything ≤20 minutes and
abandoned everything longer. G1 therefore targets the *verification surface*.

**V2 — E1 is not what the roadmap page says.** The roadmap's E1 status text is
stale in both directions. Mainline has 22 `E1*.lean` modules (~15k lines,
kernel-green) but **0 of 11** acceptance rows satisfied at whole-query scope.
The *completed* machine — 68 modules, 9/11 SATISFIED, 2 PARTIAL — lives on the
unmerged branch `claude/b1-b2-charged-fringe-tables` (tip `648e512`), which the
ratified endgame roadmap explicitly **froze** as "historical machine companion —
unmerged and unaudited." E1 is zero-paper-facing today (no citation in the
ledger, correspondence, or audit prompt) and is **not on the V1 critical
path**. The packed reviewer machine and the E1 machine are sibling refinements
of the *same* accepted 210-fuel logical protocol (shared
`RankSamplePresence.lean`; `427 = 1 + 2·3 + 2·210` reuses the protocol E1
simulates). The 9/11 self-report was never externally audited, in the one lane
whose self-reports were repeatedly refuted — treat it as candidate claims.

**V3 — S1 is not preprocessing.** S1 = bit-addressed serialized-payload
*querying* (deferred, non-gating, blocked on `flattenPayloadWords`
non-invertibility). Preprocessing = ledger row `L-OPEN-01` (construction time
and workspace, unproved in any model). They touch the same object and share
zero proof obligations. Landing S1 retires nothing of L-OPEN-01.

**V4 — Preprocessing has a real substrate and one landmine.** The repo has a
mature charged-construction stack for the FischerHeun/LCA *spokes*
(`linearBuild_constantQuery_profile`, `denseLCA_…`, both already in
`axiom_check`) and **zero** cost infrastructure for the paper's actual payload
pipeline. Decisive identity: `packedReviewerPayloadBits = buildPayload` **by
`rfl`** — one costed builder serves the classical space bound and the packed
capstone, killing the two-payload trap structurally. The landmine: several
as-written builders are naively quadratic (nested appends, per-entry prefix
recomputation), so an honest linear bound requires accumulator-refactored
builders *with value-agreement theorems*, not charging the existing
definitions.

---

## 1. Program structure

Four goals, one program:

- **G1 — Reviewer-tier verification surface** (was: "minimal paper root")
- **G2 — E1 completion** as a post-V1 supplementary artifact
- **G3 — Preprocessing** as a new roadmap rung, incremental claim ladder
- **G0 — Standing debts** that gate everything: RC-3 verdict intake,
  `WDD-20260807-014` restoration, merge-to-main, memory/handoff hygiene

Sequencing spine: **G0 → G1 → (G3 ‖ V1 loop) → V1 ACCEPTED → G2 → rung (d)
horizon where G2×G3 meet.** G3's Lean lanes may start early (new files only);
its public claims land only in synchronized candidate merges.

Preemption rules (owner-approvable, recorded as a DD at intake):
1. Audit-round corrections preempt everything.
2. The anonymised AE bundle is never preempted by E1 or polish (ITP 2027
   requires it; tooling is deliberately unbuilt today).
3. E1 has a go/no-go date (~2026-11-15): start its Lean work only if V1 is
   ACCEPTED and ≥6 worker-sessions of runway remain before the ~Jan freeze.
4. If audit rounds exceed ~rc-5, cut reading-order/tex polish — never the AE
   bundle, never a landed claim's gate.

---

## 2. Phase NOW — zero repo writes (runs during the RC-3 audit)

All items are read-only or scratchpad-only. Nothing pushes; nothing lands.

| # | Item | Output |
|---|---|---|
| N1 | **This decision memo** to the owner | approvals for DD-A..E below |
| N2 | **648e512 trial merge** in a scratch worktree (freeze bars merging, not measuring) | conflict-density number feeding E1's effort estimate and the port-vs-rederive choice |
| N3 | **`design_decision_check` classification probe** (read-only): how gate-script and lint edits classify, per-commit | validated DD/WDD choreography for every later phase |
| N4 | **Elaborator-level floor confirmation** (`#min_imports`-style probe) so "minimization is exhausted" becomes evidence before it is written into governance records | one-session report; expected to confirm the 0.4% result |
| N5 | **Draft G1's checks in scratch**: the split headline check, the citation checker (resolving at the *pinned* commit, never HEAD), the closure re-measure script | ready-to-land candidates |
| N6 | **Recorded timing baseline** on the Windows reference machine: per-command wall-clock for the intended reviewer tier | the acceptance evidence for tier docs (a green tier doc without a recorded run is the repo's own defect class applied to wall-clock) |

**Blindness rule** (resolves a flaw all three designs shared): until the RC-3
verdict lands, side-branch work stays in **local worktrees, unpushed**. The
standing push-to-green rule applies at landing time, not during the blind
window. Auditor-visible surfaces (`docs/internal/*`, packet contents) change
only at verdict intake.

---

## 3. Phase VERDICT-INTAKE (when RC-3 returns; ~1–2 coordinator sessions)

Runs regardless of verdict; order matters.

1. **Disposition + round log** (standing default).
2. **`WDD-20260807-014` restoration record** — RC-02 *passed* the 08-12 audit,
   so the U3 subsumption's source-level obligation is discharged; the
   restoration record is still owed and no design contained it. Land it with
   the disposition; correct the stale memory note in the same breath.
3. **Merge-to-main integration** (critic gap 6 — currently three-deep debt):
   ff/merge `origin/main` to the accepted commit, push watched to green
   (never a `v*` tag), sync local main. Acceptance: `origin/main == accepted
   commit, CI green`. Only then do new branches cut from integrated main.
4. **Commit the DD packet** (drafted in N1): DD-A/B/C/D/E below.
5. **Paper-pin protocol** (both judges flagged its absence): any landing that
   touches `RMQ/` or adds ledger rows triggers *exactly one* repin per landing
   round, done **last**, with the citation checker run *at the new pin* as the
   repin's acceptance gate. The `ARCHITECTURE_RESULT_PENDING` replacement in
   `rmq.tex` rides a repin round.
6. If NOT_ACCEPTABLE: fold G1 items 1.2/1.5 (spoke contradiction, stale
   closure doc) into the correction round — they are the two most likely
   findings anyway.

**Owner decisions in the DD packet:**

- **DD-A (root):** adopt the status-quo root + verification-surface program;
  formally retire "separate minimal packed root" **with the measurement**
  (packed-only = 196/198,880 — not minimal). Closes the escalation in
  DD-20260809-097.
- **DD-B (spokes):** resolve the live manuscript-vs-correspondence
  contradiction (manuscript states rank/select + BP-nav as claims; the
  correspondence declares them outside the root; 6 of 53 checked names are not
  importable from `RMQPaper`). **Recommend re-scope** (repository-surface
  claims, reworded Contributions item; zero closure cost; the paper keeps ONE
  import answer). Includes the ACCEPTED_BASE-demotion protocol: appended
  amendments only, `check_paper` bidirectionality handled in one commit, and
  the change disclosed to the next auditor rather than discovered.
- **DD-C (E1):** post-V1 supplementary root `RMQE1` at logical-store
  granularity with an explicit non-packed disclaimer; un-freeze/port `648e512`
  after V1 ACCEPTED as *a candidate with matrix evidence re-verified, never a
  raw merge*; mandatory fresh-blind audit before any public claim; keep the 22
  mainline modules as the substrate the port completes. Roadmap amendment
  retires the stale E1→V1 DAG edge — landing **with or after** the WDD-014
  restoration (the amendment redraws U3's DAG while U3's acceptance is being
  restored), re-homes S1 explicitly (stays deferred, gates nothing), and
  preserves the M1 fence ("E1's completion discharges no part of M1").
- **DD-D (preprocessing):** create the new rung (proposal: **PRE — Charged
  Construction**); pin the built object (`buildPayload`, and by `rfl` the
  packed payload — one object for space, capstone, and construction); charge
  policy: *instrumented-only, no decree ticks, value-agreement mandatory,
  all-size literal constants*; asymptotic-only rung rejected. S1 disposition
  per V3, plus: enumerate the "four surfaces" carrying serialized-payload
  disclaimers **before** any adjacent wording edit. Record numeric tripwires
  in the DD itself (access-lane split threshold; TraceEvent-conservativity
  churn threshold triggering the separate-event-type route).
- **DD-E (measures, named now, detailed at phase start):** the workspace
  measure (what counts: recursion state? the `Costed` structure? only named
  intermediates?) must be DD'd **before** the workspace lane starts; the
  Int-honesty side condition (unbounded `Int` inputs vs trans-dichotomous)
  is a *named hypothesis in the theorem and the ledger row*, not just a DD.

---

## 4. G1 — Reviewer-tier verification surface (~5–6 worker + 2 coordinator sessions)

Branch off the accepted commit post-intake. The goal is the end state both
auditors' behavior defines: **one import, one screenful, every command ≤20
minutes, no TeX on any claim path.**

| # | Item | Key content | Acceptance |
|---|---|---|---|
| 1.1 | **Split the headline check** | `headline_axiom_check.lean` (same filename — the topology lint pins five `#print` anchors into it) imports **`RMQPaper` only** (204 modules, not 317: ~⅓ build-time cut, the frozen expected-type pin and anti-bypass blocks retained). Spoke + Impl prints move to a new repository-tier check. Fix the known design defect: the spoke *aliases* live in the barrel `RMQ/Headlines.lean`, so the repository-tier check either imports the barrel (acceptable at that tier) or prints the source theorems via direct module imports. **Fallback** (if RC-4 findings touch gate scripts): land a purely additive `RMQPaper`-only check first, keep the pinned file byte-identical, with an explicit sunset commit so the two-inventory state never reaches a tag | both checks exit 0, standard axioms; deletion-mutation per check added to the lint regression; **plus a control that the check's own import closure equals its documented root** (the judges' point: negative controls must test the real defect class, not the authored one) |
| 1.2 | **Execute DD-B** (spoke re-scope) | manuscript wording + appended ledger amendments; zero Lean changes | `check_paper` green; anchors bidirectional in one commit |
| 1.3 | **Tier the reproduction surface** | TRUST_AUDIT_PACKET split into Reviewer tier (build + 5 fast checks, no TeX) and Maintainer tier (gate, campaigns, regressions); Reading Order starts at `Headlines/RMQ.lean` (818 lines), not `SuccinctFinalRAM.lean` (10,027) | the N6 **recorded timing run** is the acceptance evidence; no reviewer command >20 min |
| 1.4 | **Machine-checked citations** | the deferred `file:line→declaration` checker over the theorem ledger (the L-UB-06 defect class: 1,090 lines off at its own pinned base, unseen by an audit); resolves **at the pinned commit, never HEAD**; extend `ledger_decl_check` from 53 toward the full ~78 cited names — *gated on the L-UB-13 tier adjudication* so validation guards aren't codified into a paper check before the owner decides their tier | exits 0 on the tree AND fails on a wrong-line negative control; registered in gate + Reviewer tier |
| 1.5 | **One authoritative closure number** | `RMQ_IMPORT_CLOSURE.md` still publishes 153/139,054 (pre-promotion) and ships in the audit packet; the fact base itself had three inconsistent measurements. Publish one scripted measurement with method stated + a generated per-cone import manifest (the legibility lever that remains once minimization is exhausted) | regenerated table matches a committed script's re-run |
| 1.6 | **Fix the blindness leak** | `claim_drift_scan` default root prints prior-audit snippets to fresh auditors (both disclosed contamination); exclude `docs/internal/audit_reports` from the default root, policy regression in lockstep | injection-verified; packet advisory regenerated |
| 1.7 | **AE anonymisation lane** (graft-in; both judges demanded it) | scripted anonymised-bundle pipeline: strip CITATION/URLs/release refs, exclude `docs/internal`, no DOI in the submission; **seeded-canary self-test** (a planted identifying string must be caught) | canary caught; bundle builds from the tagged tree |

Landing: one candidate branch, synchronized surface edits atomic with their
checks, repin last, packet regenerated, round-log entry.

---

## 5. G3 — Preprocessing (PRE rung; first public claim ~9–12 sessions in)

Winner: **incremental ladder**, with the judge's central amendment adopted:

> **Rung (b) is never published standalone.** The instrumented costed builder
> lands as *unpublished scaffolding* unless its per-stage
> bounded-work-between-charges lemmas (the query side's own honesty criterion)
> are proved. The **first public claim is rung (c)**.

**PRE-1 (scaffolding, ~7–10 sessions; Lean lanes may start pre-verdict on new
files, local only):** four lanes —
shape lane (`stackCartesianShapeCosted` via the existing stack builder +
amortized bound; value-agreement through `stackCartesianShape_eq_shape` so the
canonical `Cartesian.shape` is covered without costing the quadratic spec);
access lane (single-pass prefix-statistics builders for the 18 directory
sources — the largest refactor, split tripwire per DD-D);
close lane (5 interior tables as per-block scans);
universe-table lane (o(n) build lemma mirroring the existing o(n) space lemma).
Composition: `buildPayloadCosted` with `_value = buildPayload`, closed-form
cost, `≤ c·n + o(n)`; `packedReviewerMemoryCosted` **only after a DD on the
Stage-A surface interaction** (the packed memory is accepted Stage-A surface;
costing its header/pad/chunk stages touches audited ground — a shared flaw
both designs silently skipped).
**Anti-theater conjunct (judge graft-in, mandatory):** charged write count
**= emitted payload length** — ties the charge policy to emission of the exact
object the space theorem measures, converting charge-policy vacuity from a
grep-hope into a checkable theorem.

**PRE-2 (rung (c) — the publishable centerpiece, ~8–12 sessions):**
charged-trace construction with **final-store equality**: the built store
equals the canonical store every query-adequacy theorem consumes. Without that
join conjunct the rung is the repo's named defect class. Model decision by
conservativity spike: extend `TraceEvent` with `writeWord` *only if* every
accepted `readWord_only` surface re-verifies unchanged and the packed
independence check still passes; at the churn tripwire, take the
separate-`BuilderEvent`-plus-translation route immediately — **extending an
accepted inductive re-opens acceptance** (both judges), so any accepted-file
edit beyond mechanical case-addition means the fallback, and never while an
audit is in flight on those files. Ledger: `L-OPEN-01` superseded by the
proved row + explicit residual (instruction-level time → cross-ref L-OPEN-06;
workspace → PRE-3), with the Int-honesty hypothesis named in the row.
Public wording flips **only here**, atomically, on ~10 surfaces (the P1-01
lesson: fixing a claim at its origin is not fixing the claim — the surface
inventory is enumerated in the design and lands as one synchronized edit).

**PRE-3 (workspace, ~4–6 sessions):** the DD-E measure, published in
`PAPER_MODEL_ADEQUACY.md` **before** the audit; spine-stack telescoping ≤ 2n
bits; per-stage peaks (feasible precisely because PRE-1 replaced the
quadratic-intermediate builders). Audit brief explicitly targets
measure-smuggling.

**Rung (d) — horizon only, zero sessions allocated:** preprocessing stated in
the E1 machine (the FH11-shaped "O(n) preprocessing time" sentence). Hard
preconditions: L-OPEN-06 closed, E1 accepted (G2 done), owner DDs on matrix
amendment and input representation. This is where G2×G3 meet — and why G3
deliberately does **not** wait for E1: the owner's preprocessing request must
not be hostage to a different open rung.

Every PRE phase: frozen per-candidate acceptance matrix, coordinator audit +
fresh-blind AUD1 on the exact commit, gates extended at **every** landing
(independence check stays clear of new construction constants; strict
claim-drift tokens per new claim, injection-verified), **audit brief written
into the phase** (injection gates cannot check semantic honesty —
instrumentedness and measure adequacy are audit questions).

---

## 6. G2 — E1 (post-V1; go/no-go ~2026-11-15; ~9–13 sessions + audit)

1. **Reactivation gate** (coordinator): freeze-lift record; appended amendment
   fixing the stale "hence ≤ 207" in the frozen matrix cell (reserved-for-
   coordinator item); adjudicate the REQ-E1-06 `Nat.log2` residual using the
   branch's count-indexed-table resolution as evidence; roadmap amendment per
   DD-C.
2. **Port `648e512`** (informed by N2's conflict number): as a re-verified
   candidate. **Fallback:** if conflict density is high, re-derive only the 16
   `E1WholeQuery*` composition modules against the current tree, reusing the
   branch's component theorems verbatim.
3. **Close the two PARTIAL rows:** REQ-E1-03 (promote the arm-scoped
   corruption witness to whole-query — the hard one; escalate rather than
   weaken) and REQ-E1-08 (whole-query positional receipt diff; reference
   implementation split into a zero-machine-imports module).
4. **Executable evidence on mainline:** `lean_exe e1_validator` — fixtures,
   differential answers vs the independent reference, mutants gating the exit
   code, no-synthetic + successful-read coverage, model ticks reported
   separately from wall-clock (the ratified deliverables, named verbatim).
5. **`RMQE1` supplementary root** + one-screenful `e1_axiom_check`, registered
   on all five operational surfaces in one atomic commit with the
   correspondence doc naming it **non-paper** (RC-11's one-answer property
   never has a coexistence window). `ledger_decl_check`: import the new root
   AND transcribe the new row's names, bumping `expectedCount` — the
   existence-unchecked-names gap the critic caught.
6. **Fresh-blind audit of the never-audited rung** — with the ARCH2 regression
   catalog (proxy obstruction, disconnected execution, uncharged projection,
   frozen-contract drift, non-replayable mutation evidence) in scope. Public
   claims (ledger row `L-E1-01`, manuscript subsection) **blocked on the
   verdict** — audit failure costs schedule, never claim integrity.
7. **Paper integration:** one subsection — *one logical protocol, two
   refinements: cell-probe (space/probes, headline) and word-RAM instruction
   steps (operational, strengthening)* — answering the recorded referee
   objection ("modeled cost is not real") without a bolt-on. Statement fences:
   the M1 fence; never phrased as serialized-payload querying (S1's four
   surfaces); the third `210` (E1's logical-protocol 210) added to the
   independence-check story. AE-bundle membership decided at the go/no-go: if
   E1 defers post-submission, the submission names it banked strengthening.

**The reviewer's terminal session at the end of G1+G2+G3:**

```
$ lake build RMQPaper                       # ~8–9 min: the 204-module paper closure, never 317
$ lake env lean scripts/headline_axiom_check.lean    # ~60 s, one screenful, standard axioms
$ lake env lean scripts/ledger_decl_check.lean       # seconds: every ledger-cited name exists
$ lake env lean scripts/ledger_line_check.lean       # seconds: every file:line citation resolves (at the pin)
$ lake env lean scripts/independence_check.lean      # seconds: the 210s are independent
$ pwsh paper/check_paper.ps1                         # seconds, no TeX
  # -- optional, clearly labeled supplementary --
$ lake env lean scripts/repo_surface_axiom_check.lean   # spokes + Impl, repository tier
$ lake build RMQE1 && lake env lean scripts/e1_axiom_check.lean
$ lake exe e1_validator                     # mutants flip the exit code; ticks ≠ wall-clock
```

---

## 7. Explicit non-goals

- Closure-minimization campaigns (0.4% headroom, measured; N4 confirms before
  this enters governance records), Core file splits, Segments/SuccinctFinal
  severing, repointing `RMQPaper.lean` (lint-forbidden), any second *paper*
  root.
- C/Rust generation before the reference-machine theorem is accepted.
- Resuming the banked B2/B3/B4/A4 architecture threads.
- S1 in any form now; rung (d) now; rung (e) (asymptotic-only) ever, standalone.
- Any "first"/priority phrasing (novelty-log restriction); any word-RAM
  instruction-time or wall-clock claim ahead of its rung.
- Touching the frozen E1 matrix's requirement wording (appended amendments
  only); editing the rc2-corrections worktree while the verdict is pending.

## 8. Risk register (top line)

| Risk | Mitigation |
|---|---|
| RC-3 NOT_ACCEPTABLE mid-program | side branches self-contained; G1 1.2/1.5 double as findings corrections; PRE Lean lanes unaffected |
| Owner-decision stall (the minimal-root DD sat open 4 days) | every DD carries a recommended default + decision date; default executes if the date passes (recorded as such) |
| Vocabulary extension churns accepted proofs | conservativity spike first; numeric churn tripwire → separate event type; never during an in-flight audit |
| Access-lane refactor stalls | per-source sub-candidates after the tripwire; never fall back to charging as-written quadratic builders |
| E1 port reveals unsoundness in the 9/11 self-report | public claims blocked on the fresh-blind verdict; N2 trial merge prices the port before commitment |
| New checks vacuously green | negative controls must test the real defect class (closure-equals-documented-root; wrong-line; canary), not the authored failure |
| Wall-clock claims without evidence | N6 recorded timing run is the tier docs' acceptance gate |
| Blindness leaks via packet/branch | local-until-verdict rule; packet regenerated per landing; audit-report dir out of the default scan root |

## 9. Effort and calendar

| Track | Effort | Earliest start | Lands |
|---|---|---|---|
| NOW probes (N1–N6) | 2–3 sessions, zero repo writes | today | pre-verdict |
| Verdict intake + DD packet | 1–2 coordinator | RC-3 verdict | with disposition |
| G1 reviewer surface | 5–6 worker + 2 coord | post-intake | next 1–2 rounds |
| PRE-1 scaffolding | 7–10 worker | Lean lanes: now (local) | post-G1 landing |
| PRE-2 first public claim | 8–12 worker + audit | PRE-1 | ~autumn |
| PRE-3 workspace | 4–6 worker + audit | PRE-2 | autumn/winter |
| V1 freeze + AE bundle | per V1 checklist; AE lane from G1 1.7 | RC loop closes | before ~Jan freeze |
| G2 E1 | 9–13 worker + coord + external audit | V1 ACCEPTED, go/no-go 11-15 | winter, or named as banked strengthening |

ITP 2027 (~Feb deadline) is feasible if V1 closes within 1–2 more correction
rounds. The drop-dead rule: at the freeze date, the program publishes the
strongest *already-landed* rung of every track and nothing more.

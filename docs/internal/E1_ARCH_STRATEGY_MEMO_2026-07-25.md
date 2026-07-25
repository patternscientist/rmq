# E1 architecture strategy memo — final judgment input

Prepared: 2026-07-25 by C06 (Claude runtime), from a 31-agent research campaign
over the complete Codex-produced E1 corpus: 11 deep readers (accepted reports,
both unmerged code lanes, paper surface, governance history, outside
precedent), 8 load-bearing claims each adversarially verified by two
independent lenses, and a 3-judge panel run twice (once before and once after
the owner's calibration clarification). Every factual statement below survived
adversarial verification against primary sources; corrections applied by the
verifiers are incorporated. **This memo recommends; the owner decides.**

Owner objective (verbatim): "the strongest, 'this is technically justifiable
but reviewers have to spend brainpower auditing the justification as opposed
to pattern matching against precedent'-minimized version of the RMQ spoke."
Owner calibration: precedent-fit is a cost, not a veto; the clause guards
against stopping prematurely at a merely-justifiable state. Runway: ~4 weeks.

---

## 1. Findings that reframe the question

**F1. The strict A4 select-before-implement procedure is process armor, not a
paper requirement.** It was instituted incrementally by the ARCH1/ARCH2
campaigns after five superficially-green or proxy-obstructed candidates
(assumed capstone, disconnected opcode lists, proxy obstruction). No recorded
decision requires the paper to contain a route selection. The verdict-algebra
decision it rests on (DD-20260722-003) exists only on campaign branches, its
status line still reads "coordinator decision is required," and it never
reached main's ledger. The roadmap's paper-facing E1 rung asks only for a
small familiar machine with result agreement and step/trace-cost
correspondence — no selector. (Verified: main's DD ledger jumps 20260722-002
→ 20260724-001; roadmap `:449-470`.)

**F2. The A4 HISTORICAL arm is structurally unreachable.** Under both selector
texts (accepted PRELOGIC blob `086abee6` L537-581; handoff dossier), selecting
the historical route requires a checked *universal* B2 impossibility proof —
"quantify every permitted base receipt" — which no document costs, no one has
sketched, and accepted PRECUR renders implausible by affirmatively charting
B2's lowering. Consequence: **B3 can never lawfully become "the architecture"
without an owner amendment — so every B3-publishing path already requires the
same one-DD instrument that permits skipping the procedure entirely.** The
case for running the strict procedure to completion collapses.

**F3. The north-star plan exists** — recovered at
`docs/RMQ_UNIMPEACHABLE_COST_PLAN.md` on unmerged branch
`docs/unimpeachable-rmq-plan` (sole commit `2562684`, 2026-07-07; two readers
missed it under `docs/internal/`). Its centerpiece is **Workstream A
executable cost evidence** (compiled harness, differential testing, measured
trace tables, `n ≥ 2^15`); its **A3 machine is "the flagship strengthening"**
— a *standard* ~10-instruction word-RAM with a simulation theorem, the trace
layer as an IR "with a proved bridge on both ends," and a per-leaf fallback
the plan deems publishable as in-progress. The plan's own referee table says
the machine exists so referees "pattern-match, not audit." A1/A2 are
partially delivered on main today (`rmq_succinct_classic_cost_harness` with
theorem-equal Array-backed prepared mirrors) but only at fixture sizes
64-128, not the plan's 2^15 goal.

**F4. The 648e512 lane is kernel-complete for its own contract.**
`amendedFamiliarMachineTarget_holds` at
`648e512:RMQ/Core/WordRAM/E1AmendedTarget.lean:620`: a 5,646-instruction
familiar machine, six-category per-instruction charging, memoryRead count =
per-query modeled cost as kernel equality (route constant 210), positional
receipt equality with the accepted trace, public-answer agreement, step
literal 11,886; zero sorry/axiom/native_decide. Its matrix at that ref: 8
SATISFIED / 2 PARTIAL (harness rows) / 1 NOT SATISFIED (docs row). What
remains is docs, a real merge (328/352 collision; 207→210 cost-spine
migration, same class that cost M1 five rounds), and the **never-run**
fresh-blind audit (base 8e7e3ee prepared). Its honesty bound is fixed by
accepted PREHIST: it executes against a shape-derived logical ReadStore with
geometry entering as uncounted constructor advice — "not yet a true machine
route under the same counted image." That sentence bounds what it may ever be
called.

**F5. Outside precedent (web-verified).** The published mechanized-cost
ceiling *for data structures* is LLVM-IR instruction counting
(Haslbeck–Lammich ESOP 2021), which self-classifies at Level 2 of the
Charguéraud–Pottier hierarchy and hedges ("at best a rough approximation").
No verified word-RAM/ISA-level cost theorem for a data structure exists in
any ITP. Two sharpenings from adversarial verification: (a) CPP 2026
(Tockman et al., Bedrock2/RISC-V) now provides a citable precedent for
ISA-level verified time bounds — for interactive machine code, not data
structures — so a machine-level claim is no longer zero-precedent; (b) the
current shipped story pattern-matches the **cell-probe model**, the native
model of this exact problem's published lower bounds (Liu–Yu STOC 2020), and
mechanizes *strictly more* of the between-events boundedness step than any
cited precedent — that exact wording, not "fully mechanizes."

**F6. Today's public surface depends on zero ARCH2 artifacts** (B1 is not an
ancestor of main; RMQPaper's 150-file import closure contains no E1 modules)
and is consistent modulo two or three one-line drift fixes. Countervailing
staleness that must be reconciled regardless of strategy: main's E1 matrix
header pins 207-era objects while the kernel says 210; the roadmap E1 rung
still states the kernel-refuted fully-charged target; the handoff dossier on
main reprints the three-arm selector that accepted PRELOGIC deleted.

**F7. Effort landscape (verified against committed sources only).** B3
remainder: ~6-12 focused engineer-days by the record (PREHIST 8-16 total,
minus "roughly the first quarter" consumed), with one untouched novel risk —
charged derivation of interior geometry, which has **no established B1
descriptor slots at all** — and PREHIST's only calibration datum on novel
territory is a 4-8x slip (mul/div: half-day probe budget, three rounds
actual). B2: unlaunched once-refuted descriptor precondition, then ~20-35
agent-days (accepted PRECUR) — exceeds the runway at the lower bound. Lane
648e512: zero open Lean obligations; merge + docs + audit ≈ 3-6 sessions
(coordinator-narrative tier, not committed).

---

## 2. The judgment

**Recommendation: the S5 hybrid.** Both judge panels (pre- and
post-calibration) rank it first or tied-first; under the owner's calibration
it wins the reviewer lens 9.0 and honesty lens 8.5, and is second on schedule
only to doing less.

1. **Headline (ships V1): the current M1-anchored story**, upgraded with
   precedent-matching prose: self-classify in the Charguéraud–Pottier level
   taxonomy; name the model cell-probe-shaped citing Liu–Yu (charged-read
   count on the same axis as their t); state that the between-events
   boundedness that prior work argues informally is here *strictly more*
   mechanized than the published ceiling, scoped against Bedrock2; fix the
   two drift lines (`artifact/CLAIMS.md:44-45`, `README.md:223-225`).
   Zero new Lean. Days.

2. **Companion (non-gating): merge and fresh-blind-audit the 648e512 lane**,
   published in PREHIST's own accepted vocabulary — "a fully charged familiar
   machine over the canonical logical store computes the same answers within
   a checked step literal; geometry disclosed as model input" — never "word-
   RAM execution," never "the counted image." This converts the paper's
   "documentary omissions" paragraph from prose into a kernel theorem, and it
   is what stops S4 from being the under-shooting the owner's clarification
   guards against: declining to publish a finished, zero-open-obligation
   machine theorem is the "weaker claim chosen for comfort" failure mode.
   **De-risk gate first:** dry-run the merge in a scratch worktree; if it
   exceeds ~3 sessions, degrade the companion to S4's appendix paragraph and
   ship anyway (the headline never depended on it).

3. **One owner DD** that: supersedes the A4 ordering for publication;
   records B2 and B4 as UNRESOLVED-and-unpursued in DD-20260722-003's own
   vocabulary (deliberate, honest, reversible); dispositions the
   handoff-vs-PRELOGIC selector contradiction; and adopts or explicitly
   defers DD-20260722-003 itself, which has technically never been accepted.

4. **B3 continues only probe-gated and non-gating.** Run the two half-day
   probes first — interior-geometry literal provenance (the one item that
   could reopen architecture at owner level) and the tiny-size width floor
   (`151 < 2^w`, branch targets ≥ 5,644 at smallest sizes). Both clean → B3
   R4 proceeds in parallel as strengthening that, if it lands, upgrades the
   companion to the counted image with zero headline change — exactly the
   north-star plan's machine-as-strengthening-layer structure. Either probe
   dirty → honest closure prose banking the three durable decisions (monus
   DD-20260724-001, operational arithmetic correspondence, ROM typing
   DD-20260725-003). B3 never gates V1.

5. **Close the A-gap cheaply:** extend the existing cost harness toward the
   plan's `n ≥ 2^15` measured-scale goal (pure engineering on existing
   theorem-equal mirrors; directly the north star's centerpiece).

**What this is not:** not a retreat from the machine result (it publishes the
one that exists, at its honest granularity, and keeps the counted-image
upgrade alive); not an abandonment of ARCH2 (B1, the three PRE reports, and
three B3 rounds are banked as the appendix narrative and live strengthening
path); not a silent skip of governance (the DD is the explicit, recorded
instrument — the same one every other path needed anyway, per F2).

**Why not the alternatives.** S1 (B3-to-verdict) requires five independent
gates to all pass inside the runway against a 4-8x calibration precedent, and
even total success yields a verdict that cannot be narrated as a selection
(F2) — a standing drift temptation. S2 (B2-first) exceeds the runway at its
verified lower bound with an 0-for-3 candidate record. S3 (648e512 as *the*
headline) puts the precedent-free model-fairness question in the load-bearing
position where the project's own accepted records ("not yet a true machine
route") could be quoted against it — survivable as a caveated companion,
refutable as a headline. S4 alone is the premature stop.

## 3. Panel disagreement, disclosed

The schedule judge ranks S4 first (9.0) over S5 (8.0) because S5's merge is
real unpriced work whose only precedent (M1's spine migration) cost five
rounds, and named the flip condition: a dry-run merge landing in under ~2
sessions flips S5 decisively first on that lens too. The recommendation
adopts that flip condition as S5's built-in gate rather than treating the
disagreement as unresolved. The other two judges rank S5 first outright; all
three rank S2 last or next-to-last.

## 4. Stale records to correct regardless of strategy

- Owner memory index line still says "cost-model fork pending (Option A
  rec.)"; DD-20260717-C05-001 records Option B adopted 2026-07-17 by the
  owner personally. (Note body is correct; index line is stale.)
- Main's E1 matrix header (207-era pins) vs kernel (210); roadmap E1 rung
  still states the kernel-refuted fully-charged target.
- The handoff-vs-PRELOGIC selector contradiction is arguably the fourth
  instance of the frozen-text-contradicts-accepted-input defect family
  (third is ledger-counted in DD-20260725-003; the verifiers note instance
  counting is convention-dependent). Per the owner's standing statement, a
  fourth instance triggers recording the general rule.

## 5. Decision points for the owner

1. Adopt the S5 shape (headline + gated companion + one DD + probe-gated B3)?
2. Authorize the dry-run merge of 648e512 (scratch worktree, read-only
   de-risk, no integration authority implied)?
3. Authorize the two B3 half-day probes?
4. Record the general frozen-text-yields-to-accepted-input rule now, on the
   arguable-fourth instance, or wait for an unambiguous fourth?

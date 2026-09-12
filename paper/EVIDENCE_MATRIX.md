# Evidence Matrix (frozen)

Frozen acceptance rows for the manuscript/evidence substrate authored on
branch `codex/eg-cp-paper-evidence-r1`; base commit
`3849ecbb53bbedfcd679352cc68d095fa5a304c2` (branch
`codex/fully-charged-packed-query-v1`). Row IDs and requirement text
are frozen as of 2026-08-05; evidence and status fields are append-only.
Statuses: **CLOSED** (evidence in place at this commit),
**BLOCKED_ONLY_ON: ARCHITECTURE_RESULT_PENDING** (nothing remains except
the independently accepted packed all-size result), or
**BLOCKED_ONLY_ON: EDITORIAL_INSERTION** (used by the 2026-08-07 status entry:
the result was accepted and only its insertion into the manuscript remained), or
**BLOCKED_ONLY_ON: FRESH_BLIND_ACCEPTANCE** (added 2026-08-16: nothing
remains except an external audit verdict). No other status is permitted for
this substrate; a row that could not reach one of these states would mean the
substrate is incomplete.

`EDITORIAL_INSERTION` had been in use since 2026-08-07 without ever being
listed here, and `FRESH_BLIND_ACCEPTANCE` was added by the RC-4 round the same
way. Both were found only when the enforcement below was written -- the rule
"no other status is permitted" had been violated twice while stated.

The RC-4 round appended its status to `EV-07`
without amending this list, leaving the file asserting a vocabulary it
violated one screen later. `paper/check_paper.ps1` now enforces the list, so a
status outside it fails rather than merely contradicting this paragraph.

This matrix records manuscript-substrate evidence only. It is not an
architecture acceptance record, records no coordinator acceptance, and
closes no roadmap node.

---

## EV-01-MODEL-FIDELITY

- Requirement (frozen): the manuscript keeps payload bits, allocated bits,
  charged probes, model ticks, and Lean wall-clock time distinct; states
  the declared charge policy exactly as the repository documents it;
  never presents the charged-trace bound as conventional word-RAM running
  time; and states construction/preprocessing complexity as open.
- Evidence: `rmq.tex` Section 3 defines the five quantities separately and
  reproduces the charged/uncharged policy from
  `docs/PAPER_MODEL_ADEQUACY.md`; Section 3 and Section 11 item 1 disclaim
  conventional word-RAM running time (ledger L-OPEN-06); Section 11 item 2
  states preprocessing open (L-OPEN-01); Section 8 keeps measurements in
  separate columns from theorems. `check_paper.ps1` forbids the phrase
  pattern the roadmap bans for cell-probe/charged-trace claims.
- Status: CLOSED
- Evidence (appended 2026-09-11, repin to `3849ecbb`): Section 3 now keeps six
  quantities apart. The sixth, executed instructions, belongs only to the
  candidate theorem of Section 9.2 (`L-PQ-01`) and is never attached to the
  `210` or `427` bounds. `L-OPEN-06`, cited above for the word-RAM
  disclaimer, is amended rather than retired: `L-PQ-01` falsifies its first
  clause, and the row now states only that neither the charged-trace bound
  nor the cell-probe bound counts controller steps or is claimed as
  conventional word-RAM running time. Its anchors in Section 3 and Section 11
  item 1 stay. The charge-policy paragraph is scoped to the charged-trace
  model. Preprocessing remains open (`L-OPEN-01`).

## EV-02-THEOREM-IDENTITY

- Requirement (frozen): every non-provisional mathematical claim sentence
  in the manuscript maps through a ledger anchor to an exact Lean
  declaration and file at the base commit, with proposition-level
  hypotheses and conclusion recorded; the provisional target maps to a
  PROVISIONAL_ARCHITECTURE row; unproved statements map to OPEN rows.
- Evidence: `THEOREM_LEDGER.md` (36 rows: 30 ACCEPTED_BASE, 0
  PROVISIONAL_ARCHITECTURE, 6 OPEN -- updated 2026-09-11 from 34/29/0/5, when
  `L-PQ-01` and `L-OPEN-07` were added at the repin to `3849ecbb`; corrected
  2026-08-16 from a stale
  27/1/6 that predated the Stage-A acceptance moving the architecture row out
  of PROVISIONAL; found by the 2026-08-15 fresh-blind audit, P3-1. These
  counts are now checked, not stated: see the ledger-count assertion in
  `paper/check_paper.ps1`); every ACCEPTED_BASE declaration was
  verified present at the base commit by direct source inspection this
  session (see `WORKLOG.md` for the line-reference inventory);
  `check_paper.ps1` enforces bidirectional anchor coverage between
  `rmq.tex` and the ledger.
- Status: CLOSED
- Evidence (appended 2026-09-11, repin to `3849ecbb`): rows `L-PQ-01`
  (`ACCEPTED_BASE` as a kernel status, with a `Process status: CANDIDATE`
  line) and `L-OPEN-07` added, `L-OPEN-06` amended;
  `scripts/ledger_decl_check.lean` lists the 57 fully-qualified names the
  `ACCEPTED_BASE` rows now cite, which `check_paper.ps1` step 5c derives and
  compares; every `:NNN` citation resolves at the new base. The repin also
  repaired a pointer that was wrong at the old base: `L-ARCH-01` and
  `L-PACK-01` cite `producer at :760`, correct at the new base and not at
  `0665b494`, where that line holds a field assignment and the producer is
  at `:752`. The ledger header says line references are at the base commit;
  for these two citations that was false from `DD-20260909-129` until this
  repin.

## EV-03-PRIMARY-SOURCE

- Requirement (frozen): every precedent and related-work statement has a
  source/date/result receipt; every bibliography field is verified or
  omitted; no absence-of-prior-work inference is drawn from a narrow
  search.
- Evidence: `RELATED_WORK_LEDGER.md` (receipts for all 27 bib entries with
  per-entry verification method; explicit field-omission policy; explicit
  search-limitations section forbidding absence inferences);
  `references.bib` header states the same field policy.
- Status: CLOSED
- Evidence (appended 2026-09-11, repin to `3849ecbb`): eight entries were added
  as authority for the machine model of Section 9.2 (`CookReckhow73`,
  `FredmanWillard93`, `BMM97`, `AHNR98`, `HMP01`, `PatrascuThorup14`,
  `MehlhornSanders08`, `AMT99`), each with a receipt in the new
  `RELATED_WORK_LEDGER.md` section on word-RAM instruction-set authority that
  names the text read and the tier of every field. The bibliography now
  holds 35 entries, so "all 27 bib entries" above describes the bibliography
  before this date and is superseded here rather than edited. No new receipt
  supports an absence inference; the added search-limitations item says the
  instruction-level result was not covered by the novelty search.

## EV-04-NOVELTY-RESTRAINT

- Requirement (frozen): the manuscript makes no priority claim; novelty
  wording is conditional on the completed search log; the
  Tanaka/Affeldt/Garrigue/Qi precedent line is affirmatively credited; the
  mechanized counting lower bound is never conflated with the Liu-Yu/Liu
  cell-probe bounds.
- Evidence: `rmq.tex` Sections 1.2, 4 (scope paragraph), and 10
  (mechanized succinct data structures paragraph); ledger rows L-OPEN-05
  and the priority-posture receipt in `RELATED_WORK_LEDGER.md`;
  `check_paper.ps1` forbidden-token scan rejects unconditional priority
  phrasings.
- Status: CLOSED
- Evidence (appended 2026-09-11): the manuscript makes no novelty statement
  about the fully charged packed query (Section 9.2; Section 10, mechanized
  cost analysis paragraph). `NOVELTY_LOG.md` section 7 records that the
  2026-08-07 search predates it and did not sweep instruction-level cost
  mechanizations, so no "we did not find" wording is licensed for it.

## EV-05-TRUST

- Requirement (frozen): the manuscript states the trust base exactly as
  `docs/TRUST_BASE.md` does -- Lean kernel checking under the pinned
  toolchain (Lean 4.22.0), Mathlib-free dependency policy, standard axioms
  only (`propext`, `Quot.sound`, `Classical.choice`), gate rejection of
  `sorry`/custom axioms/`native_decide`/`ofReduceBool` -- and separates
  validation, harnesses, replays, and process provenance from the trust
  base. Internal process statuses that qualify acceptance (the open
  fresh-blind audit of the `210` release lineage) are disclosed, not
  hidden.
- Evidence: `rmq.tex` Section 7 (all four paragraphs) and Section 11 item
  6 (audit-status candor); Section 6.4 flags the mutation replay as
  reproducible-artifact-tier evidence below kernel theorems, matching the
  evidence-tier discipline of `docs/internal/AUDIT_PROTOCOL.md`.
- Status: CLOSED
- Evidence (appended 2026-09-11): the candidate status of `L-PQ-01` is
  disclosed where the result is stated (Section 9.2, status paragraph) and in
  Section 1.3, Section 11 item 6 and the conclusion. Its axiom inventory is
  printed by `scripts/headline_axiom_check.lean`; its replay runner and typed
  consumer are validation-tier evidence, below the kernel theorem.

## EV-06-REPRODUCIBILITY

- Requirement (frozen): the manuscript names the exact base commit and the
  exact reproduction commands for the theorem surfaces; the paper build is
  deterministic and documented, with the checker and the PDF build command
  recorded; if no TeX engine were present the README must name the missing
  tool and the exact command.
- Evidence: `rmq.tex` Section 8 (commit, artifact script, gate, axiom
  script, checker, `latexmk` command); `README.md` documents the local
  toolchain (TinyTeX pdflatex/latexmk present on this machine), the exact
  build and checker commands, and expected outputs; `check_paper.ps1` runs
  deterministically with exit 0 recorded in `WORKLOG.md`.
- Status: CLOSED
- Evidence (appended 2026-09-11): Section 8 names the new base `3849ecbb` and
  the committed replay of the typed client of Theorem 9.2.

## EV-07-FINAL-RESULT-INSERTION

- Requirement (frozen): the packed all-size result appears in the
  manuscript only as (a) the quoted frozen target statement labeled
  provisional and (b) exactly one literal `ARCHITECTURE_RESULT_PENDING`
  insertion point; no section states, assumes, or paraphrases the pending
  result as established; the row closes only when the independently
  accepted result replaces the marker under a new governed task.
- Evidence (structural half, in place now): `rmq.tex` Section 9 quotes the
  target as a Target Statement tied to ledger row L-ARCH-01
  (PROVISIONAL_ARCHITECTURE); Section 9.1 holds the single marker;
  `check_paper.ps1` fails unless the marker count in `rmq.tex` is exactly
  one; the ledger confines the target to Section 9.
- Evidence (appended 2026-08-07, base repinned to `e3362d4f...`): the
  acceptance condition named in the frozen requirement has been met. Stage A
  was recorded `ACCEPTED` on 2026-08-07 after a fresh-blind exact-commit
  audit and a coordinator reconstruction, and ledger row L-ARCH-01 moved
  `PROVISIONAL_ARCHITECTURE` -> `ACCEPTED_BASE`, declaration
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds`.
  The requirement text is frozen and therefore still reads "labeled
  provisional"; that wording describes the state at the old base and is
  superseded by this entry rather than edited. The containment half of the
  requirement still holds and is still enforced: exactly one marker, and no
  section outside Section 9 states, assumes, or paraphrases the result.
  **Superseded 2026-08-16:** "exactly one marker" is false at this commit --
  there are zero, and the checker permits at most one. This sentence was missed
  by the RC-4 amendment below, whose enumeration named three stale statements
  and not this fourth one. An enumeration of one's own errors is itself a claim
  and can be incomplete.
- Evidence (appended 2026-08-09, after external audit): the frozen requirement
  above says the packed result appears **only** as the quoted target and the
  single marker. **That is false at this commit, and was false when written.**
  The allocated-bits entry of `rmq.tex` Section 3 states the capacity bound; it
  was added by the same commit that retracted the earlier false denial that any
  theorem bounded capacity, so repairing one claim created a containment
  violation with another. The requirement text is frozen and is therefore not
  edited; this entry records that the invariant as literally worded does not
  hold. The manuscript now states the accurate invariant -- the result appears
  in exactly two places, the allocated-bits entry and Section 9, and nowhere
  else -- and the marker count is still exactly one, which the checker enforces.
  **Superseded 2026-08-16 (third occurrence):** the marker count is **zero** and
  the checker permits at most one. The identical sentence 17 lines above was
  annotated in the round-1 amendment; this one, and the round-2 enumeration that
  claimed to list every stale statement, both missed it. Its own annotation reads
  "An enumeration of one's own errors is itself a claim and can be incomplete" --
  which it now demonstrates twice.
- Status (appended 2026-08-07): BLOCKED_ONLY_ON: EDITORIAL_INSERTION. The
  prior status is retained below for lineage. What blocks closure is no
  longer acceptance but the single edit replacing the marker with the
  theorem statement and its proof obligations.
- Evidence (appended 2026-08-16, RC-4): the editorial insertion named by the
  2026-08-07 status entry **has been performed**. `rmq.tex` Section 9 states the
  result as a `theorem` with the constant `427`; the `ARCHITECTURE_RESULT_PENDING`
  marker count in `rmq.tex` is now **zero**, and `check_paper.ps1` was changed to
  permit at most one rather than to require exactly one. Until that change the
  checker demanded the presence of the marker, so it reported success while the
  manuscript presented an accepted theorem as a future insertion, and it would
  have failed the corrected manuscript.

  Consequently three statements in the entries above are false at this commit and
  are superseded rather than edited, per the append-only rule: "Section 9.1 holds
  the single marker"; "`check_paper.ps1` fails unless the marker count in
  `rmq.tex` is exactly one"; and "the marker count is still exactly one, which the
  checker enforces". The containment half of the frozen requirement still holds in
  substance -- the result appears in the allocated-bits entry of Section 3 and in
  Section 9, and nowhere else.

  Recorded plainly because the omission is the point: the RC-4 round performed the
  insertion and did not amend this row, so the substrate's own acceptance record
  went on describing the pre-insertion state. That is the same staleness class as
  the `RC-10` finding that caused the round, inside the record that exists to
  catch it. It was found by audit, not by the round.
- Status (appended 2026-08-16, RC-4): BLOCKED_ONLY_ON: FRESH_BLIND_ACCEPTANCE.
  Nothing editorial remains. What the row now turns on is the pending fresh-blind
  audit of the RC-4 candidate; no earlier status is retracted, they are lineage.
- Status (superseded): BLOCKED_ONLY_ON: ARCHITECTURE_RESULT_PENDING
- Evidence (appended 2026-09-11): containment re-checked after inserting the
  fully charged packed query, against the rule as `rmq.tex` states it: the
  packed result (Theorem 9.1) is stated in Section 9 and, as a capacity
  bound, in the allocated-bits entry of Section 3, and no other section
  states, assumes or paraphrases it. Subsection 9.2 lies inside Section 9.
  The allocated-bits entry gained one sentence, which names the candidate's
  allocation as a repacking of that packed array. Outside those two places
  the passages added at this repin name Theorem 9.1 by label only, with
  neither its constant `427` nor its model nor its content: the
  executed-instructions item of Section 3 (neither the constant of Section
  5.3 nor Theorem 9.1 bounds executed instructions), Section 1.3 (one of the
  places that summarize the candidate is a reading of Theorem 9.1), Section
  11 item 1 (Theorem 9.1 states its own disclaimers in Section 9, and the
  candidate transfers no instruction count to it) and the conclusion (an
  instruction count for the executions the charged-trace bound and Theorem
  9.1 describe is open). Section 1.2 does not name it: it calls the
  candidate's allocation a third one, after the two objects its preceding
  sentence, unchanged from the previous pin, already names. Three phrasings
  in the uncommitted draft of this repin described Theorem 9.1 by its model
  instead: "the charged-trace and cell-probe theorems" in the Section 10 cost
  paragraph, "the charged-trace and cell-probe bounds" in the conclusion, and
  "its own cell-probe disclaimer" in Section 11 item 1. Review found the
  first two before commit; all three were replaced by the wording above
  ("the charged-trace theorems" in Section 10). This entry covers only the
  passages added at this repin; text carried over unchanged from `0665b494`
  was not re-examined. It changes no status.

## 2026-08-09 -- line-number citations audited (corrected: 27 citations, 3 defective)

**This entry supersedes a first version that reported "nine citations, seven
correct". That count was wrong, and the way it was wrong is the point.**

The first sweep matched `:NNN` only on lines that also contained a
`` `....lean` `` path. In this ledger the `File:` line comes *after* the
`Declaration:` line, so every citation written inside a `Declaration:` entry was
invisible to it -- 18 of 27. The second sweep then over-corrected by attributing
each citation to the nearest *preceding* `.lean` mention, which pointed several
citations at the wrong file and reported three of them as "past EOF" defects that
did not exist.

Correct method, third attempt: parse the ledger into rows, collect every `.lean`
file named anywhere in the row, and resolve each citation against all of them.

Result over 27 citations:

- **24 resolve** to the declaration or structure field the row names.
- **3 were wrong**, all now fixed:
  - `L-PACK-01`, producer `:702` -> `:723`. Correct at base `e3362d4` and at the
    audited candidate `f958f54`; displaced by the field-32 docstring added in
    this round.
  - `L-ARCH-01`, producer `:702` -> `:723`. Same cause. **Missed by both earlier
    sweeps** and only found by the third.
  - `L-UB-06`, `concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq`
    `:9349` -> `:8269`. **Already wrong at the pinned base commit**: at
    `e3362d4` that theorem sat at `:8261`, about 1,090 lines from where the
    ledger pointed. Not introduced recently, and not caught by the fresh-blind
    audit.

Two lessons, recorded because they are more useful than the corrections:

1. A pinned base commit does not make a citation right. A reviewer following
   `L-UB-06` at the exact commit the ledger names would have landed in unrelated
   code.
2. **Three sweeps of the same artifact gave three different answers**, and the
   first two were confidently wrong -- one under-matching, one mis-attributing.
   Ad-hoc greps over a structured document are not verification; they are
   sampling with an unknown miss rate. The durable fix is a checker over
   `row -> file -> line -> expected declaration`, which is deferred in
   `docs/internal/RC1_CORRECTION_HANDOFF.md`, or better, citing declaration
   names -- which are stable, greppable, and cannot silently rot -- and keeping
   line numbers only where a checker verifies them.

## 2026-08-16 -- the citation checker exists; three more citations were wrong

The 2026-08-09 entry above ends by saying the durable fix is "a checker over
`row -> file -> line -> expected declaration`", deferred to
`docs/internal/RC1_CORRECTION_HANDOFF.md`. It stayed deferred through two
correction rounds. It is now built: `paper/check_citations.ps1`, run by
`check_paper.ps1` section 5c.

Its first run found **three more defective citations out of 27** -- on a tree
whose citations had already been corrected once and had since passed a
fresh-blind audit:

- `L-ARCH-01` and `L-PACK-01`, `producer at :723` -> `:752` -> `:760`. **This
  pointer has now been wrong four times**: `:702` originally, corrected to
  `:723` on 2026-08-09, drifted 29 lines to `:752`, and drifted 8 more on
  2026-09-09 when a doc comment above it grew while fixing the field-32 arity
  claim (`DD-20260909-128`). Each correction was accurate when made. Nothing
  kept it accurate, and the fourth drift was caused by the very round that was
  repairing an audit -- an edit anywhere above a line-pinned citation moves it.
  `check_paper.ps1`'s citation check is what caught it, both times.
- `L-UB-12`, `queryTraceResultWithStore_eq_of_orderedReadFootprint` `:1324` ->
  `:1298`. Line 1324 holds `queryCostedWithStore_eq_of_orderedReadFootprint` --
  a **different theorem with a near-identical name**. A reviewer following the
  citation lands on something plausible and wrong, which is worse than landing
  on nothing: a dangling pointer announces itself, a plausible one does not.

Three of the six initial failures were checker defects, not ledger defects, and
were fixed before any ledger edit: a citation following a `.lean` path binds to
that file rather than to the nearest identifier; backticked `name : statement`
still names an identifier; and a citation may point at a declaration's
doc-comment line. **Reporting those three as ledger errors would have "corrected"
three correct citations.** Each failure was checked against the source before
being believed.

The checker reports how strongly each citation is pinned -- 19 to a named
declaration, 7 to a named file, 1 row-wide -- because a check is only worth what
it pinned, and a single aggregate would hide that one citation is barely
constrained at all.

Status: this entry records a correction and a new check. It closes no row.

## 2026-09-11 -- repin to `3849ecbb`; the fully charged packed query enters as a candidate

At `3849ecbb`, `import RMQPaper` supplies
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, a kernel-checked theorem
that charges every executed instruction of one fixed program, while
`rmq.tex`, pinned to `0665b494`, called instruction-level charging future
work in three places. That is the `RC-10` mismatch in a new place. This repin
states the theorem in Section 9.2 as a candidate, rescopes those passages to
the charged-trace bound and Theorem 9.1, adds `L-PQ-01` and `L-OPEN-07`,
amends `L-OPEN-06`, and cites primary sources for the machine model, with
division and remainder stated as an explicit assumption.

Status: this entry records a repin and new rows. It closes no row.

## 2026-09-12 UTC: PQ1 acceptance status synchronization (EV-07 evidence only)

The coordinator accepted the repaired source-equivalent PQ1 lineage after both-host full gates, its fresh blind source audit and the narrow tooling correction review. `docs/internal/packed_query/PQ1_COORDINATOR_ACCEPTANCE.md` records the exact identities and all 34 requirements. Editing-rule-5 status passages in rmq.tex, README, THEOREM_LEDGER and NOVELTY_LOG now distinguish that acceptance from the older mathematical pin and from the still-separate release-wide audit.

This update changes process descriptions only: no theorem statement, allocation, instruction budget, operation set, bibliography or priority claim changes. Theorem 9.1 remains confined to its existing mathematical statement and capacity entry; its referenced reading changes only the process adjective attached to the distinct PQ1 theorem. The original 3849ecbb mathematical source pins remain. EV-07 and all frozen evidence-matrix requirements/status rows are preserved; this entry adds evidence and closes no additional paper row.

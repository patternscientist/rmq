# Evidence Matrix (frozen)

Frozen acceptance rows for the manuscript/evidence substrate on branch
`codex/eg-cp-paper-evidence-r1`, base commit
`688c54a39d9a2410d281f1ded9b70937908beb4a`. Row IDs and requirement text
are frozen as of 2026-08-05; evidence and status fields are append-only.
Statuses: **CLOSED** (evidence in place at this commit) or
**BLOCKED_ONLY_ON: ARCHITECTURE_RESULT_PENDING** (nothing remains except
the independently accepted packed all-size result). No other status is
permitted for this substrate; a row that could not reach one of these two
states would mean the substrate is incomplete.

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
  `docs/PAPER_MODEL_ADEQUACY.md`; Section 3 and Section 11 item 2 disclaim
  conventional word-RAM running time (ledger L-OPEN-06); Section 11 item 3
  states preprocessing open (L-OPEN-01); Section 8 keeps measurements in
  separate columns from theorems. `check_paper.ps1` forbids the phrase
  pattern the roadmap bans for cell-probe/charged-trace claims.
- Status: CLOSED

## EV-02-THEOREM-IDENTITY

- Requirement (frozen): every non-provisional mathematical claim sentence
  in the manuscript maps through a ledger anchor to an exact Lean
  declaration and file at the base commit, with proposition-level
  hypotheses and conclusion recorded; the provisional target maps to a
  PROVISIONAL_ARCHITECTURE row; unproved statements map to OPEN rows.
- Evidence: `THEOREM_LEDGER.md` (34 rows: 27 ACCEPTED_BASE, 1
  PROVISIONAL_ARCHITECTURE, 6 OPEN); every ACCEPTED_BASE declaration was
  verified present at the base commit by direct source inspection this
  session (see `WORKLOG.md` for the line-reference inventory);
  `check_paper.ps1` enforces bidirectional anchor coverage between
  `rmq.tex` and the ledger.
- Status: CLOSED

## EV-03-PRIMARY-SOURCE

- Requirement (frozen): every precedent and related-work statement has a
  source/date/result receipt; every bibliography field is verified or
  omitted; no absence-of-prior-work inference is drawn from a narrow
  search.
- Evidence: `RELATED_WORK_LEDGER.md` (receipts for all 23 bib entries with
  per-entry verification method; explicit field-omission policy; explicit
  search-limitations section forbidding absence inferences);
  `references.bib` header states the same field policy.
- Status: CLOSED

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
  7 (audit-status candor); Section 6.4 flags the mutation replay as
  reproducible-artifact-tier evidence below kernel theorems, matching the
  evidence-tier discipline of `docs/internal/AUDIT_PROTOCOL.md`.
- Status: CLOSED

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
- Status (appended 2026-08-07): BLOCKED_ONLY_ON: EDITORIAL_INSERTION. The
  prior status is retained below for lineage. What blocks closure is no
  longer acceptance but the single edit replacing the marker with the
  theorem statement and its proof obligations.
- Status (superseded): BLOCKED_ONLY_ON: ARCHITECTURE_RESULT_PENDING

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

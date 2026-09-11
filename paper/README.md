# paper/ -- RMQ manuscript and evidence substrate

Private working draft of the RMQ manuscript, pinned to repository base
commit `3849ecbb53bbedfcd679352cc68d095fa5a304c2`, authored on branch
`codex/eg-cp-paper-evidence-r1` under governance
`f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`. This directory is a manuscript
substrate only: it records no architecture acceptance, no coordinator
acceptance, and no roadmap closure, and it is not one of the repository's
registered current-fact surfaces. **The claim-drift scan does read `paper/` as
of 2026-08-16** (WDD-20260816-048); what still excludes this substrate is the
narrower `currentFactSurfacePathRegex`, which governs required attribution.
This paragraph said `paper/` was outside the scan entirely, and was made false
by the commit that added the scan root without updating it.

### What the base pin asserts, and what verified it

The pin was moved from `e3362d4f...` to `688c54a3...` on 2026-08-09. Two roles
depend on it and they are not the same claim:

- **This substrate statement** -- "the manuscript describes that tree".
- **The `ACCEPTED_BASE` rows** in `THEOREM_LEDGER.md` (29 at the repins of
  2026-08-09 and 2026-08-16, 30 since the repin of 2026-09-11;
  `check_paper.ps1` derives the current count). That status is defined
  in the ledger header as *kernel-checked declaration present on the base
  commit*, so those rows move with the pin and each restates a claim about the
  new tree.

Because moving them restates a claim, they were not restamped on faith. At
`688c54a3`: `lake build RMQ` exit 0; `scripts/axiom_check.lean` exit 0 with no
`sorryAx` and no `ofReduceBool`; `scripts/ledger_decl_check.lean` confirms the
fully-qualified declaration names those rows cite are present in the
environment -- **54** of them from 2026-08-16, and **57** since the repin of
2026-09-11, checked at that pin as recorded below. Those rows also refer to further declarations in elided
(`...ReviewerSuccessfulReadWordFits`), short and type-annotated forms, which
that script cannot resolve as written and does not check; `paper/check_paper.ps1`
step 5c reports how many, and fails if the checked set and the cited set differ.
The figure was **53** and the word was "all" until 2026-08-16, when deriving the
set from the ledger showed one cited name checked by nothing. Both CI
workflows are green on `688c54a3`.

**Corrected 2026-08-16.** This paragraph also claimed that all **27** `:NNN`
citations resolved at `688c54a3`, "after three were corrected". That was false
when written. `L-UB-12` cited `:1324`, which at `688c54a3` held
`queryCostedWithStore_eq_of_orderedReadFootprint` while the row names
`queryTraceResultWithStore_eq_of_orderedReadFootprint` at `:1298`
(`git show 688c54a3:RMQ/Core/SuccinctRMQClassic.lean | sed -n '1324p'`).
`SuccinctRMQClassic.lean` is byte-identical between `688c54a3` and the current
pin, so the defect was present at both.

The claim was a hand count, and a hand count is what it was worth: the same
three-sweeps-three-answers problem recorded in `EVIDENCE_MATRIX.md`. The
citation set is now machine-checked by `check_citations.ps1`, which found this
one. Note the shape of the mistake -- the RC-4 round corrected the *pointer* and
left the *sentence asserting the pointers were fine* untouched. Fixing a claim
at its origin is not the same as fixing the claim.

The commit carrying that repin added only substrate edits and
`scripts/ledger_decl_check.lean`; it changed no Lean library code, so the pinned
tree and the substrate commit differed by documentation and one checker.

### Repin of 2026-08-16 (RC-4)

The pin moved again, from `688c54a3...` to `0665b494...`, as part of the RC-4
correction round. The 2026-08-15 fresh-blind audit failed `RC-10` because this
substrate was pinned to an ancestor of the release tag *and* still presented the
already-accepted packed architecture as a provisional target: at the release
commit, `import RMQPaper` supplied the 427-probe capstone while this manuscript
called it a future editorial insertion. The paper and the artifact did not
identify the same claim.

Both halves are repaired in one change. The theorem is absorbed --
Section 9 states it as a theorem with the actual constant `427` and the
`ARCHITECTURE_RESULT_PENDING` marker is gone -- and all 38 full-SHA pins across
this substrate move together. Mentions of `688c54a3` that survive below are
deliberate: they record what was true at the previous pin.

Verified at the new pin before the move: `lake build RMQ` and
`lake build RMQPaper` exit 0; `scripts/independence_check.lean` passes on all
**three** cap-supplying theorems (1,855 / 1,856 / 2,074 constants, none touching
the eight charged declarations); `paper/check_paper.ps1 -SelfTest` passes,
including two new assertions -- the ledger status counts are now *derived* from
`THEOREM_LEDGER.md` rather than restated here, and the pending marker is
permitted rather than required.

The same standing caveat applies: the commit carrying this repin is the child of
the verified tree, differing by the substrate edits themselves.

### Repin of 2026-09-11 (fully charged packed query)

The pin moved from `0665b494...` to `3849ecbb...`, on branch
`codex/fully-charged-packed-query-v1` under governance
`4639223bc8130b0ef752270b5cbdd74325abcd60` (`audit-v1-rc-6`). At the new base
`import RMQPaper` supplies `RMQ.Headlines.succinctRMQFullyChargedPackedQuery`,
a theorem that charges every executed instruction of one fixed program, while
the manuscript pinned at `0665b494` called instruction-level charging future
work in Section 3, Section 11 item 1 and the conclusion. That is the `RC-10`
class described above, arriving a second time.

The theorem is stated in Section 9.2 as a **candidate**: it is kernel-checked
at the new base, but the project's acceptance process -- a full replay, the
aggregate gate and a fresh blind exact-commit audit -- has not accepted it.
The passages that called instruction-level charging future work now speak
only of the charged-trace bound and Theorem 9.1, which are unchanged. In the
ledger, `L-PQ-01` records the theorem with `ACCEPTED_BASE` as its kernel
status and `CANDIDATE` as its process status, `L-OPEN-07` records that the
budget's optimality and attainment are unproved, and `L-OPEN-06` is amended
because `L-PQ-01` falsifies its first clause. The theorem sits in subsection
9.2 so that Sections 10 to 12 keep the numbers the ledger and the evidence
matrix cite. Section 9.2 also cites primary sources for the machine model and
states integer division and remainder as an explicit assumption beyond the
multiplication model of the cited research papers; the eight new
bibliography entries have receipts in `RELATED_WORK_LEDGER.md`.

All 38 full-SHA pins move together, and the `Commit:` line of `L-PQ-01` adds
a 39th. Mentions of `0665b494` that survive are deliberate records of the
previous pin.

Checked for this move, on a tree whose Lean library files are byte-identical
to `3849ecbb`: `lake build` and `lake build RMQPaper` exit 0 (up to date);
`lake env lean scripts/axiom_check.lean` exit 0 (1,163 axiom records, 30 of
them axiom-free); `scripts/headline_axiom_check.lean` exit 0 (114 records;
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery` depends on `propext`,
`Classical.choice` and `Quot.sound`); `scripts/wordram_axiom_check.lean` exit
0 (348 records); no record in the three inventories names any axiom other
than `propext`, `Classical.choice` and `Quot.sound`;
`scripts/independence_check.lean` passes (three cap-supplying theorems
checked against the eight charged declarations);
`scripts/ledger_decl_check.lean` passes with 57 names present and the
negative control absent. On the substrate itself:
`paper/check_paper.ps1 -SelfTest` passes (36 anchors and rows, 30/0/6, 57
declaration names equal to the decl-check list, 35 bibliography entries all
cited, 27 `:NNN` citations resolving); `scripts/claim_drift_scan.ps1 -Strict`
reports no strict failure.

The move also makes one pair of citations true at the base again.
`L-ARCH-01` and `L-PACK-01` cite `producer at :760`. Since `DD-20260909-129`
that was right at the working tree and wrong at `0665b494`, where the producer
sits at `:752` and `:760` holds a field assignment, although the ledger header
says its line references are at the base commit. The new base contains the
field-32 change, so the pointer and the base agree.

The standing caveat applies: the commit carrying this repin is a descendant of
the verified tree and differs from it only by the substrate edits,
`scripts/ledger_decl_check.lean` and the two design ledgers; no Lean library
file differs between them.

Historical mentions of `e3362d4` elsewhere in this directory are deliberate and
were not rewritten: they record what was true at the previous pin.

The same applies to `1490c97b…` in the header of `WORKLOG.md`, which is the base
of the session that log describes. It is the only full-SHA base in `paper/` that
a repin does not move, and it is annotated in place as historical so it is not
mistaken for a straggler.

## Contents

- `rmq.tex` -- the manuscript. Every mathematical claim carries an
  invisible `\ledger{ID}` anchor. The packed all-size architecture result is
  stated as a theorem in Section 9 (RC-4, 2026-08-16); it was previously a
  quoted provisional target plus one `ARCHITECTURE_RESULT_PENDING` marker,
  and there are now zero such markers. The fully charged packed query is
  stated in Section 9.2 as a candidate theorem (2026-09-11); see editing
  rule 5.
- `references.bib` -- primary-source bibliography. Unverified fields are
  omitted, never guessed; see the field policy in
  `RELATED_WORK_LEDGER.md`.
- `THEOREM_LEDGER.md` -- maps every manuscript claim to
  ACCEPTED_BASE / PROVISIONAL_ARCHITECTURE / OPEN, with exact commit,
  Lean declaration and file when formalized, and proposition-level
  hypotheses/conclusion.
- `RELATED_WORK_LEDGER.md` -- source/date/result receipts for all
  precedent statements, per-entry verification method, and explicit
  search limitations.
- `EVIDENCE_MATRIX.md` -- frozen acceptance rows for this substrate. Every
  row is CLOSED except `EV-07`, whose remaining blocker was the editorial
  insertion of the accepted architecture result. That insertion was performed
  on 2026-08-16; see the `EV-07` status entry of that date for what the row now
  turns on.
- `check_paper.ps1` -- deterministic checker (see below).
- `WORKLOG.md` -- session log, including the preflight record and the
  declaration-verification inventory.

## Building the PDF

The build was exercised on this machine with TinyTeX
(`pdflatex` and `latexmk` on `PATH`). From this directory:

```bash
latexmk -pdf rmq.tex
```

This runs `pdflatex` and `bibtex` to fixpoint and produces `rmq.pdf`.
Build artifacts (`*.aux`, `*.bbl`, `*.log`, `rmq.pdf`, ...) are
git-ignored; the PDF is a derived artifact, reproducible from the two
committed sources `rmq.tex` and `references.bib`.

If no TeX engine is installed, the missing tools are `pdflatex` and
`latexmk` (any TeX Live/TinyTeX/MiKTeX distribution provides both), and
the exact reproducible command remains `latexmk -pdf rmq.tex` run in this
directory.

## Checking the manuscript

```powershell
powershell -ExecutionPolicy Bypass -File check_paper.ps1
```

Deterministic; exit 0 iff all checks pass. It verifies: citation closure
in both directions (every `\cite` resolves, every bib entry is cited);
duplicate `\label`/bib keys and unresolved `\ref` targets; forbidden
tokens and overclaim phrasings across all substrate files; bidirectional
coverage between the manuscript's `\ledger` anchors and the theorem-ledger
rows, with only the three legal statuses; that the status breakdown
published in `EVIDENCE_MATRIX.md` matches the one derived from
`THEOREM_LEDGER.md`; that every `:NNN` source citation in the ledger
resolves to the declaration its row names (`check_citations.ps1`); and that
`rmq.tex` contains **at most one** `ARCHITECTURE_RESULT_PENDING` marker.

That last check used to demand *exactly* one. It therefore reported success
while the manuscript presented an already-accepted theorem as a future
insertion, and would have failed the corrected manuscript -- a gate
enforcing the presence of the defect it was meant to catch. Zero is the
healthy state.

`check_paper.ps1 -SelfTest` additionally verifies that each detector fires
on a planted defect, rather than passing because nothing triggered it.

The checker is textual and needs no Lean, Lake, or TeX toolchain. Theorem
truth is not established here: it rests on Lean kernel checking at the
pinned base commit, reproduced by the repository commands quoted in
Section 8 of the manuscript (for example
`lake env lean scripts/headline_axiom_check.lean` from the repository
root). Do not run repository-level Lean/Lake builds from this directory
while another build task owns the tree.

## Editing rules

1. Adding or changing a mathematical claim in `rmq.tex` requires adding or
   updating its `\ledger` row in `THEOREM_LEDGER.md` in the same change;
   the checker fails otherwise.
2. Adding a citation requires a receipt in `RELATED_WORK_LEDGER.md`.
3. The packed architecture result is **inserted** (RC-4, 2026-08-16). Section 9
   states it as a theorem with the constant `427`; there is no
   `ARCHITECTURE_RESULT_PENDING` marker left to replace, and the checker now
   permits at most one rather than requiring exactly one. Changing that
   statement is an ordinary claim change and falls under rule 1.

   This rule previously read "may be inserted only by replacing the single
   marker in Section 9.1 … what remains is the editorial insertion". That
   described the state before the insertion and survived the commit that
   performed it -- the third such passage in this file, after the Contents
   bullet and the checker paragraph, and the same staleness class as the
   `RC-10` finding the RC-4 round exists to answer.
4. Evidence-matrix requirement text is frozen; evidence/status fields are
   append-only.
5. The fully charged packed query (`L-PQ-01`) is a **candidate**. Its status
   is stated in these places, which must change together when the project
   accepts or rejects it. In `rmq.tex`: the header comment, the abstract,
   Section 1.1 (lead-in and item 6), Sections 1.2 and 1.3, Section 3 (the
   allocated-bits and executed-instructions items and the model paragraph),
   the second reading of Theorem 9.1, Section 9.2 (theorem title and status
   paragraph), the Section 10 cost paragraph, Section 11 items 1, 3 and 6,
   and Section 12. `grep -n -i candidate rmq.tex` finds every one of them, plus
   two unrelated uses ("candidate merging" in the charge policy and the
   "candidate lineage" behind Theorem 9.1's acceptance). In
   `THEOREM_LEDGER.md`: the header sentence on `L-PQ-01` and that row's
   `Process status` line. In `NOVELTY_LOG.md`: sections 0.3 and 7. In this
   file: the Contents bullet for `rmq.tex` and this rule. The dated
   `EVIDENCE_MATRIX.md` entries are append-only and get a new entry instead.

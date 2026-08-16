# paper/ -- RMQ manuscript and evidence substrate

Private working draft of the RMQ manuscript, pinned to repository base
commit `0665b494707695a70675fef0e5c8682f4d80fe0c`, authored on branch
`codex/eg-cp-paper-evidence-r1` under governance
`f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`. This directory is a manuscript
substrate only: it records no architecture acceptance, no coordinator
acceptance, and no roadmap closure, and it is not one of the repository's
registered public claim surfaces (the claim-drift policy scans `README.md`,
`artifact/`, and `docs/`; `paper/` is deliberately outside that registry
until a release-synchronization task admits it).

### What the base pin asserts, and what verified it

The pin was moved from `e3362d4f...` to `688c54a3...` on 2026-08-09. Two roles
depend on it and they are not the same claim:

- **This substrate statement** -- "the manuscript describes that tree".
- **The 29 `ACCEPTED_BASE` rows** in `THEOREM_LEDGER.md`. That status is defined
  in the ledger header as *kernel-checked declaration present on the base
  commit*, so those rows move with the pin and each restates a claim about the
  new tree.

Because moving them restates a claim, they were not restamped on faith. At
`688c54a3`: `lake build RMQ` exit 0; `scripts/axiom_check.lean` exit 0 with no
`sorryAx` and no `ofReduceBool`; `scripts/ledger_decl_check.lean` confirms all
**53** declaration names those rows cite are present in the environment; and all
**27** `:NNN` source citations resolve to the declaration or structure field
their row names, after three were corrected (see `EVIDENCE_MATRIX.md`). Both CI
workflows are green on `688c54a3`.

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

Historical mentions of `e3362d4` elsewhere in this directory are deliberate and
were not rewritten: they record what was true at the previous pin.

## Contents

- `rmq.tex` -- the manuscript. Every mathematical claim carries an
  invisible `\ledger{ID}` anchor. The packed all-size architecture result is
  stated as a theorem in Section 9 (RC-4, 2026-08-16); it was previously a
  quoted provisional target plus one `ARCHITECTURE_RESULT_PENDING` marker,
  and there are now zero such markers.
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
- `EVIDENCE_MATRIX.md` -- frozen acceptance rows for this substrate; every
  row is CLOSED except the final-result row, which is blocked only on the
  independently accepted architecture result.
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
3. The packed architecture result may be inserted only by replacing the
   single marker in Section 9.1, under a new governed task; the independent
   acceptance condition has been met (Stage A `ACCEPTED`, 2026-08-07), so
   what remains is the editorial insertion, after which `EVIDENCE_MATRIX.md`
   row EV-07 closes.
4. Evidence-matrix requirement text is frozen; evidence/status fields are
   append-only.

# paper/ -- RMQ manuscript and evidence substrate

Private working draft of the RMQ manuscript, pinned to repository base
commit `e3362d4f0300b3b0aef22d104ed67844d80134a0`, authored on branch
`codex/eg-cp-paper-evidence-r1` under governance
`f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`. This directory is a manuscript
substrate only: it records no architecture acceptance, no coordinator
acceptance, and no roadmap closure, and it is not one of the repository's
registered public claim surfaces (the claim-drift policy scans `README.md`,
`artifact/`, and `docs/`; `paper/` is deliberately outside that registry
until a release-synchronization task admits it).

## Contents

- `rmq.tex` -- the manuscript. Every mathematical claim carries an
  invisible `\ledger{ID}` anchor; the packed all-size architecture result
  appears only as a quoted provisional target plus exactly one literal
  `ARCHITECTURE_RESULT_PENDING` insertion point (Section 9.1).
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
rows, with only the three legal statuses; and that `rmq.tex` contains
exactly one `ARCHITECTURE_RESULT_PENDING` marker.

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

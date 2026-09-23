# Retrospective certifications

Eight commits in this repository's history changed governed paths without the
design-log entry the per-commit check requires. They predate that check: it was
introduced by `DD-20260816-121`, and until then a branch was certified in
aggregate, which accepts a range as long as *some* commit in it carries a
ledger update. `WDD-20260816-043` records the blind spot; `WDD-20260817-075`
records that nobody had pointed the new check backwards at existing history.

Their entries could not be added where they belong, because a commit's content
is fixed. Rewriting them would rewrite every descendant SHA, discarding the
`audit-v1-rc-4` tag, the GATE PASS it rests on, and the per-commit certification
of the ninety-six commits that pass. This file is the alternative: **the decision
each commit failed to record, written now, tied to the exact commit and the exact
paths.**

## What this file is not

It is not an exemption. `scripts/design_decision_check.ps1` consults the table
below only when `-Head` names one of these exact commits, and only accepts when
the paths it computes as missing are **exactly** the paths recorded here. A
listed commit whose missing set differs is still rejected. An unlisted commit is
still rejected. `scripts/design_decision_check_regression.ps1` pins the table's
contents to these eight SHAs and re-derives each path set from the production
checker, so an entry cannot be added, widened, or falsified without the
regression failing.

A date-based or path-based exemption was rejected. It would let the check report
green over history it does not certify, which is the defect class this candidate
exists to eliminate — committed inside the mechanism built to detect it.

## The record

Each entry gives the decision that should have accompanied the commit.

### `bb15006b4744` — Land the paper substrate worklog, bibliography, manuscript draft, and theorem ledger

Missing: `code: paper/references.bib`, `code: paper/rmq.tex`

**Decision.** The manuscript is written as a LaTeX source tree under `paper/`
rather than generated from the Lean sources, and its bibliography is maintained
by hand in BibTeX. The alternative considered was generating prose from the
theorem ledger; it was rejected because the paper must state claims in the
qualified form a referee expects, which no generator produces. The consequence
accepted is that `paper/rmq.tex` becomes a claim surface requiring its own
checker — landed later as `paper/check_paper.ps1`.

### `ebdaf222d05a` — Land the related-work ledger, evidence matrix, README, checker, and green check results

Missing: `code: paper/README.md`, `code: paper/rmq.tex`,
`workflow: paper/check_paper.ps1`

**Decision.** Claims in the manuscript are governed by a checker that lives
beside the manuscript rather than in `scripts/`, so the paper directory is
self-contained and can be handed to a co-author or referee whole. The evidence
matrix and related-work ledger are the paper's own records, not repository
governance, and so are maintained under `paper/`.

### `29c688bd88bc` — Repin the paper substrate to current main and retract the false capacity claims

Missing: `code: paper/README.md`, `code: paper/rmq.tex`

**Decision.** Two capacity claims in the manuscript were not supported by the
Lean development and were retracted rather than weakened, on the standing rule
that a claim is fixed at its origin. The paper's base pin moves to current
`main` so every citation resolves against a tree that exists.

### `4c56e7ed09da` — Harden the manuscript checker and close the remaining stale pending language

Missing: `code: paper/README.md`, `code: paper/rmq.tex`,
`workflow: paper/check_paper.ps1`

**Decision.** `check_paper.ps1` gains rejection tests rather than presence
tests: a checker that only confirms expected text is present cannot see text
that should have been removed. Stale "pending" language is closed in the
manuscript at the same time, so the checker and its subject agree.

### `aa3d585887e5` — Land the novelty log and give the checker a claim-surface / record-surface split

Missing: `code: paper/NOVELTY_LOG.md`, `workflow: paper/check_paper.ps1`

**Decision.** Novelty statements are separated from evidence records, because
the two need opposite treatment: a claim surface must be scanned for
overstatement, a record surface must be preserved verbatim. `check_paper.ps1`
is split along that line. See also `rmq-prior-art-affeldt-group`: the novelty
framing this log carried was later retired.

### `7655ee8f2bad` — Export the packed cell-probe result from RMQPaper

Missing: `workflow: scripts/headline_axiom_check.lean`

**Decision.** The headline axiom check gains the packed cell-probe result as an
exported surface so the paper can cite one name that the axiom checker also
pins. `scripts/*.lean` is both proof-code and automation; the decision was
recorded in `DESIGN_DECISIONS.md` and the workflow half was not written.

### `3652d4b5bf5b` — Make the two-210 independence claim a checked property

Missing: `code: scripts/independence_check.lean`

**Decision.** The claim that the two occurrences of `210` are independent is
made a machine-checked property rather than a prose assertion, because an
auditor asked for it (item 7) and prose cannot fail. The entry was written into
`WORKFLOW_DESIGN_DECISIONS.md`; `scripts/independence_check.lean` is
code-classified and required the code ledger as well.

### `32659871aa55` — Export the fixture probe count and clarify capstone field 32

Missing: `workflow: scripts/axiom_check.lean`

**Decision.** The fixture probe count becomes an exported constant so the gate
can assert it rather than restate it, and capstone field 32's comment is
corrected to describe what the field holds. As with `7655ee8f2bad`, the code
half was recorded and the workflow half was not.

## Machine-readable table

Format: `<40-hex sha> | <sorted, semicolon-separated missing paths>`. The
checker requires an exact match on both columns.

```retrospective-certifications
bb15006b47449031af9eb432c5b8bb1ec30b41b3 | code: paper/references.bib;code: paper/rmq.tex
ebdaf222d05a2e243fb15ad19a91ad62fd10f9ff | code: paper/README.md;code: paper/rmq.tex;workflow: paper/check_paper.ps1
29c688bd88bc413ff3d960222e6d0a7db34b51f5 | code: paper/README.md;code: paper/rmq.tex
4c56e7ed09da4c96d550d831c9e9599275d019f6 | code: paper/README.md;code: paper/rmq.tex;workflow: paper/check_paper.ps1
aa3d585887e5e475a1f5cd94a4ff4a8fef45c93e | code: paper/NOVELTY_LOG.md;workflow: paper/check_paper.ps1
7655ee8f2bad1cdd705061463453e5300acd1203 | workflow: scripts/headline_axiom_check.lean
3652d4b5bf5bb8a08efe1c6e6c0076de787f03a0 | code: scripts/independence_check.lean
32659871aa55336a5155a00bf60b9a618c24b43f | workflow: scripts/axiom_check.lean
```

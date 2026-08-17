# Commissioning prompt — outside audit of the RMQ program plan

> Hand the auditor **this prompt and the tag only** — never the coordinator
> record, never a worker verdict, never this repository's chat transcripts.
>
> **This file does not state its own commit SHA, deliberately.** Writing the SHA
> in changes it -- a file cannot name the commit that contains it. Derive it with
> `git rev-list -n1 audit-plan-v14` and record that in your report.

---

**Tag: `audit-plan-v14`** — in `github.com/patternscientist/rmq`.
Audit this commit and no other. Every `audit-plan-v14` below means this commit.

```
git fetch --tags
git checkout audit-plan-v14          # detached HEAD is expected and correct
git rev-list -n1 audit-plan-v14      # the SHA under audit; record it in your report
```

## What you are auditing

Two documents, both at `audit-plan-v14`:

- `docs/internal/RMQ_PROGRAM_PLAN.md` — the program plan
- `docs/internal/PLAN_LINEAGE.md` — its companion defect-species record

Everything else in the repository is **evidence you may check against**, not a
target. In particular these are the artifacts the plan rests on, all at the same
commit:

- `docs/internal/wf3_attack.json` — the fake-attack catalogue and required repairs
- `docs/internal/PLAN_AUDIT_DISPOSITION.md` — the 2026-08-13 plan audit, 14 accepted findings
- `docs/internal/RC3_DISPOSITION.md` — the RC-3 candidate audit dispositions
- `docs/internal/RMQ_PROGRAM_PLAN_2026-08-13.md` — the audited predecessor

## What "a defect" means here

Any statement in either document that is **false**, **unverifiable as stated**, or
**contradicted elsewhere in the same document**. Rank:

- **P1** — false, and would mislead someone making a decision from it.
- **P2** — unverifiable as stated, overstated, or self-contradicted.
- **P3** — imprecision that survives correction.

## What to check

1. **Every number.** Counts, ratios, "N of M", line counts. Recompute each from
   the artifact it describes.
2. **Every `file:line` and every SHA.** Does the cited line say what the sentence
   needs? Is the SHA the object the sentence claims — introducing commit,
   ancestor, tip, or pin?
3. **Commit-relative consistency.** The plan declares one verification pin in its
   header. Every claim depending on repository state must hold **at that pin**.
   Flag any that holds only at some other commit.
4. **Every universal and every enumeration** — "every", "all", "no", "only",
   "the four", "both", "twice". Assemble the actual set and count it.
5. **Every quotation.** Verbatim? And does the surrounding claim survive reading
   one clause *past* the quoted span?
6. **Internal cross-references.** For every "§X …", open §X and confirm it
   contains the referenced item.
7. **Rules stated and then broken.** The plan's Method section states a rule about
   adding new claims regarding past revisions, with an exception and an explicit
   accounting of where the exception is used. Check that accounting.
8. **Structural honesty.** Any property claimed — coverage, completeness, closure
   — that the contents do not establish.

## Method rules that bind you

- **Measure before you report.** Show the command and its output for every
  quantitative claim you make.
- **Check the referent, not just the citation.** A citation that exists and reads
  as a report describes can still be wrong about the thing it describes. A prior
  round reported a claim about revision `v3` as contradicted, citing a sentence in
  `v4`; the citation was real and `v4` was simply wrong about `v3`.
- **Do not report anything you have not personally reproduced.**
- If a severity level is empty, say so. A clean verdict is a real possible
  outcome; manufacturing findings is itself a defect.

## Declared open — do not report these unless the RECORD of them is wrong

These are known and stated in the documents. Report them only if what the
documents *say* about them is inaccurate.

- Revisions `v2`–`v13` of the plan exist on **no ref**. Only the revision at this
  tag is committed. Claims about what an earlier revision said are therefore
  uncheckable against any committed artifact, and the documents say so.
- `docs/internal/audit_reports/2026-08-15_V1_RC_fresh_blind.md` and the RC-1 /
  RC-2 audit material exist on no ref.
- The agent audits **of this plan** have no committed record, and the documents
  make no claim about their number or severity.
- Two items in the plan's §H are genuinely undone at this pin: rerunning the
  aggregate from a clean exact checkout, and `scripts/paper_root_measure.ps1`,
  which does not exist.

## Output

- **VERDICT**: `CLEAN` (no P1 and no P2) or `NOT_CLEAN`.
- For each finding: an ID, the exact quoted text with `file:line`, what is wrong,
  the evidence (command and output), and the minimal correct replacement.
- **"What I checked and found correct"** — the specific claims you verified as
  true. This matters as much as the findings: it is the record of what has been
  established.
- **"What I could not check"** — and why.

Report the SHA you audited. Do not seek any other input about this work; this
prompt and the tag are your only inputs.

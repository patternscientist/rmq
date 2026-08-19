# Disposition — outside audit of program plan v14

**Audited:** `audit-plan-v14` = `047c7cfcb1565674b15283f00a782a5ea10776a1`.
**Verdict returned:** `NOT_CLEAN` — 2 P1, 5 P2, 3 P3.
**Coordinator disposition: all ten ACCEPTED.** Each was independently
reproduced before acceptance; none was rejected on measurement. That is a first
for this project — across twelve internal candidate rounds, roughly a quarter of
findings were wrong about their own referent.

## The two P1s

**`AUD-01` — the catalogue placed at the pin.** `wf3_attack.json` does not exist
at `17360d1`; it and the two dispositions were introduced by `8dcd341`.
Reproduced with `git cat-file -e`. The plan's own header forbids exactly this:
"Claims about artifacts committed *with* this revision say so explicitly and are
true of that later commit, not of the pin -- the distinction exists because a
previous revision collapsed the two." **The rule was stated and then broken in
the same document**, three times. `AUD-02` and `AUD-03` are the same defect at
two other sites, so they are one repair, not three.

**`AUD-04` — a live candidate defect, not a plan defect.** The plan marked RC-3
`P2-2` landed. Its accepted disposition required three exact false-success
classes to become persistent self-tests; two never did. Reproduced at `27c5641`,
the tagged and pushed candidate:

    claim_drift MUTATED exit=0   scan complete (1206 hits, 0 strict failures)
    check_paper MUTATED exit=0   CHECK-PAPER: RESULT: PASS

and no `.ps1` in the repository contained either probe string. Closed by
`WDD-20260818-081`; the tag moved to a tree where both are rejected.

## The lesson worth keeping

**An accepted disposition is not an implemented one.** Twelve internal rounds
read this row and none checked it, because the row cites two landing SHAs and
both are real — they simply repair a third class. The cheap test nobody ran is
to grep for the probe string the disposition names. Where a disposition says
"these exact classes become persistent self-tests", the string is the artifact.

## Repairs

All nine plan-text findings are corrected in **v15**. `AUD-01`/`02`/`03` take the
header's own form. `AUD-05` moves the accepted CFP rule into §G, the section the
coverage table maps it to. `AUD-06` names the file that exists. `AUD-07` cites
`Shape.lean:654-677,892-901` plus the analysis, since `:675-677` alone is the
wrapper. `AUD-08` reads 54, the checker's declared count. `AUD-09` calls the
companion what it is. `AUD-10` narrows the cross-reference to what §E says.

`audit-plan-v14` is **not** moved: it is the artifact this audit was performed
against, and moving it would destroy the auditor's referent.

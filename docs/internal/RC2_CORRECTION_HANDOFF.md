# RC-2 correction round -- resume card

**Branch:** `codex/rc2-corrections`, on top of `0d7375f` (the RC-1 round's tip).
**Audited candidate:** `audit-v1-rc-2` = `a03fcc4`, verdict `NOT_ACCEPTABLE`
(`docs/internal/audit_reports/2026-08-12_V1_RC_fresh_blind.md`).
Full narrative: the 2026-08-12/13 entry in `docs/internal/AUDIT_AND_A_DESIGN.md`.

## Status

All seven findings corrected. Every finding was independently reproduced first
and **none were wrong**; eight spot-checked auditor citations all resolved.

| finding | disposition |
| --- | --- |
| `P1-01` exact/tight `210` on three surfaces | fixed; **was our own incomplete fix** from `DD-20260809-099` |
| `P1-02` preprocessing implicature | fixed on `README.md` and `PUBLICATION_STRATEGY.md` |
| `P1-03` Windows deadline control | real descendant barrier; both controls now pass twice consecutively |
| `P1-04` unapplied novelty-log repairs | applied, plus 4 load-bearing bib entries |
| `P2-01` forbidden set guarded the sentence | expanded 2 -> 8 declarations |
| `P2-02` field 27 intensional overclaim | scoped to what the field proves |
| `P3-01` field 15 "both decoded header fields" | corrected; header stores one |

Prevention added: a claim-drift term for exact/tight formulations of `210`/`427`,
injection-verified against the **audited** wording; `windows-2022` and
`ubuntu-24.04` CI jobs running the ownership self-tests without a Lean build;
and `Invoke-RMQOwnedProcessCollectionSelfTest` pinning the empty-collection edge
cases that broke this round twice.

## What is still open

1. **Full aggregate gate to completion** -- the auditor's item 3. Both deadline
   controls pass, but no end-to-end `GATE PASS` has been captured on the final
   tree. Runs so far died to my own wrapper timeouts and a session teardown, not
   to gate failures. **It takes >90 min on Windows**; budget 3-4 hours and run it
   on the exact tree you intend to tag, because edits after the run invalidate it.
2. `audit-v1-rc-3` (**never a `v*` tag** -- that fires `release-artifact.yml`),
   packet, and a fresh blind audit from a different model family.
3. **Owner decision, unchanged:** the separate minimal paper root. The RC-1
   promotion grew `RMQPaper`'s closure `139,054 -> 190,529` lines (**+37%**)
   against a standing goal of shrinking the reviewer surface.
4. Owner decision: DOI / anonymity for ITP 2027.
5. `main` is untouched; the branch is not merged.

## Governance

`WDD-20260807-014` (the U3 subsumption): `RC-02` **passed** this audit, so the
source-level obligation is discharged by an independent fresh-blind auditor. The
disposition can be restored on that basis; publication remained blocked by the
`RC-09` prose defect, which is now repaired and awaits re-audit.

## What this round should teach the next one

Three defects appeared **during** the repair -- two mine, one pre-existing -- and
none were found by reading:

- a cleanup routine that closed a handle then threw, so its `finally` closed it
  again and **replaced the true diagnosis** with "The handle is invalid";
- a wait loop that called `.Count` on a pipeline matching nothing, so it crashed
  **whenever nothing survived** -- the healthy path;
- a self-test bounded at `5s` where its twin used `20s`, racing its own fixture
  setup.

Rules earned:

- **Write the unit assertions before the integration run.** Two of the three
  would have been caught in seconds; each instead cost a ~90-minute gate.
- **A cleanup that both releases and validates must transfer ownership before it
  can fail**, or its error path destroys the evidence.
- **`grep -c` counts lines, not occurrences**, and a grep over a structured
  document is sampling with an unknown miss rate -- three sweeps of the ledger's
  citations gave three different answers.
- **Do not infer "never" from two consecutive failures.** An earlier draft here
  claimed the Windows gate had never completed; the repository's own receipts say
  otherwise, and `WDD-20260813-029` carries the correction.

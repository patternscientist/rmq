# A11 audit prompt — EG-CP-F03 against the amended row

Coordinator launch metadata (NOT part of the pasted prompt):

- Mode: fresh blind delta. Detached checkout of the target; no chat transcript.
- **Do not reuse the A10 auditor.** A10 recommended the amend-then-audit order;
  having them audit the amendment they recommended is not independence.
- Prefer a third model family, different from both the candidate's author and
  A10's.
- A10's report IS in the tree and is required reading for this audit — it is the
  reason the amendment exists. That is a deliberate departure from ordinary
  fresh-blind practice and is handled explicitly in the prompt.
- Log to `docs/internal/AUDIT_AND_A_DESIGN.md`; report under
  `docs/internal/audit_reports/`.
- The audit target is `89cc126`, the amendment commit. This prompt file is
  committed one commit later, so it is deliberately **not** part of the audited
  tree — a commissioning artifact should not be evidence in its own audit.

---

```text
Auditor:
- Handle: A11
- Requested title: `(A11) EG-CP-F03 amended-row fresh-blind audit`
- Mode: FRESH BLIND DELTA

Audit target:
- Base commit: 6be9e5532d90412db74506a658c3393175f6e6f7
- Target commit: 89cc126 (full: 89cc126e176379fc7bf45f948211909b80cbf021)
- Branch: claude/f03-a10-audit-repairs
- Active roadmap node and intent: Stage F row `EG-CP-F03-GEOMETRY-CLOSURE` as
  AMENDED by the two amendment rows dated 2026-07-26 in
  docs/internal/RMQ_ENDGAME_ROADMAP.md. The delta claims the amended row is
  satisfied. It does NOT claim the original row is satisfied.
- Permission: REPORT-ONLY. One file: the report named below. Scratch Lean files
  outside the repository are fine.
- Durable report: docs/internal/audit_reports/2026-07-26_A11_f03_amended_row.md

Independence:
- Do not read chat transcripts or coordinator narrative.
- UNUSUAL, AND DELIBERATE: you MUST read
  docs/internal/audit_reports/2026-07-26_A10_f03_geometry_closure.md. The A10
  audit is the reason this amendment exists, and your first job is to judge
  whether the amendment answers it or evades it. A10's findings are prior
  process evidence, not commands, and not binding on you — you may sustain,
  narrow, or overturn any of them.
- Treat every document in the delta as the claim under audit, never as evidence
  for itself. That includes DD-20260726-004 (the coordinator's retraction) and
  DD-20260726-005 (the amendment rationale).

Project-skill preflight (run first, record output):
- Governance ref: 89cc126e176379fc7bf45f948211909b80cbf021
- Runtime RMQ catalog: rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
- Applicable audit-worker role skills: NONE; omit `-RequiredSkills`, pass
  `-AllowNoRequiredSkills`. Do not name a coordinator, proof or prompt-authoring
  skill to satisfy it.

Scope:
- Delta: two amendment rows in RMQ_ENDGAME_ROADMAP.md; DD-20260726-004 and -005;
  WDD-20260726-005; a rewritten module docstring and four new theorems in
  RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean; amended headers on
  E1_ENDGAME_F03_CLOSURE_RESULT.md.
- New load-bearing theorems (namespace RMQ.SuccinctFinal.GeometryClosure):
    queryTraceResultWithStore_length_and_footprint
    orderedReadFootprintWithStore_length_and_footprint
    storesAgreeOnOrderedReadFootprint_readStoreUpdate_off_footprint
    queryTraceResultWithStore_length_and_footprint_off_diagonal
    readStoreUpdate  [def]
  Pre-existing partner they compose with:
    RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint
    (RMQ/Core/SuccinctRMQClassic.lean:1298), headline alias in
    RMQ/Headlines/RMQ.lean:251.
- Acceptance criteria: the amended evidence clause is met, AND the amendment is
  itself legitimate.
- Rejection conditions: an amendment that weakens the gate rather than
  relocating an obligation; any obligation deleted rather than moved; a theorem
  that does not meet the amended clause; any sorryAx / native_decide /
  ofReduceBool / axiom / opaque reachable from a load-bearing theorem; a
  document stating scope the theorems do not support.
- Non-goals: EG-CP-F01/F02 header schema, F04/F06 closed signature, F08 probe
  cap. Report if the delta silently depends on one.

Adversarial requirements:

1. **THE CENTRAL QUESTION: is the amendment legitimate, or is it moving the
   goalposts?** The amendment was authored by the party whose work A10 found
   short, and it makes that work sufficient. DD-20260726-005 concedes this
   conflict of interest explicitly. Judge it on the merits:
   - Does the congruence genuinely establish what the inventory would have
     established about MODEL FAITHFULNESS — that nothing observable depends on
     input content beyond `n`?
   - Is the relocated obligation genuinely relocated and not deleted? The claim
     is that syntactic eliminability is already `EG-CP-F06`'s "closed signature"
     and that F06's evidence already reads "cross-shape transcript determinism
     for equal allowed inputs/probe replies". Read F06's row
     (RMQ_ENDGAME_ROADMAP.md:377) and decide whether that reading is honest or
     convenient.
   - Does anything the original clause required now fall through the gap between
     F03, F06, F01 and F02? Enumerate the gaps you find.
   If you conclude the amendment is illegitimate, say so plainly; that is a
   supported verdict and the prompt does not favour the alternative.

2. **DOES THE THEOREM MEET THE AMENDED CLAUSE?** The clause requires a universal
   checked congruence with hypothesis (equal `n`) AND (two stores agreeing on the
   ordered read footprint), concluding identical trace and value. Verify the
   shipped theorem has exactly those quantifiers — not a stronger hypothesis
   smuggled in, not a weaker conclusion.

3. **ANTI-VACUITY, INDEPENDENTLY REPRODUCED.** The amended clause names three
   witnesses. Write your own; do not reuse the delta's.
   - dropped-hypothesis controls must FAIL;
   - the footprint hypothesis must admit stores that genuinely differ — check
     `storesAgreeOnOrderedReadFootprint_readStoreUpdate_off_footprint` really
     does that, and that `readStoreUpdate` is not degenerate;
   - the transcript must demonstrably vary with `n`, with endpoints, and with
     probe replies.
   A congruence about a machine that reads nothing would satisfy the clause
   vacuously. Rule that out.

4. **THE COMPOSITION.** Verify `queryTraceResultWithStore_eq_of_orderedReadFootprint`
   predates the delta (check it at base d09bed7) and says what the delta claims.
   Then verify the composition is sound and that the composite's hypothesis is
   strictly weaker than shared-whole-store. A10 stated the public theorems
   "neither export a sequential prior-reply invariant"; the delta corrects this,
   citing the headline alias. Adjudicate that correction independently.

5. **IS THE RETRACTION HONEST?** DD-20260726-004 withdraws the coordinator's
   contraposition as unsound, on the ground that a content-dependent value can be
   dead or cancel before an emitted event. Check that reasoning. If the
   retraction is over-broad or under-broad, say so.

6. Apply the standing requirements of docs/internal/AUDIT_PROTOCOL.md: expand
   definitions rather than trusting names; classify evidence by tier; treat the
   delta's own caveats as presumptive evidence of incomplete closure; treat
   claim-drift policy and allowlists as auditable claims.

Checks:
- git status --short --branch
- git log --oneline --decorate -20
- git diff --stat 6be9e55..89cc126
- git diff --check 6be9e55..89cc126
- lake build                       (record target count; note if it is a replay
  rather than a clean build, and say so explicitly in the report)
- lake env lean scripts/headline_axiom_check.lean
- lake env lean scripts/axiom_check.lean
- pwsh -NoProfile -File scripts/claim_drift_scan.ps1 -Strict
- pwsh -NoProfile -File scripts/design_decision_check.ps1 -Strict -Base HEAD~1
- pwsh -NoProfile -File scripts/paper_topology_lint.ps1
- your own scratch Lean for items 2, 3 and 4

Platform note: Windows CRLF working tree, Ubuntu CI. Pin Git blob ids, never
working-tree SHA-256 digests.

Report:
1. Scope and audit mode.
2. Verdict, in two parts stated separately:
   (a) is the AMENDMENT legitimate;
   (b) is the amended row SATISFIED.
   A "yes to (b), no to (a)" verdict is meaningful and expected to be possible.
3. P0/P1/P2/P3 findings with exact evidence.
4. Evidence tier for each positive claim.
5. Your disposition of each A10 finding: sustained, narrowed, or overturned.
6. Verification outcomes with exact output.
7. Roadmap alignment: does the amended matrix still gate what it was written to
   gate?
8. Best next target.
9. Report path.

Rerun strict claim drift, the strict design-decision check, and
`git diff --check` on the tree CONTAINING your report before committing.
```

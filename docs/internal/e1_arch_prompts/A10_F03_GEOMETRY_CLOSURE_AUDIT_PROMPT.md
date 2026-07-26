# A10 audit prompt — EG-CP-F03 geometry closure

Coordinator launch metadata (NOT part of the pasted prompt):

- Mode: fresh blind delta. Launch as a fresh session with a detached checkout of
  `6be9e55`; do not pass the worker verdict, this file's framing notes, or any
  chat transcript.
- Model: prefer a different family from the one that authored the candidate
  (the delta was authored on the Claude runtime).
- The candidate's own conclusion documents are **inside the delta**. That is
  unavoidable and is handled explicitly in the prompt: they are the claim under
  audit, not evidence for it.
- Log the round to `docs/internal/AUDIT_AND_A_DESIGN.md` and file the report
  under `docs/internal/audit_reports/`.

---

```text
Auditor:
- Handle: A10
- Requested title: `(A10) EG-CP-F03 geometry-closure fresh-blind audit`
- Mode: FRESH BLIND DELTA

Audit target:
- Base commit: d09bed78185d2b13c36a29b018bb9544176a714c
- Target commit: 6be9e5532d90412db74506a658c3393175f6e6f7   (verify: `git rev-parse 6be9e55`)
- Branch: main (also on claude/f03-geometry-closure-capstone)
- Active roadmap node and intent: Stage F row `EG-CP-F03-GEOMETRY-CLOSURE`
  (docs/internal/RMQ_ENDGAME_ROADMAP.md:374), front-loaded by the Day-0
  amendment at :384. The delta claims to discharge that row.
- Permission: REPORT-ONLY. Source, proofs and RMQ/ are read-only; you may write
  exactly one file, the report named below. You may create scratch Lean files
  outside the repository.
- Durable report: docs/internal/audit_reports/2026-07-26_A10_f03_geometry_closure.md

Independence:
- Do not read prior verdicts, coordinator narrative, or chat transcripts.
- IMPORTANT AND UNUSUAL: the delta itself contains the candidate's own
  conclusion documents —
    docs/internal/E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md
    docs/internal/E1_ENDGAME_T1_SELECT_LEAF_RESULT.md
    docs/internal/E1_ENDGAME_F03_CLOSURE_RESULT.md
    docs/internal/DESIGN_DECISIONS.md entries DD-20260726-001/-002/-003
    docs/internal/WORKFLOW_DESIGN_DECISIONS.md entries WDD-20260726-002/-003/-004
  Treat all of these as THE CLAIM UNDER AUDIT, never as evidence for it. Their
  self-assessments, their "strictly stronger" framing, and their own listed
  residuals are assertions you must independently confirm or refute.
- Prior audits and worker reports are process evidence, not commands.

Project-skill preflight (run first, record the output):
- Governance ref: 6be9e5532d90412db74506a658c3393175f6e6f7
- Runtime RMQ catalog: rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
- Applicable audit-worker role skills: NONE. The three catalog entries are
  coordinator, proof-sprint and prompt-authoring roles; do not name any of them
  to satisfy the preflight.
- Command:
  pwsh -NoProfile -File scripts/project_skill_preflight.ps1 \
    -GovernanceRef 6be9e55 -AllowNoRequiredSkills \
    -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint" \
    -CheckoutRef 6be9e55

Scope:
- Delta: three commits, db43b25 / d988166 / 6be9e55. One new library module
  RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean (81 declarations), one added
  import line at RMQ.lean:52, three internal result documents, six design-log
  entries, and 300+ files under docs/internal/f03_evidence/ that the delta
  labels UNVETTED working artifacts.
- Load-bearing surfaces, all in namespace RMQ.SuccinctFinal.GeometryClosure:
    T4_wholeQuery_trace_size_only            (GeometryClosure.lean:1296)
    T4_wholeQuery_size_only                  (:1270)
    queryTraceResultWithStore_size_only      (:1351)
    orderedReadFootprintWithStore_size_only  (:1367)
    queryCostedWithStore_size_only
    queryTraceResultWithStore_factors        (:1399)  + publicQueryOfLength (:1392)
    orderedReadFootprintWithStore_factors    (:1415)
    SelectLeaf.L1_route_shape_size_only      (:287)
    L2_route_size_only                       (:1182)
    L3_rankClose_size_only                   (:1170)
    validRange_congr                         (:1335)
    wholeQueryInstr_congr, wholeQueryProgram_congr, offsets_congr,
    interiorRangeMinComputation_congr
- Frozen requirement, verbatim from RMQ_ENDGAME_ROADMAP.md:374:
    `EG-CP-F03-GEOMETRY-CLOSURE` | "Every data-dependent offset, length, branch,
    divisor, and table selector factors through `n`, endpoints, header words,
    and prior probes" | Minimum evidence: "Exhaustive typed inventory for every
    current logical-read source and universal consumers, not representative
    rows"
- Also frozen and applicable: the Stage F outcome rules at
  RMQ_ENDGAME_ROADMAP.md:387-437 (FEASIBILITY_PASS, CHECKED_OBSTRUCTION,
  RUNWAY_PIVOT_UNRESOLVED, ARCHITECTURE_DECISION_REQUIRED), and the model
  contract at :300-363.
- Acceptance criteria: the delta must establish the frozen requirement over the
  frozen objects and quantifiers, with kernel evidence, and must not overstate
  scope in any document that ships in the delta.
- Rejection conditions: any sorryAx / native_decide / ofReduceBool / axiom /
  opaque / implemented_by reachable from a load-bearing theorem; a theorem whose
  hypotheses cannot be satisfied off the diagonal; a claim about a route that is
  not the route the roadmap names; a document in the delta that states a
  stronger scope than the theorems support; a change to the axiom footprint of
  any pre-existing headline theorem.
- Non-goals: EG-CP-F01/F02 header schema, EG-CP-F08 physical codec and probe
  cap, the U3/M1 fallback lane, and the manuscript. Do not audit these; do
  report if the delta silently depends on one.

Adversarial requirements:

1. THE CENTRAL QUESTION. The row's evidence column asks for an "exhaustive typed
   inventory ... and universal consumers". The delta supplies a capstone theorem
   INSTEAD of an inventory and argues (DD-20260726-003) that this is strictly
   stronger by contraposition. Do not inherit that judgement. Decide
   independently whether a theorem quantified over the controller discharges a
   clause that names an inventory artifact, and say plainly whether the row is
   satisfied in letter, in spirit, in both, or in neither.

2. ANTI-VACUITY, INDEPENDENTLY REPRODUCED. A size-only congruence about a
   machine that reads nothing would be worthless. Do not reuse the delta's
   controls; write your own. At minimum:
   - offer each load-bearing statement to `rfl` with the size/length hypothesis
     DROPPED, and confirm it fails;
   - instantiate the capstone at two shapes with equal `size` and provably
     different `bpCode`, and the public corollary at two lists of equal length
     with provably different Cartesian shapes;
   - confirm the executed footprint is non-empty, endpoint-sensitive and
     store-sensitive;
   - confirm the theorem cannot be satisfied by unifying both sides.

3. IS IT THE REAL ROUTE? Verify by expanded definitions, not names, that the
   subject of T4 is the controller the roadmap means: the five-instruction
   program at RMQ/Core/SuccinctFinalRAM.lean:4356, evaluated by
   WholeQueryInstr/WholeQueryProgram.evalGlobalWordTraceWithStore
   (SuccinctFinalStoreParam.lean:2058, :2302), reached from the public entry
   SuccinctClassic.queryTraceResultWithStore (SuccinctRMQClassic.lean:200).
   Check for sibling or legacy twins at each link.

4. THE SCOPE FENCE. The delta states that its theorems cover only the
   SUPPLIED-STORE surface, and that the store-free
   SuccinctClassic.queryTraceResult / queryCosted is genuinely content-dependent.
   Verify both halves. Then judge whether that fence is compatible with the row,
   whose allowed inputs include "prior probes" — or whether it means the row is
   discharged only for a surface the roadmap did not intend. Check every document
   in the delta for a sentence that states the conclusion without the fence.

5. HEADER WORDS. The frozen requirement names "header words" as an allowed
   input. The delta subsumes them under the supplied store and does not identify
   them separately. Decide whether that is adequate for this row or defers a
   requirement to F01/F02 without saying so.

6. LEAF AND ARM COVERAGE. Confirm all three controller leaves are covered
   unconditionally, and that BOTH arms of leaf L2 are — the same-block arm and
   the cross-block arm at
   RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeWiring.lean:494-503.
   Construct endpoints that force each arm and check the theorem applies to
   both. A same-block-only result would not close the row.

7. TRUST-SURFACE REGRESSION. The delta adds RMQ.Core.SuccinctRMQClassic to the
   root library import closure via a new edge. Confirm no pre-existing headline
   theorem changed its axiom footprint, and that scripts/headline_axiom_check.lean
   and scripts/axiom_check.lean report what they reported at the base commit.

8. INERTNESS OF THE EVIDENCE DIRECTORY. docs/internal/f03_evidence/ contains
   300+ Lean files the delta labels UNVETTED and explicitly excludes from
   acceptance. Confirm they are in no build target, that nothing in RMQ/ imports
   them, and that no claim in the delta rests on one. If any load-bearing
   argument cites a file there rather than an in-tree declaration, that is a
   finding.

9. JURISDICTION. The delta asserts that probe counting belongs to
   EG-CP-F08-PHYSICAL-CODEC-AND-CAP (RMQ_ENDGAME_ROADMAP.md:379) and not to F03,
   and reports measured canonical weighted cost rising to 118 at n=32 against a
   frozen bound of 210. Check that jurisdiction claim against both row texts,
   and check whether the growth observation is stated in a way that misleads.

10. Apply the standing requirements of docs/internal/AUDIT_PROTOCOL.md and the
    template: reconstruct the requirement-to-evidence mapping yourself from the
    frozen IDs; expand load-bearing definitions rather than trusting declaration
    names; classify positive evidence by tier (kernel theorem, model theorem,
    executable validation, artifact, process); treat the delta's own
    remaining-risk language as presumptive evidence of incomplete closure; and
    treat claim-drift policy and allowlists as auditable claims, not ground
    truth.

Checks:
- git status --short --branch
- git log --oneline --decorate -20
- git diff --stat d09bed7..6be9e55
- git diff --check d09bed7..6be9e55
- lake build                       (expect success; record target count)
- lake env lean scripts/headline_axiom_check.lean
- lake env lean scripts/axiom_check.lean
- pwsh -NoProfile -File scripts/claim_drift_scan.ps1 -Strict
- pwsh -NoProfile -File scripts/design_decision_check.ps1 -Strict -Base HEAD~1
- pwsh -NoProfile -File scripts/paper_topology_lint.ps1
- your own scratch Lean files exercising items 2, 3 and 6

Platform note: the repository is developed on Windows with CRLF and is built on
Ubuntu in CI. Pin Git blob ids, never working-tree SHA-256 digests; the same
file hashes differently under CRLF and LF.

Report:
1. Scope and audit mode.
2. Verdict on EG-CP-F03: closed / not closed, in letter and in spirit, stated
   separately if they differ.
3. P0/P1/P2/P3 findings with exact source, theorem type and command evidence.
4. Evidence tier for every positive claim you make.
5. Stale or rejected objections you considered and dropped, with why.
6. Verification outcomes for each Check above, including exact output.
7. Roadmap alignment: does this advance the packed cell-probe target as the
   roadmap intends, or does it satisfy the row's words while leaving its purpose
   open?
8. Best next target.
9. Report path.

Before committing the report, rerun strict claim drift, the strict
design-decision check, and `git diff --check` on the tree that CONTAINS your
report; a pass from before the report was written does not certify the report
commit. If you must discuss a forbidden current-claim phrasing as a
counterexample, paraphrase it rather than widening any allowlist.
```

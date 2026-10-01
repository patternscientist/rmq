# V1 Guard Repair Acceptance Matrix

Frozen before implementation on 2026-10-01. Source/base:
`447751d203a4e5d02f15680731226a56fd8894a3`; branch
`codex/v1-review-guards`; checkout
`C:/Users/poin/.codex/worktrees/v1-client-examples/RMQ`.
Node: V1 Independent Verification And Submission Freeze. This leaf closes
current-fact and constant guard gaps; coordinator acceptance remains required.

The explicit registry amendment adds `docs/V1_GUIDE.md` and
`docs/V1_CLIENTS.md` to the original 18 current-fact surfaces. V1-02's frozen
historical requirement text and matrices remain unchanged. Generic scanning
already covered these guides; this repair extends current-fact-scope guards.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-G1` | Add exactly the two existing guides to currentFactSurfacePathRegex and every exact-registry pin/list/count in the production policy regression, making 20 current surfaces. Preserve the old 18. Explicitly record the amendment; do not rewrite V1-02's historical frozen requirement text. Add discriminating production scanner probes showing a false current claim in EACH new guide is rejected and its correct counterpart accepted; preserve all existing controls including the 21-context consumer checks. Do not claim all previous generic scanning was absent; the gap is current-fact-scope guarding. | Local | Exact 20-path registry and both guide accept/reject pairs. | Policy registry -> production scanner -> pinned regression. | Both false-current guide probes rejected and their correct counterparts accepted under both shells. | Policy v29 has exactly 20 paths, preserving the original 18. Production regression passes 90 reject, 44 accept and 21 context verdicts under both shells. | Closed |
| `REQ-G2` | Add both guides to the Lean-derived 210 surface roster and V1_GUIDE to the 427 roster, using exact occurrence counts and meaningful claim-shaped anchors. Add a third Lean-derived 837572 constant from RMQ/Core/WordRAM/Packed/Capstone.lean budgetExact. Cover README.md, artifact/CLAIMS.md, docs/PAPER_THEOREM_MAP.md, docs/V1_GUIDE.md. Account correctly for comma-formatted and plain numerals; a formatting variation must not disable detection or turn 837,572 into 837. Do not rewrite existing good prose solely to evade comma parsing. Existing 210/427 checks must retain their behavior. | Local | Source extraction, exact occurrence counts, anchors and format controls. | Actual Lean files -> Get-LeanValue -> Get-SurfaceFailures -> reader surfaces. | Both printed formats pass; same-shape wrong values and malformed grouping reject. | Lean-derived 210/427/837572 rosters have 9/3/4 surfaces. Added counts: GUIDE210=1, CLIENTS210=3, GUIDE427=1; budget README=2, CLAIMS=4, THEOREM_MAP=2, GUIDE=1. | Closed |
| `REQ-G3` | Test through the same production extraction/Get-SurfaceFailures path: each new intact surface accepted; mutate one budget occurrence while retaining another legitimate occurrence and require rejection; add a conflicting budget alongside the correct one and require rejection from the matching claim shape; ensure 210/427 remain distinct and no other numeral is interpreted as this budget. Verify source extractor reads actual pinned Lean. No test-only restatement of the production predicate. | Local | Production predicate controls with intact and corrupted text. | SelfTest -> same production extractor and surface predicate. | All seven new intact consumers accept; single-occurrence corruption with another legitimate occurrence retained rejects; added conflicts fail exclusively in the matching claim shape. | Both shells pass 88 named constant controls: 14 original plus 74 new, all using production extraction/Get-SurfaceFailures. Exact IDs are enumerated below. | Closed |
| `INV-CATEGORY-SEPARATION` | Preserve List Int/half-open/leftmost semantics and separation of payload bits, proof fields, model ticks, primitive transitions and native runtime. No theorem/axiom/API edits. | Inherited | Exact scope diff; no Lean modifications. | Reader claims retain separate model identities. | Swapping 210 and 427 in each new trace/probe consumer rejects; unrelated numeral controls pass. | Exact five-file scope; no Lean, theorem, axiom, API or public prose edit. The three model quantities remain separate. | Closed |
| `REPLAY-EXACT-REGISTRY` | Inventory the exact production policy/checker consumers before edits. Preserve all prior controls; additions have unique IDs and updated independent expected rosters. Do not claim future runs as evidence. | Inherited | Original registry/control inventory and exact new-ID comparison. | Production registry -> independent expected ID roster. | Production missing/duplicate/verdict-drift controls pass; independent new-constant consumer deletion/duplication controls reject. | Original 130 fixture IDs retained in exact order, all 21 context IDs unchanged, four new policy IDs and an independent seven-consumer constant roster verified. | Closed |
| `REPLAY-SELECTOR-NONVACUITY` | Validate intact positive and named negative controls, not counts alone. Report exact IDs/counts and actual outcomes. | Inherited | Named positive/negative outcomes. | Regression exact selectors and shared constant predicate. | Positive controls accept; named negatives reject through the production final verdict or shared surface predicate. | Each shell passes 134 policy fixtures plus 21 contexts, and 88 constant controls. Exact registry and unique self-test IDs prevent silent omission or duplication. | Closed |
| `REPLAY-SUBPROCESS-DEADLINE` | Use bounded existing control runners, inspect their current deadlines and preserve finally restoration. Do not start heavy campaigns or interfere with the shared native replay slot. | Inherited | Existing bounded runner and restoration checks. | Invoke-BoundedProcess -> strict scanner/Git -> finally. | The 200 ms owned sleeper times out and is cleaned under both shells. | Existing 15000 ms Git and 30000 ms scanner deadlines preserved; both full regressions report final-clean-restoration and tracked state unchanged. No native/aggregate campaign run. | Closed |
| `CHK-G-FINAL` | Run constant_sync_check.ps1 -SelfTest and full claim_drift_policy_regression.ps1 under both pwsh and Windows PowerShell5.1; AST/JSON parse; scoped strict claim scan of changed/new prose; git diff --check; strict design per commit and exact full assignment base; exact write-scope and clean-state checks. No Lean build required for this script-only leaf. Preserve logs in .lake/v1-guards and compact exact command/result/hash record in the matrix. Finish all checks before CANDIDATE_COMPLETE. | Verification | Full required two-shell checks and exact commit checks. | Final commit -> both production guards and governance checks. | Both shell implementations, exact registries, syntax, source-range whitespace and strict per-commit design checks passed. | Exact command/result/hash records below bind to source 72c09db1f99f360ea199b62c2c3402c5c5280be9. Final evidence-commit checks are recorded separately in the final report and .lake/v1-guards. | Closed |
| `REPORT-G` | Return source/final commit, exact base/branch/worktree, requirement outcomes, failed attempts honestly, and proof digestion: conceptual change, plain-English meaning, assumptions and skeptical next question. | Reporting | Final disposition and digestion. | Matrix -> worker report -> coordinator. | Source checkpoint was not reported as completion; failure and repair history is retained. | Exact base/branch/worktree/source identified here; outcomes and proof digestion below. Coordinator acceptance remains required. | Closed |

## Pre-edit inventory

The policy JSON and exact regex/list/count pin in
`scripts/claim_drift_policy_regression.ps1` name 18 paths. Its independent
fixture roster has 130 IDs (88 reject, 42 accept) plus 21 ordered context IDs.
The constant checker has seven 210 surfaces and two 427 surfaces; its common
`Get-SurfaceFailures` consumer checks claim-shaped anchors, conflicting claims,
exact counts and historical retirement. `Get-LeanValue` reads actual source.
The regression's Git deadline is 15000 ms, scanner deadline 30000 ms, and
deadline control 200 ms; its `finally` deletes owned shadow fixtures and checks
tracked state restoration. These controls are preserved.

Skill preflight passed against governance
`ee44f04a561f2194b3713f071c26b6faf9ba7fab` with actual runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`, explicitly requiring
`rmq-proof-sprint`; log `.lake/v1-guards/preflight.log`.

## Evidence and disposition

The production implementation is source commit
`72c09db1f99f360ea199b62c2c3402c5c5280be9`, following checkpoint
`e28a772a726d4eaeda3bfba9c95d4314d598709e`. All assigned production
controls passed. This evidence-only closure changes the matrix and WDD only;
the final report identifies its exact commit and post-commit certification.
Worker disposition: CANDIDATE_COMPLETE; coordinator acceptance is still required.

## Command ledger

All commands run in the exact owned checkout; ignored evidence lives under
`.lake/v1-guards`. Final-required checks used the unchanged production sources
at the source commit above. The existing child deadlines remained 30 seconds
for each scanner invocation and 15 seconds for Git. No native or aggregate
campaign was assigned or run. A Lean build was explicitly excluded for this
script-only leaf; no Lean source or proof dependency changed.

| Role | Command | Rows / unique failure surface | Identity / result |
| --- | --- | --- | --- |
| Development | `constant_sync_check.ps1 -SelfTest` | REQ-G2/G3; source extractor, counts and shared claim predicate. | PASS at checkpoint implementation; superseded by final source runs. |
| Final-required, each shell | `constant_sync_check.ps1 -SelfTest` | REQ-G2/G3; shell compatibility and exact production controls. | See measured records below. |
| Final-required, each shell | `claim_drift_policy_regression.ps1` | REQ-G1; exact 134 fixture IDs and 21 context IDs, final scanner verdict, bounded restoration. | See measured records below. |
| Final-required | AST/JSON parse; scoped `claim_drift_scan.ps1 -Strict -Path ...`; `git diff --check` | Syntax, changed prose and whitespace. | See measured records below. |
| Final-required | `design_decision_check.ps1 -Strict -Base 447751d203a4e5d02f15680731226a56fd8894a3`; per-commit `-Head` checks; exact range whitespace and scope/clean checks | CHK-G-FINAL; committed policy compliance and ownership. | See measured records below. |

The shell paths are
`C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe`
and `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe`.


## Measured source verification

All records in this table have exit 0 and bind to source commit
`72c09db1f99f360ea199b62c2c3402c5c5280be9`. File stems below resolve under
`.lake/v1-guards`; each stem has `.stdout.log`, `.stderr.log` and
`.result.json` siblings. The JSON records retain exact arguments, shell path,
elapsed seconds and hashes. Production runs also record start UTC and shell
version: pwsh `7.6.5`; Windows PowerShell `5.1.26100.9444`.

| Record stem | Seconds | Exit | Stdout SHA-256 |
| --- | ---: | ---: | --- |
| `constant-pwsh` | 4.7934335 | 0 | `C19D16DCDCFBA55B7D207E13F981182F75F1C95468513D93336912D0B5E1A1C9` |
| `constant-winps` | 3.8073814 | 0 | `82F85AD68353C0D115BBC53236A94923C98FCB046CFADACCA99D63B58CFC4F02` |
| `design-source-range` | 2.4099215 | 0 | `59006E269382153F598D6A6AE3BECEC329E7AA39FB422E2AA893B136F89ECB25` |
| `design-source1` | 2.8259613 | 0 | `59006E269382153F598D6A6AE3BECEC329E7AA39FB422E2AA893B136F89ECB25` |
| `design-source2` | 2.7516644 | 0 | `2A4605166EABEEAEA2542055548E43AE89159A846853CF0DB550B490780E3BEF` |
| `parse-pwsh` | 1.514616 | 0 | `CE5C40AC3B8415D22126BD6F64EC3DD361EC349C6BB105CD91A31B6AB0886D8C` |
| `parse-winps` | 1.3818882 | 0 | `CE5C40AC3B8415D22126BD6F64EC3DD361EC349C6BB105CD91A31B6AB0886D8C` |
| `policy-pwsh` | 665.7165584 | 0 | `719A53BD0D9F0DC7D1872E23CED3995515B4EDE1255A7791A8109E2F95F9A367` |
| `policy-winps` | 479.4219118 | 0 | `5A290DF1D4296D8109F1B8C47C29C0D164AC27524A207DD0CD2E743CD03A4740` |

Every stderr file in that table is empty, SHA-256
`E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855`.
The exact production invocation suffixes were
`-NoLogo -NoProfile -ExecutionPolicy Bypass -File scripts/constant_sync_check.ps1 -SelfTest`
and
`-NoLogo -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_policy_regression.ps1`.
AST records call `[System.Management.Automation.Language.Parser]::ParseFile`
on both changed scripts and `ConvertFrom-Json` on the policy, requiring v29.
The complete command text is retained in the corresponding JSON record.

The design commands use
`-NoLogo -NoProfile -File scripts/design_decision_check.ps1 -Strict -Base BASE -Head HEAD`:

| Record | Exact BASE | Exact HEAD |
| --- | --- | --- |
| design-source1 | `447751d203a4e5d02f15680731226a56fd8894a3` | `e28a772a726d4eaeda3bfba9c95d4314d598709e` |
| design-source2 | `e28a772a726d4eaeda3bfba9c95d4314d598709e` | `72c09db1f99f360ea199b62c2c3402c5c5280be9` |
| design-source-range | `447751d203a4e5d02f15680731226a56fd8894a3` | `72c09db1f99f360ea199b62c2c3402c5c5280be9` |

Source scope is exactly the two scripts, policy JSON, this matrix and WDD.
`git diff --check 447751d203a4e5d02f15680731226a56fd8894a3..HEAD`
and source clean-state checks passed at the source commit above.
The required hygiene scan over `RMQ lakefile.toml` found zero matches;
`hygiene.log` is empty. No original frozen V1 matrix changed.
The nine requirement texts were also compared verbatim with the assigned prompt.
The original fixture-ID preservation record has SHA-256
`51B51893CDEBF9A869EAC379D91952980313575B398CDDAF4CEBE366C8F55132`.
Skill-preflight output has SHA-256
`06F180210B661EE60C587D31B48D1E4395A9C3A9B6BBFD776402BED5C553051C`.

A scoped production scan of this matrix, WDD and both guides passed with zero
strict failures. The correct invocation is a PowerShell `-Command` calling
`& './scripts/claim_drift_scan.ps1' -Strict -Path @('docs/internal/v1/V1_GUARD_MATRIX.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md','docs/V1_GUIDE.md','docs/V1_CLIENTS.md')`.
Its development log SHA-256 is
`3CA18EBF017581977540DB738EC51F2A08EDCF049E6688FDE0AC7241945A4E5F`.
Post-evidence-commit certification is a distinct final report record; these
source-bound measurements do not claim any future run as evidence.
The production scripts, policy and guarded prose remain byte-identical to the
source-tested commit; this closure only records evidence in the matrix and WDD.

## Exact new discriminator IDs

Both full policy runs passed the original 130 fixture IDs unchanged and these
four additions, plus all 21 original ordered context IDs:

- `v1-guide-current-cost-207-rejected`: REJECT.
- `v1-guide-current-cost-210-accepted`: ACCEPT.
- `v1-clients-current-cost-207-rejected`: REJECT.
- `v1-clients-current-cost-210-accepted`: ACCEPT.

The policy result is 90 REJECT + 44 ACCEPT + 21 context verdicts per shell.
The `subprocess-deadline-sleeper-control`, `exact-fixture-registry`,
`exact-context-registry` and `final-clean-restoration` checks all passed.

Both constant runs passed exactly 88 unique IDs: the 14 original IDs plus
these 74 new IDs, described by exact prefix/suffix products to avoid a long
repeated list:

- Four standalone IDs: `v1-exact-new-surface-registry`,
  `v1-surface-deletion-control-rejected`,
  `v1-surface-duplication-control-rejected`,
  `v1-budget-extracts-837572-from-capstone-budgetExact`.
- Three exact prefixes: `v1-210-docs-V1-GUIDE-md`,
  `v1-210-docs-V1-CLIENTS-md`, `v1-427-docs-V1-GUIDE-md`;
  each has suffixes `-intact-accepted` and `-other-model-rejected` (6 IDs).
- Four exact budget prefixes: `v1-837572-README-md`,
  `v1-837572-artifact-CLAIMS-md`, `v1-837572-docs-PAPER-THEOREM-MAP-md`,
  `v1-837572-docs-V1-GUIDE-md`. Each has 16 suffixes (64 IDs):
  `-intact-accepted`, `-unrelated-numerals-accepted`;
  `-format-F-accepted`, `-format-F-repeat-control-accepted`,
  `-format-F-one-of-several-rejected`, `-format-F-added-conflict-rejected`
  for each exact F in `837572`, `837,572`;
  and `-wrong-token-T-rejected` for each exact T in
  `837`, `572`, `210`, `427`, `83,7572`, `837,5720`.

All these IDs print PASS. ACCEPT and REJECT in their names refer to expected
production verdicts, not process failures. Intact and modified text use the
same `Get-SurfaceFailures` predicate and Lean-derived actual value. Repeating
one real claim changes only the fixture's occurrence pin to original + 1;
both that accepted control and its one-occurrence mutation use that same pin.
The mutation retains another legitimate budget occurrence. Added conflicts
retain every correct occurrence and anchor and require exclusively
`CONFLICTING` failures, so neither missing anchors nor count drift can make
those tests pass accidentally. Other-model and malformed grouping controls
also require a production conflict result. The independent seven-consumer
roster prevents omission from the generated loops from silently dropping tests.

## Failed attempts and review repair

One development command passed a comma-joined array via a native `-File`
argument. The strict scanner correctly rejected the nonexistent combined path,
exit 1 (the whole AST/JSON/scan command block took 3.405 seconds). This was an
argument-binding failure, not a rejected current claim. Its preserved log is
`claim-scan-development.log`, SHA-256
`32E66F7FA1B074C809936876DB2732616F54F5B50205788F5CE8FB87BD958F98`.
The corrected array-binding invocation passed. No production semantic fixture
failed. Read-only review found the generated constant-test roster could lose a
consumer with its production entry; source commit `72c09db1` added the
independent roster and deletion/duplication controls before final runs.
The reviewer then found no remaining blocker. No guard was weakened to pass.

## Proof digestion

Conceptually, current-fact policy membership and numeric synchronization now
reach the new reader guides. The primitive budget is extracted from the actual
Lean capstone and checked by the same surface predicate as the earlier model
constants. In plain English, changing one printed budget, adding a conflicting
budget, or dropping a new consumer can now make the shipped checks fail,
even when another correct numeral survives. Both supported Windows shells
exercised those failures and the intact controls.

Live assumptions are the pinned Lean source and the declared surface/claim
shapes. These lexical checks do not prove arbitrary prose true, establish
budget attainment, or identify model steps with native runtime. No Lean claim
changed, so a public theorem digest update is unnecessary; this matrix records
the workflow digestion. A skeptical reader should next ask whether future
reader paths or new claim phrasings are added to the independent rosters and
anchors when introduced. The downstream consumer is coordinator integration,
full candidate verification, audit disposition and archive verification;
this leaf does not accept or publish V1.

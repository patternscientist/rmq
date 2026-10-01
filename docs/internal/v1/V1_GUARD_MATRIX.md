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
| `REQ-G1` | Add exactly the two existing guides to currentFactSurfacePathRegex and every exact-registry pin/list/count in the production policy regression, making 20 current surfaces. Preserve the old 18. Explicitly record the amendment; do not rewrite V1-02's historical frozen requirement text. Add discriminating production scanner probes showing a false current claim in EACH new guide is rejected and its correct counterpart accepted; preserve all existing controls including the 21-context consumer checks. Do not claim all previous generic scanning was absent; the gap is current-fact-scope guarding. | Local | Exact 20-path registry and both guide accept/reject pairs. | Policy registry -> production scanner -> pinned regression. | Pending. | Pending. | Open |
| `REQ-G2` | Add both guides to the Lean-derived 210 surface roster and V1_GUIDE to the 427 roster, using exact occurrence counts and meaningful claim-shaped anchors. Add a third Lean-derived 837572 constant from RMQ/Core/WordRAM/Packed/Capstone.lean budgetExact. Cover README.md, artifact/CLAIMS.md, docs/PAPER_THEOREM_MAP.md, docs/V1_GUIDE.md. Account correctly for comma-formatted and plain numerals; a formatting variation must not disable detection or turn 837,572 into 837. Do not rewrite existing good prose solely to evade comma parsing. Existing 210/427 checks must retain their behavior. | Local | Source extraction, exact occurrence counts, anchors and format controls. | Actual Lean files -> Get-LeanValue -> Get-SurfaceFailures -> reader surfaces. | Pending. | Pending. | Open |
| `REQ-G3` | Test through the same production extraction/Get-SurfaceFailures path: each new intact surface accepted; mutate one budget occurrence while retaining another legitimate occurrence and require rejection; add a conflicting budget alongside the correct one and require rejection from the matching claim shape; ensure 210/427 remain distinct and no other numeral is interpreted as this budget. Verify source extractor reads actual pinned Lean. No test-only restatement of the production predicate. | Local | Production predicate controls with intact and corrupted text. | SelfTest -> same production extractor and surface predicate. | Pending. | Pending. | Open |
| `INV-CATEGORY-SEPARATION` | Preserve List Int/half-open/leftmost semantics and separation of payload bits, proof fields, model ticks, primitive transitions and native runtime. No theorem/axiom/API edits. | Inherited | Exact scope diff; no Lean modifications. | Reader claims retain separate model identities. | Pending. | Pending. | Open |
| `REPLAY-EXACT-REGISTRY` | Inventory the exact production policy/checker consumers before edits. Preserve all prior controls; additions have unique IDs and updated independent expected rosters. Do not claim future runs as evidence. | Inherited | Original registry/control inventory and exact new-ID comparison. | Production registry -> independent expected ID roster. | Pending. | Pending. | Open |
| `REPLAY-SELECTOR-NONVACUITY` | Validate intact positive and named negative controls, not counts alone. Report exact IDs/counts and actual outcomes. | Inherited | Named positive/negative outcomes. | Regression exact selectors and shared constant predicate. | Pending. | Pending. | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | Use bounded existing control runners, inspect their current deadlines and preserve finally restoration. Do not start heavy campaigns or interfere with the shared native replay slot. | Inherited | Existing bounded runner and restoration checks. | Invoke-BoundedProcess -> strict scanner/Git -> finally. | Pending. | Pending. | Open |
| `CHK-G-FINAL` | Run constant_sync_check.ps1 -SelfTest and full claim_drift_policy_regression.ps1 under both pwsh and Windows PowerShell5.1; AST/JSON parse; scoped strict claim scan of changed/new prose; git diff --check; strict design per commit and exact full assignment base; exact write-scope and clean-state checks. No Lean build required for this script-only leaf. Preserve logs in .lake/v1-guards and compact exact command/result/hash record in the matrix. Finish all checks before CANDIDATE_COMPLETE. | Verification | Full required two-shell checks and exact commit checks. | Final commit -> both production guards and governance checks. | Pending. | Pending. | Open |
| `REPORT-G` | Return source/final commit, exact base/branch/worktree, requirement outcomes, failed attempts honestly, and proof digestion: conceptual change, plain-English meaning, assumptions and skeptical next question. | Reporting | Final disposition and digestion. | Matrix -> worker report -> coordinator. | Pending. | Pending. | Open |

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

Implementation and final checks pending. Status: OPEN.

## Command ledger plan

All commands run in the exact owned checkout; ignored evidence lives under
`.lake/v1-guards`. Final-required checks use the unchanged production sources
after the implementation freezes. Expected guard runtime is seconds for
constant checks and several minutes for the full scanner regression; the
existing child deadlines remain 30 seconds for each scanner invocation and
15 seconds for Git. No native or aggregate campaign is assigned here.

| Role | Command | Rows / unique failure surface | Identity / result |
| --- | --- | --- | --- |
| Development | `constant_sync_check.ps1 -SelfTest` | REQ-G2/G3; source extractor, counts and shared claim predicate. | Dirty implementation; pending. |
| Final-required, each shell | `constant_sync_check.ps1 -SelfTest` | REQ-G2/G3; shell compatibility and exact production controls. | Pending. |
| Final-required, each shell | `claim_drift_policy_regression.ps1` | REQ-G1; exact 134 fixture IDs and 21 context IDs, final scanner verdict, bounded restoration. | Pending. |
| Final-required | AST/JSON parse; scoped `claim_drift_scan.ps1 -Strict -Path ...`; `git diff --check` | Syntax, changed prose and whitespace. | Pending. |
| Final-required | `design_decision_check.ps1 -Strict -Base 447751d203a4e5d02f15680731226a56fd8894a3`; per-commit `-Head` checks; exact range whitespace and scope/clean checks | CHK-G-FINAL; committed policy compliance and ownership. | Pending. |

The shell paths are
`C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe`
and `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe`.

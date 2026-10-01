# V1 evidence-hardening command ledger

This ledger records commands actually executed in the managed worktree
`C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ`. Paths below are
repository-relative unless an executable path is shown. The focused suites are
fixture controls and are not replays of an old lifecycle semantic campaign.

## Source checkpoint

| Classification | Exact command | Outcome |
| --- | --- | --- |
| Governance precondition | `pwsh -NoLogo -NoProfile -File scripts/project_skill_preflight.ps1 -GovernanceRef ee44f04a561f2194b3713f071c26b6faf9ba7fab -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint" -RepositoryRoot C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ` | PASS before implementation at the exact governed base. |
| Syntax/data validation | PowerShell AST parse of all eight edited `.ps1` files; `ConvertFrom-Json` on `repair-r4/FAILURE_CONTROL_REGISTRY.json` | PASS; registry contains 60 controls. This is validation, not a semantic test. |
| Focused fixture test, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile pwsh` | PASS 32/32. Aggregate `.lake/v1-evidence/pwsh-be6b18e5a8674e4c9fdc3dcc4b21c8fe/RESULT.json`: 15,798 bytes, SHA-256 `0052ad71967d318305aae03c73fd68cd8ab3d1a5dd258e7a47fa9e3287213b93`. Committed copy: `focused-pwsh-result.json`. |
| Focused fixture test, Windows PowerShell 5.1 | `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile winps` | PASS 32/32. Aggregate `.lake/v1-evidence/winps-b88de4b7892747a6ac9e418fb43c6a19/RESULT.json`: 21,973 bytes, SHA-256 `54fc9c6d229e993441aa6e4befa37607978f07907668deb3d5966cfb2a22cddb`. Committed copy: `focused-winps-result.json`. |
| Exact registry boundary, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r1/registry_controls.ps1 -Shell C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -Profile pwsh -EvidenceRoot .lake/v1-evidence/registry-controls-stable-pwsh-20261001` | PASS 12/12. `summary.json`: 48,020 bytes, SHA-256 `5b1668075b5715ce0bc3c553e7fcd45f2f3e25733afd706247b202bd05c8cade`. Committed copy: `registry-controls-pwsh-summary.json`. |
| Exact registry boundary, Windows PowerShell 5.1 | `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r1/registry_controls.ps1 -Shell C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -Profile winps -EvidenceRoot .lake/v1-evidence/registry-controls-stable-winps-20261001` | PASS 12/12. `summary.json`: 67,072 bytes, SHA-256 `4e309624928507cc7a2a5a35e7c9a9b46a24a250da4885630b79010e274b74b0`. Committed copy: `registry-controls-winps-summary.json`. |

Each focused child uses the committed finite deadline recorded in its aggregate:
30 seconds for selector/registry probes, 45 seconds for EH3 child paths, and
180 seconds for the copied 11-node dependency closure. Every fixture lives
beneath the run's owned `.lake` root. The EH2 control restores the copied
`lean.exe` and compares its restored SHA-256 with entry identity; it never
writes the installed toolchain.

The final stable-source 60-control production-registry replay, candidate
auxiliary replay, final policy checks, and postcommit whitespace checks are
pending at this checkpoint. Earlier full-registry runs are retained as
superseded observations only:

- The first PowerShell 7 attempt executed 60 and passed 53; K2-P/C/Q/M/F/T/G
  rejected because the legacy field held a 40-hex Git commit identity. Its
  aggregate SHA-256 is
  `03007916ab1d1430725e6f9f50153e76ca8feb5bfcc5c9c8b6a5161d912de2d1`.
- After typing K2 `git:HEAD`, intermediate runs passed 60/60 on both shells
  (`b55e448a159616db62221c74be33719b23487ef2949ddfc0e0ad4f403bbaee1a`
  and `fc6c42a12e3e3ea05e2e5fcb71c80e2dc03fabc739340a8c9aa52a2ddb6f3c74`).
  Later EH3 source review changed `run_controls.ps1` and
  `finalizer_control.ps1`, so these are not final-source receipts.
- Two later full-registry attempts were interrupted after a syntactically valid
  `{}` frozen-registry edge was found. Their partial console observations are
  not aggregate results and are not reported as passes.

`source_manifest.py`, `collect_evidence.py`, `verify_evidence.py`, and the
cached historical `RESULTS.json` files were inspected but not executed or
counted as tests. Their exact dependencies and old-key readers are recorded in
`../../extensions/lifecycle1/HISTORICAL_VERIFIERS.md`.

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
| Focused fixture test, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile pwsh` | PASS 32/32. Aggregate `.lake/v1-evidence/pwsh-be6b18e5a8674e4c9fdc3dcc4b21c8fe/RESULT.json`: 15,798 bytes, SHA-256 `0052ad71967d318305aae03c73fd68cd8ab3d1a5dd258e7a47fa9e3287213b93`. This first-checkpoint aggregate is superseded by the exact-path follow-up; its former committed filename is reused for the current 52-case aggregate. |
| Focused fixture test, Windows PowerShell 5.1 | `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile winps` | PASS 32/32. Aggregate `.lake/v1-evidence/winps-b88de4b7892747a6ac9e418fb43c6a19/RESULT.json`: 21,973 bytes, SHA-256 `54fc9c6d229e993441aa6e4befa37607978f07907668deb3d5966cfb2a22cddb`. This first-checkpoint aggregate is superseded by the exact-path follow-up; its former committed filename is reused for the current 52-case aggregate. |
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

## Exact-path identity follow-up

The independent follow-up began from exact source checkpoint
`7e3a1d086d81eee924036afc3f84b1447ac503cb` in the same managed worktree.
The first source checkpoint and its receipts remain immutable history; later
controls identified below supersede evidence conclusions without relabelling
those observations.

| Classification | Exact command | Outcome |
| --- | --- | --- |
| Follow-up governance precondition | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -File scripts/project_skill_preflight.ps1 -GovernanceRef ee44f04a561f2194b3713f071c26b6faf9ba7fab -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint" -RepositoryRoot C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ` after `git rev-parse HEAD` returned `7e3a1d086d81eee924036afc3f84b1447ac503cb` | PASS. This re-established the governed workflow before the follow-up edit. |
| Auxiliary replay at the first checkpoint | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r4/aux_controls.ps1 -HarnessRef 7e3a1d086d81eee924036afc3f84b1447ac503cb -Expect candidate -OutputRoot .lake/v1-evidence/aux-checkpoint-7e3a1d08` | PASS 27/27. `RESULT.json`: 16,363 bytes, SHA-256 `97ba40f98b9cacc63fb0792d720cb1a15ee8fbd7b36e1871d413c1b7b054223e`. This is a superseded observation because it predates the exact trusted-path/final-identity repair. |
| Full production registry at the first checkpoint, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1 -HarnessRef 7e3a1d086d81eee924036afc3f84b1447ac503cb -Profile pwsh -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -OutputRoot .lake/v1-evidence/failure-controls-v3-checkpoint-pwsh-20261001` | Observed PASS 60/60. `RESULT.json`: 388,288 bytes, SHA-256 `fdcba0862fa462afadda4ed1f2891ef1fcaa6dd8f8936d86160a56a22b182c4f`. Independent review then demonstrated unrelated same-basename and wrong-root substitution acceptance, so this receipt is superseded and is not final evidence. |
| Follow-up syntax/data development check | PowerShell AST parse under PowerShell 7 and Windows PowerShell 5.1 of `failure_controls.ps1`, `predicates.ps1`, `aux_controls.ps1`, and `evidence_hardening_controls.ps1`; strict UTF-8 JSON parse and CRLF-to-LF normalized SHA-256 of the v3 registry | PASS during implementation. The registry remains exactly 60 unique ordered controls; the follow-up normalized SHA-256 is `6b4734e9cbd36955636452f9b3b93089062481de52b2cf1e9bdd37e50d17db5d`. Syntax/data parsing is validation, not a semantic replay. |
| Production loader boundary, both target profiles | `failure_controls.ps1 -HarnessRef worktree -Profile <pwsh|winps> -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -ProbeOnly` executed by the pinned PowerShell 7 runner | PASS for each target profile; each emitted the exact ordered 60 IDs. This checks loading and selection only and launches no semantic control. |
| Direct predicate development smoke, both shells | `v1-predicate-smoke.ps1 -Predicate <managed-worktree>/docs/internal/extensions/lifecycle1/repair-r4/predicates.ps1` under the pinned PowerShell 7 and Windows PowerShell 5.1 executables | PASS 7/7 on each shell for same-path aliases, wrong-root rejection, verified-null rejection, changed-final acceptance, legacy Git SHA-1, valid partial typed projection, and out-of-base typed-index rejection. This task-owned scratch check is development evidence; committed focused and auxiliary controls remain authoritative. |
| Corrected focused fixture test, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile pwsh -OutputRoot .lake/v1-evidence/identity-focused-pwsh-20261001` | PASS 52/52. Aggregate `RESULT.json`: 26,128 bytes, SHA-256 `7df7250de0bf68484ae473810aec5f4cd864a4f42b41ce7ecefc0d32625970f2`; committed copy `focused-pwsh-result.json`. Thirty predicate cases include every trusted path class, final-state relation, legacy type width and typed-stage projection; all ten EH3 negatives match their mutation-specific error. |
| Corrected focused fixture test, Windows PowerShell 5.1 | `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/v1/evidence/evidence_hardening_controls.ps1 -Profile winps -OutputRoot .lake/v1-evidence/identity-focused-winps-20261001` | PASS 52/52. Aggregate `RESULT.json`: 36,715 bytes, SHA-256 `d66e9ac129d59178487509dbf5bd346cfaa7bb0a1b3c59078866ac5c9c7ecc64`; committed copy `focused-winps-result.json`. Shell-capable EH2/EH3 children execute under WinPS; the selected-shell runtime control observes the production failure runner's exact PowerShell 7-only rejection, and nine selector/registry records truthfully name the pinned PowerShell 7 subprocess plus the WinPS target profile. |

The first 32/32 focused aggregates above are also superseded for final use:
nine selector/registry subprocess records did not disclose that their actual
executing shell was PowerShell 7 even in the aggregate labelled `winps`, and
the ten EH3 negatives accepted any nonempty `StageError`. Their production
observations remain preserved. The follow-up focused runner records the actual
executing shell/target profile, exercises the deliberate PowerShell 7-only
failure-runner boundary under the selected shell, and pins mutation-specific
EH3 error patterns. Its final both-shell results are recorded only after those
runs complete.

The corrected focused aggregates pass 52/52 on both shells and replace the
two superseded committed 32-case files. The exact 60-case registry retains 57 receipt-bearing controls. `K1-W`,
`K2-W`, and `LV-W` are guarded durable-write-failure controls: their required
durable output is absent, so pin coverage is explicitly inapplicable rather
than reported as a successful verification. Auxiliary and full 60-control
evidence remains pending until the identity-repair source checkpoint exists.

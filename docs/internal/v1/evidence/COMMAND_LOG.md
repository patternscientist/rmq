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
| Production loader boundary, both target profiles | `failure_controls.ps1 -HarnessRef worktree -Profile <pwsh or winps> -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -ProbeOnly` executed by the pinned PowerShell 7 runner | PASS for each target profile; each emitted the exact ordered 60 IDs. This checks loading and selection only and launches no semantic control. |
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
EH3 error patterns. The final focused scope is 30 in-process host predicate
cases, 13 selected-shell child cases and nine PowerShell-7-only
selector/registry consumers whose records disclose both executing shell and
target profile.

The corrected focused aggregates pass 52/52 on both shells and replace the
two superseded committed 32-case files. The exact 60-case registry retains 57 receipt-bearing controls. `K1-W`,
`K2-W`, and `LV-W` are guarded durable-write-failure controls: their required
durable output is absent, so pin coverage is explicitly inapplicable rather
than reported as a successful verification. The source-bound auxiliary,
complete-registry and wording-transfer evidence follows.

## Stable exact-path source evidence

The identity repair was committed as
`a8f1c512e9a5d3d57abae6cd9b988978246af768`. Its v3 registry worktree raw
SHA-256 is `9bf8d0ac1406e67233601c42cb1c4a57a0b28212365b72712393f3a4c66c6e51`;
the runner pins its CRLF-to-LF-normalized SHA-256
`6b4734e9cbd36955636452f9b3b93089062481de52b2cf1e9bdd37e50d17db5d`.

| Classification | Exact command | Outcome |
| --- | --- | --- |
| Auxiliary replay, PowerShell 7 | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r4/aux_controls.ps1 -HarnessRef a8f1c512e9a5d3d57abae6cd9b988978246af768 -Expect candidate -OutputRoot .lake/v1-evidence/identity-aux-pwsh-a8f1c512` | PASS 46/46. Raw `RESULT.json`: 26,491 bytes, SHA-256 `e0fb1081e7218f977c352dc8b094a05366ad11e1fee92ee67bcfdf63d06450d4`; compact `aux-pwsh-result.json`: 24,925 bytes, SHA-256 `ed05ff18ca3b2a75d3640b5a96650423493a09c083177086014b3bdf0f1b99cd`. Finalization passed with two verified outer pins and no integrity/cleanup error. |
| Auxiliary replay, Windows PowerShell 5.1 | `C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r4/aux_controls.ps1 -HarnessRef a8f1c512e9a5d3d57abae6cd9b988978246af768 -Expect candidate -OutputRoot .lake/v1-evidence/identity-aux-winps-a8f1c512` | PASS 46/46. Raw `RESULT.json`: 42,831 bytes, SHA-256 `a19f7c8639e8407f764836a7df35f1e7b73b1d9c85cb7be67f4275c06e7ce935`; compact `aux-winps-result.json`: 24,875 bytes, SHA-256 `b47fbc8822b729ab8b82e5bddb0d3b0a82730efaa9c72eafb8b3bee36d140b1d`. Finalization passed with two verified outer pins and no integrity/cleanup error. |
| Complete production registry, `pwsh` profile | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1 -HarnessRef a8f1c512e9a5d3d57abae6cd9b988978246af768 -Profile pwsh -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -OutputRoot .lake/v1-evidence/identity-full60-pwsh-a8f1c512` | PASS 60/60. Raw `RESULT.json`: 419,625 bytes, SHA-256 `75792302864c807eb73748e01700fc8efeee039cd93021b42403c48a58702eb7`; compact `failure-controls-pwsh-result.json`: 136,706 bytes, SHA-256 `7cc69e894c90fe8c5d513ca037b37ccc8bb7047d3cc42c1d6e0e56d83ae32a13`. All 57 receipt-bearing controls have applicable verified pin coverage; exact W controls have false/null applicability/result; 13 outer pins verify and the worktree state is unchanged and clean. |
| Complete production registry, `winps` profile | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1 -HarnessRef a8f1c512e9a5d3d57abae6cd9b988978246af768 -Profile winps -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -OutputRoot .lake/v1-evidence/identity-full60-winps-a8f1c512` | PASS 60/60. Raw `RESULT.json`: 430,305 bytes, SHA-256 `4e420d51215ee2b4b359e655e0d20ffb98b8effc4a6dfd0cdee37b68ce338f2f`; compact `failure-controls-winps-result.json`: 131,513 bytes, SHA-256 `cf84ca4eb02714008bf86b534bf6ae34460e21e38b1f748608e8fcce5f61078a`. The same 57+3 partition, 13 outer pins, finalization and clean-state assertions pass. |
| Compact receipt derivation | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File C:/Users/poin/Documents/RMQ/research-duet-20261001/implementation/v1-compact-receipts.ps1 -Kind <aux or full60> -InputPath <raw RESULT.json> -InputLabel <repository-relative raw path> -OutputPath <task-owned compact path>` for each of the six named raw aggregates | Generator SHA-256 `9e9021ea621dd062017ca3856e62493eb48cbaea638ceeadfccf7e566d5d1881`. This is deterministic record generation, not another test. Every compact receipt says so and retains generator/source identity, counts, decisive per-case fields and finalization. |
| Evidence-receipt validation, both shells | `v1-verify-compact-receipts.ps1 -Directory C:/Users/poin/Documents/RMQ/research-duet-20261001/implementation` under the pinned PowerShell 7 and Windows PowerShell executables | PASS for six compact aggregate receipts plus two registry-comparison receipts under each shell. Verifier SHA-256 `393ba7ed6ca849fc83a8aa3e9d5c62bfeabf57961a495d1cb4a52639f1ab7189`. This checks derived records against named raw identities and invariants; it does not re-execute controls. |

The complete runs consume the current exact-path predicate and all 60 unchanged
case mappings. They prove 57 receipt-bearing pin verdicts plus three guarded
no-receipt outcomes; they are not described as 60 independent pin receipts.

## No-receipt metadata wording transfer

Independent review found two prose-only overstatements in registry metadata.
`receiptSemantics.guardMeaning` and `shapes.W` implied that every W control
forbids a success marker. K1-W and K2-W require nonzero exit, absent durable
receipt and exact stderr. LV-W additionally declares absent `PASS.json` and
absent `LIFE1-VALIDATOR PASS` stdout. No case mapping or expectation changed.

| Classification | Exact command | Outcome |
| --- | --- | --- |
| Original/final registry structural comparison, both shells | `v1-registry-wording2-compare.ps1 -OldPath FAILURE_CONTROL_REGISTRY.original-reconstructed.json -NewPath FAILURE_CONTROL_REGISTRY.wording2.json -OutputPath <shell-specific receipt>` under the pinned PowerShell 7 and Windows PowerShell executables | PASS under each shell. Comparator SHA-256 `05deecda397ba6a4f8df04bca859d07b17004623da260909131b52cd63b42da1`; removing exactly `receiptSemantics.guardMeaning` and `shapes.W` makes the parsed registries identical. Original raw/normalized SHA-256: `9bf8d0ac1406e67233601c42cb1c4a57a0b28212365b72712393f3a4c66c6e51` / `6b4734e9cbd36955636452f9b3b93089062481de52b2cf1e9bdd37e50d17db5d`; final raw/normalized: `06166cbc87e94008c10c0d92b98a13364f41700771e3c118a67e58d0d01e4339` / `218a41449d9da04f816b385bf488c1957baa05b73457d841278d78f6ae1547f1`. Committed receipts: pwsh 1,861 bytes / SHA-256 `7992f1e85f306bf11214aa1635cb3e36461ab4e486823724d2709640a2bf1f94`; WinPS 2,158 bytes / SHA-256 `c5030d216cfe02f580d6c3d42d51354fd77c156efdd81f2e491ee6a1c4d3f460`. This is structural validation, not a semantic replay. |
| Intermediate wording checkpoint | Commit `196b47a3804fa1eaf58c2ee6b39e3dd2b02be6f5`; full ProbeOnly and exact `K1-W,K2-W,LV-W` replay under both profiles | ProbeOnly emitted the exact 60 IDs and exact three-ID subset; semantic runs passed 3/3. Raw hashes were pwsh `544c19667509daa95fc6cee33adb321022a2d2b6c6e0e4dd2a699b5e06eb8395` (27,803 bytes) and WinPS `ab027b73fddd54db7d623fc34388fe1e5547c879c5b1d7e141d07915aa407c08` (28,673 bytes). These observations are preserved but superseded for final wording after `shapes.W` review. |
| Final loader boundary, both profiles | `failure_controls.ps1 -HarnessRef c79beae0d99519719d2a83882e6dd369bc29026e -Profile <pwsh or winps> -RegistryPath docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json -ProbeOnly`, plus the same command with `-OnlyControl @('K1-W','K2-W','LV-W')`, executed by pinned PowerShell 7 | PASS. Each full probe emitted the exact ordered 60 IDs; each focused probe emitted exactly `K1-W,K2-W,LV-W`. No semantic control is launched by ProbeOnly. |
| Initial final-wording observation with staged compact files present | Exact `c79beae0` three-control commands below, using output roots `wording-transfer-final-wguards-<profile>-c79beae0` | PASS 3/3 each, with identical before/after tracked and untracked state. Raw SHA-256: pwsh `ad569908c3e8c923d278c0f54e531c1a46d0c5859b1298b43dbd3085c65cb804` (28,761 bytes), WinPS `5dd320e2cd5b8f9702d90cc53a169158d2c48b75e7cc43034b521ef4c229a02e` (29,646 bytes). Preserved as an observation; the clean-worktree rerun below is the final transfer evidence. |
| Final clean-worktree W guards, `pwsh` profile | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -Command "& 'docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1' -HarnessRef 'c79beae0d99519719d2a83882e6dd369bc29026e' -Profile 'pwsh' -RegistryPath 'docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json' -OutputRoot '.lake/v1-evidence/wording-transfer-final-clean-wguards-pwsh-c79beae0' -OnlyControl @('K1-W','K2-W','LV-W')"` | PASS 3/3. Raw `RESULT.json`: 28,210 bytes, SHA-256 `bb40dcc51d02ce9b9cd7402f3b38a3454a70138055d54df4a5ee4dd87dcb6962`; compact `wording-transfer-wguards-pwsh-result.json`: 13,036 bytes, SHA-256 `5c75cece2f1923d55c7012ca20879f88226747ecfdcd055e58f79f91b62ef9a6`. Source state is exact clean `c79beae0` before and after; coverage is 0 receipt-bearing plus three guarded no-receipt, 13 outer pins verified, and finalization has no error. |
| Final clean-worktree W guards, `winps` profile | `C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -Command "& 'docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1' -HarnessRef 'c79beae0d99519719d2a83882e6dd369bc29026e' -Profile 'winps' -RegistryPath 'docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json' -OutputRoot '.lake/v1-evidence/wording-transfer-final-clean-wguards-winps-c79beae0' -OnlyControl @('K1-W','K2-W','LV-W')"` | PASS 3/3. Raw `RESULT.json`: 29,108 bytes, SHA-256 `99ecd063a8d0d95a035ba415ae0de7a7b94dd63d1963e162551d2c54857c1192`; compact `wording-transfer-wguards-winps-result.json`: 12,740 bytes, SHA-256 `ff53e4b5a5824513514cabe9ca86e841e0dcdff100a4c2c8e432c94341b6c5ad`. The same clean source state, 0+3 coverage, 13 outer pins and error-free finalization assertions pass. |

The final wording transfer is deliberately bounded: the unchanged semantic
campaign remains the both-profile 60/60 run at `a8f1c512`; only the metadata
loader and three affected W guards are rerun at `c79beae0`.

## Final evidence-record checks

| Classification | Exact command | Outcome |
| --- | --- | --- |
| Managed compact-receipt validation, both shells | `v1-verify-compact-receipts.ps1 -Directory C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ/docs/internal/v1/evidence` under the pinned PowerShell 7 and Windows PowerShell 5.1 executables | PASS with eight checked receipts under each shell at the final managed paths. Verifier SHA-256 `393ba7ed6ca849fc83a8aa3e9d5c62bfeabf57961a495d1cb4a52639f1ab7189`. This parses and cross-checks committed projections; it does not rerun their controls. |
| Frozen matrix requirement check | `python C:/Users/poin/Documents/RMQ/research-duet-20261001/implementation/v1-verify-frozen-matrix.py` | PASS: all 12 rows at `7e3a1d086d81eee924036afc3f84b1447ac503cb`, all 20 rows at `a8f1c512e9a5d3d57abae6cd9b988978246af768`, and all 20 rows at pre-evidence `HEAD` retain their exact second-column requirement text; row IDs are unique. Task-owned verifier SHA-256 `00c137152a36dc4b692333eab385995921821a4b812e308ec7e91d36b0ca40fd`. This is record validation, not a semantic test. |
| Strict scoped claim scan | Pinned PowerShell 7 executed task-owned wrapper `v1-run-final-claim-scan.ps1 -ScannerPath C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ/.lake/v1-evidence/checkers/claim_drift_scan_447751d2.ps1` from the managed repository root. The wrapper passes `-Strict -IncludeProcessRecords -Path` with the exact WDD, historical guide, matrix, command ledger, two focused aggregates, two registry summaries and eight new compact/comparison receipts. | PASS: `scan complete (109 hits, 0 strict failures)`. The scanner is the exact `447751d203a4e5d02f15680731226a56fd8894a3:scripts/claim_drift_scan.ps1` blob, 20,541 bytes, SHA-256 `e939ad8c47e1cc42e0db4f4aab9b439cb2f8402a22512658f8dc98545719ff84`; wrapper SHA-256 `c1a30345beacfc7715b5c367d6e216533711fa046de3015e1fc5baca50302fa8`. The pre-row capture is 26,257 bytes, SHA-256 `f62d1f681dd41d65dcbe0e450d9afc2938dde7e3e82bc9e18b849d6edd05a904`; the unchanged-result final-content rerun is reported with worker completion. |
| Final working-tree policy checks | `git diff --check`; `scripts/design_decision_check.ps1 -Strict -Base HEAD`; exact changed-path comparison against the 11 evidence-owned paths; Markdown table-width validation; the AGENTS hygiene scans over `RMQ lakefile.toml` and `RMQ` | PASS. Strict design checked 11 changed files (zero code, ten workflow, one neutral); exact scope contained 11 paths; both Markdown files had stable table widths; both hygiene scans found no forbidden match. These checks are repeated where applicable after commit. |

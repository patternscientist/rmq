#!/usr/bin/env pwsh

$ErrorActionPreference = "Stop"

function Fail([string]$Message) {
  Write-Host "WORKER-PROMPT-REGRESSION: FAIL $Message"
  exit 1
}

$powerShellExecutable = (Get-Process -Id $PID).Path
if (-not $powerShellExecutable) {
  Fail "could not resolve the current PowerShell executable"
}

function Write-Prompt(
  [string]$Path,
  [string]$FirstLine,
  [string]$Governance,
  [string]$Base,
  [string]$Branch,
  [string[]]$Extra = @()
) {
  @(
    $FirstLine
    ""
    "Worker identity:"
    "- Handle: E1-01R1"
    "- Requested title: (E1-01R1) Repair the machine"
    "- Fresh or returning worker: RETURNING because this repairs its audited candidate."
    ""
    "Skill:"
    "Use `$rmq-proof-sprint before starting."
    "- Workflow-governance ref: $Governance"
    ""
    "Checkout contract:"
    "- Task mode: WRITE."
    "- Exact base/target commit: $Base."
    "- For this write task, create branch exactly $Branch in a fresh worktree."
    ""
    "Roadmap contract:"
    "- Node/join: E1 repair before public M1 plus E1 composition."
    "- Local owned rung: repair the audited small-step candidate."
    "- Roadmap-node closure condition: coordinator acceptance after exact-commit audit."
    "- Goal: close the frozen E1 repair contract."
    "- Required theorem/file/tool: the checked E1 small-step capstone and validator."
    "- Write scope: E1 source, its matrix, and directly required checks."
    "- Non-goals: no A1 refactor or public merge."
    ""
    "Acceptance contract:"
    "- Frozen acceptance IDs: E1-TEST, INV-INSTRUCTION-ATOMICITY, CHK-DIFF."
    "- Record exact propositions and adversarial mutations in the matrix."
    "- REPLAY-EXACT-REGISTRY: declare and validate exact ordered case IDs and mappings."
    "- REPLAY-SELECTOR-NONVACUITY: run exactly one known ID and reject unknown IDs."
    "- REPLAY-SUBPROCESS-DEADLINE: bound child stages and clean up after timeout."
    ""
    "Forbidden shortcuts:"
    "- No wrappers, self-oracles, uncounted data, or theorem-name-only closure."
    ""
    "Context:"
    "- Read AGENTS.md, the assigned roadmap section, and direct consumers."
    ""
    "Completion:"
    "- Continue until every frozen row closes or a formal obstruction is proved."
    ""
    "Verification:"
    "- lake build"
    "- git diff --check"
    "- git diff --check $Base..HEAD"
    ""
    "Report:"
    "- Begin candidate completion with Status: CANDIDATE_COMPLETE."
    "- State that coordinator acceptance is still required."
  ) + $Extra | Set-Content -LiteralPath $Path -Encoding utf8
}

function Invoke-Case(
  [string]$Name,
  [int]$ExpectedExit,
  [string]$PromptPath,
  [string]$Governance,
  [string]$Base,
  [string]$Status,
  [string]$Feedback,
  [string[]]$RequiredOutput = @(),
  [string]$SemanticReview = "COMPLETE",
  [string]$DestinationTaskKind = "RETURNING_TASK",
  [string]$DestinationRuntimeEvidence = "VERIFIED_CURRENT"
) {
  $arguments = @(
    "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $preflight,
    "-RepositoryRoot", $tempRoot,
    "-PromptPath", $PromptPath,
    "-GovernanceRef", $Governance,
    "-WorkerBase", $Base,
    "-WorkerHandle", "E1-01R1",
    "-RequestedTitle", "(E1-01R1) Repair the machine",
    "-RequiredSkill", "rmq-proof-sprint",
    "-PromptStatus", $Status,
    "-FailureModeFeedbackStatus", $Feedback,
    "-SemanticContractReviewStatus", $SemanticReview,
    "-DestinationTaskKind", $DestinationTaskKind,
    "-DestinationRuntimeEvidence", $DestinationRuntimeEvidence,
    "-TaskMode", "WRITE",
    "-WorkerBranch", "codex/e1-repair"
  )
  $output = @(& $script:powerShellExecutable @arguments 2>&1)
  $exitCode = $LASTEXITCODE
  if ($exitCode -ne $ExpectedExit) {
    Fail "$Name expected exit $ExpectedExit, got $exitCode`n$($output -join [Environment]::NewLine)"
  }
  foreach ($pattern in $RequiredOutput) {
    if (-not ($output -match $pattern)) {
      Fail "$Name did not emit '$pattern'`n$($output -join [Environment]::NewLine)"
    }
  }
  Write-Host "WORKER-PROMPT-REGRESSION: PASS $Name"
}

$preflight = Join-Path $PSScriptRoot "worker_prompt_preflight.ps1"
if (-not (Test-Path -LiteralPath $preflight -PathType Leaf)) {
  Fail "production worker prompt preflight is missing"
}

$coordinatorSkill = Join-Path $PSScriptRoot "..\.agents\skills\rmq-coordinator\SKILL.md"
if (-not (Test-Path -LiteralPath $coordinatorSkill -PathType Leaf)) {
  Fail "coordinator skill is missing"
}
$coordinatorPolicy = Get-Content -Raw -LiteralPath $coordinatorSkill
foreach ($policyCase in @(
    @{
      Name = "auto-chain-private-repair-base-allowed"
      Literal = "AUTO-CHAIN-PRIVATE-REPAIR-BASE"
    },
    @{
      Name = "auto-chain-main-merge-stopped"
      Literal = 'not authorize integration into `main` or a published roadmap frontier'
    },
    @{
      Name = "auto-chain-terminal-watch-retired"
      Literal = "AUTO-CHAIN-MONITOR-RETIREMENT"
    },
    @{
      Name = "public-identity-consumer-inventory-required"
      Literal = "Dependency-surface inventory"
    }
  )) {
  if (-not $coordinatorPolicy.Contains($policyCase.Literal)) {
    Fail "$($policyCase.Name) missing policy anchor '$($policyCase.Literal)'"
  }
  Write-Host "WORKER-PROMPT-REGRESSION: PASS $($policyCase.Name)"
}

$tempRoot = Join-Path ([IO.Path]::GetTempPath()) ("rmq-worker-prompt-" + [guid]::NewGuid().ToString("N"))
New-Item -ItemType Directory -Path $tempRoot | Out-Null
$oldGitConfigGlobal = $env:GIT_CONFIG_GLOBAL
$oldGitConfigCount = $env:GIT_CONFIG_COUNT
$oldGitConfigKey0 = $env:GIT_CONFIG_KEY_0
$oldGitConfigValue0 = $env:GIT_CONFIG_VALUE_0
$tempExcludesFile = Join-Path $tempRoot ".gitignore-global"
New-Item -ItemType File -Path $tempExcludesFile | Out-Null
$env:GIT_CONFIG_GLOBAL = "NUL"
$env:GIT_CONFIG_COUNT = "1"
$env:GIT_CONFIG_KEY_0 = "core.excludesFile"
$env:GIT_CONFIG_VALUE_0 = $tempExcludesFile

try {
  & git -C $tempRoot init --quiet
  if ($LASTEXITCODE -ne 0) { Fail "could not initialize fixture repository" }
  & git -C $tempRoot config user.email "rmq-worker-prompt@example.invalid"
  & git -C $tempRoot config user.name "RMQ Worker Prompt"

  "root" | Set-Content -LiteralPath (Join-Path $tempRoot "root.txt") -Encoding utf8
  & git -C $tempRoot add root.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "fixture root"
  $rootRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  & git -C $tempRoot switch --quiet -c stale-base
  "stale" | Set-Content -LiteralPath (Join-Path $tempRoot "stale.txt") -Encoding utf8
  & git -C $tempRoot add stale.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "stale worker base"
  $staleRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  & git -C $tempRoot switch --quiet -c governance $rootRef
  "policy" | Set-Content -LiteralPath (Join-Path $tempRoot "policy.txt") -Encoding utf8
  New-Item -ItemType Directory -Force -Path (Join-Path $tempRoot "docs\internal") | Out-Null
  New-Item -ItemType Directory -Force -Path (Join-Path $tempRoot "artifact") | Out-Null
  '{"currentFactSurfacePathRegex":"^(?:README\\.md|artifact/CLAIMS\\.md)$"}' |
    Set-Content -LiteralPath (Join-Path $tempRoot "docs\internal\CLAIM_DRIFT_POLICY.json") -Encoding utf8
  "current reader" | Set-Content -LiteralPath (Join-Path $tempRoot "README.md") -Encoding utf8
  "current artifact" | Set-Content -LiteralPath (Join-Path $tempRoot "artifact\CLAIMS.md") -Encoding utf8
  & git -C $tempRoot add policy.txt README.md artifact/CLAIMS.md docs/internal/CLAIM_DRIFT_POLICY.json
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "governance"
  $governanceRef = (& git -C $tempRoot rev-parse HEAD).Trim()

  "worker" | Set-Content -LiteralPath (Join-Path $tempRoot "worker.txt") -Encoding utf8
  & git -C $tempRoot add worker.txt
  & git -C $tempRoot -c commit.gpgSign=false commit --quiet -m "governed worker base"
  $workerBase = (& git -C $tempRoot rev-parse HEAD).Trim()

  $validPrompt = Join-Path $tempRoot "valid-prompt.txt"
  Write-Prompt $validPrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair"
  Invoke-Case "ready-governed" 0 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("WORKER-PROMPT-PREFLIGHT: PASS")

  $gateWithoutDecisionScope = Join-Path $tempRoot "gate-without-workflow-decision-scope.txt"
  $gateWithoutDecisionScopeLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- Write scope:') {
      '- Write scope: E1 source, scripts/gate.ps1, its matrix, and directly required checks.'
    } else {
      $_
    }
  }
  $gateWithoutDecisionScopeLines += '- Outside-scope dependency note: docs/internal/WORKFLOW_DESIGN_DECISIONS.md exists but is not owned.'
  $gateWithoutDecisionScopeLines += '- powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict'
  $gateWithoutDecisionScopeLines | Set-Content -LiteralPath $gateWithoutDecisionScope -Encoding utf8
  Invoke-Case "gate-strict-wdd-outside-write-scope-rejected" 2 `
    $gateWithoutDecisionScope $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("workflow-sensitive-write-scope-requires-wdd")

  $gateWithDecisionScope = Join-Path $tempRoot "gate-with-workflow-decision-scope.txt"
  $gateWithDecisionScopeLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- Write scope:') {
      '- Write scope: E1 source, scripts/gate.ps1, docs/internal/WORKFLOW_DESIGN_DECISIONS.md, its matrix, and directly required checks.'
    } else {
      $_
    }
  }
  $gateWithDecisionScopeLines += '- powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict'
  $gateWithDecisionScopeLines | Set-Content -LiteralPath $gateWithDecisionScope -Encoding utf8
  Invoke-Case "gate-strict-wdd-in-write-scope-accepted" 0 `
    $gateWithDecisionScope $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("WORKER-PROMPT-PREFLIGHT: PASS")

  $currentSurfaceWithoutRegistry = Join-Path $tempRoot "current-surface-without-registry.txt"
  $currentSurfaceWithoutRegistryLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- Frozen acceptance IDs:') {
      '- Frozen acceptance IDs: REQ-R1R2-CURRENT-SURFACE-SYNC, INV-CATEGORY-SEPARATION, CHK-DIFF.'
    } else {
      $_
    }
  }
  $currentSurfaceWithoutRegistryLines | Set-Content -LiteralPath $currentSurfaceWithoutRegistry -Encoding utf8
  Invoke-Case "current-surface-sync-without-policy-registry-rejected" 2 `
    $currentSurfaceWithoutRegistry $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("exhaustive-current-surface-sync-requires-policy-registry")

  $governedCurrentSurfaceWithoutRegistry = Join-Path $tempRoot "governed-current-surface-without-registry.txt"
  $governedCurrentSurfaceWithoutRegistryLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- Frozen acceptance IDs:') {
      '- Frozen acceptance IDs: REQ-B7R1-CURRENT-PUBLIC-SURFACES, INV-CATEGORY-SEPARATION, CHK-DIFF.'
    } else {
      $_
    }
  }
  $governedCurrentSurfaceWithoutRegistryLines += '- Synchronize every governed current surface to the exact live cost and theorem identity.'
  $governedCurrentSurfaceWithoutRegistryLines | Set-Content -LiteralPath $governedCurrentSurfaceWithoutRegistry -Encoding utf8
  Invoke-Case "b7-governed-current-surface-wording-without-inventory-rejected" 2 `
    $governedCurrentSurfaceWithoutRegistry $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("exhaustive-current-surface-sync-requires-policy-registry")

  $currentSurfaceWithBareRegistry = Join-Path $tempRoot "current-surface-with-bare-registry.txt"
  $currentSurfaceWithBareRegistryLines = @($currentSurfaceWithoutRegistryLines) + @(
    '- Current-surface inventory: registry=docs/internal/CLAIM_DRIFT_POLICY.json; field=currentFactSurfacePathRegex.'
  )
  $currentSurfaceWithBareRegistryLines | Set-Content -LiteralPath $currentSurfaceWithBareRegistry -Encoding utf8
  Invoke-Case "current-surface-sync-unattested-inventory-rejected" 2 `
    $currentSurfaceWithBareRegistry $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("exhaustive-current-surface-sync-requires-attested-inventory")

  $currentSurfaceRepairOutsideScope = Join-Path $tempRoot "current-surface-repair-outside-scope.txt"
  $currentSurfaceRepairOutsideScopeLines = @($currentSurfaceWithoutRegistryLines) + @(
    '- Current-surface inventory: registry=docs/internal/CLAIM_DRIFT_POLICY.json; field=currentFactSurfacePathRegex; matched_count=2; inspected_paths=README.md,artifact/CLAIMS.md; expected_repair_paths=artifact/CLAIMS.md'
  )
  $currentSurfaceRepairOutsideScopeLines | Set-Content -LiteralPath $currentSurfaceRepairOutsideScope -Encoding utf8
  Invoke-Case "current-surface-sync-repair-outside-write-scope-rejected" 2 `
    $currentSurfaceRepairOutsideScope $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("exhaustive-current-surface-sync-repair-outside-write-scope")

  $currentSurfaceWithRegistry = Join-Path $tempRoot "current-surface-with-registry.txt"
  $currentSurfaceWithRegistryLines = @($currentSurfaceRepairOutsideScopeLines) | ForEach-Object {
    if ($_ -match '^- Write scope:') {
      '- Write scope: E1 source, artifact/CLAIMS.md, its matrix, and directly required checks.'
    } else {
      $_
    }
  }
  $currentSurfaceWithRegistryLines | Set-Content -LiteralPath $currentSurfaceWithRegistry -Encoding utf8
  Invoke-Case "current-surface-sync-with-attested-policy-registry-accepted" 0 `
    $currentSurfaceWithRegistry $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("WORKER-PROMPT-PREFLIGHT: PASS")

  $identityWithoutConsumers = Join-Path $tempRoot "identity-without-consumers.txt"
  $identityWithoutConsumersLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- Frozen acceptance IDs:') {
      '- Frozen acceptance IDs: REQ-B7R1-HISTORICAL-328-IDENTITY, INV-CATEGORY-SEPARATION, CHK-DIFF.'
    } else {
      $_
    }
  }
  $identityWithoutConsumersLines += '- Restore and pin the public historical identity while separating the live bound.'
  $identityWithoutConsumersLines | Set-Content -LiteralPath $identityWithoutConsumers -Encoding utf8
  Invoke-Case "b7r2-public-identity-migration-without-consumer-inventory-rejected" 2 `
    $identityWithoutConsumers $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("public-identity-migration-requires-consumer-inventory")

  $identityWithConsumers = Join-Path $tempRoot "identity-with-consumers.txt"
  $identityWithConsumersLines = @($identityWithoutConsumersLines) | ForEach-Object {
    if ($_ -match '^- Write scope:') {
      '- Write scope: E1 source, README.md, its matrix, and directly required checks.'
    } else {
      $_
    }
  }
  $identityWithConsumersLines += '- Dependency-surface inventory: searched_symbols=Example.publicHistoricalIdentity; inspected_consumer_paths=README.md; expected_repair_paths=README.md'
  $identityWithConsumersLines | Set-Content -LiteralPath $identityWithConsumers -Encoding utf8
  Invoke-Case "public-identity-migration-with-closed-consumer-inventory-accepted" 0 `
    $identityWithConsumers $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("WORKER-PROMPT-PREFLIGHT: PASS")

  Invoke-Case "returning-runtime-unknown" 2 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("destination runtime VERIFIED_CURRENT") `
    -DestinationRuntimeEvidence "UNKNOWN"

  $freshPrompt = Join-Path $tempRoot "fresh-governed.txt"
  @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    $_ -replace '^- Fresh or returning worker: RETURNING',
      '- Fresh or returning worker: FRESH'
  } | Set-Content -LiteralPath $freshPrompt -Encoding utf8
  Invoke-Case "fresh-governed-start" 0 $freshPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("destination_task=FRESH_GOVERNED_WORKTREE", "PASS") `
    -DestinationTaskKind "FRESH_GOVERNED_WORKTREE" `
    -DestinationRuntimeEvidence "GOVERNED_START"
  Invoke-Case "fresh-runtime-unknown" 2 $freshPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("destination runtime evidence GOVERNED_START") `
    -DestinationTaskKind "FRESH_GOVERNED_WORKTREE" `
    -DestinationRuntimeEvidence "UNKNOWN"

  $skeletalPrompt = Join-Path $tempRoot "skeletal-prompt.txt"
  @(
    "Make the title of this chat exactly: (E1-01R1) Repair the machine"
    "Use `$rmq-proof-sprint before starting."
    "Workflow-governance ref: $governanceRef"
    "Exact base: $workerBase"
    "Create branch exactly codex/e1-repair"
    "Status: CANDIDATE_COMPLETE"
    "coordinator acceptance is still required"
  ) | Set-Content -LiteralPath $skeletalPrompt -Encoding utf8
  Invoke-Case "skeletal-prompt" 2 $skeletalPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("missing required populated section")

  $trivialPrompt = Join-Path $tempRoot "trivial-fields.txt"
  $trivialLines = @(Get-Content -LiteralPath $validPrompt) | ForEach-Object {
    if ($_ -match '^- (Node/join|Local owned rung|Roadmap-node closure condition|Goal|Required theorem/file/tool|Write scope|Non-goals|Frozen acceptance IDs):') {
      ($_ -replace ':.*$', ': x.')
    } else {
      $_
    }
  }
  $trivialLines | Set-Content -LiteralPath $trivialPrompt -Encoding utf8
  Invoke-Case "trivial-fields" 2 $trivialPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("not substantively populated")

  $metadataTitle = Join-Path $tempRoot "metadata-title.txt"
  Write-Prompt $metadataTitle "Title: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair"
  Invoke-Case "title-metadata-only" 2 $metadataTitle $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("first line must be exactly")

  $stalePrompt = Join-Path $tempRoot "stale-base.txt"
  Write-Prompt $stalePrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $staleRef "codex/e1-repair"
  Invoke-Case "stale-worker-base" 2 $stalePrompt $governanceRef $staleRef `
    "READY_TO_SEND" "COMPLETE" @("does not contain governance")

  Invoke-Case "ready-feedback-pending" 2 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "PENDING" @("READY_TO_SEND requires failure-mode feedback")

  Invoke-Case "ready-semantic-review-pending" 2 $validPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("semantic-contract review COMPLETE") -SemanticReview "PENDING"

  foreach ($replayContract in @(
      @{ Name = "m1r3-exact-registry-omitted"; Literal = "REPLAY-EXACT-REGISTRY" },
      @{ Name = "m1r3-zero-case-selector"; Literal = "REPLAY-SELECTOR-NONVACUITY" },
      @{ Name = "m1r3-unbounded-subprocess"; Literal = "REPLAY-SUBPROCESS-DEADLINE" }
    )) {
    $missingReplayContract = Join-Path $tempRoot ($replayContract.Name + ".txt")
    @(Get-Content -LiteralPath $validPrompt) | Where-Object {
      -not $_.Contains($replayContract.Literal)
    } | Set-Content -LiteralPath $missingReplayContract -Encoding utf8
    Invoke-Case $replayContract.Name 2 $missingReplayContract $governanceRef $workerBase `
      "READY_TO_SEND" "COMPLETE" @("missing replay-harness contract '$($replayContract.Literal)'")
  }

  Invoke-Case "draft-feedback-pending" 0 $validPrompt $governanceRef $workerBase `
    "DRAFT_DO_NOT_SEND" "PENDING" @("status=DRAFT_DO_NOT_SEND", "PASS")

  $placeholderPrompt = Join-Path $tempRoot "placeholder.txt"
  Write-Prompt $placeholderPrompt "Make the title of this chat exactly: (E1-01R1) Repair the machine" `
    $governanceRef $workerBase "codex/e1-repair" @("Write scope: [PATHS]")
  Invoke-Case "template-placeholder" 2 $placeholderPrompt $governanceRef $workerBase `
    "READY_TO_SEND" "COMPLETE" @("template placeholder")

  Write-Host "WORKER-PROMPT-REGRESSION: PASS all cases"
  exit 0
} finally {
  if ($null -eq $oldGitConfigGlobal) {
    Remove-Item Env:GIT_CONFIG_GLOBAL -ErrorAction SilentlyContinue
  } else {
    $env:GIT_CONFIG_GLOBAL = $oldGitConfigGlobal
  }
  foreach ($entry in @(
    @{ Name = "GIT_CONFIG_COUNT"; Value = $oldGitConfigCount },
    @{ Name = "GIT_CONFIG_KEY_0"; Value = $oldGitConfigKey0 },
    @{ Name = "GIT_CONFIG_VALUE_0"; Value = $oldGitConfigValue0 }
  )) {
    if ($null -eq $entry.Value) {
      Remove-Item "Env:$($entry.Name)" -ErrorAction SilentlyContinue
    } else {
      Set-Item "Env:$($entry.Name)" $entry.Value
    }
  }
  Remove-Item -LiteralPath $tempRoot -Recurse -Force -ErrorAction SilentlyContinue
}

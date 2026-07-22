#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [Parameter(Mandatory = $true)]
  [string]$PromptPath,

  [Parameter(Mandatory = $true)]
  [string]$GovernanceRef,

  [Parameter(Mandatory = $true)]
  [string]$WorkerBase,

  [Parameter(Mandatory = $true)]
  [string]$WorkerHandle,

  [Parameter(Mandatory = $true)]
  [string]$RequestedTitle,

  [Parameter(Mandatory = $true)]
  [string]$RequiredSkill,

  [Parameter(Mandatory = $true)]
  [ValidateSet("READY_TO_SEND", "DRAFT_DO_NOT_SEND")]
  [string]$PromptStatus,

  [Parameter(Mandatory = $true)]
  [ValidateSet("COMPLETE", "PENDING", "NOT_APPLICABLE")]
  [string]$FailureModeFeedbackStatus,

  [Parameter(Mandatory = $true)]
  [ValidateSet("COMPLETE", "PENDING")]
  [string]$SemanticContractReviewStatus,

  [Parameter(Mandatory = $true)]
  [ValidateSet("RETURNING_TASK", "FRESH_GOVERNED_WORKTREE")]
  [string]$DestinationTaskKind,

  [Parameter(Mandatory = $true)]
  [ValidateSet("VERIFIED_CURRENT", "GOVERNED_START", "UNKNOWN", "STALE")]
  [string]$DestinationRuntimeEvidence,

  [ValidateSet("WRITE", "READ_ONLY")]
  [string]$TaskMode = "WRITE",

  [switch]$AutomatedCompletionLoop,

  [string]$WorkerBranch = "",

  [string]$RepositoryRoot
)

$ErrorActionPreference = "Stop"

function Stop-Preflight([string]$Message) {
  Write-Host "WORKER-PROMPT-PREFLIGHT: ERROR $Message"
  exit 2
}

function Invoke-Git([string[]]$Arguments) {
  $output = @(& git -C $script:RepositoryRoot @Arguments 2>&1)
  if ($LASTEXITCODE -ne 0) {
    throw "git $($Arguments -join ' ') failed:`n$($output -join [Environment]::NewLine)"
  }
  return $output
}

try {
  if (-not $RepositoryRoot) {
    $RepositoryRoot = (& git rev-parse --show-toplevel 2>&1).Trim()
    if ($LASTEXITCODE -ne 0) { Stop-Preflight "not inside a Git repository" }
  }
  $RepositoryRoot = (Resolve-Path -LiteralPath $RepositoryRoot).Path
  $PromptPath = (Resolve-Path -LiteralPath $PromptPath).Path

  if ($GovernanceRef -notmatch '^[0-9a-fA-F]{40}$') {
    Stop-Preflight "governance ref must be an exact 40-character commit SHA"
  }
  if ($WorkerBase -notmatch '^[0-9a-fA-F]{40}$') {
    Stop-Preflight "worker base must be an exact 40-character commit SHA"
  }
  if ($RequestedTitle -notmatch "^\($([regex]::Escape($WorkerHandle))\) .+") {
    Stop-Preflight "requested title must begin with ($WorkerHandle) followed by a task summary"
  }

  $governanceSha = (@(Invoke-Git @("rev-parse", "${GovernanceRef}^{commit}")))[0].Trim()
  $workerBaseSha = (@(Invoke-Git @("rev-parse", "${WorkerBase}^{commit}")))[0].Trim()
  if ($governanceSha -ne $GovernanceRef.ToLowerInvariant()) {
    Stop-Preflight "governance ref did not resolve to the supplied exact SHA"
  }
  if ($workerBaseSha -ne $WorkerBase.ToLowerInvariant()) {
    Stop-Preflight "worker base did not resolve to the supplied exact SHA"
  }

  & git -C $RepositoryRoot merge-base --is-ancestor $governanceSha $workerBaseSha 2>$null
  if ($LASTEXITCODE -ne 0) {
    Stop-Preflight "worker base $workerBaseSha does not contain governance $governanceSha"
  }

  $lines = @(Get-Content -LiteralPath $PromptPath)
  if ($lines.Count -eq 0) { Stop-Preflight "prompt file is empty" }
  $firstLine = $lines[0].TrimStart([char]0xfeff)
  $expectedFirstLine = "Make the title of this chat exactly: $RequestedTitle"
  if ($firstLine -cne $expectedFirstLine) {
    Stop-Preflight "first line must be exactly '$expectedFirstLine'"
  }

  $promptText = $lines -join [Environment]::NewLine
  foreach ($requiredLiteral in @($governanceSha, $workerBaseSha, "Use `$$RequiredSkill")) {
    if (-not $promptText.Contains($requiredLiteral)) {
      Stop-Preflight "prompt does not contain required literal '$requiredLiteral'"
    }
  }

  $requiredSections = @(
    "Worker identity:",
    "Skill:",
    "Checkout contract:",
    "Roadmap contract:",
    "Acceptance contract:",
    "Forbidden shortcuts:",
    "Context:",
    "Completion:",
    "Verification:",
    "Report:"
  )
  foreach ($section in $requiredSections) {
    if (-not [regex]::IsMatch(
        $promptText,
        "(?m)^$([regex]::Escape($section))\s*$"
      )) {
      Stop-Preflight "prompt is missing required populated section '$section'"
    }
  }

  $requiredFields = @(
    @{ Pattern = "(?m)^- Handle:\s*$([regex]::Escape($WorkerHandle))\s*$"; Name = "worker handle" },
    @{ Pattern = "(?m)^- Fresh or returning worker:\s*(FRESH|RETURNING)\b.+$"; Name = "fresh/returning worker disposition" },
    @{ Pattern = "(?m)^- Task mode:\s*$([regex]::Escape($TaskMode))\b.*$"; Name = "task mode" },
    @{ Pattern = "(?m)^- Exact base/target commit:\s*$([regex]::Escape($workerBaseSha))\b.*$"; Name = "exact base field" },
    @{ Pattern = "(?m)^- Node/join:\s*\S.+$"; Name = "roadmap node/join" },
    @{ Pattern = "(?m)^- Local owned rung:\s*\S.+$"; Name = "local owned rung" },
    @{ Pattern = "(?m)^- Roadmap-node closure condition:\s*\S.+$"; Name = "roadmap closure condition" },
    @{ Pattern = "(?m)^- Goal:\s*\S.+$"; Name = "exact goal" },
    @{ Pattern = "(?m)^- Required theorem/file/tool:\s*\S.+$"; Name = "required target" },
    @{ Pattern = "(?m)^- Write scope:\s*\S.+$"; Name = "write scope" },
    @{ Pattern = "(?m)^- Non-goals:\s*\S.+$"; Name = "non-goals" },
    @{ Pattern = "(?m)^- Frozen acceptance IDs:\s*\S.+$"; Name = "frozen acceptance IDs" }
  )
  foreach ($field in $requiredFields) {
    if (-not [regex]::IsMatch($promptText, $field.Pattern)) {
      Stop-Preflight "prompt is missing populated $($field.Name)"
    }
  }

  $dispositionMatch = [regex]::Match(
    $promptText,
    '(?m)^- Fresh or returning worker:\s*(FRESH|RETURNING)\b'
  )
  $expectedDisposition = if ($DestinationTaskKind -eq "RETURNING_TASK") {
    "RETURNING"
  } else {
    "FRESH"
  }
  if ($dispositionMatch.Groups[1].Value -ne $expectedDisposition) {
    Stop-Preflight "prompt worker disposition does not match destination task kind $DestinationTaskKind"
  }

  $substantiveFields = @(
    @{ Label = "- Fresh or returning worker:"; MinLength = 24 },
    @{ Label = "- Node/join:"; MinLength = 24 },
    @{ Label = "- Local owned rung:"; MinLength = 24 },
    @{ Label = "- Roadmap-node closure condition:"; MinLength = 24 },
    @{ Label = "- Goal:"; MinLength = 24 },
    @{ Label = "- Required theorem/file/tool:"; MinLength = 24 },
    @{ Label = "- Write scope:"; MinLength = 24 },
    @{ Label = "- Non-goals:"; MinLength = 16 },
    @{ Label = "- Frozen acceptance IDs:"; MinLength = 12 }
  )
  foreach ($field in $substantiveFields) {
    $match = [regex]::Match(
      $promptText,
      "(?m)^$([regex]::Escape($field.Label))\s*(.+?)\s*$"
    )
    if (-not $match.Success) {
      Stop-Preflight "prompt is missing $($field.Label)"
    }
    $value = $match.Groups[1].Value.Trim()
    if ($value.Length -lt $field.MinLength -or $value -match '^[xX. _-]+$') {
      Stop-Preflight "prompt field '$($field.Label)' is not substantively populated"
    }
  }

  if ($AutomatedCompletionLoop -and $TaskMode -eq "READ_ONLY") {
    $durableArtifact = [regex]::Match(
      $promptText,
      '(?m)^- Durable completion artifact:\s*mode=WORKER_REPORT;\s*path=(\S.+?)\s*$'
    )
    if (-not $durableArtifact.Success) {
      Stop-Preflight "AUTO-CHAIN-DURABLE-TERMINAL-ARTIFACT requires a read-only WORKER_REPORT at one exact path"
    }
    $durablePath = $durableArtifact.Groups[1].Value.Trim()
    if ($durablePath -match '(?i)\b(this|the)\s+(task|chat|thread)\b' -or
        $durablePath -notmatch '(?i)\.(md|txt|json|csv|lean)$') {
      Stop-Preflight "AUTO-CHAIN-DURABLE-TERMINAL-ARTIFACT requires an exact file path with a durable extension"
    }
  }

  $writeScopeLine = [regex]::Match(
    $promptText,
    '(?m)^- Write scope:\s*(.+?)\s*$'
  ).Groups[1].Value
  if ($TaskMode -eq "WRITE" -and
      $writeScopeLine -match 'scripts[\\/]gate\.ps1' -and
      $writeScopeLine -notmatch 'docs[\\/]internal[\\/]WORKFLOW_DESIGN_DECISIONS\.md') {
    Stop-Preflight "workflow-sensitive-write-scope-requires-wdd: scripts/gate.ps1 requires docs/internal/WORKFLOW_DESIGN_DECISIONS.md in the same write scope"
  }

  $isCurrentSurfaceSync =
    $promptText -match '(?i)(?:CURRENT-SURFACE-SYNC|CURRENT-PUBLIC-SURFACES|currentFactSurfacePathRegex|every\s+(?:(?:registered|governed|live|current|public|documentation)\s+){0,5}surface|every\s+surface\s+registered)'
  if ($isCurrentSurfaceSync) {
    $inventoryMatch = [regex]::Match(
      $promptText,
      '(?m)^- Current-surface inventory:\s*(.+?)\s*$'
    )
    if (-not $inventoryMatch.Success -or
        $inventoryMatch.Groups[1].Value -notmatch 'registry=docs/internal/CLAIM_DRIFT_POLICY\.json' -or
        $inventoryMatch.Groups[1].Value -notmatch 'field=currentFactSurfacePathRegex') {
      Stop-Preflight "exhaustive-current-surface-sync-requires-policy-registry: name docs/internal/CLAIM_DRIFT_POLICY.json currentFactSurfacePathRegex"
    }

    $inventoryValue = $inventoryMatch.Groups[1].Value
    $countMatch = [regex]::Match($inventoryValue, '(?:^|;)\s*matched_count=(\d+)\s*(?:;|$)')
    $inspectedMatch = [regex]::Match($inventoryValue, '(?:^|;)\s*inspected_paths=([^;]+)')
    $repairMatch = [regex]::Match($inventoryValue, '(?:^|;)\s*expected_repair_paths=([^;]+)')
    if (-not $countMatch.Success -or -not $inspectedMatch.Success -or -not $repairMatch.Success) {
      Stop-Preflight "exhaustive-current-surface-sync-requires-attested-inventory: matched_count, inspected_paths, and expected_repair_paths are required"
    }

    $policyText = @(Invoke-Git @(
        "show",
        "${workerBaseSha}:docs/internal/CLAIM_DRIFT_POLICY.json"
      )) -join [Environment]::NewLine
    try {
      $currentSurfacePolicy = $policyText | ConvertFrom-Json
      $currentSurfaceRegex = [string]$currentSurfacePolicy.currentFactSurfacePathRegex
      if ([string]::IsNullOrWhiteSpace($currentSurfaceRegex)) {
        throw "currentFactSurfacePathRegex is empty"
      }
      $null = [regex]::new($currentSurfaceRegex)
    } catch {
      Stop-Preflight "worker-base current-surface registry is unreadable: $($_.Exception.Message)"
    }

    $matchedCurrentPaths = @(
      Invoke-Git @("ls-tree", "-r", "--name-only", $workerBaseSha) |
        ForEach-Object { $_.Trim().Replace('\', '/') } |
        Where-Object { [regex]::IsMatch($_, $currentSurfaceRegex) } |
        Sort-Object -Unique
    )
    $declaredCount = [int]$countMatch.Groups[1].Value
    if ($declaredCount -ne $matchedCurrentPaths.Count) {
      Stop-Preflight "exhaustive-current-surface-sync-count-mismatch: declared $declaredCount, exact base has $($matchedCurrentPaths.Count)"
    }

    $inspectedPaths = @(
      $inspectedMatch.Groups[1].Value -split ',' |
        ForEach-Object { $_.Trim().Replace('\', '/') } |
        Where-Object { $_ }
    )
    if ($inspectedPaths.Count -ne @($inspectedPaths | Sort-Object -Unique).Count -or
        @(Compare-Object -ReferenceObject $matchedCurrentPaths -DifferenceObject @($inspectedPaths | Sort-Object -Unique)).Count -ne 0) {
      Stop-Preflight "exhaustive-current-surface-sync-path-set-mismatch: inspected_paths must equal the exact registry match set"
    }

    $repairPaths = @()
    if ($repairMatch.Groups[1].Value.Trim() -ne 'NONE') {
      $repairPaths = @(
        $repairMatch.Groups[1].Value -split ',' |
          ForEach-Object { $_.Trim().Replace('\', '/') } |
          Where-Object { $_ } |
          Sort-Object -Unique
      )
    }
    foreach ($repairPath in $repairPaths) {
      if ($repairPath -notin $matchedCurrentPaths) {
        Stop-Preflight "exhaustive-current-surface-sync-repair-not-registered: $repairPath"
      }
      if (-not $writeScopeLine.Contains($repairPath)) {
        Stop-Preflight "exhaustive-current-surface-sync-repair-outside-write-scope: $repairPath"
      }
    }
  }

  $isPublicIdentityMigration =
    $promptText -match '(?i)(?:HISTORICAL-[A-Z0-9-]+-IDENTITY|restore(?:\s+and)?\s+pin\s+(?:the\s+)?public\s+(?:historical\s+)?identity|(?:restore|rename|split|migrate|migration).{0,100}(?:public\s+theorem|historical\s+identity))'
  if ($isPublicIdentityMigration) {
    $dependencyMatch = [regex]::Match(
      $promptText,
      '(?m)^- Dependency-surface inventory:\s*(.+?)\s*$'
    )
    if (-not $dependencyMatch.Success) {
      Stop-Preflight "public-identity-migration-requires-consumer-inventory: searched_symbols, inspected_consumer_paths, and expected_repair_paths are required"
    }

    $dependencyValue = $dependencyMatch.Groups[1].Value
    $symbolsMatch = [regex]::Match($dependencyValue, '(?:^|;)\s*searched_symbols=([^;]+)')
    $consumersMatch = [regex]::Match($dependencyValue, '(?:^|;)\s*inspected_consumer_paths=([^;]+)')
    $dependencyRepairMatch = [regex]::Match($dependencyValue, '(?:^|;)\s*expected_repair_paths=([^;]+)')
    if (-not $symbolsMatch.Success -or -not $consumersMatch.Success -or
        -not $dependencyRepairMatch.Success) {
      Stop-Preflight "public-identity-migration-requires-attested-consumer-inventory: searched_symbols, inspected_consumer_paths, and expected_repair_paths are required"
    }

    $consumerPaths = @(
      $consumersMatch.Groups[1].Value -split ',' |
        ForEach-Object { $_.Trim().Replace('\', '/') } |
        Where-Object { $_ } |
        Sort-Object -Unique
    )
    if ($consumerPaths.Count -eq 0) {
      Stop-Preflight "public-identity-migration-requires-attested-consumer-inventory: inspected_consumer_paths is empty"
    }

    $dependencyRepairPaths = @()
    if ($dependencyRepairMatch.Groups[1].Value.Trim() -ne 'NONE') {
      $dependencyRepairPaths = @(
        $dependencyRepairMatch.Groups[1].Value -split ',' |
          ForEach-Object { $_.Trim().Replace('\', '/') } |
          Where-Object { $_ } |
          Sort-Object -Unique
      )
    }
    foreach ($repairPath in $dependencyRepairPaths) {
      if ($repairPath -notin $consumerPaths) {
        Stop-Preflight "public-identity-migration-repair-not-inspected: $repairPath"
      }
      if (-not $writeScopeLine.Contains($repairPath)) {
        Stop-Preflight "public-identity-migration-repair-outside-write-scope: $repairPath"
      }
    }
  }

  $acceptanceLine = [regex]::Match(
    $promptText,
    '(?m)^- Frozen acceptance IDs:\s*(.+?)\s*$'
  ).Groups[1].Value
  if ($acceptanceLine -notmatch '\b(?:INV|REQ|CHK|E1|M1|ROADMAP|GOAL|FORBID|COMPLETE|REPORT)-[A-Z0-9]') {
    Stop-Preflight "frozen acceptance field contains no stable acceptance ID"
  }

  foreach ($reportLiteral in @(
      "Status: CANDIDATE_COMPLETE",
      "coordinator acceptance is still required"
    )) {
    if (-not $promptText.Contains($reportLiteral)) {
      Stop-Preflight "prompt report contract is missing '$reportLiteral'"
    }
  }

  foreach ($replayContractLiteral in @(
      "REPLAY-EXACT-REGISTRY",
      "REPLAY-SELECTOR-NONVACUITY",
      "REPLAY-SUBPROCESS-DEADLINE"
    )) {
    if (-not $promptText.Contains($replayContractLiteral)) {
      Stop-Preflight "prompt is missing replay-harness contract '$replayContractLiteral'"
    }
  }

  if ($TaskMode -eq "WRITE") {
    if ([string]::IsNullOrWhiteSpace($WorkerBranch)) {
      Stop-Preflight "write prompt requires an exact worker branch"
    }
    if (-not $promptText.Contains($WorkerBranch)) {
      Stop-Preflight "prompt does not contain worker branch '$WorkerBranch'"
    }
    $rangeCheck = "git diff --check $workerBaseSha..HEAD"
    if (-not $promptText.Contains($rangeCheck)) {
      Stop-Preflight "write prompt is missing committed-range check '$rangeCheck'"
    }
  }

  $placeholderPattern = '\[(WORKER_HANDLE|SHORT_TASK_SUMMARY|SKILL_NAME|EXACT[^]]*|BASE_BRANCH_OR_COMMIT|WORKER_BRANCH|ROADMAP_NODE_AND_CONSUMER|ONE SENTENCE EXACT TARGET|TARGETED BUILD/CHECKS|PATHS|BOUNDARIES|ITEMS|FRESH / RETURNING[^]]*|WRITE / READ-ONLY|REPORT PATH / COORDINATOR SYNTHESIS TARGET|WHAT MUST HOLD[^]]*|LOCAL RUNG / ENTIRE ROADMAP NODE|REQ-01[^]]*)\]'
  if ($promptText -match $placeholderPattern) {
    Stop-Preflight "prompt still contains template placeholder '$($Matches[0])'"
  }

  if ($PromptStatus -eq "READY_TO_SEND" -and
      $FailureModeFeedbackStatus -eq "PENDING") {
    Stop-Preflight "READY_TO_SEND requires failure-mode feedback COMPLETE or NOT_APPLICABLE"
  }
  if ($PromptStatus -eq "READY_TO_SEND" -and
      $SemanticContractReviewStatus -ne "COMPLETE") {
    Stop-Preflight "READY_TO_SEND requires semantic-contract review COMPLETE"
  }
  if ($PromptStatus -eq "READY_TO_SEND" -and
      $DestinationTaskKind -eq "RETURNING_TASK" -and
      $DestinationRuntimeEvidence -ne "VERIFIED_CURRENT") {
    Stop-Preflight "READY_TO_SEND returning task requires destination runtime VERIFIED_CURRENT"
  }
  if ($PromptStatus -eq "READY_TO_SEND" -and
      $DestinationTaskKind -eq "FRESH_GOVERNED_WORKTREE" -and
      $DestinationRuntimeEvidence -ne "GOVERNED_START") {
    Stop-Preflight "READY_TO_SEND fresh task requires destination runtime evidence GOVERNED_START"
  }

  Write-Host "WORKER-PROMPT-PREFLIGHT: status=$PromptStatus"
  Write-Host "WORKER-PROMPT-PREFLIGHT: governance=$governanceSha"
  Write-Host "WORKER-PROMPT-PREFLIGHT: worker_base=$workerBaseSha"
  Write-Host "WORKER-PROMPT-PREFLIGHT: worker=$WorkerHandle"
  Write-Host "WORKER-PROMPT-PREFLIGHT: feedback=$FailureModeFeedbackStatus"
  Write-Host "WORKER-PROMPT-PREFLIGHT: semantic_review=$SemanticContractReviewStatus"
  Write-Host "WORKER-PROMPT-PREFLIGHT: destination_task=$DestinationTaskKind"
  Write-Host "WORKER-PROMPT-PREFLIGHT: destination_runtime=$DestinationRuntimeEvidence"
  Write-Host "WORKER-PROMPT-PREFLIGHT: automated_completion=$($AutomatedCompletionLoop.IsPresent)"
  Write-Host "WORKER-PROMPT-PREFLIGHT: PASS"
  exit 0
} catch {
  Stop-Preflight $_.Exception.Message
}

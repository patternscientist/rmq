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
  Write-Host "WORKER-PROMPT-PREFLIGHT: PASS"
  exit 0
} catch {
  Stop-Preflight $_.Exception.Message
}

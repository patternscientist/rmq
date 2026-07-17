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

  if ($TaskMode -eq "WRITE") {
    if ([string]::IsNullOrWhiteSpace($WorkerBranch)) {
      Stop-Preflight "write prompt requires an exact worker branch"
    }
    if (-not $promptText.Contains($WorkerBranch)) {
      Stop-Preflight "prompt does not contain worker branch '$WorkerBranch'"
    }
  }

  $placeholderPattern = '\[(WORKER_HANDLE|SHORT_TASK_SUMMARY|SKILL_NAME|EXACT[^]]*|BASE_BRANCH_OR_COMMIT|WORKER_BRANCH|ROADMAP_NODE_AND_CONSUMER|ONE SENTENCE EXACT TARGET|TARGETED BUILD/CHECKS|PATHS|BOUNDARIES|ITEMS)\]'
  if ($promptText -match $placeholderPattern) {
    Stop-Preflight "prompt still contains template placeholder '$($Matches[0])'"
  }

  if ($PromptStatus -eq "READY_TO_SEND" -and
      $FailureModeFeedbackStatus -eq "PENDING") {
    Stop-Preflight "READY_TO_SEND requires failure-mode feedback COMPLETE or NOT_APPLICABLE"
  }

  Write-Host "WORKER-PROMPT-PREFLIGHT: status=$PromptStatus"
  Write-Host "WORKER-PROMPT-PREFLIGHT: governance=$governanceSha"
  Write-Host "WORKER-PROMPT-PREFLIGHT: worker_base=$workerBaseSha"
  Write-Host "WORKER-PROMPT-PREFLIGHT: worker=$WorkerHandle"
  Write-Host "WORKER-PROMPT-PREFLIGHT: feedback=$FailureModeFeedbackStatus"
  Write-Host "WORKER-PROMPT-PREFLIGHT: PASS"
  exit 0
} catch {
  Stop-Preflight $_.Exception.Message
}

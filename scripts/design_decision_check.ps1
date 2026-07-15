#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$Base = "",
  [switch]$Strict
)

$ErrorActionPreference = "Continue"

function Get-ChangedFiles {
  param([string]$BaseRef)

  $files = @()
  if ($BaseRef) {
    $files += @(& git diff --name-only $BaseRef -- 2>$null)
    if ($LASTEXITCODE -ne 0) {
      Write-Host "DESIGN-CHECK: could not diff against '$BaseRef'; falling back to worktree and index"
    }
  }

  if ($files.Count -eq 0) {
    $files += @(& git diff --name-only -- 2>$null)
    $files += @(& git diff --cached --name-only -- 2>$null)
  }

  $files += @(& git ls-files --others --exclude-standard 2>$null)

  return @($files | Where-Object { $_ } | Sort-Object -Unique)
}

function Any-Match {
  param(
    [string[]]$Files,
    [string[]]$Patterns
  )

  foreach ($file in $Files) {
    foreach ($pattern in $Patterns) {
      if ($file -match $pattern) {
        return $true
      }
    }
  }
  return $false
}

$files = Get-ChangedFiles -BaseRef $Base

if ($files.Count -eq 0) {
  Write-Host "DESIGN-CHECK: no changed files detected"
  exit 0
}

$codePatterns = @(
  "^RMQPaper\.lean$",
  "^RMQ/Headlines",
  "^RMQ/Core/SuccinctRMQClassic\.lean$",
  "^RMQ/Core/SuccinctFinal",
  "^RMQ/Core/SuccinctClose",
  "^RMQ/Core/WordRAM",
  "^artifact/",
  "^docs/digests/PROJECT_DIGESTION_CURRENT\.md$",
  "^docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY\.md$",
  "^docs/PUBLICATION_STRATEGY\.md$",
  "^docs/RELATED_WORK\.md$",
  "^docs/PAPER_",
  "^docs/WHAT_IS_PROVED\.md$",
  "^docs/FAMILY_SUMMARY\.md$",
  "^README\.md$"
)

$workflowPatterns = @(
  "^\.agents/skills/",
  "^AGENTS\.md$",
  "^docs/internal/AUDIT_PROTOCOL\.md$",
  "^docs/internal/ADD_WORKFLOW_TOOLING_PLAN\.md$",
  "^docs/internal/WORKFLOW_DESIGN_DECISIONS\.md$",
  "^docs/internal/RMQ_FINAL_ROADMAP\.md$",
  "^docs/internal/CLAIM_DRIFT_POLICY",
  "^docs/internal/PUBLICATION_DOCUMENT_ROLES\.json$",
  "^docs/internal/W22_U3_SEMANTIC_PUBLICATION_TOPOLOGY_ACCEPTANCE_MATRIX\.md$",
  "^docs/internal/templates/",
  "^scripts/make_audit_packet\.ps1$",
  "^scripts/claim_drift_scan\.ps1$",
  "^scripts/claim_drift_policy_regression\.ps1$",
  "^scripts/paper_topology_lint\.ps1$",
  "^scripts/paper_topology_lint_regression\.ps1$",
  "^scripts/gate\.ps1$",
  "^scripts/design_decision_check\.ps1$",
  "^\.github/"
)

$needsCodeDecision = Any-Match -Files $files -Patterns $codePatterns
$needsWorkflowDecision = Any-Match -Files $files -Patterns $workflowPatterns
$hasCodeDecision = $files -contains "docs/internal/DESIGN_DECISIONS.md"
$hasWorkflowDecision = $files -contains "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
$failures = 0

if ($needsCodeDecision -and -not $hasCodeDecision) {
  Write-Host "DESIGN-CHECK: proof/code/artifact-sensitive files changed; inspect docs/internal/DESIGN_DECISIONS.md"
  if ($Strict) { $failures += 1 }
}

if ($needsWorkflowDecision -and -not $hasWorkflowDecision) {
  Write-Host "DESIGN-CHECK: workflow/process-sensitive files changed; inspect docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
  if ($Strict) { $failures += 1 }
}

if (-not $needsCodeDecision -and -not $needsWorkflowDecision) {
  Write-Host "DESIGN-CHECK: no design-sensitive paths detected"
} else {
  Write-Host "DESIGN-CHECK: checked $($files.Count) changed files"
}

if ($failures -gt 0) {
  Write-Host "DESIGN-CHECK: strict mode found $failures missing design-log updates"
  exit 1
}

exit 0

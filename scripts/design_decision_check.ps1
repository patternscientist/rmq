#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$Base = "",
  [switch]$Strict
)

$ErrorActionPreference = "Continue"

function Stop-DesignCheck {
  param([string]$Message)

  Write-Host "DESIGN-CHECK: $Message"
  exit 1
}

$repositoryRoot = @(& git rev-parse --show-toplevel 2>$null)
if ($LASTEXITCODE -ne 0 -or $repositoryRoot.Count -ne 1) {
  Stop-DesignCheck "not inside a Git repository"
}
$repositoryRoot = [System.IO.Path]::GetFullPath([string]$repositoryRoot[0])
$pathComparison = if ($env:OS -eq "Windows_NT") {
  [System.StringComparison]::OrdinalIgnoreCase
} else {
  [System.StringComparison]::Ordinal
}

function ConvertTo-RepositoryPath {
  param([string]$Path)

  if ([string]::IsNullOrWhiteSpace($Path)) {
    return ""
  }

  try {
    if ([System.IO.Path]::IsPathRooted($Path)) {
      $fullPath = [System.IO.Path]::GetFullPath($Path)
      $rootWithSeparator = $repositoryRoot.TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar
      ) + [System.IO.Path]::DirectorySeparatorChar
      if ($fullPath.StartsWith($rootWithSeparator, $pathComparison)) {
        return ($fullPath.Substring($rootWithSeparator.Length) -replace "\\", "/")
      }
    }
  } catch {
    # Git normally returns repository-relative paths. Preserve unusual text so
    # the default-sensitive branch still fails closed.
  }

  $normalized = $Path -replace "\\", "/"
  while ($normalized.StartsWith("./", [System.StringComparison]::Ordinal)) {
    $normalized = $normalized.Substring(2)
  }
  return $normalized
}

function Resolve-BaseRef {
  param(
    [string]$BaseRef,
    [bool]$FailClosed
  )

  if ([string]::IsNullOrWhiteSpace($BaseRef)) {
    if ($FailClosed) {
      Stop-DesignCheck "strict certification requires -Base; refusing an implicit zero-change range"
    }
    return ""
  }

  $resolved = @(& git rev-parse --verify "$BaseRef^{commit}" 2>$null)
  if ($LASTEXITCODE -ne 0 -or $resolved.Count -ne 1) {
    if ($FailClosed) {
      Stop-DesignCheck "strict certification could not resolve base '$BaseRef'"
    }
    Write-Host "DESIGN-CHECK: could not resolve base '$BaseRef'; using non-strict local-worktree mode"
    return ""
  }
  return [string]$resolved[0]
}

function Get-ChangedFiles {
  param([string]$ResolvedBase)

  $files = @()
  if ($ResolvedBase) {
    $files += @(& git diff --name-only $ResolvedBase -- 2>$null)
    if ($LASTEXITCODE -ne 0) {
      Stop-DesignCheck "could not diff against resolved base '$ResolvedBase'"
    }
  } else {
    $files += @(& git diff --name-only -- 2>$null)
    if ($LASTEXITCODE -ne 0) {
      Stop-DesignCheck "could not inspect worktree changes"
    }
    $files += @(& git diff --cached --name-only -- 2>$null)
    if ($LASTEXITCODE -ne 0) {
      Stop-DesignCheck "could not inspect index changes"
    }
  }

  $files += @(& git ls-files --others --exclude-standard 2>$null)
  if ($LASTEXITCODE -ne 0) {
    Stop-DesignCheck "could not inspect untracked files"
  }

  return @(
    $files |
      ForEach-Object { ConvertTo-RepositoryPath -Path ([string]$_) } |
      Where-Object { $_ } |
      Sort-Object -Unique
  )
}

function Test-AnyPattern {
  param(
    [string]$Path,
    [string[]]$Patterns
  )

  foreach ($pattern in $Patterns) {
    if ($Path -match $pattern) {
      return $true
    }
  }
  return $false
}

# These are semantic opt-outs, not a remembered list of sensitive paths.
# Decision records do not recursively require themselves. Durable worklogs,
# acceptance matrices, audit reports, and historical digests are evidence
# about prior work rather than new proof/code or workflow design.
$neutralEvidencePatterns = @(
  "^docs/internal/(?:DESIGN_DECISIONS|WORKFLOW_DESIGN_DECISIONS)\.md$",
  "^docs/internal/audit_reports/[^/]+\.md$",
  "^docs/internal/[^/]*(?:_WORKLOG|_ACCEPTANCE_MATRIX|_AUDIT_REPORT)\.md$",
  "^docs/digests/(?![A-Z0-9_-]*CURRENT)[A-Z0-9][A-Z0-9_-]*_\d{4}_\d{2}_\d{2}\.md$",
  "^docs/digests/[A-Z0-9][A-Z0-9_-]*(?:HISTORY|LOG)\.md$",
  "^docs/DIGESTION_LOG\.md$"
)

# Workflow roots define process, automation, review, or repository operation.
# A Lean file remains code-sensitive as well, even if placed under one of these
# roots.
$workflowRootPatterns = @(
  "^\.agents/",
  "^\.codex/",
  "^\.github/",
  "^scripts/",
  "^AGENTS\.md$",
  "^docs/internal/"
)

$proofCodePattern = "(?i)\.lean$"
$workflowCodePattern = "(?i)\.(?:ps1|psm1|psd1|py|sh|bash|js|mjs|cjs|ts|tsx|jsx)$"

function Get-PathDisposition {
  param([string]$Path)

  # File identity is authoritative at a neutral boundary. A code-bearing file
  # cannot become evidence merely by moving under an audit, worklog, or digest
  # directory. Lean requires the code decision; script/program extensions
  # require the workflow decision even outside the ordinary workflow roots.
  $isProofCode = $Path -match $proofCodePattern
  $isWorkflowCode = $Path -match $workflowCodePattern
  if ($isProofCode -or $isWorkflowCode) {
    return [PSCustomObject]@{
      Path = $Path
      Neutral = $false
      NeedsCode = $isProofCode
      NeedsWorkflow = $isWorkflowCode -or
        (Test-AnyPattern -Path $Path -Patterns $workflowRootPatterns)
    }
  }

  if (Test-AnyPattern -Path $Path -Patterns $neutralEvidencePatterns) {
    return [PSCustomObject]@{
      Path = $Path
      Neutral = $true
      NeedsCode = $false
      NeedsWorkflow = $false
    }
  }

  $needsWorkflow = Test-AnyPattern -Path $Path -Patterns $workflowRootPatterns
  $needsCode = -not $needsWorkflow
  return [PSCustomObject]@{
    Path = $Path
    Neutral = $false
    NeedsCode = $needsCode
    NeedsWorkflow = $needsWorkflow
  }
}

$resolvedBase = Resolve-BaseRef -BaseRef $Base -FailClosed ([bool]$Strict)
$files = Get-ChangedFiles -ResolvedBase $resolvedBase

if ($files.Count -eq 0) {
  $range = if ($resolvedBase) { " relative to $resolvedBase" } else { "" }
  Write-Host "DESIGN-CHECK: no changed files detected$range"
  exit 0
}

$dispositions = @($files | ForEach-Object { Get-PathDisposition -Path $_ })
$codeSensitive = @($dispositions | Where-Object NeedsCode)
$workflowSensitive = @($dispositions | Where-Object NeedsWorkflow)
$neutralEvidence = @($dispositions | Where-Object Neutral)
$hasCodeDecision = $files -contains "docs/internal/DESIGN_DECISIONS.md"
$hasWorkflowDecision = $files -contains "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
$failures = 0

if ($codeSensitive.Count -gt 0 -and -not $hasCodeDecision) {
  Write-Host "DESIGN-CHECK: code/public/repository-sensitive paths changed; update docs/internal/DESIGN_DECISIONS.md"
  $codeSensitive.Path | ForEach-Object { Write-Host "  code: $_" }
  if ($Strict) {
    $failures += 1
  }
}

if ($workflowSensitive.Count -gt 0 -and -not $hasWorkflowDecision) {
  Write-Host "DESIGN-CHECK: workflow/process-sensitive paths changed; update docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
  $workflowSensitive.Path | ForEach-Object { Write-Host "  workflow: $_" }
  if ($Strict) {
    $failures += 1
  }
}

if ($codeSensitive.Count -eq 0 -and $workflowSensitive.Count -eq 0) {
  Write-Host "DESIGN-CHECK: only neutral decision/evidence/history/report paths changed"
} else {
  Write-Host "DESIGN-CHECK: checked $($files.Count) changed files ($($codeSensitive.Count) code, $($workflowSensitive.Count) workflow, $($neutralEvidence.Count) neutral)"
}

if ($failures -gt 0) {
  Write-Host "DESIGN-CHECK: strict mode found $failures missing design-log updates"
  exit 1
}

exit 0

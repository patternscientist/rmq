#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$OutDir = ""
)

$ErrorActionPreference = "Continue"

if (-not $OutDir) {
  $stamp = Get-Date -Format "yyyyMMdd-HHmmss"
  $OutDir = Join-Path ".audit-packets" $stamp
}

New-Item -ItemType Directory -Force -Path $OutDir | Out-Null

function Write-CommandOutput {
  param(
    [string]$Name,
    [scriptblock]$Command
  )

  $path = Join-Path $OutDir $Name
  & $Command 2>&1 | Out-File -FilePath $path -Encoding utf8
}

function Copy-IfExists {
  param([string]$Path)

  if (-not (Test-Path $Path)) {
    return
  }

  $dest = Join-Path $OutDir $Path
  $parent = Split-Path -Parent $dest
  if ($parent) {
    New-Item -ItemType Directory -Force -Path $parent | Out-Null
  }
  Copy-Item -Path $Path -Destination $dest -Force
}

Write-CommandOutput "git-status.txt" { git status --short --branch }
Write-CommandOutput "git-log.txt" { git log --oneline --decorate -20 }
Write-CommandOutput "git-tags.txt" { git tag --list }
Write-CommandOutput "git-diff-stat.txt" {
  git rev-parse --verify origin/main *> $null
  if ($LASTEXITCODE -eq 0) {
    git diff --stat origin/main...HEAD
  } else {
    git diff --stat HEAD~1..HEAD
  }
}

if (Test-Path "scripts/claim_drift_scan.ps1") {
  Write-CommandOutput "claim-drift-advisory.txt" { & scripts/claim_drift_scan.ps1 }
}

$files = @(
  "AGENTS.md",
  "RMQPaper.lean",
  "RMQ/Headlines/RMQ.lean",
  "docs/PAPER_CLAIM_CORRESPONDENCE.md",
  "docs/WHAT_IS_PROVED.md",
  "docs/PAPER_MODEL_ADEQUACY.md",
  "docs/RMQ_IMPORT_CLOSURE.md",
  "artifact/CLAIMS.md",
  "artifact/README.md",
  "docs/internal/AUDIT_PROTOCOL.md",
  "docs/internal/DESIGN_DECISIONS.md",
  "docs/internal/WORKFLOW_DESIGN_DECISIONS.md",
  "docs/internal/RMQ_FINAL_ROADMAP.md",
  "docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md",
  "docs/internal/CLAIM_DRIFT_POLICY.md",
  "docs/internal/CLAIM_DRIFT_POLICY.json",
  ".agents/skills/rmq-coordinator/SKILL.md",
  ".agents/skills/rmq-audit/SKILL.md",
  ".agents/skills/rmq-proof-sprint/SKILL.md"
)

foreach ($file in $files) {
  Copy-IfExists $file
}

Write-Host "AUDIT-PACKET: wrote $OutDir"

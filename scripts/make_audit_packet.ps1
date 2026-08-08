#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$OutDir = ""
)

$ErrorActionPreference = "Continue"
$packetFailures = 0

if (-not $OutDir) {
  $stamp = Get-Date -Format "yyyyMMdd-HHmmss"
  $OutDir = Join-Path ".audit-packets" $stamp
}

New-Item -ItemType Directory -Force -Path $OutDir | Out-Null

function Write-CommandOutput {
  param(
    [string]$Name,
    [scriptblock]$Command,
    # Some captures are legitimately empty -- `git diff --stat` on a clean tree,
    # for instance. Everything else must produce output, because a zero-byte
    # evidence file in an audit packet reads as "no findings" when it actually
    # means "not captured".
    [switch]$MayBeEmpty
  )

  $path = Join-Path $OutDir $Name
  # `*>&1`, not `2>&1`. PowerShell 5+ sends Write-Host to the information
  # stream (6), which `2>&1` does not redirect. Every lint in scripts/ reports
  # via Write-Host, so `2>&1` captured nothing from them and wrote an empty
  # file while the output went to the console instead. Found on 2026-08-08 when
  # the release-candidate packet's claim-drift advisory came out zero bytes.
  & $Command *>&1 | Out-File -FilePath $path -Encoding utf8

  if (-not $MayBeEmpty) {
    $len = (Get-Item -LiteralPath $path).Length
    if ($len -eq 0) {
      Write-Host "AUDIT-PACKET: FAIL: $Name captured no output; the packet would ship an empty evidence file"
      $script:packetFailures = $script:packetFailures + 1
    }
  }
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

Write-CommandOutput -MayBeEmpty "git-status.txt" { git status --short --branch }
Write-CommandOutput "git-log.txt" { git log --oneline --decorate -20 }
Write-CommandOutput -MayBeEmpty "git-tags.txt" { git tag --list }
Write-CommandOutput -MayBeEmpty "git-diff-stat.txt" {
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
  ".agents/skills/rmq-audit-prompt/SKILL.md",
  ".agents/skills/rmq-proof-sprint/SKILL.md"
)

foreach ($file in $files) {
  Copy-IfExists $file
}

Write-Host "AUDIT-PACKET: wrote $OutDir"

if ($packetFailures -gt 0) {
  Write-Host ("AUDIT-PACKET: RESULT: FAIL ({0} empty evidence file(s))" -f $packetFailures)
  exit 1
}
Write-Host "AUDIT-PACKET: RESULT: PASS"
exit 0

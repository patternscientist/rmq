#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [switch]$Strict,
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string[]]$Path = @("README.md", "artifact", "docs")
)

$ErrorActionPreference = "Continue"

if (-not (Test-Path $PolicyPath)) {
  Write-Host "CLAIM-DRIFT: policy not found: $PolicyPath"
  exit 1
}

$policy = Get-Content -Raw -Path $PolicyPath | ConvertFrom-Json
$roots = @($Path | Where-Object { Test-Path $_ })

if ($roots.Count -eq 0) {
  Write-Host "CLAIM-DRIFT: no scan roots exist"
  exit 0
}

$failures = 0
$hits = 0

foreach ($term in $policy.terms) {
  $pattern = [string]$term.pattern
  $matches = @(& rg -n --pcre2 -- $pattern @roots 2>$null)
  $code = $LASTEXITCODE
  if ($code -gt 1) {
    Write-Host "CLAIM-DRIFT: rg failed for $($term.id)"
    exit $code
  }

  foreach ($match in $matches) {
    $parts = $match -split ":", 3
    if ($parts.Count -lt 3) {
      continue
    }

    $file = $parts[0]
    $fileNorm = $file -replace "\\", "/"
    $lineNo = $parts[1]
    $line = $parts[2]
    $hits += 1

    $allowed = $false
    if ($term.allowedPathRegex -and $fileNorm -match [string]$term.allowedPathRegex) {
      $allowed = $true
    }
    if ($term.allowedLineRegex -and $line -match [string]$term.allowedLineRegex) {
      $allowed = $true
    }

    $label = "review"
    if ($allowed) {
      $label = "allowed"
    }

    if ($Strict -and ($term.strict -eq $true) -and -not $allowed) {
      $label = "fail"
      $failures += 1
    }

    Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f $term.id, $term.status, $label, $file, $lineNo, $line.Trim())
  }
}

if ($hits -eq 0) {
  Write-Host "CLAIM-DRIFT: no sensitive terms found"
}

if ($failures -gt 0) {
  Write-Host "CLAIM-DRIFT: strict mode found $failures unapproved sensitive matches"
  exit 1
}

Write-Host "CLAIM-DRIFT: scan complete ($hits hits, $failures strict failures)"
exit 0

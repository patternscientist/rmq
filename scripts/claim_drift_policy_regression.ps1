#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json"
)

$ErrorActionPreference = "Stop"

if (-not (Test-Path -LiteralPath $PolicyPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: policy not found: $PolicyPath"
  exit 1
}

$policy = Get-Content -LiteralPath $PolicyPath -Raw | ConvertFrom-Json
$term = @($policy.terms | Where-Object { $_.id -eq "forbidden-2pow128-canonical-activation" })
if ($term.Count -ne 1 -or $term[0].strict -ne $true) {
  Write-Host "CLAIM-POLICY-REGRESSION: expected one strict canonical-activation term"
  exit 1
}

$fixtures = @(
  @{ id = "canonical-uses-unspaced"; expectMatch = $true; text = "The canonical execution uses 2^128 as an activation premise." },
  @{ id = "canonical-uses-spaced"; expectMatch = $true; text = "The canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "canonical-route-requires"; expectMatch = $true; text = "The canonical reviewer route requires 2^128 as its activation premise." },
  @{ id = "canonical-query-has"; expectMatch = $true; text = "The canonical query has 2 ^ 128 as an activation premise." },
  @{ id = "exponent-first"; expectMatch = $true; text = "2^128 is the activation premise for the current canonical execution." },
  @{ id = "negated-canonical"; expectMatch = $false; text = "No canonical execution theorem uses 2^128 as an activation premise." },
  @{ id = "negated-current-canonical"; expectMatch = $false; text = "No current canonical reviewer route has 2 ^ 128 as an activation premise." },
  @{ id = "negative-inside-clause"; expectMatch = $false; text = "The canonical execution does not use 2^128 as an activation premise." },
  @{ id = "compatibility-companion"; expectMatch = $false; text = "Compatibility companions retain 2^128 as an explicit sufficient premise." },
  @{ id = "proof-only-sparse-witness"; expectMatch = $false; text = "The proof-only sparse-local witness uses symbolic N = 2 ^ 128." }
)

$fixturePath = Join-Path ([System.IO.Path]::GetTempPath()) ("rmq-claim-policy-regression-" + [Guid]::NewGuid().ToString() + ".txt")
$failures = 0

try {
  foreach ($fixture in $fixtures) {
    [System.IO.File]::WriteAllText($fixturePath, [string]$fixture.text + [Environment]::NewLine)
    & rg -q --pcre2 -- ([string]$term[0].pattern) $fixturePath 2>$null | Out-Null
    $code = $LASTEXITCODE
    if ($code -gt 1) {
      Write-Host "CLAIM-POLICY-REGRESSION: rg failed for $($fixture.id)"
      exit $code
    }

    $matched = $code -eq 0
    if ($matched -ne [bool]$fixture.expectMatch) {
      $expected = if ($fixture.expectMatch) { "reject (must match)" } else { "accept (must not match)" }
      $actual = if ($matched) { "matched" } else { "did not match" }
      Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$($fixture.id)] expected $expected, ${actual}: $($fixture.text)"
      $failures += 1
    } else {
      $outcome = if ($matched) { "REJECT" } else { "ACCEPT" }
      Write-Host "CLAIM-POLICY-REGRESSION: PASS [$($fixture.id)] $outcome"
    }
  }
}
finally {
  Remove-Item -LiteralPath $fixturePath -ErrorAction SilentlyContinue
}

if ($failures -gt 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: $failures fixture failures"
  exit 1
}

Write-Host "CLAIM-POLICY-REGRESSION: PASS ($($fixtures.Count) role-scoped fixtures)"
exit 0

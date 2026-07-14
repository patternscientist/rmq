#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string]$ScannerPath = "scripts/claim_drift_scan.ps1"
)

$ErrorActionPreference = "Stop"

if (-not (Test-Path -LiteralPath $PolicyPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: policy not found: $PolicyPath"
  exit 1
}

if (-not (Test-Path -LiteralPath $ScannerPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: scanner not found: $ScannerPath"
  exit 1
}

$fixtures = @(
  @{ id = "canonical-uses-unspaced"; reject = $true; text = "The canonical execution uses 2^128 as an activation premise." },
  @{ id = "canonical-uses-spaced"; reject = $true; text = "The canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "canonical-route-requires"; reject = $true; text = "The canonical reviewer route requires 2^128 as its activation premise." },
  @{ id = "canonical-query-has"; reject = $true; text = "The canonical query has 2 ^ 128 as an activation premise." },
  @{ id = "exponent-first-premise"; reject = $true; text = "2^128 is the activation premise for the current canonical execution." },
  @{ id = "possessive-premise-unspaced"; reject = $true; text = "The canonical execution's activation premise is 2^128." },
  @{ id = "possessive-premise-spaced"; reject = $true; text = "The canonical execution's activation premise is 2 ^ 128." },
  @{ id = "activated-at-unspaced"; reject = $true; text = "The canonical execution is activated at 2^128." },
  @{ id = "activated-at-spaced"; reject = $true; text = "The canonical execution is activated at 2 ^ 128." },
  @{ id = "reviewer-threshold-unspaced"; reject = $true; text = "The canonical reviewer route uses a 2^128 activation threshold." },
  @{ id = "reviewer-threshold-spaced"; reject = $true; text = "The canonical reviewer route uses a 2 ^ 128 activation threshold." },
  @{ id = "exponent-first-activates"; reject = $true; text = "2 ^ 128 activates the canonical reviewer route." },
  @{ id = "exponent-first-threshold"; reject = $true; text = "At 2^128, the canonical execution crosses its activation threshold." },
  @{ id = "negated-canonical"; reject = $false; allowedMatch = $true; text = "No canonical execution theorem uses 2^128 as an activation premise." },
  @{ id = "negated-current-canonical"; reject = $false; allowedMatch = $true; text = "No current canonical reviewer route has 2 ^ 128 as an activation premise." },
  @{ id = "negative-inside-clause"; reject = $false; allowedMatch = $true; text = "The canonical execution does not use 2^128 as an activation premise." },
  @{ id = "not-true-negation"; reject = $false; allowedMatch = $true; text = "It is not true that the canonical execution uses 2^128 as an activation premise." },
  @{ id = "noncanonical-execution"; reject = $false; text = "The noncanonical execution uses 2^128 as an activation premise." },
  @{ id = "non-hyphen-canonical-execution"; reject = $false; text = "The non-canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "compatibility-companion"; reject = $false; text = "Compatibility companions retain 2^128 as an explicit sufficient premise." },
  @{ id = "proof-only-sparse-witness"; reject = $false; text = "The proof-only sparse-local witness uses symbolic N = 2 ^ 128." },
  @{ id = "historical-role"; reject = $false; allowedMatch = $true; text = "Historical note: The canonical execution's activation premise was 2^128." },
  @{ id = "compatibility-role"; reject = $false; allowedMatch = $true; text = "Compatibility companion: The canonical reviewer route uses a 2^128 activation threshold." },
  @{ id = "proof-only-role"; reject = $false; allowedMatch = $true; text = "Proof-only witness: The hypothetical canonical query has a 2 ^ 128 activation premise; this is not an execution premise." }
)

$shellPath = (Get-Process -Id $PID).Path
$relativeFixtureRoot = ".claim-drift-policy-regression-" + [Guid]::NewGuid().ToString("N")
$absoluteFixtureRoot = Join-Path (Get-Location).Path $relativeFixtureRoot
[System.IO.Directory]::CreateDirectory($absoluteFixtureRoot) | Out-Null
$failures = 0
$rejectCount = 0
$acceptCount = 0

function Invoke-StrictClaimScan {
  param([string]$Path)

  $output = @(& $shellPath -NoLogo -NoProfile -ExecutionPolicy Bypass -File $ScannerPath -Strict -PolicyPath $PolicyPath -Path $Path 2>&1)
  [PSCustomObject]@{
    Code = $LASTEXITCODE
    Output = @($output | ForEach-Object { [string]$_ })
  }
}

try {
  foreach ($fixture in $fixtures) {
    $fixturePath = Join-Path $relativeFixtureRoot ($fixture.id + ".txt")
    [System.IO.File]::WriteAllText((Join-Path (Get-Location).Path $fixturePath), [string]$fixture.text + [Environment]::NewLine)
    $result = Invoke-StrictClaimScan -Path $fixturePath
    $termFailed = [bool]($result.Output -match "CLAIM-DRIFT\[forbidden-2pow128-canonical-activation\].*\[fail\]")
    $termAllowed = [bool]($result.Output -match "CLAIM-DRIFT\[forbidden-2pow128-canonical-activation\].*\[allowed\]")

    if ($fixture.reject) {
      $rejectCount += 1
      $passed = ($result.Code -ne 0) -and $termFailed
      $expected = "REJECT"
    } else {
      $acceptCount += 1
      $passed = $result.Code -eq 0
      if ($fixture.allowedMatch) {
        $passed = $passed -and $termAllowed
      }
      $expected = "ACCEPT"
    }

    if (-not $passed) {
      Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$($fixture.id)] expected final strict verdict $expected"
      $result.Output | ForEach-Object { Write-Host "  $_" }
      $failures += 1
    } else {
      Write-Host "CLAIM-POLICY-REGRESSION: PASS [$($fixture.id)] $expected"
    }
  }

  $pathFixtures = @(
    @{ id = "policy-path-allowance"; path = "docs/internal/CLAIM_DRIFT_POLICY.md"; marker = "CLAIM_DRIFT_POLICY\.md" },
    @{ id = "contract-path-allowance"; path = "docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md"; marker = "W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX\.md" }
  )
  foreach ($pathFixture in $pathFixtures) {
    $pathResult = Invoke-StrictClaimScan -Path $pathFixture.path
    $pathAllowed = [bool]($pathResult.Output -match ("CLAIM-DRIFT\[forbidden-2pow128-canonical-activation\].*\[allowed\].*" + $pathFixture.marker))
    if ($pathResult.Code -ne 0 -or -not $pathAllowed) {
      Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$($pathFixture.id)] expected final strict verdict ACCEPT via exact path"
      $pathResult.Output | ForEach-Object { Write-Host "  $_" }
      $failures += 1
    } else {
      Write-Host "CLAIM-POLICY-REGRESSION: PASS [$($pathFixture.id)] ACCEPT"
    }
  }
}
finally {
  if ([System.IO.Directory]::Exists($absoluteFixtureRoot)) {
    [System.IO.Directory]::Delete($absoluteFixtureRoot, $true)
  }
}

if ($failures -gt 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: $failures fixture failures"
  exit 1
}

Write-Host "CLAIM-POLICY-REGRESSION: PASS ($rejectCount must-reject strict verdicts, $acceptCount must-accept strict verdicts, 2 exact-path allowance verdicts)"
exit 0

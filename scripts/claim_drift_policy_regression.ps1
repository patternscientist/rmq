#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string]$ScannerPath = "scripts/claim_drift_scan.ps1",
  [switch]$AbsoluteWindowsOnly
)

$ErrorActionPreference = "Stop"

$repoRoot = [System.IO.Path]::GetFullPath((Get-Location).Path)
$resolvedPolicyPath = [System.IO.Path]::GetFullPath($PolicyPath)
$resolvedScannerPath = [System.IO.Path]::GetFullPath($ScannerPath)

if (-not (Test-Path -LiteralPath $resolvedPolicyPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: policy not found: $PolicyPath"
  exit 1
}

if (-not (Test-Path -LiteralPath $resolvedScannerPath)) {
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

  # Two-token category representatives: none contains the old third token class.
  @{ id = "canonical-execution-requires"; reject = $true; text = "The canonical execution requires 2^128." },
  @{ id = "reviewer-route-available-only"; reject = $true; text = "The canonical reviewer route is available only at 2 ^ 128." },
  @{ id = "canonical-query-needs"; reject = $true; text = "The canonical query needs 2^128." },
  @{ id = "exponent-required-current-execution"; reject = $true; text = "2^128 is required by the current canonical execution." },
  @{ id = "heldout-canonical-query-works"; reject = $true; text = "For this construction, the canonical query works at 2^128." },
  @{ id = "heldout-exponent-bounds-route"; reject = $true; text = "Here 2 ^ 128 bounds the canonical route." },
  @{ id = "heldout-canonical-execution-mentions"; reject = $true; text = "The canonical execution mentions 2^128." },

  # Allowance-bypass mutations: negative or role words alone must not whitelist.
  @{ id = "bypass-does-not-avoid"; reject = $true; text = "The canonical execution does not avoid requiring 2^128." },
  @{ id = "bypass-not-optional"; reject = $true; text = "It is not optional: the canonical execution requires 2^128." },
  @{ id = "bypass-historical-irrelevant"; reject = $true; text = "Historical context is irrelevant: the canonical execution requires 2^128." },
  @{ id = "bypass-compatibility-irrelevant"; reject = $true; text = "Compatibility is irrelevant: the canonical route needs 2^128." },
  @{ id = "bypass-no-canonical-first-clause"; reject = $true; text = "No canonical execution is discussed here; the canonical execution requires 2^128." },
  @{ id = "bypass-not-true-first-clause"; reject = $true; text = "It is not true that the canonical execution is slow; the canonical execution requires 2^128." },

  @{ id = "negated-canonical"; reject = $false; allowedMatch = $true; text = "No canonical execution theorem uses 2^128 as an activation premise." },
  @{ id = "negated-current-canonical"; reject = $false; allowedMatch = $true; text = "No current canonical reviewer route has 2 ^ 128 as an activation premise." },
  @{ id = "negative-inside-clause"; reject = $false; allowedMatch = $true; text = "The canonical execution does not use 2^128 as an activation premise." },
  @{ id = "not-true-negation"; reject = $false; allowedMatch = $true; text = "It is not true that the canonical execution uses 2^128 as an activation premise." },
  @{ id = "negated-possessive-premise"; reject = $false; allowedMatch = $true; text = "The canonical execution's activation premise is not 2^128." },
  @{ id = "negated-route-has-no"; reject = $false; allowedMatch = $true; text = "The canonical route has no 2^128 activation threshold." },
  @{ id = "negated-unlike-old-theorem"; reject = $false; allowedMatch = $true; text = "Unlike the old theorem, no canonical execution has 2^128 as an activation premise." },
  @{ id = "negated-exponent-first"; reject = $false; allowedMatch = $true; text = "2 ^ 128 is not required by the canonical query." },
  @{ id = "noncanonical-execution"; reject = $false; text = "The noncanonical execution uses 2^128 as an activation premise." },
  @{ id = "non-hyphen-canonical-execution"; reject = $false; text = "The non-canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "compatibility-companion"; reject = $false; text = "Compatibility companions retain 2^128 as an explicit sufficient premise." },
  @{ id = "proof-only-sparse-witness"; reject = $false; text = "The proof-only sparse-local witness uses symbolic N = 2 ^ 128." },
  @{ id = "historical-role"; reject = $false; allowedMatch = $true; text = "Historical note: The canonical execution's activation premise was 2^128." },
  @{ id = "compatibility-role"; reject = $false; allowedMatch = $true; text = "Compatibility companion: The canonical reviewer route uses a 2^128 activation threshold." },
  @{ id = "proof-only-role"; reject = $false; allowedMatch = $true; text = "Proof-only witness: The hypothetical canonical query has a 2 ^ 128 activation premise; this is not an execution premise." }
)

$shellPath = (Get-Process -Id $PID).Path
$absoluteFixtureRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("claim-drift-policy-regression-" + [Guid]::NewGuid().ToString("N"))
[System.IO.Directory]::CreateDirectory($absoluteFixtureRoot) | Out-Null
$matrixPath = "docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md"
$failures = 0
$rejectCount = 0
$acceptCount = 0
$contextCount = 0
$baselineStatus = $null
$baselineTrackedHashes = $null

function Get-TrackedGitStatus {
  Push-Location $repoRoot
  try {
    return (@(& git -c core.excludesfile= -c core.autocrlf=false status --short --untracked-files=all) -join [Environment]::NewLine)
  } finally {
    Pop-Location
  }
}

function Get-TrackedFileHashSnapshot {
  Push-Location $repoRoot
  try {
    $worktreeRaw = @(& git -c core.excludesfile= -c core.autocrlf=false diff --raw --no-ext-diff --)
    $indexRaw = @(& git -c core.excludesfile= -c core.autocrlf=false diff --cached --raw --no-ext-diff --)
    $matrixHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $repoRoot $matrixPath)).Hash.ToLowerInvariant()
    return @(
      "worktree-diff-raw:"
      $worktreeRaw
      "index-diff-raw:"
      $indexRaw
      "matrix-sha256: $matrixHash"
    ) -join [Environment]::NewLine
  } finally {
    Pop-Location
  }
}

function Assert-TrackedStateUnchanged {
  param([string]$Context)

  $status = Get-TrackedGitStatus
  if ($status -ne $baselineStatus) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Context] git status changed"
    Write-Host "  expected: $baselineStatus"
    Write-Host "  actual:   $status"
    $script:failures += 1
    return
  }

  $hashes = Get-TrackedFileHashSnapshot
  if ($hashes -ne $baselineTrackedHashes) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Context] tracked file hashes changed"
    $script:failures += 1
    return
  }

  Write-Host "CLAIM-POLICY-REGRESSION: PASS [$Context] tracked state unchanged"
}

function New-ShadowMatrixRoot {
  param([string]$Content)

  $shadowRoot = Join-Path $absoluteFixtureRoot ("shadow-" + [Guid]::NewGuid().ToString("N"))
  $shadowMatrixPath = Join-Path $shadowRoot $matrixPath
  [System.IO.Directory]::CreateDirectory((Split-Path -Parent $shadowMatrixPath)) | Out-Null
  [System.IO.File]::WriteAllText($shadowMatrixPath, $Content + [Environment]::NewLine)
  [PSCustomObject]@{
    Root = $shadowRoot
    RelativeMatrixPath = $matrixPath
    AbsoluteMatrixPath = $shadowMatrixPath
  }
}

function Invoke-StrictClaimScan {
  param(
    [string]$Path,
    [string]$WorkingDirectory = $repoRoot
  )

  Push-Location $WorkingDirectory
  try {
    $output = @(& $shellPath -NoLogo -NoProfile -ExecutionPolicy Bypass -File $resolvedScannerPath -Strict -PolicyPath $resolvedPolicyPath -Path $Path 2>&1)
    $code = $LASTEXITCODE
  } finally {
    Pop-Location
  }
  [PSCustomObject]@{
    Code = $code
    Output = @($output | ForEach-Object { [string]$_ })
  }
}

function Test-FinalVerdict {
  param(
    [string]$Id,
    [string]$Path,
    [bool]$Reject,
    [bool]$RequireAllowed = $false,
    [string]$WorkingDirectory = $repoRoot,
    [bool]$CheckTrackedState = $false
  )

  if ($CheckTrackedState) {
    Assert-TrackedStateUnchanged -Context "before-$Id"
  }

  $result = Invoke-StrictClaimScan -Path $Path -WorkingDirectory $WorkingDirectory

  if ($CheckTrackedState) {
    Assert-TrackedStateUnchanged -Context "after-$Id"
  }

  $termFailed = [bool]($result.Output -match "CLAIM-DRIFT\[forbidden-2pow128-canonical-activation\].*\[fail\]")
  $termAllowed = [bool]($result.Output -match "CLAIM-DRIFT\[forbidden-2pow128-canonical-activation\].*\[allowed\]")
  if ($Reject) {
    $passed = ($result.Code -ne 0) -and $termFailed
    $expected = "REJECT"
  } else {
    $passed = $result.Code -eq 0
    if ($RequireAllowed) {
      $passed = $passed -and $termAllowed
    }
    $expected = "ACCEPT"
  }

  if (-not $passed) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Id] expected final strict verdict $expected"
    $result.Output | ForEach-Object { Write-Host "  $_" }
    $script:failures += 1
  } else {
    Write-Host "CLAIM-POLICY-REGRESSION: PASS [$Id] $expected"
  }
}

function Test-AbsoluteWindowsScannerPath {
  $absoluteFixturePath = Join-Path $absoluteFixtureRoot "absolute-windows-misuse.txt"
  [System.IO.File]::WriteAllText(
    $absoluteFixturePath,
    "The canonical execution requires 2^128." + [Environment]::NewLine
  )

  if ($env:OS -eq "Windows_NT" -and $absoluteFixturePath -notmatch "^[A-Za-z]:[\\/]") {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [absolute-windows-drive-qualified] fixture path is not drive-qualified: $absoluteFixturePath"
    $script:failures += 1
  } else {
    Test-FinalVerdict -Id "absolute-windows-single-file" -Path $absoluteFixturePath -Reject $true -CheckTrackedState $true
  }

  $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
  Test-FinalVerdict -Id "absolute-matrix-context-allowance" -Path $markedShadow.AbsoluteMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true
  $script:contextCount += 2
}

try {
  $baselineStatus = Get-TrackedGitStatus
  $baselineTrackedHashes = Get-TrackedFileHashSnapshot

  if ($AbsoluteWindowsOnly) {
    Test-AbsoluteWindowsScannerPath
  } else {
    foreach ($fixture in $fixtures) {
      $fixturePath = $fixture.id + ".txt"
      [System.IO.File]::WriteAllText(
        (Join-Path $absoluteFixtureRoot $fixturePath),
        [string]$fixture.text + [Environment]::NewLine
      )
      Test-FinalVerdict -Id $fixture.id -Path $fixturePath -WorkingDirectory $absoluteFixtureRoot -Reject ([bool]$fixture.reject) -RequireAllowed ([bool]$fixture.allowedMatch)
      if ($fixture.reject) {
        $rejectCount += 1
      } else {
        $acceptCount += 1
      }
    }

    Test-FinalVerdict -Id "policy-path-allowance" -Path "docs/internal/CLAIM_DRIFT_POLICY.md" -Reject $false -RequireAllowed $true

    $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
    Test-FinalVerdict -Id "matrix-marked-row-allowance" -Path $markedShadow.RelativeMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true
    $contextCount += 2

    Test-AbsoluteWindowsScannerPath

    $unmarkedShadow = New-ShadowMatrixRoot -Content 'The canonical execution requires 2^128.'
    Test-FinalVerdict -Id "matrix-filename-does-not-bypass" -Path $unmarkedShadow.RelativeMatrixPath -WorkingDirectory $unmarkedShadow.Root -Reject $true -CheckTrackedState $true
    $contextCount += 1
  }
} finally {
  if ([System.IO.Directory]::Exists($absoluteFixtureRoot)) {
    [System.IO.Directory]::Delete($absoluteFixtureRoot, $true)
  }
}

if ($failures -gt 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: $failures fixture failures"
  exit 1
}

if ($AbsoluteWindowsOnly) {
  Write-Host "CLAIM-POLICY-REGRESSION: ABSOLUTE-WINDOWS PASS ($contextCount production path verdicts)"
} else {
  Write-Host "CLAIM-POLICY-REGRESSION: PASS ($rejectCount must-reject strict verdicts, $acceptCount must-accept strict verdicts, $contextCount path/context/bypass verdicts)"
}
exit 0

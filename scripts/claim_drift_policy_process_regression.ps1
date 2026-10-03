#!/usr/bin/env pwsh
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$source = Join-Path $PSScriptRoot 'claim_drift_policy_regression.ps1'
$tokens = $null; $errors = $null
$ast = [Management.Automation.Language.Parser]::ParseFile($source, [ref]$tokens, [ref]$errors)
if ($errors.Count) { throw 'policy regression parse failed' }
foreach ($name in @('Invoke-BoundedProcess', 'Invoke-StrictClaimScan', 'Test-FinalVerdict')) {
  $found = @($ast.FindAll({param($n) $n -is [Management.Automation.Language.FunctionDefinitionAst]}, $false) | Where-Object Name -CEQ $name)
  if ($found.Count -ne 1) { throw "nonunique production function: $name" }
  Invoke-Expression $found[0].Extent.Text
}
$absoluteFixtureRoot = Join-Path ([IO.Path]::GetTempPath()) ('claim-policy-process-' + [Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($absoluteFixtureRoot)
$shellPath = (Get-Process -Id $PID).Path
$resolvedPolicyPath = Join-Path $repoRoot 'docs/internal/CLAIM_DRIFT_POLICY.json'
$resolvedScannerPath = Join-Path $absoluteFixtureRoot 'scanner.ps1'
$scannerStageTimeoutMs = 15000
$failures = 0
$term = 'forbidden-retired-current-cost-bound'
$observed = [Collections.Generic.List[string]]::new()
$expected = @('normal-accept', 'normal-reject', 'wrong-exit', 'missing-diagnostic',
  'timeout-reject', 'timeout-accept', 'cleanup-reject', 'cleanup-accept',
  'overflow-reject', 'overflow-accept', 'real-fail-then-hang')
function Assert-Control([string]$Id, [bool]$Reject, [bool]$ExpectedPass) {
  $before = $script:failures
  Test-FinalVerdict -Id $Id -Path 'input.md' -WorkingDirectory $absoluteFixtureRoot -Reject $Reject -TermId $term
  $passed = $script:failures -eq $before
  if ($passed -ne $ExpectedPass) { throw "wrong production verdict for $Id" }
  $script:failures = $before
  $observed.Add($Id)
  Write-Host "CLAIM-POLICY-PROCESS-CONTROL: PASS [$Id] verdict=$passed"
}
try {
  # First exercise real normal child exits and the real scanner launch function.
  [IO.File]::WriteAllText($resolvedScannerPath, 'exit 0')
  Assert-Control 'normal-accept' $false $true
  [IO.File]::WriteAllText($resolvedScannerPath, "Write-Host 'CLAIM-DRIFT[$term] [fail] intended'; exit 1")
  Assert-Control 'normal-reject' $true $true
  # Isolate status consumption without replacing the production predicate.
  $realScannerFunction = (Get-Item Function:Invoke-StrictClaimScan).ScriptBlock
  function Invoke-StrictClaimScan { return $script:syntheticResult }
  foreach ($case in @(
      @('wrong-exit', $true, 2, $false, $true, $false, $true),
      @('missing-diagnostic', $true, 1, $false, $true, $false, $false),
      @('timeout-reject', $true, 124, $true, $true, $false, $true),
      @('timeout-accept', $false, 0, $true, $true, $false, $true),
      @('cleanup-reject', $true, 1, $false, $false, $false, $true),
      @('cleanup-accept', $false, 0, $false, $false, $false, $true),
      @('overflow-reject', $true, 1, $false, $true, $true, $true),
      @('overflow-accept', $false, 0, $false, $true, $true, $true))) {
    $syntheticResult = [pscustomobject]@{
      Code=$case[2]; TimedOut=$case[3]; Cleaned=$case[4]; OutputLimitExceeded=$case[5]
      Ownership='synthetic-status'; Output=@($(if ($case[6]) { "CLAIM-DRIFT[$term] [fail] intended" } else { 'unrelated' }))
    }
    Assert-Control $case[0] $case[1] $false
  }
  Set-Item Function:Invoke-StrictClaimScan $realScannerFunction
  # The child writes both its own PID and an inherited-output descendant PID.
  # This reproduces P2-01 through the exact runner AND final verdict consumer.
  $childScript = Join-Path $absoluteFixtureRoot 'descendant.ps1'
  [IO.File]::WriteAllText($childScript, 'Start-Sleep -Seconds 60')
  [IO.File]::WriteAllText($resolvedScannerPath, @'
param([switch]$Strict, [switch]$ShowAllowed, [string]$PolicyPath, [string]$Path)
$ErrorActionPreference = 'Stop'
$child = Start-Process -FilePath (Get-Process -Id $PID).Path -ArgumentList @('-NoLogo','-NoProfile','-File',('"' + (Join-Path $PSScriptRoot 'descendant.ps1') + '"')) -PassThru -NoNewWindow
@($PID, $child.Id) | Set-Content (Join-Path $PSScriptRoot 'pids.txt')
Write-Host 'CLAIM-DRIFT[forbidden-retired-current-cost-bound] [fail] intended'
Start-Sleep -Seconds 60
'@)
  # WSL startup exceeded five seconds in the retained first attempt.
  # Fifteen seconds reached the diagnostic and still bounded the 60s sleeper.
  $scannerStageTimeoutMs = 15000
  # Capture the actual result while retaining the production invocation function.
  function Invoke-StrictClaimScan {
    param([string]$Path, [string]$WorkingDirectory, [bool]$ShowAllowed)
    $script:actualTimeout = & $realScannerFunction -Path $Path -WorkingDirectory $WorkingDirectory -ShowAllowed $ShowAllowed
    return $script:actualTimeout
  }
  Assert-Control 'real-fail-then-hang' $true $false
  if (-not $actualTimeout.TimedOut -or -not $actualTimeout.Cleaned -or
      $actualTimeout.Code -ne 124 -or -not ($actualTimeout.Output -match '\[fail\]')) {
    throw 'real timeout control failed to reach the intended antecedent'
  }
  $ownedPids = @(Get-Content (Join-Path $absoluteFixtureRoot 'pids.txt') | ForEach-Object { [int]$_ })
  if ($ownedPids.Count -ne 2 -or @(Get-RMQAliveProcessIds $ownedPids).Count -ne 0) {
    throw 'real timeout control descendants survived cleanup'
  }
  if (($observed -join '|') -cne ($expected -join '|') -or
      @($observed | Group-Object | Where-Object Count -ne 1).Count) {
    throw 'process control registry mismatch'
  }
  Write-Host "CLAIM-POLICY-PROCESS-CONTROL: PASS exact registry ($($expected.Count)); descendant cleanup verified"
} finally {
  $full = [IO.Path]::GetFullPath($absoluteFixtureRoot)
  $parent = [IO.Path]::GetFullPath([IO.Path]::GetTempPath()).TrimEnd('\', '/')
  if ([IO.Path]::GetDirectoryName($full) -ne $parent -or
      [IO.Path]::GetFileName($full) -notmatch '^claim-policy-process-[0-9a-f]{32}$') {
    throw 'refusing cleanup outside owned process fixture'
  }
  if (Test-Path -LiteralPath $full) { Remove-Item -LiteralPath $full -Recurse -Force }
}
exit 0

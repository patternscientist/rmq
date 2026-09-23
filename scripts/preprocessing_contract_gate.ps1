#!/usr/bin/env pwsh
<#
PRE1-CONTRACT-GATE. Aggregate-gate checker for the frozen PRE-1 contract layer:
production contract firewall, contract producer build, typed contract consumer.
Each stage is an owned bounded subprocess. A timeout or output-limit hit is
inconclusive and fails; a nonzero exit fails. Invoke-Checker runs this file
in-process and requires an explicit `exit`.
#>
[CmdletBinding()]
param([string]$LakePath = '')

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$script:RepositoryRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$script:TempRoot = Join-Path $script:RepositoryRoot '.lake/preprocessing-contract-gate'
$script:OutputLimitBytes = 16777216
$script:LastOutput = @()

function Resolve-GateLake([string]$ExplicitPath) {
  if (-not [string]::IsNullOrWhiteSpace($ExplicitPath)) {
    $resolved = if ([IO.Path]::IsPathRooted($ExplicitPath)) {
      [IO.Path]::GetFullPath($ExplicitPath)
    } else { [IO.Path]::GetFullPath((Join-Path $script:RepositoryRoot $ExplicitPath)) }
    if (-not (Test-Path -LiteralPath $resolved -PathType Leaf)) {
      throw "lake unavailable at $resolved"
    }
    return $resolved
  }
  # The aggregate gate itself uses `lake` from PATH.
  return Resolve-RMQScalarApplicationPath @(Get-Command lake -CommandType Application -ErrorAction Stop) 'lake'
}

function Invoke-GateStage([string]$Stage, [string]$FilePath, [string[]]$Arguments,
    [int]$Seconds, [hashtable]$Environment = @{}, [string]$RequiredOutput = '') {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments `
    -WorkingDirectory $script:RepositoryRoot -Stage $Stage -DeadlineSeconds $Seconds `
    -OutputLimitBytes $script:OutputLimitBytes -TempRoot $script:TempRoot -Environment $Environment
  $script:LastOutput = @($result.Output)
  Write-Host "PRE1-CONTRACT-GATE stage=$Stage exit=$($result.ExitCode) duration=$($result.DurationSeconds)s deadline=$($Seconds)s"
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    throw "inconclusive stage $Stage after $($result.DurationSeconds)s; timeout=$($result.TimedOut), outputLimit=$($result.OutputLimitExceeded)"
  }
  if ($result.ExitCode -ne 0) { throw "stage $Stage exited $($result.ExitCode)" }
  if ($RequiredOutput -ne '' -and -not (($result.Output -join "`n").Contains($RequiredOutput))) {
    throw "stage $Stage exited 0 without printing '$RequiredOutput'"
  }
  return $result
}

try {
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $lake = Resolve-GateLake $LakePath
  $shell = (Get-Process -Id $PID).Path
  Write-Host "PRE1-CONTRACT-GATE lake=$lake shell=$shell"
  # 1. Production contract guard (imports + frozen bytes), under the current shell.
  [void](Invoke-GateStage 'contract-firewall' $shell `
    @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File',
      (Join-Path $PSScriptRoot 'preprocessing_contract_firewall.ps1')) `
    120 @{} 'PRE1-FIREWALL PASS: exact Std-only primitive closure and frozen evaluator bytes')
  # 2. Producer. Cold audit build measured 77.207 s; 900 s is 2x cold margin
  #    plus contention margin on a shared host.
  [void](Invoke-GateStage 'contract-producer' $lake `
    @('build', 'RMQ.Core.WordRAM.Construction.Contract') `
    900 @{ LEAN_NUM_THREADS = '1' })
  # 3. Typed consumer. Measured 2.7-9.9 s.
  [void](Invoke-GateStage 'contract-consumer' $lake `
    @('env', 'lean', 'scripts/preprocessing_contract_check.lean') `
    300 @{ LEAN_NUM_THREADS = '1' } 'PRE1-CONTRACT-TYPED-CONSUMERS PASS')
} catch {
  Write-Host "PRE1-CONTRACT-GATE FAIL: $($_.Exception.Message)"
  foreach ($line in $script:LastOutput) { Write-Host "  | $line" }
  exit 1
}
Write-Host 'PRE1-CONTRACT-GATE PASS'
exit 0

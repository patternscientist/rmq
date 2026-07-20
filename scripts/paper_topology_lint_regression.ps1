#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$OnlyCase = '',
  [ValidateRange(30, 3600)]
  [int]$StageDeadlineSeconds = 300,
  [ValidateRange(4096, 16777216)]
  [int]$StageOutputLimitBytes = 4194304
)

$ErrorActionPreference = 'Stop'
$pathKeys = @(
  [Environment]::GetEnvironmentVariables().Keys |
    Where-Object { [string]$_ -ieq 'path' })
if ($pathKeys.Count -gt 1 -and $pathKeys -ccontains 'PATH') {
  Remove-Item Env:PATH -ErrorAction Stop
}
if (-not ('RMQReplayJob' -as [type])) {
  Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.Runtime.InteropServices;
public static class RMQReplayJob {
  private const int Extended = 9;
  private const uint KillOnClose = 0x00002000;
  [StructLayout(LayoutKind.Sequential)] private struct IO { public ulong a,b,c,d,e,f; }
  [StructLayout(LayoutKind.Sequential)] private struct Basic {
    public long a,b; public uint flags; public UIntPtr c,d;
    public uint e; public UIntPtr f; public uint g,h;
  }
  [StructLayout(LayoutKind.Sequential)] private struct ExtendedInfo {
    public Basic basic; public IO io; public UIntPtr a,b,c,d;
  }
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern IntPtr CreateJobObject(IntPtr a, string n);
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern bool SetInformationJobObject(IntPtr j,int c,ref ExtendedInfo i,uint n);
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern bool AssignProcessToJobObject(IntPtr j,IntPtr p);
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern bool CloseHandle(IntPtr h);
  public static IntPtr CreateKillOnClose() {
    IntPtr j=CreateJobObject(IntPtr.Zero,null);
    if(j==IntPtr.Zero) throw new Win32Exception(Marshal.GetLastWin32Error());
    var i=new ExtendedInfo(); i.basic.flags=KillOnClose;
    if(!SetInformationJobObject(j,Extended,ref i,(uint)Marshal.SizeOf(typeof(ExtendedInfo)))) {
      int e=Marshal.GetLastWin32Error(); CloseHandle(j); throw new Win32Exception(e);
    }
    return j;
  }
  public static void Assign(IntPtr j,IntPtr p) {
    if(!AssignProcessToJobObject(j,p)) throw new Win32Exception(Marshal.GetLastWin32Error());
  }
  public static void Close(IntPtr j) {
    if(j!=IntPtr.Zero && !CloseHandle(j)) throw new Win32Exception(Marshal.GetLastWin32Error());
  }
}
'@
}
$repoRoot = [IO.Path]::GetFullPath((Get-Location).Path)
$lintPath = [IO.Path]::GetFullPath('scripts/paper_topology_lint.ps1')
$shellPath = (Get-Process -Id $PID).Path
$failures = 0
$executedCount = 0
$rejectCount = 0
$acceptCount = 0
$executedIds = [Collections.Generic.List[string]]::new()
$ownedRootIds = [Collections.Generic.HashSet[int]]::new()
$integrityPaths = @(
  'scripts/headline_axiom_check.lean',
  'scripts/gate.ps1',
  'scripts/m1_certificate_mutation_regression.ps1',
  'scripts/paper_topology_lint.ps1',
  'scripts/paper_topology_lint_regression.ps1',
  'docs/internal/M1_REVIEWER_NATIVE_ADEQUACY_ACCEPTANCE_MATRIX.md'
)

if (-not (Test-Path -LiteralPath $lintPath)) {
  Write-Host "PAPER-TOPOLOGY-REGRESSION: missing lint $lintPath"
  exit 1
}

function New-TopologyCase(
    [string]$Id,
    [string]$Path,
    [string]$Text,
    [bool]$Reject,
    [string]$RemoveText = '',
    [string]$MutationCase = '',
    [string[]]$ExpectedPatterns = @()) {
  return [pscustomobject]@{
    Id = $Id
    Path = $Path
    Text = $Text
    Reject = $Reject
    RemoveText = $RemoveText
    MutationCase = $MutationCase
    ExpectedPatterns = $ExpectedPatterns
  }
}

$fencedTransitional = @'
```lean
#check RMQ.Headlines.succinctRMQCanonicalTransitionalQueryCostEq
```
'@
$retiredAlias = 'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'
$exactFrozenLine =
  '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'

# REPLAY-SELECTOR-NONVACUITY
$expectedCaseIds = @(
  'retired-alias-in-prose',
  'transitional-alias-in-fence',
  'dead-documentary-alias',
  'renamed-w18-alias',
  'compatibility-as-current-anchor',
  'canonical-paper-anchor',
  'retired-alias-current-publication-digest',
  'retired-current-alias-audit-report',
  'valid-exact-frozen-snapshot-occurrence',
  'same-frozen-occurrence-current-digest',
  'casual-frozen-history-marker',
  'forged-duplicate-exact-marker',
  'worker-phase-label-canonical-comment',
  'dated-snapshot-current-family-summary',
  'A01',
  'A02'
)
$caseRegistry = @(
  (New-TopologyCase 'retired-alias-in-prose' 'README.md' 'Current capstone: RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery.' $true),
  (New-TopologyCase 'transitional-alias-in-fence' 'docs/PAPER_THEOREM_MAP.md' $fencedTransitional $true),
  (New-TopologyCase 'dead-documentary-alias' 'docs/PAPER_THEOREM_MAP.md' 'Current capstone: RMQ.Headlines.succinctRMQInventedDeadPaperAnchor.' $true),
  (New-TopologyCase 'renamed-w18-alias' 'docs/FAMILY_SUMMARY.md' 'Current evidence: RMQ.Headlines.listIntSuccinctRMQEventValueProducerProvenanceOfValid.' $true),
  (New-TopologyCase 'compatibility-as-current-anchor' 'docs/PAPER_THEOREM_MAP.md' 'Current capstone: RMQ.Headlines.succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreExecutionStory.' $true),
  (New-TopologyCase 'canonical-paper-anchor' 'README.md' 'Current capstone: RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile.' $false),
  (New-TopologyCase 'retired-alias-current-publication-digest' 'docs/digests/PROJECT_DIGESTION_CURRENT.md' "Current capstone: $retiredAlias." $true),
  (New-TopologyCase 'retired-current-alias-audit-report' 'docs/internal/audit_reports/2026-07-14_A04_u2_blind_acceptance_audit.md' "Current capstone: $retiredAlias." $true),
  (New-TopologyCase 'valid-exact-frozen-snapshot-occurrence' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' $exactFrozenLine $false $exactFrozenLine),
  (New-TopologyCase 'same-frozen-occurrence-current-digest' 'docs/digests/PROJECT_DIGESTION_CURRENT.md' $exactFrozenLine $true),
  (New-TopologyCase 'casual-frozen-history-marker' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' "[FROZEN-HISTORY: casual] $retiredAlias" $true),
  (New-TopologyCase 'forged-duplicate-exact-marker' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' $exactFrozenLine $true),
  (New-TopologyCase 'worker-phase-label-canonical-comment' 'RMQ/Headlines/RMQ.lean' '/-- W99 current packet. -/' $true),
  (New-TopologyCase 'dated-snapshot-current-family-summary' 'docs/FAMILY_SUMMARY.md' 'Snapshot: 2026-01-01, current canonical story.' $true),
  (New-TopologyCase 'A01' 'scripts/headline_axiom_check.lean' '' $true '' 'A01' @(
      '\[m1-public-type-pin\] headline inventory is missing the literal M1 R3 expected-type anchor',
      '\[m1-public-type-pin\] headline inventory does not consume the paper theorem value at the frozen expected type')),
  (New-TopologyCase 'A02' 'scripts/gate.ps1' '' $true '' 'A02' @(
      '\[m1-mutation-gate\] aggregate gate is missing the literal M1 R3 runner anchor',
      '\[m1-mutation-gate\] aggregate gate does not invoke the committed M1 mutation runner'))
)

function Assert-ExactTopologyRegistry {
  if ($caseRegistry.Count -ne $expectedCaseIds.Count) {
    throw (
      "registry count mismatch: expected $($expectedCaseIds.Count), " +
      "observed $($caseRegistry.Count)")
  }
  $seen = [Collections.Generic.HashSet[string]]::new(
    [StringComparer]::Ordinal)
  for ($index = 0; $index -lt $expectedCaseIds.Count; $index += 1) {
    $entry = $caseRegistry[$index]
    if (-not $seen.Add([string]$entry.Id)) {
      throw "duplicate case ID $($entry.Id)"
    }
    if ([string]$entry.Id -cne $expectedCaseIds[$index]) {
      throw (
        "registry order/set mismatch at index $index`: expected " +
        "$($expectedCaseIds[$index]), observed $($entry.Id)")
    }
  }
  $rejects = @($caseRegistry | Where-Object { $_.Reject }).Count
  $accepts = @($caseRegistry | Where-Object { -not $_.Reject }).Count
  if ($rejects -ne 14 -or $accepts -ne 2) {
    throw "registry verdict totals mismatch: reject=$rejects accept=$accepts"
  }
}

try {
  Assert-ExactTopologyRegistry
} catch {
  Write-Host (
    "PAPER-TOPOLOGY-REGRESSION: FAIL [REGISTRY] $($_.Exception.Message)")
  exit 1
}

$selectedCases = @(
  if ($OnlyCase -eq '') {
    $caseRegistry
  } else {
    $caseRegistry | Where-Object { $_.Id -ceq $OnlyCase }
  }
)
if ($selectedCases.Count -ne $(if ($OnlyCase -eq '') { 16 } else { 1 })) {
  Write-Host (
    "PAPER-TOPOLOGY-REGRESSION: FAIL [SELECTOR] unknown case $OnlyCase; " +
    "available=$(@($caseRegistry | ForEach-Object { $_.Id }) -join ',')")
  exit 1
}

function Get-TrackedState {
  $stateScript = Join-Path ([IO.Path]::GetTempPath()) (
    'rmq-topology-state-' + [Guid]::NewGuid().ToString('N') + '.ps1')
  try {
    [IO.File]::WriteAllText($stateScript, @'
param([string]$LaunchReleasePath)
$ErrorActionPreference = 'Stop'
while (-not (Test-Path -LiteralPath $LaunchReleasePath -PathType Leaf)) {
  Start-Sleep -Milliseconds 10
}
& git -c core.excludesfile= -c core.autocrlf=false status --short --untracked-files=all
if ($LASTEXITCODE -ne 0) { throw "git status exited $LASTEXITCODE" }
Write-Output '---WORKTREE---'
& git -c core.excludesfile= -c core.autocrlf=false diff --raw --no-ext-diff --
if ($LASTEXITCODE -ne 0) { throw "git diff exited $LASTEXITCODE" }
Write-Output '---INDEX---'
& git -c core.excludesfile= -c core.autocrlf=false diff --cached --raw --no-ext-diff --
if ($LASTEXITCODE -ne 0) { throw "git diff --cached exited $LASTEXITCODE" }
'@, [Text.UTF8Encoding]::new($false))
    $result = Invoke-BoundedTool `
      -FilePath $shellPath `
      -Arguments @(
        '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $stateScript) `
      -Stage 'git-live-state' `
      -DeadlineSeconds $StageDeadlineSeconds `
      -ReleaseGatedScript
    if ($result.TimedOut) {
      throw "git live-state timed out after $StageDeadlineSeconds seconds"
    }
    if ($result.OutputLimitExceeded) {
      throw "git live-state exceeded $StageOutputLimitBytes bytes"
    }
    if ($result.ExitCode -ne 0) {
      throw "git live-state exited $($result.ExitCode): $($result.Output -join ' | ')"
    }
    return $result.Output -join [Environment]::NewLine
  } finally {
    Remove-Item -LiteralPath $stateScript -Force -ErrorAction SilentlyContinue
  }
}

function Get-LiveHashes {
  $result = [ordered]@{}
  foreach ($relativePath in $integrityPaths) {
    $fullPath = Join-Path $repoRoot $relativePath
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) {
      throw "missing integrity path $relativePath"
    }
    $result[$relativePath] =
      (Get-FileHash -Algorithm SHA256 -LiteralPath $fullPath).Hash
  }
  return $result
}

function Assert-LiveIntegrity([string]$Id) {
  if ((Get-TrackedState) -cne $baselineTrackedState) {
    throw "[$Id] tracked/status/index state changed"
  }
  $hashes = Get-LiveHashes
  foreach ($relativePath in $integrityPaths) {
    if ($hashes[$relativePath] -cne $baselineHashes[$relativePath]) {
      throw "[$Id] live hash changed for $relativePath"
    }
  }
}

function Invoke-BoundedTool(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$Stage,
    [int]$DeadlineSeconds,
    [switch]$ReleaseGatedScript) {
  if ($DeadlineSeconds -le 0) {
    throw "$Stage deadline must be positive"
  }
  $logStem = Join-Path ([IO.Path]::GetTempPath()) (
    'rmq-paper-topology-regression-r4-' + [Guid]::NewGuid().ToString('N'))
  $stdoutPath = $logStem + '.stdout.log'
  $stderrPath = $logStem + '.stderr.log'
  $specPath = $logStem + '.launch.json'
  $releasePath = $logStem + '.release'
  $bootstrapPath = $logStem + '.bootstrap.ps1'
  $process = $null
  $jobHandle = [IntPtr]::Zero
  $timedOut = $false
  $outputLimitExceeded = $false
  $terminatedIds = @()
  $exitCode = -1
  $output = @()
  $stopwatch = [Diagnostics.Stopwatch]::StartNew()
  try {
    $utf8 = [Text.UTF8Encoding]::new($false)
    if (-not $ReleaseGatedScript) {
      $launchSpec = [ordered]@{
        FilePath = $FilePath
        Arguments = @($Arguments)
        Environment = @{}
      }
      [IO.File]::WriteAllText(
        $specPath, ($launchSpec | ConvertTo-Json -Depth 5), $utf8)
      [IO.File]::WriteAllText($bootstrapPath, @'
param([string]$SpecPath, [string]$ReleasePath)
$ErrorActionPreference = 'Stop'
while (-not (Test-Path -LiteralPath $ReleasePath -PathType Leaf)) {
  Start-Sleep -Milliseconds 10
}
$spec = Get-Content -LiteralPath $SpecPath -Raw | ConvertFrom-Json
& ([string]$spec.FilePath) @([string[]]$spec.Arguments)
if ($null -eq $LASTEXITCODE) { exit 0 }
exit ([int]$LASTEXITCODE)
'@, $utf8)
    }
    if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) {
      $jobHandle = [RMQReplayJob]::CreateKillOnClose()
    }
    $startFilePath = if ($ReleaseGatedScript) { $FilePath } else { $shellPath }
    $startArguments = if ($ReleaseGatedScript) {
      @($Arguments) + @('-LaunchReleasePath', $releasePath)
    } else {
      @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $bootstrapPath, '-SpecPath', $specPath,
        '-ReleasePath', $releasePath)
    }
    $process = Start-Process -FilePath $startFilePath -ArgumentList $startArguments `
      -WorkingDirectory $repoRoot -PassThru -NoNewWindow `
      -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath
    if ($jobHandle -ne [IntPtr]::Zero) {
      [RMQReplayJob]::Assign($jobHandle, $process.Handle)
    }
    [void]$ownedRootIds.Add($process.Id)
    # Release only after the bootstrap root belongs to the private job.
    [IO.File]::WriteAllText($releasePath, 'assigned', $utf8)
    while (-not $process.WaitForExit(100)) {
      $bytes = 0L
      foreach ($path in @($stdoutPath, $stderrPath)) {
        if (Test-Path -LiteralPath $path -PathType Leaf) {
          $bytes += (Get-Item -LiteralPath $path).Length
        }
      }
      if ($bytes -gt $StageOutputLimitBytes) {
        $outputLimitExceeded = $true
        break
      }
      if ($stopwatch.Elapsed.TotalSeconds -ge $DeadlineSeconds) {
        $timedOut = $true
        break
      }
    }
    if ($timedOut -or $outputLimitExceeded) {
      $terminatedIds = @($process.Id)
      if ($jobHandle -ne [IntPtr]::Zero) {
        [RMQReplayJob]::Close($jobHandle)
        $jobHandle = [IntPtr]::Zero
      } else {
        Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
      }
      [void]$process.WaitForExit(10000)
    } else {
      $process.WaitForExit()
      $exitCode = [int]$process.ExitCode
      if ($jobHandle -ne [IntPtr]::Zero) {
        [RMQReplayJob]::Close($jobHandle)
        $jobHandle = [IntPtr]::Zero
      }
    }
    $finalBytes = 0L
    foreach ($path in @($stdoutPath, $stderrPath)) {
      if (Test-Path -LiteralPath $path -PathType Leaf) {
        $finalBytes += (Get-Item -LiteralPath $path).Length
      }
    }
    if ($finalBytes -gt $StageOutputLimitBytes) {
      $outputLimitExceeded = $true
    }
    if ($outputLimitExceeded) {
      $output = @("redirected output exceeded $StageOutputLimitBytes bytes")
    } else {
      foreach ($path in @($stdoutPath, $stderrPath)) {
        if (Test-Path -LiteralPath $path -PathType Leaf) {
          $text = $null
          for ($attempt = 0; $attempt -lt 100; $attempt += 1) {
            try {
              $text = [IO.File]::ReadAllText($path)
              break
            } catch [IO.IOException] {
              Start-Sleep -Milliseconds 100
            }
          }
          if ($null -eq $text) {
            throw "redirected output remained locked after owned process exit: $path"
          }
          $output += @([regex]::Split($text, '\r?\n') |
            Where-Object { $_ -ne '' })
        }
      }
    }
  } finally {
    $stopwatch.Stop()
    if ($jobHandle -ne [IntPtr]::Zero) {
      [RMQReplayJob]::Close($jobHandle)
      $jobHandle = [IntPtr]::Zero
    }
    if ($null -ne $process -and -not $process.HasExited) {
      $terminatedIds = @($process.Id)
      Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
      [void]$process.WaitForExit(10000)
    }
    if ($null -ne $process) {
      if ($null -ne (Get-Process -Id $process.Id -ErrorAction SilentlyContinue)) {
        throw "lint root process $($process.Id) survived"
      }
      [void]$ownedRootIds.Remove($process.Id)
    }
    Remove-Item -LiteralPath $stdoutPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $stderrPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $specPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $releasePath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $bootstrapPath -Force -ErrorAction SilentlyContinue
  }
  return [pscustomobject]@{
    ExitCode = $exitCode
    Output = @($output)
    TimedOut = $timedOut
    OutputLimitExceeded = $outputLimitExceeded
    TerminatedIds = $terminatedIds
    DurationSeconds = [Math]::Round($stopwatch.Elapsed.TotalSeconds, 3)
  }
}

function Invoke-BoundedLint([object]$Case) {
  $arguments = @(
    '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
    '-File', $lintPath,
    '-StageDeadlineSeconds', [string]([Math]::Max(1, $StageDeadlineSeconds - 15)),
    '-StageOutputLimitBytes', [string]$StageOutputLimitBytes)
  if ($Case.MutationCase -ne '') {
    $arguments += @('-MutationCase', [string]$Case.MutationCase)
  } else {
    $mutationTextBase64 = [Convert]::ToBase64String(
      [Text.Encoding]::UTF8.GetBytes([string]$Case.Text))
    $arguments += @(
      '-MutationPath', [string]$Case.Path,
      '-MutationTextBase64', $mutationTextBase64)
    if ($Case.RemoveText -ne '') {
      $removeTextBase64 = [Convert]::ToBase64String(
        [Text.Encoding]::UTF8.GetBytes([string]$Case.RemoveText))
      $arguments += @('-MutationRemoveTextBase64', $removeTextBase64)
    }
  }
  return Invoke-BoundedTool `
    -FilePath $shellPath `
    -Arguments $arguments `
    -Stage "topology-$($Case.Id)" `
    -DeadlineSeconds $StageDeadlineSeconds `
    -ReleaseGatedScript
}

$baselineTrackedState = Get-TrackedState
$baselineHashes = Get-LiveHashes

function Test-Mutation([object]$Case) {
  $problem = $null
  $result = $null
  try {
    Assert-LiveIntegrity "$($Case.Id)-before"
    $result = Invoke-BoundedLint $Case
    if ($result.TimedOut) {
      throw (
        "lint timed out after $StageDeadlineSeconds seconds; " +
        "terminated=$($result.TerminatedIds -join ',')")
    }
    if ($result.OutputLimitExceeded) {
      throw (
        "lint exceeded redirected output limit $StageOutputLimitBytes bytes; " +
        "terminated=$($result.TerminatedIds -join ',')")
    }
    $passed = if ($Case.Reject) {
      $result.ExitCode -ne 0
    } else {
      $result.ExitCode -eq 0
    }
    if (-not $passed) {
      $verdict = if ($Case.Reject) { 'REJECT' } else { 'ACCEPT' }
      throw "expected $verdict, observed exit $($result.ExitCode)"
    }
    $text = $result.Output -join [Environment]::NewLine
    foreach ($pattern in @($Case.ExpectedPatterns)) {
      if ($text -notmatch $pattern) {
        throw "intended rejection surface /$pattern/ was absent"
      }
    }
  } catch {
    $problem = $_.Exception.Message
  } finally {
    try {
      Assert-LiveIntegrity "$($Case.Id)-finally"
    } catch {
      if ($null -eq $problem) {
        $problem = $_.Exception.Message
      } else {
        $problem += '; ' + $_.Exception.Message
      }
    }
  }
  $script:executedCount += 1
  $executedIds.Add([string]$Case.Id)
  if ($null -ne $problem) {
    Write-Host (
      "PAPER-TOPOLOGY-REGRESSION: FAIL [$($Case.Id)] $problem")
    $script:failures += 1
    return
  }
  $verdict = if ($Case.Reject) { 'REJECT' } else { 'ACCEPT' }
  if ($Case.Reject) { $script:rejectCount += 1 } else { $script:acceptCount += 1 }
  Write-Host (
    "PAPER-TOPOLOGY-REGRESSION: PASS [$($Case.Id)] $verdict " +
    "exit=$($result.ExitCode) duration=$($result.DurationSeconds)s/" +
    "$StageDeadlineSeconds`s; tracked/index/hashes unchanged")
}

try {
  foreach ($case in $selectedCases) {
    Test-Mutation $case
  }
} finally {
  try {
    Assert-LiveIntegrity 'FINAL'
    if ($ownedRootIds.Count -ne 0) {
      throw "owned root registry is not empty: $($ownedRootIds -join ',')"
    }
  } catch {
    Write-Host "PAPER-TOPOLOGY-REGRESSION: FAIL [FINAL] $($_.Exception.Message)"
    $failures += 1
  }
}

if ($failures -gt 0) {
  Write-Host "PAPER-TOPOLOGY-REGRESSION: $failures failures"
  exit 1
}

$expectedIds = @($selectedCases | ForEach-Object { [string]$_.Id })
$expectedRejects = @($selectedCases | Where-Object { $_.Reject }).Count
$expectedAccepts = @($selectedCases | Where-Object { -not $_.Reject }).Count
if ($executedCount -ne $selectedCases.Count -or
    ($executedIds -join ',') -cne ($expectedIds -join ',') -or
    $rejectCount -ne $expectedRejects -or
    $acceptCount -ne $expectedAccepts) {
  Write-Host (
    'PAPER-TOPOLOGY-REGRESSION: FAIL [COUNTS] expected ' +
    "executed=$($selectedCases.Count) reject=$expectedRejects " +
    "accept=$expectedAccepts ids=$($expectedIds -join ','); observed " +
    "executed=$executedCount reject=$rejectCount accept=$acceptCount " +
    "ids=$($executedIds -join ',')")
  exit 1
}

Write-Host (
  'PAPER-TOPOLOGY-REGRESSION PASS ' +
  "($executedCount executed; $rejectCount reject; $acceptCount accept; " +
  'tracked/index/hashes unchanged; no owned process survives)')
exit 0

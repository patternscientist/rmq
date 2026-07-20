#!/usr/bin/env pwsh

param(
  [string]$MutationPath = '',
  [string]$MutationText = '',
  [string]$MutationRemoveText = '',
  [string]$MutationTextBase64 = '',
  [string]$MutationRemoveTextBase64 = '',
  [ValidateSet('', 'A01', 'A02')]
  [string]$MutationCase = '',
  [ValidateRange(1, 3600)]
  [int]$StageDeadlineSeconds = 300,
  [ValidateRange(4096, 16777216)]
  [int]$StageOutputLimitBytes = 4194304,
  [string]$LaunchReleasePath = ''
)

$ErrorActionPreference = 'Stop'
$failures = 0

if ($LaunchReleasePath -ne '') {
  while (-not (Test-Path -LiteralPath $LaunchReleasePath -PathType Leaf)) {
    Start-Sleep -Milliseconds 10
  }
}

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
  [StructLayout(LayoutKind.Sequential)] private struct IO {
    public ulong a,b,c,d,e,f;
  }
  [StructLayout(LayoutKind.Sequential)] private struct Basic {
    public long a,b; public uint flags;
    public UIntPtr c,d; public uint e; public UIntPtr f; public uint g,h;
  }
  [StructLayout(LayoutKind.Sequential)] private struct ExtendedInfo {
    public Basic basic; public IO io;
    public UIntPtr a,b,c,d;
  }
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern IntPtr CreateJobObject(IntPtr a, string n);
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern bool SetInformationJobObject(
    IntPtr j, int c, ref ExtendedInfo i, uint n);
  [DllImport("kernel32.dll", SetLastError=true)]
  private static extern bool AssignProcessToJobObject(IntPtr j, IntPtr p);
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
  public static void Assign(IntPtr j, IntPtr p) {
    if(!AssignProcessToJobObject(j,p)) throw new Win32Exception(Marshal.GetLastWin32Error());
  }
  public static void Close(IntPtr j) {
    if(j!=IntPtr.Zero && !CloseHandle(j)) throw new Win32Exception(Marshal.GetLastWin32Error());
  }
}
'@
}

function Normalize-RepoPath([string]$Path) {
  $normalized = $Path -replace '\\', '/'
  while ($normalized.StartsWith('./')) {
    $normalized = $normalized.Substring(2)
  }
  return $normalized
}

$MutationPath = Normalize-RepoPath $MutationPath
if ($MutationTextBase64 -ne '') {
  if ($MutationText -ne '') {
    throw 'specify MutationText or MutationTextBase64, not both'
  }
  $MutationText = [Text.Encoding]::UTF8.GetString(
    [Convert]::FromBase64String($MutationTextBase64))
}
if ($MutationRemoveTextBase64 -ne '') {
  if ($MutationRemoveText -ne '') {
    throw 'specify MutationRemoveText or MutationRemoveTextBase64, not both'
  }
  $MutationRemoveText = [Text.Encoding]::UTF8.GetString(
    [Convert]::FromBase64String($MutationRemoveTextBase64))
}
if ($MutationCase -ceq 'A01') {
  $MutationPath = 'scripts/headline_axiom_check.lean'
} elseif ($MutationCase -ceq 'A02') {
  $MutationPath = 'scripts/gate.ps1'
}

$frozenSnapshotMarker = '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT -->'
$frozenSnapshotLines = [ordered]@{
  'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' =
    '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'
  'docs/digests/PROJECT_STATE_2026_06_28.md' =
    '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> `RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery` abbreviates'
}

function Fail([string]$Message) {
  Write-Host "PAPER-TOPOLOGY: FAIL $Message"
  $script:failures += 1
}

function Invoke-BoundedLintTool(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$Stage,
    [hashtable]$Environment = @{}) {
  if ($StageDeadlineSeconds -le 0) {
    throw "$Stage deadline must be positive"
  }
  $logStem = [IO.Path]::Combine(
    [IO.Path]::GetTempPath(),
    'rmq-paper-topology-r4-' + [Guid]::NewGuid().ToString('N'))
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
    $launchSpec = [ordered]@{
      FilePath = $FilePath
      Arguments = @($Arguments)
      Environment = $Environment
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
foreach ($property in $spec.Environment.PSObject.Properties) {
  [Environment]::SetEnvironmentVariable(
    $property.Name, [string]$property.Value, 'Process')
}
& ([string]$spec.FilePath) @([string[]]$spec.Arguments)
if ($null -eq $LASTEXITCODE) { exit 0 }
exit ([int]$LASTEXITCODE)
'@, $utf8)
    if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) {
      $jobHandle = [RMQReplayJob]::CreateKillOnClose()
    }
    $shellPath = (Get-Process -Id $PID).Path
    $process = Start-Process -FilePath $shellPath -ArgumentList @(
      '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
      '-File', $bootstrapPath, '-SpecPath', $specPath,
      '-ReleasePath', $releasePath) `
      -WorkingDirectory (Get-Location).Path -PassThru -NoNewWindow `
      -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath
    if ($jobHandle -ne [IntPtr]::Zero) {
      [RMQReplayJob]::Assign($jobHandle, $process.Handle)
    }
    # The requested tool cannot spawn before the bootstrap root is job-owned.
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
      if ($stopwatch.Elapsed.TotalSeconds -ge $StageDeadlineSeconds) {
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
    if ($null -ne $process -and
        $null -ne (Get-Process -Id $process.Id -ErrorAction SilentlyContinue)) {
      throw "$Stage owned root process $($process.Id) survived cleanup"
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

function Require-File([string]$Path) {
  if (-not (Test-Path -LiteralPath $Path)) {
    Fail "missing required file $Path"
    return $false
  }
  return $true
}

function Remove-ExactVirtualBlock(
    [string]$Text,
    [string]$StartMarker,
    [string]$EndMarker,
    [string]$CaseId) {
  $start = $Text.IndexOf($StartMarker, [StringComparison]::Ordinal)
  if ($start -lt 0) {
    throw "$CaseId virtual block start not found"
  }
  if ($Text.IndexOf(
      $StartMarker, $start + $StartMarker.Length,
      [StringComparison]::Ordinal) -ge 0) {
    throw "$CaseId virtual block start is not unique"
  }
  $end = $Text.IndexOf($EndMarker, $start, [StringComparison]::Ordinal)
  if ($end -lt 0) {
    throw "$CaseId virtual block end not found"
  }
  if ($Text.IndexOf(
      $EndMarker, $end + $EndMarker.Length,
      [StringComparison]::Ordinal) -ge 0) {
    throw "$CaseId virtual block end is not unique"
  }
  $end += $EndMarker.Length
  while ($end -lt $Text.Length -and
      ($Text[$end] -eq [char]13 -or $Text[$end] -eq [char]10)) {
    $end += 1
  }
  return $Text.Remove($start, $end - $start)
}

function Read-Text([string]$Path) {
  $normalized = Normalize-RepoPath $Path
  $text = Get-Content -Raw -LiteralPath $normalized
  if ($MutationPath -ne '' -and $normalized -eq $MutationPath) {
    if ($MutationCase -ceq 'A01') {
      $text = Remove-ExactVirtualBlock `
        $text `
        '-- M1R3-PUBLIC-TYPE-PIN-ANCHOR' `
        'end M1PublicExpectedTypeCheck' `
        'A01'
    } elseif ($MutationCase -ceq 'A02') {
      $text = Remove-ExactVirtualBlock `
        $text `
        '# M1R3-MUTATION-RUNNER-GATE-ANCHOR' `
        'if ($LASTEXITCODE -ne 0) { Fail "m1_certificate_mutation_regression.ps1 found issues" }' `
        'A02'
    }
    if ($MutationRemoveText -ne '') {
      if (-not $text.Contains($MutationRemoveText)) {
        throw "mutation removal text not found in $normalized"
      }
      $text = $text.Replace($MutationRemoveText, '')
    }
    $text += [Environment]::NewLine + $MutationText + [Environment]::NewLine
  }
  return $text
}

function Read-Lines([string]$Path) {
  return [regex]::Split((Read-Text $Path), '\r?\n')
}

function Is-PreciselyFrozenSnapshotLine([string]$Path, [string]$Line) {
  $normalized = Normalize-RepoPath $Path
  return (
    $frozenSnapshotLines.Contains($normalized) -and
    $Line -ceq $frozenSnapshotLines[$normalized])
}

function Run-LeanResolution(
    [string]$Import,
    [System.Collections.Generic.HashSet[string]]$Names,
    [string]$Role) {
  $lines = [System.Collections.Generic.List[string]]::new()
  $lines.Add("import $Import")
  foreach ($name in @($Names | Sort-Object)) {
    $lines.Add("#check RMQ.Headlines.$name")
  }

  $tempName = "rmq-paper-topology-{0}.lean" -f [Guid]::NewGuid().ToString('N')
  $tempPath = [IO.Path]::Combine([IO.Path]::GetTempPath(), $tempName)
  $encoding = New-Object System.Text.UTF8Encoding($false)
  try {
    [IO.File]::WriteAllText(
      $tempPath,
      ($lines -join [Environment]::NewLine) + [Environment]::NewLine,
      $encoding)
    $repoRoot = [IO.Path]::GetFullPath((Get-Location).Path)
    $toolchainSpec = (
      [IO.File]::ReadAllText((Join-Path $repoRoot 'lean-toolchain'))).Trim()
    $toolchainDirectoryName =
      $toolchainSpec.Replace('/', '--').Replace(':', '---')
    $toolchainRoot = Join-Path (
      Join-Path $env:USERPROFILE '.elan\toolchains') $toolchainDirectoryName
    $leanExe = Join-Path (Join-Path $toolchainRoot 'bin') 'lean.exe'
    $projectLeanPath = Join-Path $repoRoot '.lake/build/lib/lean'
    $toolchainLeanPath = Join-Path $toolchainRoot 'lib/lean'
    if (-not (Test-Path -LiteralPath $leanExe -PathType Leaf)) {
      throw "installed pinned Lean binary missing: $leanExe"
    }
    $result = Invoke-BoundedLintTool `
      -FilePath $leanExe `
      -Arguments @("--root=$repoRoot", $tempPath) `
      -Stage "$Role-resolution" `
      -Environment @{
        LEAN_PATH = $projectLeanPath + [IO.Path]::PathSeparator +
          $toolchainLeanPath
      }
    if ($result.TimedOut) {
      Fail (
        "[$Role-resolution] timed out after $StageDeadlineSeconds seconds; " +
        "terminated=$($result.TerminatedIds -join ',')")
    } elseif ($result.OutputLimitExceeded) {
      Fail (
        "[$Role-resolution] exceeded redirected output limit " +
        "$StageOutputLimitBytes bytes; terminated=$($result.TerminatedIds -join ',')")
    } elseif ($result.ExitCode -ne 0) {
      Fail "[$Role-resolution] documentary headline identifiers do not resolve under import $Import"
      foreach ($line in @($result.Output | Where-Object { $_ -match 'error:' })) {
        Write-Host "PAPER-TOPOLOGY: LEAN $line"
      }
    }
  } finally {
    if (Test-Path -LiteralPath $tempPath) {
      Remove-Item -LiteralPath $tempPath -Force
    }
  }
}

$canonicalModule = 'RMQ/Headlines/RMQ.lean'
$compatibilityModule = 'RMQ/Headlines/RMQCompatibility.lean'
$paperRoot = 'RMQPaper.lean'
$aggregateModule = 'RMQ/Headlines.lean'
$headlineInventory = 'scripts/headline_axiom_check.lean'
$gateScript = 'scripts/gate.ps1'
$m1MutationRunner = 'scripts/m1_certificate_mutation_regression.ps1'
$currentPublicationDigest =
  'docs/digests/PROJECT_DIGESTION_CURRENT.md'

$currentLeanSurfaces = @($canonicalModule, $paperRoot, $headlineInventory)
$publicClaimSurfaces = @(
  'README.md',
  'artifact/CLAIMS.md',
  'docs/FAMILY_SUMMARY.md',
  'docs/PAPER_CLAIM_CORRESPONDENCE.md',
  'docs/PAPER_THEOREM_MAP.md',
  'docs/PAPER_MAIN_THEOREM.md',
  'docs/PAPER_MODEL_ADEQUACY.md',
  'docs/WHAT_IS_PROVED.md',
  $currentPublicationDigest
)
$paperDocumentSurfaces = @(
  'docs/PAPER_CLAIM_CORRESPONDENCE.md',
  'docs/PAPER_THEOREM_MAP.md',
  'docs/PAPER_MAIN_THEOREM.md',
  'docs/PAPER_MODEL_ADEQUACY.md',
  $currentPublicationDigest
)
$currentLifecycleSurfaces = @($canonicalModule) + $publicClaimSurfaces

$requiredFiles = @(
  $canonicalModule,
  $compatibilityModule,
  $paperRoot,
  $aggregateModule,
  $headlineInventory,
  $gateScript,
  $m1MutationRunner
) + $publicClaimSurfaces

$requiredFiles += @($frozenSnapshotLines.Keys)

foreach ($path in $requiredFiles) {
  [void](Require-File $path)
}

if ($failures -gt 0) {
  exit 1
}

# M1 R3 public-dependency enforcement is itself part of the paper topology.
# Require both the frozen expected-type consumer and the literal aggregate-gate
# runner invocation; declaration-name or current-type-only checks are
# insufficient.
$headlineInventoryText = Read-Text $headlineInventory
$gateScriptText = Read-Text $gateScript
$m1MutationRunnerText = Read-Text $m1MutationRunner
$m1PublicTypePinAnchor = '-- M1R3-PUBLIC-TYPE-PIN-ANCHOR'
$m1GateAnchor = '# M1R3-MUTATION-RUNNER-GATE-ANCHOR'

if (-not $headlineInventoryText.Contains($m1PublicTypePinAnchor)) {
  Fail '[m1-public-type-pin] headline inventory is missing the literal M1 R3 expected-type anchor'
}
if ($headlineInventoryText -notmatch
    '(?s)example\s*:\s*M1ReviewerNativeExpectedPaperType\s*:=\s*RMQ\.Headlines\.listIntSuccinctRMQPaperMainTheorem') {
  Fail '[m1-public-type-pin] headline inventory does not consume the paper theorem value at the frozen expected type'
}
if (-not $gateScriptText.Contains($m1GateAnchor)) {
  Fail '[m1-mutation-gate] aggregate gate is missing the literal M1 R3 runner anchor'
}
if ($gateScriptText -notmatch
    '(?m)^& "\$PSScriptRoot\\m1_certificate_mutation_regression\.ps1"\s*$') {
  Fail '[m1-mutation-gate] aggregate gate does not invoke the committed M1 mutation runner'
}
foreach ($anchor in @(
    'REPLAY-EXACT-REGISTRY',
    'REPLAY-SELECTOR-NONVACUITY',
    'REPLAY-SUBPROCESS-DEADLINE')) {
  if (-not $m1MutationRunnerText.Contains($anchor)) {
    Fail "[m1-mutation-runner] committed runner is missing $anchor"
  }
}
if ($m1MutationRunnerText -notmatch
    '(?s)Assert-ExactRegistry\s+\$caseRegistry.*omitted-middle-F21.*duplicated-middle-F21') {
  Fail '[m1-mutation-runner] exact registry and middle-drift controls are not wired'
}
if ($m1MutationRunnerText -notmatch
    '(?s)executed registry mismatch.*verdict totals mismatch') {
  Fail '[m1-mutation-runner] exact executed-order and verdict-total checks are not wired'
}

if ($failures -gt 0) {
  exit 1
}

# Every key is a spelling removed from the public API.  The value is the
# checked current or explicitly historical replacement used in diagnostics.
$retiredAliasReplacements = [ordered]@{
  'succinctRMQTwoNPlusOConstantQuery' =
    'succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile or succinctRMQLegacy196727DirectTwoNPlusOConstantQuery'
  'succinctRMQTwoNPlusOConstantQueryInterpreted' =
    'succinctRMQLegacy196727InterpretedTwoNPlusOConstantQuery'
  'succinctRMQTwoNPlusOConstantQueryLeafTrace' =
    'succinctRMQLegacy196727LeafTraceTwoNPlusOConstantQuery'
  'succinctRMQTwoNPlusOConstantQueryWordTrace' =
    'succinctRMQLegacy196727WordTraceTwoNPlusOConstantQuery'
  'succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime' =
    'succinctRMQLegacy196727LargeRegimeWordTraceTwoNPlusOConstantQuery'
  'succinctRMQTwoNPlusOConstantQueryGlobalWordTraceLargeRegime' =
    'succinctRMQLegacy196727LargeRegimeGlobalWordTraceTwoNPlusOConstantQuery'
  'listIntSuccinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal' =
    'listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal, listIntSuccinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal (historical 328), or listIntSuccinctRMQCompatibility352FinalFullModelCostLeOfFootprintGlobal (live expression)'
  'succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe' =
    'succinctRMQWholeQueryGlobalWordTraceCostedCostLe, succinctRMQCompatibility328WholeQueryGlobalWordTraceCostedCostLe (historical 328), or succinctRMQCompatibility352WholeQueryGlobalWordTraceCostedCostLe (live expression)'
  'succinctRMQCanonicalTransitionalQueryCostEq' =
    'succinctRMQQueryCostEq, succinctRMQCompatibility328QueryCostEq (historical 328), or succinctRMQCompatibility352QueryCostEq (live 352)'
  'succinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal' =
    'succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal, succinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal (historical 328), or succinctRMQCompatibility352FinalFullModelCostLeOfFootprintGlobal (live expression)'
  'succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory' =
    'succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreExecutionStory'
  'succinctRMQLargeRegimeGlobalPayloadStoreBoundedExecutionStory' =
    'succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreBoundedExecutionStory'
  'listIntSuccinctRMQEventValueProducerProvenanceOfValid' =
    'listIntSuccinctRMQOccurrenceProvenanceOfValid or listIntSuccinctRMQCompatibilityW18EventValueProducerProvenanceOfValid'
  'succinctRMQReviewerEveryReadEventValueProducerProvenance' =
    'succinctRMQReviewerEveryReadOccurrenceProvenance or succinctRMQCompatibilityW18ReviewerEveryReadEventValueProducerProvenance'
  'succinctRMQReviewerCountedSourceComponentMayPath' =
    'succinctRMQReviewerCountedSourceSuccessfulClosedValidOccurrence or succinctRMQCompatibilityW18ReviewerCountedSourceComponentMayPath'
  'succinctRMQReviewerSharedBPConsumerComponentPath' =
    'succinctRMQReviewerSharedBPConsumerSuccessfulClosedValidOccurrence or succinctRMQCompatibilityW18ReviewerSharedBPConsumerComponentPath'
  'succinctRMQProgramEventValueProducer' =
    'succinctRMQProgramOccurrenceActualProducer or succinctRMQCompatibilityW18ProgramEventValueProducer'
}

$retiredSourcePattern =
  'builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_(?:profile|whole_query_(?:interpreted|leaf_trace|word_trace(?:_large_regime)?|global_word_trace_large_regime)_profile)'
$oldRegimePattern =
  '(?i)(?:\b(?:196727|328|352|118|4144)\b|2\s*\^\s*128|zero[- ]?block|\bReady\b|LargeRegime|large[- ]regime|CanonicalTransitional)'

# These files intentionally contain the removed vocabulary as enforcement
# data.  They are not documentary theorem references.
$enforcementPaths = @(
  'docs/internal/CLAIM_DRIFT_POLICY.json',
  'docs/internal/CLAIM_DRIFT_POLICY.md',
  'scripts/claim_drift_policy_regression.ps1',
  'scripts/paper_topology_lint.ps1',
  'scripts/paper_topology_lint_regression.ps1'
)

$gitPath = (Get-Command git -ErrorAction Stop).Source
$gitFiles = Invoke-BoundedLintTool `
  -FilePath $gitPath `
  -Arguments @('ls-files') `
  -Stage 'repository-git-ls-files'
if ($gitFiles.TimedOut) {
  Fail "[repository-search] git ls-files timed out after $StageDeadlineSeconds seconds"
  $trackedFiles = @()
} elseif ($gitFiles.OutputLimitExceeded) {
  Fail "[repository-search] git ls-files exceeded $StageOutputLimitBytes bytes"
  $trackedFiles = @()
} elseif ($gitFiles.ExitCode -ne 0) {
  Fail '[repository-search] git ls-files failed'
  $trackedFiles = @()
} else {
  $trackedFiles = @($gitFiles.Output | ForEach-Object { Normalize-RepoPath $_ })
}
$trackedFiles = @(
  $trackedFiles + $requiredFiles + @($MutationPath) |
    Where-Object { $_ -ne '' -and (Test-Path -LiteralPath $_) } |
    Sort-Object -Unique
)

# Repository-wide migration closure: outside exact enforcement files and an
# exact marker on one line of one registered June snapshot, no removed spelling
# may survive in tracked text. No directory or casual history word grants an
# allowance.
$textExtensions = @('.lean', '.md', '.ps1', '.json', '.toml', '.yml', '.yaml', '.sh')
$frozenSnapshotLineCounts = @{}
foreach ($path in $frozenSnapshotLines.Keys) {
  $frozenSnapshotLineCounts[$path] = 0
}
foreach ($path in $trackedFiles) {
  if ($enforcementPaths -contains $path) { continue }
  if ($textExtensions -notcontains [IO.Path]::GetExtension($path)) { continue }
  if (-not (Test-Path -LiteralPath $path)) { continue }

  $lineNumber = 0
  foreach ($line in Read-Lines $path) {
    $lineNumber += 1
    $isPreciselyFrozen = Is-PreciselyFrozenSnapshotLine $path $line
    if ($line.Contains($frozenSnapshotMarker) -and -not $isPreciselyFrozen) {
      Fail "[frozen-marker-scope] $path`:$lineNumber has a malformed or misplaced snapshot marker"
    }
    if ($isPreciselyFrozen) {
      $frozenSnapshotLineCounts[$path] += 1
      continue
    }
    foreach ($name in $retiredAliasReplacements.Keys) {
      if ($line -match ([regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
        Fail "[removed-spelling] $path`:$lineNumber contains $name; use $($retiredAliasReplacements[$name])"
      }
    }
  }
}

foreach ($path in $frozenSnapshotLines.Keys) {
  if ($frozenSnapshotLineCounts[$path] -ne 1) {
    Fail "[frozen-marker-metadata] registered snapshot $path must have exactly one exact frozen line; found $($frozenSnapshotLineCounts[$path])"
  }
}

foreach ($path in $currentLeanSurfaces) {
  $text = Read-Text $path
  if ($text -match $retiredSourcePattern) {
    Fail "[retired-source] $path directly cites a retired source profile"
  }
  if ($text -match $oldRegimePattern) {
    Fail "[old-paper-regime] $path contains an old cost/regime token"
  }
}

foreach ($path in $publicClaimSurfaces) {
  $lineNumber = 0
  foreach ($line in Read-Lines $path) {
    $lineNumber += 1
    if ($line -match '^\s*\|' -and $line -match $retiredSourcePattern) {
      Fail "[retired-source-row] $path`:$lineNumber presents a retired source profile in a current table row"
    }
    if (
      $line -match '^\s*\|' -and
      $line -match '(?:RMQ\.Headlines\.(?:succinctRMQ|listIntSuccinctRMQ)|Headlines\.(?:succinctRMQ|listIntSuccinctRMQ))' -and
      $line -match $oldRegimePattern
    ) {
      Fail "[old-current-row] $path`:$lineNumber has an old cost/regime token in a current headline row"
    }
  }
}

# Current reader-facing surfaces must not expose proof-campaign labels or embed
# a dated snapshot preamble. These are narrow lifecycle tripwires, not an
# attempt to infer publication roles from arbitrary prose.
$staleLifecyclePattern =
  '(?m)(?:\b[WU][0-9]+\b|^\s*Snapshot:\s*20[0-9]{2}-[0-9]{2}-[0-9]{2})'
foreach ($path in $currentLifecycleSurfaces) {
  if ((Read-Text $path) -match $staleLifecyclePattern) {
    Fail "[stale-lifecycle] $path contains a worker-phase label or dated snapshot preamble"
  }
}

$paperText = Read-Text $paperRoot
if ($paperText -notmatch '(?m)^import RMQ\.Headlines\.RMQ\s*$') {
  Fail "[paper-import] $paperRoot must import RMQ.Headlines.RMQ"
}
if ($paperText -match '(?m)^import RMQ\.Headlines(?:\.RMQCompatibility)?\s*$') {
  Fail "[paper-import] $paperRoot imports a broad or compatibility headline surface"
}

$aggregateText = Read-Text $aggregateModule
if ($aggregateText -notmatch '(?m)^import RMQ\.Headlines\.RMQ\s*$') {
  Fail "[broad-import] $aggregateModule must explicitly import the canonical RMQ surface"
}
if ($aggregateText -notmatch '(?m)^import RMQ\.Headlines\.RMQCompatibility\s*$') {
  Fail "[broad-import] $aggregateModule must explicitly import the compatibility RMQ surface"
}

$compatibilityText = Read-Text $compatibilityModule
foreach ($name in $retiredAliasReplacements.Keys) {
  if ($compatibilityText -match ('(?m)^\s*(?:abbrev|theorem)\s+' +
      [regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
    Fail "[unqualified-compatibility] $compatibilityModule preserves removed alias $name"
  }
}

$compatibilityNames = [System.Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
foreach ($match in [regex]::Matches(
    $compatibilityText,
    '(?m)^\s*(?:abbrev|theorem)\s+([A-Za-z][A-Za-z0-9_]*)')) {
  $name = $match.Groups[1].Value
  [void]$compatibilityNames.Add($name)
  if ($name -notmatch '(?:Compatibility|Legacy)') {
    Fail "[compatibility-name] $compatibilityModule declaration $name lacks Compatibility or Legacy"
  }
}

# Compatibility declarations may be documented as history on broad surfaces,
# but may not occur in the canonical module, paper root, headline inventory,
# or current paper-claim surfaces.
foreach ($path in @($currentLeanSurfaces + $publicClaimSurfaces)) {
  $text = Read-Text $path
  foreach ($name in $compatibilityNames) {
    if ($text -match ([regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
      Fail "[compatibility-current-anchor] $path presents compatibility declaration $name as a current paper anchor"
    }
  }
}

# A structural rejection is already conclusive. Avoid paying for documentary
# symbol collection and compiler-backed resolution on known-bad mutations;
# successful repository states still run the complete checked path below.
if ($failures -gt 0) {
  Write-Host "PAPER-TOPOLOGY: $failures failures"
  exit 1
}

$canonicalAlias =
  'succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile'
$weightLengthAlias =
  'succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqTraceLength'
$weightCostAlias =
  'succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumEqCost'
$weightBoundAlias =
  'succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe210'
$readWordOnlyAlias =
  'succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly'
$canonicalText = Read-Text $canonicalModule
$inventoryText = Read-Text $headlineInventory
foreach ($anchor in @($canonicalAlias, $weightLengthAlias, $weightCostAlias, $weightBoundAlias, $readWordOnlyAlias)) {
  if ($canonicalText -notmatch [regex]::Escape($anchor)) {
    Fail "[canonical-anchor] $canonicalModule is missing required anchor $anchor"
  }
  if ($inventoryText -notmatch
      ('#print axioms RMQ\.Headlines\.' + [regex]::Escape($anchor))) {
    Fail "[headline-inventory] $headlineInventory does not print required anchor $anchor"
  }
}

$legacyAnchors = @(
  'succinctRMQLegacy196727DirectTwoNPlusOConstantQuery',
  'succinctRMQLegacy196727InterpretedTwoNPlusOConstantQuery',
  'succinctRMQLegacy196727LeafTraceTwoNPlusOConstantQuery',
  'succinctRMQLegacy196727WordTraceTwoNPlusOConstantQuery',
  'succinctRMQLegacy196727LargeRegimeWordTraceTwoNPlusOConstantQuery',
  'succinctRMQLegacy196727LargeRegimeGlobalWordTraceTwoNPlusOConstantQuery'
)
foreach ($anchor in $legacyAnchors) {
  if ($compatibilityText -notmatch
      ('(?m)^\s*abbrev\s+' + [regex]::Escape($anchor) + '\b')) {
    Fail "[legacy-anchor] $compatibilityModule is missing retained historical alias $anchor"
  }
}

# Extract single-token documentary identifiers from every tracked Markdown
# file, including the current publication digest and audit reports. Only an
# exact registered snapshot line is omitted. Broad documentation must resolve
# after `import RMQ.Headlines`; the RMQ paper maps additionally resolve after
# the narrower `import RMQPaper`.
$broadDocumentNames = [System.Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
$paperDocumentNames = [System.Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
$canonicalHeadlineNames = [System.Collections.Generic.HashSet[string]]::new(
  [StringComparer]::Ordinal)
foreach ($match in [regex]::Matches(
    $canonicalText,
    '(?m)^\s*(?:abbrev|theorem|def)\s+([A-Za-z_][A-Za-z0-9_]*)\b')) {
  [void]$canonicalHeadlineNames.Add($match.Groups[1].Value)
}
$headlinePattern =
  '(?<![A-Za-z0-9_])(?:RMQ\.)?Headlines\.([a-z][A-Za-z0-9_]*)'

foreach ($path in $trackedFiles) {
  if ([IO.Path]::GetExtension($path) -ne '.md') { continue }
  if (-not (Test-Path -LiteralPath $path)) { continue }

  foreach ($line in Read-Lines $path) {
    if (Is-PreciselyFrozenSnapshotLine $path $line) { continue }
    foreach ($match in [regex]::Matches($line, $headlinePattern)) {
      $name = $match.Groups[1].Value
      # File references such as `RMQ.Headlines.lean` share the namespace prefix
      # but are not documentary declaration identifiers.
      if ($name -in @('lean', 'md')) { continue }
      [void]$broadDocumentNames.Add($name)
      # RMQPaper deliberately excludes standalone rank/select and BP-navigation
      # spoke headlines.  Resolve canonical RMQ declarations under RMQPaper;
      # the broad resolution above covers every other documented headline.
      if (($paperDocumentSurfaces -contains $path) -and
          ($path -eq $currentPublicationDigest -or
            $canonicalHeadlineNames.Contains($name))) {
        [void]$paperDocumentNames.Add($name)
      }
    }
  }
}

if ($failures -eq 0) {
  Run-LeanResolution 'RMQ.Headlines' $broadDocumentNames 'broad-documentary-symbol'
  Run-LeanResolution 'RMQPaper' $paperDocumentNames 'paper-documentary-symbol'
}

if ($failures -gt 0) {
  Write-Host "PAPER-TOPOLOGY: $failures failures"
  exit 1
}

Write-Host (
  'PAPER-TOPOLOGY PASS ' +
  "($($broadDocumentNames.Count) broad documentary identifiers; " +
  "$($paperDocumentNames.Count) paper identifiers resolved)"
)
exit 0

#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$OnlyCase = '',
  [ValidateRange(1, 3600)]
  [int]$StageDeadlineSeconds = 300,
  [ValidateRange(4096, 16777216)]
  [int]$StageOutputLimitBytes = 4194304,
  [ValidateRange(1, 30)]
  [int]$SelfTestDeadlineSeconds = 20,
  [switch]$RegistrySelfTestOnly,
  [switch]$SelectorSelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [switch]$StartupSmokeOnly
)

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

# Some managed Windows launch environments contain both `Path` and `PATH`.
# Windows PowerShell's Start-Process rejects that duplicate case-insensitive
# key, so remove only the redundant uppercase entry in this runner process.
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
  private const int JobObjectExtendedLimitInformation = 9;
  private const uint JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000;

  [StructLayout(LayoutKind.Sequential)]
  private struct IO_COUNTERS {
    public ulong ReadOperationCount, WriteOperationCount, OtherOperationCount;
    public ulong ReadTransferCount, WriteTransferCount, OtherTransferCount;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct JOBOBJECT_BASIC_LIMIT_INFORMATION {
    public long PerProcessUserTimeLimit, PerJobUserTimeLimit;
    public uint LimitFlags;
    public UIntPtr MinimumWorkingSetSize, MaximumWorkingSetSize;
    public uint ActiveProcessLimit;
    public UIntPtr Affinity;
    public uint PriorityClass, SchedulingClass;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
    public JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
    public IO_COUNTERS IoInfo;
    public UIntPtr ProcessMemoryLimit, JobMemoryLimit, PeakProcessMemoryUsed;
    public UIntPtr PeakJobMemoryUsed;
  }

  [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
  private static extern IntPtr CreateJobObject(IntPtr attributes, string name);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool SetInformationJobObject(
    IntPtr job, int infoClass,
    ref JOBOBJECT_EXTENDED_LIMIT_INFORMATION info, uint length);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool CloseHandle(IntPtr handle);

  public static IntPtr CreateKillOnClose() {
    IntPtr job = CreateJobObject(IntPtr.Zero, null);
    if (job == IntPtr.Zero) throw new Win32Exception(Marshal.GetLastWin32Error());
    var info = new JOBOBJECT_EXTENDED_LIMIT_INFORMATION();
    info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!SetInformationJobObject(
        job, JobObjectExtendedLimitInformation, ref info,
        (uint)Marshal.SizeOf(typeof(JOBOBJECT_EXTENDED_LIMIT_INFORMATION)))) {
      int error = Marshal.GetLastWin32Error();
      CloseHandle(job);
      throw new Win32Exception(error);
    }
    return job;
  }

  public static void Assign(IntPtr job, IntPtr process) {
    if (!AssignProcessToJobObject(job, process))
      throw new Win32Exception(Marshal.GetLastWin32Error());
  }

  public static void Close(IntPtr job) {
    if (job != IntPtr.Zero && !CloseHandle(job))
      throw new Win32Exception(Marshal.GetLastWin32Error());
  }
}
'@
}

$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
Push-Location $repoRoot

$encoding = [Text.UTF8Encoding]::new($false)
$pathSeparator = [IO.Path]::PathSeparator
$lf = [string][char]10
$failures = 0
$passes = 0
$executedIds = [Collections.Generic.List[string]]::new()
$rejectPasses = 0
$acceptPasses = 0

$finalModelPath = 'RMQ/Core/SuccinctFinalModelAdequacy.lean'
$classicPath = 'RMQ/Core/SuccinctRMQClassic.lean'
$headlinePath = 'RMQ/Headlines/RMQ.lean'
$checkerPath = 'scripts/headline_axiom_check.lean'
$reviewerPhysicalPath = 'RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean'
$semanticProvenancePath = 'RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean'
$ramPath = 'RMQ/Core/SuccinctFinalRAM.lean'
$shadowSources = @(
  $finalModelPath,
  $classicPath,
  $headlinePath,
  $checkerPath
)
$integrityPaths = @(
  $finalModelPath,
  $classicPath,
  $headlinePath,
  $checkerPath,
  $reviewerPhysicalPath,
  $semanticProvenancePath,
  $ramPath,
  'scripts/m1_certificate_mutation_regression.ps1',
  'scripts/gate.ps1',
  'scripts/paper_topology_lint.ps1',
  'scripts/paper_topology_lint_regression.ps1',
  'docs/internal/M1_REVIEWER_NATIVE_ADEQUACY_ACCEPTANCE_MATRIX.md'
)

function New-ReplayCase(
    [string]$Id,
    [string]$Verdict,
    [string]$Field = '') {
  return [pscustomobject]@{
    Id = $Id
    Verdict = $Verdict
    Field = $Field
  }
}

# REPLAY-EXACT-REGISTRY
# This independent expected map is deliberately separate from the executable
# registry.  A field rename, reorder, omission, or duplicate must disagree with
# one of these frozen literals before any Lean child starts.
$expectedFieldMap = [ordered]@{
  F01 = 'physical_words_erase_canonical_payload'
  F02 = 'physical_execution_is_canonical_trace'
  F03 = 'canonical_trace_is_first_order_controller'
  F04 = 'canonical_physical_store_adapts_to_global_store'
  F05 = 'physical_events_match_canonical_store'
  F06 = 'successful_physical_reads_backed_by_canonical_words'
  F07 = 'ordered_physical_footprint_recorded'
  F08 = 'supplied_execution_eq_of_exact_read_agreement'
  F09 = 'physical_value_is_translated_supplied_store_value'
  F10 = 'physical_value_dependency'
  F11 = 'no_synthetic_physical_event'
  F12 = 'certificate_weight_eq_trace_length'
  F13 = 'certificate_weight_eq_cost'
  F14 = 'certificate_weight_le_210'
  F15 = 'reviewer_capacity_linear'
  F16 = 'physical_words_fit_capacity'
  F17 = 'reviewer_word_bits_logarithmic'
  F18 = 'input_operands_fit_reviewer_word'
  F19 = 'segment_encodings_fit_reviewer_word'
  F20 = 'every_physical_address_fits_reviewer_word'
  F21 = 'every_recorded_footprint_address_fits_reviewer_word'
  F22 = 'physical_primitive_operands_fit_reviewer_word'
  F23 = 'every_stored_physical_word_fits_reviewer_word'
  F24 = 'every_successful_returned_word_fits_reviewer_word'
}
$expectedCaseIds = @(
  'F01', 'F02', 'F03', 'F04', 'F05', 'F06', 'F07', 'F08',
  'F09', 'F10', 'F11', 'F12', 'F13', 'F14', 'F15', 'F16',
  'F17', 'F18', 'F19', 'F20', 'F21', 'F22', 'F23', 'F24',
  'Q01', 'Q02', 'Q03', 'Q04', 'Q05', 'Q06', 'Q07', 'Q08',
  'Q09', 'Q10', 'Q11', 'P01', 'P02', 'P03', 'P04', 'P05',
  'C01'
)
$caseRegistry = @(
  (New-ReplayCase 'F01' 'REJECT' 'physical_words_erase_canonical_payload'),
  (New-ReplayCase 'F02' 'REJECT' 'physical_execution_is_canonical_trace'),
  (New-ReplayCase 'F03' 'REJECT' 'canonical_trace_is_first_order_controller'),
  (New-ReplayCase 'F04' 'REJECT' 'canonical_physical_store_adapts_to_global_store'),
  (New-ReplayCase 'F05' 'REJECT' 'physical_events_match_canonical_store'),
  (New-ReplayCase 'F06' 'REJECT' 'successful_physical_reads_backed_by_canonical_words'),
  (New-ReplayCase 'F07' 'REJECT' 'ordered_physical_footprint_recorded'),
  (New-ReplayCase 'F08' 'REJECT' 'supplied_execution_eq_of_exact_read_agreement'),
  (New-ReplayCase 'F09' 'REJECT' 'physical_value_is_translated_supplied_store_value'),
  (New-ReplayCase 'F10' 'REJECT' 'physical_value_dependency'),
  (New-ReplayCase 'F11' 'REJECT' 'no_synthetic_physical_event'),
  (New-ReplayCase 'F12' 'REJECT' 'certificate_weight_eq_trace_length'),
  (New-ReplayCase 'F13' 'REJECT' 'certificate_weight_eq_cost'),
  (New-ReplayCase 'F14' 'REJECT' 'certificate_weight_le_210'),
  (New-ReplayCase 'F15' 'REJECT' 'reviewer_capacity_linear'),
  (New-ReplayCase 'F16' 'REJECT' 'physical_words_fit_capacity'),
  (New-ReplayCase 'F17' 'REJECT' 'reviewer_word_bits_logarithmic'),
  (New-ReplayCase 'F18' 'REJECT' 'input_operands_fit_reviewer_word'),
  (New-ReplayCase 'F19' 'REJECT' 'segment_encodings_fit_reviewer_word'),
  (New-ReplayCase 'F20' 'REJECT' 'every_physical_address_fits_reviewer_word'),
  (New-ReplayCase 'F21' 'REJECT' 'every_recorded_footprint_address_fits_reviewer_word'),
  (New-ReplayCase 'F22' 'REJECT' 'physical_primitive_operands_fit_reviewer_word'),
  (New-ReplayCase 'F23' 'REJECT' 'every_stored_physical_word_fits_reviewer_word'),
  (New-ReplayCase 'F24' 'REJECT' 'every_successful_returned_word_fits_reviewer_word'),
  (New-ReplayCase 'Q01' 'REJECT'),
  (New-ReplayCase 'Q02' 'REJECT'),
  (New-ReplayCase 'Q03' 'REJECT'),
  (New-ReplayCase 'Q04' 'REJECT'),
  (New-ReplayCase 'Q05' 'REJECT'),
  (New-ReplayCase 'Q06' 'REJECT'),
  (New-ReplayCase 'Q07' 'REJECT'),
  (New-ReplayCase 'Q08' 'REJECT'),
  (New-ReplayCase 'Q09' 'REJECT'),
  (New-ReplayCase 'Q10' 'REJECT'),
  (New-ReplayCase 'Q11' 'REJECT'),
  (New-ReplayCase 'P01' 'REJECT'),
  (New-ReplayCase 'P02' 'REJECT'),
  (New-ReplayCase 'P03' 'REJECT'),
  (New-ReplayCase 'P04' 'REJECT'),
  (New-ReplayCase 'P05' 'REJECT'),
  (New-ReplayCase 'C01' 'ACCEPT')
)

function Assert-ExactRegistry($Registry) {
  $entries = @($Registry)
  if ($entries.Count -ne $expectedCaseIds.Count) {
    throw (
      "registry count mismatch: expected $($expectedCaseIds.Count), " +
      "observed $($entries.Count)")
  }
  $seen = [Collections.Generic.HashSet[string]]::new(
    [StringComparer]::Ordinal)
  for ($index = 0; $index -lt $expectedCaseIds.Count; $index += 1) {
    $entry = $entries[$index]
    $expectedId = $expectedCaseIds[$index]
    if (-not $seen.Add([string]$entry.Id)) {
      throw "duplicate registry ID $($entry.Id) at index $index"
    }
    if ([string]$entry.Id -cne $expectedId) {
      throw (
        "registry order/set mismatch at index $index`: expected $expectedId, " +
        "observed $($entry.Id)")
    }
    $expectedVerdict = if ($expectedId -ceq 'C01') { 'ACCEPT' } else { 'REJECT' }
    if ([string]$entry.Verdict -cne $expectedVerdict) {
      throw (
        "registry verdict mismatch for $expectedId`: expected " +
        "$expectedVerdict, observed $($entry.Verdict)")
    }
    if ($index -lt 24) {
      $expectedField = [string]$expectedFieldMap[$expectedId]
      if ([string]$entry.Field -cne $expectedField) {
        throw (
          "registry field mapping mismatch for $expectedId`: expected " +
          "$expectedField, observed $($entry.Field)")
      }
    } elseif (-not [string]::IsNullOrEmpty([string]$entry.Field)) {
      throw "non-field registry entry $expectedId unexpectedly maps a field"
    }
  }
  $rejects = @($entries | Where-Object { $_.Verdict -ceq 'REJECT' }).Count
  $accepts = @($entries | Where-Object { $_.Verdict -ceq 'ACCEPT' }).Count
  if ($rejects -ne 40 -or $accepts -ne 1) {
    throw "registry verdict totals mismatch: reject=$rejects accept=$accepts"
  }
}

function Assert-RegistryMutationRejected([string]$Label, $Registry) {
  $message = $null
  try {
    Assert-ExactRegistry $Registry
  } catch {
    $message = $_.Exception.Message
  }
  if ($null -eq $message) {
    throw "$Label malformed registry unexpectedly passed"
  }
  Write-Host "M1-MUTATION REGISTRY CONTROL PASS [$Label] $message"
}

function Assert-ExactTextCount(
    [string]$Text,
    [string]$Needle,
    [int]$Expected,
    [string]$Label) {
  $count = 0
  $offset = 0
  while ($true) {
    $next = $Text.IndexOf($Needle, $offset, [StringComparison]::Ordinal)
    if ($next -lt 0) { break }
    $count += 1
    $offset = $next + $Needle.Length
  }
  if ($count -ne $Expected) {
    throw "$Label exact-count mismatch: expected $Expected observed $count"
  }
}

function Assert-CurrentFrontierPins {
  $physical = [IO.File]::ReadAllText(
    (Join-Path $repoRoot $reviewerPhysicalPath))
  $semantic = [IO.File]::ReadAllText(
    (Join-Path $repoRoot $semanticProvenancePath))
  $ram = [IO.File]::ReadAllText((Join-Path $repoRoot $ramPath))
  Assert-ExactTextCount $physical `
    'concreteBPNativeSuccinctRMQReviewerPhysicalSources.length = 22' 1 `
    '22-source manifest'
  Assert-ExactTextCount $physical '| 22 => some .selectChunkTable' 1 `
    'live logical segment 22'
  Assert-ExactTextCount $physical '| _ + 23 => none' 2 `
    'fresh segment-23 source/leaf tail'
  Assert-ExactTextCount $semantic 'segment < 23' 1 `
    'typed semantic segment frontier'
  Assert-ExactTextCount $ram '  segment := 23' 1 `
    'fresh unused segment-23 counterfactual'
  Assert-ExactTextCount $ram `
    'concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 210' 2 `
    'principled 210-cost identity'
  Assert-ExactTextCount $ram `
    'concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210' 2 `
    'same-trace 210 theorem and direct consumer'
  Write-Host (
    'M1-MUTATION FRONTIER PASS (22 physical sources; logical 0..22; ' +
    'fresh 23; cost 210)')
}

function Resolve-SelectedRegistry($Registry, [string]$Requested) {
  if ($Requested -eq '') { return @($Registry) }
  if ([string]::IsNullOrWhiteSpace($Requested) -or $Requested -ceq '0') {
    throw "empty/zero selector is invalid"
  }
  $selected = @($Registry | Where-Object { $_.Id -ceq $Requested })
  if ($selected.Count -ne 1) {
    throw "unknown or non-unique case $Requested"
  }
  return $selected
}

function Assert-SelectorRejected([string]$Label, $Registry, [string]$Requested) {
  $message = $null
  try { [void](Resolve-SelectedRegistry $Registry $Requested) } catch {
    $message = $_.Exception.Message
  }
  if ($null -eq $message) {
    throw "$Label selector unexpectedly passed"
  }
  Write-Host "M1-MUTATION SELECTOR CONTROL PASS [$Label] $message"
}

try {
  Assert-ExactRegistry $caseRegistry
  Assert-CurrentFrontierPins
  $omittedMiddle = @(
    $caseRegistry[0..19] + $caseRegistry[21..($caseRegistry.Count - 1)])
  $duplicatedMiddle = @(
    $caseRegistry[0..20] + $caseRegistry[20] +
      $caseRegistry[21..($caseRegistry.Count - 1)])
  Assert-RegistryMutationRejected 'omitted-middle-F21' $omittedMiddle
  Assert-RegistryMutationRejected 'duplicated-middle-F21' $duplicatedMiddle
  Write-Host (
    'M1-MUTATION REGISTRY PASS (ordered F01-F24,Q01-Q11,P01-P05,C01; ' +
    '24 exact fields; 40 reject; 1 accept)')
} catch {
  Write-Host "M1-MUTATION FAIL [REPLAY-EXACT-REGISTRY] $($_.Exception.Message)"
  Pop-Location
  exit 1
}

if ($RegistrySelfTestOnly) {
  Pop-Location
  exit 0
}

# REPLAY-SELECTOR-NONVACUITY
try {
  $selected = @(Resolve-SelectedRegistry $caseRegistry $OnlyCase)
  $middle = @(Resolve-SelectedRegistry $caseRegistry 'F21')
  if ($middle.Count -ne 1 -or $middle[0].Id -cne 'F21') {
    throw 'valid middle selector F21 did not resolve exactly once'
  }
  $omittedMiddle = @(
    $caseRegistry[0..19] + $caseRegistry[21..($caseRegistry.Count - 1)])
  $duplicatedMiddle = @(
    $caseRegistry[0..20] + $caseRegistry[20] +
      $caseRegistry[21..($caseRegistry.Count - 1)])
  Assert-SelectorRejected 'omitted-middle-F21' $omittedMiddle 'F21'
  Assert-SelectorRejected 'duplicated-middle-F21' $duplicatedMiddle 'F21'
  Assert-SelectorRejected 'unknown-ID' $caseRegistry 'UNKNOWN'
  Assert-SelectorRejected 'zero-selection' $caseRegistry '0'
  Assert-SelectorRejected 'whitespace-selection' $caseRegistry ' '
  Write-Host 'M1-MUTATION SELECTOR PASS (valid F21 resolves exactly once)'
} catch {
  Write-Host (
    "M1-MUTATION FAIL [REPLAY-SELECTOR-NONVACUITY] $($_.Exception.Message)")
  Pop-Location
  exit 1
}

if ($SelectorSelfTestOnly) {
  Pop-Location
  exit 0
}

function Normalize-Lf([string]$Text) {
  return [regex]::Replace($Text, '\r\n?', $lf)
}

function Get-TrackedState {
  $stateScript = Join-Path $sweepRoot (
    'tracked-state-' + [Guid]::NewGuid().ToString('N') + '.ps1')
  $shellPath = (Get-Process -Id $PID).Path
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
'@, $encoding)
    $result = Invoke-BoundedProcess `
      -FilePath $shellPath `
      -Arguments @(
        '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $stateScript) `
      -WorkingDirectory $repoRoot `
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
  $currentState = Get-TrackedState
  if ($currentState -cne $script:baselineTrackedState) {
    throw "[$Id] live tracked state changed"
  }
  $currentHashes = Get-LiveHashes
  foreach ($relativePath in $integrityPaths) {
    if ($currentHashes[$relativePath] -cne
        $script:baselineHashes[$relativePath]) {
      throw "[$Id] live hash changed for $relativePath"
    }
  }
}

$toolchainSpec = (
  [IO.File]::ReadAllText((Join-Path $repoRoot 'lean-toolchain'))).Trim()
$toolchainDirectoryName =
  $toolchainSpec.Replace('/', '--').Replace(':', '---')
$userProfilePath = $env:USERPROFILE
if ([string]::IsNullOrWhiteSpace($userProfilePath)) {
  $userProfilePath =
    [Environment]::GetFolderPath([Environment+SpecialFolder]::UserProfile)
}
$elanRoot = Join-Path $userProfilePath '.elan'
$toolchainRoot =
  Join-Path (Join-Path $elanRoot 'toolchains') $toolchainDirectoryName
$leanBinaryName = if ([Environment]::OSVersion.Platform -eq
    [PlatformID]::Win32NT) { 'lean.exe' } else { 'lean' }
$leanExe = Join-Path (Join-Path $toolchainRoot 'bin') $leanBinaryName
$projectLeanPath = Join-Path $repoRoot '.lake/build/lib/lean'
$toolchainLeanPath = Join-Path $toolchainRoot 'lib/lean'
$baseLeanPath =
  $projectLeanPath + $pathSeparator + $toolchainLeanPath
$sharedOleanArtifacts = @()

$sweepRoot = Join-Path ([IO.Path]::GetTempPath()) (
  'rmq-m1-r4-mutations-' + [Guid]::NewGuid().ToString('N'))
$sweepRoot = [IO.Path]::GetFullPath($sweepRoot)
[void](New-Item -ItemType Directory -Path $sweepRoot)

function New-CaseRoot([string]$Id) {
  $caseRoot = Join-Path $sweepRoot $Id
  [void](New-Item -ItemType Directory -Path $caseRoot)
  foreach ($artifact in $sharedOleanArtifacts) {
    $relativeArtifact = $artifact.FullName.Substring(
      $projectLeanPath.Length).TrimStart(
        [IO.Path]::DirectorySeparatorChar,
        [IO.Path]::AltDirectorySeparatorChar)
    $destination = Join-Path $caseRoot $relativeArtifact
    [void](New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($destination)))
    [void](New-Item -ItemType HardLink -Path $destination -Target $artifact.FullName)
  }
  foreach ($relativePath in $shadowSources) {
    $destination = Join-Path $caseRoot $relativePath
    [void](New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($destination)))
    $text = Normalize-Lf (
      [IO.File]::ReadAllText((Join-Path $repoRoot $relativePath)))
    [IO.File]::WriteAllText($destination, $text, $encoding)
  }
  return [IO.Path]::GetFullPath($caseRoot)
}

function Remove-ShadowTree([string]$Path) {
  if (-not (Test-Path -LiteralPath $Path)) {
    return
  }
  $fullPath = [IO.Path]::GetFullPath($Path)
  $allowedPrefix =
    $sweepRoot.TrimEnd([IO.Path]::DirectorySeparatorChar) +
      [IO.Path]::DirectorySeparatorChar
  if (-not $fullPath.StartsWith(
      $allowedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
    throw "refusing to remove shadow path outside sweep root: $fullPath"
  }
  Remove-Item -LiteralPath $fullPath -Recurse -Force
}

function Read-Shadow([string]$CaseRoot, [string]$RelativePath) {
  return Normalize-Lf (
    [IO.File]::ReadAllText((Join-Path $CaseRoot $RelativePath)))
}

function Write-Shadow(
    [string]$CaseRoot,
    [string]$RelativePath,
    [string]$Text) {
  [IO.File]::WriteAllText(
    (Join-Path $CaseRoot $RelativePath),
    (Normalize-Lf $Text),
    $encoding)
}

function Reset-ShadowSources([string]$CaseRoot) {
  foreach ($relativePath in $shadowSources) {
    $text = Normalize-Lf (
      [IO.File]::ReadAllText((Join-Path $repoRoot $relativePath)))
    Write-Shadow $CaseRoot $relativePath $text
  }
}

# REPLAY-SUBPROCESS-DEADLINE
function Read-BoundedProcessOutput([string]$StdoutPath, [string]$StderrPath) {
  $lines = [Collections.Generic.List[string]]::new()
  foreach ($path in @($StdoutPath, $StderrPath)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
      continue
    }
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
    foreach ($line in [regex]::Split($text, '\r?\n')) {
      if ($line -ne '') {
        $lines.Add($line)
      }
    }
  }
  return @($lines)
}

function Invoke-BoundedProcess(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$WorkingDirectory,
    [string]$Stage,
    [int]$DeadlineSeconds,
    [hashtable]$Environment = @{},
    [switch]$ReleaseGatedScript) {
  if ($DeadlineSeconds -le 0) {
    throw "$Stage deadline must be positive"
  }
  $safeStage = [regex]::Replace($Stage, '[^A-Za-z0-9_-]', '-')
  $logStem = Join-Path $sweepRoot (
    $safeStage + '-' + [Guid]::NewGuid().ToString('N'))
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
  $output = @()
  $exitCode = -1
  $stopwatch = [Diagnostics.Stopwatch]::StartNew()
  try {
    if (-not $ReleaseGatedScript) {
      $launchSpec = [ordered]@{
        FilePath = $FilePath
        Arguments = @($Arguments)
        Environment = $Environment
      }
      [IO.File]::WriteAllText(
        $specPath, ($launchSpec | ConvertTo-Json -Depth 5), $encoding)
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
'@, $encoding)
    } elseif ($Environment.Count -ne 0) {
      throw "$Stage release-gated scripts cannot receive an environment override"
    }
    if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) {
      $jobHandle = [RMQReplayJob]::CreateKillOnClose()
    }
    $startFilePath = if ($ReleaseGatedScript) { $FilePath } else {
      (Get-Process -Id $PID).Path
    }
    $startArguments = if ($ReleaseGatedScript) {
      @($Arguments) + @('-LaunchReleasePath', $releasePath)
    } else {
      @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $bootstrapPath, '-SpecPath', $specPath,
        '-ReleasePath', $releasePath)
    }
    $process = Start-Process -FilePath $startFilePath -ArgumentList $startArguments `
      -WorkingDirectory $WorkingDirectory -PassThru -NoNewWindow `
      -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath
    if ($jobHandle -ne [IntPtr]::Zero) {
      [RMQReplayJob]::Assign($jobHandle, $process.Handle)
    }
    # The bootstrap cannot launch the requested tool until its root is owned.
    [IO.File]::WriteAllText($releasePath, 'assigned', $encoding)

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
        # The root is complete; close ownership now so no residual descendant
        # can keep writing between the final byte count and bounded read.
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
    $output = if ($outputLimitExceeded) {
      @("redirected output exceeded $StageOutputLimitBytes bytes")
    } else {
      @(Read-BoundedProcessOutput $stdoutPath $stderrPath)
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
    Stage = $Stage
    ExitCode = $exitCode
    Output = $output
    TimedOut = $timedOut
    OutputLimitExceeded = $outputLimitExceeded
    TerminatedIds = $terminatedIds
    DurationSeconds = [Math]::Round($stopwatch.Elapsed.TotalSeconds, 3)
    DeadlineSeconds = $DeadlineSeconds
  }
}

$baselineTrackedState = Get-TrackedState
$baselineHashes = Get-LiveHashes

function Invoke-ShadowLean(
    [string]$CaseRoot,
    [string]$RelativePath,
    [string]$Stage) {
  $sourcePath = Join-Path $CaseRoot $RelativePath
  $oleanPath = [IO.Path]::ChangeExtension($sourcePath, '.olean')
  [void](New-Item -ItemType Directory -Force -Path ([IO.Path]::GetDirectoryName($oleanPath)))
  if (Test-Path -LiteralPath $oleanPath) {
    Remove-Item -LiteralPath $oleanPath -Force
  }
  return Invoke-BoundedProcess `
    -FilePath $leanExe `
    -Arguments @("--root=$CaseRoot", '-o', $oleanPath, $sourcePath) `
    -WorkingDirectory $CaseRoot `
    -Stage $Stage `
    -DeadlineSeconds $StageDeadlineSeconds `
    -Environment @{
      LEAN_PATH = $CaseRoot + $pathSeparator + $baseLeanPath
    }
}

function Remove-SweepRoot {
  if (-not (Test-Path -LiteralPath $sweepRoot)) {
    return
  }
  $fullSweepRoot = [IO.Path]::GetFullPath($sweepRoot)
  $tempRoot = [IO.Path]::GetFullPath([IO.Path]::GetTempPath())
  if (-not $fullSweepRoot.StartsWith(
      $tempRoot, [StringComparison]::OrdinalIgnoreCase)) {
    throw "refusing to remove sweep root outside temp: $fullSweepRoot"
  }
  Remove-Item -LiteralPath $fullSweepRoot -Recurse -Force
}

function Invoke-DeadlineSelfTest {
  $selfTestScript = Join-Path $sweepRoot 'deadline-sleeper.ps1'
  $childPidPath = Join-Path $sweepRoot 'deadline-sleeper-child.pid'
  $shellPath = (Get-Process -Id $PID).Path
  $quotedShellPath = $shellPath.Replace("'", "''")
  $quotedPidPath = $childPidPath.Replace("'", "''")
  $selfTestText = @"
`$child = Start-Process -FilePath '$quotedShellPath' -ArgumentList @(
  '-NoLogo', '-NoProfile', '-Command', 'Start-Sleep -Seconds 60') -PassThru
[IO.File]::WriteAllText('$quotedPidPath', [string]`$child.Id)
Start-Sleep -Seconds 60
"@
  $result = $null
  try {
    [IO.File]::WriteAllText($selfTestScript, $selfTestText, $encoding)
    $result = Invoke-BoundedProcess `
      -FilePath $shellPath `
      -Arguments @(
        '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $selfTestScript) `
      -WorkingDirectory $sweepRoot `
      -Stage 'deadline-sleeper-self-test' `
      -DeadlineSeconds $SelfTestDeadlineSeconds
    if (-not $result.TimedOut) {
      throw 'sleeper self-test did not classify the deadline as a timeout'
    }
    if ($result.OutputLimitExceeded) {
      throw 'sleeper self-test hit the output limit instead of the deadline'
    }
    if (-not (Test-Path -LiteralPath $childPidPath -PathType Leaf)) {
      throw (
        'sleeper self-test child PID receipt was not written; output=' +
        (($result.Output | Select-Object -Last 8) -join ' | '))
    }
    $childId = [int]([IO.File]::ReadAllText($childPidPath).Trim())
    if ($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)) {
      throw "sleeper child $childId survived owned-tree termination"
    }
    Write-Host (
      'M1-MUTATION DEADLINE CONTROL PASS ' +
      "(timeout=$SelfTestDeadlineSeconds`s; " +
      "terminated-root=$($result.TerminatedIds -join ','); " +
      "child=$childId absent; duration=$($result.DurationSeconds)s)")
  } finally {
    Remove-Item -LiteralPath $selfTestScript -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $childPidPath -Force -ErrorAction SilentlyContinue
    Assert-LiveIntegrity 'deadline-sleeper-finally'
  }
}

try {
  Invoke-DeadlineSelfTest
} catch {
  Write-Host (
    "M1-MUTATION FAIL [REPLAY-SUBPROCESS-DEADLINE] $($_.Exception.Message)")
  try { Remove-SweepRoot } catch {
    Write-Host "M1-MUTATION FAIL [DEADLINE-CLEANUP] $($_.Exception.Message)"
  }
  Pop-Location
  exit 1
}

if ($DeadlineSelfTestOnly) {
  try {
    Assert-LiveIntegrity 'deadline-self-test-only-final'
    Remove-SweepRoot
  } catch {
    Write-Host "M1-MUTATION FAIL [DEADLINE-FINAL] $($_.Exception.Message)"
    Pop-Location
    exit 1
  }
  Pop-Location
  exit 0
}

if (-not (Test-Path -LiteralPath $leanExe -PathType Leaf) -or
    -not (Test-Path -LiteralPath $projectLeanPath -PathType Container) -or
    -not (Test-Path -LiteralPath $toolchainLeanPath -PathType Container)) {
  Write-Host (
    'M1-MUTATION FAIL: pinned installed Lean or shared build artifacts missing ' +
    "($toolchainSpec)")
  try { Remove-SweepRoot } catch {
    Write-Host "M1-MUTATION FAIL [LEAN-PREFLIGHT-CLEANUP] $($_.Exception.Message)"
  }
  Pop-Location
  exit 1
}
$sharedOleanArtifacts = @(
  Get-ChildItem -LiteralPath $projectLeanPath -Recurse -File -Filter '*.olean'
)
if ($sharedOleanArtifacts.Count -eq 0) {
  Write-Host 'M1-MUTATION FAIL: shared project olean set is empty'
  try { Remove-SweepRoot } catch {
    Write-Host "M1-MUTATION FAIL [OLEAN-PREFLIGHT-CLEANUP] $($_.Exception.Message)"
  }
  Pop-Location
  exit 1
}

function Limit-Line([string]$Line) {
  $flat = $Line.Replace([string][char]13, ' ').Replace([string][char]10, ' ')
  if ($flat.Length -le 1200) {
    return $flat
  }
  return $flat.Substring(0, 1197) + '...'
}

function Diagnostic-Tail($Result) {
  return (@(
    $Result.Output |
      Select-Object -Last 12 |
      ForEach-Object { Limit-Line ([string]$_) }
  ) -join ' | ')
}

function Require-Reject($Result, [string[]]$Patterns) {
  if ($Result.TimedOut) {
    throw (
      "$($Result.Stage) timed out after $($Result.DeadlineSeconds)s; " +
      "terminated=$($Result.TerminatedIds -join ',')")
  }
  if ($Result.OutputLimitExceeded) {
    throw (
      "$($Result.Stage) exceeded redirected output limit " +
      "$StageOutputLimitBytes bytes; terminated=$($Result.TerminatedIds -join ',')")
  }
  if ($Result.ExitCode -eq 0) {
    throw "$($Result.Stage) unexpectedly exited 0"
  }
  $text = $Result.Output -join [Environment]::NewLine
  foreach ($pattern in $Patterns) {
    if ($text -notmatch $pattern) {
      throw (
        "$($Result.Stage) exit=$($Result.ExitCode) missed surface /$pattern/: " +
        (Diagnostic-Tail $Result))
    }
  }
  $surface = @(
    $Result.Output |
      Where-Object { $_ -match 'error:' } |
      Select-Object -First 1
  )
  if ($surface.Count -eq 0) {
    $surface = @(
      $Result.Output |
        Where-Object { $_ -match $Patterns[0] } |
        Select-Object -First 1
    )
  }
  if ($surface.Count -eq 0) {
    $surface = @('matched expected diagnostics')
  }
  return (
    "$($Result.Stage) exit=$($Result.ExitCode) surface=" +
    (Limit-Line ([string]$surface[0])) +
    " duration=$($Result.DurationSeconds)s/$($Result.DeadlineSeconds)s")
}

function Require-Accept($Result) {
  if ($Result.TimedOut) {
    throw (
      "$($Result.Stage) timed out after $($Result.DeadlineSeconds)s; " +
      "terminated=$($Result.TerminatedIds -join ',')")
  }
  if ($Result.OutputLimitExceeded) {
    throw (
      "$($Result.Stage) exceeded redirected output limit " +
      "$StageOutputLimitBytes bytes; terminated=$($Result.TerminatedIds -join ',')")
  }
  if ($Result.ExitCode -ne 0) {
    throw (
      "$($Result.Stage) exit=$($Result.ExitCode): " +
      (Diagnostic-Tail $Result))
  }
  return (
    "$($Result.Stage) exit=0 " +
    "duration=$($Result.DurationSeconds)s/$($Result.DeadlineSeconds)s")
}

function Run-Case(
    [string]$Id,
    [string]$Verdict,
    [scriptblock]$Body) {
  if ($OnlyCase -ne '' -and $Id -cne $OnlyCase) {
    return
  }
  $registryEntry = @($caseRegistry | Where-Object { $_.Id -ceq $Id })
  if ($registryEntry.Count -ne 1) {
    throw "execution attempted unregistered or duplicate case $Id"
  }
  if ([string]$registryEntry[0].Verdict -cne $Verdict) {
    throw (
      "execution verdict for $Id is $Verdict, registry requires " +
      "$($registryEntry[0].Verdict)")
  }
  if ($executedIds.Contains($Id)) {
    throw "case $Id executed more than once"
  }
  $executedIds.Add($Id)
  $caseRoot = $null
  $evidence = @()
  $problem = $null
  try {
    $caseRoot = New-CaseRoot $Id
    $evidence = @(& $Body $caseRoot)
  } catch {
    $problem = $_.Exception.Message
  }
  try {
    if ($null -ne $caseRoot) {
      Remove-ShadowTree $caseRoot
    }
    Assert-LiveIntegrity $Id
  } catch {
    if ($null -eq $problem) {
      $problem = $_.Exception.Message
    } else {
      $problem += '; ' + $_.Exception.Message
    }
  }
  if ($null -ne $problem) {
    Write-Host "M1-MUTATION FAIL [$Id] expected $($Verdict): $problem"
    $script:failures += 1
    return
  }
  $joinedEvidence = $evidence -join '; '
  Write-Host (
    "M1-MUTATION PASS [$Id] $Verdict $joinedEvidence; " +
    'live-hashes/state=unchanged')
  $script:passes += 1
  if ($Verdict -ceq 'REJECT') {
    $script:rejectPasses += 1
  } else {
    $script:acceptPasses += 1
  }
}

function Replace-ExactOnce(
    [string]$Text,
    [string]$Old,
    [string]$New,
    [string]$Context) {
  # Shadow sources are normalized to LF. Windows PowerShell materializes
  # multiline here-strings with CRLF, so normalize both exact operands before
  # ordinal matching; otherwise every multiline mutation is a false no-op.
  $Old = Normalize-Lf $Old
  $New = Normalize-Lf $New
  $first = $Text.IndexOf($Old, [StringComparison]::Ordinal)
  if ($first -lt 0) {
    throw "$Context replacement source not found"
  }
  $second = $Text.IndexOf(
    $Old, $first + $Old.Length, [StringComparison]::Ordinal)
  if ($second -ge 0) {
    throw "$Context replacement source is not unique"
  }
  return $Text.Substring(0, $first) + $New +
    $Text.Substring($first + $Old.Length)
}

function Get-RecordBounds(
    [string]$Text,
    [string]$StartMarker,
    [string]$EndMarker) {
  $start = $Text.IndexOf($StartMarker, [StringComparison]::Ordinal)
  if ($start -lt 0) {
    throw "record start marker not found: $StartMarker"
  }
  $end = $Text.IndexOf($EndMarker, $start, [StringComparison]::Ordinal)
  if ($end -lt 0) {
    throw "record end marker not found: $EndMarker"
  }
  return [pscustomobject]@{ Start = $start; End = $end }
}

function Remove-RecordField(
    [string]$Text,
    [string]$StartMarker,
    [string]$EndMarker,
    [string]$Field) {
  $bounds = Get-RecordBounds $Text $StartMarker $EndMarker
  $record = $Text.Substring(
    $bounds.Start, $bounds.End - $bounds.Start)
  $matches = [regex]::Matches(
    $record, '(?m)^  ([a-z][a-z0-9_]*) :')
  $target = -1
  for ($index = 0; $index -lt $matches.Count; $index += 1) {
    if ($matches[$index].Groups[1].Value -ceq $Field) {
      $target = $index
      break
    }
  }
  if ($target -lt 0) {
    throw "field $Field not found in record"
  }
  $removeStart = $matches[$target].Index
  $removeEnd = if ($target + 1 -lt $matches.Count) {
    $matches[$target + 1].Index
  } else {
    $record.Length
  }
  $mutatedRecord = $record.Remove(
    $removeStart, $removeEnd - $removeStart)
  return $Text.Substring(0, $bounds.Start) + $mutatedRecord +
    $Text.Substring($bounds.End)
}

function Edit-RecordField(
    [string]$Text,
    [string]$StartMarker,
    [string]$EndMarker,
    [string]$Field,
    [scriptblock]$Editor) {
  $bounds = Get-RecordBounds $Text $StartMarker $EndMarker
  $record = $Text.Substring(
    $bounds.Start, $bounds.End - $bounds.Start)
  $matches = [regex]::Matches(
    $record, '(?m)^  ([a-z][a-z0-9_]*) :')
  $target = -1
  for ($index = 0; $index -lt $matches.Count; $index += 1) {
    if ($matches[$index].Groups[1].Value -ceq $Field) {
      $target = $index
      break
    }
  }
  if ($target -lt 0) {
    throw "field $Field not found in record"
  }
  $fieldStart = $matches[$target].Index
  $fieldEnd = if ($target + 1 -lt $matches.Count) {
    $matches[$target + 1].Index
  } else {
    $record.Length
  }
  $fieldText = $record.Substring(
    $fieldStart, $fieldEnd - $fieldStart)
  $mutatedField = [string](& $Editor $fieldText)
  if ($mutatedField -ceq $fieldText) {
    throw "field editor made no change to $Field"
  }
  $mutatedRecord = $record.Substring(0, $fieldStart) +
    $mutatedField + $record.Substring($fieldEnd)
  return $Text.Substring(0, $bounds.Start) + $mutatedRecord +
    $Text.Substring($bounds.End)
}

function Edit-WellFormedField(
    [string]$Text,
    [string]$Field,
    [scriptblock]$Editor) {
  return Edit-RecordField $Text 'structure ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed' ($lf + $lf + '/--' + $lf + 'Independent typed consumer') $Field $Editor
}

function Edit-PaperTheorem([string]$Text, [scriptblock]$Editor) {
  $startMarker = 'theorem listIntSuccinctRMQPaperMainTheorem :'
  $start = $Text.IndexOf($startMarker, [StringComparison]::Ordinal)
  if ($start -lt 0) {
    throw 'paper theorem start not found'
  }
  $end = $Text.IndexOf(
    ($lf + $lf + '/--'), $start, [StringComparison]::Ordinal)
  if ($end -lt 0) {
    throw 'paper theorem end not found'
  }
  $theoremText = $Text.Substring($start, $end - $start)
  $mutated = [string](& $Editor $theoremText)
  if ($mutated -ceq $theoremText) {
    throw 'paper theorem editor made no change'
  }
  return $Text.Substring(0, $start) + $mutated +
    $Text.Substring($end)
}

function Invoke-StartupSmoke {
  $caseRoot = $null
  try {
    $caseRoot = New-CaseRoot 'STARTUP-SMOKE'
    $evidence = @()
    foreach ($stage in @(
        [pscustomobject]@{ Path = $finalModelPath; Label = 'startup final-model' },
        [pscustomobject]@{ Path = $classicPath; Label = 'startup classic' },
        [pscustomobject]@{ Path = $headlinePath; Label = 'startup headline' },
        [pscustomobject]@{ Path = $checkerPath; Label = 'startup expected-type checker' })) {
      $result = Invoke-ShadowLean $caseRoot $stage.Path $stage.Label
      $evidence += Require-Accept $result
    }
    Write-Host (
      'M1-MUTATION STARTUP SMOKE PASS ' + ($evidence -join '; '))
  } finally {
    if ($null -ne $caseRoot) { Remove-ShadowTree $caseRoot }
    Assert-LiveIntegrity 'startup-smoke-finally'
  }
}

if ($StartupSmokeOnly) {
  try {
    Invoke-StartupSmoke
    Remove-SweepRoot
  } catch {
    Write-Host "M1-MUTATION FAIL [STARTUP-SMOKE] $($_.Exception.Message)"
    try { Remove-SweepRoot } catch {
      Write-Host "M1-MUTATION FAIL [STARTUP-SMOKE-CLEANUP] $($_.Exception.Message)"
    }
    Pop-Location
    exit 1
  }
  Pop-Location
  exit 0
}

$wellFormedStart =
  'structure ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed'
$wellFormedEnd =
  $lf + $lf + '/--' + $lf + 'Independent typed consumer'
$fields = @(
  $caseRegistry |
    Where-Object { $_.Id -cmatch '^F[0-9][0-9]$' }
)

$runLabel = if ($OnlyCase -eq '') {
  '41 cases (F01-F24, Q01-Q11, P01-P05, C01)'
} else {
  "focused case $OnlyCase"
}
Write-Host "M1-MUTATION START $runLabel; focused Lean; shadow copies"

try {
foreach ($entry in $fields) {
  $id = [string]$entry.Id
  $field = [string]$entry.Field
  Run-Case $id 'REJECT' {
    param($caseRoot)
    $text = Read-Shadow $caseRoot $finalModelPath
    $mutated = Remove-RecordField $text $wellFormedStart $wellFormedEnd $field
    Write-Shadow $caseRoot $finalModelPath $mutated
    $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
    $evidence = @(Require-Reject $result @('Invalid field', [regex]::Escape($field)))
    if ($id -ceq 'F14') {
      # The inherited deletion test proves that the named certificate field is
      # consumed.  This second phase proves that its exact 210 proposition and
      # the literal public conjunct are pinned: the weakened 211 chain itself
      # must compile before the independent expected type rejects it.
      Reset-ShadowSources $caseRoot
      $modelText = Read-Shadow $caseRoot $finalModelPath
      $modelText = Edit-WellFormedField $modelText 'certificate_weight_le_210' {
        param($fieldText)
        Replace-ExactOnce $fieldText ($lf + '      210') ($lf + '      211') `
          'F14 WellFormed bound'
      }
      $modelText = Edit-RecordField $modelText `
        'structure ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts' `
        ($lf + $lf + '/--' + $lf + 'Project every mandatory') `
        'requires_certificate_weight_le_210' {
          param($fieldText)
          Replace-ExactOnce $fieldText ($lf + '      210') ($lf + '      211') `
            'F14 RequiredFacts bound'
        }
      $modelText = Replace-ExactOnce $modelText `
        'certificate_weight_le_210 := h.nonSyntheticWeight_sum_le_210' `
        'certificate_weight_le_210 := Nat.le_trans h.nonSyntheticWeight_sum_le_210 (Nat.le_succ 210)' `
        'F14 canonical constructor weakening'
      Write-Shadow $caseRoot $finalModelPath $modelText

      $headlineText = Read-Shadow $caseRoot $headlinePath
      $headlineText = Edit-PaperTheorem $headlineText {
        param($theoremText)
        Replace-ExactOnce $theoremText ').sum <= 210) /\' ').sum <= 211) /\' `
          'F14 literal paper bound'
      }
      Write-Shadow $caseRoot $headlinePath $headlineText

      $evidence += Require-Accept (
        Invoke-ShadowLean $caseRoot $finalModelPath 'weakened 211 certificate')
      $evidence += Require-Accept (
        Invoke-ShadowLean $caseRoot $classicPath 'weakened 211 guarded packet')
      $evidence += Require-Accept (
        Invoke-ShadowLean $caseRoot $headlinePath 'weakened 211 paper theorem')
      $evidence += Require-Reject (
        Invoke-ShadowLean $caseRoot $checkerPath 'frozen 210 expected type') @(
          'M1ReviewerNativeExpectedPaperType|listIntSuccinctRMQPaperMainTheorem',
          'type mismatch|application type mismatch')
    }
    $evidence
  }
}

Run-Case 'Q01' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'supplied_execution_eq_of_exact_read_agreement' {
      param($fieldText)
      $old = @'
concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right =
          concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape storeB left right
'@
      $new = @'
(concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).value =
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape storeB left right).value
'@
      Replace-ExactOnce $fieldText $old $new 'Q01'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'supplied_execution_eq_of_exact_read_agreement')
}

Run-Case 'Q02' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'physical_words_erase_canonical_payload' {
      param($fieldText)
      Replace-ExactOnce $fieldText 'concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape' '([] : List Bool)' 'Q02'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'physical_words_erase_canonical_payload')
}

Run-Case 'Q03' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'physical_words_erase_canonical_payload' {
      param($fieldText)
      Replace-ExactOnce $fieldText 'concreteBPNativeSuccinctRMQReviewerPhysicalWords shape' '([] : List (List Bool))' 'Q03'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'physical_words_erase_canonical_payload')
}

Run-Case 'Q04' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'canonical_physical_store_adapts_to_global_store' {
      param($fieldText)
      Replace-ExactOnce $fieldText 'concreteBPNativeSuccinctRMQGlobalReadStore shape' 'concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape' 'Q04'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'canonical_physical_store_adapts_to_global_store')
}

Run-Case 'Q05' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'canonical_trace_is_first_order_controller' {
      param($fieldText)
      $old = @'
concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
'@
      $new = @'
concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        (Cartesian.shape []) left right
'@
      Replace-ExactOnce $fieldText $old $new 'Q05'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'canonical_trace_is_first_order_controller')
}

Run-Case 'Q06' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'canonical_trace_is_first_order_controller' {
      param($fieldText)
      $old = @'
concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right
'@
      $new = @'
concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape right left
'@
      Replace-ExactOnce $fieldText $old $new 'Q06'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'canonical_trace_is_first_order_controller')
}

Run-Case 'Q07' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'reviewer_word_bits_logarithmic' {
      param($fieldText)
      Replace-ExactOnce $fieldText 'concreteBPNativeSuccinctRMQReviewerWordBits shape.size <=' '(concreteBPNativeSuccinctRMQReviewerWordBits shape.size + 1) <=' 'Q07'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'reviewer_word_bits_logarithmic')
}

Run-Case 'Q08' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'ordered_physical_footprint_recorded' {
      param($fieldText)
      $old = @'
concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
'@
      $new = @'
concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape right left =
'@
      Replace-ExactOnce $fieldText $old $new 'Q08'
    }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'ordered_physical_footprint_recorded')
}

Run-Case 'Q09' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $finalModelPath
  $mutated = Edit-WellFormedField $text 'physical_value_dependency' {
    param($fieldText)
    $count = [regex]::Matches($fieldText, '\)\.value').Count
    if ($count -ne 4) {
      throw "Q09 expected four value projections, found $count"
    }
    $fieldText.Replace(').value', ')')
  }
  Write-Shadow $caseRoot $finalModelPath $mutated
  $result = Invoke-ShadowLean $caseRoot $finalModelPath 'requiredFacts'
  Require-Reject $result @('type mismatch', 'physical_value_dependency')
}

Run-Case 'Q10' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $classicPath
  $oldWellFormed = @'
  machine_well_formed_of_valid :
    ValidRange xs left right ->
      SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
        (cartesianShape xs) left right
'@
  $newWellFormed = @'
  machine_well_formed_of_valid :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
      (cartesianShape xs) left right
'@
  $oldRequired = @'
  machine_required_facts_of_valid :
    ValidRange xs left right ->
      SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
        (cartesianShape xs) left right
'@
  $newRequired = @'
  machine_required_facts_of_valid :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
      (cartesianShape xs) left right
'@
  $oldWellFormedInit = @'
      machine_well_formed_of_valid := fun _ =>
        SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed
          (cartesianShape xs) left right
'@
  $newWellFormedInit = @'
      machine_well_formed_of_valid :=
        SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed
          (cartesianShape xs) left right
'@
  $oldRequiredInit = @'
      machine_required_facts_of_valid := fun _ =>
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed
          (cartesianShape xs) left right).requiredFacts
'@
  $newRequiredInit = @'
      machine_required_facts_of_valid :=
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerMachineWellFormed
          (cartesianShape xs) left right).requiredFacts
'@
  $text = Replace-ExactOnce $text $oldWellFormed $newWellFormed 'Q10 well-formed guard'
  $text = Replace-ExactOnce $text $oldRequired $newRequired 'Q10 required-facts guard'
  $text = Replace-ExactOnce $text $oldWellFormedInit $newWellFormedInit 'Q10 well-formed initializer'
  $text = Replace-ExactOnce $text $oldRequiredInit $newRequiredInit 'Q10 required-facts initializer'
  Write-Shadow $caseRoot $classicPath $text
  $classic = Invoke-ShadowLean $caseRoot $classicPath 'mutated Classic'
  Require-Accept $classic
  $headline = Invoke-ShadowLean $caseRoot $headlinePath 'unchanged headline consumer'
  Require-Reject $headline @('machine_(well_formed|required_facts)_of_valid', 'function expected|type mismatch|application type mismatch')
}

Run-Case 'Q11' 'REJECT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $headlinePath
  $mutated = Edit-PaperTheorem $text {
    param($theoremText)
    $old = @'
RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right
'@
    $new = @'
RMQ.SuccinctClassic.storesAgreeOnFootprint
              xs storeA storeB
'@
    Replace-ExactOnce $theoremText $old $new 'Q11 paper premise'
  }
  Write-Shadow $caseRoot $headlinePath $mutated
  $result = Invoke-ShadowLean $caseRoot $headlinePath 'paper theorem proof'
  Require-Reject $result @('hagree', 'type mismatch|application type mismatch')
}

$wellFormedConjunct = @'
        (forall left right,
          RMQ.ValidRange xs left right ->
            RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed
              (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
'@
$wellFormedProof = @'
      fun left right hvalid =>
        (RMQ.SuccinctClassic.listIntSuccinctRMQReviewerNativeMachineAdequacy
          xs left right).machine_well_formed_of_valid hvalid,
'@
$requiredFactsConjunct = @'
        (forall left right,
          RMQ.ValidRange xs left right ->
            RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineRequiredFacts
              (RMQ.SuccinctClassic.cartesianShape xs) left right) /\
'@
$requiredFactsProof = @'
      fun left right hvalid =>
        (RMQ.SuccinctClassic.listIntSuccinctRMQReviewerNativeMachineAdequacy
          xs left right).machine_required_facts_of_valid hvalid,
'@
$physicalConjunct = @'
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right =
              RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right) /\
'@
$physicalProof = @'
      fun storeA storeB left right hagree =>
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
          xs storeA storeB left right hagree,
'@

function Run-PublicPinCase(
    [string]$Id,
    [scriptblock]$Editor) {
  Run-Case $Id 'REJECT' {
    param($caseRoot)
    $text = Read-Shadow $caseRoot $headlinePath
    $mutated = Edit-PaperTheorem $text $Editor
    Write-Shadow $caseRoot $headlinePath $mutated
    $headline = Invoke-ShadowLean $caseRoot $headlinePath 'repaired mutated paper theorem'
    Require-Accept $headline
    $checker = Invoke-ShadowLean $caseRoot $checkerPath 'frozen public expected type'
    Require-Reject $checker @(
      'M1ReviewerNativeExpectedPaperType|listIntSuccinctRMQPaperMainTheorem',
      'type mismatch|application type mismatch')
  }
}

Run-PublicPinCase 'P01' {
  param($theoremText)
  $theoremText = Replace-ExactOnce $theoremText $wellFormedConjunct '' 'P01 WellFormed conjunct'
  Replace-ExactOnce $theoremText $wellFormedProof '' 'P01 WellFormed proof'
}

Run-PublicPinCase 'P02' {
  param($theoremText)
  $theoremText = Replace-ExactOnce $theoremText $requiredFactsConjunct '' 'P02 RequiredFacts conjunct'
  Replace-ExactOnce $theoremText $requiredFactsProof '' 'P02 RequiredFacts proof'
}

$physicalValueConjunct = @'
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right).value =
              (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right).value) /\
'@
$physicalValueProof = @'
      fun storeA storeB left right hagree =>
        congrArg (fun result => result.value)
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
            xs storeA storeB left right hagree),
'@
Run-PublicPinCase 'P03' {
  param($theoremText)
  $theoremText = Replace-ExactOnce $theoremText $physicalConjunct $physicalValueConjunct 'P03 value conjunct'
  Replace-ExactOnce $theoremText $physicalProof $physicalValueProof 'P03 value proof'
}

$physicalCostConjunct = @'
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          RMQ.SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
              xs storeA storeB left right ->
            (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right).toCosted.cost =
              (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right).toCosted.cost) /\
'@
$physicalCostProof = @'
      fun storeA storeB left right hagree =>
        congrArg (fun result => result.toCosted.cost)
          (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
            xs storeA storeB left right hagree),
'@
Run-PublicPinCase 'P04' {
  param($theoremText)
  $theoremText = Replace-ExactOnce $theoremText $physicalConjunct $physicalCostConjunct 'P04 cost conjunct'
  Replace-ExactOnce $theoremText $physicalProof $physicalCostProof 'P04 cost proof'
}

$physicalStaticConjunct = @'
        (forall (storeA storeB : RMQ.WordRAM.ReadStore) left right,
          (forall address,
            storeA.readWord? 0 address = storeB.readWord? 0 address) ->
            RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeA left right =
              RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
                xs storeB left right) /\
'@
$physicalStaticProof = @'
      fun storeA storeB left right hagree =>
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
          xs storeA storeB left right (fun address _ => hagree address),
'@
Run-PublicPinCase 'P05' {
  param($theoremText)
  $theoremText = Replace-ExactOnce $theoremText $physicalConjunct $physicalStaticConjunct 'P05 static conjunct'
  Replace-ExactOnce $theoremText $physicalProof $physicalStaticProof 'P05 static proof'
}

Run-Case 'C01' 'ACCEPT' {
  param($caseRoot)
  $text = Read-Shadow $caseRoot $classicPath
  $text = Remove-RecordField $text 'structure ReviewerNativeMachineAdequacy' ($lf + $lf + '/-- The ordinary-list construction satisfies the guarded reviewer packet.') 'exact_dynamic_logical_store_agreement'
  $initializerStart =
    '      exact_dynamic_logical_store_agreement := by' + $lf
  $initializerEnd =
    '      physical_value_projection_of_valid :='
  $start = $text.IndexOf(
    $initializerStart, [StringComparison]::Ordinal)
  if ($start -lt 0) {
    throw 'C01 initializer start not found'
  }
  $end = $text.IndexOf(
    $initializerEnd, $start, [StringComparison]::Ordinal)
  if ($end -lt 0) {
    throw 'C01 initializer end not found'
  }
  $text = $text.Remove($start, $end - $start)
  Write-Shadow $caseRoot $classicPath $text
  $classic = Invoke-ShadowLean $caseRoot $classicPath 'packet-only deletion'
  Require-Accept $classic
  $headline = Invoke-ShadowLean $caseRoot $headlinePath 'unchanged paper theorem'
  Require-Accept $headline
  $checker = Invoke-ShadowLean $caseRoot $checkerPath 'frozen public expected type'
  Require-Accept $checker
}
} catch {
  Write-Host "M1-MUTATION FAIL [SEMANTIC-DISPATCH] $($_.Exception.Message)"
  $failures += 1
} finally {
  try {
    Assert-LiveIntegrity 'FINAL'
    Remove-SweepRoot
  } catch {
    Write-Host "M1-MUTATION FAIL [FINAL] $($_.Exception.Message)"
    $failures += 1
  }
}

Pop-Location

if ($failures -ne 0) {
  Write-Host "M1-MUTATION FAIL ($failures failures; $passes passes)"
  exit 1
}
$expectedEntries = @(
  if ($OnlyCase -eq '') {
    $caseRegistry
  } else {
    $caseRegistry | Where-Object { $_.Id -ceq $OnlyCase }
  }
)
$expectedPasses = $expectedEntries.Count
if ($passes -ne $expectedPasses) {
  Write-Host (
    "M1-MUTATION FAIL (expected $expectedPasses passes; observed $passes)")
  exit 1
}
$expectedExecutedIds = @($expectedEntries | ForEach-Object { [string]$_.Id })
if (($executedIds -join ',') -cne ($expectedExecutedIds -join ',')) {
  Write-Host (
    'M1-MUTATION FAIL (executed registry mismatch: expected ' +
    "$($expectedExecutedIds -join ','); observed $($executedIds -join ','))")
  exit 1
}
$expectedRejects = @(
  $expectedEntries | Where-Object { $_.Verdict -ceq 'REJECT' }).Count
$expectedAccepts = @(
  $expectedEntries | Where-Object { $_.Verdict -ceq 'ACCEPT' }).Count
if ($rejectPasses -ne $expectedRejects -or $acceptPasses -ne $expectedAccepts) {
  Write-Host (
    'M1-MUTATION FAIL (verdict totals mismatch: expected ' +
    "reject=$expectedRejects accept=$expectedAccepts; observed " +
    "reject=$rejectPasses accept=$acceptPasses)")
  exit 1
}
if ($OnlyCase -eq '') {
  Write-Host (
    'M1-MUTATION PASS (41 executed; 40 expected rejects; 1 expected accept; ' +
    'live hashes/tracked state unchanged)')
} else {
  Write-Host (
    "M1-MUTATION PASS ($OnlyCase; 1 executed; " +
    "reject=$rejectPasses accept=$acceptPasses; " +
    'live hashes/tracked state unchanged)')
}
exit 0

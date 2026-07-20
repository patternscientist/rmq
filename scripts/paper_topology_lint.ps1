#!/usr/bin/env pwsh

param(
  [string]$MutationPath = '',
  [string]$MutationText = '',
  [string]$MutationRemoveText = '',
  [string]$MutationTextBase64 = '',
  [string]$MutationRemoveTextBase64 = '',
  [ValidateSet('', 'A01', 'A02', 'R1LEGACY')]
  [string]$MutationCase = '',
  [ValidateRange(1, 3600)]
  [int]$StageDeadlineSeconds = 300,
  [ValidateRange(4096, 16777216)]
  [int]$StageOutputLimitBytes = 4194304,
  [string]$LaunchReleasePath = ''
)

$ErrorActionPreference = 'Stop'
$failures = 0

# A release-gated launch must block before dot-sourcing the shared helper,
# because Add-Type may itself initialize platform machinery.  This keeps the
# root quiescent until the parent has assigned Windows Job / POSIX group
# ownership.
if ($LaunchReleasePath -ne '') {
  while (-not (Test-Path -LiteralPath $LaunchReleasePath -PathType Leaf)) {
    Start-Sleep -Milliseconds 10
  }
}

. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')

$repoRoot = [IO.Path]::GetFullPath((Get-Location).Path)
$ownedTempRoot = [IO.Path]::GetFullPath([IO.Path]::GetTempPath())

$pathKeys = @(
  [Environment]::GetEnvironmentVariables().Keys |
    Where-Object { [string]$_ -ieq 'path' })
if ($pathKeys.Count -gt 1 -and $pathKeys -ccontains 'PATH') {
  Remove-Item Env:PATH -ErrorAction Stop
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
} elseif ($MutationCase -ceq 'R1LEGACY') {
  $MutationPath = 'RMQ/Core/SuccinctFinalModelAdequacy.lean'
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
  return Invoke-RMQOwnedBoundedProcess `
    -FilePath $FilePath `
    -Arguments $Arguments `
    -WorkingDirectory $repoRoot `
    -Stage $Stage `
    -DeadlineSeconds $StageDeadlineSeconds `
    -OutputLimitBytes $StageOutputLimitBytes `
    -TempRoot $ownedTempRoot `
    -Environment $Environment
}

# M1R5R1-CLEAN-BASELINE
# Virtual topology mutations are permitted only from an actually clean live
# repository.  A dirty initial state is never accepted as a restoration target.
$topologyInitialState = Get-RMQRepositoryStateBounded `
  -RepositoryRoot $repoRoot `
  -GitPath ((Get-Command git -CommandType Application -ErrorAction Stop).Source) `
  -DeadlineSeconds $StageDeadlineSeconds `
  -OutputLimitBytes $StageOutputLimitBytes `
  -TempRoot $ownedTempRoot `
  -StagePrefix 'paper-topology-live-state'
Assert-RMQCleanRepositoryStateText `
  $topologyInitialState 'production topology lint live baseline'

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
    } elseif ($MutationCase -ceq 'R1LEGACY') {
      $modelLineBreak = if ($text.Contains("`r`n")) { "`r`n" } else { "`n" }
      $needle =
        '  exact' + $modelLineBreak +
        '    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint'
      if (-not $text.Contains($needle)) {
        throw 'R1LEGACY current-safe mutation anchor is missing'
      }
      $legacyCall =
        '  exact' + $modelLineBreak +
        '    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint' +
        $modelLineBreak + '      shape hfoot left right' +
        $modelLineBreak + $needle
      $mutated = $text.Replace($needle, $legacyCall)
      if ($mutated -ceq $text) {
        throw 'R1LEGACY did not mutate the current safe theorem body'
      }
      $text = $mutated
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

function Get-ExactDeclarationBlock(
    [string]$Text,
    [string]$StartNeedle,
    [string]$EndNeedle,
    [string]$Label) {
  $start = $Text.IndexOf($StartNeedle, [StringComparison]::Ordinal)
  if ($start -lt 0) { throw "$Label start is missing" }
  if ($Text.IndexOf(
      $StartNeedle, $start + $StartNeedle.Length,
      [StringComparison]::Ordinal) -ge 0) {
    throw "$Label start is not unique"
  }
  $end = $Text.IndexOf(
    $EndNeedle, $start + $StartNeedle.Length,
    [StringComparison]::Ordinal)
  if ($end -lt 0) { throw "$Label end is missing" }
  return $Text.Substring($start, $end - $start)
}

function Assert-CurrentSafeDependencyRoute(
    [string]$StoreParamText,
    [string]$ModelText,
    [string]$ClassicText,
    [string]$HeadlineText,
    [string]$CheckerText) {
  $legacy =
    'concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint'
  $legacyPattern = '(?<![A-Za-z0-9_])' + [regex]::Escape($legacy) +
    '(?![A-Za-z0-9_])'
  if ([regex]::Matches($StoreParamText, $legacyPattern).Count -lt 1) {
    throw 'legacy compatibility theorem is no longer available'
  }
  $structural = Get-ExactDeclarationBlock $StoreParamText `
    'private def concreteBPNativeSuccinctRMQWithStoreReadSegmentLive' `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint' `
    'structural containment helpers and direct theorem'
  $direct = Get-ExactDeclarationBlock $StoreParamText `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt' `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint' `
    'direct segment containment'
  $subset = Get-ExactDeclarationBlock $StoreParamText `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint' `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_reads_subset_footprint' `
    'safe footprint containment'
  $bridge = Get-ExactDeclarationBlock $ModelText `
    'theorem concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_of_footprint' `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint_via_orderedReadFootprint' `
    'safe-to-dynamic bridge'
  $currentSafe = Get-ExactDeclarationBlock $ModelText `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint_via_orderedReadFootprint' `
    'theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint_via_orderedReadFootprint' `
    'current safe equality'
  $packet = Get-ExactDeclarationBlock $ClassicText `
    'structure ReviewerNativeMachineAdequacy' `
    'theorem listIntSuccinctRMQReviewerNativeMachineAdequacy' `
    'guarded reviewer packet'
  $constructor = Get-ExactDeclarationBlock $ClassicText `
    'theorem listIntSuccinctRMQReviewerNativeMachineAdequacy' `
    'theorem shape_queryOffset?_eq_scanWindow' `
    'guarded reviewer packet constructor'
  $paper = Get-ExactDeclarationBlock $HeadlineText `
    'theorem listIntSuccinctRMQPaperMainTheorem' `
    'abbrev succinctRMQReviewerMachineWellFormed' `
    'literal paper theorem'
  $expected = Get-ExactDeclarationBlock $CheckerText `
    'def M1ReviewerNativeExpectedPaperType' `
    'example : M1ReviewerNativeExpectedPaperType' `
    'independent expected type'
  foreach ($surface in @(
      [pscustomobject]@{ Label = 'structural-containment'; Text = $structural },
      [pscustomobject]@{ Label = 'direct'; Text = $direct },
      [pscustomobject]@{ Label = 'subset'; Text = $subset },
      [pscustomobject]@{ Label = 'bridge'; Text = $bridge },
      [pscustomobject]@{ Label = 'current-safe'; Text = $currentSafe },
      [pscustomobject]@{ Label = 'packet'; Text = $packet },
      [pscustomobject]@{ Label = 'packet-constructor'; Text = $constructor },
      [pscustomobject]@{ Label = 'paper'; Text = $paper })) {
    if ([regex]::IsMatch($surface.Text, $legacyPattern)) {
      throw "legacy safe equality entered $($surface.Label) dependency surface"
    }
  }
  foreach ($pin in @(
      [pscustomobject]@{ Label = 'structural select'; Text = $structural;
        Token = 'concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'structural rank'; Text = $structural;
        Token = 'concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'structural LCA'; Text = $structural;
        Token = 'concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'structural interior'; Text = $structural;
        Token = 'concreteBPNativeInteriorWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'structural instruction'; Text = $structural;
        Token = 'WholeQueryInstr.evalGlobalWordTraceWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'direct program'; Text = $direct;
        Token = 'WholeQueryProgram.evalGlobalWordTraceWithStore_withStoreReadSegmentLive' },
      [pscustomobject]@{ Label = 'subset direct theorem'; Text = $subset;
        Token = 'concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt' },
      [pscustomobject]@{ Label = 'bridge direct theorem'; Text = $bridge;
        Token = 'concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_read_segment_lt' },
      [pscustomobject]@{ Label = 'safe dynamic theorem'; Text = $currentSafe;
        Token = 'store_parametric_of_ordered_read_footprint' },
      [pscustomobject]@{ Label = 'safe bridge'; Text = $currentSafe;
        Token = 'StoresAgreeOnOrderedReadFootprint_of_footprint' },
      [pscustomobject]@{ Label = 'packet safe field'; Text = $packet;
        Token = 'safe_logical_store_agreement' },
      [pscustomobject]@{ Label = 'packet constructor'; Text = $constructor;
        Token = 'store_parametric_of_footprint_via_orderedReadFootprint' },
      [pscustomobject]@{ Label = 'paper projection'; Text = $paper;
        Token = '.safe_logical_store_agreement' },
      [pscustomobject]@{ Label = 'expected proposition'; Text = $expected;
        Token = 'storesAgreeOnFootprint' })) {
    if (-not $pin.Text.Contains($pin.Token)) {
      throw "$($pin.Label) token is missing: $($pin.Token)"
    }
  }
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
    $userProfilePath = $env:USERPROFILE
    if ([string]::IsNullOrWhiteSpace($userProfilePath)) {
      $userProfilePath =
        [Environment]::GetFolderPath([Environment+SpecialFolder]::UserProfile)
    }
    $toolchainRoot = Join-Path (
      Join-Path (Join-Path $userProfilePath '.elan') 'toolchains') `
      $toolchainDirectoryName
    $leanBinaryName = if ([Environment]::OSVersion.Platform -eq
        [PlatformID]::Win32NT) { 'lean.exe' } else { 'lean' }
    $leanExe = Join-Path (Join-Path $toolchainRoot 'bin') $leanBinaryName
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
$storeParamModule = 'RMQ/Core/SuccinctFinalStoreParam.lean'
$finalModelModule = 'RMQ/Core/SuccinctFinalModelAdequacy.lean'
$classicModule = 'RMQ/Core/SuccinctRMQClassic.lean'
$compatibilityModule = 'RMQ/Headlines/RMQCompatibility.lean'
$paperRoot = 'RMQPaper.lean'
$aggregateModule = 'RMQ/Headlines.lean'
$headlineInventory = 'scripts/headline_axiom_check.lean'
$gateScript = 'scripts/gate.ps1'
$m1MutationRunner = 'scripts/m1_certificate_mutation_regression.ps1'
$ownedProcessHelper = 'scripts/owned_process_tree.ps1'
$topologyRegression = 'scripts/paper_topology_lint_regression.ps1'
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
  $storeParamModule,
  $finalModelModule,
  $classicModule,
  $canonicalModule,
  $compatibilityModule,
  $paperRoot,
  $aggregateModule,
  $headlineInventory,
  $gateScript,
  $m1MutationRunner,
  $ownedProcessHelper,
  $topologyRegression
) + $publicClaimSurfaces

$requiredFiles += @($frozenSnapshotLines.Keys)

foreach ($path in $requiredFiles) {
  [void](Require-File $path)
}

if ($failures -gt 0) {
  exit 1
}

# The direct segment<23 theorem is checked by Lean; this topology control pins
# the current dependency route and rejects any virtual reinsertion of the
# legacy safe-equality theorem into its load-bearing chain.
try {
  Assert-CurrentSafeDependencyRoute `
    (Read-Text $storeParamModule) `
    (Read-Text $finalModelModule) `
    (Read-Text $classicModule) `
    (Read-Text $canonicalModule) `
    (Read-Text $headlineInventory)
  Write-Host (
    'PAPER-TOPOLOGY: PASS [m1-safe-dependency] ' +
    'direct segment<23 -> safe-to-dynamic -> ordered equality -> packet -> paper')
} catch {
  Fail "[m1-safe-dependency] $($_.Exception.Message)"
}

# M1 R3 public-dependency enforcement is itself part of the paper topology.
# Require both the frozen expected-type consumer and the literal aggregate-gate
# runner invocation; declaration-name or current-type-only checks are
# insufficient.  Accumulate these directly related diagnostics even when the
# safe-dependency check already failed, so topology case A01 continues to pin
# its original public expected-type rejection surface.
$headlineInventoryText = Read-Text $headlineInventory
$gateScriptText = Read-Text $gateScript
$m1MutationRunnerText = Read-Text $m1MutationRunner
$ownedProcessHelperText = Read-Text $ownedProcessHelper
$topologyRegressionText = Read-Text $topologyRegression
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
    'REPLAY-SUBPROCESS-DEADLINE',
    'SAFE-DEPENDENCY-ROUTE',
    'Assert-RMQCleanRepositoryStateText',
    'Invoke-RMQOwnedBoundedProcess')) {
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
foreach ($pin in @(
    'RMQOwnedWindowsJob',
    'Get-RMQOwnedLaunchPlan',
    'setsid-process-group',
    'Stop-RMQPosixOwnedProcessGroup',
    'Invoke-RMQCleanBaselineFixtureTests')) {
  if (-not $ownedProcessHelperText.Contains($pin)) {
    Fail "[owned-process-helper] production helper is missing $pin"
  }
}
foreach ($pin in @(
    "ContainsKey('OnlyCase')",
    'Invoke-TopologySafeDependencyAntiBypassSelfTest',
    'Invoke-TopologyDeadlineSelfTest',
    'Assert-RMQCleanRepositoryStateText',
    'Invoke-RMQOwnedBoundedProcess')) {
  if (-not $topologyRegressionText.Contains($pin)) {
    Fail "[topology-regression-portability] production regression is missing $pin"
  }
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

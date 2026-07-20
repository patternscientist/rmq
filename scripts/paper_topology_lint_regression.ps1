#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$OnlyCase = '',
  [ValidateRange(30, 3600)]
  [int]$StageDeadlineSeconds = 300,
  [ValidateRange(4096, 16777216)]
  [int]$StageOutputLimitBytes = 4194304,
  [ValidateRange(1, 30)]
  [int]$SelfTestDeadlineSeconds = 5,
  [switch]$SelectorBoundaryProbeOnly,
  [switch]$SelectorSelfTestOnly,
  [switch]$DeadlineSelfTestOnly,
  [switch]$PortabilitySelfTestOnly
)

$ErrorActionPreference = 'Stop'
$onlyCaseWasBound = $PSBoundParameters.ContainsKey('OnlyCase')
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')

$pathKeys = @(
  [Environment]::GetEnvironmentVariables().Keys |
    Where-Object { [string]$_ -ieq 'path' })
if ($pathKeys.Count -gt 1 -and $pathKeys -ccontains 'PATH') {
  Remove-Item Env:PATH -ErrorAction Stop
}
$repoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$lintPath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot 'paper_topology_lint.ps1'))
$shellPath = (Get-Process -Id $PID).Path
$ownedTempRoot = [IO.Path]::GetFullPath([IO.Path]::GetTempPath())
$failures = 0
$executedCount = 0
$rejectCount = 0
$acceptCount = 0
$executedIds = [Collections.Generic.List[string]]::new()
$integrityPaths = @(
  'scripts/headline_axiom_check.lean',
  'scripts/gate.ps1',
  'scripts/m1_certificate_mutation_regression.ps1',
  'scripts/owned_process_tree.ps1',
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

$selectedCases = @()
if (-not $onlyCaseWasBound) {
  $selectedCases = @($caseRegistry)
} elseif ([string]::IsNullOrWhiteSpace($OnlyCase) -or $OnlyCase -ceq '0') {
  Write-Host (
    'PAPER-TOPOLOGY-REGRESSION: FAIL [SELECTOR] ' +
    'bound empty/whitespace/zero selector is invalid')
  exit 1
} else {
  $selectedCases = @(
    $caseRegistry | Where-Object { $_.Id -ceq $OnlyCase })
}
if ($selectedCases.Count -ne $(if ($onlyCaseWasBound) { 1 } else { 16 })) {
  Write-Host (
    "PAPER-TOPOLOGY-REGRESSION: FAIL [SELECTOR] unknown case $OnlyCase; " +
    "available=$(@($caseRegistry | ForEach-Object { $_.Id }) -join ',')")
  exit 1
}

if ($SelectorBoundaryProbeOnly) {
  Write-Host (
    'PAPER-TOPOLOGY-REGRESSION BOUNDARY PROBE PASS ' +
    "(bound=$onlyCaseWasBound; selected=$($selectedCases.Count); " +
    "ids=$((@($selectedCases | ForEach-Object { $_.Id })) -join ','))")
  exit 0
}

function Get-TrackedState {
  return Get-RMQRepositoryStateBounded `
    -RepositoryRoot $repoRoot `
    -GitPath ((Get-Command git -CommandType Application -ErrorAction Stop).Source) `
    -DeadlineSeconds $StageDeadlineSeconds `
    -OutputLimitBytes $StageOutputLimitBytes `
    -TempRoot $ownedTempRoot `
    -StagePrefix 'paper-topology-regression-live-state'
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
  return Invoke-RMQOwnedBoundedProcess `
    -FilePath $FilePath `
    -Arguments $Arguments `
    -WorkingDirectory $repoRoot `
    -Stage $Stage `
    -DeadlineSeconds $DeadlineSeconds `
    -OutputLimitBytes $StageOutputLimitBytes `
    -TempRoot $ownedTempRoot `
    -ReleaseGatedScript:$ReleaseGatedScript
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

function Invoke-TopologySelectorBoundarySelfTest {
  $wrapperPath = Join-Path $ownedTempRoot (
    'rmq-topology-selector-' + [Guid]::NewGuid().ToString('N') + '.ps1')
  $encoding = [Text.UTF8Encoding]::new($false)
  $wrapper = @'
param([string]$Target, [string]$Mode)
$ErrorActionPreference = 'Continue'
switch ($Mode) {
  'omitted' { & $Target -SelectorBoundaryProbeOnly }
  'empty' { & $Target -SelectorBoundaryProbeOnly -OnlyCase '' }
  'whitespace' { & $Target -SelectorBoundaryProbeOnly -OnlyCase ' ' }
  'zero' { & $Target -SelectorBoundaryProbeOnly -OnlyCase '0' }
  'unknown' { & $Target -SelectorBoundaryProbeOnly -OnlyCase 'UNKNOWN' }
  'valid-a01' { & $Target -SelectorBoundaryProbeOnly -OnlyCase 'A01' }
  default { throw "unknown topology boundary wrapper mode $Mode" }
}
exit ([int]$LASTEXITCODE)
'@
  $cases = @(
    [pscustomobject]@{ Mode = 'omitted'; Exit = 0; Token = 'selected=16' },
    [pscustomobject]@{ Mode = 'valid-a01'; Exit = 0; Token = 'selected=1; ids=A01' },
    [pscustomobject]@{ Mode = 'empty'; Exit = 1; Token = 'bound empty/whitespace/zero' },
    [pscustomobject]@{ Mode = 'whitespace'; Exit = 1; Token = 'bound empty/whitespace/zero' },
    [pscustomobject]@{ Mode = 'zero'; Exit = 1; Token = 'bound empty/whitespace/zero' },
    [pscustomobject]@{ Mode = 'unknown'; Exit = 1; Token = 'unknown case' }
  )
  try {
    [IO.File]::WriteAllText($wrapperPath, $wrapper, $encoding)
    foreach ($case in $cases) {
      $result = Invoke-BoundedTool `
        -FilePath $shellPath `
        -Arguments @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
          '-File', $wrapperPath, '-Target', $PSCommandPath,
          '-Mode', $case.Mode) `
        -Stage "topology-selector-$($case.Mode)" `
        -DeadlineSeconds $StageDeadlineSeconds
      $joined = $result.Output -join [Environment]::NewLine
      if ($result.TimedOut -or $result.OutputLimitExceeded -or
          $result.ExitCode -ne $case.Exit -or
          -not $joined.Contains($case.Token)) {
        throw (
          "boundary $($case.Mode) expected exit=$($case.Exit) " +
          "token=$($case.Token); observed exit=$($result.ExitCode) " +
          "timeout=$($result.TimedOut) outputLimit=$($result.OutputLimitExceeded) " +
          "output=$joined")
      }
      if ($case.Exit -ne 0 -and
          $joined.Contains('PAPER-TOPOLOGY-REGRESSION: PASS [')) {
        throw "boundary $($case.Mode) reached topology case execution"
      }
      Write-Host (
        "PAPER-TOPOLOGY-REGRESSION BOUNDARY CONTROL PASS [$($case.Mode)] " +
        "exit=$($result.ExitCode)")
    }
  } finally {
    Remove-Item -LiteralPath $wrapperPath -Force -ErrorAction SilentlyContinue
  }
}

function Invoke-TopologyDeadlineSelfTest {
  $stem = Join-Path $ownedTempRoot (
    'rmq-topology-sleeper-' + [Guid]::NewGuid().ToString('N'))
  $scriptPath = $stem + '.ps1'
  $childPidPath = $stem + '.child.pid'
  $encoding = [Text.UTF8Encoding]::new($false)
  $quotedShellPath = $shellPath.Replace("'", "''")
  $quotedPidPath = $childPidPath.Replace("'", "''")
  $scriptText = @"
`$child = Start-Process -FilePath '$quotedShellPath' -ArgumentList @(
  '-NoLogo', '-NoProfile', '-Command', 'Start-Sleep -Seconds 60') -PassThru
[IO.File]::WriteAllText('$quotedPidPath', [string]`$child.Id)
Start-Sleep -Seconds 60
"@
  try {
    [IO.File]::WriteAllText($scriptPath, $scriptText, $encoding)
    $result = Invoke-BoundedTool `
      -FilePath $shellPath `
      -Arguments @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $scriptPath) `
      -Stage 'topology-deadline-sleeper' `
      -DeadlineSeconds $SelfTestDeadlineSeconds
    if (-not $result.TimedOut -or $result.OutputLimitExceeded) {
      throw (
        "sleeper expected deadline timeout; timeout=$($result.TimedOut) " +
        "outputLimit=$($result.OutputLimitExceeded)")
    }
    if (-not (Test-Path -LiteralPath $childPidPath -PathType Leaf)) {
      throw 'sleeper child PID receipt was not written'
    }
    $childId = [int]([IO.File]::ReadAllText($childPidPath).Trim())
    if ($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)) {
      throw "sleeper child $childId survived owned-tree termination"
    }
    Write-Host (
      'PAPER-TOPOLOGY-REGRESSION DEADLINE CONTROL PASS ' +
      "(ownership=$($result.Ownership); child=$childId absent; " +
      "duration=$($result.DurationSeconds)s)")
  } finally {
    Remove-Item -LiteralPath $scriptPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $childPidPath -Force -ErrorAction SilentlyContinue
  }
}

function Invoke-TopologySafeDependencyAntiBypassSelfTest {
  $arguments = @(
    '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
    '-File', $lintPath,
    '-MutationCase', 'R1LEGACY',
    '-StageDeadlineSeconds', [string]([Math]::Max(1, $StageDeadlineSeconds - 15)),
    '-StageOutputLimitBytes', [string]$StageOutputLimitBytes)
  $result = Invoke-BoundedTool `
    -FilePath $shellPath `
    -Arguments $arguments `
    -Stage 'topology-safe-dependency-antibypass' `
    -DeadlineSeconds $StageDeadlineSeconds `
    -ReleaseGatedScript
  $joined = $result.Output -join [Environment]::NewLine
  if ($result.TimedOut -or $result.OutputLimitExceeded -or
      $result.ExitCode -eq 0 -or
      -not $joined.Contains(
        'legacy safe equality entered current-safe dependency surface')) {
    throw (
      "safe-dependency mutation expected precise rejection; " +
      "exit=$($result.ExitCode) timeout=$($result.TimedOut) " +
      "outputLimit=$($result.OutputLimitExceeded) output=$joined")
  }
  Write-Host (
    'PAPER-TOPOLOGY-REGRESSION SAFE-DEPENDENCY CONTROL PASS ' +
    '(legacy current-safe reinsertion rejected outside the 16-case registry)')
}

$initialTrackedState = Get-TrackedState
Assert-RMQCleanRepositoryStateText `
  $initialTrackedState 'topology regression live baseline'
$baselineTrackedState = $initialTrackedState
$baselineHashes = Get-LiveHashes

Invoke-RMQOwnedProcessDeterministicTests
Invoke-RMQCleanBaselineFixtureTests `
  -GitPath ((Get-Command git -CommandType Application -ErrorAction Stop).Source) `
  -DeadlineSeconds $StageDeadlineSeconds `
  -OutputLimitBytes $StageOutputLimitBytes `
  -TempRoot $ownedTempRoot
Assert-LiveIntegrity 'portable-process-and-clean-baseline-self-tests'

Invoke-TopologySelectorBoundarySelfTest
Assert-LiveIntegrity 'selector-boundary-self-test'
if ($SelectorSelfTestOnly) {
  exit 0
}

Invoke-TopologySafeDependencyAntiBypassSelfTest
Assert-LiveIntegrity 'safe-dependency-antibypass-self-test'

Invoke-TopologyDeadlineSelfTest
Assert-LiveIntegrity 'deadline-sleeper-self-test'
if ($DeadlineSelfTestOnly -or $PortabilitySelfTestOnly) {
  exit 0
}

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

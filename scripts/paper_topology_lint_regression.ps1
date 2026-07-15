#!/usr/bin/env pwsh

$ErrorActionPreference = 'Stop'

$repoRoot = [IO.Path]::GetFullPath((Get-Location).Path)
$lintPath = [IO.Path]::GetFullPath('scripts/paper_topology_lint.ps1')
$shellPath = (Get-Process -Id $PID).Path
$failures = 0
$rejectCount = 0
$acceptCount = 0

if (-not (Test-Path -LiteralPath $lintPath)) {
  Write-Host "PAPER-TOPOLOGY-REGRESSION: missing lint $lintPath"
  exit 1
}

# Resolve the unchanged documentary name inventories once through the full
# production lint. Mutations below exercise the same production semantic and
# topology checks; none needs to repay the two generated Lean imports because
# the only accepting documentary identifier is already in the baseline set.
$baselineOutput = @(& $shellPath -NoLogo -NoProfile -ExecutionPolicy Bypass `
    -File $lintPath 2>&1)
if ($LASTEXITCODE -ne 0) {
  Write-Host 'PAPER-TOPOLOGY-REGRESSION: baseline production lint failed'
  $baselineOutput | ForEach-Object { Write-Host "  $_" }
  exit 1
}
Write-Host 'PAPER-TOPOLOGY-REGRESSION: PASS [baseline-production-lint] ACCEPT'

function Get-TrackedState {
  Push-Location $repoRoot
  try {
    return (@(
      & git -c core.excludesfile= -c core.autocrlf=false status --short --untracked-files=all
      '---WORKTREE---'
      & git -c core.excludesfile= -c core.autocrlf=false diff --raw --no-ext-diff --
      '---INDEX---'
      & git -c core.excludesfile= -c core.autocrlf=false diff --cached --raw --no-ext-diff --
    ) -join [Environment]::NewLine)
  } finally {
    Pop-Location
  }
}

function Test-Mutation(
    [string]$Id,
    [string]$Path,
    [string]$Text,
    [bool]$Reject,
    [string]$RemoveText = '') {
  $before = Get-TrackedState
  Push-Location $repoRoot
  try {
    $arguments = @(
      '-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
      '-File', $lintPath, '-MutationPath', $Path, '-MutationText', $Text,
      '-SkipLeanResolution', '-MutationFocused')
    if ($RemoveText -ne '') {
      $arguments += @('-MutationRemoveText', $RemoveText)
    }
    $output = @(& $shellPath @arguments 2>&1)
    $code = $LASTEXITCODE
  } finally {
    Pop-Location
  }
  $after = Get-TrackedState

  if ($before -ne $after) {
    Write-Host "PAPER-TOPOLOGY-REGRESSION: FAIL [$Id] mutation changed tracked state"
    $script:failures += 1
    return
  }

  $passed = if ($Reject) { $code -ne 0 } else { $code -eq 0 }
  $verdict = if ($Reject) { 'REJECT' } else { 'ACCEPT' }
  if (-not $passed) {
    Write-Host "PAPER-TOPOLOGY-REGRESSION: FAIL [$Id] expected $verdict"
    $output | ForEach-Object { Write-Host "  $_" }
    $script:failures += 1
    return
  }

  if ($Reject) { $script:rejectCount += 1 } else { $script:acceptCount += 1 }
  Write-Host "PAPER-TOPOLOGY-REGRESSION: PASS [$Id] $verdict"
}

$fencedTransitional = @'
```lean
#check RMQ.Headlines.succinctRMQCanonicalTransitionalQueryCostEq
```
'@
$retiredAlias =
  'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'
$exactFrozenLine =
  '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'

Test-Mutation 'retired-alias-in-prose' 'README.md' 'Current capstone: RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery.' $true
Test-Mutation 'transitional-alias-in-fence' 'docs/PAPER_THEOREM_MAP.md' $fencedTransitional $true
Test-Mutation 'dead-documentary-alias' 'docs/PAPER_THEOREM_MAP.md' 'Current capstone: RMQ.Headlines.succinctRMQInventedDeadPaperAnchor.' $true
Test-Mutation 'renamed-w18-alias' 'docs/FAMILY_SUMMARY.md' 'Current evidence: RMQ.Headlines.listIntSuccinctRMQEventValueProducerProvenanceOfValid.' $true
Test-Mutation 'compatibility-as-current-anchor' 'docs/PAPER_THEOREM_MAP.md' 'Current capstone: RMQ.Headlines.succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreExecutionStory.' $true
Test-Mutation 'canonical-paper-anchor' 'README.md' 'Current capstone: RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile.' $false
Test-Mutation 'retired-alias-current-publication-digest' 'docs/digests/PROJECT_DIGESTION_CURRENT.md' "Current capstone: $retiredAlias." $true
Test-Mutation 'retired-current-alias-audit-report' 'docs/internal/audit_reports/2026-07-14_A04_u2_blind_acceptance_audit.md' "Current capstone: $retiredAlias." $true
Test-Mutation 'valid-exact-frozen-snapshot-occurrence' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' $exactFrozenLine $false $exactFrozenLine
Test-Mutation 'same-frozen-occurrence-current-digest' 'docs/digests/PROJECT_DIGESTION_CURRENT.md' $exactFrozenLine $true
Test-Mutation 'casual-frozen-history-marker' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' "[FROZEN-HISTORY: casual] $retiredAlias" $true
Test-Mutation 'forged-duplicate-exact-marker' 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' $exactFrozenLine $true
Test-Mutation 'current-public-all-size-4144' 'README.md' 'The public all-size bound is 4144.' $true
Test-Mutation 'current-public-negation-does-not-allow-4144' 'README.md' 'The public all-size bound is not 4144.' $true
Test-Mutation 'current-public-ready-118' 'docs/FAMILY_SUMMARY.md' 'The Ready threshold costs 118.' $true
Test-Mutation 'current-public-route-dispatch' 'docs/digests/PROJECT_DIGESTION_CURRENT.md' 'The current Ready/non-Ready/zero-block dispatch selects the large regime.' $true
Test-Mutation 'current-public-2pow128-activation' 'docs/PAPER_THEOREM_MAP.md' 'The current canonical reviewer execution activates at 2^128.' $true
Test-Mutation 'current-public-canonical-76' 'README.md' 'The canonical reviewer payload and canonical global trace have uniform charged-trace bound 76; controller operations remain outside the charged event model, so this is not a conventional word-RAM theorem.' $false
Test-Mutation 'compatibility-old-route-history' 'docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md' 'Compatibility history: the former route-split all-size bound was 4144 and the Ready threshold cost was 118; the zero-block route remains historical.' $false
Test-Mutation 'compatibility-2pow128-history' 'docs/digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md' 'Compatibility theorem: 2^128 is retained only as an explicit sufficient premise.' $false

if ($failures -gt 0) {
  Write-Host "PAPER-TOPOLOGY-REGRESSION: $failures failures"
  exit 1
}

Write-Host "PAPER-TOPOLOGY-REGRESSION PASS ($rejectCount reject; $acceptCount accept; tracked state unchanged)"
exit 0

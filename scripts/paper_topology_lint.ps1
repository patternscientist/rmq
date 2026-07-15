#!/usr/bin/env pwsh

$ErrorActionPreference = 'Stop'
$failures = 0

function Fail([string]$Message) {
  Write-Host "PAPER-TOPOLOGY: FAIL $Message"
  $script:failures += 1
}

function Require-File([string]$Path) {
  if (-not (Test-Path -LiteralPath $Path)) {
    Fail "missing required file $Path"
    return $false
  }
  return $true
}

function Read-Text([string]$Path) {
  return Get-Content -Raw -LiteralPath $Path
}

$canonicalModule = 'RMQ/Headlines/RMQ.lean'
$compatibilityModule = 'RMQ/Headlines/RMQCompatibility.lean'
$paperRoot = 'RMQPaper.lean'
$aggregateModule = 'RMQ/Headlines.lean'
$headlineInventory = 'scripts/headline_axiom_check.lean'

$currentLeanSurfaces = @($canonicalModule, $paperRoot, $headlineInventory)
$publicClaimSurfaces = @(
  'README.md',
  'artifact/CLAIMS.md',
  'docs/FAMILY_SUMMARY.md',
  'docs/PAPER_CLAIM_CORRESPONDENCE.md',
  'docs/PAPER_THEOREM_MAP.md',
  'docs/PAPER_MAIN_THEOREM.md',
  'docs/PAPER_MODEL_ADEQUACY.md',
  'docs/WHAT_IS_PROVED.md'
)

$requiredFiles = @(
  $canonicalModule,
  $compatibilityModule,
  $paperRoot,
  $aggregateModule,
  $headlineInventory
) + $publicClaimSurfaces

foreach ($path in $requiredFiles) {
  [void](Require-File $path)
}

if ($failures -gt 0) {
  exit 1
}

$retiredAliases = @(
  'succinctRMQTwoNPlusOConstantQuery',
  'succinctRMQTwoNPlusOConstantQueryInterpreted',
  'succinctRMQTwoNPlusOConstantQueryLeafTrace',
  'succinctRMQTwoNPlusOConstantQueryWordTrace',
  'succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime',
  'succinctRMQTwoNPlusOConstantQueryGlobalWordTraceLargeRegime'
)

$retiredSourcePattern =
  'builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_(?:profile|whole_query_(?:interpreted|leaf_trace|word_trace(?:_large_regime)?|global_word_trace_large_regime)_profile)'
$oldRegimePattern =
  '(?i)(?:\b(?:196727|328|118|4144)\b|2\s*\^\s*128|zero[- ]?block|\bReady\b|LargeRegime|large[- ]regime|CanonicalTransitional)'

foreach ($path in $currentLeanSurfaces) {
  $text = Read-Text $path
  foreach ($name in $retiredAliases) {
    if ($text -match ([regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
      Fail "$path contains retired paper alias $name"
    }
  }
  if ($text -match $retiredSourcePattern) {
    Fail "$path directly cites a retired source profile"
  }
  if ($text -match $oldRegimePattern) {
    Fail "$path contains an old cost/regime token"
  }
}

foreach ($path in $publicClaimSurfaces) {
  $text = Read-Text $path
  foreach ($name in $retiredAliases) {
    if ($text -match ([regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
      Fail "$path presents retired paper alias $name"
    }
  }
  $lineNumber = 0
  foreach ($line in Get-Content -LiteralPath $path) {
    $lineNumber += 1
    if ($line -match '^\s*\|' -and $line -match $retiredSourcePattern) {
      Fail "$path`:$lineNumber presents a retired source profile in a current table row"
    }
    if (
      $line -match '^\s*\|' -and
      $line -match '(?:RMQ\.Headlines\.(?:succinctRMQ|listIntSuccinctRMQ)|Headlines\.(?:succinctRMQ|listIntSuccinctRMQ))' -and
      $line -match $oldRegimePattern
    ) {
      Fail "$path`:$lineNumber has an old cost/regime token in a current table row"
    }
  }
}

$paperText = Read-Text $paperRoot
if ($paperText -notmatch '(?m)^import RMQ\.Headlines\.RMQ\s*$') {
  Fail "$paperRoot must import RMQ.Headlines.RMQ"
}
if ($paperText -match '(?m)^import RMQ\.Headlines(?:\.RMQCompatibility)?\s*$') {
  Fail "$paperRoot imports a broad or compatibility headline surface"
}

$aggregateText = Read-Text $aggregateModule
if ($aggregateText -notmatch '(?m)^import RMQ\.Headlines\.RMQ\s*$') {
  Fail "$aggregateModule must explicitly import the canonical RMQ surface"
}
if ($aggregateText -notmatch '(?m)^import RMQ\.Headlines\.RMQCompatibility\s*$') {
  Fail "$aggregateModule must explicitly import the compatibility RMQ surface"
}

$compatibilityText = Read-Text $compatibilityModule
foreach ($name in $retiredAliases) {
  if ($compatibilityText -match ('(?m)^\s*(?:abbrev|theorem)\s+' +
      [regex]::Escape($name) + '(?![A-Za-z0-9_])')) {
    Fail "$compatibilityModule preserves retired unqualified alias $name"
  }
}
foreach ($match in [regex]::Matches(
    $compatibilityText,
    '(?m)^\s*(?:abbrev|theorem)\s+([A-Za-z][A-Za-z0-9_]*)')) {
  $name = $match.Groups[1].Value
  if ($name -notmatch '(?:Compatibility|Legacy)') {
    Fail "$compatibilityModule declaration $name lacks Compatibility or Legacy"
  }
}

$canonicalAlias =
  'succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile'
$weightAlias =
  'succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe76'
$canonicalText = Read-Text $canonicalModule
$inventoryText = Read-Text $headlineInventory
foreach ($anchor in @($canonicalAlias, $weightAlias)) {
  if ($canonicalText -notmatch [regex]::Escape($anchor)) {
    Fail "$canonicalModule is missing required anchor $anchor"
  }
  if ($inventoryText -notmatch
      ('#print axioms RMQ\.Headlines\.' + [regex]::Escape($anchor))) {
    Fail "$headlineInventory does not print required anchor $anchor"
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
    Fail "$compatibilityModule is missing retained historical alias $anchor"
  }
}

if ($failures -gt 0) {
  Write-Host "PAPER-TOPOLOGY: $failures failures"
  exit 1
}

Write-Host 'PAPER-TOPOLOGY PASS'
exit 0

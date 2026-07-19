#!/usr/bin/env pwsh

param(
  [string]$MutationPath = '',
  [string]$MutationText = '',
  [string]$MutationRemoveText = ''
)

$ErrorActionPreference = 'Stop'
$failures = 0

function Normalize-RepoPath([string]$Path) {
  $normalized = $Path -replace '\\', '/'
  while ($normalized.StartsWith('./')) {
    $normalized = $normalized.Substring(2)
  }
  return $normalized
}

$MutationPath = Normalize-RepoPath $MutationPath

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

function Require-File([string]$Path) {
  if (-not (Test-Path -LiteralPath $Path)) {
    Fail "missing required file $Path"
    return $false
  }
  return $true
}

function Read-Text([string]$Path) {
  $normalized = Normalize-RepoPath $Path
  $text = Get-Content -Raw -LiteralPath $normalized
  if ($MutationPath -ne '' -and $normalized -eq $MutationPath) {
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
    $output = @(& lake env lean $tempPath 2>&1)
    $leanExit = $LASTEXITCODE
    if ($leanExit -ne 0) {
      Fail "[$Role-resolution] documentary headline identifiers do not resolve under import $Import"
      foreach ($line in @($output | Where-Object { $_ -match 'error:' })) {
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
  $headlineInventory
) + $publicClaimSurfaces

$requiredFiles += @($frozenSnapshotLines.Keys)

foreach ($path in $requiredFiles) {
  [void](Require-File $path)
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
    'listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal or listIntSuccinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal'
  'succinctRMQWholeQueryGlobalWordTraceCanonicalTransitionalCostedCostLe' =
    'succinctRMQWholeQueryGlobalWordTraceCostedCostLe or succinctRMQCompatibility328WholeQueryGlobalWordTraceCostedCostLe'
  'succinctRMQCanonicalTransitionalQueryCostEq' =
    'succinctRMQQueryCostEq or succinctRMQCompatibility328QueryCostEq'
  'succinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal' =
    'succinctRMQPrincipledAllSizeChargedTraceFinalFullModelCostLeOfFootprintGlobal or succinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal'
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
  '(?i)(?:\b(?:196727|328|118|4144)\b|2\s*\^\s*128|zero[- ]?block|\bReady\b|LargeRegime|large[- ]regime|CanonicalTransitional)'

# These files intentionally contain the removed vocabulary as enforcement
# data.  They are not documentary theorem references.
$enforcementPaths = @(
  'docs/internal/CLAIM_DRIFT_POLICY.json',
  'docs/internal/CLAIM_DRIFT_POLICY.md',
  'scripts/claim_drift_policy_regression.ps1',
  'scripts/paper_topology_lint.ps1',
  'scripts/paper_topology_lint_regression.ps1'
)

$trackedFiles = @(& git ls-files | ForEach-Object { Normalize-RepoPath $_ })
if ($LASTEXITCODE -ne 0) {
  Fail '[repository-search] git ls-files failed'
  $trackedFiles = @()
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

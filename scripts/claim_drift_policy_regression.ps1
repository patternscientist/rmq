#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  [string]$ScannerPath = "scripts/claim_drift_scan.ps1",
  [switch]$AbsoluteWindowsOnly
)

$ErrorActionPreference = "Stop"

$repoRoot = [System.IO.Path]::GetFullPath((Get-Location).Path)
$resolvedPolicyPath = [System.IO.Path]::GetFullPath($PolicyPath)
$resolvedScannerPath = [System.IO.Path]::GetFullPath($ScannerPath)

if (-not (Test-Path -LiteralPath $resolvedPolicyPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: policy not found: $PolicyPath"
  exit 1
}

if (-not (Test-Path -LiteralPath $resolvedScannerPath)) {
  Write-Host "CLAIM-POLICY-REGRESSION: scanner not found: $ScannerPath"
  exit 1
}

$policyObject = Get-Content -Raw -LiteralPath $resolvedPolicyPath | ConvertFrom-Json
$currentSurfaceRegex = [string]$policyObject.currentFactSurfacePathRegex
foreach ($requiredCurrentSurface in @(
    'artifact/CLAIMS.md',
    'docs/FAMILY_SUMMARY.md',
    'docs/PAPER_CLAIM_CORRESPONDENCE.md',
    'docs/PAPER_MODEL_ADEQUACY.md'
  )) {
  if (-not [regex]::IsMatch($requiredCurrentSurface, $currentSurfaceRegex)) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r2-48147cb-current-surface-registry] missing $requiredCurrentSurface"
    exit 1
  }
}
$currentEventVocabularyTerm = @(
  $policyObject.terms |
    Where-Object id -eq 'forbidden-retired-current-event-vocabulary'
)
if ($currentEventVocabularyTerm.Count -ne 1 -or
    -not [bool]$currentEventVocabularyTerm[0].strict -or
    [string]$currentEventVocabularyTerm[0].scope -ne 'current-fact-surface') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r2-48147cb-current-event-vocabulary-config]"
  exit 1
}
$readWordAttribution = @(
  $policyObject.requiredAttributions |
    Where-Object id -eq 'required-current-readword-only-theorem-attribution'
)
if ($readWordAttribution.Count -ne 1 -or
    -not [bool]$readWordAttribution[0].strict -or
    [string]$readWordAttribution[0].requiredPattern -notmatch 'succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r3-bad14d0-readword-attribution-config]"
  exit 1
}
Write-Host "CLAIM-POLICY-REGRESSION: PASS [r1r2-48147cb-current-surface-registry]"

$sourceManifestTerm = @($policyObject.terms | Where-Object id -eq 'typed-reviewer-source-manifest')
if ($sourceManifestTerm.Count -ne 1 -or
    [string]$sourceManifestTerm[0].pattern -notmatch '22-source' -or
    [string]$sourceManifestTerm[0].pattern -match '20-source') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r1-3a2b472-current-source-policy-config] expected current 22-source advisory pattern"
  exit 1
}
$retiredCostTerm = @($policyObject.terms | Where-Object id -eq 'principled-charged-trace-76')
if ($retiredCostTerm.Count -ne 1 -or
    [string]$retiredCostTerm[0].status -notmatch 'historical' -or
    [string]$retiredCostTerm[0].status -match '^current-') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r1-3a2b472-current-cost-policy-config] retired cost advisory is still current"
  exit 1
}
Write-Host "CLAIM-POLICY-REGRESSION: PASS [r1r1-3a2b472-current-policy-config]"

$fixtures = @(
  @{ id = "canonical-uses-unspaced"; reject = $true; text = "The canonical execution uses 2^128 as an activation premise." },
  @{ id = "canonical-uses-spaced"; reject = $true; text = "The canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "canonical-route-requires"; reject = $true; text = "The canonical reviewer route requires 2^128 as its activation premise." },
  @{ id = "canonical-query-has"; reject = $true; text = "The canonical query has 2 ^ 128 as an activation premise." },
  @{ id = "exponent-first-premise"; reject = $true; text = "2^128 is the activation premise for the current canonical execution." },
  @{ id = "possessive-premise-unspaced"; reject = $true; text = "The canonical execution's activation premise is 2^128." },
  @{ id = "possessive-premise-spaced"; reject = $true; text = "The canonical execution's activation premise is 2 ^ 128." },
  @{ id = "activated-at-unspaced"; reject = $true; text = "The canonical execution is activated at 2^128." },
  @{ id = "activated-at-spaced"; reject = $true; text = "The canonical execution is activated at 2 ^ 128." },
  @{ id = "reviewer-threshold-unspaced"; reject = $true; text = "The canonical reviewer route uses a 2^128 activation threshold." },
  @{ id = "reviewer-threshold-spaced"; reject = $true; text = "The canonical reviewer route uses a 2 ^ 128 activation threshold." },
  @{ id = "exponent-first-activates"; reject = $true; text = "2 ^ 128 activates the canonical reviewer route." },
  @{ id = "exponent-first-threshold"; reject = $true; text = "At 2^128, the canonical execution crosses its activation threshold." },

  # Two-token category representatives: none contains the old third token class.
  @{ id = "canonical-execution-requires"; reject = $true; text = "The canonical execution requires 2^128." },
  @{ id = "reviewer-route-available-only"; reject = $true; text = "The canonical reviewer route is available only at 2 ^ 128." },
  @{ id = "canonical-query-needs"; reject = $true; text = "The canonical query needs 2^128." },
  @{ id = "exponent-required-current-execution"; reject = $true; text = "2^128 is required by the current canonical execution." },
  @{ id = "heldout-canonical-query-works"; reject = $true; text = "For this construction, the canonical query works at 2^128." },
  @{ id = "heldout-exponent-bounds-route"; reject = $true; text = "Here 2 ^ 128 bounds the canonical route." },
  @{ id = "heldout-canonical-execution-mentions"; reject = $true; text = "The canonical execution mentions 2^128." },

  # Allowance-bypass mutations: negative or role words alone must not whitelist.
  @{ id = "bypass-does-not-avoid"; reject = $true; text = "The canonical execution does not avoid requiring 2^128." },
  @{ id = "bypass-not-optional"; reject = $true; text = "It is not optional: the canonical execution requires 2^128." },
  @{ id = "bypass-historical-irrelevant"; reject = $true; text = "Historical context is irrelevant: the canonical execution requires 2^128." },
  @{ id = "bypass-compatibility-irrelevant"; reject = $true; text = "Compatibility is irrelevant: the canonical route needs 2^128." },
  @{ id = "bypass-no-canonical-first-clause"; reject = $true; text = "No canonical execution is discussed here; the canonical execution requires 2^128." },
  @{ id = "bypass-not-true-first-clause"; reject = $true; text = "It is not true that the canonical execution is slow; the canonical execution requires 2^128." },

  @{ id = "retired-direct-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery" },
  @{ id = "retired-interpreted-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted" },
  @{ id = "retired-leaf-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryLeafTrace" },
  @{ id = "retired-word-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTrace" },
  @{ id = "retired-large-word-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryWordTraceLargeRegime" },
  @{ id = "retired-large-global-paper-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryGlobalWordTraceLargeRegime" },
  @{ id = "retired-transitional-cost-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQCanonicalTransitionalQueryCostEq" },
  @{ id = "retired-transitional-model-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.listIntSuccinctRMQCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal" },
  @{ id = "retired-large-regime-story-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQLargeRegimeGlobalPayloadStoreExecutionStory" },
  @{ id = "renamed-w18-list-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.listIntSuccinctRMQEventValueProducerProvenanceOfValid" },
  @{ id = "renamed-w18-program-alias"; reject = $true; termId = "forbidden-retired-paper-query-alias"; text = "RMQ.Headlines.succinctRMQProgramEventValueProducer" },

  # Exact stale-current evidence pattern reproduced from rejected R1-R1
  # candidate 3a2b47261ba6a15829a3160a7fce352b62c88380.
  @{ id = "r1r1-3a2b472-current-cost-76"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current principled charged-trace bound is 76." },
  @{ id = "r1r1-3a2b472-current-source-count-20"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "forbidden-retired-current-source-count"; text = "The canonical reviewer manifest is one typed 20-source universe." },
  @{ id = "r1r1-3a2b472-fresh-segment-21"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "forbidden-retired-fresh-segment-21"; text = "Fresh unused segment 21 is rejected by the common predicate." },
  @{ id = "r1r1-3a2b472-global-positions-0-12"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "forbidden-retired-trace-position-12"; text = "The current global positions 0 and 12 remain distinct obligations." },
  @{ id = "r1r1-current-cost-207-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; termId = "forbidden-retired-current-cost-bound"; text = "The current principled charged-trace bound is 207." },
  @{ id = "r1r1-current-source-count-22-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; termId = "forbidden-retired-current-source-count"; text = "The canonical reviewer manifest is one typed 22-source universe." },
  @{ id = "r1r1-fresh-segment-23-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; termId = "forbidden-retired-fresh-segment-21"; text = "Fresh unused segment 23 is rejected by the common predicate." },
  @{ id = "r1r1-global-positions-0-15-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; termId = "forbidden-retired-trace-position-12"; text = "The current global positions 0 and 15 remain distinct obligations." },

  # Exact stale-current vocabulary patterns reproduced from rejected R1-R2
  # candidate 48147cbc67c6c01c4abcf2565f9b981adb5eacb8.
  @{ id = "r1r2-48147cb-artifact-three-constructor-vocabulary"; relativePath = "artifact/CLAIMS.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "Every actual emitted event is readWord, wordRank, or wordSelect." },
  @{ id = "r1r2-48147cb-correspondence-three-constructor-vocabulary"; relativePath = "docs/PAPER_CLAIM_CORRESPONDENCE.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "The canonical trace proves every actual event is readWord, wordRank, or wordSelect." },
  @{ id = "r1r2-48147cb-family-three-constructor-vocabulary"; relativePath = "docs/FAMILY_SUMMARY.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "The canonical trace proves every emitted event is one of the three genuine constructors." },
  @{ id = "r1r3-a835720-readme-hyphenated-three-constructor-vocabulary"; relativePath = "README.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "Every event actually emitted by the canonical whole-query trace is a payload read, word-rank, or word-select event." },
  @{ id = "r1r3-a835720-readme-bounded-word-primitive-vocabulary"; relativePath = "README.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "Every event is either a payload read or a bounded word primitive." },
  @{ id = "r1r3-a835720-artifact-word-primitive-vocabulary"; relativePath = "artifact/CLAIMS.md"; reject = $true; termId = "forbidden-retired-current-event-vocabulary"; text = "Every event is a payload read or word primitive." },
  @{ id = "r1r2-current-readword-only-control"; relativePath = "docs/PAPER_CLAIM_CORRESPONDENCE.md"; reject = $false; termId = "forbidden-retired-current-event-vocabulary"; text = "RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly proves every emitted event is readWord on the current readWord-only route." },
  @{ id = "r1r2-current-compatibility-labeled-control"; relativePath = "docs/FAMILY_SUMMARY.md"; reject = $false; termId = "forbidden-retired-current-event-vocabulary"; text = "RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly proves the current route is readWord-only; wordRank and wordSelect are compatibility-only constructors and are never emitted." },
  @{ id = "r1r3-compatibility-labeled-weaker-story-control"; relativePath = "README.md"; reject = $false; termId = "forbidden-retired-current-event-vocabulary"; text = "RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly proves the current route is readWord-only. The compatibility theorem says every event is a payload read or bounded word primitive." },

  # Exact theorem-attribution misses reproduced from rejected R1-R3 candidate
  # bad14d0f1f7561f5f4200c19259a4ae5c8375499.
  @{ id = "r1r3-bad14d0-paper-main-missing-strong-alias"; relativePath = "docs/PAPER_MAIN_THEOREM.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "Every actual emitted event is proved to be readWord." },
  @{ id = "r1r3-bad14d0-theorem-map-missing-strong-alias"; relativePath = "docs/PAPER_THEOREM_MAP.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "These anchors package that every emitted trace event is readWord." },
  @{ id = "r1r3-bad14d0-trust-packet-missing-strong-alias"; relativePath = "docs/TRUST_AUDIT_PACKET.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "The checked type packages only genuine readWord events and no synthetic cost marker." },
  @{ id = "r1r3-bad14d0-wordram-packet-missing-strong-alias"; relativePath = "docs/WORD_RAM_REVIEW_PACKET.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "The same execution proves every emitted event is readWord." },
  @{ id = "r1r3-bad14d0-digestion-missing-strong-alias"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "The construction-facing theorem states that every emitted event is a payload-word read." },
  @{ id = "r1r3-bad14d0-what-is-proved-missing-strong-alias"; relativePath = "docs/WHAT_IS_PROVED.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "The execution story proves every emitted event is a payload read." },
  @{ id = "r1r3-bad14d0-artifact-readme-missing-strong-alias"; relativePath = "artifact/README.md"; reject = $true; termId = "required-current-readword-only-theorem-attribution"; text = "Every accepted emitted event is a payload read." },
  @{ id = "r1r3-current-readword-strong-attribution-control"; relativePath = "docs/PAPER_MAIN_THEOREM.md"; reject = $false; termId = "required-current-readword-only-theorem-attribution"; text = "RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly proves every actual emitted event is readWord." },
  @{ id = "r1r3-accurate-weaker-attribution-control"; relativePath = "docs/WHAT_IS_PROVED.md"; reject = $false; termId = "required-current-readword-only-theorem-attribution"; text = "RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly is the strong readWord-only theorem. RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultEventReadWordOrWordRankOrWordSelect is a weaker compatibility alias." },

  @{ id = "negated-canonical"; reject = $false; allowedMatch = $true; text = "No canonical execution theorem uses 2^128 as an activation premise." },
  @{ id = "negated-current-canonical"; reject = $false; allowedMatch = $true; text = "No current canonical reviewer route has 2 ^ 128 as an activation premise." },
  @{ id = "negative-inside-clause"; reject = $false; allowedMatch = $true; text = "The canonical execution does not use 2^128 as an activation premise." },
  @{ id = "not-true-negation"; reject = $false; allowedMatch = $true; text = "It is not true that the canonical execution uses 2^128 as an activation premise." },
  @{ id = "negated-possessive-premise"; reject = $false; allowedMatch = $true; text = "The canonical execution's activation premise is not 2^128." },
  @{ id = "negated-route-has-no"; reject = $false; allowedMatch = $true; text = "The canonical route has no 2^128 activation threshold." },
  @{ id = "negated-unlike-old-theorem"; reject = $false; allowedMatch = $true; text = "Unlike the old theorem, no canonical execution has 2^128 as an activation premise." },
  @{ id = "negated-exponent-first"; reject = $false; allowedMatch = $true; text = "2 ^ 128 is not required by the canonical query." },
  @{ id = "noncanonical-execution"; reject = $false; text = "The noncanonical execution uses 2^128 as an activation premise." },
  @{ id = "non-hyphen-canonical-execution"; reject = $false; text = "The non-canonical execution uses 2 ^ 128 as an activation premise." },
  @{ id = "compatibility-companion"; reject = $false; text = "Compatibility companions retain 2^128 as an explicit sufficient premise." },
  @{ id = "proof-only-sparse-witness"; reject = $false; text = "The proof-only sparse-local witness uses symbolic N = 2 ^ 128." },
  @{ id = "historical-role"; reject = $false; allowedMatch = $true; text = "Historical note: The canonical execution's activation premise was 2^128." },
  @{ id = "compatibility-role"; reject = $false; allowedMatch = $true; text = "Compatibility companion: The canonical reviewer route uses a 2^128 activation threshold." },
  @{ id = "proof-only-role"; reject = $false; allowedMatch = $true; text = "Proof-only witness: The hypothetical canonical query has a 2 ^ 128 activation premise; this is not an execution premise." },
  @{ id = "canonical-paper-alias"; reject = $false; text = "RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile" },
  @{ id = "legacy-paper-alias"; reject = $false; text = "RMQ.Headlines.succinctRMQLegacy196727InterpretedTwoNPlusOConstantQuery" }
)

$shellPath = (Get-Process -Id $PID).Path
$absoluteFixtureRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("claim-drift-policy-regression-" + [Guid]::NewGuid().ToString("N"))
[System.IO.Directory]::CreateDirectory($absoluteFixtureRoot) | Out-Null
$matrixPath = "docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md"
$failures = 0
$rejectCount = 0
$acceptCount = 0
$contextCount = 0
$baselineStatus = $null
$baselineTrackedHashes = $null

function Get-TrackedGitStatus {
  Push-Location $repoRoot
  try {
    return (@(& git -c core.excludesfile= -c core.autocrlf=false status --short --untracked-files=all) -join [Environment]::NewLine)
  } finally {
    Pop-Location
  }
}

function Get-TrackedFileHashSnapshot {
  Push-Location $repoRoot
  try {
    $worktreeRaw = @(& git -c core.excludesfile= -c core.autocrlf=false diff --raw --no-ext-diff --)
    $indexRaw = @(& git -c core.excludesfile= -c core.autocrlf=false diff --cached --raw --no-ext-diff --)
    $matrixHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $repoRoot $matrixPath)).Hash.ToLowerInvariant()
    return @(
      "worktree-diff-raw:"
      $worktreeRaw
      "index-diff-raw:"
      $indexRaw
      "matrix-sha256: $matrixHash"
    ) -join [Environment]::NewLine
  } finally {
    Pop-Location
  }
}

function Assert-TrackedStateUnchanged {
  param([string]$Context)

  $status = Get-TrackedGitStatus
  if ($status -ne $baselineStatus) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Context] git status changed"
    Write-Host "  expected: $baselineStatus"
    Write-Host "  actual:   $status"
    $script:failures += 1
    return
  }

  $hashes = Get-TrackedFileHashSnapshot
  if ($hashes -ne $baselineTrackedHashes) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Context] tracked file hashes changed"
    $script:failures += 1
    return
  }

  Write-Host "CLAIM-POLICY-REGRESSION: PASS [$Context] tracked state unchanged"
}

function New-ShadowMatrixRoot {
  param([string]$Content)

  $shadowRoot = Join-Path $absoluteFixtureRoot ("shadow-" + [Guid]::NewGuid().ToString("N"))
  $shadowMatrixPath = Join-Path $shadowRoot $matrixPath
  [System.IO.Directory]::CreateDirectory((Split-Path -Parent $shadowMatrixPath)) | Out-Null
  [System.IO.File]::WriteAllText($shadowMatrixPath, $Content + [Environment]::NewLine)
  [PSCustomObject]@{
    Root = $shadowRoot
    RelativeMatrixPath = $matrixPath
    AbsoluteMatrixPath = $shadowMatrixPath
  }
}

function New-ShadowFileRoot {
  param(
    [string]$RelativePath,
    [string]$Content
  )

  $shadowRoot = Join-Path $absoluteFixtureRoot ("shadow-" + [Guid]::NewGuid().ToString("N"))
  $shadowPath = Join-Path $shadowRoot $RelativePath
  [System.IO.Directory]::CreateDirectory((Split-Path -Parent $shadowPath)) | Out-Null
  [System.IO.File]::WriteAllText(
    $shadowPath,
    $Content + [Environment]::NewLine)
  [PSCustomObject]@{
    Root = $shadowRoot
    RelativePath = $RelativePath
    AbsolutePath = $shadowPath
  }
}

function Invoke-StrictClaimScan {
  param(
    [string]$Path,
    [string]$WorkingDirectory = $repoRoot
  )

  Push-Location $WorkingDirectory
  try {
    $output = @(& $shellPath -NoLogo -NoProfile -ExecutionPolicy Bypass -File $resolvedScannerPath -Strict -PolicyPath $resolvedPolicyPath -Path $Path 2>&1)
    $code = $LASTEXITCODE
  } finally {
    Pop-Location
  }
  [PSCustomObject]@{
    Code = $code
    Output = @($output | ForEach-Object { [string]$_ })
  }
}

function Test-FinalVerdict {
  param(
    [string]$Id,
    [string]$Path,
    [bool]$Reject,
    [bool]$RequireAllowed = $false,
    [string]$TermId = "forbidden-2pow128-canonical-activation",
    [string]$WorkingDirectory = $repoRoot,
    [bool]$CheckTrackedState = $false
  )

  if ($CheckTrackedState) {
    Assert-TrackedStateUnchanged -Context "before-$Id"
  }

  $result = Invoke-StrictClaimScan -Path $Path -WorkingDirectory $WorkingDirectory

  if ($CheckTrackedState) {
    Assert-TrackedStateUnchanged -Context "after-$Id"
  }

  $escapedTermId = [regex]::Escape($TermId)
  $termFailed = [bool]($result.Output -match "CLAIM-DRIFT\[$escapedTermId\].*\[fail\]")
  $termAllowed = [bool]($result.Output -match "CLAIM-DRIFT\[$escapedTermId\].*\[allowed\]")
  if ($Reject) {
    $passed = ($result.Code -ne 0) -and $termFailed
    $expected = "REJECT"
  } else {
    $passed = $result.Code -eq 0
    if ($RequireAllowed) {
      $passed = $passed -and $termAllowed
    }
    $expected = "ACCEPT"
  }

  if (-not $passed) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [$Id] expected final strict verdict $expected"
    $result.Output | ForEach-Object { Write-Host "  $_" }
    $script:failures += 1
  } else {
    Write-Host "CLAIM-POLICY-REGRESSION: PASS [$Id] $expected"
  }
}

function Test-AbsoluteWindowsScannerPath {
  $absoluteFixturePath = Join-Path $absoluteFixtureRoot "absolute-windows-misuse.txt"
  [System.IO.File]::WriteAllText(
    $absoluteFixturePath,
    "The canonical execution requires 2^128." + [Environment]::NewLine
  )

  if ($env:OS -eq "Windows_NT" -and $absoluteFixturePath -notmatch "^[A-Za-z]:[\\/]") {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [absolute-windows-drive-qualified] fixture path is not drive-qualified: $absoluteFixturePath"
    $script:failures += 1
  } else {
    Test-FinalVerdict -Id "absolute-windows-single-file" -Path $absoluteFixturePath -Reject $true -CheckTrackedState $true
  }

  $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
  Test-FinalVerdict -Id "absolute-matrix-context-allowance" -Path $markedShadow.AbsoluteMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true
  $script:contextCount += 2
}

try {
  $baselineStatus = Get-TrackedGitStatus
  $baselineTrackedHashes = Get-TrackedFileHashSnapshot

  if ($AbsoluteWindowsOnly) {
    Test-AbsoluteWindowsScannerPath
  } else {
    foreach ($fixture in $fixtures) {
      $fixturePath = if ($fixture.ContainsKey("relativePath")) {
        [string]$fixture.relativePath
      } else {
        $fixture.id + ".txt"
      }
      $fixtureFullPath = Join-Path $absoluteFixtureRoot $fixturePath
      [System.IO.Directory]::CreateDirectory((Split-Path -Parent $fixtureFullPath)) | Out-Null
      [System.IO.File]::WriteAllText(
        $fixtureFullPath,
        [string]$fixture.text + [Environment]::NewLine
      )
      $termId = "forbidden-2pow128-canonical-activation"
      if ($fixture.ContainsKey("termId")) {
        $termId = [string]$fixture.termId
      }
      Test-FinalVerdict -Id $fixture.id -Path $fixturePath -WorkingDirectory $absoluteFixtureRoot -Reject ([bool]$fixture.reject) -RequireAllowed ([bool]$fixture.allowedMatch) -TermId $termId
      if ($fixture.reject) {
        $rejectCount += 1
      } else {
        $acceptCount += 1
      }
    }

    Test-FinalVerdict -Id "policy-path-allowance" -Path "docs/internal/CLAIM_DRIFT_POLICY.md" -Reject $false -RequireAllowed $true

    $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
    Test-FinalVerdict -Id "matrix-marked-row-allowance" -Path $markedShadow.RelativeMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true
    $contextCount += 2

    Test-AbsoluteWindowsScannerPath

    $unmarkedShadow = New-ShadowMatrixRoot -Content 'The canonical execution requires 2^128.'
    Test-FinalVerdict -Id "matrix-filename-does-not-bypass" -Path $unmarkedShadow.RelativeMatrixPath -WorkingDirectory $unmarkedShadow.Root -Reject $true -CheckTrackedState $true
    $contextCount += 1

    $retiredTerm = 'forbidden-retired-paper-query-alias'
    $retiredAlias = 'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'
    $exactFrozenLine = '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'

    $currentDigestShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/PROJECT_DIGESTION_CURRENT.md' `
      -Content "Current capstone: $retiredAlias."
    Test-FinalVerdict -Id 'retired-alias-current-publication-digest' -Path $currentDigestShadow.RelativePath -WorkingDirectory $currentDigestShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true

    $auditShadow = New-ShadowFileRoot `
      -RelativePath 'docs/internal/audit_reports/frozen-boundary-mutation.md' `
      -Content "Current capstone: $retiredAlias."
    Test-FinalVerdict -Id 'retired-current-alias-audit-report' -Path $auditShadow.RelativePath -WorkingDirectory $auditShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true

    $validFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content $exactFrozenLine
    Test-FinalVerdict -Id 'valid-exact-frozen-snapshot-occurrence' -Path $validFrozenShadow.RelativePath -WorkingDirectory $validFrozenShadow.Root -Reject $false -RequireAllowed $true -TermId $retiredTerm -CheckTrackedState $true

    $misplacedFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/PROJECT_DIGESTION_CURRENT.md' `
      -Content $exactFrozenLine
    Test-FinalVerdict -Id 'same-frozen-occurrence-outside-exact-scope' -Path $misplacedFrozenShadow.RelativePath -WorkingDirectory $misplacedFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true

    $forgedFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content "$exactFrozenLine forged"
    Test-FinalVerdict -Id 'forged-exact-marker-does-not-bypass' -Path $forgedFrozenShadow.RelativePath -WorkingDirectory $forgedFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true

    $casualFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content "[FROZEN-HISTORY: casual] $retiredAlias"
    Test-FinalVerdict -Id 'casual-history-word-does-not-bypass' -Path $casualFrozenShadow.RelativePath -WorkingDirectory $casualFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true
    $contextCount += 6

    $historicalR1Shadow = New-ShadowFileRoot `
      -RelativePath 'docs/internal/audit_reports/r1r1-3a2b472-frozen-evidence.md' `
      -Content @'
The historical current bound at the audited candidate was 76.
The historical canonical manifest was a typed 20-source universe.
Fresh unused segment 21 was rejected in that frozen candidate.
The historical global positions 0 and 12 were distinct.
'@
    foreach ($historicalTerm in @(
        'forbidden-retired-current-cost-bound',
        'forbidden-retired-current-source-count',
        'forbidden-retired-fresh-segment-21',
        'forbidden-retired-trace-position-12'
      )) {
      Test-FinalVerdict -Id "r1r1-3a2b472-historical-$historicalTerm" `
        -Path $historicalR1Shadow.RelativePath `
        -WorkingDirectory $historicalR1Shadow.Root `
        -Reject $false -RequireAllowed $true -TermId $historicalTerm `
        -CheckTrackedState $true
      $contextCount += 1
    }
  }
} finally {
  if ([System.IO.Directory]::Exists($absoluteFixtureRoot)) {
    [System.IO.Directory]::Delete($absoluteFixtureRoot, $true)
  }
}

if ($failures -gt 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: $failures fixture failures"
  exit 1
}

if ($AbsoluteWindowsOnly) {
  Write-Host "CLAIM-POLICY-REGRESSION: ABSOLUTE-WINDOWS PASS ($contextCount production path verdicts)"
} else {
  Write-Host "CLAIM-POLICY-REGRESSION: PASS ($rejectCount must-reject strict verdicts, $acceptCount must-accept strict verdicts, $contextCount path/context/bypass verdicts)"
}
exit 0

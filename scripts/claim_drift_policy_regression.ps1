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
$expectedCurrentSurfaceRegex = '^(?:README\.md|artifact/(?:CLAIMS|README)\.md|docs/(?:FAMILY_SUMMARY|PAPER_CLAIM_CORRESPONDENCE|PAPER_MAIN_THEOREM|PAPER_MODEL_ADEQUACY|PAPER_THEOREM_MAP|WHAT_IS_PROVED|PAPER_RELATED_WORK|PUBLICATION_STRATEGY|RELATED_WORK_AND_LIMITATIONS|ROADMAP|TRUST_AUDIT_PACKET|WORD_RAM_REVIEW_PACKET)\.md|docs/digests/PROJECT_DIGESTION_CURRENT\.md|docs/internal/(?:CLAIM_DRIFT_POLICY\.md|RMQ_FINAL_ROADMAP\.md))$'
if ($currentSurfaceRegex -cne $expectedCurrentSurfaceRegex) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [p1r1-exact-current-surface-registry] regex drift"
  exit 1
}
$requiredCurrentSurfaces = @(
  'artifact/CLAIMS.md',
  'artifact/README.md',
  'docs/digests/PROJECT_DIGESTION_CURRENT.md',
  'docs/FAMILY_SUMMARY.md',
  'docs/internal/CLAIM_DRIFT_POLICY.md',
  'docs/internal/RMQ_FINAL_ROADMAP.md',
  'docs/PAPER_CLAIM_CORRESPONDENCE.md',
  'docs/PAPER_MAIN_THEOREM.md',
  'docs/PAPER_MODEL_ADEQUACY.md',
  'docs/PAPER_RELATED_WORK.md',
  'docs/PAPER_THEOREM_MAP.md',
  'docs/PUBLICATION_STRATEGY.md',
  'docs/RELATED_WORK_AND_LIMITATIONS.md',
  'docs/ROADMAP.md',
  'docs/TRUST_AUDIT_PACKET.md',
  'docs/WHAT_IS_PROVED.md',
  'docs/WORD_RAM_REVIEW_PACKET.md',
  'README.md'
)
foreach ($requiredCurrentSurface in $requiredCurrentSurfaces) {
  if (-not [regex]::IsMatch($requiredCurrentSurface, $currentSurfaceRegex)) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [r1r2-48147cb-current-surface-registry] missing $requiredCurrentSurface"
    exit 1
  }
}
if ($requiredCurrentSurfaces.Count -ne 18 -or
    @($requiredCurrentSurfaces | Group-Object | Where-Object Count -ne 1).Count -ne 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [p1r1-exact-current-surface-registry] path registry drift"
  exit 1
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
Write-Host "CLAIM-POLICY-REGRESSION: PASS [p1r1-exact-current-surface-registry] 18 exact paths"

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
$retired207Term = @($policyObject.terms | Where-Object id -eq 'historical-silent-sparse-level-207')
if ($retired207Term.Count -ne 1 -or
    [string]$retired207Term[0].status -notmatch 'historical|retired' -or
    [string]$retired207Term[0].status -match '^current-') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [p1-retired-207-policy-config]"
  exit 1
}
$strictRetiredCostTerm = @($policyObject.terms | Where-Object id -eq 'forbidden-retired-current-cost-bound')
if ($strictRetiredCostTerm.Count -ne 1 -or
    -not [bool]$strictRetiredCostTerm[0].strict -or
    [string]$strictRetiredCostTerm[0].scope -ne 'current-fact-surface' -or
    -not [bool]$strictRetiredCostTerm[0].multiline -or
    [string]$strictRetiredCostTerm[0].pattern -notmatch '\(\?:76\|142\|207' -or
    [string]$strictRetiredCostTerm[0].pattern -match '\(\?:76\|142\|207\|210' -or
    [string]$strictRetiredCostTerm[0].pattern -match '207\(\?!' -or
    [string]$strictRetiredCostTerm[0].allowedLineRegex -notmatch 'retired\|historical') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [p1-current-cost-category-config]"
  exit 1
}
$historical328Term = @($policyObject.terms | Where-Object id -eq 'historical-canonical-transitional-328')
$compatibility352Term = @($policyObject.terms | Where-Object id -eq 'live-compatibility-352')
if ($historical328Term.Count -ne 1 -or
    [string]$historical328Term[0].status -notmatch 'historical' -or
    $compatibility352Term.Count -ne 1 -or
    [string]$compatibility352Term[0].status -notmatch 'compatibility') {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [p1-historical-compatibility-role-config]"
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
  @{ id = "p1-current-cost-207-rejected"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current principled charged-trace bound is 207." },
  @{ id = "p1-canonical-query-cost-207-heldout"; relativePath = "docs/PAPER_MAIN_THEOREM.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The canonical query cost is bounded by 207." },
  @{ id = "p1-uniform-modeled-trace-length-207-heldout"; relativePath = "artifact/CLAIMS.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The uniform modeled trace-length ceiling is 207." },
  @{ id = "p1-costed-cost-207-heldout"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The execution's Costed.cost is at most 207." },
  @{ id = "p1-number-first-current-charged-trace-207"; relativePath = "README.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "207 is the current charged-trace cap." },
  @{ id = "p1-registered-current-cost-cross-line-207-rejected"; relativePath = "docs/PUBLICATION_STRATEGY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current theorem gives the checked charged-trace cap`n207." },
  @{ id = "p1-cross-line-number-first-current-cost-207-heldout"; relativePath = "artifact/CLAIMS.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "207`nis the current charged-trace cap." },
  @{ id = "p1-cross-line-blank-paragraph-boundary-control"; relativePath = "docs/PUBLICATION_STRATEGY.md"; reject = $false; termId = "forbidden-retired-current-cost-bound"; text = "The current theorem is described here.`n`n207 appears in an unrelated historical inventory." },
  @{ id = "p1-current-cost-210-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; termId = "forbidden-retired-current-cost-bound"; text = "The current principled charged-trace bound is 210." },
  @{ id = "p1-historical-207-marker-control"; relativePath = "docs/digests/PROJECT_DIGESTION_CURRENT.md"; reject = $false; allowedMatch = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical record: the charged-trace cap at the audited checkpoint was 207 <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-historical-76-marker-control"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $false; allowedMatch = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical note: the principled bound at the pre-A07 checkpoint was 76 <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-historical-142-marker-control"; relativePath = "artifact/README.md"; reject = $false; allowedMatch = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical comparison: the modeled cap at the retired checkpoint was 142 <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-history-conjunction-current-207-rejected"; relativePath = "README.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical note: 76 was retired and the current query bound is 207 <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-compound-comparison-current-207-rejected"; relativePath = "docs/FAMILY_SUMMARY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current bound is 210. Historical comparison: the current query bound is 207 <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-history-marker-unrelated-clause-bypass"; relativePath = "README.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical note: 76 was retired; the current charged-trace cap is 207. <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-history-word-unrelated-clause-bypass"; relativePath = "docs/FAMILY_SUMMARY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "Historical context is useful; the canonical query bound is 207. <!-- CLAIM-HISTORY-A07-COST -->" },
  @{ id = "p1-historical-328-control"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $false; termId = "historical-canonical-transitional-328"; text = "Historical transitional comparison: the retired literal was 328." },
  @{ id = "p1-live-compatibility-352-control"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $false; termId = "live-compatibility-352"; text = "The distinctly named live compatibility expression is 352, not the paper-facing bound." },
  @{ id = "p1-supersession-arrow-207-to-210-control"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $false; allowedMatch = $true; termId = "forbidden-retired-current-cost-bound"; text = "The retired query bound moved from 207 to the current bound 210." },
  @{ id = "p1-current-subject-arrow-207-to-210-rejected"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current query bound is 207 -> 210." },
  @{ id = "p1-current-subject-fat-arrow-207-to-210-rejected"; relativePath = "docs/PAPER_MAIN_THEOREM.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The current query cap is 207 => 210." },
  @{ id = "p1-supersession-arrow-unrelated-current-bypass"; relativePath = "docs/PAPER_MODEL_ADEQUACY.md"; reject = $true; termId = "forbidden-retired-current-cost-bound"; text = "The historical literal moved 207 -> 210; the current query bound is 207." },
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

$expectedFixtureIds = @'
canonical-uses-unspaced
canonical-uses-spaced
canonical-route-requires
canonical-query-has
exponent-first-premise
possessive-premise-unspaced
possessive-premise-spaced
activated-at-unspaced
activated-at-spaced
reviewer-threshold-unspaced
reviewer-threshold-spaced
exponent-first-activates
exponent-first-threshold
canonical-execution-requires
reviewer-route-available-only
canonical-query-needs
exponent-required-current-execution
heldout-canonical-query-works
heldout-exponent-bounds-route
heldout-canonical-execution-mentions
bypass-does-not-avoid
bypass-not-optional
bypass-historical-irrelevant
bypass-compatibility-irrelevant
bypass-no-canonical-first-clause
bypass-not-true-first-clause
retired-direct-paper-alias
retired-interpreted-paper-alias
retired-leaf-paper-alias
retired-word-paper-alias
retired-large-word-paper-alias
retired-large-global-paper-alias
retired-transitional-cost-alias
retired-transitional-model-alias
retired-large-regime-story-alias
renamed-w18-list-alias
renamed-w18-program-alias
r1r1-3a2b472-current-cost-76
r1r1-3a2b472-current-source-count-20
r1r1-3a2b472-fresh-segment-21
r1r1-3a2b472-global-positions-0-12
p1-current-cost-207-rejected
p1-canonical-query-cost-207-heldout
p1-uniform-modeled-trace-length-207-heldout
p1-costed-cost-207-heldout
p1-number-first-current-charged-trace-207
p1-registered-current-cost-cross-line-207-rejected
p1-cross-line-number-first-current-cost-207-heldout
p1-cross-line-blank-paragraph-boundary-control
p1-current-cost-210-control
p1-historical-207-marker-control
p1-historical-76-marker-control
p1-historical-142-marker-control
p1-history-conjunction-current-207-rejected
p1-compound-comparison-current-207-rejected
p1-history-marker-unrelated-clause-bypass
p1-history-word-unrelated-clause-bypass
p1-historical-328-control
p1-live-compatibility-352-control
p1-supersession-arrow-207-to-210-control
p1-current-subject-arrow-207-to-210-rejected
p1-current-subject-fat-arrow-207-to-210-rejected
p1-supersession-arrow-unrelated-current-bypass
r1r1-current-source-count-22-control
r1r1-fresh-segment-23-control
r1r1-global-positions-0-15-control
r1r2-48147cb-artifact-three-constructor-vocabulary
r1r2-48147cb-correspondence-three-constructor-vocabulary
r1r2-48147cb-family-three-constructor-vocabulary
r1r3-a835720-readme-hyphenated-three-constructor-vocabulary
r1r3-a835720-readme-bounded-word-primitive-vocabulary
r1r3-a835720-artifact-word-primitive-vocabulary
r1r2-current-readword-only-control
r1r2-current-compatibility-labeled-control
r1r3-compatibility-labeled-weaker-story-control
r1r3-bad14d0-paper-main-missing-strong-alias
r1r3-bad14d0-theorem-map-missing-strong-alias
r1r3-bad14d0-trust-packet-missing-strong-alias
r1r3-bad14d0-wordram-packet-missing-strong-alias
r1r3-bad14d0-digestion-missing-strong-alias
r1r3-bad14d0-what-is-proved-missing-strong-alias
r1r3-bad14d0-artifact-readme-missing-strong-alias
r1r3-current-readword-strong-attribution-control
r1r3-accurate-weaker-attribution-control
negated-canonical
negated-current-canonical
negative-inside-clause
not-true-negation
negated-possessive-premise
negated-route-has-no
negated-unlike-old-theorem
negated-exponent-first
noncanonical-execution
non-hyphen-canonical-execution
compatibility-companion
proof-only-sparse-witness
historical-role
compatibility-role
proof-only-role
canonical-paper-alias
legacy-paper-alias
'@ -split "\r?\n" | Where-Object { $_ }

$expectedRejectCount = 68
$expectedAcceptCount = 33
$expectedContextCount = 15
$expectedContextFixtureIds = @(
  "policy-path-allowance",
  "matrix-marked-row-allowance",
  "absolute-windows-single-file",
  "absolute-matrix-context-allowance",
  "matrix-filename-does-not-bypass",
  "retired-alias-current-publication-digest",
  "retired-current-alias-audit-report",
  "valid-exact-frozen-snapshot-occurrence",
  "same-frozen-occurrence-outside-exact-scope",
  "forged-exact-marker-does-not-bypass",
  "casual-history-word-does-not-bypass",
  "r1r1-3a2b472-historical-forbidden-retired-current-cost-bound",
  "r1r1-3a2b472-historical-forbidden-retired-current-source-count",
  "r1r1-3a2b472-historical-forbidden-retired-fresh-segment-21",
  "r1r1-3a2b472-historical-forbidden-retired-trace-position-12"
)

function Test-FixtureRegistry {
  param(
    [object[]]$Registry,
    [string[]]$ExpectedIds,
    [int]$Rejects,
    [int]$Accepts
  )

  $ids = @($Registry | ForEach-Object { [string]$_.id })
  if ($ids.Count -ne $ExpectedIds.Count) {
    return $false
  }
  if (@($ids | Group-Object | Where-Object Count -ne 1).Count -ne 0) {
    return $false
  }
  for ($i = 0; $i -lt $ExpectedIds.Count; $i += 1) {
    if ($ids[$i] -ne $ExpectedIds[$i]) {
      return $false
    }
  }
  if (@($Registry | Where-Object { [bool]$_.reject }).Count -ne $Rejects) {
    return $false
  }
  if (@($Registry | Where-Object { -not [bool]$_.reject }).Count -ne $Accepts) {
    return $false
  }
  return $true
}

if (-not (Test-FixtureRegistry -Registry $fixtures -ExpectedIds $expectedFixtureIds `
      -Rejects $expectedRejectCount -Accepts $expectedAcceptCount)) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [exact-fixture-registry]"
  exit 1
}

$duplicateRegistry = @($fixtures) + @($fixtures[17])
if (Test-FixtureRegistry -Registry $duplicateRegistry -ExpectedIds $expectedFixtureIds `
    -Rejects ($expectedRejectCount + [int][bool]$fixtures[17].reject) `
    -Accepts ($expectedAcceptCount + [int](-not [bool]$fixtures[17].reject))) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [duplicate-fixture-id-control]"
  exit 1
}
Write-Host "CLAIM-POLICY-REGRESSION: PASS [duplicate-fixture-id-control] REJECT"

$missingRegistry = @($fixtures | Where-Object { [string]$_.id -ne $expectedFixtureIds[46] })
if (Test-FixtureRegistry -Registry $missingRegistry -ExpectedIds $expectedFixtureIds `
    -Rejects $expectedRejectCount -Accepts $expectedAcceptCount) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [missing-required-fixture-id-control]"
  exit 1
}
Write-Host "CLAIM-POLICY-REGRESSION: PASS [missing-required-fixture-id-control] REJECT"

$verdictDriftRegistry = @(
  foreach ($fixture in $fixtures) {
    $copy = @{}
    foreach ($key in $fixture.Keys) {
      $copy[$key] = $fixture[$key]
    }
    $copy
  }
)
$verdictDriftRegistry[0].reject = -not [bool]$verdictDriftRegistry[0].reject
if (Test-FixtureRegistry -Registry $verdictDriftRegistry -ExpectedIds $expectedFixtureIds `
    -Rejects $expectedRejectCount -Accepts $expectedAcceptCount) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [verdict-count-drift-control]"
  exit 1
}
Write-Host "CLAIM-POLICY-REGRESSION: PASS [verdict-count-drift-control] REJECT"
Write-Host "CLAIM-POLICY-REGRESSION: PASS [exact-fixture-registry] $($fixtures.Count) ordered fixtures"

$shellPath = (Get-Process -Id $PID).Path
$absoluteFixtureRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("claim-drift-policy-regression-" + [Guid]::NewGuid().ToString("N"))
[System.IO.Directory]::CreateDirectory($absoluteFixtureRoot) | Out-Null
$matrixPath = "docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md"
$failures = 0
$rejectCount = 0
$acceptCount = 0
$contextCount = 0
$observedContextIds = New-Object System.Collections.Generic.List[string]
$baselineStatus = $null
$baselineTrackedHashes = $null
$gitStageTimeoutMs = 15000
$scannerStageTimeoutMs = 30000

function Stop-OwnedProcessTree {
  param([System.Diagnostics.Process]$Process)

  if ($null -eq $Process -or $Process.HasExited) {
    return $true
  }

  if ($env:OS -eq "Windows_NT") {
    $all = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue)
    $pending = @([int]$Process.Id)
    $owned = @()
    while ($pending.Count -gt 0) {
      $parent = $pending[0]
      $pending = @($pending | Select-Object -Skip 1)
      $children = @($all | Where-Object { [int]$_.ParentProcessId -eq $parent })
      foreach ($child in $children) {
        $pending += [int]$child.ProcessId
        $owned += [int]$child.ProcessId
      }
    }
    [array]::Reverse($owned)
    foreach ($id in @($owned + [int]$Process.Id)) {
      Stop-Process -Id $id -Force -ErrorAction SilentlyContinue
    }
  } else {
    Stop-Process -Id $Process.Id -Force -ErrorAction SilentlyContinue
  }

  $null = $Process.WaitForExit(5000)
  return $Process.HasExited
}

function Invoke-BoundedProcess {
  param(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$WorkingDirectory,
    [int]$TimeoutMs
  )

  if ($TimeoutMs -le 0) {
    throw "positive subprocess deadline required"
  }

  $argumentText = @(
    foreach ($argument in $Arguments) {
      if ($argument -match '[\s"]') {
        '"' + $argument.Replace('"', '\"') + '"'
      } else {
        $argument
      }
    }
  ) -join " "
  $startInfo = [System.Diagnostics.ProcessStartInfo]::new()
  $startInfo.FileName = $FilePath
  $startInfo.Arguments = $argumentText
  $startInfo.WorkingDirectory = $WorkingDirectory
  $startInfo.UseShellExecute = $false
  $startInfo.CreateNoWindow = $true
  $startInfo.RedirectStandardOutput = $true
  $startInfo.RedirectStandardError = $true
  $process = $null
  try {
    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    if (-not $process.Start()) {
      throw "failed to start bounded subprocess: $FilePath"
    }
    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $completed = $process.WaitForExit($TimeoutMs)
    $timedOut = -not $completed
    $cleaned = $true
    if ($timedOut) {
      $cleaned = Stop-OwnedProcessTree -Process $process
    } else {
      $process.WaitForExit()
    }
    $stdout = $stdoutTask.GetAwaiter().GetResult()
    $stderr = $stderrTask.GetAwaiter().GetResult()
    $output = @(($stdout + [Environment]::NewLine + $stderr) -split "\r?\n" | Where-Object { $_ })
    $code = if ($timedOut) { 124 } else { [int]$process.ExitCode }
    return [PSCustomObject]@{
      Code = $code
      TimedOut = $timedOut
      Cleaned = $cleaned
      Output = @($output | ForEach-Object { [string]$_ })
    }
  } finally {
    if ($null -ne $process -and -not $process.HasExited) {
      $null = Stop-OwnedProcessTree -Process $process
    }
    if ($null -ne $process) {
      $process.Dispose()
    }
  }
}

function Invoke-BoundedGit {
  param(
    [string[]]$Arguments,
    [string]$WorkingDirectory = $repoRoot
  )

  $result = Invoke-BoundedProcess -FilePath "git" -Arguments $Arguments `
    -WorkingDirectory $WorkingDirectory -TimeoutMs $gitStageTimeoutMs
  if ($result.TimedOut -or -not $result.Cleaned -or $result.Code -ne 0) {
    throw "bounded git stage failed: git $($Arguments -join ' ') (exit $($result.Code))"
  }
  return @($result.Output)
}

function Test-SubprocessDeadlineControl {
  $result = Invoke-BoundedProcess -FilePath $shellPath `
    -Arguments @("-NoLogo", "-NoProfile", "-Command", "Start-Sleep -Seconds 5") `
    -WorkingDirectory $repoRoot -TimeoutMs 200
  if (-not $result.TimedOut -or -not $result.Cleaned) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [subprocess-deadline-sleeper-control]"
    $script:failures += 1
    return
  }
  Write-Host "CLAIM-POLICY-REGRESSION: PASS [subprocess-deadline-sleeper-control] timeout classified and owned process cleaned"
}

function Get-TrackedGitStatus {
  return (@(Invoke-BoundedGit -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "status", "--short", "--untracked-files=all"
    )) -join [Environment]::NewLine)
}

function Get-TrackedFileHashSnapshot {
  $worktreeRaw = @(Invoke-BoundedGit -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "diff", "--raw", "--no-ext-diff", "--"
    ))
  $indexRaw = @(Invoke-BoundedGit -Arguments @(
      "-c", "core.excludesfile=", "-c", "core.autocrlf=false",
      "diff", "--cached", "--raw", "--no-ext-diff", "--"
    ))
  $matrixHash = (Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $repoRoot $matrixPath)).Hash.ToLowerInvariant()
  return @(
    "worktree-diff-raw:"
    $worktreeRaw
    "index-diff-raw:"
    $indexRaw
    "matrix-sha256: $matrixHash"
  ) -join [Environment]::NewLine
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

  return Invoke-BoundedProcess -FilePath $shellPath `
    -Arguments @(
      "-NoLogo", "-NoProfile", "-ExecutionPolicy", "Bypass",
      "-File", $resolvedScannerPath, "-Strict",
      "-PolicyPath", $resolvedPolicyPath, "-Path", $Path
    ) -WorkingDirectory $WorkingDirectory -TimeoutMs $scannerStageTimeoutMs
}

function Test-FinalVerdict {
  param(
    [string]$Id,
    [string]$Path,
    [bool]$Reject,
    [bool]$RequireAllowed = $false,
    [string]$TermId = "forbidden-2pow128-canonical-activation",
    [string]$WorkingDirectory = $repoRoot,
    [bool]$CheckTrackedState = $false,
    [bool]$ContextCase = $false
  )

  if ($ContextCase) {
    $script:observedContextIds.Add($Id)
  }

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
    Test-FinalVerdict -Id "absolute-windows-single-file" -Path $absoluteFixturePath -Reject $true -CheckTrackedState $true -ContextCase $true
  }

  $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
  Test-FinalVerdict -Id "absolute-matrix-context-allowance" -Path $markedShadow.AbsoluteMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true -ContextCase $true
}

try {
  $baselineStatus = Get-TrackedGitStatus
  $baselineTrackedHashes = Get-TrackedFileHashSnapshot
  Test-SubprocessDeadlineControl

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

    Test-FinalVerdict -Id "policy-path-allowance" -Path "docs/internal/CLAIM_DRIFT_POLICY.md" -Reject $false -RequireAllowed $true -ContextCase $true

    $markedShadow = New-ShadowMatrixRoot -Content '| `POLICY-R3` | The canonical execution requires 2^128. |'
    Test-FinalVerdict -Id "matrix-marked-row-allowance" -Path $markedShadow.RelativeMatrixPath -WorkingDirectory $markedShadow.Root -Reject $false -RequireAllowed $true -CheckTrackedState $true -ContextCase $true

    Test-AbsoluteWindowsScannerPath

    $unmarkedShadow = New-ShadowMatrixRoot -Content 'The canonical execution requires 2^128.'
    Test-FinalVerdict -Id "matrix-filename-does-not-bypass" -Path $unmarkedShadow.RelativeMatrixPath -WorkingDirectory $unmarkedShadow.Root -Reject $true -CheckTrackedState $true -ContextCase $true

    $retiredTerm = 'forbidden-retired-paper-query-alias'
    $retiredAlias = 'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'
    $exactFrozenLine = '<!-- RMQ-PAPER-TOPOLOGY-FROZEN-SNAPSHOT --> RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery'

    $currentDigestShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/PROJECT_DIGESTION_CURRENT.md' `
      -Content "Current capstone: $retiredAlias."
    Test-FinalVerdict -Id 'retired-alias-current-publication-digest' -Path $currentDigestShadow.RelativePath -WorkingDirectory $currentDigestShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

    $auditShadow = New-ShadowFileRoot `
      -RelativePath 'docs/internal/audit_reports/frozen-boundary-mutation.md' `
      -Content "Current capstone: $retiredAlias."
    Test-FinalVerdict -Id 'retired-current-alias-audit-report' -Path $auditShadow.RelativePath -WorkingDirectory $auditShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

    $validFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content $exactFrozenLine
    Test-FinalVerdict -Id 'valid-exact-frozen-snapshot-occurrence' -Path $validFrozenShadow.RelativePath -WorkingDirectory $validFrozenShadow.Root -Reject $false -RequireAllowed $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

    $misplacedFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/PROJECT_DIGESTION_CURRENT.md' `
      -Content $exactFrozenLine
    Test-FinalVerdict -Id 'same-frozen-occurrence-outside-exact-scope' -Path $misplacedFrozenShadow.RelativePath -WorkingDirectory $misplacedFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

    $forgedFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content "$exactFrozenLine forged"
    Test-FinalVerdict -Id 'forged-exact-marker-does-not-bypass' -Path $forgedFrozenShadow.RelativePath -WorkingDirectory $forgedFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

    $casualFrozenShadow = New-ShadowFileRoot `
      -RelativePath 'docs/digests/DEEP_PROJECT_DIGESTION_2026_06_28.md' `
      -Content "[FROZEN-HISTORY: casual] $retiredAlias"
    Test-FinalVerdict -Id 'casual-history-word-does-not-bypass' -Path $casualFrozenShadow.RelativePath -WorkingDirectory $casualFrozenShadow.Root -Reject $true -TermId $retiredTerm -CheckTrackedState $true -ContextCase $true

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
        -CheckTrackedState $true -ContextCase $true
    }
  }
} finally {
  if ([System.IO.Directory]::Exists($absoluteFixtureRoot)) {
    [System.IO.Directory]::Delete($absoluteFixtureRoot, $true)
  }
  if ($null -ne $baselineStatus -and $null -ne $baselineTrackedHashes) {
    Assert-TrackedStateUnchanged -Context "final-clean-restoration"
  }
}

$contextCount = $observedContextIds.Count
if (-not $AbsoluteWindowsOnly) {
  $contextRegistryValid =
    $observedContextIds.Count -eq $expectedContextFixtureIds.Count -and
    @($observedContextIds | Group-Object | Where-Object Count -ne 1).Count -eq 0
  if ($contextRegistryValid) {
    for ($i = 0; $i -lt $expectedContextFixtureIds.Count; $i += 1) {
      if ($observedContextIds[$i] -ne $expectedContextFixtureIds[$i]) {
        $contextRegistryValid = $false
        break
      }
    }
  }
  if (-not $contextRegistryValid) {
    Write-Host "CLAIM-POLICY-REGRESSION: FAIL [exact-context-registry]"
    $failures += 1
  } else {
    Write-Host "CLAIM-POLICY-REGRESSION: PASS [exact-context-registry] $contextCount ordered context fixtures"
  }
}

if (-not $AbsoluteWindowsOnly -and (
    $rejectCount -ne $expectedRejectCount -or
    $acceptCount -ne $expectedAcceptCount -or
    $contextCount -ne $expectedContextCount
  )) {
  Write-Host "CLAIM-POLICY-REGRESSION: FAIL [final-verdict-counts] expected $expectedRejectCount reject, $expectedAcceptCount accept, $expectedContextCount context; got $rejectCount reject, $acceptCount accept, $contextCount context"
  $failures += 1
}

if ($failures -gt 0) {
  Write-Host "CLAIM-POLICY-REGRESSION: $failures fixture failures"
  exit 1
}

if ($AbsoluteWindowsOnly) {
  Write-Host "CLAIM-POLICY-REGRESSION: ABSOLUTE-WINDOWS PASS ($contextCount production path verdicts)"
} else {
  Write-Host "CLAIM-POLICY-REGRESSION: PASS [final-verdict-counts] ($rejectCount must-reject strict verdicts, $acceptCount must-accept strict verdicts, $contextCount path/context/bypass verdicts)"
}
exit 0

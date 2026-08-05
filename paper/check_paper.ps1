#!/usr/bin/env pwsh
# Deterministic manuscript checker for the paper/ substrate.
# Windows PowerShell 5.1 compatible. Exit 0 iff every check passes.
#
# Checks:
#   1. Citation closure: every \cite key resolves to a bib entry, and every
#      bib entry is cited at least once.
#   2. Duplicate \label keys in rmq.tex; duplicate bib keys; every \ref
#      target resolves to a \label.
#   3. Forbidden tokens and overclaim phrasings in the paper deliverables.
#   4. Theorem-ledger coverage: bidirectional between \ledger{ID} anchors
#      in rmq.tex and '#### <ID>' rows in THEOREM_LEDGER.md; every ledger
#      row status is one of ACCEPTED_BASE / PROVISIONAL_ARCHITECTURE / OPEN.
#   5. Exactly one literal ARCHITECTURE_RESULT_PENDING marker in rmq.tex.

$ErrorActionPreference = "Stop"
$paperDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$failures = 0

function Fail([string]$msg) {
  Write-Host "CHECK-PAPER: FAIL: $msg"
  $script:failures = $script:failures + 1
}

function Info([string]$msg) {
  Write-Host "CHECK-PAPER: $msg"
}

function ReadText([string]$name) {
  $path = Join-Path $paperDir $name
  if (-not (Test-Path $path)) {
    Fail "required file missing: $name"
    return ""
  }
  return [System.IO.File]::ReadAllText($path)
}

$tex     = ReadText "rmq.tex"
$bib     = ReadText "references.bib"
$ledger  = ReadText "THEOREM_LEDGER.md"
$related = ReadText "RELATED_WORK_LEDGER.md"
$matrix  = ReadText "EVIDENCE_MATRIX.md"
$readme  = ReadText "README.md"
$worklog = ReadText "WORKLOG.md"

# ---------------------------------------------------------------- 1. cites
$citeKeys = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\cite\{([^}]+)\}')) {
  foreach ($k in ($m.Groups[1].Value -split ',')) {
    [void]$citeKeys.Add($k.Trim())
  }
}
$bibKeys = New-Object System.Collections.Generic.List[string]
foreach ($m in [regex]::Matches($bib, '@[A-Za-z]+\{\s*([^,\s]+)\s*,')) {
  $bibKeys.Add($m.Groups[1].Value)
}
$bibKeySet = New-Object System.Collections.Generic.HashSet[string]
foreach ($k in $bibKeys) {
  if (-not $bibKeySet.Add($k)) { Fail "duplicate bib key: $k" }
}
foreach ($k in $citeKeys) {
  if (-not $bibKeySet.Contains($k)) { Fail "cited key has no bib entry: $k" }
}
foreach ($k in $bibKeySet) {
  if (-not $citeKeys.Contains($k)) { Fail "bib entry never cited: $k" }
}
Info ("citations: {0} cite keys, {1} bib entries" -f $citeKeys.Count, $bibKeySet.Count)

# ------------------------------------------------------- 2. labels and refs
$labelSet = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\label\{([^}]+)\}')) {
  $l = $m.Groups[1].Value
  if (-not $labelSet.Add($l)) { Fail "duplicate label: $l" }
}
foreach ($m in [regex]::Matches($tex, '\\ref\{([^}]+)\}')) {
  $r = $m.Groups[1].Value
  if (-not $labelSet.Contains($r)) { Fail "unresolved \ref target: $r" }
}
Info ("labels: {0} unique labels, all refs resolve" -f $labelSet.Count)

# --------------------------------------------------- 3. forbidden phrasings
$forbidden = @(
  '\bTODO\b',
  '\bFIXME\b',
  '\bXXX\b',
  '\bTBD\b',
  '\bPLACEHOLDER\b',
  'word-RAM time',
  'we are the first',
  'first-ever',
  'first machine-checked',
  'first formalization',
  'first mechanization',
  'first mechanized succinct',
  'first verified succinct'
)
$scanTargets = [ordered]@{
  'rmq.tex'                = $tex
  'references.bib'         = $bib
  'THEOREM_LEDGER.md'      = $ledger
  'RELATED_WORK_LEDGER.md' = $related
  'EVIDENCE_MATRIX.md'     = $matrix
  'README.md'              = $readme
  'WORKLOG.md'             = $worklog
}
foreach ($name in $scanTargets.Keys) {
  $text = $scanTargets[$name]
  foreach ($pat in $forbidden) {
    if ([regex]::IsMatch($text, $pat, 'IgnoreCase')) {
      Fail "forbidden token/phrase '$pat' in $name"
    }
  }
}
Info ("forbidden-token scan: {0} patterns over {1} files" -f $forbidden.Count, $scanTargets.Count)

# ------------------------------------------------- 4. theorem-ledger coverage
$texLedger = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\ledger\{([A-Z0-9-]+)\}')) {
  [void]$texLedger.Add($m.Groups[1].Value)
}
$ledgerIds = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($ledger, '(?m)^####\s+(L-[A-Z]+-\d+)\s*$')) {
  $id = $m.Groups[1].Value
  if (-not $ledgerIds.Add($id)) { Fail "duplicate ledger row: $id" }
}
foreach ($id in $texLedger) {
  if (-not $ledgerIds.Contains($id)) { Fail "manuscript anchor has no ledger row: $id" }
}
foreach ($id in $ledgerIds) {
  if (-not $texLedger.Contains($id)) { Fail "ledger row never anchored in manuscript: $id" }
}
$allowedStatus = @('ACCEPTED_BASE', 'PROVISIONAL_ARCHITECTURE', 'OPEN')
$statusCount = 0
foreach ($m in [regex]::Matches($ledger, '(?m)^- Status:\s*(\S+)')) {
  $statusCount = $statusCount + 1
  $s = $m.Groups[1].Value
  if ($allowedStatus -notcontains $s) { Fail "illegal ledger status: $s" }
}
if ($statusCount -ne $ledgerIds.Count) {
  Fail ("ledger has {0} rows but {1} status lines" -f $ledgerIds.Count, $statusCount)
}
Info ("ledger coverage: {0} anchors <-> {1} rows, statuses legal" -f $texLedger.Count, $ledgerIds.Count)

# ------------------------------------------- 5. single pending-result marker
$markerCount = ([regex]::Matches($tex, 'ARCHITECTURE_RESULT_PENDING')).Count
if ($markerCount -ne 1) {
  Fail ("rmq.tex must contain exactly one ARCHITECTURE_RESULT_PENDING marker, found {0}" -f $markerCount)
} else {
  Info "insertion-point marker: exactly one in rmq.tex"
}

# ------------------------------------------------------------------- verdict
if ($failures -gt 0) {
  Write-Host ("CHECK-PAPER: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host "CHECK-PAPER: RESULT: PASS"
exit 0

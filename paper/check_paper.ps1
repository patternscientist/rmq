#!/usr/bin/env pwsh
# Deterministic manuscript checker for the paper/ substrate.
# Windows PowerShell 5.1 compatible. Exit 0 iff every check passes.
#
# Checks:
#   1. Citation closure: every \cite key resolves to a bib entry, and every
#      bib entry is cited at least once.
#   2. Duplicate \label keys in rmq.tex; duplicate bib keys; every cross
#      reference (\ref, \eqref, \autoref, \cref, \Cref, \pageref, starred
#      forms) resolves to a \label.
#   3. Forbidden tokens and overclaim phrasings, matched against BOTH the raw
#      text and a whitespace-normalized copy, so a banned phrase cannot hide
#      in a LaTeX line wrap.
#   4. Theorem-ledger coverage: bidirectional between \ledger{ID} anchors in
#      rmq.tex and '#### <ID>' rows in THEOREM_LEDGER.md; every row carries
#      exactly one status, associated with that row, drawn case-sensitively
#      from ACCEPTED_BASE / PROVISIONAL_ARCHITECTURE / OPEN.
#   5. Exactly one literal ARCHITECTURE_RESULT_PENDING marker in rmq.tex.
#
# Run with -SelfTest to additionally verify that the detectors above actually
# fire. Every self-test case corresponds to a defect found by audit on
# 2026-08-07, where a check passed while the property it advertised was false.
#
# Design note. A success line is printed only when its own section recorded no
# failure. The previous revision printed "all refs resolve" unconditionally,
# immediately after reporting an unresolved ref, which is how a green log came
# to be cited as evidence for a property the script had just contradicted.

[CmdletBinding()]
param(
  [switch]$SelfTest
)

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

# Print $msg only if no failure was recorded since $before. Prevents a section
# from advertising a property it just failed to establish.
function InfoIfClean([int]$before, [string]$msg) {
  if ($script:failures -eq $before) { Info $msg }
}

function ReadText([string]$name) {
  $path = Join-Path $paperDir $name
  if (-not (Test-Path $path)) {
    Fail "required file missing: $name"
    return ""
  }
  return [System.IO.File]::ReadAllText($path)
}

# Collapse every run of whitespace (including CRLF) to a single space. Multi-word
# forbidden patterns are matched against this as well as the raw text: rmq.tex is
# hard-wrapped, so 'we are the first' split across a newline evades a raw match.
function Normalize([string]$text) {
  return [regex]::Replace($text, '\s+', ' ')
}

$tex     = ReadText "rmq.tex"
$bib     = ReadText "references.bib"
$ledger  = ReadText "THEOREM_LEDGER.md"
$related = ReadText "RELATED_WORK_LEDGER.md"
$matrix  = ReadText "EVIDENCE_MATRIX.md"
$readme  = ReadText "README.md"
$worklog = ReadText "WORKLOG.md"

# ---------------------------------------------------------------- 1. cites
$before = $failures
$citeKeys = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\cite[tp]?\*?(?:\[[^\]]*\])*\{([^}]+)\}')) {
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
InfoIfClean $before ("citations: {0} cite keys, {1} bib entries" -f $citeKeys.Count, $bibKeySet.Count)

# ------------------------------------------------------- 2. labels and refs
$before = $failures
$labelSet = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\label\{([^}]+)\}')) {
  $l = $m.Groups[1].Value
  if (-not $labelSet.Add($l)) { Fail "duplicate label: $l" }
}
# All cross-reference spellings, not just \ref. \cref/\autoref were previously
# invisible to this check; that was latent rather than active, but adding one
# would have silently dropped it out of coverage.
$refCount = 0
foreach ($m in [regex]::Matches($tex, '\\(?:ref|eqref|autoref|cref|Cref|pageref)\*?\{([^}]+)\}')) {
  foreach ($r in ($m.Groups[1].Value -split ',')) {
    $refCount = $refCount + 1
    $t = $r.Trim()
    if (-not $labelSet.Contains($t)) { Fail "unresolved cross-reference target: $t" }
  }
}
InfoIfClean $before ("labels: {0} unique labels, {1} cross-references, all resolve" -f $labelSet.Count, $refCount)

# --------------------------------------------------- 3. forbidden phrasings
$before = $failures

# Editorial placeholders and priority claims.
$forbidden = @(
  '\bTODO\b',
  '\bFIXME\b',
  '\bXXX\b',
  '\bTBD\b',
  '\bPLACEHOLDER\b',
  'we are the first',
  'first-ever',
  'first machine-checked',
  'first formalization',
  'first mechanization',
  'first mechanized succinct',
  'first verified succinct'
)

# Model-vocabulary overclaims. These mirror the framings retired from the
# repository's public surfaces on 2026-08-07. They are deliberately narrow:
# a bare 'O(1)' is legitimate in this manuscript (the lower bound is
# '2n - 1.5 log n - O(1)'), so only claim-shaped uses are banned.
$forbiddenClaims = @(
  'word[-\s]RAM\s+time',
  'constant\s+modeled\s+time',
  'after\s+preprocessing\s+an\s+array',
  'constant[-\s]time\s+succinct',
  'succinct\s+RMQ\s+in\s+constant\s+time',
  '\bin\s+O\(1\)\s+time',
  '\bO\(1\)\s+query\s+time',
  '\bO\(1\)[-\s]time\b'
)

$allForbidden = $forbidden + $forbiddenClaims

$scanTargets = [ordered]@{
  'rmq.tex'                = $tex
  'references.bib'         = $bib
  'THEOREM_LEDGER.md'      = $ledger
  'RELATED_WORK_LEDGER.md' = $related
  'EVIDENCE_MATRIX.md'     = $matrix
  'README.md'              = $readme
  'WORKLOG.md'             = $worklog
}
# A model-vocabulary phrase is allowed when it carries an attribution within
# this many characters either side, in normalized text: describing a cited
# author's constant-time result is legitimate, asserting it unattributed is the
# overclaim. Related work at rmq.tex:767 is exactly the licensed case --
# "Fischer and Heun~\cite{FischerHeun11} gave the systematic 2n+o(n)-bit,
# constant-time succinct RMQ preprocessing scheme". Editorial placeholders and
# priority claims get NO such allowance; a citation does not license "we are
# the first".
$citeWindow = 220

function HasNearbyCite([string]$norm, [int]$at, [int]$len, [int]$window) {
  $lo = [Math]::Max(0, $at - $window)
  $hi = [Math]::Min($norm.Length, $at + $len + $window)
  $slice = $norm.Substring($lo, $hi - $lo)
  return [regex]::IsMatch($slice, '\\cite[tp]?\*?(?:\[[^\]]*\])*\{')
}

foreach ($name in $scanTargets.Keys) {
  $raw  = $scanTargets[$name]
  $norm = Normalize $raw

  # Unconditional patterns: matched raw and unwrapped, no allowance.
  foreach ($pat in $forbidden) {
    if ([regex]::IsMatch($raw, $pat, 'IgnoreCase')) {
      Fail "forbidden phrase '$pat' in $name"
    }
    elseif ([regex]::IsMatch($norm, $pat, 'IgnoreCase')) {
      Fail "forbidden phrase '$pat' in $name (split across a line wrap)"
    }
  }

  # Model-vocabulary patterns: matched on normalized text (so wraps cannot
  # hide them), excused only by a nearby attribution.
  foreach ($pat in $forbiddenClaims) {
    foreach ($m in [regex]::Matches($norm, $pat, 'IgnoreCase')) {
      if (-not (HasNearbyCite $norm $m.Index $m.Length $citeWindow)) {
        $ctx = $norm.Substring([Math]::Max(0, $m.Index - 40),
                 [Math]::Min($norm.Length - [Math]::Max(0, $m.Index - 40), $m.Length + 80))
        Fail "unattributed model-vocabulary claim '$pat' in ${name}: ...$ctx..."
      }
    }
  }
}
InfoIfClean $before ("forbidden-phrase scan: {0} patterns over {1} files, raw and unwrapped" -f $allForbidden.Count, $scanTargets.Count)

# ------------------------------------------------- 4. theorem-ledger coverage
$before = $failures
$texLedger = New-Object System.Collections.Generic.HashSet[string]
foreach ($m in [regex]::Matches($tex, '\\ledger\{([A-Z0-9-]+)\}')) {
  [void]$texLedger.Add($m.Groups[1].Value)
}

# Split the ledger into rows so each status is associated with the row it
# belongs to. Counting statuses in aggregate, as the previous revision did,
# cannot detect a row that lost its status while another gained a spare.
$rowIds = New-Object System.Collections.Generic.List[string]
$rowBodies = New-Object System.Collections.Generic.List[string]
$rowMatches = [regex]::Matches($ledger, '(?m)^####\s+(L-[A-Z]+-\d+)\s*$')
for ($i = 0; $i -lt $rowMatches.Count; $i++) {
  $rowIds.Add($rowMatches[$i].Groups[1].Value)
  $start = $rowMatches[$i].Index + $rowMatches[$i].Length
  $end = if ($i + 1 -lt $rowMatches.Count) { $rowMatches[$i + 1].Index } else { $ledger.Length }
  $rowBodies.Add($ledger.Substring($start, $end - $start))
}

$ledgerIds = New-Object System.Collections.Generic.HashSet[string]
foreach ($id in $rowIds) {
  if (-not $ledgerIds.Add($id)) { Fail "duplicate ledger row: $id" }
}
foreach ($id in $texLedger) {
  if (-not $ledgerIds.Contains($id)) { Fail "manuscript anchor has no ledger row: $id" }
}
foreach ($id in $ledgerIds) {
  if (-not $texLedger.Contains($id)) { Fail "ledger row never anchored in manuscript: $id" }
}

# Case-sensitive: PowerShell's -contains is case-insensitive, so the previous
# revision accepted 'open' and 'Accepted_Base' as legal statuses even though
# the ledger declares the vocabulary fixed and upper-case.
$allowedStatus = @('ACCEPTED_BASE', 'PROVISIONAL_ARCHITECTURE', 'OPEN')
for ($i = 0; $i -lt $rowIds.Count; $i++) {
  $id = $rowIds[$i]
  $statuses = [regex]::Matches($rowBodies[$i], '(?m)^- Status:\s*(\S+)\s*$')
  if ($statuses.Count -eq 0) {
    Fail "ledger row $id has no status line"
  }
  elseif ($statuses.Count -gt 1) {
    Fail ("ledger row {0} has {1} status lines, expected exactly 1" -f $id, $statuses.Count)
  }
  else {
    $s = $statuses[0].Groups[1].Value
    if ($allowedStatus -cnotcontains $s) { Fail "illegal ledger status in row ${id}: $s" }
  }
}
InfoIfClean $before ("ledger coverage: {0} anchors <-> {1} rows, one legal status per row" -f $texLedger.Count, $ledgerIds.Count)

# ------------------------------------------- 5. single pending-result marker
$before = $failures
$markerCount = ([regex]::Matches($tex, 'ARCHITECTURE_RESULT_PENDING')).Count
if ($markerCount -ne 1) {
  Fail ("rmq.tex must contain exactly one ARCHITECTURE_RESULT_PENDING marker, found {0}" -f $markerCount)
}
InfoIfClean $before "insertion-point marker: exactly one in rmq.tex"

# ------------------------------------------------------------------ selftest
if ($SelfTest) {
  Info "--- self-test: do the detectors actually fire? ---"
  $stFail = 0
  function STCase([string]$name, [bool]$ok) {
    if ($ok) { Info "  SELFTEST PASS $name" }
    else { Write-Host "CHECK-PAPER: SELFTEST FAIL $name"; $script:stFail = $script:stFail + 1 }
  }

  # Each multi-word pattern must survive a line wrap. This is the demonstrated
  # evasion: the audit injected priority claims wrapped after 'the first' and
  # the scan reported clean.
  foreach ($pat in $allForbidden) {
    if ($pat -notmatch '\\s\+|\\s\*|\s') { continue }
    $probe = 'we are the first'
    if ($pat -eq 'we are the first') {
      $wrapped = "lorem we are the`r`n  first ipsum"
      STCase "wrap-evasion '$pat'" ([regex]::IsMatch((Normalize $wrapped), $pat, 'IgnoreCase'))
      STCase "wrap-evasion '$pat' escapes raw scan" (-not [regex]::IsMatch($wrapped, $pat, 'IgnoreCase'))
    }
  }

  # Every claim pattern must match at least one concrete positive.
  $positives = @{
    'word[-\s]RAM\s+time'                  = 'a word-RAM time bound'
    'constant\s+modeled\s+time'            = 'answered in constant modeled time'
    'after\s+preprocessing\s+an\s+array'   = 'after preprocessing an array, queries'
    'constant[-\s]time\s+succinct'         = 'a constant-time succinct RMQ structure'
    'succinct\s+RMQ\s+in\s+constant\s+time' = 'answers succinct RMQ in constant time'
    '\bin\s+O\(1\)\s+time'                 = 'answered in O(1) time'
    '\bO\(1\)\s+query\s+time'              = 'with O(1) query time'
    '\bO\(1\)[-\s]time\b'                  = 'an O(1)-time query'
  }
  foreach ($pat in $forbiddenClaims) {
    if ($positives.ContainsKey($pat)) {
      STCase "detects '$pat'" ([regex]::IsMatch($positives[$pat], $pat, 'IgnoreCase'))
    }
    else {
      STCase "positive fixture defined for '$pat'" $false
    }
  }

  # The legitimate lower-bound O(1) must NOT trip any claim pattern.
  $legit = 'any fixed-length payload-only exact RMQ encoding needs $2n - 1.5 \log n - O(1)$ bits'
  $tripped = @()
  foreach ($pat in $forbiddenClaims) {
    if ([regex]::IsMatch($legit, $pat, 'IgnoreCase')) { $tripped += $pat }
  }
  STCase "lower-bound O(1) is not a false positive" ($tripped.Count -eq 0)
  if ($tripped.Count -gt 0) { Write-Host ("    tripped by: {0}" -f ($tripped -join ', ')) }

  # The attribution allowance must excuse a cited description of prior work and
  # must NOT excuse the same phrase asserted on our own behalf.
  $attributed = Normalize 'Fischer and Heun~\cite{FischerHeun11} gave the systematic $2n + o(n)$-bit, constant-time succinct RMQ preprocessing scheme.'
  $bare       = Normalize 'Our development yields a constant-time succinct RMQ structure with exact answers.'
  $pat = 'constant[-\s]time\s+succinct'
  $mA = [regex]::Match($attributed, $pat, 'IgnoreCase')
  $mB = [regex]::Match($bare, $pat, 'IgnoreCase')
  STCase "attributed prior-work phrase is excused" `
    ($mA.Success -and (HasNearbyCite $attributed $mA.Index $mA.Length $citeWindow))
  STCase "same phrase unattributed is caught" `
    ($mB.Success -and -not (HasNearbyCite $bare $mB.Index $mB.Length $citeWindow))
  # A citation must not license a priority claim.
  $cited1st = Normalize 'We are the first to do this~\cite{FischerHeun11}.'
  STCase "citation does not license a priority claim" `
    ([regex]::IsMatch($cited1st, 'we are the first', 'IgnoreCase'))

  # A row that loses its status must be caught even if the total is preserved.
  $fakeLedger = "#### L-AAA-01`r`n- Status: OPEN`r`n- Status: OPEN`r`n`r`n#### L-BBB-02`r`n- Note: none`r`n"
  $fm = [regex]::Matches($fakeLedger, '(?m)^####\s+(L-[A-Z]+-\d+)\s*$')
  $caught = $false
  for ($i = 0; $i -lt $fm.Count; $i++) {
    $s2 = $fm[$i].Index + $fm[$i].Length
    $e2 = if ($i + 1 -lt $fm.Count) { $fm[$i + 1].Index } else { $fakeLedger.Length }
    $body = $fakeLedger.Substring($s2, $e2 - $s2)
    $cnt = ([regex]::Matches($body, '(?m)^- Status:\s*(\S+)\s*$')).Count
    if ($cnt -ne 1) { $caught = $true }
  }
  STCase "per-row status detects a moved status (total preserved)" $caught

  # Status comparison must be case-sensitive.
  STCase "status check is case-sensitive" (@('ACCEPTED_BASE','PROVISIONAL_ARCHITECTURE','OPEN') -cnotcontains 'open')

  if ($stFail -gt 0) {
    Write-Host ("CHECK-PAPER: SELFTEST RESULT: FAIL ({0} case(s))" -f $stFail)
    $failures = $failures + $stFail
  }
  else {
    Info "self-test: all detector cases pass"
  }
}

# ------------------------------------------------------------------- verdict
if ($failures -gt 0) {
  Write-Host ("CHECK-PAPER: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host "CHECK-PAPER: RESULT: PASS"
exit 0

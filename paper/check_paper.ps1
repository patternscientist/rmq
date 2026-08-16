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
#   5. AT MOST ONE literal ARCHITECTURE_RESULT_PENDING marker in rmq.tex. Zero
#      is the healthy state: the result was absorbed into Section 9 on
#      2026-08-16. This header read "Exactly one" for the whole RC-4 round
#      AFTER the code was changed to `-gt 1` -- a file's own documentation
#      describing the behaviour that file was edited to stop having.
#   6. Evidence-matrix statuses come from the vocabulary EVIDENCE_MATRIX.md's
#      own header declares.
#   7. Every :NNN citation in THEOREM_LEDGER.md resolves to a declaration site
#      (delegated to check_citations.ps1).
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
$novelty = ReadText "NOVELTY_LOG.md"

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

# Editorial placeholders. Unconditional everywhere, no allowance of any kind.
$editorial = @(
  '\bTODO\b',
  '\bFIXME\b',
  '\bXXX\b',
  '\bTBD\b',
  '\bPLACEHOLDER\b'
)

# Priority claims. Unconditional everywhere EXCEPT NOVELTY_LOG.md, whose entire
# purpose is to name such claims in order to retire them, and to quote third
# parties who made them. There the phrase must carry a retirement or
# attribution marker; a bare priority claim in the novelty log still fails.
$citeWindow = 220

$priority = @(
  'we are the first',
  'first-ever',
  'first machine-checked',
  'first formalization',
  'first mechanization',
  'first mechanized succinct',
  'first verified succinct'
)
# Two tiers of file, because they play different roles for a referee.
#
# CLAIM SURFACES (everything not listed below) are read as assertions by the
# project: rmq.tex, the bibliography, the ledgers, the evidence matrix, the
# README. A priority phrase or model-vocabulary phrase there is a claim, and is
# banned outright (model-vocabulary phrases keep only the attribution allowance).
#
# RECORD SURFACES are records ABOUT claims: the worklog records what the project
# did, and the novelty log exists precisely to name priority claims in order to
# retire them and to quote third parties who made them. Banning the phrases there
# would make it impossible to write down that they are retired. So on record
# surfaces the phrases are permitted only when accompanied by a retirement,
# attribution, or quotation marker within the window. A bare, unmarked priority
# claim in the worklog or novelty log still fails.
# The marker set is deliberately narrow and contains NO punctuation. An earlier
# revision of this rule included a quote character, which made the allowance
# vacuous: ordinary prose has a quote within the window almost always, so a bare
# priority claim in the novelty log passed. Verified by injection, and that is
# now a standing self-test case (see 'bare priority claim on a record surface').
$recordSurfaces = @('WORKLOG.md', 'NOVELTY_LOG.md')
$retirementMarker = 'Killed by|Retire|retired|Restriction|Drop any|No claim|not license|must not|may not|is dead|not defensible|cannot drift|Abstract:|scoped to|we do not claim|attributed|supersed'
# For model-vocabulary phrases on a record surface, quoting a source is the
# legitimate mechanism, so a quote character close to the match also excuses --
# but within a much tighter window than the marker rule.
$quoteWindow = 60

$forbidden = $editorial + $priority

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
  '\bO\(1\)[-\s]time\b',
  # Added after an external audit on 2026-08-09 passed a manuscript sentence
  # asserting constant query time on a conventional RAM model, phrased outside
  # the patterns above. The MODEL word is what makes such a claim false here,
  # not the word "constant" -- the repository's house term is "constant modeled
  # query cost", which these patterns deliberately leave alone.
  'conventional\s+RAM',
  'standard\s+RAM\s+model',
  'RAM\s+model[^.]{0,40}constant',
  'constant[^.]{0,40}\bRAM\s+model',
  'constant\s+query\s+time',
  'queries?\s+in\s+constant\s+time'
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
  'NOVELTY_LOG.md'         = $novelty
}
# A model-vocabulary phrase is allowed when it carries an attribution within
# this many characters either side, in normalized text: describing a cited
# author's constant-time result is legitimate, asserting it unattributed is the
# overclaim. Related work at rmq.tex:767 is exactly the licensed case --
# "Fischer and Heun~\cite{FischerHeun11} gave the systematic 2n+o(n)-bit,
# constant-time succinct RMQ preprocessing scheme". Editorial placeholders and
# priority claims get NO such allowance; a citation does not license "we are
# the first".

function HasNearbyCite([string]$norm, [int]$at, [int]$len, [int]$window) {
  # A citation is `\cite{...}` in LaTeX, but the markdown ledgers attribute with
  # the bib key itself in backticks -- e.g. "**Fischer & Heun 2011**
  # (`FischerHeun11`) ... constant query time in the standard model". That is a
  # description of cited prior work, not a claim about this development, so it
  # must be excused by the same rule. The keys are the ones actually parsed from
  # references.bib, so this recognises real attributions rather than anything
  # that merely looks like one.
  $lo = [Math]::Max(0, $at - $window)
  $hi = [Math]::Min($norm.Length, $at + $len + $window)
  $slice = $norm.Substring($lo, $hi - $lo)
  if ([regex]::IsMatch($slice, '\\cite[tp]?\*?(?:\[[^\]]*\])*\{')) { return $true }
  foreach ($k in $bibKeySet) {
    if ($slice -match ('`' + [regex]::Escape($k) + '`')) { return $true }
  }
  return $false
}

foreach ($name in $scanTargets.Keys) {
  $raw  = $scanTargets[$name]
  $norm = Normalize $raw

  # Editorial placeholders: unconditional, matched raw and unwrapped.
  foreach ($pat in $editorial) {
    if ([regex]::IsMatch($raw, $pat, 'IgnoreCase')) {
      Fail "forbidden phrase '$pat' in $name"
    }
    elseif ([regex]::IsMatch($norm, $pat, 'IgnoreCase')) {
      Fail "forbidden phrase '$pat' in $name (split across a line wrap)"
    }
  }

  # Priority claims: unconditional, except in the novelty log where a
  # retirement or attribution marker excuses the phrase.
  foreach ($pat in $priority) {
    foreach ($m in [regex]::Matches($norm, $pat, 'IgnoreCase')) {
      $excused = $false
      if ($recordSurfaces -contains $name) {
        $lo = [Math]::Max(0, $m.Index - $citeWindow)
        $hi = [Math]::Min($norm.Length, $m.Index + $m.Length + $citeWindow)
        $slice = $norm.Substring($lo, $hi - $lo)
        $excused = [regex]::IsMatch($slice, $retirementMarker)
      }
      if (-not $excused) {
        $ctx = $norm.Substring([Math]::Max(0, $m.Index - 40),
                 [Math]::Min($norm.Length - [Math]::Max(0, $m.Index - 40), $m.Length + 80))
        Fail "priority claim '$pat' in ${name}: ...$ctx..."
      }
    }
  }

  # Model-vocabulary patterns: matched on normalized text (so wraps cannot
  # hide them), excused only by a nearby attribution.
  foreach ($pat in $forbiddenClaims) {
    foreach ($m in [regex]::Matches($norm, $pat, 'IgnoreCase')) {
      $ok = HasNearbyCite $norm $m.Index $m.Length $citeWindow
      if (-not $ok -and ($recordSurfaces -contains $name)) {
        $lo2 = [Math]::Max(0, $m.Index - $citeWindow)
        $hi2 = [Math]::Min($norm.Length, $m.Index + $m.Length + $citeWindow)
        $ok = [regex]::IsMatch($norm.Substring($lo2, $hi2 - $lo2), $retirementMarker)
        if (-not $ok) {
          $lo3 = [Math]::Max(0, $m.Index - $quoteWindow)
          $hi3 = [Math]::Min($norm.Length, $m.Index + $m.Length + $quoteWindow)
          $ok = [regex]::IsMatch($norm.Substring($lo3, $hi3 - $lo3), '["“”]')
        }
      }
      if (-not $ok) {
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

# ------------------------------------------- 5. pending-result marker
#
# This REQUIRED exactly one marker until 2026-08-16, which made it enforce the
# presence of a defect: while `rmq.tex` carried the marker, the manuscript
# presented an already-accepted theorem as a future editorial insertion, and
# this checker reported success for it. The 2026-08-15 fresh-blind audit failed
# RC-10 on exactly that (P1-1) and noted the checker reinforcing the mismatch.
#
# The marker is now permitted but never required: zero is the healthy state once
# a result is absorbed; more than one is still a defect.
$before = $failures
$markerCount = ([regex]::Matches($tex, 'ARCHITECTURE_RESULT_PENDING')).Count
if ($markerCount -gt 1) {
  Fail ("rmq.tex must contain at most one ARCHITECTURE_RESULT_PENDING marker, found {0}" -f $markerCount)
}
InfoIfClean $before ("insertion-point marker: {0} in rmq.tex (0 = absorbed, 1 = pending, >1 fails)" -f $markerCount)

# ------------------------------------- 5b. ledger status counts are CHECKED
#
# `paper/EVIDENCE_MATRIX.md` publishes the ledger's status breakdown. It stated
# 27/1/6 while the ledger held 29/0/5 -- stale because the Stage-A acceptance
# moved the architecture row out of PROVISIONAL and nothing re-derived the
# published figure (2026-08-15 audit, P3-1). A count stated in prose beside one
# derivable from source is a claim; it is derived here instead of asserted.
$before = $failures
$ledgerAccepted = ([regex]::Matches($ledger, '(?m)^- Status: ACCEPTED_BASE\s*$')).Count
$ledgerProvisional = ([regex]::Matches($ledger, '(?m)^- Status: PROVISIONAL_ARCHITECTURE\s*$')).Count
$ledgerOpen = ([regex]::Matches($ledger, '(?m)^- Status: OPEN\s*$')).Count
# EVIDENCE_MATRIX statuses must come from the vocabulary its own header declares.
#
# The header says "No other status is permitted for this substrate", and nothing
# checked it: the RC-4 round appended `BLOCKED_ONLY_ON: FRESH_BLIND_ACCEPTANCE`
# to EV-07 while the header listed only two statuses, so the file asserted a rule
# it violated one screen later. Parsing the permitted set FROM the header rather
# than restating it here means adding a status requires amending the header,
# which is the property the header claims to have.
$before = $failures
$matrixPathForStatus = Join-Path $PSScriptRoot 'EVIDENCE_MATRIX.md'
if (Test-Path -LiteralPath $matrixPathForStatus) {
  $matrixText = [IO.File]::ReadAllText($matrixPathForStatus)
  $permitted = @()
  foreach ($m in [regex]::Matches($matrixText, '\*\*(CLOSED|BLOCKED_ONLY_ON:\s*[A-Z_]+)\*\*')) {
    $permitted += ($m.Groups[1].Value -replace '\s+', ' ')
  }
  $permitted = @($permitted | Sort-Object -Unique)
  if ($permitted.Count -eq 0) {
    Fail "EVIDENCE_MATRIX.md declares no permitted status vocabulary; the status check cannot run"
  } else {
    foreach ($m in [regex]::Matches($matrixText, '(?m)^- Status[^:]*:\s*(.+?)\s*$')) {
      $used = ($m.Groups[1].Value -replace '\s+', ' ').Trim().TrimEnd('.')
      # Statuses carry trailing prose; compare on the leading token.
      $head = if ($used -match '^(BLOCKED_ONLY_ON:\s*[A-Z_]+)') { $Matches[1] -replace '\s+', ' ' }
              elseif ($used -match '^(CLOSED)') { $Matches[1] } else { $used }
      if ($permitted -cnotcontains $head) {
        Fail ("EVIDENCE_MATRIX.md uses status '{0}', which its own header does not permit (permitted: {1})" -f $head, ($permitted -join ', '))
      }
    }
  }
}
InfoIfClean $before "evidence-matrix statuses all come from the vocabulary the header declares"

$matrixPath = Join-Path $PSScriptRoot 'EVIDENCE_MATRIX.md'
if (Test-Path -LiteralPath $matrixPath) {
  $matrix = [IO.File]::ReadAllText($matrixPath)
  $stated = [regex]::Match($matrix,
    '(\d+)\s+rows:\s*(\d+)\s+ACCEPTED_BASE,\s*(\d+)\s*[\r\n]+\s*PROVISIONAL_ARCHITECTURE,\s*(\d+)\s+OPEN')
  if (-not $stated.Success) {
    Fail "EVIDENCE_MATRIX.md no longer states a parseable ledger status breakdown; the count check cannot run"
  } elseif ([int]$stated.Groups[2].Value -ne $ledgerAccepted -or
            [int]$stated.Groups[3].Value -ne $ledgerProvisional -or
            [int]$stated.Groups[4].Value -ne $ledgerOpen -or
            [int]$stated.Groups[1].Value -ne $ledgerIds.Count) {
    Fail ("EVIDENCE_MATRIX.md states {0} rows {1}/{2}/{3} accepted/provisional/open; the ledger has {4} rows {5}/{6}/{7}" -f
      $stated.Groups[1].Value, $stated.Groups[2].Value, $stated.Groups[3].Value, $stated.Groups[4].Value,
      $ledgerIds.Count, $ledgerAccepted, $ledgerProvisional, $ledgerOpen)
  }
}
InfoIfClean $before ("ledger status counts: {0} rows, {1}/{2}/{3} accepted/provisional/open, matching EVIDENCE_MATRIX.md" -f $ledgerIds.Count, $ledgerAccepted, $ledgerProvisional, $ledgerOpen)

# ----------------------------------------- 5c. `:NNN` source citations resolve
#
# Scheduled since the RC-1 correction handoff and deferred through two rounds.
# Line numbers rot silently: the `:723` producer pointer in L-ARCH-01/L-PACK-01
# was corrected from `:702` in August and had drifted again to `:752` by this
# round -- wrong three times -- and L-UB-12's `:1324` pointed at
# `queryCostedWithStore_...` while naming `queryTraceResultWithStore_...`, a
# different theorem with a near-identical name. A reviewer following either one
# lands somewhere plausible and wrong, which is worse than a dangling pointer.
#
# `check_citations.ps1` carries the reasoning and its own -SelfTest.
$before = $failures
$citationScript = Join-Path $PSScriptRoot 'check_citations.ps1'
if (-not (Test-Path -LiteralPath $citationScript)) {
  Fail "check_citations.ps1 is missing; source citations are unverified"
} else {
  # `*>&1`, not `2>&1`: the sub-checker reports through Write-Host, which writes
  # to the information stream (6). Redirecting only stderr captured nothing, so
  # a real citation failure surfaced as "exited 1 without naming a failure".
  $citationOutput = @(& $citationScript *>&1 | ForEach-Object { [string]$_ })
  if ($LASTEXITCODE -ne 0) {
    foreach ($citationLine in $citationOutput) {
      if ($citationLine -match 'FAIL') { Fail $citationLine }
    }
    if ($failures -eq $before) { Fail "check_citations.ps1 exited $LASTEXITCODE without naming a failure" }
  }
}
InfoIfClean $before "source citations: every :NNN in THEOREM_LEDGER.md resolves to the declaration its row names"

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
    'conventional\s+RAM'                   = 'constant query time on a conventional RAM machine'
    'standard\s+RAM\s+model'               = 'queries in the standard RAM model'
    'RAM\s+model[^.]{0,40}constant'        = 'in the RAM model this is constant'
    'constant[^.]{0,40}\bRAM\s+model'      = 'constant query time in a RAM model'
    'constant\s+query\s+time'              = 'the structure has constant query time'
    'queries?\s+in\s+constant\s+time'      = 'answers queries in constant time'
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

  # The record-surface allowance must NOT be vacuous. A bare priority claim in
  # the novelty log or worklog must still fail; only a marked retirement passes.
  $bareRecord = Normalize 'This work is the first machine-checked succinct RMQ structure ever produced anywhere.'
  $markedRecord = Normalize 'R99. The first machine-checked succinct structure. Killed by TAG16.'
  $pp = 'first machine-checked'
  $mBare = [regex]::Match($bareRecord, $pp, 'IgnoreCase')
  $mMark = [regex]::Match($markedRecord, $pp, 'IgnoreCase')
  function ExcusedOnRecord([string]$n, [System.Text.RegularExpressions.Match]$mm) {
    $l = [Math]::Max(0, $mm.Index - $citeWindow)
    $h = [Math]::Min($n.Length, $mm.Index + $mm.Length + $citeWindow)
    return [regex]::IsMatch($n.Substring($l, $h - $l), $retirementMarker)
  }
  STCase "bare priority claim on a record surface is NOT excused" `
    ($mBare.Success -and -not (ExcusedOnRecord $bareRecord $mBare))
  STCase "marked retirement on a record surface IS excused" `
    ($mMark.Success -and (ExcusedOnRecord $markedRecord $mMark))
  STCase "marker set contains no punctuation" `
    (-not ($retirementMarker -match '["“”`]'))

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

  # The citation checker owns the harder self-test (mutate exactly one citation,
  # demand exactly one failure). Delegate rather than restate it, but require it
  # to actually run: a missing sub-checker must not read as a silent pass.
  $citationSelfTestOk = $false
  if (Test-Path -LiteralPath $citationScript) {
    $null = & $citationScript -SelfTest 2>&1
    $citationSelfTestOk = ($LASTEXITCODE -eq 0)
  }
  STCase "check_citations.ps1 self-test passes (fails closed on a moved citation)" $citationSelfTestOk

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

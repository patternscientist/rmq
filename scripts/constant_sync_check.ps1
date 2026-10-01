#!/usr/bin/env pwsh
# Current-constant synchronization guard: Lean is the source of truth, the
# public surfaces must agree with it.
#
# WHY THIS EXISTS. `docs/internal/CLAIM_DRIFT_POLICY.json` guards every RETIRED
# constant (76, 142, 207, 328, 352, 118, 4144, 196727, 2^128) and neither of the
# CURRENT ones. `427` appears nowhere in the policy; `210` appears only inside an
# allowedLineRegex exception. The consequence, recorded as DD-20260807-087: if a
# proved bound moved, the Lean build would fail until updated, and then dozens of
# public lines would go on asserting the stale numeral with green CI.
#
# That gap is structural, not an oversight. Guarding a retired value is a
# negative "must not appear" grep, which a regex policy expresses fine. Guarding
# a CURRENT value needs a positive Lean-versus-docs equality check, which it
# cannot express. Hence a separate script.
#
# HOW IT WORKS. Each constant below names a Lean file and a regex whose capture
# group is the authoritative numeral. The script:
#   1. extracts the value from Lean;
#   2. compares it against the pinned expectation here -- so changing the proved
#      bound fails THIS script too, forcing the doc update into the same change
#      rather than letting it be forgotten;
#   3. requires every listed public surface to state the current value;
#   4. fails if a surface states a superseded value in a current-claim context.
#
# Exit 0 iff Lean and the public surfaces agree.
#
# Run with -SelfTest to verify the extractor and the drift detector actually
# fire. A guard that cannot fail is not a guard.

[CmdletBinding()]
param(
  [switch]$SelfTest
)

$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path (Split-Path -Parent $MyInvocation.MyCommand.Path) '..')).Path
$failures = 0

function Fail([string]$m) { Write-Host "CONST-SYNC: FAIL: $m"; $script:failures = $script:failures + 1 }
function Info([string]$m) { Write-Host "CONST-SYNC: $m" }

# The three current constants. `expected` is the pin: it must be updated in the
# same change that moves the proof, which is the point.
$constants = @(
  @{
    name     = 'charged-trace cap'
    expected = '210'
    leanFile = 'RMQ/Core/SuccinctFinalRAM.lean'
    leanPat  = 'concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = (\d+)'
    # Values this constant has previously had. Their appearance in a
    # current-claim context on a public surface is drift.
    retired  = @('76', '142', '207')
    # `anchors` are claim-shaped phrases that must carry the current numeral;
    # `{VALUE}` is substituted with the Lean-derived value. `count` pins the
    # total occurrences so corrupting ANY of them fails, including ones no
    # anchor names. A count of 0 disables the count check for that surface.
    # 2026-09-11 (PQ1 public-surface synchronization): every move below is a
    # deliberate restatement of the SAME `210`, added to keep the separate
    # 837,572 primitive-instruction candidate from being read as a change to
    # it -- either "the 210 trace bound is separate" or "the 210 theorem leaves
    # the controller uncharged". No sentence restates a different value, and
    # the anchors and claim shapes are unchanged. The PQ1 worker's own export
    # commit had already added one such restatement to README, CLAIMS,
    # PAPER_THEOREM_MAP and PAPER_CLAIM_CORRESPONDENCE without moving these
    # pins, which is why the gate stage failed before this change.
    surfaces = @(
      # V1 landing-page condensation: 1 deliberate statements of the same bound.
      @{ path = 'README.md';                          count = 1; anchors = @('charged-trace cap is `{VALUE}`') },
      # 10 -> 13: PQ1 section contrast, Scope bullet and Non-Claims bullet.
      @{ path = 'artifact/CLAIMS.md';                 count = 13; anchors = @('at most\*\* `{VALUE}`') },
      # 9 -> 10: Cost Model bullet scoping the uncharged controller to `210`.
      @{ path = 'docs/WHAT_IS_PROVED.md';             count = 10; anchors = @('charged-trace bound is `{VALUE}`') },
      # 11 -> 13 on 2026-08-12: the execution-cost sentence was corrected from
      # "is exactly `210`" to a budget-plus-inequality statement, which names
      # the constant twice more.  The pin moved in the same edit, as this check
      # demands.  Note what that does and does not show: the count moving
      # proves the change was deliberate, not that the new wording is right.
      # This check reads numerals, never the relation around them, so it would
      # have passed "exactly 210" forever.
      # 13 -> 16 on 2026-09-11: PQ1 section contrast, the E1-supersession
      # sentence ("does not reinterpret `210`") and the rescoped Non-Claims.
      @{ path = 'docs/PAPER_THEOREM_MAP.md';          count = 16; anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace \*\*budget\*\* is `{VALUE}`', 'literal bound `{VALUE}`') },
      # 11 -> 12: PQ1 status paragraph contrast (PQ1 export, restated).
      @{ path = 'docs/PAPER_CLAIM_CORRESPONDENCE.md'; count = 12; anchors = @('at most\*\* `{VALUE}`') },
      @{ path = 'docs/TRUST_AUDIT_PACKET.md';         count = 7;  anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace cost at most `{VALUE}`') },
      # 7 -> 8: PQ1 scope paragraph ("the `210` trace and `427` probe bounds").
      @{ path = 'docs/FAMILY_SUMMARY.md';             count = 8;  anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace constant `{VALUE}`') },
      @{ path = 'docs/V1_GUIDE.md';                   count = 1;
         anchors = @('\| `{VALUE}` \| Canonical reviewer query''s charged trace \|') },
      @{ path = 'docs/V1_CLIENTS.md';                 count = 3;
         anchors = @('Earlier paper cost at most `{VALUE}`') }
    )
  },
  @{
    name     = 'derived packed probe cap'
    expected = '427'
    leanFile = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean'
    leanPat  = 'derived_cap_le_(\d+)'
    retired  = @()
    # 2026-09-11 (PQ1): both moves restate the same `427` as a quantity the
    # separate primitive-instruction candidate does not reinterpret.
    surfaces = @(
      # 5 -> 7: PQ1 section contrast (PQ1 export) and rescoped Non-Claims.
      @{ path = 'docs/PAPER_THEOREM_MAP.md';          count = 7;
         anchors = @('at most `{VALUE}` attempted aligned', 'derived_cap_le_{VALUE}',
                     '`{VALUE}` is an \*\*upper bound') },
      # 5 -> 6: PQ1 status paragraph contrast (PQ1 export, restated).
      @{ path = 'docs/PAPER_CLAIM_CORRESPONDENCE.md'; count = 6;
         anchors = @('at most `{VALUE}` attempted aligned', 'derived numeral `{VALUE}`',
                     '`{VALUE}` is an upper bound') },
      @{ path = 'docs/V1_GUIDE.md';                   count = 1;
         anchors = @('\| `{VALUE}` \| Packed cell-probe controller \|') }
    )
  },
  @{
    name     = 'packed primitive query budget'
    expected = '837572'
    leanFile = 'RMQ/Core/WordRAM/Packed/Capstone.lean'
    leanPat  = '(?m)^\s*budgetExact\s*:\s*queryBudget\s*=\s*(\d+)\s*$'
    retired  = @()
    # A third model: this is the capstone's primitive-transition budget,
    # separate from trace ticks, packed probes and native runtime.
    surfaces = @(
      @{ path = 'README.md';                          count = 2;
         anchors = @('closed loop-free program of\s+{VALUE} primitive instructions',
                     'run halts within at most {VALUE} steps') },
      @{ path = 'artifact/CLAIMS.md';                 count = 4;
         anchors = @('closed loop-free program of {VALUE} primitive instructions',
                     'run halts within at most {VALUE} steps',
                     'halt within at most {VALUE} primitive instructions') },
      @{ path = 'docs/PAPER_THEOREM_MAP.md';          count = 2;
         anchors = @('fixed {VALUE}-step\s+budget equal to the length of the loop-free `queryProgram`') },
      @{ path = 'docs/V1_GUIDE.md';                   count = 1;
         anchors = @('\| `{VALUE}` \| Fixed loop-free primitive query program on per-input `buildMemory xs`; theorem `RMQ\.Headlines\.succinctRMQFullyChargedPackedQuery`') }
    )
  }
)

# A retired numeral is allowed on a line that marks itself historical. This
# mirrors the claim-drift policy's own exculpating vocabulary rather than
# inventing a second one.
# `was` was REMOVED on 2026-08-16. It exempted any line containing the word
# "was", so "The uniform canonical charged-trace constant `214` was adopted for
# all sizes." -- a conflicting claim, phrased in the surface's OWN declared
# shape -- passed with exit 0. Changing that one word to "is" made the same
# line exit 1.
#
# Strictly worse than the shape-coverage residual WDD-20260816-042 records:
# that one is about conflicts phrased OUTSIDE a declared shape. This conflict
# was INSIDE the shape and still passed, on one common English verb. Nothing in
# the guarded surfaces relies on bare "was" to mark a retired value.
$historicalMarker = 'historical|Historical|retired|Retired|superseded|Superseded|formerly|previously|CLAIM-HISTORY'

# A historical marker excuses a numeral only when it is ATTACHED to it.
#
# The two tests below were `$line -match $historicalMarker`, which exempts the
# WHOLE LINE. These are common prose words, not annotations: one `previously`
# anywhere in a wide table row excused every conflicting numeral in that row,
# including one stated as current fact hundreds of characters away. The rows in
# these surfaces are routinely that wide -- see the acceptance matrices, whose
# single lines run past 1000 characters.
#
# Proximity is the fix. The marker must fall within reach of the numeral it
# excuses. The reach is deliberately generous: the point is to stop an
# unrelated clause from granting the exemption, not to demand a fixed phrasing.
$historicalMarkerReach = 120

function Test-HistoricalContext {
  param([string]$Line, [int]$At, [int]$Length)
  if ($Line.Length -eq 0) { return $false }
    # The marker must mark THIS numeral, not merely share a line with it.
    # Measured 2026-09-08: prefixing 'Historical background is elsewhere.' to
    # 'The current charged-trace constant `214` applies to every query.' flipped
    # this checker from exit 1 to exit 0 while the false current-fact assertion
    # stood. So the window is the SENTENCE holding the numeral, and a sentence
    # asserting a current fact is never historical.
    $sentenceLo = $Line.LastIndexOfAny([char[]]@('.', ';'), [Math]::Max(0, $At - 1))
    if ($sentenceLo -lt 0) { $sentenceLo = 0 } else { $sentenceLo += 1 }
    $sentenceHi = $Line.IndexOfAny([char[]]@('.', ';'), [Math]::Min($Line.Length - 1, $At + $Length))
    if ($sentenceHi -lt 0) { $sentenceHi = $Line.Length }
    if ($sentenceHi -le $sentenceLo) { return $false }
    $sentence = $Line.Substring($sentenceLo, $sentenceHi - $sentenceLo)
    if ($sentence -match '(?i)\b(?:current|currently|now|today|applies\s+to\s+every)\b') { return $false }
    return ($sentence -match $historicalMarker)
}

# An anchor doubles as a CLAIM SHAPE when it carries enough literal text to
# identify a claim on its own. `at most** `{VALUE}`` does; a bare `` `{VALUE}` ``
# does not -- as a shape it would match every backticked numeral in the file,
# including historical ones, and report conflicts that are not conflicts.
# Four letters is the threshold; it is arbitrary but it separates the two
# shapes actually in use here, and a shape that falls below it simply keeps its
# weaker anchor-only treatment rather than silently becoming a false alarm.
function Test-IsClaimShape([string]$anchor) {
  $literal = $anchor -replace '\{VALUE\}', ''
  return (($literal -replace '[^A-Za-z_]', '').Length -ge 4)
}

# Consume each whole numeral before normalization. In particular, a comma
# cannot truncate 837,572 to 837 or expose a trailing 210 as a trace-cap hit.
# Invalid grouping remains a whole token and is rejected inside claim shapes.
$numeralTokenPattern = '(?<![0-9,])[0-9]+(?:,[0-9]+)*(?![0-9]|,[0-9])'
function ConvertTo-NumeralValue([string]$Token) {
  if ($Token -notmatch '^(?:[0-9]+|[0-9]{1,3}(?:,[0-9]{3})+)$') { return $null }
  return ($Token -replace ',', '')
}

function Get-ValuePattern([string]$Value) {
  $grouped = [regex]::Replace($Value, '(?<=\d)(?=(?:\d{3})+$)', ',')
  return '(?<![0-9,])(?:' + [regex]::Escape($Value) + '|' +
    [regex]::Escape($grouped) + ')(?![0-9]|,[0-9])'
}

# All surface conditions in one place, over TEXT rather than a path, so the
# self-test exercises this exact code against fixtures instead of restating the
# logic. A self-test that re-implements the check can pass while the check is
# broken -- that is the failure mode this script was written to catch.
function Get-SurfaceFailures {
  param(
    [string]$Text,
    [hashtable]$Entry,
    [string]$Actual,
    [string[]]$Retired,
    [string]$ConstantName,
    [string]$SurfacePath
  )

  $out = @()
  $actualPattern = Get-ValuePattern $Actual

  foreach ($anchor in $Entry.anchors) {
    $pat = $anchor.Replace('{VALUE}', $actualPattern)
    if ($Text -notmatch $pat) {
      $out += ("{0}: {1} anchor /{2}/ does not carry the current value {3}" -f $ConstantName, $SurfacePath, $anchor, $Actual)
    }
  }

  # CONFLICTING NUMERALS. The anchor check asks whether the claim appears with
  # the right value SOMEWHERE; the count check asks whether the right value
  # appears the right number of times. Neither catches an ADDED claim carrying a
  # different numeral: inserting "at most **`214`**" leaves every `210` intact
  # and every anchor satisfied, so both conditions hold while the surface asserts
  # two incompatible bounds.
  #
  # Every instantiation of a claim shape must carry the current value, not merely
  # one of them.
  #
  # Shapes come from qualifying anchors PLUS explicit `claimShapes`. Three
  # surfaces carry only a bare `` `{VALUE}` `` anchor, which cannot serve as a
  # shape -- it matches every backticked numeral in the file, historical ones
  # included. Those three were therefore outside this scan entirely while
  # WDD-20260816-035 presented the hole as closed: injecting the very text that
  # entry cites as its proof into `docs/FAMILY_SUMMARY.md` exited 0. Found by
  # audit. A surface with no shape at all is now itself a failure, so this cannot
  # recur silently for a surface added later.
  $conflictShapes = @()
  foreach ($anchor in $Entry.anchors) {
    if (Test-IsClaimShape $anchor) { $conflictShapes += $anchor }
  }
  if ($Entry.ContainsKey('claimShapes')) {
    foreach ($declared in @($Entry.claimShapes)) { $conflictShapes += $declared }
  }
  if ($conflictShapes.Count -eq 0) {
    $out += ("{0}: {1} declares no claim shape, so a conflicting numeral added to it would go undetected; give it a 'claimShapes' entry" -f $ConstantName, $SurfacePath)
  }

  foreach ($shapeSpec in $conflictShapes) {
    $shape = $shapeSpec.Replace('{VALUE}', ('(?<ClaimValue>' + $numeralTokenPattern + ')'))
    # A shape matching nothing is silent non-protection. WDD-20260816-035
    # reported this hole closed and quoted an injection its own shape could not
    # match ("at most **`214`**" against a shape requiring "at most** `"), so
    # the verification never exercised the shape it claimed to verify.
    if (-not [regex]::IsMatch($Text, $shapeSpec.Replace('{VALUE}', $actualPattern))) {
      $out += ("{0}: {1} declares claim shape /{2}/ but nothing in the file matches it with the current value; the shape protects nothing" -f `
        $ConstantName, $SurfacePath, $shapeSpec)
    }
    foreach ($hit in [regex]::Matches($Text, $shape)) {
      $claimToken = $hit.Groups['ClaimValue'].Value
      if ((ConvertTo-NumeralValue $claimToken) -ceq $Actual) { continue }
      # A historical line may legitimately restate a superseded value.
      $lineStart = $Text.LastIndexOf("`n", [Math]::Max(0, [Math]::Min($hit.Index, $Text.Length - 1))) + 1
      $lineEnd = $Text.IndexOf("`n", $hit.Index)
      if ($lineEnd -lt 0) { $lineEnd = $Text.Length }
      $line = $Text.Substring($lineStart, $lineEnd - $lineStart)
      if (Test-HistoricalContext -Line $line -At ($hit.Index - $lineStart) -Length $hit.Length) { continue }
      $out += ("{0}: {1} states a CONFLICTING value {2} in a current claim (shape /{3}/); the proved value is {4}: {5}" -f `
        $ConstantName, $SurfacePath, $claimToken, $shapeSpec, $Actual, $line.Trim())
    }
  }

  $occ = @([regex]::Matches($Text, $numeralTokenPattern) |
    Where-Object { (ConvertTo-NumeralValue $_.Value) -ceq $Actual }).Count
  if ($occ -ne $Entry.count) {
    $out += ("{0}: {1} states {2} {3} time(s), pinned at {4}. If the surface genuinely changed, update the pin in the same edit." -f $ConstantName, $SurfacePath, $Actual, $occ, $Entry.count)
  }

  foreach ($r in $Retired) {
    foreach ($line in ($Text -split "`r?`n")) {
      foreach ($rm in [regex]::Matches($line, '\b' + [regex]::Escape($r) + '\b')) {
        if (Test-HistoricalContext -Line $line -At $rm.Index -Length $rm.Length) { continue }
        $out += ("{0}: {1} states superseded value {2} without a historical marker: {3}" -f $ConstantName, $SurfacePath, $r, $line.Trim().Substring(0, [Math]::Min(90, $line.Trim().Length)))
        break
      }
    }
  }

  return $out
}

function Get-LeanValue([string]$file, [string]$pat) {
  $p = Join-Path $repoRoot $file
  if (-not (Test-Path -LiteralPath $p)) { return $null }
  $m = [regex]::Match([System.IO.File]::ReadAllText($p), $pat)
  if (-not $m.Success) { return $null }
  return $m.Groups[1].Value
}

foreach ($c in $constants) {
  $actual = Get-LeanValue $c.leanFile $c.leanPat
  if ($null -eq $actual) {
    Fail ("could not extract the {0} from {1} using /{2}/ -- the anchor moved, so this guard is blind; fix the pattern" -f $c.name, $c.leanFile, $c.leanPat)
    continue
  }
  if ($actual -ne $c.expected) {
    Fail ("{0}: Lean proves {1} but this script pins {2}. If the bound genuinely moved, update this pin AND every public surface in the same change." -f $c.name, $actual, $c.expected)
    continue
  }

  # Every listed surface must state the current value, checked at ANCHORS and by
  # COUNT -- not by file-wide presence.
  #
  # The previous revision asked only whether the numeral appeared anywhere in the
  # file. An external audit on 2026-08-09 corrupted one of five `427`s in
  # PAPER_THEOREM_MAP.md to `999`; four remained, so the check passed. That is
  # the vacuity failure this script exists to prevent, reproduced inside the
  # script itself.
  #
  # Two independent conditions now hold per surface:
  #   anchors -- named claim-shaped phrases must carry the current numeral, so a
  #              corrupted claim fails even if the numeral survives elsewhere;
  #   count   -- the total occurrences must match the pin, so corrupting ANY
  #              occurrence fails even one this script does not name.
  foreach ($entry in $c.surfaces) {
    $s = $entry.path
    $p = Join-Path $repoRoot $s
    if (-not (Test-Path -LiteralPath $p)) { Fail "surface missing: $s"; continue }
    $text = [System.IO.File]::ReadAllText($p)

    foreach ($problem in @(Get-SurfaceFailures -Text $text -Entry $entry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $s)) {
      Fail $problem
    }
  }
  if ($failures -eq 0) {
    Info ("{0}: Lean proves {1}; all {2} listed surfaces agree" -f $c.name, $actual, $c.surfaces.Count)
  }
}

if ($SelfTest) {
  Info '--- self-test: can this guard actually fail? ---'
  $stf = 0
  $selfTestIds = @{}
  function ST([string]$n, [bool]$ok) {
    if ($script:selfTestIds.ContainsKey($n)) { $ok = $false }
    $script:selfTestIds[$n] = $true
    if ($ok) { Info "  SELFTEST PASS $n" } else { Write-Host "CONST-SYNC: SELFTEST FAIL $n"; $script:stf = $script:stf + 1 }
  }
  # Independent consumer roster: deleting a required surface must not delete
  # its own test silently. Keep this list separate from the production table.
  $expectedV1Surfaces = @(
    '210:docs/V1_GUIDE.md',
    '210:docs/V1_CLIENTS.md',
    '427:docs/V1_GUIDE.md',
    '837572:README.md',
    '837572:artifact/CLAIMS.md',
    '837572:docs/PAPER_THEOREM_MAP.md',
    '837572:docs/V1_GUIDE.md'
  )
  $observedV1Surfaces = @(
    foreach ($c in $constants) {
      foreach ($entry in $c.surfaces) {
        if ($c.expected -eq '837572' -or $entry.path -match '^docs/V1_') {
          $c.expected + ':' + $entry.path
        }
      }
    }
  )
  function Test-V1SurfaceRegistry([string[]]$Observed) {
    return $Observed.Count -eq 7 -and
      @($Observed | Group-Object | Where-Object Count -ne 1).Count -eq 0 -and
      ($Observed -join "`n") -ceq ($expectedV1Surfaces -join "`n")
  }
  ST 'v1-exact-new-surface-registry' (Test-V1SurfaceRegistry $observedV1Surfaces)
  ST 'v1-surface-deletion-control-rejected' `
    (-not (Test-V1SurfaceRegistry @($observedV1Surfaces | Where-Object { $_ -ne '837572:docs/V1_GUIDE.md' })))
  ST 'v1-surface-duplication-control-rejected' `
    (-not (Test-V1SurfaceRegistry @($observedV1Surfaces + '837572:docs/V1_GUIDE.md')))
  # extractor really reads Lean, and would see a changed value
  ST 'extracts 210 from Lean' ((Get-LeanValue $constants[0].leanFile $constants[0].leanPat) -eq '210')
  ST 'extracts 427 from Lean' ((Get-LeanValue $constants[1].leanFile $constants[1].leanPat) -eq '427')
  ST 'v1-budget-extracts-837572-from-capstone-budgetExact' `
    ((Get-LeanValue $constants[2].leanFile $constants[2].leanPat) -ceq '837572')
  # a changed Lean value must mismatch the pin
  $fake = [regex]::Match('concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 214', $constants[0].leanPat)
  ST 'a changed Lean value is detected' ($fake.Success -and $fake.Groups[1].Value -ne $constants[0].expected)
  # a bad anchor must be reported as blindness, not silently pass
  ST 'a moved anchor yields null rather than a false pass' ($null -eq (Get-LeanValue $constants[0].leanFile 'thisPatternMatchesNothing_(\d+)'))
  # retired value without a marker is drift; with a marker it is allowed
  ST 'retired value without a marker is drift' (('the current cap is 207' -notmatch $historicalMarker))
  ST 'retired value with a marker is allowed' (('Historical comparison: the retired cap is 207' -match $historicalMarker))

  # ------------------------------------------------------------------------
  # The three ways this guard has been, or could be, GREEN WHILE WRONG.
  #
  # These run fixtures through `Get-SurfaceFailures` -- the same function the
  # real check calls -- rather than re-deriving the logic. A self-test that
  # restates the check passes whenever its restatement is right, which is not
  # the property anyone wants verified.
  # ------------------------------------------------------------------------
  $fixtureEntry = @{ path = 'FIXTURE.md'; count = 3; anchors = @('at most\*\* `{VALUE}`') }
  function FixtureFailures([string]$text, [hashtable]$entry) {
    return @(Get-SurfaceFailures -Text $text -Entry $entry -Actual '210' `
        -Retired @('207') -ConstantName 'fixture' -SurfacePath 'FIXTURE.md')
  }

  # Control: a healthy surface must produce NO failures. Without this, a
  # function that always reports a failure would pass every case below.
  $healthy = "The bound is at most** ``210``.`nAlso ``210`` here.`nAnd ``210``.`n"
  ST 'control: a healthy fixture produces no failures' ((FixtureFailures $healthy $fixtureEntry).Count -eq 0)

  # (1) 2026-08-09 external audit: one of several occurrences corrupted, the
  #     rest intact. A file-wide presence test passed. The count pin catches it.
  $corrupted = "The bound is at most** ``210``.`nAlso ``210`` here.`nAnd ``999``.`n"
  ST 'one corrupted occurrence among several is caught (count pin)' `
    ((FixtureFailures $corrupted $fixtureEntry).Count -gt 0)

  # (2) NEW this round: a conflicting claim ADDED alongside the correct ones.
  #     Every `210` survives and the anchor is satisfied, so the anchor check
  #     and the count check both pass -- the surface asserts two incompatible
  #     bounds and the guard is green. Only the claim-shape scan catches it.
  $conflicting = "The bound is at most** ``210``.`nRevised: at most** ``214``.`nAlso ``210``.`nAnd ``210``.`n"
  $conflictEntry = @{ path = 'FIXTURE.md'; count = 3; anchors = @('at most\*\* `{VALUE}`') }
  $conflictFailures = FixtureFailures $conflicting $conflictEntry
  ST 'a conflicting numeral added alongside the correct one is caught' `
    (($conflictFailures | Where-Object { $_ -match 'CONFLICTING' }).Count -gt 0)
  # ...and specifically NOT because the count or anchor moved: prove the two
  # older conditions are both satisfied, so the new one is doing the work.
  ST 'the conflicting case defeats BOTH older conditions (count and anchor hold)' `
    (($conflictFailures | Where-Object { $_ -notmatch 'CONFLICTING' }).Count -eq 0)

  # (3) A historical restatement of a superseded value must still be allowed,
  #     or the conflict scan would make every changelog entry a failure.
  $historical = "The bound is at most** ``210``.`nFormerly the cap was at most** ``207``.`nAlso ``210``.`nAnd ``210``.`n"
  ST 'a historical restatement is not reported as a conflict' `
    ((FixtureFailures $historical $fixtureEntry | Where-Object { $_ -match 'CONFLICTING' }).Count -eq 0)
  # (4) The marker must be ATTACHED to the numeral it excuses. `$pad` puts the
  #     word `previously` well outside reach of the conflicting `214`, on the
  #     same line -- the shape of a wide acceptance-matrix row. Before the
  #     proximity rule this fixture produced no CONFLICTING failure at all.
  $pad = ' filler' * 40
  $farMarker = "The bound is at most** ``210``.`nRevised: at most** ``214``.$pad previously discussed.`nAlso ``210``.`nAnd ``210``.`n"
  ST 'a marker far from the numeral does NOT excuse it' `
    ((FixtureFailures $farMarker $fixtureEntry | Where-Object { $_ -match 'CONFLICTING' }).Count -gt 0)

  # ...and the near case still passes, so (4) is proximity and not a blanket
  #    removal of the exemption. Same word, same numeral, same line.
  $nearMarker = "The bound is at most** ``210``.`nPreviously: at most** ``214``.$pad`nAlso ``210``.`nAnd ``210``.`n"
  ST 'a marker beside the numeral still excuses it' `
    ((FixtureFailures $nearMarker $fixtureEntry | Where-Object { $_ -match 'CONFLICTING' }).Count -eq 0)

  # (5) Same rule on the retired-value scan, which had the same whole-line test.
  $farRetired = "The bound is at most** ``210``.`nThe cap is 207.$pad previously.`nAlso ``210``.`nAnd ``210``.`n"
  ST 'a far marker does NOT excuse a superseded value either' `
    ((FixtureFailures $farRetired $fixtureEntry | Where-Object { $_ -match 'superseded value' }).Count -gt 0)

  # New surfaces and format mutations use the production extraction and
  # Get-SurfaceFailures predicate above. No fixture writes source or prose.
  foreach ($c in $constants) {
    $actual = Get-LeanValue $c.leanFile $c.leanPat
    foreach ($entry in $c.surfaces) {
      if ($c.expected -ne '837572' -and $entry.path -notmatch '^docs/V1_') { continue }
      $surfaceText = [System.IO.File]::ReadAllText((Join-Path $repoRoot $entry.path))
      $caseId = 'v1-' + $c.expected + '-' + ($entry.path -replace '[^A-Za-z0-9]', '-')
      $intactFailures = @(Get-SurfaceFailures -Text $surfaceText -Entry $entry -Actual $actual `
        -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
      ST "$caseId-intact-accepted" ($intactFailures.Count -eq 0)

      if ($c.expected -ne '837572') {
        # Swapping trace and probe values must fail in the guide's own shape.
        $otherModel = if ($c.expected -eq '210') { '427' } else { '210' }
        $wrongModel = [regex]::Replace($surfaceText, (Get-ValuePattern $actual), $otherModel)
        $wrongModelFailures = @(Get-SurfaceFailures -Text $wrongModel -Entry $entry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-other-model-rejected" `
          (@($wrongModelFailures | Where-Object { $_ -match 'CONFLICTING' }).Count -gt 0)
        continue
      }

      foreach ($format in @('837572', '837,572')) {
        $formatted = [regex]::Replace($surfaceText, (Get-ValuePattern $actual), $format)
        $formatFailures = @(Get-SurfaceFailures -Text $formatted -Entry $entry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-format-$format-accepted" ($formatFailures.Count -eq 0)

        # Repeat one actual claim to give even the one-occurrence guide two
        # legitimate budget occurrences; pin its new multiplicity explicitly.
        $claim = [regex]::Match($formatted, $entry.anchors[0].Replace('{VALUE}', (Get-ValuePattern $actual)))
        $repeatedEntry = $entry.Clone()
        $repeatedEntry.count = $entry.count + 1
        $repeated = $formatted + "`n" + $claim.Value + "`n"
        $repeatedFailures = @(Get-SurfaceFailures -Text $repeated -Entry $repeatedEntry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-format-$format-repeat-control-accepted" ($claim.Success -and $repeatedFailures.Count -eq 0)
        $mutator = [regex](Get-ValuePattern $actual)
        $wrong = if ($format -eq '837572') { '837573' } else { '837,573' }
        $mutated = $mutator.Replace($repeated, $wrong, 1)
        $mutationFailures = @(Get-SurfaceFailures -Text $mutated -Entry $repeatedEntry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-format-$format-one-of-several-rejected" `
          ($mutator.IsMatch($mutated) -and @($mutationFailures | Where-Object { $_ -match 'pinned at' }).Count -gt 0)

        # Every correct occurrence and anchor remains intact. Only the
        # production claim-shape conflict check can reject this addition.
        $conflictingClaim = $mutator.Replace($claim.Value, $wrong)
        $addedConflict = $formatted + "`n" + $conflictingClaim + "`n"
        $addedFailures = @(Get-SurfaceFailures -Text $addedConflict -Entry $entry -Actual $actual `
          -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-format-$format-added-conflict-rejected" `
          (@($addedFailures | Where-Object { $_ -match 'CONFLICTING' }).Count -gt 0 -and
           @($addedFailures | Where-Object { $_ -notmatch 'CONFLICTING' }).Count -eq 0)
      }

      # Unrelated model constants and larger numerals are not this budget.
      $unrelated = $surfaceText + "`nOther quantities: 210, 427, 837, 572, 1,837,572, 8375720, 837,210, 837,427.`n"
      $unrelatedFailures = @(Get-SurfaceFailures -Text $unrelated -Entry $entry -Actual $actual `
        -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
      ST "$caseId-unrelated-numerals-accepted" ($unrelatedFailures.Count -eq 0)
      foreach ($wrongToken in @('837', '572', '210', '427', '83,7572', '837,5720')) {
        $wrongClaim = [regex]::Replace($claim.Value, (Get-ValuePattern $actual), $wrongToken)
        $tokenFailures = @(Get-SurfaceFailures -Text ($surfaceText + "`n" + $wrongClaim) `
          -Entry $entry -Actual $actual -Retired $c.retired -ConstantName $c.name -SurfacePath $entry.path)
        ST "$caseId-wrong-token-$wrongToken-rejected" `
          (@($tokenFailures | Where-Object { $_ -match 'CONFLICTING' }).Count -gt 0)
      }
    }
  }

  if ($stf -gt 0) { $failures = $failures + $stf }
  else { Info 'self-test: all cases pass' }
}

if ($failures -gt 0) {
  Write-Host ("CONST-SYNC: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host 'CONST-SYNC: RESULT: PASS'
exit 0

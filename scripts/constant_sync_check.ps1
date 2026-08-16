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

# The two current constants. `expected` is the pin: it must be updated in the
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
    surfaces = @(
      @{ path = 'README.md';                          count = 9;  anchors = @('charged-trace cap is `{VALUE}`') },
      @{ path = 'artifact/CLAIMS.md';                 count = 10; anchors = @('at most\*\* `{VALUE}`') },
      @{ path = 'docs/WHAT_IS_PROVED.md';             count = 9;  anchors = @('charged-trace bound is `{VALUE}`') },
      # 11 -> 13 on 2026-08-12: the execution-cost sentence was corrected from
      # "is exactly `210`" to a budget-plus-inequality statement, which names
      # the constant twice more.  The pin moved in the same edit, as this check
      # demands.  Note what that does and does not show: the count moving
      # proves the change was deliberate, not that the new wording is right.
      # This check reads numerals, never the relation around them, so it would
      # have passed "exactly 210" forever.
      @{ path = 'docs/PAPER_THEOREM_MAP.md';          count = 13; anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace \*\*budget\*\* is `{VALUE}`', 'literal bound `{VALUE}`') },
      @{ path = 'docs/PAPER_CLAIM_CORRESPONDENCE.md'; count = 11; anchors = @('at most\*\* `{VALUE}`') },
      @{ path = 'docs/TRUST_AUDIT_PACKET.md';         count = 7;  anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace cost at most `{VALUE}`') },
      @{ path = 'docs/FAMILY_SUMMARY.md';             count = 7;  anchors = @('`{VALUE}`');
         claimShapes = @('charged-trace constant `{VALUE}`') }
    )
  },
  @{
    name     = 'derived packed probe cap'
    expected = '427'
    leanFile = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean'
    leanPat  = 'derived_cap_le_(\d+)'
    retired  = @()
    surfaces = @(
      @{ path = 'docs/PAPER_THEOREM_MAP.md';          count = 5;
         anchors = @('at most `{VALUE}` attempted aligned', 'derived_cap_le_{VALUE}',
                     '`{VALUE}` is an \*\*upper bound') },
      @{ path = 'docs/PAPER_CLAIM_CORRESPONDENCE.md'; count = 5;
         anchors = @('at most `{VALUE}` attempted aligned', 'derived numeral `{VALUE}`',
                     '`{VALUE}` is an upper bound') }
    )
  }
)

# A retired numeral is allowed on a line that marks itself historical. This
# mirrors the claim-drift policy's own exculpating vocabulary rather than
# inventing a second one.
$historicalMarker = 'historical|Historical|retired|Retired|superseded|Superseded|formerly|previously|was\b|CLAIM-HISTORY'

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

  foreach ($anchor in $Entry.anchors) {
    $pat = $anchor -replace '\{VALUE\}', [regex]::Escape($Actual)
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
    $shape = $shapeSpec -replace '\{VALUE\}', '(\d+)'
    foreach ($hit in [regex]::Matches($Text, $shape)) {
      if ($hit.Groups[1].Value -eq $Actual) { continue }
      # A historical line may legitimately restate a superseded value.
      $lineStart = $Text.LastIndexOf("`n", [Math]::Max(0, [Math]::Min($hit.Index, $Text.Length - 1))) + 1
      $lineEnd = $Text.IndexOf("`n", $hit.Index)
      if ($lineEnd -lt 0) { $lineEnd = $Text.Length }
      $line = $Text.Substring($lineStart, $lineEnd - $lineStart)
      if ($line -match $historicalMarker) { continue }
      $out += ("{0}: {1} states a CONFLICTING value {2} in a current claim (shape /{3}/); the proved value is {4}: {5}" -f `
        $ConstantName, $SurfacePath, $hit.Groups[1].Value, $shapeSpec, $Actual, $line.Trim())
    }
  }

  $occ = ([regex]::Matches($Text, '(?<![0-9])' + [regex]::Escape($Actual) + '(?![0-9])')).Count
  if ($occ -ne $Entry.count) {
    $out += ("{0}: {1} states {2} {3} time(s), pinned at {4}. If the surface genuinely changed, update the pin in the same edit." -f $ConstantName, $SurfacePath, $Actual, $occ, $Entry.count)
  }

  foreach ($r in $Retired) {
    foreach ($line in ($Text -split "`r?`n")) {
      if ($line -match ('\b' + [regex]::Escape($r) + '\b') -and $line -notmatch $historicalMarker) {
        $out += ("{0}: {1} states superseded value {2} without a historical marker: {3}" -f $ConstantName, $SurfacePath, $r, $line.Trim().Substring(0, [Math]::Min(90, $line.Trim().Length)))
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
  function ST([string]$n, [bool]$ok) {
    if ($ok) { Info "  SELFTEST PASS $n" } else { Write-Host "CONST-SYNC: SELFTEST FAIL $n"; $script:stf = $script:stf + 1 }
  }
  # extractor really reads Lean, and would see a changed value
  ST 'extracts 210 from Lean' ((Get-LeanValue $constants[0].leanFile $constants[0].leanPat) -eq '210')
  ST 'extracts 427 from Lean' ((Get-LeanValue $constants[1].leanFile $constants[1].leanPat) -eq '427')
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
  if ($stf -gt 0) { $failures = $failures + $stf }
  else { Info 'self-test: all cases pass' }
}

if ($failures -gt 0) {
  Write-Host ("CONST-SYNC: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host 'CONST-SYNC: RESULT: PASS'
exit 0

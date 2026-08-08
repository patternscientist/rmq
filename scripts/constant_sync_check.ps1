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
    surfaces = @('README.md', 'artifact/CLAIMS.md', 'docs/WHAT_IS_PROVED.md',
                 'docs/PAPER_THEOREM_MAP.md', 'docs/PAPER_CLAIM_CORRESPONDENCE.md',
                 'docs/TRUST_AUDIT_PACKET.md', 'docs/FAMILY_SUMMARY.md')
  },
  @{
    name     = 'derived packed probe cap'
    expected = '427'
    leanFile = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean'
    leanPat  = 'derived_cap_le_(\d+)'
    retired  = @()
    surfaces = @('docs/PAPER_THEOREM_MAP.md', 'docs/PAPER_CLAIM_CORRESPONDENCE.md')
  }
)

# A retired numeral is allowed on a line that marks itself historical. This
# mirrors the claim-drift policy's own exculpating vocabulary rather than
# inventing a second one.
$historicalMarker = 'historical|Historical|retired|Retired|superseded|Superseded|formerly|previously|was\b|CLAIM-HISTORY'

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

  # every listed surface must state the current value
  foreach ($s in $c.surfaces) {
    $p = Join-Path $repoRoot $s
    if (-not (Test-Path -LiteralPath $p)) { Fail "surface missing: $s"; continue }
    $text = [System.IO.File]::ReadAllText($p)
    if ($text -notmatch [regex]::Escape($actual)) {
      Fail ("{0}: {1} does not state the current value {2}" -f $c.name, $s, $actual)
    }
    # a superseded value in a current-claim context is drift
    foreach ($r in $c.retired) {
      foreach ($line in ($text -split "`r?`n")) {
        if ($line -match ('\b' + [regex]::Escape($r) + '\b') -and $line -notmatch $historicalMarker) {
          Fail ("{0}: {1} states superseded value {2} without a historical marker: {3}" -f $c.name, $s, $r, $line.Trim().Substring(0, [Math]::Min(90, $line.Trim().Length)))
        }
      }
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
  if ($stf -gt 0) { $failures = $failures + $stf }
  else { Info 'self-test: all cases pass' }
}

if ($failures -gt 0) {
  Write-Host ("CONST-SYNC: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host 'CONST-SYNC: RESULT: PASS'
exit 0

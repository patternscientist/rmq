#!/usr/bin/env pwsh
#
# Audit-tag annotations carry IDENTITY AND SCOPE ONLY -- never a verdict.
#
# WHY THIS EXISTS. A fresh-blind auditor is commissioned with a tag, and
# `docs/internal/V1_RELEASE_CANDIDATE_AUDIT_PROMPT.md` tells them to
# `git checkout <tag>` and to confirm `git tag --points-at HEAD`. The tag name
# is therefore in front of them by construction, and `git show <tag>` or
# `git tag -n99` prints its annotation.
#
# The `audit-v1-rc-3` annotation contained a full prior-round summary: the
# previous verdict (`NOT_ACCEPTABLE`), the finding IDs (`P1-01` ... `P1-03`),
# which requirements were discharged, and the claim that every prior finding
# had been reproduced and none were wrong. An auditor who is told what the last
# auditor found, and that those findings were all correct, is no longer blind.
# This was predicted before the RC-3 audit was commissioned and it happened.
#
# The annotation is not a place to be proud of the round. It answers exactly
# two questions: which commit is this, and what is in scope.
#
# ALREADY-PUBLISHED TAGS. `audit-v1-rc-2` and `audit-v1-rc-3` are on `origin`
# and were handed to auditors. They are NOT rewritten here: rewriting a
# published tag breaks a reference an auditor may already hold, and the
# contamination they caused has already happened. They are listed below with
# that reason. The list is frozen and pinned by count -- a NEW contaminated tag
# fails this check, and the list cannot absorb it silently.
#
# Run with -SelfTest to verify the detector fires on the real `audit-v1-rc-3`
# annotation and stays quiet on a clean one.

[CmdletBinding()]
param(
  [switch]$SelfTest,
  # Accept a run in which no annotated tag matched. For clones that cannot fetch
  # tags; CI must not pass it.
  [switch]$AllowNoTags,
  [string]$Pattern = "audit-*"
)

$ErrorActionPreference = "Stop"
$failures = 0

function Fail([string]$m) { Write-Host "TAG-ANNOTATION: FAIL: $m"; $script:failures = $script:failures + 1 }
function Info([string]$m) { Write-Host "TAG-ANNOTATION: $m" }

# Verdicts, finding identifiers and requirement IDs. Each is a thing a NEXT
# auditor must not be handed. Deliberately narrow: an annotation may say what
# is in scope ("V1 release candidate 4, for fresh-blind external audit")
# without tripping any of these.
$forbidden = @(
  @{ id = 'verdict';      pattern = 'NOT_ACCEPTABLE|\bACCEPTABLE\b|MERGE[ _-]?READY|\bACCEPTED\b|\bREJECTED\b' },
  @{ id = 'finding-id';   pattern = '\bP[1-3]-\d' },
  @{ id = 'requirement';  pattern = '\bRC-\d' },
  @{ id = 'audit-round';  pattern = '\bAUD\d' },
  @{ id = 'outcome-prose'; pattern = 'every finding|none were wrong|were wrong|was wrong|returned NOT|discharged' }
)

# Frozen: published before this convention existed. See the header.
$publishedContaminated = @('audit-v1-rc-2', 'audit-v1-rc-3')
$publishedContaminatedCount = 2

function Get-AnnotatedTags {
  param([string]$Glob)
  # Only ANNOTATED tags have an annotation. A lightweight tag's `%(contents)`
  # is the commit message, which would be a false positive.
  $rows = @(& git for-each-ref --format='%(objecttype)|%(refname:short)' ("refs/tags/" + $Glob) 2>$null)
  return @($rows | Where-Object { $_ -like 'tag|*' } | ForEach-Object { ($_ -split '\|', 2)[1] })
}

function Get-TagAnnotation {
  param([string]$Tag)
  return (& git for-each-ref --format='%(contents)' ("refs/tags/" + $Tag) 2>$null) -join "`n"
}

function Get-AnnotationViolations {
  param([string]$Text)
  $hits = @()
  foreach ($rule in $forbidden) {
    $m = [regex]::Match($Text, $rule.pattern)
    if ($m.Success) { $hits += ("{0} ('{1}')" -f $rule.id, $m.Value) }
  }
  return $hits
}

if ($SelfTest) {
  Info '--- self-test: does the detector fire? ---'
  $stf = 0
  function ST([string]$n, [bool]$ok) {
    if ($ok) { Info "  SELFTEST PASS $n" } else { Write-Host "TAG-ANNOTATION: SELFTEST FAIL $n"; $script:stf = $script:stf + 1 }
  }

  # Positive fixture: the REAL contaminated annotation, not a synthetic one. If
  # the detector cannot catch the annotation that actually leaked, it is not a
  # detector for this problem.
  $realContaminated = Get-TagAnnotation 'audit-v1-rc-3'
  if ([string]::IsNullOrWhiteSpace($realContaminated)) {
    ST 'the audit-v1-rc-3 annotation is readable (fixture present)' $false
  } else {
    ST 'the audit-v1-rc-3 annotation is readable (fixture present)' $true
    $realHits = Get-AnnotationViolations $realContaminated
    ST 'the real contaminated annotation is caught' ($realHits.Count -gt 0)
    ST 'it is caught for a VERDICT, not merely incidentally' `
      (($realHits | Where-Object { $_ -like 'verdict*' }).Count -gt 0)
    ST 'it is caught for FINDING IDs too' `
      (($realHits | Where-Object { $_ -like 'finding-id*' }).Count -gt 0)
  }

  # Negative fixture: a compliant annotation must stay silent, or the rule is
  # unusable and would be turned off.
  $clean = @"
V1 release candidate 4, for fresh-blind external audit.

Scope: the full repository at this commit -- Lean sources, scripts, docs and
the paper/ substrate. Build with `lake build RMQ`. The audit prompt is
docs/internal/V1_RELEASE_CANDIDATE_AUDIT_PROMPT.md.
"@
  ST 'a clean identity/scope annotation is not flagged' ((Get-AnnotationViolations $clean).Count -eq 0)

  # The exception list must not be able to grow silently.
  ST 'the published-contaminated list matches its pinned count' `
    ($publishedContaminated.Count -eq $publishedContaminatedCount)

  if ($stf -gt 0) { $failures = $failures + $stf } else { Info 'self-test: all cases pass' }
}

# The exception-list count pin runs on EVERY invocation, not only under
# -SelfTest. `docs/internal/AUDIT_PROTOCOL.md` states unconditionally that the
# list "is pinned by count and cannot absorb a new tag silently"; a pin that
# only fires in a mode the standalone path does not use does not support that
# sentence.
if ($publishedContaminated.Count -ne $publishedContaminatedCount) {
  Fail ("the known-contaminated tag list holds {0} entries but is pinned at {1}; a tag was added or removed without updating the pin" -f `
    $publishedContaminated.Count, $publishedContaminatedCount)
}

$tags = @(Get-AnnotatedTags $Pattern)
if ($tags.Count -eq 0) {
  # Not a pass, and now the code agrees with that.
  #
  # This block previously printed the sentence below and then fell through to
  # RESULT: PASS, exit 0 -- a comment asserting the check must not pass silently,
  # sitting directly above the code that made it pass silently. A CI checkout
  # with `fetch-depth: 1` or `--no-tags` would have got a clean exit having
  # examined nothing. Found by audit.
  #
  # `-AllowNoTags` mirrors `-AllowInconclusive` in `owned_process_tree.ps1`: it
  # exists for environments that genuinely cannot fetch tags, and CI must not
  # pass it.
  Info "no annotated tags match '$Pattern' (nothing checked -- tags may not be present in this clone)"
  if (-not $AllowNoTags) {
    Write-Host "TAG-ANNOTATION: RESULT: FAIL (nothing was checked; fetch tags, or pass -AllowNoTags to accept that)"
    exit 1
  }
  Info "-AllowNoTags was passed; accepting a run that checked nothing"
} else {
  foreach ($tag in $tags) {
    $annotation = Get-TagAnnotation $tag
    $hits = @(Get-AnnotationViolations $annotation)
    if ($hits.Count -eq 0) {
      Info "$tag : identity/scope only"
      continue
    }
    if ($publishedContaminated -ccontains $tag) {
      Info ("$tag : KNOWN-CONTAMINATED, published before this convention -- {0}" -f ($hits -join '; '))
      Info "         not rewritten (published to origin and already handed to auditors); do not reuse for commissioning"
      continue
    }
    Fail ("$tag annotation carries audit outcome, which contaminates the next blind auditor: {0}" -f ($hits -join '; '))
    Fail "         an audit-tag annotation states identity and scope only"
  }
}

if ($failures -gt 0) {
  Write-Host ("TAG-ANNOTATION: RESULT: FAIL ({0} failure(s))" -f $failures)
  exit 1
}
Write-Host 'TAG-ANNOTATION: RESULT: PASS'
exit 0

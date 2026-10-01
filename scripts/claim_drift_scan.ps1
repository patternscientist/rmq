#!/usr/bin/env pwsh

[CmdletBinding()]
param(
  [switch]$Strict,
  # Print `allowed` hits too. Off by default since 2026-08-16: printing every
  # match leaked prior audit reports to a commissioned blind auditor. See the
  # emission site below.
  [switch]$ShowAllowed,
  # Scan process records (audit reports, worklogs) too. Excluded by default
  # since 2026-08-16: they leaked prior verdicts to a blind auditor. See
  # Get-ScanFiles below.
  [switch]$IncludeProcessRecords,
  # Verify the process-record exclusion actually excludes. See below.
  [switch]$SelfTest,
  [string]$PolicyPath = "docs/internal/CLAIM_DRIFT_POLICY.json",
  # `paper` since 2026-08-16. It was absent, so the manuscript, the novelty log,
  # the theorem ledger and the evidence matrix -- the most public claim surfaces
  # in the release candidate -- were outside the scan the aggregate gate
  # advertises over it. Adding the root produced seven strict failures on the
  # first run, all in lines that PROHIBIT the phrase they contain; the policy
  # allowances for those two terms were widened in the same change, and the
  # allowance is keyed to the prohibiting language AND the path, as an
  # allowedPathLine pair (policy v25). It was language-only at v24, which made it
  # repo-wide -- broader than the path allowance it was chosen over.
  [string[]]$Path = @("README.md", "artifact", "docs", "paper")
)

$ErrorActionPreference = "Continue"

# Self-test for the process-record exclusion.
#
# Written because the first two attempts at that exclusion were both no-ops and
# both looked exactly like success. Attempt one suppressed `allowed` labels, but
# the leaking hits are labelled `review`. Attempt two filtered Get-ScanFiles with
# `-like "*\\audit_reports\\*"`, where the backslash is not an escape character,
# so it matched nothing -- AND Get-ScanFiles only feeds the required-attribution
# pass anyway, while the leak comes from the term scan, which hands the roots to
# `rg` and never calls that function. A no-op filter and a working filter produce
# the same exit code, so only a measurement distinguishes them.
#
# Assertion 2 is the one that matters: it fails if the exclusion removes nothing.
if ($SelfTest) {
  $hostExe = if ($PSVersionTable.PSEdition -eq "Core") { "pwsh" } else { "powershell" }
  $selfPath = $PSCommandPath
  $selfTestFailures = 0

  $defaultRun = @(& $hostExe -NoProfile -ExecutionPolicy Bypass -File $selfPath -Strict 2>&1 |
    ForEach-Object { [string]$_ })
  $recordRun = @(& $hostExe -NoProfile -ExecutionPolicy Bypass -File $selfPath -Strict -IncludeProcessRecords 2>&1 |
    ForEach-Object { [string]$_ })

  # (0) BEHAVIOURAL pin on the protected claim classes.
  #
  # The policy-term regression drives its cases from the policy file, so DELETING
  # a term deletes its own coverage -- measured 2026-09-08: removing
  # `forbidden-wordram-instruction-count` left the regression and this self-test
  # at exit 0, and the bare README claim then passed -Strict with 0 strict
  # failures. These probes assert the production DECISION on fixed text instead:
  # some strict term must match, and no allowance may excuse it. A deleted term,
  # a weakened pattern, or a widened allowance each make a probe stop being
  # rejected, and that fails here.
  #
  # Policy v28 adds the PQ1 primitive-instruction classes. An 837,572 or
  # "fully charged" paragraph that names no PQ1 theorem must be rejected, and
  # so must the same words attached to a 210 trace or 427 probe theorem name
  # even when the PQ1 alias is present -- the fifth probe below is excused by
  # the attribution term and can only be rejected by the attachment term.
  $protectedClaimProbes = @(
    'The canonical query executes in 210 word-RAM instructions.',
    'The canonical query runs in a fixed number of word-RAM instructions.',
    'This is not merely a modeled bound: the canonical query executes in 210 word-RAM instructions.',
    'The packed primitive query halts within at most 837,572 instructions.',
    'RMQ.Headlines.succinctRMQPackedCellProbeArchitecture is fully charged; see RMQ.Headlines.succinctRMQFullyChargedPackedQuery.',
    'The canonical reviewer route is fully charged.'
  )
  # The other half of the same decision: attributed PQ1 sentences, including
  # one that contrasts the 210 and 427 numerals, must stay accepted. A term
  # widened to reject them, or an attribution allowance that stopped firing,
  # makes one of these fail.
  $acceptedClaimProbes = @(
    'RMQ.Headlines.succinctRMQFullyChargedPackedQuery proves that the packed primitive run halts within at most 837,572 instructions.',
    'RMQ.Headlines.succinctRMQFullyChargedPackedQuery bounds its own packed run by at most 837,572 primitive instructions; the 210 trace and 427 probe bounds are separate quantities.'
  )
  $probePolicy = Get-Content -Raw -Path $PolicyPath | ConvertFrom-Json
  function Test-ProbeRejected([string]$ProbeText) {
    $rejected = $false
    foreach ($t in $probePolicy.terms) {
      if (-not $t.strict) { continue }
      if ([string]$t.pattern -eq '') { continue }
      if ($ProbeText -notmatch [string]$t.pattern) { continue }
      # README.md is a governed current-fact surface and matches no allowedPathRegex
      # of this term, so only the LINE allowance can excuse the probe.
      if ($t.allowedLineRegex -and $ProbeText -match [string]$t.allowedLineRegex) { continue }
      $rejected = $true
    }
    return $rejected
  }
  foreach ($probeText in $protectedClaimProbes) {
    if (-not (Test-ProbeRejected $probeText)) {
      Write-Host ("CLAIM-DRIFT SELFTEST: FAIL -- protected claim class is no longer rejected: {0}" -f $probeText)
      $selfTestFailures += 1
    }
  }
  foreach ($probeText in $acceptedClaimProbes) {
    if (Test-ProbeRejected $probeText) {
      Write-Host ("CLAIM-DRIFT SELFTEST: FAIL -- accurate attributed claim is now rejected: {0}" -f $probeText)
      $selfTestFailures += 1
    }
  }
  if ($selfTestFailures -eq 0) {
    Write-Host ("CLAIM-DRIFT SELFTEST: ok -- {0} protected probes rejected and {1} attributed probes accepted" -f `
        $protectedClaimProbes.Count, $acceptedClaimProbes.Count)
  }

  # (1) No emitted finding may CITE a process-record path.
  #
  # Match the path field specifically, not the whole line: governed documents
  # legitimately mention "E1_WORKLOG.md" in their prose, and a whole-line grep
  # reports those as leaks.
  $leaked = @()
  foreach ($emitted in $defaultRun) {
    if ($emitted -match '^CLAIM-DRIFT\[[^\]]*\]\[[^\]]*\]\[[^\]]*\] (.+?):[0-9]+: ') {
      $citedPath = $Matches[1]
      if ($citedPath -match '[\\/]audit_reports[\\/]' -or $citedPath -match 'WORKLOG\.md$') {
        $leaked += $citedPath
      }
    }
  }
  if ($leaked.Count -gt 0) {
    Write-Host ("CLAIM-DRIFT SELFTEST: FAIL -- {0} emitted line(s) cite process records, e.g. {1}" -f `
        $leaked.Count, $leaked[0])
    $selfTestFailures += 1
  } else {
    Write-Host "CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path"
  }

  # (2) The exclusion must actually remove something.
  function Get-ReportedHitCount {
    param([string[]]$Lines)
    foreach ($reported in $Lines) {
      if ($reported -match 'scan complete \(([0-9]+) hits') { return [int]$Matches[1] }
    }
    return -1
  }
  $defaultHits = Get-ReportedHitCount -Lines $defaultRun
  $recordHits = Get-ReportedHitCount -Lines $recordRun
  if ($defaultHits -lt 0 -or $recordHits -lt 0) {
    Write-Host "CLAIM-DRIFT SELFTEST: FAIL -- could not read a hit count from both runs"
    $selfTestFailures += 1
  } elseif ($recordHits -le $defaultHits) {
    Write-Host ("CLAIM-DRIFT SELFTEST: FAIL -- exclusion removed nothing ({0} hits with records, {1} without); a filter that matches nothing looks identical to one that works" -f `
        $recordHits, $defaultHits)
    $selfTestFailures += 1
  } else {
    Write-Host ("CLAIM-DRIFT SELFTEST: ok -- exclusion removed {0} hits ({1} -> {2})" -f `
        ($recordHits - $defaultHits), $recordHits, $defaultHits)
  }

  if ($selfTestFailures -gt 0) {
    Write-Host "CLAIM-DRIFT SELFTEST: RESULT: FAIL"
    exit 1
  }
  Write-Host "CLAIM-DRIFT SELFTEST: RESULT: PASS"
  exit 0
}

if (-not (Test-Path $PolicyPath)) {
  Write-Host "CLAIM-DRIFT: policy not found: $PolicyPath"
  exit 1
}

$policy = Get-Content -Raw -Path $PolicyPath | ConvertFrom-Json
$currentFactSurfacePathRegex = [string]$policy.currentFactSurfacePathRegex
foreach ($term in @($policy.terms)) {
  $scope = [string]$term.scope
  if ([string]::IsNullOrWhiteSpace($scope)) {
    continue
  }
  if ($scope -ne "current-fact-surface") {
    Write-Host "CLAIM-DRIFT: unknown term scope '$scope' for $($term.id)"
    exit 1
  }
  if ([string]::IsNullOrWhiteSpace($currentFactSurfacePathRegex)) {
    Write-Host "CLAIM-DRIFT: current-fact-surface scope requires currentFactSurfacePathRegex"
    exit 1
  }
}
foreach ($attribution in @($policy.requiredAttributions)) {
  foreach ($field in @("id", "pathRegex", "claimPattern", "requiredPattern", "status")) {
    if ([string]::IsNullOrWhiteSpace([string]$attribution.$field)) {
      Write-Host "CLAIM-DRIFT: required attribution is missing '$field'"
      exit 1
    }
  }
  try {
    $null = [regex]::new([string]$attribution.pathRegex)
    $null = [regex]::new([string]$attribution.claimPattern)
    $null = [regex]::new([string]$attribution.requiredPattern)
  } catch {
    Write-Host "CLAIM-DRIFT: invalid required-attribution regex for $($attribution.id): $($_.Exception.Message)"
    exit 1
  }
}
# A requested root that does not exist means the scan covered less than it was
# asked to. Reporting success for that is how a scan of nothing looks identical
# to a scan that found nothing. External audit 2026-08-09 pointed a strict run at
# a missing path and got exit 0.
$missingRoots = @($Path | Where-Object { -not (Test-Path $_) })
$roots = @($Path | Where-Object { Test-Path $_ })

foreach ($mr in $missingRoots) {
  Write-Host "CLAIM-DRIFT: requested scan root does not exist: $mr"
}
if ($Strict -and $missingRoots.Count -gt 0) {
  Write-Host ("CLAIM-DRIFT: RESULT: FAIL ({0} requested scan root(s) missing; the scan did not cover what it was asked to)" -f $missingRoots.Count)
  exit 1
}

if ($roots.Count -eq 0) {
  Write-Host "CLAIM-DRIFT: no scan roots exist"
  if ($Strict) { Write-Host "CLAIM-DRIFT: RESULT: FAIL (nothing scanned)"; exit 1 }
  exit 0
}

$failures = 0
$hits = 0
$repositoryRoot = [System.IO.Path]::GetFullPath((Get-Location).Path)
$pathComparison = [System.StringComparison]::Ordinal
if ($env:OS -eq "Windows_NT") {
  $pathComparison = [System.StringComparison]::OrdinalIgnoreCase
}

function Get-RipgrepJsonText {
  param($Value)

  if ($null -ne $Value.text) {
    return [string]$Value.text
  }
  if ($null -ne $Value.bytes) {
    return [System.Text.Encoding]::UTF8.GetString(
      [System.Convert]::FromBase64String([string]$Value.bytes)
    )
  }
  return ""
}

function ConvertTo-PolicyPath {
  param([string]$RipgrepPath)

  try {
    if ([System.IO.Path]::IsPathRooted($RipgrepPath)) {
      $fullPath = [System.IO.Path]::GetFullPath($RipgrepPath)
    } else {
      $fullPath = [System.IO.Path]::GetFullPath(
        [System.IO.Path]::Combine($repositoryRoot, $RipgrepPath)
      )
    }

    $rootWithSeparator = $repositoryRoot.TrimEnd(
      [System.IO.Path]::DirectorySeparatorChar,
      [System.IO.Path]::AltDirectorySeparatorChar
    ) + [System.IO.Path]::DirectorySeparatorChar
    if ($fullPath.StartsWith($rootWithSeparator, $pathComparison)) {
      return ($fullPath.Substring($rootWithSeparator.Length) -replace "\\", "/")
    }
  } catch {
    # Preserve a usable policy/display path even for an unusual rg path.
  }

  return ($RipgrepPath -replace "\\", "/")
}

function Get-ScanFiles {
  $files = @()
  foreach ($root in $roots) {
    $item = Get-Item -LiteralPath $root -ErrorAction SilentlyContinue
    if ($null -eq $item) {
      continue
    }
    if ($item.PSIsContainer) {
      $files += @(Get-ChildItem -LiteralPath $item.FullName -Recurse -File)
    } else {
      $files += $item
    }
  }
  # Exclude PROCESS RECORDS from the default roots.
  #
  # Suppressing `allowed`-labelled output was not enough and fixing only that
  # was this repair's own first mistake: hits inside `docs/internal/audit_reports`
  # are frequently labelled `review`, not `allowed`, so 104 lines of prior audit
  # reports still printed after that change. The label is not the property; the
  # PATH is. These directories hold verdicts, findings and worklogs -- process
  # evidence that is never a governed claim surface, and precisely the material
  # a commissioned fresh-blind auditor must not be shown while forming
  # conclusions (2026-08-15 audit, P2-4).
  #
  # `-IncludeProcessRecords` restores them for coordinator use.
  # This covers the required-attribution pass ONLY. The term scan below does not
  # go through this function -- it shells out to `rg` against $roots directly --
  # so it carries its own copy of the exclusion via $processRecordExcludeGlobs.
  # Both are needed; fixing only this one changed nothing at all.
  if (-not $IncludeProcessRecords) {
    $files = @($files | Where-Object {
      $_.FullName -notmatch '[\\/]audit_reports[\\/]' -and
      $_.Name -notmatch 'WORKLOG\.md$'
    })
  }
  return @($files | Sort-Object FullName -Unique)
}

function Get-MatchLineNumber {
  param(
    [string]$Content,
    [int]$Index
  )

  if ($Index -le 0) {
    return 1
  }
  return 1 + ([regex]::Matches($Content.Substring(0, $Index), "`n")).Count
}

# Process-record exclusion for the TERM SCAN.
#
# The term scan does not enumerate files in PowerShell; it hands $roots to `rg`,
# which recurses them itself. So the exclusion has to be expressed as rg globs
# here, in addition to the PowerShell filter in Get-ScanFiles that covers the
# required-attribution pass. Two independent enumerations, two exclusions.
$processRecordExcludeGlobs = @()
if (-not $IncludeProcessRecords) {
  $processRecordExcludeGlobs = @(
    "--glob", "!**/audit_reports/**",
    "--glob", "!**/*WORKLOG.md"
  )
}

# Current-surface rules previously ran their multiline regex over every
# historical receipt and JSON inventory, only to mark those matches allowed.
# Enumerate with rg itself so ignore, hidden-file and explicit-path behavior is
# unchanged for the registered ASCII Markdown paths. -ShowAllowed retains the
# exhaustive diagnostic enumeration. Scoped terms cannot match process-record
# paths, so the self-test exclusion delta is now carried by non-scoped terms.
# make_audit_packet.ps1 archives the narrower default hit count; old packet
# totals therefore need not match on otherwise identical source.
$currentTermPaths = $null
foreach ($term in $policy.terms) {
  $termRoots = @($roots)
  if (-not $ShowAllowed -and [string]$term.scope -eq "current-fact-surface") {
    if ($null -eq $currentTermPaths) {
      $candidatePaths = @(& rg --files @processRecordExcludeGlobs -- @roots 2>$null)
      $enumerationExit = $LASTEXITCODE
      if ($enumerationExit -gt 1) {
        Write-Host "CLAIM-DRIFT: rg failed while enumerating current surfaces"
        exit $enumerationExit
      }
      $currentTermPaths = @($candidatePaths | Where-Object {
        (ConvertTo-PolicyPath $_) -match $currentFactSurfacePathRegex
      })
      Write-Host ("CLAIM-DRIFT: scoped terms scanned {0} of {1} enumerated files" -f $currentTermPaths.Count, $candidatePaths.Count)
      if ($currentTermPaths.Count -eq 0) {
        Write-Host "CLAIM-DRIFT: no current-fact surface under the requested roots; scoped terms scanned 0 files"
      }
    }
    $termRoots = @($currentTermPaths)
    # Passing no paths to rg would read stdin; there is no scoped input here.
    if ($termRoots.Count -eq 0) { continue }
  }
  $pattern = [string]$term.pattern
  $rgArguments = @("--json", "--pcre2")
  if ($term.multiline -eq $true) {
    $rgArguments += "--multiline"
  }
  $rgArguments += $processRecordExcludeGlobs
  $rgArguments += @("--", $pattern)
  $rgArguments += @($termRoots)
  $matches = @(& rg @rgArguments 2>$null)
  $code = $LASTEXITCODE
  if ($code -gt 1) {
    Write-Host "CLAIM-DRIFT: rg failed for $($term.id)"
    exit $code
  }

  foreach ($jsonLine in $matches) {
    try {
      $record = $jsonLine | ConvertFrom-Json -ErrorAction Stop
    } catch {
      Write-Host "CLAIM-DRIFT: invalid rg JSON for $($term.id)"
      exit 1
    }
    if ($record.type -ne "match") {
      continue
    }

    $file = Get-RipgrepJsonText $record.data.path
    $fileNorm = ConvertTo-PolicyPath $file
    $lineNo = [string]$record.data.line_number
    $line = Get-RipgrepJsonText $record.data.lines
    $policyLine = $line.TrimEnd([char[]]"`r`n")
    $hits += 1

    $allowed = $false
    if ([string]$term.scope -eq "current-fact-surface" -and
        $fileNorm -notmatch $currentFactSurfacePathRegex) {
      $allowed = $true
    }
    if ($term.allowedPathRegex -and $fileNorm -match [string]$term.allowedPathRegex) {
      $allowed = $true
    }
    if ($term.allowedLineRegex -and $policyLine -match [string]$term.allowedLineRegex) {
      $allowed = $true
    }
    if (
      $term.allowedPathLinePathRegex -and
      $term.allowedPathLineRegex -and
      $fileNorm -match [string]$term.allowedPathLinePathRegex -and
      $policyLine -match [string]$term.allowedPathLineRegex
    ) {
      $allowed = $true
    }
    if ($term.allowedPathLinePairs) {
      foreach ($pair in @($term.allowedPathLinePairs)) {
        if (
          $pair.pathRegex -and
          $pair.lineRegex -and
          $fileNorm -match [string]$pair.pathRegex -and
          $policyLine -match [string]$pair.lineRegex
        ) {
          $allowed = $true
          break
        }
      }
    }

    $label = "review"
    if ($allowed) {
      $label = "allowed"
    }

    if ($Strict -and ($term.strict -eq $true) -and -not $allowed) {
      $label = "fail"
      $failures += 1
    }

    # Emit `fail` and `review` always; emit `allowed` only when asked.
    #
    # Until 2026-08-16 every hit was printed, so a required strict run emitted
    # ~1,579 lines -- including PRIOR AUDIT REPORTS AND WORKLOGS, because the
    # default root recurses all of `docs`. A commissioned fresh-blind auditor ran
    # this gate before freezing conclusions and was involuntarily shown earlier
    # verdicts and findings: a contamination channel built into a required gate.
    # It fired on the 2026-08-15 audit (P2-4) after being identified in the
    # previous round and left unfixed -- a known leak left open is a leak chosen.
    #
    # `allowed` hits are by definition matches OUTSIDE the governed surfaces:
    # scan bookkeeping, not findings. `-ShowAllowed` restores the old output for
    # policy debugging, including out-of-scope matches of current-surface
    # rules. The summary counts matches in the inputs actually searched.
    if ($label -ne "allowed" -or $ShowAllowed) {
      Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f $term.id, $term.status, $label, $file, $lineNo, $line.Trim())
    }
  }
}

foreach ($attribution in @($policy.requiredAttributions)) {
  foreach ($fileItem in @(Get-ScanFiles)) {
    $fileNorm = ConvertTo-PolicyPath $fileItem.FullName
    if ($fileNorm -notmatch [string]$attribution.pathRegex) {
      continue
    }

    $content = Get-Content -Raw -LiteralPath $fileItem.FullName
    $claimMatch = [regex]::Match($content, [string]$attribution.claimPattern)
    if (-not $claimMatch.Success) {
      continue
    }

    $hits += 1
    $hasRequiredAttribution = [regex]::IsMatch(
      $content,
      [string]$attribution.requiredPattern
    )
    $label = if ($hasRequiredAttribution) { "allowed" } else { "review" }
    if ($Strict -and ($attribution.strict -eq $true) -and -not $hasRequiredAttribution) {
      $label = "fail"
      $failures += 1
    }
    $lineNo = Get-MatchLineNumber -Content $content -Index $claimMatch.Index
    $summary = if ($hasRequiredAttribution) {
      "strong claim has its required theorem identity"
    } else {
      "strong claim is missing required theorem identity"
    }
    Write-Host ("CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}" -f `
        $attribution.id, $attribution.status, $label, $fileNorm, $lineNo, $summary)
  }
}

if ($hits -eq 0) {
  Write-Host "CLAIM-DRIFT: no sensitive terms found"
}

if ($failures -gt 0) {
  Write-Host "CLAIM-DRIFT: strict mode found $failures unapproved sensitive matches"
  exit 1
}

Write-Host "CLAIM-DRIFT: scan complete ($hits hits, $failures strict failures)"
exit 0

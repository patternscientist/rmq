#!/usr/bin/env pwsh
#
# Verify every `:NNN` source citation in paper/THEOREM_LEDGER.md.
#
# Why this exists
# ---------------
# On 2026-08-09 the citations in this ledger were audited three times by ad-hoc
# grep and produced three different answers:
#
#   1. Nine citations, seven correct -- the sweep matched `:NNN` only on lines
#      that also carried a `` `....lean` `` path, and in this ledger the `File:`
#      line comes AFTER the `Declaration:` line, so 18 of 27 were invisible.
#   2. Twenty-seven, with three "past EOF" defects that did not exist -- the
#      sweep attributed each citation to the nearest PRECEDING `.lean` mention,
#      which points at the wrong file.
#   3. Twenty-seven with three real defects, found only by parsing rows.
#
# Two of those three answers were confidently wrong. Ad-hoc greps over a
# structured document are not verification; they are sampling with an unknown
# miss rate. `L-UB-06` cited a line ~1,090 lines from its theorem AT THE PINNED
# BASE COMMIT -- a pinned commit does not make a citation right, and the
# fresh-blind audit did not catch it either.
#
# What this checks
# ----------------
# Rows are parsed as units (`#### L-...`). For each row we collect every `.lean`
# path it names and every Lean identifier it names, then bind each citation to
# the most specific identifier its immediate context supports and require that
# identifier to appear ON the cited line (or inside the cited range).
#
# Binding strength is reported per citation, because a check is only as strong
# as what it pinned:
#
#   exact  -- context named one identifier; that identifier was required.
#   file   -- the citation follows a `.lean` path (the `- File:` shape). The
#             file is pinned exactly; the name must be one the row declares.
#   row    -- context named none; any identifier the row names was accepted.
#
# What this does NOT check: that the declaration is true, that it is the right
# declaration for the claim, or that it kernel-checks. This is a pointer
# integrity check over text. Theorem truth rests on Lean at the pinned commit.

[CmdletBinding()]
param(
  [string]$LedgerPath,
  [string]$RepositoryRoot,
  [switch]$SelfTest,
  # NOT -Verbose: that name collides with the CmdletBinding common parameter.
  [switch]$ShowAll
)

$ErrorActionPreference = "Stop"

function Resolve-Inputs {
  param([string]$Ledger, [string]$Root)

  $scriptDir = Split-Path -Parent $PSCommandPath
  if ([string]::IsNullOrWhiteSpace($Ledger)) {
    $Ledger = Join-Path $scriptDir "THEOREM_LEDGER.md"
  }
  if ([string]::IsNullOrWhiteSpace($Root)) {
    # The ledger's `File:` paths are repository-root relative. This script is
    # normally run from paper/, so the root is its parent.
    $Root = Split-Path -Parent $scriptDir
  }
  return @{ Ledger = $Ledger; Root = $Root }
}

function Test-IsLeanIdentifier {
  param([string]$Candidate)

  if ([string]::IsNullOrWhiteSpace($Candidate)) { return $false }
  if ($Candidate -match '\.lean$') { return $false }
  if ($Candidate -match '[/\\]') { return $false }
  return ($Candidate -match "^[A-Za-z_][A-Za-z0-9_.']*$")
}

function Get-NameLeaf {
  param([string]$FullName)
  $parts = $FullName -split '\.'
  return $parts[$parts.Length - 1]
}

# Parse the ledger into rows keyed by heading id.
function Get-LedgerRows {
  param([string]$Path)

  $lines = Get-Content -LiteralPath $Path
  $rows = @()
  $current = $null
  foreach ($line in $lines) {
    if ($line -match '^####\s+(L-[A-Za-z0-9-]+)\s*$') {
      if ($null -ne $current) { $rows += $current }
      $current = [ordered]@{ Id = $Matches[1]; Text = New-Object System.Text.StringBuilder }
      continue
    }
    # A new top-level section closes the current row.
    if ($line -match '^#{1,3}\s' -and $null -ne $current) {
      $rows += $current
      $current = $null
      continue
    }
    if ($null -ne $current) { [void]$current.Text.AppendLine($line) }
  }
  if ($null -ne $current) { $rows += $current }

  foreach ($row in $rows) { $row.Body = $row.Text.ToString() }
  return $rows
}

function Get-RowFiles {
  param([string]$Body)
  $found = @()
  foreach ($m in [regex]::Matches($Body, '`([^`]*?\.lean)`')) {
    $found += $m.Groups[1].Value
  }
  # Unbackticked paths occur, but require a directory separator: bare file names
  # appear in prose ("see ReviewerWholeProtocol.lean") and admitting those made
  # failure messages list files the row never cited.
  foreach ($m in [regex]::Matches($Body, '(?<![`\w/])([A-Za-z0-9_.-]+/[A-Za-z0-9_./-]+\.lean)(?!`)')) {
    $found += $m.Groups[1].Value
  }
  return @($found | Sort-Object -Unique)
}

function Get-RowNames {
  param([string]$Body)
  $found = @()
  foreach ($m in [regex]::Matches($Body, '`([^`]+)`')) {
    $candidate = $m.Groups[1].Value.Trim()
    if (Test-IsLeanIdentifier $candidate) {
      $found += $candidate
      continue
    }
    # Rows sometimes quote a name together with its statement, as in
    # `RMQ.SuccinctClassic.queryCost_eq : queryCost = 210`. The identifier is
    # still named; take the part before the colon. Missing this made a correct
    # citation look like a defect.
    if ($candidate -match "^([A-Za-z_][A-Za-z0-9_.']*)\s*:") {
      if (Test-IsLeanIdentifier $Matches[1]) { $found += $Matches[1] }
    }
  }
  return @($found | Sort-Object -Unique)
}

# The first identifier on the `Declaration:` line is the row's primary subject.
function Get-RowPrimaryDeclaration {
  param([string]$Body)
  $m = [regex]::Match($Body, '(?ms)^- Declaration:(.*?)(?=^- [A-Z])')
  if (-not $m.Success) { return $null }
  foreach ($tick in [regex]::Matches($m.Groups[1].Value, '`([^`]+)`')) {
    $candidate = $tick.Groups[1].Value.Trim()
    if (Test-IsLeanIdentifier $candidate) { return $candidate }
  }
  return $null
}

# Map "field 8 `allocation_two_n_plus_rho`" -> @{ 8 = 'allocation_two_n_plus_rho' }
function Get-RowFieldMap {
  param([string]$Body)
  $map = @{}
  foreach ($m in [regex]::Matches($Body, 'field\s+(\d+)\s+`([^`]+)`')) {
    $number = [int]$m.Groups[1].Value
    $name = $m.Groups[2].Value.Trim()
    if (Test-IsLeanIdentifier $name) { $map[$number] = $name }
  }
  return $map
}

# Bind a citation to the most specific identifier its preceding context supports.
function Get-CitationBinding {
  param(
    [string]$Preceding,
    [hashtable]$FieldMap,
    [string[]]$RowNames
  )

  # Only the tail of the preceding text is context; anything further back
  # belongs to a different citation. Cut at the previous citation if present.
  $segment = $Preceding
  $previous = [regex]::Matches($segment, ':\d{2,}')
  if ($previous.Count -gt 0) {
    $last = $previous[$previous.Count - 1]
    $segment = $segment.Substring($last.Index + $last.Length)
  }

  # "field 8 at :356--359" -- bind through the row's field table.
  $fieldMatches = [regex]::Matches($segment, 'field\s+(\d+)')
  if ($fieldMatches.Count -gt 0) {
    $number = [int]$fieldMatches[$fieldMatches.Count - 1].Groups[1].Value
    if ($FieldMap.ContainsKey($number)) {
      return @{ Names = @($FieldMap[$number]); Strength = "exact"; Why = "field $number" }
    }
  }

  # "producer at :723" -- the declaration that inhabits the structure.
  if ($segment -match 'producer\s+(at\s+)?$' -or $segment -match 'inhabited by\s*$') {
    $producers = @($RowNames | Where-Object { (Get-NameLeaf $_) -match '_holds$|_valid$' })
    if ($producers.Count -gt 0) {
      return @{ Names = $producers; Strength = "exact"; Why = "producer" }
    }
  }

  # "structure at :300" -- the capitalized structure name.
  if ($segment -match 'structure\s+(at\s+)?$') {
    $structures = @($RowNames | Where-Object { (Get-NameLeaf $_) -cmatch '^[A-Z]' })
    if ($structures.Count -gt 0) {
      return @{ Names = $structures; Strength = "exact"; Why = "structure" }
    }
  }

  # Nearest backticked token before the citation decides the binding.
  #
  # If it is a `.lean` PATH, the citation is a file pointer -- the shape used on
  # `- File:` lines, e.g. "`RMQ/Core/SuccinctRMQClassic.lean` (:1240)". Those
  # bind to the file, not to whatever identifier happened to be quoted earlier;
  # treating them as "nearest identifier" walked back into the alias list on the
  # `Declaration:` line and reported three correct citations as defects. The
  # binding is still meaningful: the file is pinned exactly, and the name must
  # be one the row declares.
  $ticked = [regex]::Matches($segment, '`([^`]+)`')
  for ($i = $ticked.Count - 1; $i -ge 0; $i--) {
    $candidate = $ticked[$i].Groups[1].Value.Trim()
    if ($candidate -match '\.lean$') {
      return @{ Names = $RowNames; Files = @($candidate); Strength = "file"; Why = "in $candidate" }
    }
    if (Test-IsLeanIdentifier $candidate) {
      return @{ Names = @($candidate); Strength = "exact"; Why = "nearest name" }
    }
    if ($candidate -match "^([A-Za-z_][A-Za-z0-9_.']*)\s*:") {
      if (Test-IsLeanIdentifier $Matches[1]) {
        return @{ Names = @($Matches[1]); Strength = "exact"; Why = "nearest name" }
      }
    }
  }

  return @{ Names = $RowNames; Strength = "row"; Why = "row-wide" }
}

function Test-CitationResolves {
  param(
    [string]$Root,
    [string[]]$Files,
    [string[]]$Names,
    [int]$Start,
    [int]$End
  )

  $leaves = @($Names | ForEach-Object { Get-NameLeaf $_ } | Sort-Object -Unique)
  $missingFiles = @()

  foreach ($relative in $Files) {
    $full = Join-Path $Root $relative
    if (-not (Test-Path -LiteralPath $full)) { $missingFiles += $relative; continue }
    $content = Get-Content -LiteralPath $full
    if ($Start -lt 1 -or $Start -gt $content.Count) { continue }
    $upper = [Math]::Min($End, $content.Count)

    # A citation may land on the declaration's doc-comment rather than its
    # `theorem` line -- the ledger does both, e.g. L-UB-01 cites the theorem
    # line and L-UB-02 cites the docstring one line above it. Both point at the
    # declaration, so extend the window across a doc-comment block and the
    # blank lines after it. Nothing else is tolerated: the extension stops at
    # the first line that is not a comment or blank, so genuine rot (a citation
    # 29 or 1,090 lines away) still fails.
    if ($content[$Start - 1] -match '^\s*/--') {
      $scan = $Start
      while ($scan -le $content.Count -and $content[$scan - 1] -notmatch '-/\s*$') { $scan++ }
      $scan++
      while ($scan -le $content.Count -and $content[$scan - 1] -match '^\s*$') { $scan++ }
      if ($scan -gt $upper) { $upper = [Math]::Min($scan, $content.Count) }
    }

    for ($lineNo = $Start; $lineNo -le $upper; $lineNo++) {
      $text = $content[$lineNo - 1]
      foreach ($leaf in $leaves) {
        if ($text -match ("(?<![A-Za-z0-9_'.])" + [regex]::Escape($leaf) + "(?![A-Za-z0-9_'])")) {
          return @{ Ok = $true; File = $relative; Line = $lineNo; Name = $leaf; MissingFiles = $missingFiles }
        }
      }
    }
  }
  return @{ Ok = $false; MissingFiles = $missingFiles }
}

function Invoke-CitationCheck {
  param([string]$LedgerPath, [string]$Root, [switch]$ShowAll)

  if (-not (Test-Path -LiteralPath $LedgerPath)) {
    Write-Host "CITATIONS: ledger not found: $LedgerPath"
    return @{ Failures = 1; Total = 0; Exact = 0; FileScoped = 0 }
  }

  $rows = Get-LedgerRows -Path $LedgerPath
  $failures = 0
  $total = 0
  $exact = 0
  $fileScoped = 0

  foreach ($row in $rows) {
    $body = $row.Body
    $files = Get-RowFiles -Body $body
    $names = Get-RowNames -Body $body
    $fieldMap = Get-RowFieldMap -Body $body

    foreach ($m in [regex]::Matches($body, ':(\d{2,})(?:--(\d+))?')) {
      $start = [int]$m.Groups[1].Value
      $end = if ($m.Groups[2].Success) { [int]$m.Groups[2].Value } else { $start }
      $total += 1

      if ($files.Count -eq 0) {
        Write-Host ("CITATIONS[{0}] FAIL :{1} -- row cites a line but names no .lean file" -f $row.Id, $start)
        $failures += 1
        continue
      }
      if ($names.Count -eq 0) {
        Write-Host ("CITATIONS[{0}] FAIL :{1} -- row cites a line but names no declaration" -f $row.Id, $start)
        $failures += 1
        continue
      }

      $binding = Get-CitationBinding -Preceding $body.Substring(0, $m.Index) -FieldMap $fieldMap -RowNames $names
      if ($binding.Strength -eq "exact") { $exact += 1 }
      if ($binding.Strength -eq "file") { $fileScoped += 1 }

      $searchFiles = if ($binding.Files) { @($binding.Files) } else { $files }
      $result = Test-CitationResolves -Root $Root -Files $searchFiles -Names $binding.Names -Start $start -End $end
      if ($result.Ok) {
        if ($ShowAll) {
          Write-Host ("CITATIONS[{0}] ok :{1} -> {2} in {3} [{4}/{5}]" -f `
              $row.Id, $start, $result.Name, $result.File, $binding.Strength, $binding.Why)
        }
      } else {
        $expected = ($binding.Names | ForEach-Object { Get-NameLeaf $_ }) -join ", "
        $where = if ($start -eq $end) { ":$start" } else { ":$start--$end" }
        Write-Host ("CITATIONS[{0}] FAIL {1} -- expected [{2}] ({3}) at that line in: {4}" -f `
            $row.Id, $where, $expected, $binding.Why, ($searchFiles -join ", "))
        if ($result.MissingFiles.Count -gt 0) {
          Write-Host ("             (file(s) not present at this tree: {0})" -f ($result.MissingFiles -join ", "))
        }
        $failures += 1
      }
    }
  }

  return @{ Failures = $failures; Total = $total; Exact = $exact; FileScoped = $fileScoped }
}

$resolved = Resolve-Inputs -Ledger $LedgerPath -Root $RepositoryRoot

if ($SelfTest) {
  # A checker that reports success on a corrupted ledger is worth nothing. Prove
  # it fails closed before trusting the green run: perturb a citation to a line
  # that certainly does not hold the declaration, and require a new failure.
  $baseline = Invoke-CitationCheck -LedgerPath $resolved.Ledger -Root $resolved.Root
  Write-Host ("CITATIONS SELFTEST: baseline {0} citations, {1} pinned to a declaration, {2} to a file, {3} failures" -f `
      $baseline.Total, $baseline.Exact, $baseline.FileScoped, $baseline.Failures)

  if ($baseline.Failures -ne 0) {
    Write-Host "CITATIONS SELFTEST: RESULT: FAIL (baseline is not clean)"
    exit 1
  }

  $temporary = Join-Path ([System.IO.Path]::GetTempPath()) ("ledger_selftest_" + [System.Guid]::NewGuid().ToString("N") + ".md")
  try {
    $originalText = Get-Content -Raw -LiteralPath $resolved.Ledger

    # Mutate EXACTLY ONE citation, and require exactly one new failure.
    #
    # `[regex]::Replace(input, pattern, replacement, 1)` does not do this: the
    # fourth argument of that static overload is RegexOptions, not a count, so
    # `1` means IgnoreCase and every citation is replaced. That version of this
    # self-test reported 27 failures and looked like it passed -- but a checker
    # that only ever examined the first row would have passed it too. Mutating
    # one and demanding one is the assertion that has teeth.
    $mutated = [regex]::new(':(\d{2,})').Replace($originalText, ':999901', 1)
    if ($mutated -eq $originalText) {
      Write-Host "CITATIONS SELFTEST: RESULT: FAIL (could not mutate any citation)"
      exit 1
    }
    Set-Content -LiteralPath $temporary -Value $mutated -Encoding UTF8

    $mutatedResult = Invoke-CitationCheck -LedgerPath $temporary -Root $resolved.Root
    if ($mutatedResult.Failures -ne 1) {
      Write-Host ("CITATIONS SELFTEST: RESULT: FAIL (one mutated citation produced {0} failure(s), expected exactly 1)" -f `
          $mutatedResult.Failures)
      exit 1
    }
    if ($mutatedResult.Total -ne $baseline.Total) {
      Write-Host ("CITATIONS SELFTEST: RESULT: FAIL (mutation changed the citation count {0} -> {1})" -f `
          $baseline.Total, $mutatedResult.Total)
      exit 1
    }
    Write-Host "CITATIONS SELFTEST: ok -- one mutated citation produced exactly one failure"
  } finally {
    if (Test-Path -LiteralPath $temporary) { Remove-Item -LiteralPath $temporary -Force }
  }

  Write-Host "CITATIONS SELFTEST: RESULT: PASS"
  exit 0
}

$run = Invoke-CitationCheck -LedgerPath $resolved.Ledger -Root $resolved.Root -ShowAll:$ShowAll
if ($run.Failures -gt 0) {
  Write-Host ("CITATIONS: RESULT: FAIL ({0} of {1} citations do not resolve)" -f $run.Failures, $run.Total)
  exit 1
}
# Report the three binding strengths separately. Lumping `file` in with `row`
# would overstate how much of the ledger is pinned to a named declaration.
Write-Host ("CITATIONS: RESULT: PASS ({0} citations resolve; {1} pinned to a named declaration, {2} pinned to a named file, {3} row-wide)" -f `
    $run.Total, $run.Exact, $run.FileScoped, ($run.Total - $run.Exact - $run.FileScoped))
exit 0

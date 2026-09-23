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
#             file is pinned exactly; the name must be one on `- Declaration:`.
#   row    -- context named none; any name on `- Declaration:` was accepted.
#
# The two FALLBACK bindings admit only names on the row's `- Declaration:`
# line. The `nearest name` binding also admits a name quoted immediately
# before the citation, which is deliberate -- that is what `$RowNames` is for,
# as the comment at the fallback site says. This sentence read "All three
# admit ONLY", which the file contradicted two hundred lines later. The cited
# line must DECLARE that name -- a `theorem`/`def`/`structure`/... keyword, or a
# structure field `name :` -- rather than merely mention it.
#
# Both restrictions were forced by audit, and the measured strength is the point:
#
#   any backticked identifier in the row    worst case 570 of 1,617 lines
#   only `- Declaration:` names             worst case  35 of   746 lines
#   a declaration SITE (current)            worst case   2 of   209 lines
#
# 26 of the 26 cited names have exactly one satisfying line in their file, so a
# rotted citation has almost nowhere to land. The middle row was reported as a
# fix; it left five real rots passing, including a `rw [...]` proof step 1,274
# lines from its theorem.
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

# The identifiers on the `- Declaration:` line: the names the row actually
# CLAIMS, as opposed to every identifier it happens to mention.
#
# This distinction is the difference between a check and a formality. An earlier
# version used every backticked identifier in the row as the acceptable set for
# the weaker bindings, which swept in prose metavariables from the `Proposition:`
# text -- `xs`, `v`, `w`, `idx`, `lem`, `thm`. `xs` occurs on 35% of the lines of
# `RMQ/Core/SuccinctRMQClassic.lean`, so "the citation lands on a line naming
# something this row mentions" was satisfied by roughly any line at all.
#
# Demonstrated, not theorised: with that set, moving L-REF-01's `:48` to `:44`
# (a `ValidRange` definition) and L-REF-02's `:1198` to `:900` (298 lines of
# drift) both still reported RESULT: PASS.
function Get-RowDeclarationNames {
  param([string]$Body)
  $m = [regex]::Match($Body, '(?ms)^- Declaration:(.*?)(?=^- [A-Z])')
  if (-not $m.Success) { return @() }
  $found = @()
  foreach ($tick in [regex]::Matches($m.Groups[1].Value, '`([^`]+)`')) {
    $candidate = $tick.Groups[1].Value.Trim()
    if (Test-IsLeanIdentifier $candidate) {
      $found += $candidate
      continue
    }
    if ($candidate -match "^([A-Za-z_][A-Za-z0-9_.']*)\s*:") {
      if (Test-IsLeanIdentifier $Matches[1]) { $found += $Matches[1] }
    }
  }
  return @($found | Sort-Object -Unique)
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
    [string[]]$RowNames,
    [string[]]$DeclarationNames
  )

  # Every FALLBACK below uses $DeclarationNames -- the names the row claims --
  # never $RowNames, which includes prose metavariables from the `Proposition:`
  # text. $RowNames is still right for the `nearest name` binding, where the
  # identifier was quoted immediately before the citation and is deliberate.
  $fallback = @($DeclarationNames)

  # Only the tail of the preceding text is context; anything further back
  # belongs to a different citation. Cut at the previous citation if present.
  $segment = $Preceding
  $previous = [regex]::Matches($segment, ':\d+')
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
    $producers = @($fallback | Where-Object { (Get-NameLeaf $_) -match '_holds$|_valid$' })
    if ($producers.Count -gt 0) {
      return @{ Names = $producers; Strength = "exact"; Why = "producer" }
    }
  }

  # "structure at :300" -- the capitalized structure name.
  if ($segment -match 'structure\s+(at\s+)?$') {
    $structures = @($fallback | Where-Object { (Get-NameLeaf $_) -cmatch '^[A-Z]' })
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
      return @{ Names = $fallback; Files = @($candidate); Strength = "file"; Why = "in $candidate" }
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

  return @{ Names = $fallback; Strength = "row"; Why = "row-wide" }
}

# Is this line inside a `/- ... -/` or `/-- ... -/` block?
#
# Counts openers and closers from the top of the file. Cheap enough here (the
# cited files are read once per citation) and correct for the shapes Lean uses,
# including a docstring whose text spans several lines -- the case that made
# "comments are rejected" false.
function Test-InsideBlockComment {
  param([string[]]$Lines, [int]$LineNumber)
  $depth = 0
  for ($i = 0; $i -lt $LineNumber - 1; $i++) {
    $opens = ([regex]::Matches($Lines[$i], '/-')).Count
    $closes = ([regex]::Matches($Lines[$i], '-/')).Count
    $depth += $opens - $closes
    if ($depth -lt 0) { $depth = 0 }
  }
  return ($depth -gt 0)
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
    # A cited RANGE is honoured, but bounded. `:1--860` spanned an entire file
    # and resolved, reported identically to a one-line citation as "pinned to a
    # named declaration". Real ranges in this ledger are a few lines
    # (`:356--359`); anything wider is not a pointer.
    $citationRangeLimit = 12
    if ($End - $Start -gt $citationRangeLimit) {
      continue
    }
    $upper = [Math]::Min($End, $content.Count)

    # A citation may land on the declaration's doc-comment rather than its
    # `theorem` line -- the ledger does both: L-UB-01 cites the theorem line,
    # L-UB-02 cites the docstring one line above it. So the window extends
    # across a doc-comment block and the blank lines after it, hard-bounded.
    #
    # The bound is not decoration. `/-- One line. -/ def width := 3` terminates
    # inline, and an unbounded scan for the terminator would run past EOF and
    # open the window to the whole file. That shape is COMMON here -- 65
    # occurrences in `SuccinctRMQClassic.lean` alone, including line 1233, which
    # L-UB-02 cites. An earlier comment claimed no cited file contained it; that
    # was false, and the same commit removed the `\s*$` anchor its own comment
    # blamed. The budget is what makes this safe, not the anchor.
    $docCommentWindowLimit = 6
    if ($content[$Start - 1] -match '^\s*/--') {
      $scan = $Start
      $budget = $docCommentWindowLimit
      while ($scan -le $content.Count -and $budget -gt 0 -and
             $content[$scan - 1] -notmatch '-/') { $scan++; $budget-- }
      $scan++
      while ($scan -le $content.Count -and $budget -gt 0 -and
             $content[$scan - 1] -match '^\s*$') { $scan++; $budget-- }
      $capped = [Math]::Min($scan, $Start + $docCommentWindowLimit)
      if ($capped -gt $upper) { $upper = [Math]::Min($capped, $content.Count) }
    }

    # The cited line must DECLARE the name, not merely mention it.
    #
    # Requiring only a mention made the check far weaker than its own wording.
    # Restricting the acceptable names to the `- Declaration:` line helped a
    # great deal (worst case 570 of 1,617 lines down to 35 of 746) but did not
    # fix the kind: a proof step `rw [queryCosted_invalid xs left right hbad]`
    # 1,274 lines from the theorem still satisfied L-UB-04, and four more rots
    # like it passed. "Mentions the name somewhere" is not "is the declaration".
    #
    # Accepted shapes: a Lean declaration keyword followed by the name, or a
    # structure field declaration `name :`. Rejected: proof steps, hypothesis
    # lines, imports, prose, comments, and field ASSIGNMENTS.
    #
    # `name :=` is the trap. The field pattern was `\s*:` unanchored on the
    # right, so it matched `allocation_two_n_plus_rho :=` -- a field assignment
    # inside the `refine { ... }` that PROVES the capstone, 415 lines below the
    # structure. L-PACK-01's `field 8 at :356` could be moved to `:771` and the
    # run still reported PASS. A field declaration states a type; a field
    # assignment discharges it. Only the former is a declaration site, so the
    # right-hand side must not be `=`.
    #
    # Comment text is stripped before matching for the same reason: `-- theorem
    # foo` and a docstring mentioning `theorem foo` are prose about a
    # declaration, not one.
    foreach ($leaf in $leaves) {
      $escaped = [regex]::Escape($leaf)
      $declarationSite =
        '(^|\s)(theorem|lemma|def|abbrev|structure|inductive|instance|axiom|opaque|example)\s+' +
        $escaped + "(?![A-Za-z0-9_'.])"
      $fieldSite = '^\s*' + $escaped + "(?![A-Za-z0-9_'.])\s*:(?!=)"
      for ($lineNo = $Start; $lineNo -le $upper; $lineNo++) {
        $text = $content[$lineNo - 1]
        # Skip comment text. The earlier rule only skipped lines STARTING with a
        # marker, so the interior of a block comment and the continuation lines
        # of a docstring were still treated as code -- "prose, comments ...
        # rejected" was false for both. Determine block-comment membership by
        # scanning from the top of the file rather than by inspecting one line.
        if ($text -match '^\s*(--|/-|-/)') { continue }
        if (Test-InsideBlockComment -Lines $content -LineNumber $lineNo) { continue }
        # String literals are prose too. `throwError "expected theorem foo"`
        # satisfies the declaration-site pattern -- the keyword is preceded by a
        # space, which is all `(^|\s)` asks for. Stripping literals costs
        # nothing on real declaration lines, which contain none.
        #
        # KNOWN LIMIT, stated rather than implied: a `where`-clause binding
        # `  foo : Nat := 3` matches the field-site pattern and would resolve a
        # citation whose leaf is `foo`. Distinguishing it needs the enclosing
        # declaration, which this line-local matcher does not have. It requires
        # a cited line to be a `where` binding of the same leaf name as the
        # declaration the row names; no row in this ledger is that shape.
        $code = ($text -split '--', 2)[0]
        $code = [regex]::Replace($code, '"(?:[^"\\]|\\.)*"', '""')
        if ($code -match $declarationSite -or $code -match $fieldSite) {
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
    $declarationNames = Get-RowDeclarationNames -Body $body

    foreach ($m in [regex]::Matches($body, ':(\d+)(?:--(\d+))?')) {
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

      $binding = Get-CitationBinding -Preceding $body.Substring(0, $m.Index) -FieldMap $fieldMap -RowNames $names -DeclarationNames $declarationNames
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
    $mutated = [regex]::new(':(\d+)').Replace($originalText, ':999901', 1)
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

    # Two defects a :999901 mutation cannot see, both found by audit after this
    # checker was first reported working. Fixtures, because each needs a source
    # file shaped a particular way.
    $fixtureRoot = Join-Path ([System.IO.Path]::GetTempPath()) ("citefx_" + [System.Guid]::NewGuid().ToString("N"))
    try {
      New-Item -ItemType Directory -Force -Path (Join-Path $fixtureRoot "Fake") | Out-Null

      # (a) PROSE METAVARIABLES. A rot onto a line mentioning `xs` used to pass,
      #     because every backticked identifier in the row -- including `xs`,
      #     `v`, `idx` from the Proposition text -- was an acceptable target.
      #     `xs` occurs on ~35% of lines of a real source file.
      $drifted = @(1..40 | ForEach-Object { "  cases xs with" })
      $drifted[19] = "theorem real_decl : True := trivial"   # line 20
      [IO.File]::WriteAllLines((Join-Path $fixtureRoot "Fake\M.lean"), $drifted)
      $metavarLedger = Join-Path $fixtureRoot "meta.md"
      [IO.File]::WriteAllText($metavarLedger,
        "#### L-FX-01`n- Declaration: ``real_decl```n- File: ``Fake/M.lean`` (:5)`n- Proposition: for all ``xs``, with ``v`` and ``idx``.`n")
      # And that the fixture SOURCE exists. Deleting the fixture .lean makes the
      # citation unresolvable, so Total and Failures come out identical to the
      # healthy run -- "failed because the source is missing" and "failed for the
      # reason under test" are otherwise the same observation.
      if (-not (Test-Path -LiteralPath (Join-Path $fixtureRoot "Fake\M.lean"))) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (metavariable fixture source was not written)"
        exit 1
      }
      $metavarResult = Invoke-CitationCheck -LedgerPath $metavarLedger -Root $fixtureRoot
      # Assert the fixture was EXAMINED, not merely that it did not pass. A
      # fixture parsing to zero citations yields zero failures, which is
      # indistinguishable from one the checker handled. An earlier round claimed
      # this guard was added; it was not -- the patch matched nothing (CRLF vs
      # LF) and reported success anyway.
      if ($metavarResult.Total -lt 1) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (metavariable fixture parsed 0 citations; it tested nothing)"
        exit 1
      }
      if ($metavarResult.Failures -lt 1) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (a citation drifted onto a line mentioning only a prose metavariable still passed)"
        exit 1
      }
      Write-Host "CITATIONS SELFTEST: ok -- prose metavariables are not acceptable citation targets"

      # (b) DOC-COMMENT WINDOW. `/-- One line. -/ def x := 1` terminates inline,
      #     so a terminator search anchored to end-of-line never matches. Before
      #     the window was bounded it ran past EOF and the citation resolved
      #     against the entire file.
      $inline = @(1..400 | ForEach-Object { "-- filler" })
      $inline[9] = "/-- Inline terminated. -/ def decoy : Nat := 1"   # line 10
      $inline[399] = "theorem far_away : True := trivial"             # line 400
      [IO.File]::WriteAllLines((Join-Path $fixtureRoot "Fake\W.lean"), $inline)
      $windowLedger = Join-Path $fixtureRoot "window.md"
      [IO.File]::WriteAllText($windowLedger,
        "#### L-FX-02`n- Declaration: ``far_away```n- File: ``Fake/W.lean`` (:10)`n- Proposition: x`n")
      if (-not (Test-Path -LiteralPath (Join-Path $fixtureRoot "Fake\W.lean"))) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (doc-comment fixture source was not written)"
        exit 1
      }
      $windowResult = Invoke-CitationCheck -LedgerPath $windowLedger -Root $fixtureRoot
      if ($windowResult.Total -lt 1) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (doc-comment fixture parsed 0 citations; it tested nothing)"
        exit 1
      }
      if ($windowResult.Failures -lt 1) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (an inline-terminated doc comment opened a whole-file resolution window)"
        exit 1
      }
      Write-Host "CITATIONS SELFTEST: ok -- the doc-comment window is bounded"

      # (c) NON-DECLARATION SHAPES. Each of these mentions the name in a context
      #     that is not a declaration. A field ASSIGNMENT (`name :=`) is the one
      #     that bit: it appears in the `refine { ... }` proving a structure,
      #     hundreds of lines from the structure itself, and an unanchored
      #     `name\s*:` pattern matched it. L-PACK-01 could be moved 415 lines
      #     into a proof and still report PASS.
      $decoy = @(1..60 | ForEach-Object { "  filler" })
      $decoy[9]  = "-- theorem decoy_target is described here"      # comment
      $decoy[19] = "  decoy_target := by simp"                      # field assignment
      $decoy[29] = "/-- Mentions theorem decoy_target in prose. -/" # docstring
      $decoy[39] = "  exact decoy_target xs left right"             # proof step
      [IO.File]::WriteAllLines((Join-Path $fixtureRoot "Fake\D.lean"), $decoy)
      if (-not (Test-Path -LiteralPath (Join-Path $fixtureRoot "Fake\D.lean"))) {
        Write-Host "CITATIONS SELFTEST: RESULT: FAIL (non-declaration fixture source was not written)"
        exit 1
      }
      foreach ($decoyLine in @(10, 20, 30, 40)) {
        $decoyLedger = Join-Path $fixtureRoot ("decoy" + $decoyLine + ".md")
        [IO.File]::WriteAllText($decoyLedger,
          "#### L-FX-03`n- Declaration: ``decoy_target```n- File: ``Fake/D.lean`` (:$decoyLine)`n- Proposition: x`n")
        $decoyResult = Invoke-CitationCheck -LedgerPath $decoyLedger -Root $fixtureRoot
        if ($decoyResult.Total -lt 1) {
          Write-Host "CITATIONS SELFTEST: RESULT: FAIL (decoy fixture at :$decoyLine parsed 0 citations)"
          exit 1
        }
        if ($decoyResult.Failures -lt 1) {
          Write-Host "CITATIONS SELFTEST: RESULT: FAIL (a citation to line $decoyLine resolved; that line mentions the name but does not declare it)"
          exit 1
        }
      }
      Write-Host "CITATIONS SELFTEST: ok -- comments, field assignments and proof steps are not declaration sites"
    } finally {
      if (Test-Path -LiteralPath $fixtureRoot) {
        Remove-Item -LiteralPath $fixtureRoot -Recurse -Force -ErrorAction SilentlyContinue
      }
    }
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

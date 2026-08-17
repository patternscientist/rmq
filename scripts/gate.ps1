#!/usr/bin/env pwsh
# RMQ autonomous-loop acceptance gate.
#
# Exit 0  = ACCEPT: the round is sound and non-regressing; the loop may continue.
# Exit !=0 = STOP: surface to the human (or retry once, then stop).
#
# This gate proves soundness and non-regression. It does NOT prove the round
# moved the needle -- that is the roadmap / anti-filler contract's job
# (see docs/internal/CODEX_AUTONOMY.md and docs/ROADMAP.md).

$ErrorActionPreference = 'Continue'

# Builds are DEPENDENCIES: if one fails, everything after it is meaningless, so
# `Fail` still exits immediately.  The independent checks below use `SoftFail`,
# which records the problem and keeps going, so ONE run reports EVERY issue.
# Before this, a gate with N accumulated defects cost N push-wait-fix cycles;
# the night of 2026-07-20 spent seven of them on one root cause.
$script:issues = @()
function Fail($msg) { Write-Host "GATE FAIL: $msg"; exit 1 }
function SoftFail($msg) { Write-Host "GATE ISSUE: $msg"; $script:issues += $msg }

function RunAxiomCheck($script, $label) {
  $tmp = New-TemporaryFile
  & lake env lean $script *> $tmp
  $code = $LASTEXITCODE
  if ($code -ne 0) {
    # Print the ERROR lines first.  A tail alone hides the cause: on 2026-07-20
    # an `unknown constant` error sat above the last 80 lines, so the tail showed
    # only healthy-looking axiom output and the real failure was invisible.
    $errs = Select-String -Path $tmp -Pattern "error|unknown constant" |
      ForEach-Object { $_.Line }
    if ($errs) {
      Write-Host "AXIOM CHECK ERRORS [${label}]:"
      $errs | ForEach-Object { Write-Host "  $_" }
    }
    Write-Host "AXIOM CHECK OUTPUT (tail) [${label}]:"
    Get-Content $tmp -Tail 80
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail "$label did not run cleanly"
    return
  }
  if (Select-String -Path $tmp -Pattern "sorryAx|ofReduceBool") {
    $bad = Get-Content $tmp
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail "non-standard axiom in ${label}:`n$bad"
    return
  }
  # WHITELIST, not only a blacklist.  Until 2026-08-16 this function rejected
  # just the two names above, so a declaration depending on a differently-named
  # project axiom printed its dependency set and still received
  # `AXIOM CHECK PASS`.  The property these inventories advertise is "only the
  # three standard axioms"; a blacklist of two known-bad names is not that
  # property, it is a check that happens to agree with it on the current tree.
  # Found by the 2026-08-15 fresh-blind audit (P2-3).
  $allowed = @('propext', 'Classical.choice', 'Quot.sound')
  $unexpected = @()
  $examined = 0
  # `#print axioms` emits: 'X' depends on axioms: [a, b, c]
  #
  # Lean WRAPS long dependency lists, so the closing `]` is often on a later
  # line. Matching per-line with `\[(.*)\]` therefore saw only the records that
  # happened to fit on one line -- 36 of 104 at this tree. The other 68 fell
  # through to the two-name blacklist this whitelist replaced, which
  # WDD-20260816-032 itself calls "not that property".
  #
  # Read the whole file and match across newlines instead, and count what was
  # examined so a parse that silently stops finding records cannot pass as clean.
  $axiomText = [IO.File]::ReadAllText($tmp)
  foreach ($m in [regex]::Matches($axiomText, "depends on axioms:\s*\[([^\]]*)\]", 'Singleline')) {
    $examined += 1
    foreach ($name in ($m.Groups[1].Value -split ',')) {
      $trimmed = $name.Trim() -replace '\s+', ''
      if ($trimmed -and ($allowed -cnotcontains $trimmed)) {
        $unexpected += $trimmed
      }
    }
  }
  $declared = ([regex]::Matches($axiomText, "depends on axioms:")).Count
  if ($examined -ne $declared) {
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail ("axiom parse in ${label} examined $examined of $declared dependency records; the rest were not inspected")
    return
  }

  # Both quantities above come from the SAME output, so an inventory that emits
  # no records at all satisfies `0 -eq 0` and reports PASS. Deleting every
  # `#print axioms` line from a check file was a clean pass.
  #
  # The floor is derived from the source rather than pinned by hand: every
  # `#print axioms` directive emits exactly one line, either `depends on axioms:`
  # or `does not depend on any axioms`. Fewer records than directives means some
  # directive did not run.
  # `[IO.File]` resolves a relative path against .NET's CurrentDirectory, which
  # `Set-Location` does not update: measured, this read `scripts/gate.ps1` out of a
  # DIFFERENT worktree. When the path does not resolve at all it throws,
  # `$directiveCount` stays `$null`, and BOTH guards below evaluate false -- the
  # floor becomes a silent no-op while AXIOM CHECK PASS prints. `-1` makes an
  # unreadable source fail closed instead.
  #
  # Block comments are stripped first: a directive inside `/- ... -/` emits no
  # record, so counting it would false-fail. No such block exists in the eight
  # inventories today; the strip is here so that adding one is not a gate failure.
  $directiveCount = -1
  $sourceText = $null
  try { $sourceText = Get-Content -Raw -LiteralPath $script -ErrorAction Stop } catch { }
  if ($null -ne $sourceText) {
    $liveSource = [regex]::Replace($sourceText, '(?s)/-.*?-/', '')
    $directiveCount = ([regex]::Matches($liveSource, '(?m)^\s*#print axioms\b')).Count
  }
  $recordCount = $declared + ([regex]::Matches($axiomText, "does not depend on any axioms")).Count
  if ($directiveCount -lt 1) {
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail ("${label} contains no ``#print axioms`` directive; it is not an axiom inventory and a clean run means nothing")
    return
  }
  if ($recordCount -lt $directiveCount) {
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail ("${label} produced $recordCount axiom record(s) for $directiveCount ``#print axioms`` directive(s); some directive did not run")
    return
  }
  if ($unexpected.Count -gt 0) {
    Remove-Item $tmp -ErrorAction SilentlyContinue
    SoftFail ("axiom outside the standard three in ${label}: " +
      (($unexpected | Select-Object -Unique) -join ', '))
    return
  }
  Remove-Item $tmp -ErrorAction SilentlyContinue
  Write-Host "AXIOM CHECK PASS: $label (standard axioms only)"
}


# --- How a sub-checker fails to run, and why that used to be a PASS ---------
#
# The pattern below was `& "$PSScriptRoot\x.ps1"` followed by
# `if ($LASTEXITCODE -ne 0) { SoftFail ... }`. That reports PASS when the
# checker did not run at all. Measured on this runtime (PowerShell 5.1), FOUR
# distinct failures leave $LASTEXITCODE at its PREVIOUS value:
#
#   missing file  -> CommandNotFoundException
#   parse error   -> ParseException
#   `throw`       -> RuntimeException
#   no `exit`     -> the variable is simply never assigned
#
# In this script the previous value is the previous checker's 0. So deleting a
# checker from disk, or breaking its syntax, turned its stage green. Every
# `.ps1` stage had this shape, and step 7c made it explicit: `check_paper.ps1`
# sat behind a bare `Test-Path` with no `else`, so an absent manuscript checker
# was silently skipped.
#
# Invoke-Checker removes $LASTEXITCODE before the call, so "still undefined
# afterwards" is decidable, and catches the exception so a throw is
# distinguishable from a clean run that never called `exit`.
$script:checkersRun = @()

function Invoke-Checker {
  param(
    [Parameter(Mandatory)][string]$Path,
    [hashtable]$CheckerParams = @{},
    [switch]$Soft,
    [string]$Label
  )
  if (-not $Label) { $Label = Split-Path $Path -Leaf }

  # The roster records path AND arguments. It recorded the LABEL alone -- a
  # hand-written string with no relation to $CheckerParams -- so changing
  # `@{ Strict = $true }` to `@{}` on the claim-policy stage left coverage at
  # 17 of 17, raw call sites at 0, and that stage incapable of failing:
  # measured, the same scan exits 1 with -Strict and 0 without. Coverage that
  # cannot see the mode is not coverage.
  # Path AND key=VALUE. Recording key names alone was not mode-awareness:
  # `@{ Strict = $true }` and `@{ Strict = $false }` produced the IDENTICAL roster
  # entry, so a one-token change disarmed the claim-policy stage at full coverage
  # -- the exact defect the previous version was written to close, which it caught
  # only for `@{}`, the one mutation it was tested against.
  #
  # The resolved script name is recorded too, because `-Label` is a free string: a
  # stage could otherwise run against a different script and still match its entry.

  if (-not (Test-Path -LiteralPath $Path)) {
    $m = "$Label DID NOT RUN: no such file ($Path). A missing checker is not a passing checker."
    if ($Soft) { SoftFail $m; return }
    Fail $m
  }

  # Hashtable splatting, NOT array splatting. Measured: `& $Path @('-SelfTest')`
  # passes the string as a POSITIONAL value, so it bound to each target's first
  # positional parameter -- `-SelfTest` became `claim_drift_scan`'s $PolicyPath
  # and `tag_annotation_check`'s $Pattern, and threw outright on the scripts with
  # no positional to absorb it. The literal `-SelfTest` in the old call sites was
  # correct; the conversion to array splatting is what broke it.
  #
  # A hashtable binds switches correctly -- and silently DROPS a key the target
  # does not declare, which is the same failure one level quieter. So the keys
  # are checked against the target's own parameter list first.
  $declared = $null
  try { $declared = (Get-Command -Name $Path -CommandType ExternalScript -ErrorAction Stop).Parameters } catch { }
  if ($null -eq $declared) {
    $m = "$Label DID NOT RUN: its parameters could not be read, so arguments cannot be checked"
    if ($Soft) { SoftFail $m; return }
    Fail $m
  }
  foreach ($k in $CheckerParams.Keys) {
    if (-not $declared.ContainsKey($k)) {
      $m = "$Label does not declare -$k; splatting would drop it silently and the check would run in the wrong mode"
      if ($Soft) { SoftFail $m; return }
      Fail $m
    }
  }


  Remove-Variable -Name LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
  $threw = $null
  try { & $Path @CheckerParams } catch { $threw = $_ }

  if ($null -ne $threw) {
    $m = "$Label DID NOT RUN: {0}: {1}" -f $threw.Exception.GetType().Name, $threw.Exception.Message
    if ($Soft) { SoftFail $m; return }
    Fail $m
  }

  # Recorded after the THROW check too. A `#requires` mismatch, a parse error or a
  # thrown exception all reach this point having executed nothing of the body, and
  # a checker counted there prints `GATE COVERAGE: n of 17` beside `DID NOT RUN`.
  # Recorded AFTER the guards, not before. Appending on entry counted a checker
  # that then failed Test-Path or the parameter check: `GATE COVERAGE: 1 of 17`
  # printed alongside `DID NOT RUN: no such file`. The verdict was right -- the
  # gate still exits 1 -- but the coverage sentence said a stage was invoked when
  # it was not, which is the species this file keeps correcting elsewhere.
  $paramSig = @($CheckerParams.GetEnumerator() | Sort-Object Key |
    ForEach-Object { "$($_.Key)=$($_.Value)" })
  $script:checkersRun += ($Label + ' {' + (Split-Path $Path -Leaf) + '}' +
    $(if ($paramSig.Count) { ' [' + ($paramSig -join ',') + ']' } else { '' }))

  $lec = Get-Variable -Name LASTEXITCODE -Scope Global -ErrorAction SilentlyContinue
  if ($null -eq $lec) {
    # Ran, raised nothing, and never called `exit`. That is a pass, but it is a
    # different thing from `exit 0`, so it is named rather than conflated.
    Write-Host "GATE NOTE: $Label completed without an explicit exit code (treated as 0)"
    return
  }
  $code = [int]$lec.Value
  if ($code -ne 0) {
    $m = "$Label found issues (exit $code)"
    if ($Soft) { SoftFail $m; return }
    Fail $m
  }
}

# The stages below call `lake`, `rg` and `git` directly, and a missing external
# tool fails the same way for the same reason -- CommandNotFoundException under
# $ErrorActionPreference = 'Continue', with $LASTEXITCODE untouched.
#
# `rg` was omitted when this assertion was written, and steps 2 and 2b depend on
# it entirely: with `rg` absent, `$hygiene` and `$nd` are simply never assigned,
# `if ($hygiene)` is false, no SoftFail is recorded, and the proof-hygiene and
# `native_decide` scans contribute nothing to the verdict while the gate walks on
# toward GATE PASS. Measured on a probe of the two step-2 lines with `rg` removed
# from PATH: issues recorded = 0, identical to the healthy run.
foreach ($tool in @('lake', 'rg', 'git')) {
  if (-not (Get-Command $tool -ErrorAction SilentlyContinue)) {
    Fail ("$tool is not on PATH; the stages that depend on it would record nothing and the gate would proceed")
  }
}
# 0. Project-skill startup policy must reject stale checkout/runtime catalogs.
Invoke-Checker -Path "$PSScriptRoot\project_skill_preflight_regression.ps1" -Soft

Invoke-Checker -Path "$PSScriptRoot\worker_prompt_preflight_regression.ps1" -Soft

# Default-sensitive design classification and strict-base behavior must be
# exercised through the production checker before broad repository work.
Invoke-Checker -Path "$PSScriptRoot\design_decision_check_regression.ps1"

# 1. Build must be green.
lake build
if ($LASTEXITCODE -ne 0) { Fail "lake build failed" }

# The M1 replay's headline check imports RMQPaper, which is not part of the
# default RMQ target, so RMQPaper must be built before the replay runs on a
# cold builder.
lake build RMQPaper
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQPaper failed" }

# M1R3-MUTATION-RUNNER-GATE-ANCHOR
# The exact 41-case M1 certificate/public-dependency replay runs once in the
# aggregate gate. Its exit code is propagated before later certification.
Invoke-Checker -Path "$PSScriptRoot\m1_certificate_mutation_regression.ps1"

# EG-CP-REPLAY-GATE-ANCHOR
# The two committed EG-CP architecture replays run from the aggregate.
#
# Until 2026-08-16 neither was invoked here, so the required gate's advertised
# mutation coverage EXCLUDED the release headline: the packed cell-probe
# architecture.  Both suites existed, were committed, and passed when run by
# hand -- the defect was that nothing required them.  A coordinated
# implementation/proof edit could therefore keep ordinary elaboration green
# while making a sibling store, hidden oracle, fabricated cap or weakened
# consumer acceptable, and no step of this gate would notice.
#
# Found by the 2026-08-15 fresh-blind audit (P1-2), after surviving two prior
# fresh-blind audits and a coordinator review.  Exit codes propagate; each
# runner keeps its own clean-tree and hash-restoration checks.
Invoke-Checker -Path "$PSScriptRoot\eg_cp_stagea_replay.ps1"

Invoke-Checker -Path "$PSScriptRoot\eg_cp_final_falsification_replay.ps1"

lake build RMQHub
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQHub failed" }

lake build RMQRankSelect
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQRankSelect failed" }

lake build RMQBPNavigation
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQBPNavigation failed" }

lake build RMQUnionFind
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQUnionFind failed" }

lake build VerifiedDS
if ($LASTEXITCODE -ne 0) { Fail "lake build VerifiedDS failed" }

lake build RMQArchive
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQArchive failed" }

lake build RMQExamples
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQExamples failed" }

lake build RMQ.Core.GenericSelectBPCompat
if ($LASTEXITCODE -ne 0) { Fail "lake build RMQ.Core.GenericSelectBPCompat failed" }

# 1b. Validation executables, DERIVED from lakefile.toml rather than hardcoded.
# These carry `#guard`s that fire at BUILD time, so building them here catches a
# stale fixture in the fast gate instead of only in the slow artifact-repro
# workflow -- a stale `#guard` went undetected for days because the only
# workflow covering these was itself broken.  The list is read from the lakefile
# so that a branch which adds or removes an executable does not need this script
# edited, and so that this gate cannot name a target that does not exist.
$exeNames = @()
foreach ($line in (Get-Content lakefile.toml)) {
  if ($line -match '^\s*\[\[lean_exe\]\]\s*$') { $inExe = $true; continue }
  if ($line -match '^\s*\[\[') { $inExe = $false }
  if ($inExe -and $line -match '^\s*name\s*=\s*"([^"]+)"') { $exeNames += $Matches[1] }
}
if ($exeNames.Count -eq 0) { Fail "no lean_exe targets found in lakefile.toml (parser broken?)" }
foreach ($exe in $exeNames) {
  lake build $exe
  if ($LASTEXITCODE -ne 0) { Fail "lake build $exe failed" }
}
Write-Host "VALIDATION EXES BUILT: $($exeNames -join ', ')"

# 2. Proof-hygiene scan: any hit fails the gate.
$hygiene = rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples RMQPaper.lean RMQHub.lean RMQRankSelect.lean RMQBPNavigation.lean RMQUnionFind.lean VerifiedDS.lean RMQArchive.lean RMQExamples.lean lakefile.toml
if ($hygiene) { SoftFail "hygiene scan hit:`n$hygiene" }

$nd = rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples RMQPaper.lean RMQHub.lean RMQRankSelect.lean RMQBPNavigation.lean RMQUnionFind.lean VerifiedDS.lean RMQArchive.lean RMQExamples.lean
if ($nd) { SoftFail "native_decide / ofReduceBool present in source:`n$nd" }

# 3. Curated trust-base check: load-bearing theorems use only standard axioms.
RunAxiomCheck "scripts/hub_axiom_check.lean" "hub_axiom_check.lean"
RunAxiomCheck "scripts/wordram_axiom_check.lean" "wordram_axiom_check.lean"
RunAxiomCheck "scripts/axiom_check.lean" "axiom_check.lean"
RunAxiomCheck "scripts/headline_axiom_check.lean" "headline_axiom_check.lean"
RunAxiomCheck "scripts/archive_axiom_check.lean" "archive_axiom_check.lean"
RunAxiomCheck "scripts/rank_select_axiom_check.lean" "rank_select_axiom_check.lean"
RunAxiomCheck "scripts/bp_navigation_axiom_check.lean" "bp_navigation_axiom_check.lean"
RunAxiomCheck "scripts/union_find_axiom_check.lean" "union_find_axiom_check.lean"

# 3b. Independence regression for the packed structural countdown.  The claim
# that the `210` in `427 = 1 + 2*3 + 2*210` is not the charged-trace `210` was
# prose in paper/THEOREM_LEDGER.md and in the RMQ/Headlines/RMQ.lean docstring;
# this makes it a checked property of the proof term.  Unlike the axiom checks
# it signals purely by exit code, so it gets its own step rather than
# RunAxiomCheck's output grep.
lake env lean scripts/independence_check.lean
if ($LASTEXITCODE -ne 0) { Fail "independence_check.lean failed (see output above)" }
Write-Host "INDEPENDENCE CHECK: PASS"

# 3c. Every declaration cited by an ACCEPTED_BASE row of paper/THEOREM_LEDGER.md
# still exists.  That status means "kernel-checked declaration present on the
# base commit", so a rename or removal makes the ledger assert something false
# without breaking any build.  Existence only -- whether a declaration still
# says what its row claims is the audit's job, not this script's.
lake env lean scripts/ledger_decl_check.lean
if ($LASTEXITCODE -ne 0) { Fail "ledger_decl_check.lean failed (see output above)" }
Write-Host "LEDGER DECL CHECK: PASS"

# 4. Succinct frontier cost/space lints.
Invoke-Checker -Path "$PSScriptRoot\succinct_cost_lint.ps1" -Soft

# 5. Compatibility-shim import boundary.
Invoke-Checker -Path "$PSScriptRoot\shim_lint.ps1" -Soft

# 5b. Hub import-closure boundary. RMQHub.lean's docstring claims the hub layer
# depends on nothing RMQ-specific. That was true but enforced by nothing: both
# `lake build RMQHub` and hub_axiom_check.lean would still pass with
# `import RMQ.Core.Spec` added to ModelHub.lean. This makes the claim checked.
Invoke-Checker -Path "$PSScriptRoot\hub_closure_lint.ps1" -CheckerParams @{ SelfTest = $true } -Soft

# 6. Claim-drift policy mutations must enforce the full canonical-role/exponent
# category, contextual allowances, parser shapes, and allowance bypasses.
Invoke-Checker -Path "$PSScriptRoot\claim_drift_policy_regression.ps1" -Soft

# 7. Strict claim-policy violations block the aggregate gate.
#
# The self-test runs FIRST because the scan's own output is a contamination
# channel: a fresh-blind auditor is required to run this gate, and until
# 2026-08-16 the strict run printed 104 lines of PRIOR AUDIT REPORTS at them. The
# exclusion that closed it is unobservable from the exit code -- two earlier
# attempts were no-ops and both exited 0 -- so it is asserted, not assumed.
Invoke-Checker -Path "$PSScriptRoot\claim_drift_scan.ps1" -CheckerParams @{ SelfTest = $true } -Soft -Label 'claim_drift_scan.ps1 -SelfTest'

Invoke-Checker -Path "$PSScriptRoot\claim_drift_scan.ps1" -CheckerParams @{ Strict = $true } -Soft -Label 'claim_drift_scan.ps1 -Strict'

# 7a. An audit tag's annotation must not hand the next blind auditor the last
# round's verdict. The `audit-v1-rc-3` annotation carried the prior
# NOT_ACCEPTABLE, its finding IDs, and the assurance that every prior finding
# was correct -- and the prompt tells auditors to check the tag out by name.
Invoke-Checker -Path "$PSScriptRoot\tag_annotation_check.ps1" -CheckerParams @{ SelfTest = $true } -Soft

# 7b. Current-constant synchronization. The claim-drift policy guards every
# RETIRED constant and neither current one, so a moved bound would leave public
# surfaces asserting a stale numeral with the scan still reporting zero strict
# failures -- demonstrated by moving 210 to 214, where the scan exits 0 and this
# check exits 1. Lean is the source of truth here.
Invoke-Checker -Path "$PSScriptRoot\constant_sync_check.ps1" -CheckerParams @{ SelfTest = $true } -Soft

# 7c. Manuscript checker. `paper/` is part of the release candidate, but the
# aggregate gate never invoked its checker, so a citation, ledger-coverage,
# insertion-marker or claim-language failure in the manuscript could pass the
# advertised aggregate. Found by external audit 2026-08-09.
Invoke-Checker -Path "$PSScriptRoot\..\paper\check_paper.ps1" -CheckerParams @{ SelfTest = $true } -Soft -Label 'paper/check_paper.ps1'

# 8. The paper root must expose only the canonical reviewer-payload,
# readWord-only, derived-210 query topology; historical profiles remain in the
# explicit compatibility module.
Invoke-Checker -Path "$PSScriptRoot\paper_topology_lint.ps1" -Soft

Invoke-Checker -Path "$PSScriptRoot\paper_topology_lint_regression.ps1" -Soft

# 9. Whitespace / leftover merge markers.
git diff --check
if ($LASTEXITCODE -ne 0) { SoftFail "git diff --check found issues" }


# 9b. Every checker this gate advertises must have been reached, and no call site
# may bypass Invoke-Checker.
#
# THIS CHECK IS AN AST WALK, NOT A REGEX. Five consecutive audit rounds found the
# regex version inadequate, each time inside the fix for the previous round:
#
#   round  7  the pattern was `\[` -- an escaped literal -- and matched nothing
#   round  8  anchored at column 0, so an INDENTED call was invisible
#   round  9  the four controls were exactly the pattern's own envelope
#   round 10  ten more shapes missed, incl. `$script:rc = & ...`; controls again
#             the envelope; and it flagged its own fixtures and its own prose
#   round 11  nineteen controls collapsed to FOUR distinct consumed substrings --
#             a degenerate pattern dropping `$PSScriptRoot` missed 0 of 19 -- and
#             the comment stripper written to keep prose out was cutting SEVEN
#             lines of live code, counting only double quotes
#
# The last one is the tell. Adding controls cannot fix a control set that does
# not constrain the pattern, and stripping comments by hand cannot beat a parser
# that already knows what a comment is. So this asks PowerShell.
#
# `ParseInput` gives the same tokenisation the shell uses. A commented-out call is
# not a CommandAst. A path inside a string literal -- which is what the fixtures
# below are -- is not a CommandAst either, so the fixtures need no exclusion
# region: the previous version needed sentinels precisely because a regex cannot
# tell a call from a quotation of one.
$rawCallFixtures = @(
  '& "$PSScriptRoot\plain.ps1"',
  '  & "$PSScriptRoot\indented.ps1"',
  '. "$PSScriptRoot\dotsourced.ps1"',
  '& "$PSScriptRoot/forwardslash.ps1"',
  'if (Test-Path X) { & "$PSScriptRoot\one_line_if.ps1" }',
  '  if ($env:CI) { & "$PSScriptRoot\guarded.ps1" }',
  '$out = & "$PSScriptRoot\assigned.ps1"',
  'try { & "$PSScriptRoot\in_try.ps1" } catch {}',
  '& "${PSScriptRoot}\braced.ps1"',
  '$script:rc = & "$PSScriptRoot\scoped.ps1"',
  'if (Test-Path X) { $script:rc = & "$PSScriptRoot\scoped_if.ps1" }',
  '$rc = (& "$PSScriptRoot\paren.ps1")',
  '$rc = @(& "$PSScriptRoot\arraysub.ps1")',
  '$env:RC = & "$PSScriptRoot\envassign.ps1"',
  '$h.Rc = & "$PSScriptRoot\prop.ps1"',
  '$a, $b = & "$PSScriptRoot\multi.ps1"',
  '$all = @(1, (& "$PSScriptRoot\comma.ps1"))',
  '& "$PSScriptRoot\upper.PS1"',
  '& "$($PSScriptRoot)\interpolated.ps1"',
  '& (Join-Path $PSScriptRoot ''joined.ps1'')',
  '$tag = ''issue #12''; & "$PSScriptRoot\after_hash_in_string.ps1"',
  # These five carry NO `PSScriptRoot` literal, or use the BAREWORD form. The
  # previous set was 21 for 21 on that string, so it could not detect that a
  # substring test -- not the AST -- was what bounded coverage. The bareword
  # shape is the one `ci.yml` itself uses.
  '$repoRoot = $PSScriptRoot; & "$repoRoot\viarepo.ps1"',
  './scripts/bareword.ps1',
  './scripts/bareword.ps1 -Base "x" -Head y -Strict',
  '& ".\scripts\relative.ps1"',
  'pwsh -NoProfile -File "$PSScriptRoot\viashell.ps1"',
  '& "$env:CHECKER_DIR\fromenv.ps1"'
)

# `@(1, & "x")` is NOT in this list: it is a parse error in PowerShell -- "Missing
# expression after ','" -- so it cannot appear in a working script. A round-11
# finding named it as a missed shape; the parenthesised form below is the real
# one, and the fixture-parse assertion above is what surfaced the difference.

# Shapes that must NOT be reported. The first is the converted form; the rest are
# the prose and commented-out forms the regex version kept firing on, and the
# reason it needed a stripper at all.
$rawCallNonFixtures = @(
  'Invoke-Checker -Path "$PSScriptRoot\converted.ps1"',
  '# & "$PSScriptRoot\commented_out.ps1"',
  '  # was: if (x) { & "$PSScriptRoot\old.ps1" }',
  '$x = 1  # trailing; & "$PSScriptRoot\trailing.ps1"',
  'Write-Host "a `" b"  # & "$PSScriptRoot\escaped_quote.ps1"',
  '$doc = @"
& "$PSScriptRoot\inside_a_herestring.ps1"
"@'
)

function Get-RawCallSites {
  param([string]$Text)

  $parseErrors = $null
  $ast = [System.Management.Automation.Language.Parser]::ParseInput(
    $Text, [ref]$null, [ref]$parseErrors)
  if (@($parseErrors).Count -gt 0) { return $null }

  # What decides coverage is "does this command name a .ps1 file", NOT "does its
  # text contain the string PSScriptRoot".
  #
  # The previous version tested `$text -match 'PSScriptRoot'`, and every one of
  # its 21 fixtures contained that literal -- so the fixture set could not detect
  # the restriction, which is the same defect three earlier rounds found in the
  # regex. Measured, six working invocations were invisible: `& "$repoRoot\x.ps1"`
  # after `$repoRoot = $PSScriptRoot`, a bareword `./scripts/x.ps1` (the form
  # ci.yml itself uses), `& ($p)`, `& "$p"`, `& $arr[0]`, `& $h.Prop`, plus
  # `pwsh -File "...ps1"` and `Invoke-Expression`.
  $ps1Pattern = '\.ps1["'']?\s*$'
  $static = @()
  $dynamic = @()
  foreach ($cmd in $ast.FindAll({
      param($n) $n -is [System.Management.Automation.Language.CommandAst] }, $true)) {
    $elements = @($cmd.CommandElements)
    if ($elements.Count -eq 0) { continue }
    $head = $elements[0].Extent.Text

    # The sanctioned wrapper. Everything it dispatches goes through the guards.
    if ($head -ceq 'Invoke-Checker') { continue }

    # Any element naming a script -- catches the bareword form (operator
    # `Unknown`, which the previous version skipped entirely), `& "$anything.ps1"`
    # however the directory is spelled, and `pwsh -File "...ps1"`.
    $named = @($elements | Where-Object { $_.Extent.Text -match $ps1Pattern })
    if ($named.Count -gt 0) {
      $static += ($named | ForEach-Object { $_.Extent.Text })
      continue
    }

    # Unresolvable targets. `& $x`, `& $a[0]`, `& $h.P`, `& ($x)`, `& "$x"` and
    # `Invoke-Expression` cannot be decided statically. They are recorded so a NEW
    # one has to be looked at -- the previous version recorded only a bare
    # VariableExpressionAst, so four of those shapes reached neither bucket and
    # the "pinned rather than resolved" claim did not hold.
    if ($head -imatch '^(Invoke-Expression|iex)$') { $dynamic += $head; continue }
    # A BAREWORD target is a resolvable command name, not an unresolvable one:
    # `& lake env lean ...` was landing in the dynamic bucket and reported for
    # review, which is noise, not a finding. Only a non-literal target -- a
    # variable, an index, a property, a subexpression -- is undecidable here.
    if ($cmd.InvocationOperator -ne 'Unknown' -and
        -not ($elements[0] -is [System.Management.Automation.Language.StringConstantExpressionAst])) {
      $dynamic += $elements[0].Extent.Text
    }
  }
  return @{ Static = $static; Dynamic = $dynamic }
}

# The fixtures are asserted against the walk BEFORE it is trusted on real source.
foreach ($fixture in $rawCallFixtures) {
  $probe = Get-RawCallSites -Text $fixture
  if ($null -eq $probe) {
    SoftFail "the raw-call fixture [$fixture] does not parse; the walk cannot be exercised on it"
  } elseif ($probe.Static.Count -lt 1) {
    SoftFail "the raw-call walk does not see [$fixture]; it is blind to that shape"
  }
}
foreach ($nonFixture in $rawCallNonFixtures) {
  $probe = Get-RawCallSites -Text $nonFixture
  if ($null -ne $probe -and $probe.Static.Count -ne 0) {
    SoftFail "the raw-call walk reports [$nonFixture], which is not a call site"
  }
}
# Distinctness and coverage, not just count. Twenty-one identical copies of one
# fixture satisfied the old count pin -- structurally the same failure as
# `nineteen controls collapsed to four`, which is the defect this check exists
# to stop repeating. And at least four fixtures must be free of the
# `PSScriptRoot` literal, so a substring test can never silently become the
# bound again.
$distinctFixtures = @($rawCallFixtures | Sort-Object -Unique).Count
$withoutLiteral = @($rawCallFixtures | Where-Object { $_ -notmatch 'PSScriptRoot' }).Count
if ($rawCallFixtures.Count -lt 26 -or $distinctFixtures -ne $rawCallFixtures.Count -or
    $rawCallNonFixtures.Count -lt 6 -or $withoutLiteral -lt 4) {
  SoftFail ("the raw-call fixtures were weakened: {0} positive ({1} distinct, {2} free of the PSScriptRoot literal), {3} negative" -f `
    $rawCallFixtures.Count, $distinctFixtures, $withoutLiteral, $rawCallNonFixtures.Count)
}

$gateWalk = Get-RawCallSites -Text (Get-Content -Raw -LiteralPath $PSCommandPath)
if ($null -eq $gateWalk) {
  Fail "gate.ps1 does not parse; the raw-call walk cannot run"
}
if ($gateWalk.Static.Count -gt 0) {
  SoftFail ("{0} sub-checker call site(s) bypass Invoke-Checker and would score a non-running checker as PASS: {1}" -f `
    $gateWalk.Static.Count, ($gateWalk.Static -join '; '))
}

# Dynamic invocation is not statically decidable -- `& $someVariable` could be
# anything. It is not treated as a finding; it is pinned, so a NEW one has to be
# looked at. `$Path` is Invoke-Checker's own dispatch.
$allowedDynamic = @('$Path')   # Invoke-Checker's own dispatch, recorded as its extent text
$unexpectedDynamic = @($gateWalk.Dynamic | Sort-Object -Unique |
  Where-Object { $allowedDynamic -cnotcontains $_ })
if ($unexpectedDynamic.Count -gt 0) {
  SoftFail ("{0} dynamic invocation(s) this check cannot resolve statically: {1}. Add to the allowed list only after confirming the target is not a sub-checker." -f `
    $unexpectedDynamic.Count, ($unexpectedDynamic -join ', '))
}

#
# Invoke-Checker turns "the checker is gone" into a failure. This turns "the
# CALL to the checker is gone" into one too: an edit that deletes a stage, or
# hides one behind a condition that is false in CI, no longer shows up as a
# shorter green run. The list is the gate's advertised coverage, so it is
# written out rather than derived from the calls it is checking.
$expectedCheckers = @(
  'm1_certificate_mutation_regression.ps1 {m1_certificate_mutation_regression.ps1}',
  'eg_cp_stagea_replay.ps1 {eg_cp_stagea_replay.ps1}',
  'eg_cp_final_falsification_replay.ps1 {eg_cp_final_falsification_replay.ps1}',
  'project_skill_preflight_regression.ps1 {project_skill_preflight_regression.ps1}',
  'worker_prompt_preflight_regression.ps1 {worker_prompt_preflight_regression.ps1}',
  'design_decision_check_regression.ps1 {design_decision_check_regression.ps1}',
  'succinct_cost_lint.ps1 {succinct_cost_lint.ps1}',
  'shim_lint.ps1 {shim_lint.ps1}',
  'hub_closure_lint.ps1 {hub_closure_lint.ps1} [SelfTest=True]',
  'claim_drift_policy_regression.ps1 {claim_drift_policy_regression.ps1}',
  'claim_drift_scan.ps1 -SelfTest {claim_drift_scan.ps1} [SelfTest=True]',
  'claim_drift_scan.ps1 -Strict {claim_drift_scan.ps1} [Strict=True]',
  'tag_annotation_check.ps1 {tag_annotation_check.ps1} [SelfTest=True]',
  'constant_sync_check.ps1 {constant_sync_check.ps1} [SelfTest=True]',
  'paper_topology_lint.ps1 {paper_topology_lint.ps1}',
  'paper_topology_lint_regression.ps1 {paper_topology_lint_regression.ps1}',
  'paper/check_paper.ps1 {check_paper.ps1} [SelfTest=True]'
)
$notReached = @($expectedCheckers | Where-Object { $script:checkersRun -cnotcontains $_ })
if ($notReached.Count -gt 0) {
  SoftFail ("{0} advertised checker(s) were never invoked: {1}" -f $notReached.Count, ($notReached -join ', '))
}
$unadvertised = @($script:checkersRun | Where-Object { $expectedCheckers -cnotcontains $_ })
if ($unadvertised.Count -gt 0) {
  SoftFail ("{0} checker(s) ran that the roster does not list: {1}" -f $unadvertised.Count, ($unadvertised -join ', '))
}

Write-Host ("GATE COVERAGE: {0} of {1} advertised checkers invoked; {2} raw call site(s), {3} dynamic invocation(s)" -f `
  ($script:checkersRun.Count), ($expectedCheckers.Count), $gateWalk.Static.Count, $gateWalk.Dynamic.Count)
if ($script:issues.Count -gt 0) {
  Write-Host ""
  Write-Host "GATE FAIL: $($script:issues.Count) check(s) failed. ALL of them:"
  $n = 1
  foreach ($issue in $script:issues) {
    $first = ($issue -split "`n")[0]
    Write-Host "  [$n] $first"
    $n++
  }
  Write-Host ""
  Write-Host "Fix all of the above before re-running; they were collected in one pass."
  exit 1
}

Write-Host "GATE PASS"
exit 0

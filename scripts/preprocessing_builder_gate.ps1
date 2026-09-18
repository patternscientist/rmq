#!/usr/bin/env pwsh
<#
PRE1-BUILDER-REPLAY. Aggregate-gate checker that runs the PRE-1 builder replay
in FULL mode (no selector) as one owned bounded child of the current shell. A
timeout or output-limit hit is inconclusive and fails; the child must exit 0
and print `PRE-BUILDER-REPLAY: PASS mode=full`. Invoke-Checker runs this file
in-process and requires an explicit `exit`.
#>
[CmdletBinding()]
param(
  [string]$LakePath = '',
  # MEASURED-DEADLINE (AMEND-4: at least 2x the measured full run).
  #   measured full run (mode=full, 13/13 cases, 145 stages, 44 self-tests,
  #   pwsh 7.6.6, Windows 11 host shared with a running aggregate gate,
  #   2026-09-12, evidence .lake/preprocessing-builder-replay/
  #   20260912-222805-1503b7b95df0437092e1528cde924a47): 516.8 s wall
  #   (evidence directory creation to report.json), 507.7 s summed stages.
  #   default = 1800 s = 3.48 x measured; the extra margin over 2x covers host
  #   contention and a cold producer build on a CI runner. Record any later
  #   isolated gate-checker duration in BUILDER_STAGE_LOG.md and revise here only
  #   on evidence.
  #   2026-09-13 (registry now 15 cases): no full 15-case run is measured yet
  #   (the heavy-verification mutex was held; BUILDER_STAGE_LOG.md C3-9). The
  #   two added cases were measured focused: B14 55 s wall (C2-3), B15 74 s wall
  #   (C3-6). Projected full run 516.8 + 55 + 74 = 645.8 s; 1800 s = 2.79 x the
  #   projection, still above 2x, so the default is unchanged. Replace this
  #   projection by the measured 15-case (and later final) full run.
  #   2026-09-14 (registry 34 cases, commit 48702c2): measured full run
  #   (mode=full, 34/34 cases, 355 stages, 51 self-tests, pwsh 7.6.6, same host,
  #   no concurrent Lean process, evidence .lake/preprocessing-builder-replay/
  #   20260913-180035-2cfe7f588f944bdb9ba74b277e6ae0ba): 1535.87 s wall. The
  #   1800 s default was 1.17 x this run, below the 2x rule, so the default is
  #   raised to 3600 s = 2.34 x measured. The three Builder/Program.lean cases
  #   rebuild the literal pins (96-111 s producer stages each, twice per case).
  #   Revise again on the measured final-candidate run (never shortened).
  #   2026-09-14 (registry 52 cases, commit cb2ba2c): measured full run
  #   (mode=full, 52/52 cases, 541 stages, 54 self-tests, capstone baseline and
  #   validator stage included, pwsh 7.6.6, same host, no concurrent Lean
  #   process, evidence .lake/preprocessing-builder-replay/
  #   20260913-214415-41a250552f0945618bb586b67514d094): 4573.59 s wall, 4562.1 s
  #   summed stages. 3600 s was 0.79 x this run, so the default is raised to
  #   10800 s = 2.36 x measured. The eight foundation cases rebuild the builder
  #   closure twice each (94-105 s producer stages), and the validator's full
  #   executable run took 273.1 s.
  #   2026-09-17 (registry 55 cases, repair PRE-1-R2, commit f5d6128): measured
  #   full run (mode=full, 55/55 cases, 571 stages, 58 self-tests,
  #   capstone baseline and validator stage included, pwsh 7.6.6, same host,
  #   no concurrent Lean process, evidence .lake/preprocessing-builder-replay/
  #   20260917-132238-092add735903413b878e3fdfb7b1e977): 8674.82 s wall, 7999.1 s
  #   summed stages. The fail-closed verdict markers re-elaborate each consumer
  #   file, so every consumer stage runs about twice as long, and B53-B55 were
  #   added; 10800 s was 1.24 x this run, above the 60 percent line of
  #   coordinator ruling R-R2-1, so the default is raised to the measured
  #   duration times 2.5 rounded up to a multiple of 1800 s: 23400 s =
  #   2.70 x measured (never shortened).
  [int]$OuterDeadlineSeconds = 23400
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$script:RepositoryRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$script:TempRoot = Join-Path $script:RepositoryRoot '.lake/preprocessing-builder-gate'
$script:OutputLimitBytes = 16777216
$script:LastOutput = @()

try {
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $shell = (Get-Process -Id $PID).Path
  $replay = Join-Path $PSScriptRoot 'preprocessing_builder_replay.ps1'
  $arguments = @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $replay)
  if (-not [string]::IsNullOrWhiteSpace($LakePath)) { $arguments += @('-LakePath', $LakePath) }
  Write-Host "PRE1-BUILDER-REPLAY shell=$shell replay=$replay deadline=$($OuterDeadlineSeconds)s"
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments $arguments `
    -WorkingDirectory $script:RepositoryRoot -Stage 'builder-replay-full' `
    -DeadlineSeconds $OuterDeadlineSeconds -OutputLimitBytes $script:OutputLimitBytes `
    -TempRoot $script:TempRoot
  $script:LastOutput = @($result.Output)
  if ($result.TimedOut -or $result.OutputLimitExceeded) {
    throw "inconclusive after $($result.DurationSeconds)s of $($OuterDeadlineSeconds)s; timeout=$($result.TimedOut), outputLimit=$($result.OutputLimitExceeded)"
  }
  if ($result.ExitCode -ne 0) {
    throw "replay exited $($result.ExitCode) after $($result.DurationSeconds)s"
  }
  $passLine = @($result.Output | Where-Object { $_ -clike 'PRE-BUILDER-REPLAY: PASS mode=full*' })
  if ($passLine.Count -ne 1) {
    throw "replay exited 0 without exactly one 'PRE-BUILDER-REPLAY: PASS mode=full' line (found $($passLine.Count))"
  }
  Write-Host $passLine[0]
  Write-Host "PRE1-BUILDER-REPLAY duration=$($result.DurationSeconds)s"
} catch {
  Write-Host "PRE1-BUILDER-REPLAY FAIL: $($_.Exception.Message)"
  foreach ($line in $script:LastOutput) { Write-Host "  | $line" }
  exit 1
}
Write-Host 'PRE1-BUILDER-REPLAY PASS'
exit 0

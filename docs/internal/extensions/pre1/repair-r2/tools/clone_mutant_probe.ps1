# PRE-1-R2 development probe in the disposable clone (never the repair worktree):
# apply one registry-shaped fragment edit, build the targets, elaborate the
# consumer, record exit, error lines of the consumer file and marker lines,
# restore the exact bytes and rebuild. Cases come from a JSON list.
param(
  [Parameter(Mandatory)][string]$Clone,
  [Parameter(Mandatory)][string]$CasesJson,
  [Parameter(Mandatory)][string]$OutJson,
  [Parameter(Mandatory)][string]$OwnedTree,
  [int]$DeadlineSeconds = 3600
)
$ErrorActionPreference = 'Stop'
. $OwnedTree
$utf8 = [Text.UTF8Encoding]::new($false)
$lake = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe'
$temp = Join-Path $Clone '.lake/r2-probe-temp'
function Sha([byte[]]$b) { $s = [Security.Cryptography.SHA256]::Create(); try { [BitConverter]::ToString($s.ComputeHash($b)).Replace('-', '') } finally { $s.Dispose() } }
function Run([string[]]$Arguments, [string]$Stage) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $lake -Arguments $Arguments -WorkingDirectory $Clone -Stage $Stage `
    -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 33554432 -TempRoot $temp -Environment @{ LEAN_NUM_THREADS = '1' }
}
function Errors([object]$r, [string]$FileName) {
  $lines = @($r.Output | ForEach-Object { [string]$_ })
  $pattern = [regex]::Escape($FileName) + ':(\d+):(\d+): error: ?(.*)$'
  return @($lines | Where-Object { $_ -match $pattern } | ForEach-Object { if ($_ -match $pattern) { [pscustomobject]@{ file = $FileName; line = [int]$Matches[1]; head = $(if ($Matches[3].Length -gt 100) { $Matches[3].Substring(0, 100) } else { $Matches[3] }) } } })
}
$cases = Get-Content -LiteralPath $CasesJson -Raw | ConvertFrom-Json
$results = [ordered]@{ clone = $Clone; head = (& git -C $Clone rev-parse HEAD); cases = @() }
foreach ($c in $cases) {
  $path = Join-Path $Clone ([string]$c.path)
  $original = [IO.File]::ReadAllBytes($path)
  $text = $utf8.GetString($original)
  $before = ([string]$c.before).Replace("`r`n", "`n"); $after = ([string]$c.after).Replace("`r`n", "`n")
  if ($text.Contains("`r`n")) { $before = $before.Replace("`n", "`r`n"); $after = $after.Replace("`n", "`r`n") }
  $at = $text.IndexOf($before, [StringComparison]::Ordinal)
  if ($at -lt 0 -or $text.IndexOf($before, $at + $before.Length, [StringComparison]::Ordinal) -ge 0) { throw "$($c.id): fragment must occur once" }
  $mutant = $text.Substring(0, $at) + $after + $text.Substring($at + $before.Length)
  $entry = [ordered]@{ id = [string]$c.id; path = [string]$c.path; originalSha256 = Sha $original }
  try {
    [IO.File]::WriteAllBytes($path, $utf8.GetBytes($mutant))
    $p = Run (@('build') + @($c.targets)) "$($c.id)-producer"
    $entry.producer = [ordered]@{ exit = $p.ExitCode; seconds = $p.DurationSeconds; timedOut = $p.TimedOut
      errors = @(@($p.Output | ForEach-Object { [string]$_ }) | Where-Object { $_ -match 'error' } | ForEach-Object { if ($_.Length -gt 160) { $_.Substring(0, 160) } else { $_ } } | Select-Object -First 12) }
    if ($p.ExitCode -eq 0) {
      $r = Run @('env', 'lean', [string]$c.consumer) "$($c.id)-consumer"
      $errs = Errors $r ([IO.Path]::GetFileName([string]$c.consumer))
      $entry.consumer = [ordered]@{ exit = $r.ExitCode; seconds = $r.DurationSeconds; timedOut = $r.TimedOut
        markerLines = @(@($r.Output | ForEach-Object { [string]$_ }) | Where-Object { $_.Contains([string]$c.marker) }).Count
        errorLines = @($errs | ForEach-Object { $_.line } | Sort-Object -Unique); errorHeads = @($errs | ForEach-Object { "$($_.line): $($_.head)" }) }
    }
  } finally {
    [IO.File]::WriteAllBytes($path, $original)
    $entry.restoredExact = ((Sha ([IO.File]::ReadAllBytes($path))) -eq $entry.originalSha256)
    $rb = Run (@('build') + @($c.targets)) "$($c.id)-restore"
    $entry.restoreBuild = [ordered]@{ exit = $rb.ExitCode; seconds = $rb.DurationSeconds }
  }
  $results.cases += [pscustomobject]$entry
  [IO.File]::WriteAllText($OutJson, ($results | ConvertTo-Json -Depth 8), $utf8)
}
$results.statusAfter = @(& git -C $Clone status --porcelain)
[IO.File]::WriteAllText($OutJson, ($results | ConvertTo-Json -Depth 8), $utf8)
Write-Output "CLONE-PROBE: done"

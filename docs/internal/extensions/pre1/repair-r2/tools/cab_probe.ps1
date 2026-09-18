# PRE-1-R2 reproduction of the PRE-1-A2 capstone sibling-producer probes CAB2 and
# CAB4 in a disposable clone (never the repair worktree). Each probe edits
# Capstone.lean in the clone, builds the capstone, elaborates the capstone typed
# consumer, restores the exact bytes and rebuilds; outcomes go to -OutJson.
param(
  [Parameter(Mandatory)][string]$Clone,
  [Parameter(Mandatory)][string]$OutJson,
  [Parameter(Mandatory)][string]$OwnedTree,
  [int]$DeadlineSeconds = 1800
)
$ErrorActionPreference = 'Stop'
. $OwnedTree
$utf8 = [Text.UTF8Encoding]::new($false)
$lake = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe'
$capstonePath = Join-Path $Clone 'RMQ/Core/WordRAM/Construction/Capstone.lean'
$temp = Join-Path $Clone '.lake/r2-cab-temp'
function Sha([byte[]]$b) { $s = [Security.Cryptography.SHA256]::Create(); try { [BitConverter]::ToString($s.ComputeHash($b)).Replace('-', '') } finally { $s.Dispose() } }
function Run([string[]]$Arguments, [string]$Stage) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $lake -Arguments $Arguments -WorkingDirectory $Clone -Stage $Stage `
    -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 33554432 -TempRoot $temp -Environment @{ LEAN_NUM_THREADS = '1' }
}
function Summary([object]$r, [string]$Marker) {
  $lines = @($r.Output | ForEach-Object { [string]$_ })
  $errs = @($lines | Where-Object { $_ -match 'PreprocessingContract\.lean:(\d+):\d+: error' } | ForEach-Object { if ($_ -match 'PreprocessingContract\.lean:(\d+):\d+: error: (.*)$') { [pscustomobject]@{ line = [int]$Matches[1]; head = $Matches[2] } } })
  return [ordered]@{ exit = $r.ExitCode; seconds = $r.DurationSeconds; timedOut = $r.TimedOut
    markerLines = @($lines | Where-Object { $_.Contains($Marker) }).Count
    errorLines = @($errs | ForEach-Object { $_.line } | Sort-Object -Unique)
    maxRecursionErrors = @($errs | Where-Object { $_.head.Contains('maximum recursion depth has been reached') }).Count
    errorHeads = @($errs | ForEach-Object { $h = $_.head; if ($h.Length -gt 100) { $h.Substring(0, 100) } else { $h } } | Sort-Object -Unique) }
}
$probes = [ordered]@{
  CAB2 = @(
    @('  queryOnEmitted : ∀ xs : List Int, PackedQueryOn (efficientBuild xs) xs', '  queryOnEmitted : ∀ xs : List Int, PackedQueryOn (buildMemory xs) xs'),
    @('  queryOnEmitted := packedQueryOn_efficientBuild', '  queryOnEmitted := fun xs => packedQueryOn_of_eq xs _ rfl'))
  CAB4 = @(
    @('  headerUseWord : HeaderUse builderProgramWord', '  headerUseWord : HeaderUse builderProgram'),
    @('  headerUseWord := Proof.builderProgramWord_headerUse', '  headerUseWord := Proof.builderProgram_headerUse'))
}
$results = [ordered]@{ clone = $Clone; head = (& git -C $Clone rev-parse HEAD); probes = [ordered]@{} }
foreach ($name in $probes.Keys) {
  $original = [IO.File]::ReadAllBytes($capstonePath)
  $text = $utf8.GetString($original)
  $crlf = $text.Contains("`r`n")
  foreach ($pair in $probes[$name]) {
    $before = $pair[0]; $after = $pair[1]
    $needle = if ($crlf) { $before + "`r`n" } else { $before + "`n" }
    $count = ([regex]::Matches($text, [regex]::Escape($needle))).Count
    if ($count -ne 1) { throw "$name fragment occurs $count times: $before" }
    $text = $text.Replace($needle, $(if ($crlf) { $after + "`r`n" } else { $after + "`n" }))
  }
  $entry = [ordered]@{ originalSha256 = Sha $original }
  try {
    [IO.File]::WriteAllBytes($capstonePath, $utf8.GetBytes($text))
    $entry.mutantSha256 = Sha ([IO.File]::ReadAllBytes($capstonePath))
    $p = Run @('build', 'RMQ.Core.WordRAM.Construction.Capstone') "$name-producer"
    $entry.producer = [ordered]@{ exit = $p.ExitCode; seconds = $p.DurationSeconds; timedOut = $p.TimedOut }
    if ($p.ExitCode -eq 0) {
      $c = Run @('env', 'lean', 'RMQ/Validation/PreprocessingContract.lean') "$name-consumer"
      $entry.consumer = Summary $c 'PRE1-CAPSTONE-TYPED-CONSUMERS PASS'
    }
  } finally {
    [IO.File]::WriteAllBytes($capstonePath, $original)
    $entry.restoredSha256 = Sha ([IO.File]::ReadAllBytes($capstonePath))
    $entry.restoredExact = ($entry.restoredSha256 -eq $entry.originalSha256)
    $r = Run @('build', 'RMQ.Core.WordRAM.Construction.Capstone') "$name-restore"
    $entry.restoreBuild = [ordered]@{ exit = $r.ExitCode; seconds = $r.DurationSeconds }
  }
  $results.probes[$name] = $entry
}
$c0 = Run @('env', 'lean', 'RMQ/Validation/PreprocessingContract.lean') 'R0-consumer'
$results.R0 = Summary $c0 'PRE1-CAPSTONE-TYPED-CONSUMERS PASS'
$results.statusAfter = @(& git -C $Clone status --porcelain)
[IO.File]::WriteAllText($OutJson, ($results | ConvertTo-Json -Depth 8), $utf8)
Write-Output "CAB-PROBE: done"

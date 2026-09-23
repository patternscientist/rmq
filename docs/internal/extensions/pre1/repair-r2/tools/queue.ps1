# Run a list of heavy steps sequentially under Global\RMQHeavyVerification.
param([Parameter(Mandatory)][string]$StepsJson, [Parameter(Mandatory)][string]$OutJson)
$ErrorActionPreference = 'Stop'
$utf8 = [Text.UTF8Encoding]::new($false)
$wt = 'C:/Users/poin/Documents/RMQ/.claude/worktrees/pre1-r2-consumer-markers'
. (Join-Path $wt 'scripts/owned_process_tree.ps1')
$steps = Get-Content -LiteralPath $StepsJson -Raw | ConvertFrom-Json
$summary = [ordered]@{ requested = (Get-Date).ToString('o'); mutex = 'Global\RMQHeavyVerification'; mutexWaitSeconds = $null; steps = @(); status = 'WAITING' }
function Save { [IO.File]::WriteAllText($OutJson, ($summary | ConvertTo-Json -Depth 8), $utf8) }
Save
$mutex = [System.Threading.Mutex]::new($false, 'Global\RMQHeavyVerification')
$owned = $false
try {
  $sw = [Diagnostics.Stopwatch]::StartNew()
  try { $owned = $mutex.WaitOne() } catch [System.Threading.AbandonedMutexException] { $owned = $true }
  $summary.mutexWaitSeconds = [Math]::Round($sw.Elapsed.TotalSeconds, 1)
  $summary.acquired = (Get-Date).ToString('o'); $summary.status = 'RUNNING'; Save
  foreach ($step in $steps) {
    $entry = [ordered]@{ label = [string]$step.Label; command = [string]$step.FilePath; arguments = @($step.Arguments)
      workingDirectory = [string]$step.WorkingDirectory; deadlineSeconds = [int]$step.DeadlineSeconds; start = (Get-Date).ToString('o') }
    $envTable = @{}
    if ($null -ne $step.Environment) { foreach ($p in $step.Environment.PSObject.Properties) { $envTable[$p.Name] = [string]$p.Value } }
    try {
      $r = Invoke-RMQOwnedBoundedProcess -FilePath ([string]$step.FilePath) -Arguments @([string[]]$step.Arguments) `
        -WorkingDirectory ([string]$step.WorkingDirectory) -Stage ([string]$step.Label) -DeadlineSeconds ([int]$step.DeadlineSeconds) `
        -OutputLimitBytes 67108864 -TempRoot (Join-Path (Split-Path $OutJson) 'queue-proc') -Environment $envTable
      $entry.exit = $r.ExitCode; $entry.seconds = $r.DurationSeconds; $entry.timedOut = $r.TimedOut; $entry.outputLimitExceeded = $r.OutputLimitExceeded
      [IO.File]::WriteAllText((Join-Path (Split-Path $OutJson) ($step.Label + '.log')), ((@($r.Output) -join "`n") + "`n"), $utf8)
    } catch { $entry.error = $_.Exception.Message }
    $entry.end = (Get-Date).ToString('o')
    $summary.steps += [pscustomobject]$entry
    Save
  }
  $summary.status = 'DONE'
} finally {
  $summary.released = (Get-Date).ToString('o')
  if ($owned) { $mutex.ReleaseMutex() }
  $mutex.Dispose()
  Save
}

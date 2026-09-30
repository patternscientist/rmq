[CmdletBinding()]
param([Parameter(Mandatory=$true)][string]$SpecPath)
# LIFE-1-R3 bounded heavy-command wrapper. It acquires the named host mutexes in
# a fixed order (global first), launches exactly one owned process tree through
# the unchanged scripts/owned_process_tree.ps1 helper with a positive deadline,
# and always writes RESULT.json. Mutex release and the result write each run in
# their own guard so neither can replace the stage error. LIFE-1-R4: a failed
# RESULT.json write fails the run (exit 1, no success line) after any earlier
# stage or cleanup error has been reported.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$spec=[IO.File]::ReadAllText($SpecPath,$utf8)|ConvertFrom-Json
if($spec.name -cnotmatch '^[a-z0-9][a-z0-9-]*$'){throw 'R3-HEAVY: exact lowercase name required'}
if($spec.deadline -lt 1 -or $spec.deadline -gt 86400){throw 'R3-HEAVY: positive deadline required'}
$known=@{global='Global\RMQHeavyVerification';lane='Local\RMQLifecycleImplementationHeavy20260920'}
$order=@('global','lane')
foreach($m in @($spec.mutexes)){if(-not $known.ContainsKey([string]$m)){throw 'R3-HEAVY: unknown mutex'}}
$out=[IO.Path]::GetFullPath([string]$spec.out)
$allowed=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $out.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $out)){throw 'R3-HEAVY: fresh owned output under .lake required'}
[void][IO.Directory]::CreateDirectory($out)
$held=[Collections.Generic.List[object]]::new()
$waits=[ordered]@{}
$r=$null;$stageError=$null;$cleanupErrors=[Collections.Generic.List[string]]::new()
$durableFailed=$false
$started=[DateTime]::UtcNow
try {
  . (Join-Path $repo 'scripts/owned_process_tree.ps1')
  foreach($name in $order){
    if(@($spec.mutexes) -notcontains $name){continue}
    $m=[Threading.Mutex]::new($false,$known[$name])
    $watch=[Diagnostics.Stopwatch]::StartNew()
    $got=$false
    try{$got=$m.WaitOne([int]$spec.mutexWaitMilliseconds)}catch [Threading.AbandonedMutexException]{$got=$true}
    $watch.Stop()
    $waits[$name]=[Math]::Round($watch.Elapsed.TotalSeconds,3)
    if(-not $got){$m.Dispose();throw ('R3-HEAVY: mutex wait expired '+$known[$name])}
    $held.Add([pscustomobject]@{name=$name;mutex=$m})
  }
  $environment=@{}
  if($null -ne $spec.environment){foreach($p in $spec.environment.PSObject.Properties){$environment[$p.Name]=[string]$p.Value}}
  $r=Invoke-RMQOwnedBoundedProcess -FilePath ([string]$spec.file) -Arguments @($spec.arguments|ForEach-Object {[string]$_}) `
    -WorkingDirectory ([string]$spec.cwd) -Stage ([string]$spec.name) -DeadlineSeconds ([int]$spec.deadline) `
    -OutputLimitBytes 67108864 -TempRoot (Join-Path $out 'process') -Environment $environment
  [IO.File]::WriteAllText((Join-Path $out 'stdout.returned-lines.txt'),(@($r.StandardOutput) -join "`n"),$utf8)
  [IO.File]::WriteAllText((Join-Path $out 'stderr.returned-lines.txt'),(@($r.StandardError) -join "`n"),$utf8)
} catch {$stageError=$_.Exception.Message}
finally {
  for($i=$held.Count-1;$i -ge 0;$i--){
    try{$held[$i].mutex.ReleaseMutex()}catch{$cleanupErrors.Add('release '+$held[$i].name+': '+$_.Exception.Message)}
    try{$held[$i].mutex.Dispose()}catch{$cleanupErrors.Add('dispose '+$held[$i].name+': '+$_.Exception.Message)}
  }
  $record=[ordered]@{schema='life1-r3-heavy-v1';name=$spec.name;spec=$spec;host=[Environment]::MachineName
    shell=(Get-Process -Id $PID).Path;psVersion=$PSVersionTable.PSVersion.ToString()
    startedUtc=$started.ToString('o');finishedUtc=[DateTime]::UtcNow.ToString('o')
    mutexWaitSeconds=$waits;stageError=$stageError;cleanupErrors=@($cleanupErrors.ToArray());result=$r}
  try{[IO.File]::WriteAllText((Join-Path $out 'RESULT.json'),($record|ConvertTo-Json -Depth 30),$utf8)}
  catch{$durableFailed=$true;[Console]::Error.WriteLine('R3-HEAVY: RESULT.json write failed: '+$_.Exception.Message)}
}
if($null -ne $stageError){[Console]::Error.WriteLine('R3-HEAVY: '+$stageError);exit 1}
if($cleanupErrors.Count){foreach($e in $cleanupErrors){[Console]::Error.WriteLine('R3-HEAVY cleanup: '+$e)};exit 1}
if($durableFailed){[Console]::Error.WriteLine('R3-HEAVY: no durable result for '+$spec.name+'; child exit='+$r.ExitCode+' timeout='+$r.TimedOut);exit 1}
Write-Output ('R3-HEAVY '+$spec.name+' exit='+$r.ExitCode+' seconds='+$r.DurationSeconds+' timeout='+$r.TimedOut+' overflow='+$r.OutputLimitExceeded+' evidence='+$out)
if($r.TimedOut -or $r.OutputLimitExceeded){exit 2}
exit $r.ExitCode

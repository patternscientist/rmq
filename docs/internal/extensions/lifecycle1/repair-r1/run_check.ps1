[CmdletBinding()]
param([Parameter(Mandatory=$true)][string]$SpecPath)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$spec=Get-Content -LiteralPath $SpecPath -Raw|ConvertFrom-Json
$out=Join-Path $root ('.lake/repair-r1/checks/'+$spec.name)
if(Test-Path -LiteralPath $out){throw 'Check name already exists; retain earlier attempt'}
[void][IO.Directory]::CreateDirectory($out)
$utf8=[Text.UTF8Encoding]::new($false)
# LIFE-1-R3: once the owned check directory exists, every exit path writes
# result.json. The stage error, the child outcome, each independent source pin
# comparison and each cleanup error are recorded separately.
$mutex=$null;$locked=$false;$r=$null
$sourcePaths=@('scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1',
    'scripts/lifecycle_dependency_replay.ps1','scripts/owned_process_tree.ps1',
    'scripts/lifecycle_dependency_cases.json','RMQ/Validation/PackedLifecycle.lean',
    'RMQ/Validation/LifecycleContract.lean','scripts/lifecycle_provenance_contract.lean',
    'lean-toolchain','lakefile.toml','.lake/build/bin/rmq_lifecycle_validate.exe')
$sources=[ordered]@{}
$absentSources=[Collections.Generic.List[string]]::new()
$captured=$false
$stageError=$null;$stageRecord=$null;$childFailure=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$exitCode=1
$durableFailed=$false
try {
  foreach($p in $sourcePaths) {
    if(Test-Path -LiteralPath (Join-Path $root $p)){$sources[$p]=(Get-FileHash -LiteralPath (Join-Path $root $p) -Algorithm SHA256).Hash}
    else{$absentSources.Add($p)}
  }
  $captured=$true
  . (Join-Path $root 'scripts/owned_process_tree.ps1')
  if($spec.mutex){
    $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
    try{$locked=$mutex.WaitOne(7200000)}catch [Threading.AbandonedMutexException]{$locked=$true}
    if(-not $locked){throw 'Heavy mutex wait expired'}
  }
  $environment=@{LEAN_NUM_THREADS='1'}
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $spec.file -Arguments @($spec.arguments) -WorkingDirectory $root `
    -Stage $spec.name -DeadlineSeconds $spec.deadline -OutputLimitBytes 16777216 -TempRoot $out -Environment $environment
  # LIFE-1-R4: a malformed or unowned helper result is a harness failure, never a child outcome.
  if($null -eq $r -or $r.ExitCode -isnot [int] -or @('kill-on-close-job','setsid-process-group') -cnotcontains [string]$r.Ownership -or
     (-not $r.TimedOut -and -not $r.OutputLimitExceeded -and @($r.TerminatedIds).Count -ne 0)){throw 'R1-CHECK: owned child result malformed or unowned'}
  [IO.File]::WriteAllText((Join-Path $out 'stdout.txt'),($r.StandardOutput -join "`n"),$utf8)
  [IO.File]::WriteAllText((Join-Path $out 'stderr.txt'),($r.StandardError -join "`n"),$utf8)
  if($r.TimedOut -or $r.OutputLimitExceeded){$childFailure='R1-CHECK: child timed out or exceeded its output limit';$exitCode=2}
  else{$exitCode=$r.ExitCode;if($r.ExitCode -ne 0){$childFailure='R1-CHECK: child exit '+$r.ExitCode}}
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  # Independent integrity: every entry source pin (present or absent) in its own
  # guard, re-checked while the heavy slot is still held (LIFE-1-R4).
  foreach($p in $sourcePaths){
    $entry=if($sources.Contains($p)){$sources[$p]}else{$null}
    $final=$null;$status='not-captured'
    try {
      if($sources.Contains($p)){
        $status='verified'
        $final=(Get-FileHash -LiteralPath (Join-Path $root $p) -Algorithm SHA256).Hash
        if($final -cne $entry){$status='changed';$integrityErrors.Add('R1-CHECK-INTEGRITY: source changed '+$p)}
      } elseif($captured -and $absentSources.Contains($p)){
        $status='absent-verified'
        if(Test-Path -LiteralPath (Join-Path $root $p)){$status='appeared';$integrityErrors.Add('R1-CHECK-INTEGRITY: absent source appeared '+$p)}
      }
    } catch {$status='unreadable-final';$integrityErrors.Add('R1-CHECK-INTEGRITY: final hash failed '+$p+': '+$_.Exception.Message)}
    $pinChecks.Add([ordered]@{path=$p;entrySha256=$entry;finalSha256=$final;status=$status})
  }
  if($locked){try{$mutex.ReleaseMutex()}catch{$cleanupErrors.Add('R1-CHECK-CLEANUP: mutex release: '+$_.Exception.Message)}}
  if($null -ne $mutex){try{$mutex.Dispose()}catch{$cleanupErrors.Add('R1-CHECK-CLEANUP: mutex dispose: '+$_.Exception.Message)}}
  if($null -ne $stageError){$exitCode=1}
  elseif($integrityErrors.Count -or $cleanupErrors.Count){$exitCode=3}
  # LIFE-1-R4: the verdict is the overall verdict; a failed, timed-out or
  # over-limit child fails it exactly as a stage, integrity or cleanup error does.
  $failed=$null -ne $stageError -or $null -ne $childFailure -or $integrityErrors.Count -ne 0 -or $cleanupErrors.Count -ne 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($failed){'fail'}else{'pass'})
    stageError=$stageError;childFailure=$childFailure
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    entryPinCount=$sources.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count
    exitCode=$exitCode;exitSemantics='child exit when the stage completed and integrity is intact; 2 timeout/output limit; 3 integrity or cleanup failure; 1 harness stage exception, malformed/unowned child result, or a durable-result write failure that would otherwise exit 0'}
  try {
    [IO.File]::WriteAllText((Join-Path $out 'result.json'),([ordered]@{spec=$spec;entrySources=$sources;absentSources=@($absentSources.ToArray());
      shell=(Get-Process -Id $PID).Path;version=$PSVersionTable.PSVersion.ToString();dotnet=[Environment]::Version.ToString();
      result=$r;finalization=$finalization;streamRepresentation='unchanged helper returned nonempty lines'}|ConvertTo-Json -Depth 30),$utf8)
  } catch {$durableFailed=$true;[Console]::Error.WriteLine('R1-CHECK: durable result write failed: '+$_.Exception.Message)}
}
if($null -ne $r){Write-Output ($spec.name+' exit='+$r.ExitCode+' seconds='+$r.DurationSeconds+' timeout='+$r.TimedOut+' evidence='+$out)}
foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
if($null -ne $stageRecord){throw $stageRecord}
# LIFE-1-R4: without a durable result the run never reports success.
if($durableFailed -and $exitCode -eq 0){$exitCode=1}
exit $exitCode

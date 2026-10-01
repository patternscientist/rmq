param([switch]$Worker,[string]$RunDirectory='')
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
if([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT){throw 'OWNED-CONTROL: Windows job certification required'}
$allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake/lifecycle-native1/owned-controls')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
$shell=(Get-Process -Id $PID).Path
function Quote-DC([string]$Text){return "'"+$Text.Replace("'","''")+"'"}
function Write-DCJson([string]$Path,$Value){[IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 28),$utf8)}
function Check-DCIntegrity($Pins){
  $errors=[Collections.Generic.List[string]]::new();$checked=[Collections.Generic.List[object]]::new()
  foreach($pin in $Pins){
    try{
      $now=Get-LN1Pin $pin.path;$checked.Add($now)
      if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}
    }catch{$errors.Add($_.Exception.Message)}
  }
  return @{attempted=$true;success=($errors.Count -eq 0);checked=@($checked.ToArray());errors=@($errors.ToArray())}
}
function Remove-DCScratch([string]$Path,[string]$Run){
  $full=[IO.Path]::GetFullPath($Path)
  $prefix=[IO.Path]::GetFullPath((Join-Path $Run 'disposable')).TrimEnd('\','/')
  if(($full -cne $prefix) -and -not $full.StartsWith($prefix+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)){
    throw 'OWNED-CONTROL: cleanup outside owned disposable directory'
  }
  if(-not $prefix.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase)){throw 'OWNED-CONTROL: cleanup outside owned evidence root'}
  if([IO.Directory]::Exists($full)){
    $entries=@(Get-Item -LiteralPath $full)+@(Get-ChildItem -LiteralPath $full -Recurse -Force)
    foreach($entry in $entries){if($entry.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'OWNED-CONTROL: cleanup refuses reparse point'}}
    Remove-Item -LiteralPath $full -Recurse -Force
  }
  if([IO.Directory]::Exists($full)){throw 'OWNED-CONTROL: scratch remains'}
  return @{attempted=$true;success=$true;removed=$full}
}
function Test-DCPartialSetup([string]$Run,$Pins,[bool]$ChangePin){
  $id=if($ChangePin){'partial-setup-changed-pin'}else{'partial-setup-intact'}
  $scratch=Join-Path (Join-Path $Run 'disposable') $id
  $casePins=[Collections.Generic.List[object]]::new();foreach($pin in $Pins){$casePins.Add($pin)}
  $row=[ordered]@{id=$id;passed=$false;setupComplete=$false;semanticChildStarted=$false;
    caught=$null;expectedSetupError='OWNED-CONTROL: forced partial setup';integrity=$null;cleanup=$null}
  try{
    [void][IO.Directory]::CreateDirectory($scratch)
    $fixture=Join-Path $scratch 'allocated-before-error.txt'
    [IO.File]::WriteAllText($fixture,'original',$utf8);$casePins.Add((Get-LN1Pin $fixture))
    $row.initialFixture=$casePins[$casePins.Count-1]
    if($ChangePin){[IO.File]::WriteAllText($fixture,'changed',$utf8)}
    throw $row.expectedSetupError
  }catch{$row.caught=$_.Exception.Message}
  finally{
    # Independent blocks: a pin mismatch must never suppress scratch cleanup.
    try{$row.integrity=Check-DCIntegrity @($casePins.ToArray())}
    catch{$row.integrity=@{attempted=$true;success=$false;errors=@($_.Exception.Message)}}
    try{$row.cleanup=Remove-DCScratch $scratch $Run}
    catch{$row.cleanup=@{attempted=$true;success=$false;error=$_.Exception.Message}}
  }
  $expectedErrors=if($ChangePin){@('changed pin '+$fixture)}else{@()}
  if($row.caught -cne $row.expectedSetupError -or -not $row.cleanup.success -or
      $row.integrity.success -ne (-not $ChangePin) -or
      (@($row.integrity.errors) -join '|') -cne ($expectedErrors -join '|')){
    throw ('OWNED-CONTROL: partial-setup finalizers differ '+$id)
  }
  $row.passed=$true;return $row
}

if($Worker){
  $run=[IO.Path]::GetFullPath($RunDirectory)
  if(-not $run.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or
    -not [IO.Directory]::Exists($run) -or -not [IO.File]::Exists((Join-Path $run 'PLAN.json'))){
    throw 'OWNED-CONTROL: worker requires an existing owned plan'
  }
  $plan=[IO.File]::ReadAllText((Join-Path $run 'PLAN.json'),$utf8)|ConvertFrom-Json
  $pins=@($plan.sourcePins);$rows=[Collections.Generic.List[object]]::new()
  $result=[ordered]@{schema='lifecycle-native1-owned-descendant-worker-v1';success=$false;
    controls=@();failure=$null;integrity=$null;cleanup=$null;innerCapture=$null}
  $scratch=Join-Path $run 'disposable'
  try{
    [void][IO.Directory]::CreateDirectory($scratch)
    $rootPidPath=Join-Path $run 'sleep-root.pid';$childPidPath=Join-Path $run 'sleep-child.pid'
    $childSelfPath=Join-Path $run 'sleep-child-self.pid'
    $descendant=Join-Path $run 'descendant.ps1';$sleeper=Join-Path $run 'sleep-root.ps1'
    $descendantText='[IO.File]::WriteAllText('+(Quote-DC $childSelfPath)+',[string]$PID)'+"`nStart-Sleep -Seconds 120`n"
    [IO.File]::WriteAllText($descendant,$descendantText,$utf8)
    # Start-Process quotes the one path-containing argument explicitly. The
    # descendant inherits the same owned Windows jobs; it opens no visible UI.
    $childArgument='"'+$descendant.Replace('"','\"')+'"'
    $sleeperText='[IO.File]::WriteAllText('+(Quote-DC $rootPidPath)+',[string]$PID)'+"`n"+
      '$ownedChild=Start-Process -FilePath '+(Quote-DC $shell)+' -ArgumentList @('+
      "'-NoLogo','-NoProfile','-File',"+(Quote-DC $childArgument)+') -WindowStyle Hidden -PassThru'+"`n"+
      '[IO.File]::WriteAllText('+(Quote-DC $childPidPath)+',[string]$ownedChild.Id)'+"`n"+
      'while(-not [IO.File]::Exists('+(Quote-DC $childSelfPath)+')){Start-Sleep -Milliseconds 10}'+"`n"+
      '[Console]::Out.Write("OWNED-DESCENDANT ROOT READY`n")'+"`nStart-Sleep -Seconds 120`n"
    [IO.File]::WriteAllText($sleeper,$sleeperText,$utf8)
    $result.fixtures=@(Get-LN1Pin $sleeper;Get-LN1Pin $descendant)
    $capture=Invoke-LNStreamCapture $root $shell @('-NoLogo','-NoProfile','-File',$sleeper) $root (Join-Path $run 'inner') 8 'owned-descendant-inner'
    $result.innerCapture=$capture
    if(-not $capture.launcher.TimedOut -or $capture.launcher.OutputLimitExceeded -or
      $capture.launcher.ExitCode -ne -1 -or $null -ne $capture.actual -or
      [IO.File]::Exists($capture.spec.error) -or [IO.File]::Exists($capture.spec.overflow)){
      throw 'OWNED-CONTROL: exact timeout/absent ordinary-exit receipt differs'
    }
    foreach($file in @($rootPidPath,$childPidPath,$childSelfPath,$capture.spec.pid)){
      if(-not [IO.File]::Exists($file)){throw ('OWNED-CONTROL: required PID evidence missing '+$file)}
    }
    $rootId=[int][IO.File]::ReadAllText($rootPidPath);$childId=[int][IO.File]::ReadAllText($childPidPath)
    if($rootId -ne [int][IO.File]::ReadAllText($capture.spec.pid) -or
      $childId -ne [int][IO.File]::ReadAllText($childSelfPath) -or $rootId -eq $childId){
      throw 'OWNED-CONTROL: actual root/descendant identity differs'
    }
    foreach($ownedId in @($rootId,$childId)){
      if($ownedId -le 0 -or $capture.launcher.TerminatedIds -notcontains $ownedId -or
        $null -ne (Get-Process -Id $ownedId -ErrorAction SilentlyContinue)){
        throw ('OWNED-CONTROL: owned PID survives barrier or is absent from receipt '+$ownedId)
      }
    }
    Assert-LNExactStreamText (Read-LNExactStream $capture.spec.stdout) "OWNED-DESCENDANT ROOT READY`n" 'timeout root stdout'
    Assert-LNExactStreamText (Read-LNExactStream $capture.spec.stderr) '' 'timeout root stderr'
    Assert-LNExactStreamText (Read-LNExactStream $capture.launcher.RawStandardOutput) '' 'timeout launcher stdout'
    Assert-LNExactStreamText (Read-LNExactStream $capture.launcher.RawStandardError) '' 'timeout launcher stderr'
    $rejected=$null
    try{Assert-LNOuterCapture $capture "OWNED-DESCENDANT ROOT READY`n" '' 0 'owned-timeout'}catch{$rejected=$_.Exception.Message}
    if($rejected -cne 'STREAM: owned-timeout incomplete bounded capture'){throw 'OWNED-CONTROL: timeout was not rejected by production stream predicate'}
    $rows.Add(@{id='owned-descendant-timeout';passed=$true;rootPid=$rootId;descendantPid=$childId;
      rootAbsent=$true;descendantAbsent=$true;actualOrdinaryExit=$null;helperExitSentinel=$capture.launcher.ExitCode;
      timedOut=$capture.launcher.TimedOut;productionRejection=$rejected;
      pidPins=@(Get-LN1Pin $rootPidPath;Get-LN1Pin $childPidPath;Get-LN1Pin $childSelfPath)})
    $rows.Add((Test-DCPartialSetup $run $pins $false))
    $rows.Add((Test-DCPartialSetup $run $pins $true))
    if(($rows.id -join '|') -cne 'owned-descendant-timeout|partial-setup-intact|partial-setup-changed-pin'){
      throw 'OWNED-CONTROL: completed ordered roster differs'
    }
    $result.success=$true
  }catch{$result.failure=$_.Exception.Message}
  finally{
    try{$result.integrity=Check-DCIntegrity ($pins+@($result.fixtures))}catch{$result.integrity=@{attempted=$true;success=$false;error=$_.Exception.Message}}
    try{$result.cleanup=Remove-DCScratch $scratch $run}catch{$result.cleanup=@{attempted=$true;success=$false;error=$_.Exception.Message}}
    if(-not $result.integrity.success -or -not $result.cleanup.success){$result.success=$false}
    $result.controls=@($rows.ToArray());Write-DCJson (Join-Path $run 'WORKER.json') $result
  }
  if(-not $result.success){[Console]::Error.Write('OWNED-DESCENDANT INNER FAIL '+$result.failure+"`n");exit 1}
  [Console]::Out.Write("OWNED-DESCENDANT INNER PASS`n");exit 0
}

if($RunDirectory){throw 'OWNED-CONTROL: RunDirectory is internal to the bounded worker'}
$run=Join-Path $allowed ([DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
$run=[IO.Path]::GetFullPath($run)
if(-not $run.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase)){throw 'OWNED-CONTROL: evidence scope'}
$pins=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-owned-descendant-control-v1';success=$false;
  innerDeadlineSeconds=8;outerDeadlineSeconds=30;failure=$null;sourcePins=@();outerCapture=$null;
  worker=$null;integrity=$null;cleanup=$null;startedUtc=[DateTime]::UtcNow.ToString('o');
  rationale='Existing lifecycle storage descendant control uses an eight-second deadline after sub-three-second startup. Outer thirty seconds bounds helper startup, inner barrier and finalizers.';
  boundary='Windows owned root+one actual descendant; strict raw streams; timeout is failure with no fabricated ordinary exit. Forced partial setup tests finally integrity and cleanup on owned fixtures only.'}
try{
  [void][IO.Directory]::CreateDirectory($run)
  foreach($path in @($PSCommandPath,$shell,(Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
    (Join-Path $root 'scripts/owned_process_tree.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
    (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){$pins.Add((Get-LN1Pin $path))}
  $report.sourcePins=@($pins.ToArray());Write-DCJson (Join-Path $run 'PLAN.json') $report
  $capture=Invoke-LNStreamCapture $root $shell @('-NoLogo','-NoProfile','-File',$PSCommandPath,'-Worker','-RunDirectory',$run) $root (Join-Path $run 'outer') 30 'owned-descendant-outer'
  $report.outerCapture=$capture
  Assert-LNOuterCapture $capture "OWNED-DESCENDANT INNER PASS`n" '' 0 'owned-descendant-outer'
  $workerResult=[IO.File]::ReadAllText((Join-Path $run 'WORKER.json'),$utf8)|ConvertFrom-Json
  if(-not $workerResult.success -or -not $workerResult.integrity.success -or -not $workerResult.cleanup.success -or @($workerResult.controls).Count -ne 3){throw 'OWNED-CONTROL: worker completion differs'}
  $report.worker=Get-LN1Pin (Join-Path $run 'WORKER.json')
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  try{$report.integrity=Check-DCIntegrity @($pins.ToArray())}catch{$report.integrity=@{attempted=$true;success=$false;error=$_.Exception.Message}}
  try{
    $report.cleanup=Remove-DCScratch (Join-Path $run 'disposable') $run
    $remaining=@(foreach($name in @('sleep-root.pid','sleep-child.pid')){
      $file=Join-Path $run $name
      if([IO.File]::Exists($file)){$ownedId=[int][IO.File]::ReadAllText($file);if($null -ne (Get-Process -Id $ownedId -ErrorAction SilentlyContinue)){$ownedId}}
    })
    $report.cleanup.recordedPidsStillLive=$remaining
    if($remaining.Count){throw 'OWNED-CONTROL: recorded process survives outer barrier'}
  }catch{$report.cleanup=@{attempted=$true;success=$false;error=$_.Exception.Message}}
  if(-not $report.integrity.success -or -not $report.cleanup.success){$report.success=$false}
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  if([IO.Directory]::Exists($run)){Write-DCJson (Join-Path $run 'RESULT.json') $report}
}
Write-Output ('OWNED-DESCENDANT-CONTROL evidence='+$run)
if(-not $report.success){Write-Output ('OWNED-DESCENDANT-CONTROL FAIL '+$report.failure);exit 1}
Write-Output 'OWNED-DESCENDANT-CONTROL PASS controls=3'

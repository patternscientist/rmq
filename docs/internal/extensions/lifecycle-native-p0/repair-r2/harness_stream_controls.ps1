param([string]$OutputRoot,[AllowEmptyCollection()][AllowEmptyString()][string[]]$ControlIds)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath=Join-Path $PSScriptRoot 'HARNESS_STREAM_REGISTRY.json'
$registry=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
$expectedIds=@('success-positive','error-positive','success-extra-stderr','error-extra-stderr','success-extra-stdout','error-extra-stdout','selector-empty','selector-unknown','selector-duplicate','launcher-blank-stdout','launcher-blank-stderr')
if((@($registry.controls.id)-join ',') -cne ($expectedIds-join ',') -or @($registry.controls.id|Select-Object -Unique).Count -ne $expectedIds.Count){throw 'STREAM-REGISTRY: ordered IDs differ'}
foreach($row in $registry.controls){
  $id=[string]$row.id
  $kind=if($id.StartsWith('selector-')){'selector'}elseif($id.StartsWith('launcher-')){'launcher'}else{'harness'}
  $stream=if($kind -ceq 'selector'){$id.Substring(9)}elseif($id.EndsWith('stderr')){'stderr'}elseif($id.EndsWith('stdout')){'stdout'}else{'none'}
  $outcome=if($id.EndsWith('-positive')){'accept'}else{'reject'}
  if($row.kind -cne $kind -or $row.stream -cne $stream -or $row.outcome -cne $outcome){throw 'STREAM-REGISTRY: field mapping differs'}
  if($kind -ceq 'harness'){
    $nativeCase=if($id.StartsWith('success-')){'intact-success'}else{'intact-stage-error'}
    if($row.case -cne $nativeCase){throw 'STREAM-REGISTRY: fixture mapping differs'}
  }
  $predicate=if($kind -ceq 'selector'){'command-selector'}else{'Assert-LNOuterCapture'}
  if($row.predicate -cne $predicate){throw 'STREAM-REGISTRY: predicate mapping differs'}
}
if($PSBoundParameters.ContainsKey('ControlIds')){
  if(-not $ControlIds.Count -or @($ControlIds|Where-Object {[string]::IsNullOrWhiteSpace($_)}).Count){throw 'STREAM-SELECTOR: empty'}
  if(@($ControlIds|Select-Object -Unique).Count -ne $ControlIds.Count){throw 'STREAM-SELECTOR: duplicate'}
  foreach($id in $ControlIds){if($id -cnotin $expectedIds){throw 'STREAM-SELECTOR: unknown'}}
  $cases=@($registry.controls|Where-Object {$_.id -cin $ControlIds})
}else{$cases=@($registry.controls)}
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r2/harness-'+[Guid]::NewGuid().ToString('N'))}
[void][IO.Directory]::CreateDirectory($OutputRoot)
# LIFE-1-R3: once OutputRoot exists, every exit path writes RESULTS.json. Every
# live source this harness reads or copies into a carrier is pinned at entry and
# re-checked in finally, and every created carrier/fixture is status-checked in
# finally; the stage error, every integrity difference and every cleanup error
# are recorded separately.
$sourcePath=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1'
$livePaths=@('docs/internal/extensions/lifecycle-native-p0/repair-r2/HARNESS_STREAM_REGISTRY.json',
  'docs/internal/extensions/lifecycle-native-p0/repair-r1/integrity_controls.ps1',
  'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1','scripts/owned_process_tree.ps1',
  'scripts/packed_native_lifecycle_stream_check.ps1','native/packed-rmq/tests/lifecycle_storage_probe.c','lean-toolchain',
  'docs/internal/extensions/lifecycle-native-p0/REGISTRY.json')
$entryPins=[ordered]@{}
$ownedRoots=[Collections.Generic.List[object]]::new()
$records=[Collections.Generic.List[object]]::new()
$mutex=$null
$held=$false
$stageError=$null;$stageRecord=$null;$completed=$false
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$finalPins=[ordered]@{}
$ownedStatus=[Collections.Generic.List[object]]::new()
$durableFailed=$false
try {
  . (Join-Path $repo 'scripts/owned_process_tree.ps1')
  . (Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1')
  . (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
  $shell=(Get-Process -Id $PID).Path
  foreach($relative in $livePaths){$entryPins[$relative]=Get-LNRawPin (Join-Path $repo $relative)}
  $source=[IO.File]::ReadAllText($sourcePath,$utf8)
  $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  try{$held=$mutex.WaitOne(600000)}catch [Threading.AbandonedMutexException]{$held=$true}
  if(-not $held){throw 'host mutex unavailable'}
  foreach($case in $cases){
    $out=Join-Path $OutputRoot $case.id
    [void][IO.Directory]::CreateDirectory($out)
    $driver=Join-Path $out 'driver.ps1'
    $expectedExit=0;$expectedError='';$carrier=$null
    if($case.kind -ceq 'harness'){
      # The immutable source carrier contains exact current owned source bytes;
      # all operations and mutations occur in its ignored fixture directories.
      $carrier=Join-Path $out 'source'
      [void][IO.Directory]::CreateDirectory($carrier)
      $paths=@('scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1','scripts/owned_process_tree.ps1','scripts/packed_native_lifecycle_stream_check.ps1','native/packed-rmq/tests/lifecycle_storage_probe.c','lean-toolchain','docs/internal/extensions/lifecycle-native-p0/REGISTRY.json')
      foreach($relative in $paths){$dest=Join-Path $carrier $relative;[void][IO.Directory]::CreateDirectory((Split-Path $dest -Parent));[IO.File]::WriteAllBytes($dest,[IO.File]::ReadAllBytes((Join-Path $repo $relative)))}
      [IO.File]::WriteAllText((Join-Path $carrier '.gitignore'),".lake/`n",$utf8)
      & git -C $carrier init -q
      & git -C $carrier config core.autocrlf false
      & git -C $carrier -c core.excludesfile= add --all
      & git -C $carrier -c user.name=RMQFixture -c user.email=fixture@invalid commit -qm source-carrier
      if($LASTEXITCODE){throw 'carrier initialization failed'}
      $ownedRoots.Add([ordered]@{carrier=$carrier;fixture=(Join-Path (Join-Path $carrier '.lake/controls') $case.case)})
      $rootLine='$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot ''../../../../..''))'
      if([regex]::Matches($source,[regex]::Escape($rootLine)).Count -ne 1){throw 'source root anchor differs'}
      $derived=$source.Replace($rootLine,('$repo='''+$carrier.Replace("'","''")+''''))
      if($case.stream -cne 'none'){
        $anchor=[regex]::Matches($derived,'(?m)^  \$mutation\r?$')
        if($anchor.Count -ne 1){throw 'injection anchor differs'}
        $target=if($case.stream -ceq 'stderr'){'Error'}else{'Out'}
        $derived=$derived.Insert($anchor[0].Index,("  [Console]::"+$target+".WriteLine('UNEXPECTED OUTER DIAGNOSTIC')`n"))
        $expectedExit=1;$expectedError='STREAM: integrity-'+$case.case+' '+$case.stream+' differs'
      }
      $harness=Join-Path $out 'harness-derived.ps1';[IO.File]::WriteAllText($harness,$derived,$utf8)
      $controlOutput=Join-Path $carrier '.lake/controls'
      $action="& '"+$harness.Replace("'","''")+"' -OutputRoot '"+$controlOutput.Replace("'","''")+"' -ControlIds '"+$case.case+"'"
    }elseif($case.kind -ceq 'selector'){
      $argument=switch($case.id){'selector-empty'{"@('')"}'selector-unknown'{"@('unknown')"}'selector-duplicate'{"@('success-positive','success-positive')"}}
      $action="& '"+$PSCommandPath.Replace("'","''")+"' -ControlIds "+$argument
      $expectedExit=1;$expectedError='STREAM-SELECTOR: '+$case.stream
    }else{
      # Execute a real release-gated launcher that emits only an unexpected blank.
      $target=if($case.stream -ceq 'stdout'){'Out'}else{'Error'}
      $child=Join-Path $out 'blank-launcher.ps1'
      [IO.File]::WriteAllText($child,("param([string]`$LaunchReleasePath)`nwhile(-not [IO.File]::Exists(`$LaunchReleasePath)){Start-Sleep -Milliseconds 10}`n[Console]::"+$target+".WriteLine('')`nexit 0"),$utf8)
      $launch=Invoke-LNRetainedLauncher -FilePath $shell -Arguments @('-NoProfile','-File',$child) -WorkingDirectory $repo -Stage $case.id -DeadlineSeconds 30 -OutputLimitBytes 8388608 -TempRoot (Join-Path $out 'launcher') -ReleaseGatedScript
      if($launch.ExitCode -ne 0 -or $launch.TimedOut -or $launch.OutputLimitExceeded -or @($launch.RetentionErrors).Count -or @($launch.StandardOutput).Count -or @($launch.StandardError).Count){throw 'unexpected blank-launcher transport/exit/decoded output'}
      $blankOut=if($case.stream -ceq 'stdout'){[Environment]::NewLine}else{''}
      $blankErr=if($case.stream -ceq 'stderr'){[Environment]::NewLine}else{''}
      Assert-LNExactStreamText (Read-LNExactStream $launch.RawStandardOutput) $blankOut 'observed blank-launcher stdout'
      Assert-LNExactStreamText (Read-LNExactStream $launch.RawStandardError) $blankErr 'observed blank-launcher stderr'
      $rawOut=Join-Path $out 'stdout';$rawErr=Join-Path $out 'stderr';[IO.File]::WriteAllText($rawOut,'');[IO.File]::WriteAllText($rawErr,'')
      $capture=@{launcher=$launch;actual=@{exitCode=0};spec=@{stdout=$rawOut;stderr=$rawErr;error=(Join-Path $out 'absent-error');overflow=(Join-Path $out 'absent-overflow')}}
      $failure=$null
      try {Assert-LNOuterCapture $capture '' '' 0 $case.id}catch{$failure=$_.Exception.Message}
      $wanted='STREAM: '+$case.id+' launcher '+$case.stream+' differs'
      if($failure -cne $wanted){throw ('wrong launcher blank verdict: '+$failure)}
      if([IO.File]::ReadAllText($(if($case.stream -ceq 'stdout'){$launch.RawStandardOutput}else{$launch.RawStandardError})) -cne [Environment]::NewLine){throw 'actual blank launcher output missing'}
      $records.Add(@{id=$case.id;outcome='reject';surface=$failure;capture=$capture;predicate='Assert-LNOuterCapture';raw=@((Get-LNRawPin $launch.RawStandardOutput),(Get-LNRawPin $launch.RawStandardError))})
      Write-Output ('STREAM CONTROL PASS '+$case.id)
      continue
    }
    [IO.File]::WriteAllText($driver,("`$ErrorActionPreference='Stop'`ntry {"+$action+"`nexit 0}catch{[Console]::Error.WriteLine(`$_.Exception.Message);exit 1}"),$utf8)
    $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver) $repo (Join-Path $out 'capture') 300 $case.id
    $expectedStdout=if($case.kind -ceq 'harness' -and $expectedExit -eq 0){'CONTROL PASS '+$case.case+[Environment]::NewLine+'INTEGRITY CONTROLS evidence='+$controlOutput+[Environment]::NewLine}else{''}
    $expectedStderr=if($expectedExit -eq 1){$expectedError+[Environment]::NewLine}else{''}
    Assert-LNOuterCapture $capture $expectedStdout $expectedStderr $expectedExit ('control-'+$case.id)
    $record=@{id=$case.id;outcome=$case.outcome;surface=$expectedError;capture=$capture;predicate=$case.predicate;raw=@((Get-LNRawPin $driver))}
    if($null -ne $carrier){
      $fixture=Join-Path $controlOutput $case.case
      $inner=Get-Content -LiteralPath (Join-Path $fixture '.lake/outer/CAPTURE.json') -Raw|ConvertFrom-Json
      $summaries=@(Get-ChildItem -LiteralPath (Join-Path $fixture '.lake/lifecycle-native-p0/runs') -Filter SUMMARY.json -Recurse -File)
      if($summaries.Count -ne 1){throw 'summary cardinality differs'}
      $summary=Get-Content -LiteralPath $summaries[0].FullName -Raw|ConvertFrom-Json
      if(-not $summary.integrity.success -or $summary.selected.Count -ne 1 -or $summary.selected[0] -cne 'pop-unique'){throw 'fixture inner guards differ'}
      $wantedNative=if($case.case -ceq 'intact-success'){0}else{7};$wantedRunner=if($wantedNative -eq 0){0}else{1}
      if($summary.stages[0].child.exitCode -ne $wantedNative -or $inner.actual.exitCode -ne $wantedRunner){throw 'actual inner exits differ'}
      $expectedInnerOut='LIFECYCLE-REPLAY evidence='+$summary.runRoot+[Environment]::NewLine
      if($wantedRunner -eq 0){$expectedInnerOut+='LIFECYCLE-REPLAY PASS cases=1 selfTest=False'+[Environment]::NewLine}
      $expectedInnerErr=if($wantedRunner -eq 1){'PROCESS: fixture-stage actual child or launcher exit differs from 0'+[Environment]::NewLine}else{''}
      if($case.stream -ceq 'stdout'){$expectedInnerOut='UNEXPECTED OUTER DIAGNOSTIC'+[Environment]::NewLine+$expectedInnerOut}
      if($case.stream -ceq 'stderr'){$expectedInnerErr='UNEXPECTED OUTER DIAGNOSTIC'+[Environment]::NewLine+$expectedInnerErr}
      Assert-LNOuterCapture $inner $expectedInnerOut $expectedInnerErr $wantedRunner ('observed-'+$case.id)
      foreach($root in @($carrier,$fixture)){
        $status=@(& git -C $root -c core.excludesfile= status --porcelain=v1 --untracked-files=all)
        $expectedStatus=if($root -ceq $fixture){'?? existing-untracked.txt'}else{''}
        if($LASTEXITCODE -ne 0 -or ($status -join '') -cne $expectedStatus){throw 'owned fixture/carrier restoration differs'}
      }
      $record.inner=$inner;$record.summary=Get-LNRawPin $summaries[0].FullName
      $record.fixtureRestored=$true;$record.carrierUnchanged=$true
      $record.raw+=@((Get-LNRawPin $harness),(Get-LNRawPin (Join-Path $fixture 'scripts/packed_native_lifecycle_storage_replay.ps1')))
    }
    $records.Add($record)
    Write-Output ('STREAM CONTROL PASS '+$case.id)
  }
  if((@($records.ToArray().id)-join ',') -cne (@($cases.id)-join ',')){throw 'STREAM-REGISTRY: missing/unused executed control'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  # Every created carrier and fixture, success or not, is status-checked. LIFE-1-R4:
  # each git status runs through the owned-process helper with a positive
  # deadline; its exit, streams and timeout are kept, and any failure is an
  # integrity error, never a hang or a silent pass.
  foreach($owned in $ownedRoots){
    foreach($root in @($owned.carrier,$owned.fixture)){
      if(-not [IO.Directory]::Exists($root)){continue}
      $check=[ordered]@{root=$root;exitCode=$null;timedOut=$null;outputLimitExceeded=$null;stdout=@();stderr=@();durationSeconds=$null;deadlineSeconds=60;status='unchecked'}
      try {
        $gitPath=(Get-Command git -CommandType Application -ErrorAction Stop|Select-Object -First 1).Source
        $g=Invoke-RMQOwnedBoundedProcess -FilePath $gitPath -Arguments @('-C',$root,'-c','core.excludesfile=','status','--porcelain=v1','--untracked-files=all') `
          -WorkingDirectory $repo -Stage 'stream-finalization-git-status' -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot (Join-Path $OutputRoot 'finalization-git')
        $check.exitCode=$g.ExitCode;$check.timedOut=$g.TimedOut;$check.outputLimitExceeded=$g.OutputLimitExceeded
        $check.stdout=@($g.StandardOutput);$check.stderr=@($g.StandardError);$check.durationSeconds=$g.DurationSeconds
        $expectedStatus=if($root -ceq $owned.fixture){'?? existing-untracked.txt'}else{''}
        if($g.TimedOut -or $g.OutputLimitExceeded -or $g.ExitCode -ne 0 -or @($g.StandardError).Count -ne 0){
          $check.status='failed'
          $integrityErrors.Add('STREAM-INTEGRITY: owned fixture/carrier status failed: '+$root+': git exit '+$g.ExitCode+'; timeout '+$g.TimedOut+'; overflow '+$g.OutputLimitExceeded+'; stderr: '+(@($g.StandardError) -join ' | '))
        } elseif((@($g.StandardOutput) -join '') -cne $expectedStatus){
          $check.status='differs'
          $integrityErrors.Add('STREAM-INTEGRITY: owned fixture/carrier restoration differs: '+$root)
        } else {$check.status='verified'}
      } catch {$check.status='failed';$integrityErrors.Add('STREAM-INTEGRITY: owned fixture/carrier status failed: '+$root+': '+$_.Exception.Message)}
      $ownedStatus.Add($check)
    }
  }
  foreach($relative in $livePaths){
    $entry=if($entryPins.Contains($relative)){$entryPins[$relative]}else{$null}
    $final=$null;$status='not-captured'
    if($null -ne $entry){
      $status='verified'
      try {
        $final=Get-LNRawPin (Join-Path $repo $relative)
        $finalPins[$relative]=$final
        if($final.bytes -ne $entry.bytes -or $final.sha256 -cne $entry.sha256){$status='changed';$integrityErrors.Add('INTEGRITY: changed captured pin: '+$entry.path)}
      } catch {$status='unreadable-final';$integrityErrors.Add($_.Exception.Message)}
    }
    $pinChecks.Add([ordered]@{path=$relative;entrySha256=$(if($null -ne $entry){$entry.sha256}else{$null});finalSha256=$(if($null -ne $final){$final.sha256}else{$null});status=$status})
  }
  if($held){try{$mutex.ReleaseMutex()}catch{$cleanupErrors.Add('host mutex release: '+$_.Exception.Message)}}
  if($null -ne $mutex){try{$mutex.Dispose()}catch{$cleanupErrors.Add('host mutex dispose: '+$_.Exception.Message)}}
  $passed=$completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    ownedRoots=@($ownedRoots.ToArray());ownedRootStatus=@($ownedStatus.ToArray());entryPinCount=$entryPins.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count}
  try {
    # LIFE-1-R4: entry pins are labelled entry*; `registry`, `source` and
    # `validator` keep their eb8e4f25 meaning, the post-run pin observed in
    # finalization (null if unreadable).
    $result=@{selected=@($cases.id);controls=@($records.ToArray())
      entryRegistry=$(if($entryPins.Contains($livePaths[0])){$entryPins[$livePaths[0]]}else{$null})
      entrySource=$(if($entryPins.Contains($livePaths[1])){$entryPins[$livePaths[1]]}else{$null});entryValidator=$(if($entryPins.Contains($livePaths[5])){$entryPins[$livePaths[5]]}else{$null})
      registry=$(if($finalPins.Contains($livePaths[0])){$finalPins[$livePaths[0]]}else{$null})
      source=$(if($finalPins.Contains($livePaths[1])){$finalPins[$livePaths[1]]}else{$null});validator=$(if($finalPins.Contains($livePaths[5])){$finalPins[$livePaths[5]]}else{$null})
      finalization=$finalization}
    [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($result|ConvertTo-Json -Depth 40),$utf8)
  } catch {$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('STREAM CONTROLS: durable result write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('STREAM CONTROLS evidence='+$OutputRoot)

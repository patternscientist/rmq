param([string]$OutputRoot,[string[]]$ControlIds)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r1/controls-'+[Guid]::NewGuid().ToString('N'))}
[void][IO.Directory]::CreateDirectory($OutputRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
# LIFE-1-R3: once OutputRoot exists, every exit path writes RESULTS.json. The
# real-candidate tree snapshot and every live source this harness reads or copies
# are compared independently in finally; the stage error, every integrity
# difference and every fixture-restoration error are recorded separately.
$production=Join-Path $repo 'scripts/packed_native_lifecycle_storage_replay.ps1'
$livePaths=@('scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1',
  'scripts/owned_process_tree.ps1','scripts/packed_native_lifecycle_stream_check.ps1',
  'native/packed-rmq/tests/lifecycle_storage_probe.c','lean-toolchain','docs/internal/extensions/lifecycle-native-p0/REGISTRY.json')
$entryPins=[ordered]@{}
$records=[Collections.Generic.List[object]]::new()
$candidateBefore=$null
$start=-1;$stop=-1
$stageError=$null;$stageRecord=$null;$completed=$false
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$treeCheck=[ordered]@{attempted=$false;equal=$false;error=$null}
$finalPins=[ordered]@{}
$durableFailed=$false
try {
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1')
$shell=(Get-Process -Id $PID).Path
$candidateBefore=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'candidate-before')
foreach($relative in $livePaths){$entryPins[$relative]=Get-LNRawPin (Join-Path $repo $relative)}
$source=[IO.File]::ReadAllText($production,$utf8)
$start=$source.IndexOf('  $LeanRoot = [IO.Path]::GetFullPath($LeanRoot)')
$stop=$source.LastIndexOf('  $taskSuccess = $true')
if($start -lt 0 -or $stop -le $start){throw 'fixture splice anchors unavailable'}
$prefix=$source.Substring(0,$start);$suffix=$source.Substring($stop)
$cases=@(
 @{id='intact-success';stage='exit 0';mutation='';error=$null;integrity=$true},
  @{id='intact-stage-error';stage='exit 7';mutation='';error='PROCESS:';integrity=$true},
 @{id='malformed-stdout-intact';stage='[Console]::OpenStandardOutput().WriteByte(255);exit 0';mutation='';error='DIAGNOSTIC:';integrity=$true},
 @{id='stage-error-and-pin-change';stage='exit 7';mutation='pin';error='PROCESS:';integrity=$false},
 @{id='stage-error-and-capture-error';stage='exit 7';mutation='capture';error='PROCESS:';integrity=$false},
 @{id='success-and-pin-change';stage='exit 0';mutation='pin';error=$null;integrity=$false},
 @{id='mixed-diagnostic-and-pin-change';stage="[Console]::Error.WriteLine('unexpected');exit 0";mutation='pin';error='DIAGNOSTIC:';integrity=$false},
 @{id='timeout-and-pin-change';stage='Start-Sleep -Seconds 120';mutation='pin';error='PROCESS:';integrity=$false;deadline=8},
 @{id='success-and-tracked-change';stage='exit 0';mutation='tracked';error=$null;integrity=$false},
 @{id='success-and-index-change';stage='exit 0';mutation='index';error=$null;integrity=$false},
 @{id='success-and-untracked-addition';stage='exit 0';mutation='untracked';error=$null;integrity=$false},
 @{id='success-and-untracked-byte-change';stage='exit 0';mutation='untracked-bytes';error=$null;integrity=$false},
 @{id='success-and-link-map-change';stage='exit 0';mutation='map';error=$null;integrity=$false},
 @{id='partial-identity-and-pin-change';stage='exit 0';mutation='partial';error='IDENTITY:';integrity=$false},
 @{id='missing-baseline';stage='exit 0';mutation='baseline';error=$null;integrity=$false}
)
if($PSBoundParameters.ContainsKey('ControlIds')) {
  if(-not $ControlIds.Count -or @($ControlIds|Select-Object -Unique).Count -ne $ControlIds.Count){throw 'invalid control selector'}
  foreach($id in $ControlIds){if($id -cnotin $cases.id){throw 'unknown control selector'}}
  $cases=@($cases|Where-Object {$_.id -cin $ControlIds})
}
foreach($case in $cases) {
  $fixture=Join-Path $OutputRoot $case.id
  [void][IO.Directory]::CreateDirectory($fixture)
  $paths=@('scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1',
    'scripts/owned_process_tree.ps1','native/packed-rmq/tests/lifecycle_storage_probe.c','lean-toolchain',
    'docs/internal/extensions/lifecycle-native-p0/REGISTRY.json')
  foreach($relative in $paths){
    $dest=Join-Path $fixture $relative
    [void][IO.Directory]::CreateDirectory((Split-Path $dest -Parent))
    [IO.File]::WriteAllBytes($dest,[IO.File]::ReadAllBytes((Join-Path $repo $relative)))
  }
  [IO.File]::WriteAllText((Join-Path $fixture '.gitignore'),".lake/`n",$utf8)
  [IO.File]::WriteAllText((Join-Path $fixture 'tracked.txt'),'original',$utf8)
  $mutation=switch($case.mutation) {
    'pin' {"[IO.File]::AppendAllText((Join-Path `$taskRoot 'native/packed-rmq/tests/lifecycle_storage_probe.c'),'fixture-change')"}
    'tracked' {"[IO.File]::WriteAllText((Join-Path `$taskRoot 'tracked.txt'),'changed')"}
    'index' {'$blob=(& git -C $taskRoot rev-parse HEAD:tracked.txt).Trim(); & git -C $taskRoot update-index --cacheinfo ("100755,"+$blob+",tracked.txt"); if($LASTEXITCODE){throw "fixture index change failed"}'}
    'untracked' {"[IO.File]::WriteAllText((Join-Path `$taskRoot 'new.txt'),'unexpected')"}
    'untracked-bytes' {"[IO.File]::WriteAllText((Join-Path `$taskRoot 'existing-untracked.txt'),'changed')"}
    'map' {"`$map=Join-Path `$taskRunRoot 'link.map';[IO.File]::WriteAllText(`$map,'original');`$null=Get-LNPin `$map;[IO.File]::WriteAllText(`$map,'changed')"}
    'capture' {'$map=Join-Path $taskRunRoot "link.map";[IO.File]::WriteAllText($map,"original");$lock=[IO.File]::Open($map,[IO.FileMode]::Open,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None);try {$null=Get-LNAvailablePin $map}finally{$lock.Dispose()}'}
    'partial' {"[IO.File]::AppendAllText((Join-Path `$taskRoot 'native/packed-rmq/tests/lifecycle_storage_probe.c'),'fixture-change');`$taskIdentity=@{files=@((Get-LNPin `$taskScript),(Get-LNPin (Join-Path `$taskRoot 'missing-tool.exe')))}"}
    'baseline' {'$taskIntegrityState.baseline=$null'}
    default {''}
  }
  $deadline=if($case.ContainsKey('deadline')){$case.deadline}else{30}
  # Replace ONLY the tool/semantic stage body. All initialization, source capture,
  # Invoke-LNStage, production validators, catch, finally and final verdict remain.
  # Each test child is a real owned process; this is not an extracted-finally test.
  $body=@"
  `$fixtureStage=Join-Path `$taskRunRoot 'fixture-stage.ps1'
  [IO.File]::WriteAllText(`$fixtureStage,'$($case.stage.Replace("'","''"))',`$taskEncoding)
  `$null=Get-LNPin `$fixtureStage
  `$r=Invoke-LNStage 'fixture-stage' `$taskShell @('-NoProfile','-File',`$fixtureStage) $deadline
  $mutation
  Assert-LNProcess `$r 0
  Assert-LNNoStderr `$r
"@
  $derived=$prefix+$body+"`n"+$suffix
  if(-not $derived.StartsWith($prefix) -or -not $derived.EndsWith($suffix)){throw 'fixture changed production finalization'}
  [IO.File]::WriteAllText((Join-Path $fixture $paths[0]),$derived,$utf8)
  & git -C $fixture init -q
  & git -C $fixture config core.autocrlf false
  & git -C $fixture -c core.excludesfile= add --all
  & git -C $fixture -c user.name=RMQFixture -c user.email=fixture@invalid commit -qm baseline
  if($LASTEXITCODE){throw 'isolated fixture initialization failed'}
  [IO.File]::WriteAllText((Join-Path $fixture 'existing-untracked.txt'),'original',$utf8)
  $before=Get-LNTreeSnapshot $fixture (Join-Path $fixture '.lake/before')
  $run=$null;$summary=$null;$caseError=$null
  $restoreErrors=[Collections.Generic.List[string]]::new()
  try {
    $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',(Join-Path $fixture $paths[0]),'-Cases','pop-unique') `
      $fixture (Join-Path $fixture '.lake/outer') 120 $case.id
    $run=$capture.launcher
    if($run.TimedOut -or $run.OutputLimitExceeded){throw 'fixture outer deadline/output failure'}
    $summaries=@(Get-ChildItem -LiteralPath (Join-Path $fixture '.lake/lifecycle-native-p0/runs') -Filter SUMMARY.json -Recurse -File)
    if($summaries.Count -ne 1){throw 'fixture final receipt absent/ambiguous'}
    $summary=[IO.File]::ReadAllText($summaries[0].FullName,$utf8)|ConvertFrom-Json
    $expectedSuccess=$case.integrity -and $null -eq $case.error
    if($summary.success -ne $expectedSuccess -or $run.ExitCode -ne $(if($expectedSuccess){0}else{1})){throw "wrong final verdict: $($case.id)"}
    if(-not $summary.integrity.attempted -or $summary.integrity.success -ne $case.integrity -or $summary.integrity.checkedPins -lt 8){throw "wrong independent integrity: $($case.id)"}
    if($null -eq $case.error){if($null -ne $summary.failure){throw "unexpected stage error $($summary.failure)"}}
    elseif(-not $summary.failure.StartsWith($case.error)){throw "original stage error lost: $($case.id)"}
    if($case.id -eq 'malformed-stdout-intact' -and -not @($summary.capturedPins|Where-Object {$_.path -like '*fixture-stage.stdout' -and $_.bytes -eq 1}).Count){throw 'malformed raw bytes were not pinned'}
    if($case.mutation -in @('pin','partial','map') -and -not @($summary.integrity.errors|Where-Object {$_ -like 'INTEGRITY: changed captured pin:*'}).Count){throw 'changed pin surface absent'}
    if($case.mutation -in @('tracked','index','untracked','untracked-bytes','pin','partial') -and $summary.integrity.errors -notcontains 'INTEGRITY: live tracked/index/untracked baseline changed'){throw 'tree surface absent'}
    if($case.id -eq 'timeout-and-pin-change' -and -not $summary.stages[0].launcher.TimedOut){throw 'timeout not reached'}
    # Exact ordinary exits/raw bytes prevent an unrelated process failure from
    # satisfying an expected PROCESS/DIAGNOSTIC prefix.
    $rawStem=Join-Path $summary.runRoot '000-fixture-stage'
    $rawOut=[IO.File]::ReadAllBytes($rawStem+'.stdout')
    $rawErr=[IO.File]::ReadAllBytes($rawStem+'.stderr')
    $timeout=$case.id -eq 'timeout-and-pin-change'
    $malformed=$case.id -eq 'malformed-stdout-intact'
    if(-not $timeout){
      $actual=Get-Content ($rawStem+'.exit.json') -Raw|ConvertFrom-Json
      $exit=if($case.stage -ceq 'exit 7'){7}else{0}
      if($actual.exitCode -ne $exit){throw 'unexpected actual native exit'}
      $expectedOut=if($malformed){'FF'}else{''}
      if([BitConverter]::ToString($rawOut) -cne $expectedOut){throw 'unexpected raw stdout'}
      $expectedErr=if($case.id -eq 'mixed-diagnostic-and-pin-change'){"unexpected`r`n"}else{''}
      if($utf8.GetString($rawErr) -cne $expectedErr){throw 'unexpected raw stderr'}
    } elseif($rawOut.Length -ne 0 -or $rawErr.Length -ne 0){throw 'unexpected timeout raw output'}
    if(-not $malformed){
      if($summary.stages.Count -ne 1){throw 'fixture did not reach exactly one real stage'}
      $s=$summary.stages[0]
      if(@($s.launcher.StandardOutput).Count -ne 0 -or @($s.launcher.StandardError).Count -ne 0){throw 'unexpected launcher streams'}
      if($s.launcherError -or $s.childError -or $s.launcher.OutputLimitExceeded -or $s.nativeOutputLimitExceeded -or $s.launcher.TimedOut -ne $timeout){throw 'unexpected process failure'}
      if(-not $timeout -and ($s.launcher.ExitCode -ne $exit -or $s.child.exitCode -ne $exit)){throw 'ordinary exit mismatch'}
      if($timeout -and ($null -eq $s.nativePid -or $null -ne (Get-Process -Id $s.nativePid -ErrorAction SilentlyContinue))){throw 'timeout native process not established/cleaned'}
    }
    $expectedErrors=@()
    if($case.mutation -in @('pin','partial')){$expectedErrors+=('INTEGRITY: changed captured pin: '+(Join-Path $fixture 'native/packed-rmq/tests/lifecycle_storage_probe.c'))}
    if($case.mutation -eq 'map'){$expectedErrors+=('INTEGRITY: changed captured pin: '+(Join-Path $summary.runRoot 'link.map'))}
    if($case.mutation -in @('tracked','index','untracked','untracked-bytes','pin','partial')){$expectedErrors+='INTEGRITY: live tracked/index/untracked baseline changed'}
    if($case.mutation -eq 'baseline'){$expectedErrors+='INTEGRITY: UNCOVERED; initial tree inventory unavailable'}
    if($case.mutation -eq 'capture'){
      # Derive the runtime-specific message from the same independently known
      # exclusive-lock operation, never from the summary's claimed suffix.
      $map=Join-Path $summary.runRoot 'link.map'
      $lock=[IO.File]::Open($map,[IO.FileMode]::Open,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None)
      $captureFailure=$null
      try {try {$null=Get-FileHash -LiteralPath $map -Algorithm SHA256}catch{$captureFailure=$_.Exception.Message}}
      finally {$lock.Dispose()}
      if($null -eq $captureFailure){throw 'expected exclusive-lock hash failure absent'}
      $expectedErrors=@('INTEGRITY: artifact capture failed: '+$map+'; '+$captureFailure)
    }
    if((@($summary.integrity.errors|Sort-Object)|ConvertTo-Json -Compress) -cne (@($expectedErrors|Sort-Object)|ConvertTo-Json -Compress)){throw 'unexpected additional/missing integrity failure'}
    $exactFailure=if($case.stage -ceq 'exit 7'){'PROCESS: fixture-stage actual child or launcher exit differs from 0'}elseif($timeout){'PROCESS: fixture-stage was not a completed bounded process; see retained logs'}elseif($case.id -eq 'mixed-diagnostic-and-pin-change'){'DIAGNOSTIC: unexpected or mixed stderr for fixture-stage'}elseif($case.mutation -eq 'partial'){'IDENTITY: missing file '+(Join-Path $fixture 'missing-tool.exe')}else{$null}
    if($malformed){
      $decodeFailure=$null
      try {$null=[IO.File]::ReadAllText($rawStem+'.stdout',$utf8)}catch{$decodeFailure=$_.Exception.Message}
      if($null -eq $decodeFailure){throw 'expected strict UTF-8 decode failure absent'}
      $exactFailure='DIAGNOSTIC: invalid raw stage evidence for fixture-stage; '+$decodeFailure
    }
    if($summary.failure -cne $exactFailure){throw 'unexpected independent stage failure'}
    $nl=[Environment]::NewLine
    $expectedStdout='LIFECYCLE-REPLAY evidence='+$summary.runRoot+$nl
    if($expectedSuccess){$expectedStdout+='LIFECYCLE-REPLAY PASS cases=1 selfTest=False'+$nl}
    $expectedStderr=if($null -ne $exactFailure){$exactFailure+$nl}else{''}
    foreach($message in $expectedErrors){$expectedStderr+=$message+$nl}
    Assert-LNOuterCapture $capture $expectedStdout $expectedStderr $(if($expectedSuccess){0}else{1}) ('integrity-'+$case.id)
    $records.Add(@{id=$case.id;expectedSuccess=$expectedSuccess;expectedStageError=$case.error;expectedIntegrity=$case.integrity;
      actualExit=$run.ExitCode;seconds=$run.DurationSeconds;summary=Get-LNRawPin $summaries[0].FullName;integrity=$summary.integrity;
      stageFailure=$summary.failure;fixtureSource=Get-LNRawPin (Join-Path $fixture $paths[0]);outer=$run;capture=$capture;
      streamContract=@{expectedStdout=$expectedStdout;expectedStderr=$expectedStderr;expectedExit=$(if($expectedSuccess){0}else{1});validated=$true}})
  } catch {$caseError=$_}
  finally {
    # This exact fixture directory was created above. Restore only owned fixture
    # files/index; never reset the real worktree or touch an installed tool.
    # Every step is guarded and exit-checked; restoration errors never replace
    # the case error.
    try{& git -C $fixture update-index --no-assume-unchanged tracked.txt;if($LASTEXITCODE){$restoreErrors.Add('git update-index exit '+$LASTEXITCODE)}}catch{$restoreErrors.Add('git update-index: '+$_.Exception.Message)}
    try{& git -C $fixture restore --source=HEAD --staged --worktree -- $paths 'tracked.txt' '.gitignore';if($LASTEXITCODE){$restoreErrors.Add('git restore exit '+$LASTEXITCODE)}}catch{$restoreErrors.Add('git restore: '+$_.Exception.Message)}
    try{if([IO.File]::Exists((Join-Path $fixture 'new.txt'))){[IO.File]::Delete((Join-Path $fixture 'new.txt'))}}catch{$restoreErrors.Add('untracked removal: '+$_.Exception.Message)}
    try{[IO.File]::WriteAllText((Join-Path $fixture 'existing-untracked.txt'),'original',$utf8)}catch{$restoreErrors.Add('untracked restoration: '+$_.Exception.Message)}
    try {
      $ownedRuns=Join-Path $fixture '.lake/lifecycle-native-p0/runs'
      if([IO.Directory]::Exists($ownedRuns)){
        foreach($map in @(Get-ChildItem -LiteralPath $ownedRuns -Filter link.map -Recurse -File)){
          if(-not $map.FullName.StartsWith($ownedRuns+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)){throw 'fixture map escaped owned root'}
          [IO.File]::WriteAllText($map.FullName,'original')
          if([IO.File]::ReadAllText($map.FullName) -cne 'original'){throw 'ignored map restoration failed'}
        }
      }
    } catch {$restoreErrors.Add($_.Exception.Message)}
    try {
      $after=Get-LNTreeSnapshot $fixture (Join-Path $fixture '.lake/after')
      if(($before|ConvertTo-Json -Depth 10 -Compress) -cne ($after|ConvertTo-Json -Depth 10 -Compress)){$restoreErrors.Add('owned fixture restoration failed')}
    } catch {$restoreErrors.Add('owned fixture snapshot: '+$_.Exception.Message)}
    foreach($message in $restoreErrors){$cleanupErrors.Add($case.id+': '+$message)}
  }
  if($null -ne $caseError){throw $caseError}
  if($restoreErrors.Count){break}
  Write-Output ('CONTROL PASS '+$case.id)
}
if($cleanupErrors.Count -eq 0){$completed=$true}
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
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
  if($null -ne $candidateBefore){
    $treeCheck.attempted=$true
    try {
      $candidateAfter=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'candidate-after')
      $treeCheck.equal=(($candidateBefore|ConvertTo-Json -Depth 10 -Compress) -ceq ($candidateAfter|ConvertTo-Json -Depth 10 -Compress))
      if(-not $treeCheck.equal){$integrityErrors.Add('real candidate changed')}
    } catch {$treeCheck.error=$_.Exception.Message;$integrityErrors.Add('real candidate snapshot failed: '+$_.Exception.Message)}
  }
  $passed=$completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray());treeCheck=$treeCheck
    entryPinCount=$entryPins.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count}
  try {
    # LIFE-1-R4: entry pins are labelled entry*; `source` and `helper` keep their
    # eb8e4f25 meaning, the post-run pin observed in finalization (null if unreadable).
    $result=@{entrySource=$(if($entryPins.Contains($livePaths[0])){$entryPins[$livePaths[0]]}else{$null});entryHelper=$(if($entryPins.Contains($livePaths[1])){$entryPins[$livePaths[1]]}else{$null});
      source=$(if($finalPins.Contains($livePaths[0])){$finalPins[$livePaths[0]]}else{$null});helper=$(if($finalPins.Contains($livePaths[1])){$finalPins[$livePaths[1]]}else{$null});
      stageSplice=@{start=$start;stop=$stop;preserved='entire prefix and suffix, including production catch/finally/final verdict; only stage body replaced'};
      controls=@($records.ToArray());fixtureRestoration=($cleanupErrors.Count -eq 0);candidateUnchanged=($treeCheck.attempted -and $treeCheck.equal);
      finalization=$finalization}
    [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($result|ConvertTo-Json -Depth 40),$utf8)
  } catch {$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('INTEGRITY CONTROLS: durable result write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('INTEGRITY CONTROLS evidence='+$OutputRoot)

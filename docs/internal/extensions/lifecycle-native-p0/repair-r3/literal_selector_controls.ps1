param([string]$OutputRoot,[AllowNull()][AllowEmptyCollection()][AllowEmptyString()][string[]]$ControlIds)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath=Join-Path $PSScriptRoot 'CONTROL_REGISTRY.json'
$registry=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
# The registry is committed expected data, pinned independently before execution.
if((Get-FileHash $registryPath).Hash -cne '16E26C5B131BBE258B3813BCDB252414E8BED454EF6286EB2ED7F7EF3496261D'){throw 'R3 registry byte identity differs'}
$ids=@($registry.controls.id)
$knownIds=[Collections.Generic.HashSet[string]]::new([string[]]$ids,[StringComparer]::Ordinal)
if($knownIds.Count -ne $ids.Count){throw 'R3 registry duplicate'}
if($PSBoundParameters.ContainsKey('ControlIds')){
  if($null -eq $ControlIds -or -not $ControlIds.Count -or @($ControlIds|Where-Object {[string]::IsNullOrWhiteSpace($_)}).Count){throw 'R3 selector empty'}
  $selectedIds=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in $ControlIds){
    if(-not $knownIds.Contains($id)){throw 'R3 selector unknown'}
    if(-not $selectedIds.Add($id)){throw 'R3 selector duplicate'}
  }
  $cases=@($registry.controls|Where-Object {$selectedIds.Contains($_.id)})
}else{$cases=@($registry.controls)}
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r3/controls-'+[Guid]::NewGuid().ToString('N'))}
if(Test-Path -LiteralPath $OutputRoot){throw 'R3 output must be fresh'}
[void][IO.Directory]::CreateDirectory($OutputRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
$shell=(Get-Process -Id $PID).Path
$selector=Join-Path $PSScriptRoot '../repair-r2/certify_profiles.ps1'
$selectorSource=[IO.File]::ReadAllText($selector,$utf8)
$tokens=$null;$parseErrors=$null
$ast=[Management.Automation.Language.Parser]::ParseInput($selectorSource,[ref]$tokens,[ref]$parseErrors)
if($parseErrors.Count){throw 'selector parse failed'}
$param=@($ast.ParamBlock.Parameters|Where-Object {$_.Name.VariablePath.UserPath -ceq 'Kinds'})
if($param.Count -ne 1 -or $param[0].DefaultValue.Extent.Text -cne "@('focused','full','integrity','dependencies','checks','claims')"){throw 'omitted default roster differs'}
$before=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'candidate-before')
$sourcePaths=@($PSCommandPath,$registryPath,$selector,(Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1'),(Join-Path $repo 'scripts/owned_process_tree.ps1'),(Join-Path $repo 'scripts/packed_native_lifecycle_storage_replay.ps1'),(Join-Path $PSScriptRoot '../repair-r1/run_owned.ps1'),(Join-Path $PSScriptRoot '../repair-r1/integrity_controls.ps1'),(Join-Path $PSScriptRoot '../repair-r2/harness_stream_controls.ps1'))
$pins=@($sourcePaths|ForEach-Object {Get-LNRawPin $_})
$records=[Collections.Generic.List[object]]::new()
$failure=$null;$integrityFailure=$null
$watch=[Diagnostics.Stopwatch]::StartNew()
function Assert-Bytes([string]$Path,[string]$Base64) {
  if(-not [string]::Equals([Convert]::ToBase64String([IO.File]::ReadAllBytes($Path)),$Base64,[StringComparison]::Ordinal)){throw ('R3 emitted bytes differ: '+$Path)}
}
try {
  foreach($case in $cases){
    $out=Join-Path $OutputRoot $case.id
    [void][IO.Directory]::CreateDirectory($out)
    $driver=Join-Path $out 'driver.ps1'
    $record=@{id=$case.id;mode=$case.mode;predicate=$case.predicate;tier=$case.tier;verdict=$case.verdict}
    if($case.mode -ceq 'literal'){
      $body="`$o=[Convert]::FromBase64String('"+$case.stdout+"');`$e=[Convert]::FromBase64String('"+$case.stderr+"');`$s=[Console]::OpenStandardOutput();`$s.Write(`$o,0,`$o.Length);`$s.Flush();`$s=[Console]::OpenStandardError();`$s.Write(`$e,0,`$e.Length);`$s.Flush();exit "+$case.exit
      [IO.File]::WriteAllText($driver,$body,$utf8)
      $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920');$held=$false
      try {
        try{$held=$mutex.WaitOne(600000)}catch [Threading.AbandonedMutexException]{$held=$true}
        if(-not $held){throw 'R3 shared mutex unavailable'}
        $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver) $repo (Join-Path $out 'capture') 60 $case.id
      }finally{if($held){$mutex.ReleaseMutex()};$mutex.Dispose()}
      Assert-Bytes $capture.spec.stdout $case.stdout
      Assert-Bytes $capture.spec.stderr $case.stderr
      Assert-Bytes $capture.launcher.RawStandardOutput ''
      Assert-Bytes $capture.launcher.RawStandardError ''
      # Guard observations precede intended rejection, including malformed bytes.
      if($capture.launcher.TimedOut -or $capture.launcher.OutputLimitExceeded -or @($capture.launcher.RetentionErrors).Count -or @($capture.launcher.StandardOutput).Count -or @($capture.launcher.StandardError).Count -or [IO.File]::Exists($capture.spec.error) -or [IO.File]::Exists($capture.spec.overflow) -or $null -eq $capture.actual -or $capture.actual.exitCode -ne $case.exit -or $capture.launcher.ExitCode -ne $case.exit){throw 'R3 actual transport/ordinary exit differs'}
      $actualExit=[IO.File]::ReadAllText($capture.spec.exit,$utf8)|ConvertFrom-Json
      if($actualExit.exitCode -ne $case.exit){throw 'R3 ordinary exit artifact differs'}
      if($case.failure -cne 'invalid-utf8'){
        Assert-LNOuterCapture $capture ($utf8.GetString([Convert]::FromBase64String($case.stdout))) ($utf8.GetString([Convert]::FromBase64String($case.stderr))) $case.exit ('observed-'+$case.id)
      }
      $rejection=$null
      try {Assert-LNOuterCapture $capture ($utf8.GetString([Convert]::FromBase64String($case.expectedStdout))) ($utf8.GetString([Convert]::FromBase64String($case.expectedStderr))) $case.exit $case.id}catch{$rejection=$_.Exception.Message}
      $wanted=if($case.failure -ceq 'invalid-utf8'){'STREAM: invalid UTF-8 capture: '+$capture.spec.stdout}elseif($case.verdict -ceq 'reject'){$case.failure}else{$null}
      if(-not [string]::Equals($rejection,$wanted,[StringComparison]::Ordinal)){throw ('R3 wrong verdict '+$case.id+': '+$rejection)}
      $childPid=[int][IO.File]::ReadAllText($capture.spec.pid)
      if(Get-Process -Id $childPid -ErrorAction SilentlyContinue){throw 'R3 emitted child survived'}
      $record.capture=$capture;$record.failure=$rejection;$record.childAbsent=$true
    }elseif($case.mode -ceq 'selector'){
      $targetOutput=Join-Path $out 'must-not-exist'
      $body="`$ErrorActionPreference='Stop';try { & '"+$selector.Replace("'","''")+"' -OutputRoot '"+$targetOutput.Replace("'","''")+"' -Kinds "+$case.expression+";throw 'UNEXPECTED NORMAL RETURN' }catch{ if(`$_.Exception.Message -cne '"+$case.failure+"'){throw};if(Test-Path -LiteralPath '"+$targetOutput.Replace("'","''")+"'){throw 'selector started work'};[Console]::Out.WriteLine('BOUNDARY REJECTED "+$case.id+"');exit 0}"
      [IO.File]::WriteAllText($driver,$body,$utf8)
      $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver) $repo (Join-Path $out 'capture') 60 $case.id
      Assert-LNOuterCapture $capture ('BOUNDARY REJECTED '+$case.id+[Environment]::NewLine) '' 0 $case.id
      if(Test-Path -LiteralPath $targetOutput){throw 'R3 rejected selector created output'}
      $record.capture=$capture;$record.failure=$case.failure;$record.noWorkBeforeRejection=$true
    }elseif($case.mode -ceq 'focused'){
      $targetOutput=Join-Path $out 'certification'
      $body="`$ErrorActionPreference='Stop'; & '"+$selector.Replace("'","''")+"' -OutputRoot '"+$targetOutput.Replace("'","''")+"' -Kinds @('focused')"
      [IO.File]::WriteAllText($driver,$body,$utf8)
      $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver) $repo (Join-Path $out 'capture') 1200 $case.id
      $manifestPath=Join-Path $targetOutput 'PROFILES.json'
      $expected='OWNED focused exit=0 evidence='+(Join-Path $targetOutput 'focused')+[Environment]::NewLine+'PROFILE CERTIFIED focused manifest='+$manifestPath+[Environment]::NewLine
      Assert-LNOuterCapture $capture $expected '' 0 $case.id
      $manifest=[IO.File]::ReadAllText($manifestPath,$utf8)|ConvertFrom-Json -AsHashtable
      if($manifest.profiles.Count -ne 1 -or -not $manifest.profiles.ContainsKey('focused')){throw 'R3 focused manifest not exactly one profile'}
      $receipt=[IO.File]::ReadAllText($manifest.profiles.focused,$utf8)|ConvertFrom-Json
      $spec=[IO.File]::ReadAllText((Join-Path $targetOutput 'focused/spec.json'),$utf8)|ConvertFrom-Json
      $inner=@{launcher=$receipt.outer;actual=$receipt.actual;spec=$spec}
      $validation=Assert-LNWrapperCapture $inner 'focused' $repo
      $evidence=Get-LNStreamEvidencePath $validation.expectedStdout 'LIFECYCLE-REPLAY evidence=' (Join-Path $repo '.lake/lifecycle-native-p0/runs')
      $summary=[IO.File]::ReadAllText((Join-Path $evidence 'SUMMARY.json'),$utf8)|ConvertFrom-Json
      if(@($summary.selected).Count -ne 1 -or $summary.selected[0] -cne 'pop-unique'){throw 'R3 focused native selection differs'}
      $record.capture=$capture;$record.manifest=Get-LNRawPin $manifestPath;$record.receipt=Get-LNRawPin $manifest.profiles.focused;$record.summary=Get-LNRawPin (Join-Path $evidence 'SUMMARY.json');$record.validation=$validation
    }elseif($case.mode -ceq 'integrity'){
      $harness=Join-Path $PSScriptRoot '../repair-r2/harness_stream_controls.ps1'
      $targetOutput=Join-Path $out 'harness'
      $body="`$ErrorActionPreference='Stop'; & '"+$harness.Replace("'","''")+"' -OutputRoot '"+$targetOutput.Replace("'","''")+"' -ControlIds @('success-positive','error-positive')"
      [IO.File]::WriteAllText($driver,$body,$utf8)
      $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver) $repo (Join-Path $out 'capture') 300 $case.id
      $expected='STREAM CONTROL PASS success-positive'+[Environment]::NewLine+'STREAM CONTROL PASS error-positive'+[Environment]::NewLine+'STREAM CONTROLS evidence='+$targetOutput+[Environment]::NewLine
      Assert-LNOuterCapture $capture $expected '' 0 $case.id
      $resultPath=Join-Path $targetOutput 'RESULTS.json'
      $result=[IO.File]::ReadAllText($resultPath,$utf8)|ConvertFrom-Json
      if((@($result.selected)-join ',') -cne 'success-positive,error-positive'){throw 'R3 integrity pair selection differs'}
      $record.capture=$capture;$record.results=Get-LNRawPin $resultPath
    }else{throw 'R3 unsupported registry mode'}
    $record.driver=Get-LNRawPin $driver
    $records.Add($record)
    Write-Output ('R3 CONTROL PASS '+$case.id)
  }
  if(-not [string]::Equals((@($records.ToArray().id)-join ','),(@($cases.id)-join ','),[StringComparison]::Ordinal)){throw 'R3 missing/unused control'}
}catch{$failure=$_.Exception.Message}
finally{
  try {
    foreach($pin in $pins){if((Get-FileHash -LiteralPath $pin.path).Hash -cne $pin.sha256 -or ([IO.FileInfo]$pin.path).Length -ne $pin.bytes){throw ('R3 source changed: '+$pin.path)}}
    $after=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'candidate-after')
    if(-not [string]::Equals(($before|ConvertTo-Json -Depth 12 -Compress),($after|ConvertTo-Json -Depth 12 -Compress),[StringComparison]::Ordinal)){throw 'R3 live candidate changed'}
  }catch{$integrityFailure=$_.Exception.Message}
  $watch.Stop()
  $result=@{head=(& git -C $repo rev-parse HEAD).Trim();selected=@($cases.id);controls=@($records.ToArray());failure=$failure;integrityFailure=$integrityFailure;candidateUnchanged=($null -eq $integrityFailure);seconds=$watch.Elapsed.TotalSeconds;sourcePins=$pins;omittedDefaultProfiles=@($registry.defaultProfiles);defaultEvidence='actual AST default; composed six historical profiles separately revalidated'}
  [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($result|ConvertTo-Json -Depth 45),$utf8)
}
if($null -ne $failure -or $null -ne $integrityFailure){throw ('R3 controls failed: '+$failure+'; integrity: '+$integrityFailure)}
Write-Output ('R3 CONTROLS evidence='+$OutputRoot)

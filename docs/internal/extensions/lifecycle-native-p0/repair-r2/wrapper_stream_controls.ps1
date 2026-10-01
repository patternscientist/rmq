param([string]$ProfilesPath,[AllowNull()][AllowEmptyCollection()][AllowEmptyString()][string[]]$ControlIds,[string]$OutputRoot)
$ErrorActionPreference='Stop'
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$encoding=[Text.UTF8Encoding]::new($false,$true)
$nl=[Environment]::NewLine
$profiles=@('focused','full','integrity','dependencies','claims','checks')
$mutations=@('positive','extra-stdout','extra-stderr','blank-stdout','blank-stderr','missing-output','duplicate-output',
  'misleading-success','mixed-streams','wrong-exit','missing-ordinary-exit','timeout','output-limit',
  'launcher-blank-stdout','launcher-blank-stderr','launcher-output','launcher-retention-error','missing-launcher-raw')
$boundaryMutations=@('controlids-empty-array','controlids-empty-string','controlids-whitespace','controlids-unknown','controlids-duplicate','kind-missing','kind-empty','kind-unknown')
$registryPath=Join-Path $PSScriptRoot 'WRAPPER_STREAM_REGISTRY.json'
$registry=[IO.File]::ReadAllText($registryPath,$encoding)|ConvertFrom-Json
$expectedRows=@(foreach($profile in $profiles){foreach($mutation in $mutations){
  [ordered]@{id=('wrapper-'+$profile+'-'+$mutation);profile=$profile;mode='component';mutation=$mutation;
    expected=if($mutation -ceq 'positive'){'accept'}else{'reject'};predicate='Assert-LNWrapperCapture';failureSurface='Get-ExpectedWrapperFailure exact derived string'}
}};foreach($mutation in @('positive','extra-stdout','extra-stderr')){
  [ordered]@{id=('wrapper-focused-process-'+$mutation);profile='focused';mode='process';mutation=$mutation;
    expected=if($mutation -ceq 'positive'){'accept'}else{'reject'};predicate='run_owned.ps1 -> Assert-LNWrapperCapture';failureSurface='Get-ExpectedWrapperFailure exact derived string'}
};foreach($mutation in $boundaryMutations){
  [ordered]@{id=('wrapper-boundary-'+$mutation);profile='boundary';mode='boundary';mutation=$mutation;expected='reject';
    predicate=if($mutation.StartsWith('controlids-',[StringComparison]::Ordinal)){'wrapper_stream_controls.ps1 command boundary'}else{'run_owned.ps1 parameter boundary'};
    failureSurface='Exact exception message, exception type and FullyQualifiedErrorId; no other raw output'}
};[ordered]@{id='wrapper-focused-observed-mixed-holdout';profile='focused';mode='component';mutation='observed-mixed-holdout';expected='reject';
  predicate='Assert-LNOuterCapture same process-observed-stream contract';failureSurface='Get-ExpectedWrapperFailure exact derived string'})
if($registry.schemaVersion -ne 1 -or @($registry.controls).Count -ne $expectedRows.Count){throw 'WRAPPER-STREAM: registry count/schema differs'}
for($i=0;$i -lt $expectedRows.Count;$i++) {
  $row=$registry.controls[$i];$expected=$expectedRows[$i]
  if((@($row.PSObject.Properties.Name|Sort-Object)-join ',') -cne (@($expected.Keys|Sort-Object)-join ',')){throw 'WRAPPER-STREAM: registry columns differ'}
  foreach($key in $expected.Keys){if([string]$row.$key -cne [string]$expected[$key]){throw ('WRAPPER-STREAM: registry row differs at '+$i+' field '+$key)}}
}
$allIds=@($registry.controls.id)
if(@($allIds|Sort-Object -Unique).Count -ne $allIds.Count){throw 'WRAPPER-STREAM: duplicate registry ID'}
if($PSBoundParameters.ContainsKey('ControlIds')) {
  if($null -eq $ControlIds -or $ControlIds.Count -eq 0){throw 'WRAPPER-STREAM: empty selector'}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in $ControlIds){
    if([string]::IsNullOrWhiteSpace($id)){throw 'WRAPPER-STREAM: empty selector'}
    if(-not $seen.Add($id)){throw 'WRAPPER-STREAM: duplicate selector'}
    if(-not ($allIds -ccontains $id)){throw ('WRAPPER-STREAM: unknown selector '+$id)}
  }
  $selected=@($registry.controls|Where-Object {$ControlIds -ccontains $_.id})
}else{$selected=@($registry.controls)}
if([string]::IsNullOrWhiteSpace($ProfilesPath)){throw 'WRAPPER-STREAM: ProfilesPath required'}
$manifest=[IO.File]::ReadAllText([IO.Path]::GetFullPath($ProfilesPath),$encoding)|ConvertFrom-Json
if((@($manifest.profiles.PSObject.Properties.Name|Sort-Object)-join ',') -cne (@($profiles|Sort-Object)-join ',')){
  throw 'WRAPPER-STREAM: exact six-profile manifest required'
}
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r2/wrapper-stream-controls-'+[Guid]::NewGuid().ToString('N'))}
$OutputRoot=[IO.Path]::GetFullPath($OutputRoot)
if(Test-Path -LiteralPath $OutputRoot){throw 'WRAPPER-STREAM: output root must be fresh'}
[void][IO.Directory]::CreateDirectory($OutputRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1')
. (Join-Path $PSScriptRoot 'claim_expectations.ps1')
$shell=(Get-Process -Id $PID).Path
$protectedPins=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::OrdinalIgnoreCase)
$controls=[Collections.Generic.List[object]]::new()
$baselines=@{}
$claimExpectation=$null
$claimExpectationPin=$null
$claimExpectationSourceReceipt=$null
$failure=$null
$unchanged=$false

function Pin-WrapperInput([string]$Path) {
  $full=[IO.Path]::GetFullPath($Path)
  if(-not [IO.File]::Exists($full)){throw ('WRAPPER-STREAM: immutable input missing '+$full)}
  $pin=@{path=$full;bytes=([IO.FileInfo]$full).Length;sha256=(Get-FileHash -LiteralPath $full).Hash}
  if($protectedPins.ContainsKey($full)){
    $prior=$protectedPins[$full]
    if($prior.bytes -ne $pin.bytes -or $prior.sha256 -cne $pin.sha256){throw ('WRAPPER-STREAM: input changed '+$full)}
  }else{$protectedPins.Add($full,$pin)}
  return $pin
}
function Get-WrapperPins([string[]]$Paths) {
  return @(foreach($path in $Paths){if([IO.File]::Exists($path)){
    @{path=$path;bytes=([IO.FileInfo]$path).Length;sha256=(Get-FileHash -LiteralPath $path).Hash}
  }})
}
function Copy-WrapperObject($Value){return ($Value|ConvertTo-Json -Depth 30|ConvertFrom-Json)}
function Get-ExpectedWrapperFailure([string]$Profile,[string]$Mutation,[string]$Stdout,[object]$Capture) {
  switch -CaseSensitive ($Mutation) {
    'positive' {return $null}
    {$_ -in @('extra-stdout','blank-stdout','misleading-success')} {
      if($Profile -ceq 'claims'){return 'STREAM: claim footer differs'}
      return ('STREAM: wrapper-'+$Profile+' stdout differs')
    }
    {$_ -in @('extra-stderr','blank-stderr','mixed-streams')} {return ('STREAM: wrapper-'+$Profile+' stderr differs')}
    'missing-output' {
      if($Profile -ceq 'claims'){return 'STREAM: claim footer differs'}
      if($Profile -in @('focused','full')){return ('STREAM: wrapper-'+$Profile+' stdout differs')}
      return 'STREAM: evidence line missing'
    }
    'duplicate-output' {
      if($Profile -ceq 'claims'){
        if(@($claimExpectation.Records).Count -eq 0){return 'STREAM: unexpected claim output with empty record roster'}
        return ('STREAM: unexpected or duplicate claim record/text at character '+($Stdout.Length-$claimExpectation.Footer.Length))
      }
      return ('STREAM: wrapper-'+$Profile+' stdout differs')
    }
    {$_ -in @('wrong-exit','missing-ordinary-exit')} {return ('STREAM: wrapper-'+$Profile+' ordinary exit differs')}
    {$_ -in @('timeout','output-limit')} {return ('STREAM: wrapper-'+$Profile+' incomplete bounded capture')}
    'launcher-blank-stdout' {return ('STREAM: wrapper-'+$Profile+' launcher stdout differs')}
    'launcher-blank-stderr' {return ('STREAM: wrapper-'+$Profile+' launcher stderr differs')}
    'launcher-output' {return ('STREAM: wrapper-'+$Profile+' launcher output')}
    'launcher-retention-error' {return ('STREAM: wrapper-'+$Profile+' launcher retention failed')}
    'missing-launcher-raw' {return ('STREAM: raw capture missing: '+$Capture.launcher.RawStandardOutput)}
    'observed-mixed-holdout' {return 'STREAM: wrapper-observed-focused-extra-stdout stderr differs'}
    default {throw 'WRAPPER-STREAM: unmapped mutation'}
  }
}
function Load-WrapperBaseline([string]$Profile) {
  $receiptPath=[IO.Path]::GetFullPath([string]$manifest.profiles.$Profile)
  $null=Pin-WrapperInput $receiptPath
  $receipt=Read-LNExactStream $receiptPath|ConvertFrom-Json
  if($receipt.kind -cne $Profile -or -not $receipt.streamValidation.validated){throw ('WRAPPER-STREAM: positive receipt invalid '+$Profile)}
  if($Profile -ceq 'claims') {
    # The expectation is part of the actual producing wrapper's predicate.
    # Equal concatenated text is insufficient: a different tokenization can
    # recognize a different language. Require that exact produced artifact.
    $producedPin=$receipt.claimExpectation
    if($null -eq $producedPin -or [string]::IsNullOrWhiteSpace([string]$producedPin.path) -or
       [string]::IsNullOrWhiteSpace([string]$producedPin.sha256)){throw 'WRAPPER-STREAM: producing claims expectation pin missing'}
    $producedPath=[IO.Path]::GetFullPath([string]$producedPin.path)
    if($manifest.claimExpectationPath -and -not [string]::Equals(
        [IO.Path]::GetFullPath([string]$manifest.claimExpectationPath),$producedPath,[StringComparison]::OrdinalIgnoreCase)){
      throw 'WRAPPER-STREAM: manifest claims expectation differs from producing receipt'
    }
    $actualExpectationPin=Pin-WrapperInput $producedPath
    if($actualExpectationPin.bytes -ne $producedPin.bytes -or $actualExpectationPin.sha256 -cne $producedPin.sha256){
      throw 'WRAPPER-STREAM: producing claims expectation bytes/hash differ'
    }
    $script:claimExpectation=Read-LNExactStream $producedPath|ConvertFrom-Json
    Assert-LNClaimStreamExpectation ((@($script:claimExpectation.Records)-join '')+$script:claimExpectation.Footer) $script:claimExpectation
    $script:claimExpectationPin=$actualExpectationPin
    $script:claimExpectationSourceReceipt=$receiptPath
  }
  $rawSeen=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach($pin in @($receipt.raw)) {
    if(-not $rawSeen.Add([IO.Path]::GetFullPath($pin.path))){throw 'WRAPPER-STREAM: duplicate receipt raw pin'}
    $actual=Pin-WrapperInput $pin.path
    if($actual.bytes -ne $pin.bytes -or $actual.sha256 -cne $pin.sha256){throw ('WRAPPER-STREAM: raw pin differs '+$pin.path)}
  }
  $specPath=Join-Path (Split-Path -Parent $receiptPath) 'spec.json'
  if(-not $rawSeen.Contains($specPath)){throw 'WRAPPER-STREAM: unpinned capture spec'}
  $spec=Read-LNExactStream $specPath|ConvertFrom-Json
  foreach($path in @($spec.stdout,$spec.stderr,$spec.exit,$receipt.outer.RawStandardOutput,$receipt.outer.RawStandardError)) {
    if([string]::IsNullOrEmpty($path) -or -not $rawSeen.Contains([IO.Path]::GetFullPath($path))){throw 'WRAPPER-STREAM: missing current raw stream pin; historical capture uncovered'}
  }
  $actual=Read-LNExactStream $spec.exit|ConvertFrom-Json
  if(($actual|ConvertTo-Json -Compress) -cne ($receipt.actual|ConvertTo-Json -Compress)){throw 'WRAPPER-STREAM: actual exit receipt differs'}
  $capture=@{launcher=$receipt.outer;actual=$actual;spec=$spec}
  $positive=Assert-LNWrapperCapture $capture $Profile $repo $claimExpectation
  $stdout=Read-LNExactStream $spec.stdout
  # Bind the independently checked producing summary/result consumed by the
  # real predicate, including claims expectation when that profile is selected.
  switch -CaseSensitive ($Profile) {
    {$_ -in @('focused','full')} {
      $path=Get-LNStreamEvidencePath $stdout 'LIFECYCLE-REPLAY evidence=' (Join-Path $repo '.lake/lifecycle-native-p0/runs')
      $null=Pin-WrapperInput (Join-Path $path 'SUMMARY.json')
    }
    'integrity' {$line=@($stdout.Split(@($nl),[StringSplitOptions]::None)|Where-Object {$_.StartsWith('INTEGRITY CONTROLS evidence=',[StringComparison]::Ordinal)})[0];$null=Pin-WrapperInput (Join-Path $line.Substring('INTEGRITY CONTROLS evidence='.Length) 'RESULTS.json')}
    'dependencies' {$path=Get-LNStreamEvidencePath $stdout 'DEPENDENCY CONTROLS PASS evidence=' (Join-Path $repo '.lake/repair-r1');$null=Pin-WrapperInput (Join-Path $path 'RESULTS.json')}
    'checks' {$line=@($stdout.Split(@($nl),[StringSplitOptions]::None)|Where-Object {$_.StartsWith('FINAL CHECKS evidence=',[StringComparison]::Ordinal)})[0];$null=Pin-WrapperInput (Join-Path $line.Substring('FINAL CHECKS evidence='.Length) 'RESULTS.json')}
  }
  return @{receipt=$receiptPath;capture=$capture;positive=$positive;stdout=$stdout;stderr=(Read-LNExactStream $spec.stderr)}
}
function Invoke-WrapperComponent($Row,$Baseline,[string]$CaseRoot) {
  $fixture=Join-Path $CaseRoot 'fixture';$observed=Join-Path $CaseRoot 'observed'
  [void][IO.Directory]::CreateDirectory($fixture);[void][IO.Directory]::CreateDirectory($observed)
  $capture=Copy-WrapperObject $Baseline.capture
  $paths=@{stdout=$capture.spec.stdout;stderr=$capture.spec.stderr;exit=$capture.spec.exit;
    launcherStdout=$capture.launcher.RawStandardOutput;launcherStderr=$capture.launcher.RawStandardError}
  $restore=@{}
  foreach($name in $paths.Keys){$target=Join-Path $fixture ($name+'.raw');$restore[$target]=[IO.File]::ReadAllBytes($paths[$name]);[IO.File]::WriteAllBytes($target,$restore[$target])}
  $capture.spec.stdout=Join-Path $fixture 'stdout.raw';$capture.spec.stderr=Join-Path $fixture 'stderr.raw';$capture.spec.exit=Join-Path $fixture 'exit.raw'
  $capture.spec.error=Join-Path $fixture 'error';$capture.spec.overflow=Join-Path $fixture 'overflow'
  $capture.launcher.RawStandardOutput=Join-Path $fixture 'launcherStdout.raw';$capture.launcher.RawStandardError=Join-Path $fixture 'launcherStderr.raw'
  $baselineCapture=Copy-WrapperObject $capture
  $expectedFailure=Get-ExpectedWrapperFailure $Row.profile $Row.mutation $Baseline.stdout $capture
  $actualFailure=$null;$restored=$false;$pins=@();$snapshotPath=Join-Path $observed 'CAPTURE.json'
  $observedContract=$null
  try {
    switch -CaseSensitive ($Row.mutation) {
      'positive' {}
      'extra-stdout' {[IO.File]::WriteAllText($capture.spec.stdout,($Baseline.stdout+'UNEXPECTED WRAPPER STDOUT'+$nl),$encoding)}
      'extra-stderr' {[IO.File]::WriteAllText($capture.spec.stderr,($Baseline.stderr+'UNEXPECTED WRAPPER STDERR'+$nl),$encoding)}
      'blank-stdout' {[IO.File]::WriteAllText($capture.spec.stdout,($Baseline.stdout+$nl),$encoding)}
      'blank-stderr' {[IO.File]::WriteAllText($capture.spec.stderr,($Baseline.stderr+$nl),$encoding)}
      'missing-output' {
        $cut=$Baseline.stdout.LastIndexOf($nl,$Baseline.stdout.Length-$nl.Length-1,[StringComparison]::Ordinal)
        $value=if($cut -lt 0){''}else{$Baseline.stdout.Substring(0,$cut+$nl.Length)}
        [IO.File]::WriteAllText($capture.spec.stdout,$value,$encoding)
      }
      'duplicate-output' {[IO.File]::WriteAllText($capture.spec.stdout,($Baseline.stdout+$Baseline.stdout),$encoding)}
      'misleading-success' {[IO.File]::WriteAllText($capture.spec.stdout,($Baseline.stdout+'{"success":true,"validated":true}'+$nl),$encoding)}
      'mixed-streams' {[IO.File]::WriteAllText($capture.spec.stderr,($Baseline.stdout+$Baseline.stderr),$encoding)}
      'wrong-exit' {$capture.actual.exitCode=99;$capture.launcher.ExitCode=99;[IO.File]::WriteAllText($capture.spec.exit,($capture.actual|ConvertTo-Json),$encoding)}
      'missing-ordinary-exit' {$capture.actual=$null;[IO.File]::WriteAllText($capture.spec.exit,'null',$encoding)}
      'timeout' {$capture.launcher.TimedOut=$true}
      'output-limit' {$capture.launcher.OutputLimitExceeded=$true}
      'launcher-blank-stdout' {[IO.File]::WriteAllText($capture.launcher.RawStandardOutput,$nl,$encoding)}
      'launcher-blank-stderr' {[IO.File]::WriteAllText($capture.launcher.RawStandardError,$nl,$encoding)}
      'launcher-output' {$capture.launcher.StandardOutput=@('UNEXPECTED LAUNCHER OUTPUT');[IO.File]::WriteAllText($capture.launcher.RawStandardOutput,('UNEXPECTED LAUNCHER OUTPUT'+$nl),$encoding)}
      'launcher-retention-error' {$capture.launcher.RetentionErrors=@('injected isolated retention failure')}
      'missing-launcher-raw' {Remove-Item -LiteralPath $capture.launcher.RawStandardOutput}
      'observed-mixed-holdout' {
        # Same observed-stream contract used by the real extra-stdout process
        # control: the declared stdout addition is legitimate fixture data.
        $observedContract=@{expectedStdout=($Baseline.stdout+'UNEXPECTED WRAPPER STDOUT'+$nl);expectedStderr=$Baseline.stderr;expectedExit=0;profile='wrapper-observed-focused-extra-stdout'}
        [IO.File]::WriteAllText($capture.spec.stdout,$observedContract.expectedStdout,$encoding)
        Assert-LNOuterCapture $capture $observedContract.expectedStdout $observedContract.expectedStderr 0 $observedContract.profile
        $observedContract.positiveAccepted=$true
        # This second unregistered diagnostic must not hide behind the known
        # stdout rejection produced by the wrapper itself.
        [IO.File]::WriteAllText($capture.spec.stderr,($Baseline.stderr+'UNRELATED SECOND STDERR DIAGNOSTIC'+$nl),$encoding)
      }
      default {throw 'WRAPPER-STREAM: unexecuted component mutation'}
    }
    try {
      if($null -ne $observedContract){Assert-LNOuterCapture $capture $observedContract.expectedStdout $observedContract.expectedStderr 0 $observedContract.profile}
      else{$null=Assert-LNWrapperCapture $capture $Row.profile $repo $claimExpectation}
    }catch{$actualFailure=$_.Exception.Message}
    # Preserve the complete challenged objects/bytes before fixture restoration.
    $snapshot=Copy-WrapperObject $capture
    foreach($name in $paths.Keys){$from=Join-Path $fixture ($name+'.raw');$to=Join-Path $observed ($name+'.raw');if([IO.File]::Exists($from)){[IO.File]::Copy($from,$to,$false)}}
    $snapshot.spec.stdout=Join-Path $observed 'stdout.raw';$snapshot.spec.stderr=Join-Path $observed 'stderr.raw';$snapshot.spec.exit=Join-Path $observed 'exit.raw'
    $snapshot.launcher.RawStandardOutput=Join-Path $observed 'launcherStdout.raw';$snapshot.launcher.RawStandardError=Join-Path $observed 'launcherStderr.raw'
    [IO.File]::WriteAllText($snapshotPath,($snapshot|ConvertTo-Json -Depth 25),$encoding)
    $pins=Get-WrapperPins @($snapshotPath,(Join-Path $observed 'stdout.raw'),(Join-Path $observed 'stderr.raw'),(Join-Path $observed 'exit.raw'),(Join-Path $observed 'launcherStdout.raw'),(Join-Path $observed 'launcherStderr.raw'))
    if($actualFailure -cne $expectedFailure){throw ('WRAPPER-STREAM: '+$Row.id+' expected ['+$expectedFailure+'] got ['+$actualFailure+']')}
  } finally {
    foreach($path in $restore.Keys){[IO.File]::WriteAllBytes($path,$restore[$path]);if([Convert]::ToBase64String([IO.File]::ReadAllBytes($path)) -cne [Convert]::ToBase64String($restore[$path])){throw 'WRAPPER-STREAM: fixture bytes not restored'}}
    [IO.File]::WriteAllText((Join-Path $fixture 'RESTORED_CAPTURE.json'),($baselineCapture|ConvertTo-Json -Depth 25),$encoding)
    $restored=$true
  }
  return @{id=$Row.id;profile=$Row.profile;mode=$Row.mode;expected=$Row.expected;expectedFailure=$expectedFailure;actualFailure=$actualFailure;
    replayExpectedFailure=if($Row.mutation -ceq 'missing-launcher-raw'){'STREAM: raw capture missing: '+(Join-Path $observed 'launcherStdout.raw')}else{$expectedFailure};
    replayCapture=$snapshotPath;observedStreamContract=$observedContract;passed=$true;fixtureRestored=$restored;sourceReceipt=$Baseline.receipt;raw=$pins}
}
function Invoke-WrapperProcess($Row,$Baseline,[string]$CaseRoot) {
  [void][IO.Directory]::CreateDirectory($CaseRoot)
  $wrapperPath=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/run_owned.ps1'
  $source=[IO.File]::ReadAllText($wrapperPath,$encoding)
  $rootNeedle='$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot ''../../../../..''))'
  $rootReplacement='$repo='''+$repo.Replace("'","''")+''''
  $innerNeedle='$inner=Join-Path $OutputRoot ''inner.ps1'''
  if(([regex]::Matches($source,[regex]::Escape($rootNeedle))).Count -ne 1 -or
     ([regex]::Matches($source,[regex]::Escape($innerNeedle))).Count -ne 1){throw 'WRAPPER-STREAM: production wrapper fixture anchors differ'}
  $savedOut=Join-Path $CaseRoot 'positive.stdout';$savedErr=Join-Path $CaseRoot 'positive.stderr'
  [IO.File]::Copy($Baseline.capture.spec.stdout,$savedOut,$false);[IO.File]::Copy($Baseline.capture.spec.stderr,$savedErr,$false)
  $action="[Console]::Out.Write([IO.File]::ReadAllText('"+$savedOut.Replace("'","''")+"',[Text.UTF8Encoding]::new(`$false,`$true)))`n"+
    "[Console]::Error.Write([IO.File]::ReadAllText('"+$savedErr.Replace("'","''")+"',[Text.UTF8Encoding]::new(`$false,`$true)))`n"
  if($Row.mutation -ceq 'extra-stdout'){$action+="[Console]::Out.Write('UNEXPECTED WRAPPER STDOUT'+[Environment]::NewLine)`n"}
  if($Row.mutation -ceq 'extra-stderr'){$action+="[Console]::Error.Write('UNEXPECTED WRAPPER STDERR'+[Environment]::NewLine)`n"}
  $action+="exit 0`n"
  $insertion="`$action = @'`n"+$action+"'@`n"+$innerNeedle
  $derived=$source.Replace($rootNeedle,$rootReplacement).Replace($innerNeedle,$insertion)
  if($derived.Replace($insertion,$innerNeedle).Replace($rootReplacement,$rootNeedle) -cne $source){throw 'WRAPPER-STREAM: copied wrapper delta not exact'}
  $driver=Join-Path $CaseRoot 'run_owned.derived.ps1'
  [IO.File]::WriteAllText($driver,$derived,$encoding)
  $wrapperOutput=Join-Path $CaseRoot 'wrapper-output'
  $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver,'-Kind','focused','-OutputRoot',$wrapperOutput) $repo (Join-Path $CaseRoot 'outer') 300 ('wrapper-process-'+$Row.mutation)
  $expectedExit=if($Row.mutation -ceq 'positive'){0}else{1}
  Assert-LNOuterCapture $capture ('OWNED focused exit=0 evidence='+$wrapperOutput+$nl) '' $expectedExit ('wrapper-process-'+$Row.mutation)
  $receiptPath=Join-Path $wrapperOutput 'RECEIPT.json'
  $receipt=Read-LNExactStream $receiptPath|ConvertFrom-Json
  # Establish the declared two-sided observation before interpreting the
  # expected production rejection. A stdout failure cannot conceal an
  # unrelated stderr anomaly (or vice versa) in the control's own verdict.
  $innerSpec=Read-LNExactStream (Join-Path $wrapperOutput 'spec.json')|ConvertFrom-Json
  $innerCapture=@{launcher=$receipt.outer;actual=$receipt.actual;spec=$innerSpec}
  $expectedInnerStdout=$Baseline.stdout
  $expectedInnerStderr=$Baseline.stderr
  if($Row.mutation -ceq 'extra-stdout'){$expectedInnerStdout+='UNEXPECTED WRAPPER STDOUT'+$nl}
  if($Row.mutation -ceq 'extra-stderr'){$expectedInnerStderr+='UNEXPECTED WRAPPER STDERR'+$nl}
  Assert-LNOuterCapture $innerCapture $expectedInnerStdout $expectedInnerStderr 0 ('wrapper-observed-focused-'+$Row.mutation)
  $expectedFailure=Get-ExpectedWrapperFailure 'focused' $Row.mutation $Baseline.stdout $null
  if($receipt.actual.exitCode -ne 0 -or $receipt.outer.ExitCode -ne 0 -or
     [bool]$receipt.streamValidation.validated -ne ($Row.mutation -ceq 'positive') -or
     $receipt.streamValidation.failure -cne $expectedFailure){throw ('WRAPPER-STREAM: actual production verdict differs '+$Row.id)}
  $pins=@($capture.raw)+@(Get-WrapperPins @($receiptPath,$driver,$savedOut,$savedErr))
  $pins+=@($receipt.raw)
  return @{id=$Row.id;profile=$Row.profile;mode=$Row.mode;expected=$Row.expected;expectedFailure=$expectedFailure;actualFailure=$receipt.streamValidation.failure;
    passed=$true;fixtureRestored=$true;sourceReceipt=$Baseline.receipt;sourceWrapperSha256=(Get-FileHash -LiteralPath $wrapperPath).Hash;
    exactDerivedDelta='Only repository root resolution and action override immediately before original inner creation; original switch/capture/verdict retained.';
    replayMeaning='Real wrapper process and capture/verdict; saved positive native output replay, not a new native runtime experiment.';
    observedStreamContract=@{expectedStdout=$expectedInnerStdout;expectedStderr=$expectedInnerStderr;expectedExit=0;validated=$true};
    actualOuterExit=$capture.actual.exitCode;actualInnerExit=$receipt.actual.exitCode;deadlineSeconds=300;raw=$pins}
}
function Invoke-WrapperBoundary($Row,[string]$CaseRoot) {
  [void][IO.Directory]::CreateDirectory($CaseRoot)
  $isSelector=$Row.mutation.StartsWith('controlids-',[StringComparison]::Ordinal)
  $target=if($isSelector){Join-Path $PSScriptRoot 'wrapper_stream_controls.ps1'}else{Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/run_owned.ps1'}
  $arguments=@{}
  $message='';$type='System.Management.Automation.RuntimeException';$fqid=''
  switch -CaseSensitive ($Row.mutation) {
    'controlids-empty-array' {$arguments=@{ControlIds=@()};$message='WRAPPER-STREAM: empty selector'}
    'controlids-empty-string' {$arguments=@{ControlIds=@('')};$message='WRAPPER-STREAM: empty selector'}
    'controlids-whitespace' {$arguments=@{ControlIds=@(' ')};$message='WRAPPER-STREAM: empty selector'}
    'controlids-unknown' {$arguments=@{ControlIds=@('__unknown__')};$message='WRAPPER-STREAM: unknown selector __unknown__'}
    'controlids-duplicate' {$arguments=@{ControlIds=@('wrapper-focused-positive','wrapper-focused-positive')};$message='WRAPPER-STREAM: duplicate selector'}
    'kind-missing' {$message='STREAM: wrapper Kind is required'}
    {$_ -in @('kind-empty','kind-unknown')} {
      $value=if($_ -ceq 'kind-empty'){''}else{'__unknown__'}
      $arguments=@{Kind=$value}
      $message="Cannot validate argument on parameter 'Kind'. The argument `""+$value+"`" does not belong to the set `"focused,full,integrity,dependencies,claims,checks`" specified by the ValidateSet attribute. Supply an argument that is in the set and then try the command again."
      $type='System.Management.Automation.ParameterBindingValidationException'
      $fqid='ParameterArgumentValidationError,run_owned.ps1'
    }
    default {throw 'WRAPPER-STREAM: unmapped boundary mutation'}
  }
  if($fqid -ceq ''){$fqid=$message}
  $testSpec=@{id=$Row.id;target=$target;arguments=$arguments;message=$message;type=$type;fqid=$fqid;errorArtifact=(Join-Path $CaseRoot 'ERROR.json')}
  $testSpecPath=Join-Path $CaseRoot 'BOUNDARY_SPEC.json'
  [IO.File]::WriteAllText($testSpecPath,($testSpec|ConvertTo-Json -Depth 8),$encoding)
  $driver=Join-Path $CaseRoot 'boundary.ps1'
  [IO.File]::WriteAllText($driver,@'
param([string]$SpecPath)
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$spec=[IO.File]::ReadAllText($SpecPath,$utf8)|ConvertFrom-Json
$arguments=@{}
foreach($property in $spec.arguments.PSObject.Properties){$arguments[$property.Name]=$property.Value}
$failure=$null
try { & $spec.target @arguments } catch {
  $failure=@{message=$_.Exception.Message;type=$_.Exception.GetType().FullName;fqid=$_.FullyQualifiedErrorId}
  [IO.File]::WriteAllText($spec.errorArtifact,($failure|ConvertTo-Json),$utf8)
}
if($null -eq $failure -or $failure.message -cne $spec.message -or $failure.type -cne $spec.type -or $failure.fqid -cne $spec.fqid){throw 'boundary exception differs'}
[Console]::Out.Write('BOUNDARY REJECTED '+$spec.id+[Environment]::NewLine)
exit 0
'@,$encoding)
  $capture=Invoke-LNStreamCapture $repo $shell @('-NoProfile','-File',$driver,'-SpecPath',$testSpecPath) $repo (Join-Path $CaseRoot 'outer') 300 $Row.id
  Assert-LNOuterCapture $capture ('BOUNDARY REJECTED '+$Row.id+$nl) '' 0 $Row.id
  return @{id=$Row.id;profile=$Row.profile;mode=$Row.mode;expected=$Row.expected;expectedFailure=$message;actualFailure=$message;
    expectedExceptionType=$type;expectedFullyQualifiedErrorId=$fqid;passed=$true;fixtureRestored=$true;actualOuterExit=$capture.actual.exitCode;
    targetBoundary='Actual script parameter/selector invocation in a caught child scope; target exception is not a target ordinary process exit.';
    raw=(@($capture.raw)+@(Get-WrapperPins @($driver,$testSpecPath,$testSpec.errorArtifact)))}
}
try {
  foreach($path in @($ProfilesPath,$registryPath,$PSCommandPath,(Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1'),
    (Join-Path $repo 'scripts/owned_process_tree.ps1'),(Join-Path $repo 'scripts/packed_native_lifecycle_storage_replay.ps1'),
    (Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/run_owned.ps1'),(Join-Path $PSScriptRoot 'claim_expectations.ps1'))){$null=Pin-WrapperInput $path}

  foreach($profile in @($selected|Where-Object {$_.mode -cne 'boundary'}|ForEach-Object {$_.profile}|Select-Object -Unique)){$baselines[$profile]=Load-WrapperBaseline $profile}
  foreach($row in $selected) {
    $caseRoot=Join-Path $OutputRoot $row.id
    $watch=[Diagnostics.Stopwatch]::StartNew()
    $result=switch -CaseSensitive ($row.mode) {
      'component' {Invoke-WrapperComponent $row $baselines[$row.profile] $caseRoot}
      'process' {Invoke-WrapperProcess $row $baselines[$row.profile] $caseRoot}
      'boundary' {Invoke-WrapperBoundary $row $caseRoot}
      default {throw 'WRAPPER-STREAM: unknown registry mode'}
    }
    $watch.Stop();$result.seconds=$watch.Elapsed.TotalSeconds
    $controls.Add($result)
    Write-Output ('WRAPPER CONTROL PASS '+$row.id)
  }
  if((@($controls.id)-join ',') -cne (@($selected.id)-join ',')){throw 'WRAPPER-STREAM: executed registry differs'}
} catch {$failure=$_.Exception.Message} finally {
  try {
    foreach($pin in @($protectedPins.Values)){
      if(-not [IO.File]::Exists($pin.path) -or ([IO.FileInfo]$pin.path).Length -ne $pin.bytes -or
         (Get-FileHash -LiteralPath $pin.path).Hash -cne $pin.sha256){throw ('WRAPPER-STREAM: immutable input changed '+$pin.path)}
    }
    $unchanged=$true
  }catch{if($null -eq $failure){$failure=$_.Exception.Message}else{$failure+=' | '+$_.Exception.Message}}
  $report=@{success=($null -eq $failure);failure=$failure;registryCount=$allIds.Count;selected=@($selected.id);controls=@($controls.ToArray());
    immutableInputsUnchanged=$unchanged;sourcePins=@($protectedPins.Values);profileManifest=[IO.Path]::GetFullPath($ProfilesPath);
    claimExpectationPin=$claimExpectationPin;claimExpectationSourceReceipt=$claimExpectationSourceReceipt;
    fixtureBoundary='Only owned copies are mutated/restored; original raw captures and producer summaries remain pinned and unchanged.'}
  [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($report|ConvertTo-Json -Depth 30),$encoding)
}
if($null -ne $failure){throw $failure}
Write-Output ('WRAPPER STREAM CONTROLS PASS evidence='+$OutputRoot)

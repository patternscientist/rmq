param([int]$DeadlineSeconds=30)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
if([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT){throw 'SELECTOR-CONTROLS: Windows raw-stream profile required'}
if($DeadlineSeconds -le 0){throw 'SELECTOR-CONTROLS: positive deadline required'}
$registryPath=Join-Path $PSScriptRoot 'native_selector_controls.json'
$registryBytes=[IO.File]::ReadAllBytes($registryPath)
if((Get-LN1BytesHash $registryBytes) -cne 'fb9d38afd5ca8b8ff1313c355e7c649cb6e3e44777eef9a1915b818585ef67b5'){
  throw 'SELECTOR-CONTROLS: frozen expected control bytes differ'
}
$registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
$expectedIds=@('caller-omitted','caller-known','caller-null','caller-empty-array','caller-empty-string',
  'caller-whitespace','caller-unknown','caller-duplicate','registry-intact','registry-omit-middle',
  'registry-duplicate-middle','registry-reorder-middle','stream-extra-newline','stream-extra-text',
  'stream-extra-stderr','stream-wrong-exit','stream-exact-bytes','stream-bom','stream-nul',
  'stream-crlf-to-lf','stream-invalid-utf8','stream-output-overflow','caller-deadline-max','caller-deadline-overflow',
  'caller-known-plus-nul','caller-known-plus-soft-hyphen','caller-known-plus-zero-width-space','caller-known-plus-bom',
  'control-name-known-boundary','control-name-known-plus-nul','control-name-known-plus-soft-hyphen',
  'control-name-known-plus-zero-width-space','control-name-known-plus-bom')
if($registry.schema -cne 'lifecycle-native1-selector-controls-v2' -or
  ($registry.orderedIds -join '|') -cne ($expectedIds -join '|') -or
  ($registry.cases.id -join '|') -cne ($expectedIds -join '|') -or @($registry.fixtureIds).Count -ne 13){
  throw 'SELECTOR-CONTROLS: frozen registry roster differs'
}
$liveRegistry=Join-Path $root 'scripts/lifecycle_native_cases.json'
$liveBytes=[IO.File]::ReadAllBytes($liveRegistry)
if((Get-LN1BytesHash $liveBytes) -cne '9dc72366b51592f18dc50e52d2b799c736dc047e6166538a0a880192062985fd'){
  throw 'SELECTOR-CONTROLS: source fixture bytes differ'
}
$fixture=$utf8.GetString($liveBytes)|ConvertFrom-Json
if(($fixture.orderedIds -join '|') -cne ($registry.fixtureIds -join '|')){throw 'SELECTOR-CONTROLS: expected full fixture roster differs'}
$run=Join-Path $root ('.lake/lifecycle-native1/selector-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
$allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake/lifecycle-native1/selector-controls')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not [IO.Path]::GetFullPath($run).StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase)){throw 'SELECTOR-CONTROLS: evidence scope'}
$scratch=Join-Path $run 'disposable'
$sourceRel=@('scripts/lifecycle_native_replay.ps1','scripts/lifecycle_native_identity.ps1',
  'scripts/lifecycle_native_cases.json','scripts/owned_process_tree.ps1',
  'scripts/packed_native_lifecycle_stream_check.ps1','scripts/packed_native_lifecycle_storage_replay.ps1',
  'scripts/packed_native_lifecycle_integrity_check.ps1')
$pins=[Collections.Generic.List[object]]::new()
$shell=$null
$pinSetupComplete=$false;$setupComplete=$false;$receiptError=$null
$results=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-selector-control-results-v2';success=$false;
  boundary=$registry.boundary;startedUtc=[DateTime]::UtcNow.ToString('o');
  registry=$null;sourcePins=@();controls=@();failure=$null;integrity=$null;cleanup=$null;
  setup=@{complete=$false;pinSetComplete=$false;expectedPins=($sourceRel.Count+3)};
  failureStage=$null;semanticChildInvocations=0;finalReceiptAttempted=$false;
  deadlineSeconds=$DeadlineSeconds;deadlineRationale='Cheap PowerShell validation callers: existing export selector controls use 30 seconds; no native, Lean, or heavy mutex acquisition.'}
function Quote-SC([string]$Text){return "'"+$Text.Replace("'","''")+"'"}
function Remove-SCScratch {
  $full=[IO.Path]::GetFullPath($scratch)
  $prefix=[IO.Path]::GetFullPath($run).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
    $full -cne [IO.Path]::GetFullPath((Join-Path $run 'disposable'))){throw 'SELECTOR-CONTROLS: cleanup target outside owned scratch'}
  if([IO.Directory]::Exists($full)){
    $entries=@(Get-Item -LiteralPath $full)+@(Get-ChildItem -LiteralPath $full -Recurse -Force)
    foreach($entry in $entries){if($entry.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'SELECTOR-CONTROLS: cleanup refuses reparse point'}}
    Remove-Item -LiteralPath $full -Recurse -Force
  }
  if([IO.Directory]::Exists($full)){throw 'SELECTOR-CONTROLS: scratch remained'}
}
function Expected-SCOutput([int]$Count){
  $ids=if($Count -eq 13){$registry.fixtureIds -join ','}elseif($Count -eq 1){$registry.knownId}else{throw 'SELECTOR-CONTROLS: invalid expected count'}
  return 'LIFECYCLE-REPLAY VALIDATED cases='+$Count+' ids='+$ids+"`r`n"
}
try{
  # Acquisition and every source/tool pin belong to this protected lifetime.
  # Add pins individually so a later setup exception retains earlier evidence.
  [void][IO.Directory]::CreateDirectory($run)
  [void][IO.Directory]::CreateDirectory($scratch)
  $pins.Add((Get-LN1Pin $PSCommandPath))
  $report.registry=Get-LN1Pin $registryPath;$pins.Add($report.registry)
  $shell=(Get-Process -Id $PID).Path;$pins.Add((Get-LN1Pin $shell))
  foreach($relative in $sourceRel){$pins.Add((Get-LN1Pin (Join-Path $root $relative)))}
  $pinSetupComplete=$true;$report.sourcePins=@($pins.ToArray())
  $report.setup.pinSetComplete=$true
  [IO.File]::WriteAllText((Join-Path $run 'PLAN.json'),($report|ConvertTo-Json -Depth 12),$utf8)
  $setupComplete=$true;$report.setup.complete=$true
  foreach($case in $registry.cases){
    $entry=Join-Path $root 'scripts/lifecycle_native_replay.ps1'
    $argument=' -Cases '+(Quote-SC $registry.knownId)
    $mutationPin=$null
    if($case.handler -ceq 'registry'){
      $copyRoot=Join-Path $scratch $case.id
      [void][IO.Directory]::CreateDirectory((Join-Path $copyRoot 'scripts'))
      foreach($relative in $sourceRel){[IO.File]::Copy((Join-Path $root $relative),(Join-Path $copyRoot $relative),$false)}
      $entry=Join-Path $copyRoot 'scripts/lifecycle_native_replay.ps1'
      $copyRegistry=Join-Path $copyRoot 'scripts/lifecycle_native_cases.json'
      if($case.mutation -cne 'none'){
        $copy=$utf8.GetString($liveBytes)|ConvertFrom-Json
        switch -CaseSensitive ($case.mutation){
          'omit' {$copy.cases=@($copy.cases[0..5])+@($copy.cases[7..12])}
          'duplicate' {$copy.cases[6]=$copy.cases[5]}
          'reorder' {$item=$copy.cases[5];$copy.cases[5]=$copy.cases[6];$copy.cases[6]=$item}
          default {throw 'SELECTOR-CONTROLS: unknown registry mutation'}
        }
        [IO.File]::WriteAllText($copyRegistry,($copy|ConvertTo-Json -Depth 20),$utf8)
      }
      $savedRegistry=Join-Path $run ($case.id+'-registry.json')
      [IO.File]::Copy($copyRegistry,$savedRegistry,$false)
      $mutationPin=Get-LN1Pin $savedRegistry
    }elseif($case.handler -ceq 'caller'){
      switch -CaseSensitive ($case.selector){
        'omitted' {$argument=''}
        'known' {}
        'null' {$argument=' -Cases $null'}
        'empty-array' {$argument=' -Cases @()'}
        'empty-string' {$argument=" -Cases ''"}
        'whitespace' {$argument=" -Cases ' '"}
        'unknown' {$argument=" -Cases 'LN1-UNKNOWN'"}
        'duplicate' {$argument=' -Cases @('+(Quote-SC $registry.knownId)+','+(Quote-SC $registry.knownId)+')'}
        'deadline-max' {$argument+=' -CaseDeadlineSeconds 2147483647'}
        'deadline-overflow' {$argument+=" -CaseDeadlineSeconds '2147483648'"}
        'known-plus-codepoint' {$argument=' -Cases ('+(Quote-SC $registry.knownId)+'+[char]'+[string]$case.codePoint+')'}
        default {throw 'SELECTOR-CONTROLS: unknown caller selector'}
      }
    }elseif($case.handler -ceq 'control-name'){
      # Omitting BuildReceipt makes the known-name control stop at the next
      # pre-output guard; malformed names must stop at the selector guard.
      $argument=" -ControlName 'none'"
      if($case.selector -ceq 'known-plus-codepoint'){$argument=" -ControlName ('none'+[char]"+[string]$case.codePoint+')'}
      elseif($case.selector -cne 'known'){throw 'SELECTOR-CONTROLS: unknown control-name selector'}
    }elseif($case.handler -cne 'stream'){throw 'SELECTOR-CONTROLS: unknown handler'}
    $prefix=''
    # The Unicode callers must retain their actual exception text, without
    # Windows Console best-fit conversion of format characters to ASCII.
    if($case.selector -ceq 'known-plus-codepoint'){$prefix='[Console]::OutputEncoding=[Text.UTF8Encoding]::new($false,$true)'}
    $invocation='& '+(Quote-SC $entry)+' -Phase Validate'+$argument
    if($case.handler -ceq 'control-name'){$invocation='& '+(Quote-SC $entry)+' -Phase ControlDiscovery -Variant testing'+$argument}
    $suffix='exit $LASTEXITCODE'
    if($case.handler -ceq 'stream'){
      switch -CaseSensitive ($case.mutation){
        'newline' {$suffix='[Console]::Out.Write("`n"); exit 0'}
        'text' {$suffix='[Console]::Out.Write("unexpected`n"); exit 0'}
        'stderr' {$suffix='[Console]::Error.Write("unexpected`n"); exit 0'}
        'exit' {$suffix='exit 7'}
        'exact' {}
        'bom' {$prefix='$scStream=[Console]::OpenStandardOutput(); $scStream.Write([byte[]]@(239,187,191),0,3); $scStream.Flush()'}
        'nul' {$suffix='$scStream=[Console]::OpenStandardOutput(); $scStream.WriteByte(0); $scStream.Flush(); exit 0'}
        'crlf-to-lf' {
          # The hostile caller changes the actual returned line ending. The
          # acceptance predicate still requires the untouched CRLF byte stream.
          $invocation='$scLines=@('+ $invocation+'); foreach($scLine in $scLines){[Console]::Out.Write([string]$scLine+"`n")}'
        }
        'invalid-utf8' {$suffix='$scStream=[Console]::OpenStandardOutput(); $scStream.WriteByte(255); $scStream.Flush(); exit 0'}
        'output-overflow' {
          $suffix='$scBytes=[byte[]]::new('+[string]$case.emittedExtraBytes+'); $scStream=[Console]::OpenStandardOutput(); $scStream.Write($scBytes,0,$scBytes.Length); $scStream.Flush(); exit 0'
        }
        default {throw 'SELECTOR-CONTROLS: unknown stream mutation'}
      }
    }
    # These literal PowerShell arguments exercise actual parameter binding. The
    # catch only makes the production exception message a deterministic stream;
    # it does not reimplement or override the production selector predicate.
    $caller=Join-Path $run ($case.id+'-caller.ps1')
    $body='$ErrorActionPreference="Stop"'+"`ntry {`n"+$prefix+"`n"+$invocation+"`n"+$suffix+
      "`n} catch {`n"+'[Console]::Error.Write("SELECTOR-CALL ERROR: "+$_.Exception.Message+"`n"); exit 1'+"`n}`n"
    [IO.File]::WriteAllText($caller,$body,$utf8)
    $report.semanticChildInvocations++
    $capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$caller) $root (Join-Path $run $case.id) $DeadlineSeconds $case.id
    $expectedOut='';$expectedErr='';$expectedExit=0;$rejected=$null;$rawEvidence=$null
    if($case.handler -ceq 'stream'){
      $expectedOut=Expected-SCOutput 1
      $actualOut=$expectedOut;$actualErr=''
      switch($case.mutation){
        'newline'{$actualOut+="`n"};'text'{$actualOut+="unexpected`n"};'stderr'{$actualErr="unexpected`n"}
        'bom'{$actualOut=([string][char]0xFEFF)+$actualOut}
        'nul'{$actualOut+=[string][char]0}
        'crlf-to-lf'{$actualOut=$actualOut.Replace("`r`n","`n")}
      }
      if($case.mutation -ceq 'output-overflow'){
        # This is a real producer exceeding the unchanged raw child's bound.
        # Depending on the polling race, its own ordinary exit may be absent;
        # keep the actual nullable receipt and never invent a successful exit.
        $size=([IO.FileInfo]$capture.spec.stdout).Length
        if($capture.spec.outputLimit -ne $case.outputLimitBytes -or $size -le $case.outputLimitBytes -or
          -not [IO.File]::Exists($capture.spec.overflow) -or [IO.File]::Exists($capture.spec.error) -or
          $capture.launcher.ExitCode -ne $case.launcherExit -or $capture.launcher.TimedOut -or
          $capture.launcher.OutputLimitExceeded){throw 'SELECTOR-CONTROLS: actual output overflow not observed'}
        $prefixBytes=$utf8.GetBytes($expectedOut);$stream=[IO.File]::OpenRead($capture.spec.stdout)
        try{$prefixRead=[byte[]]::new($prefixBytes.Length);$read=$stream.Read($prefixRead,0,$prefixRead.Length)}finally{$stream.Dispose()}
        if($read -ne $prefixBytes.Length -or [Convert]::ToHexString($prefixRead) -cne [Convert]::ToHexString($prefixBytes)){
          throw 'SELECTOR-CONTROLS: overflow did not follow actual validated caller output'
        }
        Assert-LNExactStreamText (Read-LNExactStream $capture.spec.stderr) '' ($case.id+' producer stderr')
        Assert-LNExactStreamText (Read-LNExactStream $capture.launcher.RawStandardOutput) '' ($case.id+' launcher stdout')
        Assert-LNExactStreamText (Read-LNExactStream $capture.launcher.RawStandardError) '' ($case.id+' launcher stderr')
        $rawEvidence=@{capturedBytes=$size;bound=$capture.spec.outputLimit;
          overflow=(Get-LN1Pin $capture.spec.overflow);actualProducerExit=$capture.actual;
          actualLauncherExit=$capture.launcher.ExitCode;partialOutputIsSemanticFailure=$true}
      }else{
        [byte[]]$actualBytes=$utf8.GetBytes($actualOut)
        if($case.mutation -ceq 'invalid-utf8'){$actualBytes=[byte[]]@($actualBytes+[byte]255)}
        $capturedBytes=[IO.File]::ReadAllBytes($capture.spec.stdout)
        if([Convert]::ToHexString($capturedBytes) -cne [Convert]::ToHexString($actualBytes)){
          throw ('SELECTOR-CONTROLS: actual emitted bytes differ '+$case.id)
        }
        Assert-LNExactStreamText (Read-LNExactStream $capture.spec.stderr) $actualErr ($case.id+' actual stderr')
        $rawEvidence=@{capturedBytes=$capturedBytes.Length;expectedActualHex=[Convert]::ToHexString($actualBytes);
          actualProducerExit=$capture.actual;actualLauncherExit=$capture.launcher.ExitCode}
        if($case.mutation -cne 'invalid-utf8'){
          Assert-LNOuterCapture $capture $actualOut $actualErr $case.actualExit ($case.id+'-actual')
        }elseif($capture.actual.exitCode -ne $case.actualExit -or $capture.launcher.ExitCode -ne $case.actualExit){
          throw 'SELECTOR-CONTROLS: invalid-UTF8 producer ordinary exit differs'
        }
      }
      if($case.mutation -ceq 'exact'){
        Assert-LNOuterCapture $capture $expectedOut '' 0 $case.id
      }else{
        try{Assert-LNOuterCapture $capture $expectedOut '' 0 $case.id}
        catch{$rejected=$_.Exception.Message}
        $expectedRejection=if($case.mutation -ceq 'invalid-utf8'){'STREAM: invalid UTF-8 capture: '+$capture.spec.stdout}
          elseif($case.mutation -ceq 'output-overflow'){'STREAM: '+$case.id+' incomplete bounded capture'}
          else{'STREAM: '+$case.id+' '+$case.rejectionSurface+' differs'}
        if($rejected -cne $expectedRejection){throw ('SELECTOR-CONTROLS: exact stream rejection differs '+$case.id)}
      }
    }else{
      $expectedExit=[int]$case.expectedExit
      if($expectedExit -eq 0){$expectedOut=Expected-SCOutput $case.expectedCount}
      else{$expectedErr='SELECTOR-CALL ERROR: '+$case.expectedError+"`n"}
      Assert-LNOuterCapture $capture $expectedOut $expectedErr $expectedExit $case.id
    }
    $results.Add([ordered]@{id=$case.id;handler=$case.handler;passed=$true;capture=$capture;
      caller=(Get-LN1Pin $caller);copiedRegistry=$mutationPin;expectedStdout=$expectedOut;
      expectedStderr=$expectedErr;expectedExit=$expectedExit;productionStreamRejection=$rejected;rawEvidence=$rawEvidence})
  }
  if(($results.id -join '|') -cne ($expectedIds -join '|')){throw 'SELECTOR-CONTROLS: completed roster differs'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message;$report.failureStage=if($setupComplete){'controls'}else{'setup'}}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed source '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{attempted=$true;success=($errors.Count -eq 0);checked=$pins.Count;initialPinSetComplete=$pinSetupComplete;errors=@($errors.ToArray())}
  if($errors.Count){$report.success=$false}
  try{Remove-SCScratch;$report.cleanup=@{attempted=$true;success=$true;removedScratch=$scratch;liveSourcesNeverEdited=$true}}
  catch{$report.cleanup=@{attempted=$true;success=$false;error=$_.Exception.Message};$report.success=$false}
  $report.controls=@($results.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  $report.sourcePins=@($pins.ToArray());$report.finalReceiptAttempted=$true
  try{
    [void][IO.Directory]::CreateDirectory($run)
    [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 25),$utf8)
  }catch{$receiptError=$_.Exception.Message;$report.success=$false}

}
Write-Output ('NATIVE-SELECTOR-CONTROLS evidence='+$run)
if(-not $report.success){
  Write-Output ('NATIVE-SELECTOR-CONTROLS FAIL '+$report.failure)
  if($receiptError){Write-Output ('NATIVE-SELECTOR-CONTROLS receipt failure '+$receiptError)}
  exit 1
}
Write-Output ('NATIVE-SELECTOR-CONTROLS PASS controls='+$results.Count)

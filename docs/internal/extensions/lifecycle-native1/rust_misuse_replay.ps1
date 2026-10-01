[CmdletBinding()]
param(
  [ValidateSet('Discovery','Replay')][string]$Mode='Replay',
  [AllowNull()][AllowEmptyCollection()][AllowEmptyString()][object[]]$OnlyCase,
  [switch]$SelectorProbeOnly,
  [string]$DiagnosticsPath='',
  [string]$DiagnosticsSHA256='',
  [string]$RustRoot='C:/Users/poin/.rustup/toolchains/stable-x86_64-pc-windows-msvc'
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
if($Mode -cnotin @('Discovery','Replay')){throw 'RUST-MISUSE: exact mode spelling required'}
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
# Fixed independent clients of the real facade. Compiler rejection is required;
# no foreign object is constructed and no undefined-behavior test is executed.
$cases=@(
  @{id='RS-RUNTIME-SEND';code='E0277';source='fn demand<T: Send>() {} demand::<LifecycleRuntime>();'},
  @{id='RS-RUNTIME-SYNC';code='E0277';source='fn demand<T: Sync>() {} demand::<LifecycleRuntime>();'},
  @{id='RS-OWNER-SEND';code='E0277';source="fn demand<T: Send>() {} demand::<Owner<'static>>();"},
  @{id='RS-OWNER-SYNC';code='E0277';source="fn demand<T: Sync>() {} demand::<Owner<'static>>();"},
  @{id='RS-OBSERVATION-SEND';code='E0277';source="fn demand<T: Send>() {} demand::<Observation<'static>>();"},
  @{id='RS-OBSERVATION-SYNC';code='E0277';source="fn demand<T: Sync>() {} demand::<Observation<'static>>();"},
  @{id='RS-NATURAL-SEND';code='E0277';source="fn demand<T: Send>() {} demand::<Natural<'static>>();"},
  @{id='RS-NATURAL-SYNC';code='E0277';source="fn demand<T: Sync>() {} demand::<Natural<'static>>();"},
  @{id='RS-RESULT-SEND';code='E0277';source="fn demand<T: Send>() {} demand::<QueryResult<'static>>();"},
  @{id='RS-RESULT-SYNC';code='E0277';source="fn demand<T: Sync>() {} demand::<QueryResult<'static>>();"},
  @{id='RS-OWNER-CLONE';code='E0277';source="fn duplicate(owner: &Owner<'_>) { let _ = Owner::clone(owner); }"},
  @{id='RS-IMMUTABLE-QUERY';code='E0596';source="fn mutate(owner: &Owner<'_>) { let _ = owner.query(&[], &[], false); }"},
  @{id='RS-BYTES-ESCAPE';code='E0515';source="fn escape<'a>(answer: Natural<'a>) -> &'a [u8] { answer.bytes() }"},
  @{id='RS-RAW-ALIAS';code='E0616';source="fn alias(owner: &Owner<'_>) { let _ = owner.raw; }"},
  @{id='RS-RUNTIME-ESCAPE';code='E0515';source="fn escape() -> Owner<'static> { let runtime = LifecycleRuntime::new().unwrap(); let bytes = runtime.profile(0).unwrap().endpoint(&[0]).unwrap(); let (owner, answer) = runtime.build_first(Model::Comparison, &[], &bytes, &bytes, false).unwrap(); drop(answer); owner }"},
  @{id='RS-ACCEPT-MUTABLE';code='';source="fn mutate(owner: &mut Owner<'_>) { let _ = owner.query(&[], &[], false); }"},
  @{id='RS-ACCEPT-BORROW';code='';source="fn view<'a>(answer: &'a Natural<'_>) -> &'a [u8] { answer.bytes() }"}
)
$mappingText=(@($cases|ForEach-Object{$_.id+"`t"+$_.code+"`t"+$_.source}) -join "`n")+"`n"
$mappingHash=Get-LN1BytesHash ($utf8.GetBytes($mappingText))
if($cases.Count -ne 17 -or $mappingHash -cne '8c5f71775d51a892b23267b79ddf60982b77bdb1174ca83ee7efe0e977ec7de6'){
  throw 'RUST-MISUSE: fixed ordered ID/code/source mapping differs'
}
$allIds=@($cases|ForEach-Object{$_.id})
$knownIds=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach($id in $allIds){[void]$knownIds.Add($id)}
$selected=$allIds
if($PSBoundParameters.ContainsKey('OnlyCase')){
  if($null -eq $OnlyCase -or $OnlyCase.Count -eq 0){throw 'RUST-MISUSE: empty bound selector'}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in $OnlyCase){
    if($id -isnot [string] -or [string]::IsNullOrWhiteSpace($id) -or -not $knownIds.Contains($id) -or -not $seen.Add($id)){
      throw 'RUST-MISUSE: invalid or duplicate selector'
    }
  }
  $selected=@($OnlyCase)
}
if($SelectorProbeOnly){Write-Output ('RUST-MISUSE SELECTED '+($selected -join ','));exit 0}
$frozen=$null
if($Mode -ceq 'Replay'){
  if(-not $DiagnosticsPath -or $DiagnosticsSHA256 -notmatch '^[a-fA-F0-9]{64}$' -or
      (Get-FileHash -LiteralPath $DiagnosticsPath).Hash -ine $DiagnosticsSHA256){throw 'RUST-MISUSE: frozen diagnostic identity required'}
  $frozen=[IO.File]::ReadAllText($DiagnosticsPath,$utf8)|ConvertFrom-Json
  if($frozen.schema -cne 'lifecycle-native1-rust-diagnostics-v1' -or
      $frozen.status -cne 'FROZEN_ROOT_REVIEWED' -or $frozen.mappingSHA256 -cne $mappingHash -or
      (@($frozen.cases|ForEach-Object{$_.id}) -join '|') -cne ($allIds -join '|')){throw 'RUST-MISUSE: full ordered diagnostic roster differs'}
}
$run=Join-Path $root ('.lake/lifecycle-native1/rust-misuse/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$caseRoot=Join-Path $run 'cases'
[void][IO.Directory]::CreateDirectory($caseRoot)
$pins=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$diagnostics=[Collections.Generic.List[object]]::new()
$inputFingerprint=$null
$mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
$locked=$false
$report=[ordered]@{schema='lifecycle-native1-rust-misuse-v1';mode=$Mode;success=$false;selected=$selected;
  completeRegistry=(($selected -join '|') -ceq ($allIds -join '|'));startedUtc=[DateTime]::UtcNow.ToString('o');
  deadlineSeconds=60;deadlineRationale='Metadata-only facade and tiny independent callers; prior release client stages completed within the 300-second native bound. Narrow discovery ceiling is 60 seconds per compiler.';
  pins=@();results=@();failure=$null;integrity=$null;cleanup=$null}
function Pin-RustMisuse([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
try{
  $locked=$mutex.WaitOne(0);if(-not $locked){throw 'RUST-MISUSE: shared heavy slot busy'}
  $report.contract=Assert-LN1FrozenContract $root
  foreach($path in @($PSCommandPath,(Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
      (Join-Path $root 'scripts/owned_process_tree.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){[void](Pin-RustMisuse $path)}
  foreach($file in Get-ChildItem -LiteralPath (Join-Path $root 'native/packed-rmq/src') -Recurse -File -Filter '*.rs'){[void](Pin-RustMisuse $file.FullName)}
  foreach($part in @('bin','lib')){
    foreach($file in Get-ChildItem -LiteralPath (Join-Path $RustRoot $part) -Recurse -File){[void](Pin-RustMisuse $file.FullName)}
  }
  $fingerprintText=(@($pins|Sort-Object path|ForEach-Object{$_.path+"`t"+$_.bytes+"`t"+$_.sha256}) -join "`n")+"`n"
  $inputFingerprint=Get-LN1BytesHash ($utf8.GetBytes($fingerprintText))
  if($Mode -ceq 'Replay' -and $frozen.inputFingerprint -cne $inputFingerprint){throw 'RUST-MISUSE: reviewed producer/tool/runner recipe changed'}
  if($DiagnosticsPath){[void](Pin-RustMisuse $DiagnosticsPath)}
  $report.inputFingerprint=$inputFingerprint
  $rustc=Join-Path $RustRoot 'bin/rustc.exe'
  $common=@('--edition=2021','--color=never','--error-format=human',('--remap-path-prefix='+$root+'=RMQ'),('--remap-path-prefix='+$caseRoot+'=LN1-RUST'))
  $library=Join-Path $caseRoot 'libpacked_rmq.rmeta'
  $producer=Invoke-LN1Stage -File $rustc -Arguments ($common+@('--crate-type=rlib','--crate-name','packed_rmq','--emit=metadata',(Join-Path $root 'native/packed-rmq/src/lib.rs'),'-o',$library)) -Stage 'facade' -DeadlineSeconds 60 -OutputRoot (Join-Path $run 'facade') -WorkingDirectory $root
  Assert-LNOuterCapture $producer '' '' 0 'facade'
  [void](Pin-RustMisuse $library)
  $report.producer=$producer
  foreach($id in $selected){
    $case=@($cases|Where-Object{$_.id -ceq $id})[0]
    $source="#![allow(dead_code, unused_imports, unused_variables)]`nuse packed_rmq::lifecycle::{LifecycleRuntime, Model, Owner, Observation, Natural, QueryResult};`nfn main() {`n"+$case.source+"`n}`n"
    $sourcePath=Join-Path $caseRoot ($id+'.rs')
    [IO.File]::WriteAllText($sourcePath,$source,$utf8)
    $sourcePin=Pin-RustMisuse $sourcePath
    $arguments=$common+@('--crate-name','misuse','--emit=metadata','--extern',('packed_rmq='+$library),$sourcePath,'-o',(Join-Path $caseRoot ($id+'.rmeta')))
    $capture=Invoke-LNStreamCapture $root $rustc $arguments $root (Join-Path $run $id) 60 $id
    $stdout=Read-LNExactStream $capture.spec.stdout;$stderr=Read-LNExactStream $capture.spec.stderr
    $exitCode=if($case.code){1}else{0}
    Assert-LNOuterCapture $capture '' $stderr $exitCode $id
    if($case.code){
      $codes=@([regex]::Matches($stderr,'(?m)^error\[(E[0-9]+)\]:')|ForEach-Object{$_.Groups[1].Value})
      if($codes.Count -eq 0 -or @($codes|Where-Object{$_ -cne $case.code}).Count -ne 0){throw ('RUST-MISUSE: unintended diagnostic surface '+$id)}
      if($stderr -match '(?m)^warning(?:\[|:)' -or $stderr -match '(?m)^error: (?!aborting due to )'){
        throw ('RUST-MISUSE: unrelated uncoded diagnostic '+$id)
      }
    }elseif($stderr -cne ''){throw ('RUST-MISUSE: positive control emitted diagnostics '+$id)}
    $entry=@{id=$id;code=$case.code;sourceSHA256=$sourcePin.sha256;stdout=$stdout;stderr=$stderr;exitCode=$exitCode}
    if($Mode -ceq 'Replay'){
      $expected=@($frozen.cases|Where-Object{$_.id -ceq $id})[0]
      if($expected.code -cne $case.code -or $expected.sourceSHA256 -cne $sourcePin.sha256 -or $expected.exitCode -ne $exitCode){throw ('RUST-MISUSE: fixed mapping differs '+$id)}
      Assert-LNOuterCapture $capture $expected.stdout $expected.stderr $expected.exitCode $id
    }
    $diagnostics.Add($entry)
    $results.Add(@{id=$id;expectedVerdict=$(if($case.code){'reject'}else{'accept'});source=$sourcePin;capture=$capture})
  }
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  if($errors.Count){$report.success=$false}
  # Captures and source fixtures intentionally persist as evidence; no live
  # source was replaced and each compiler used the owned-process boundary.
  try{if($locked){$mutex.ReleaseMutex()};$mutex.Dispose();$report.cleanup=@{success=$true;mutexReleased=$locked;retainedEvidence=$run}}
  catch{$report.cleanup=@{success=$false;error=$_.Exception.Message};$report.success=$false}
  $report.pins=@($pins.ToArray());$report.results=@($results.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'DIAGNOSTICS.candidate.json'),(@{schema='lifecycle-native1-rust-diagnostics-v1';status='UNREVIEWED_DISCOVERY';mappingSHA256=$mappingHash;inputFingerprint=$inputFingerprint;cases=@($diagnostics.ToArray())}|ConvertTo-Json -Depth 12),$utf8)
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 25),$utf8)
}
Write-Output ('RUST-MISUSE evidence='+$run)
if(-not $report.success){Write-Output ('RUST-MISUSE FAIL '+$report.failure);exit 1}
Write-Output ('RUST-MISUSE '+$Mode+' PASS cases='+$results.Count)

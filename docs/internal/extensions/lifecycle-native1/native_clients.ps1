[CmdletBinding()]
param(
  [ValidateSet('Run','Validate')][string]$Phase='Run',
  [object]$Cases,
  [string]$BuildReceipt='',
  [int]$CaseDeadlineSeconds=300,
  [string]$DeadlineRationale='Initial client ceiling300s inherits the native stage budget and predecessor62-120s execution baseline; replace using measured lifecycle construction before final certification.',
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$LeanRoot=[IO.Path]::GetFullPath($LeanRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath=Join-Path $PSScriptRoot 'native_clients.json'
function Test-ClientExactString($Actual,[string]$Expected){
  return $Actual -is [string] -and [string]::Equals($Actual,$Expected,[StringComparison]::Ordinal)
}
function Test-ClientExactMember($Actual,[string[]]$Expected){
  if($Actual -isnot [string]){return $false}
  foreach($item in $Expected){if([string]::Equals($Actual,$item,[StringComparison]::Ordinal)){return $true}}
  return $false
}
$registry=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
# Independent full ordered mapping; producer JSON cannot choose its own roster,
# handler, model, executable, variant, verdict or exact output language.
$mapping=@(
  'LN1-CPP-WORD|cpp-production|production|lifecycle-cpp.exe|word|CPP',
  'LN1-CPP-COMPARISON|cpp-production|production|lifecycle-cpp.exe|comparison|CPP',
  'LN1-RUST-WORD|rust-production|production|packed-rmq-lifecycle.exe|word|RUST',
  'LN1-RUST-COMPARISON|rust-production|production|packed-rmq-lifecycle.exe|comparison|RUST',
  'LN1-RUST-OWNER-ERRORS|rust-control|testing|lifecycle-rust-tests.exe|owner-errors|RUST',
  'LN1-RUST-POST-TAKE-FAILURE|rust-control|testing|lifecycle-rust-tests.exe|post-take-failure|RUST',
  'LN1-RUST-CONFLICT-NEW-FIRST|rust-control|testing|lifecycle-rust-tests.exe|runtime-conflict-new-first|RUST',
  'LN1-RUST-CONFLICT-OLD-FIRST|rust-control|testing|lifecycle-rust-tests.exe|runtime-conflict-old-first|RUST',
  'LN1-RUST-CONFLICT-NATIVE-FIRST|rust-control|testing|lifecycle-rust-tests.exe|runtime-conflict-native-first|RUST',
  'LN1-RUST-INIT-FAILURE|rust-control|testing|lifecycle-rust-tests.exe|initialization-failure|RUST')
if(-not (Test-ClientExactString $registry.schema 'lifecycle-native1-client-registry-v1') -or
    @($registry.cases).Count -ne 10 -or @($registry.orderedIds).Count -ne 10){throw 'NATIVE-CLIENTS: registry schema/count differs'}
$known=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
for($i=0;$i -lt $mapping.Count;$i++){
  $m=$mapping[$i] -split '\|';$c=$registry.cases[$i]
  if(-not (Test-ClientExactString $c.id $m[0]) -or -not (Test-ClientExactString $registry.orderedIds[$i] $m[0]) -or -not $known.Add($c.id) -or
      -not (Test-ClientExactString $c.handler $m[1]) -or -not (Test-ClientExactString $c.variant $m[2]) -or -not (Test-ClientExactString $c.executable $m[3]) -or -not (Test-ClientExactString $c.mode $m[4]) -or
      -not (Test-ClientExactString $c.expectedVerdict 'accept') -or ($c.expectedExit -isnot [int] -and $c.expectedExit -isnot [long]) -or $c.expectedExit -ne 0 -or -not (Test-ClientExactString $c.expectedStderr '') -or
      -not (Test-ClientExactString $c.expectedStdout ('LIFE-NATIVE1 '+$m[5]+' '+$m[4]+" PASS`n"))){
    throw ('NATIVE-CLIENTS: frozen mapping differs at '+$m[0])
  }
}
if(-not $PSBoundParameters.ContainsKey('Cases')){$selected=@($registry.orderedIds)}else{
  if($null -eq $Cases -or @($Cases).Count -eq 0){throw 'NATIVE-CLIENTS: explicitly empty selector'}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in @($Cases)){
    if($id -isnot [string] -or [string]::IsNullOrWhiteSpace($id)){throw 'NATIVE-CLIENTS: empty or whitespace selector'}
    if(-not $known.Contains($id)){throw ('NATIVE-CLIENTS: unknown selector '+$id)}
    if(-not $seen.Add($id)){throw ('NATIVE-CLIENTS: duplicate selector '+$id)}
  }
  $selected=@($Cases)
}
if($Phase -cnotin @('Run','Validate') -or $CaseDeadlineSeconds -le 0 -or [string]::IsNullOrWhiteSpace($DeadlineRationale)){
  throw 'NATIVE-CLIENTS: exact phase, positive deadline and rationale required'
}
if($Phase -ceq 'Validate'){
  Write-Output ('NATIVE-CLIENTS VALIDATED cases='+$selected.Count+' ids='+($selected -join ','));exit 0
}
# All selector boundaries precede output-directory creation and runtime work.
if([string]::IsNullOrWhiteSpace($BuildReceipt)){throw 'NATIVE-CLIENTS: BuildReceipt required'}
$build=[IO.File]::ReadAllText($BuildReceipt,$utf8)|ConvertFrom-Json
if($build.schema -cne 'lifecycle-native1-build-v1' -or -not $build.success -or
    -not $build.integrity.success -or -not $build.cleanup.success -or $build.phase -cnotin @('all','clients')){
  throw 'NATIVE-CLIENTS: successful client build receipt required'
}
foreach($variable in @('PACKED_LIFECYCLE_FAIL_INIT','PACKED_LIFECYCLE_FAIL_AFTER_TAKE')){
  if([Environment]::GetEnvironmentVariable($variable,'Process')){throw ('NATIVE-CLIENTS: ambient test control '+$variable)}
}
$runRoot=Join-Path $root ('.lake/lifecycle-native1/clients/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($runRoot)
$mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
$locked=$false;$savedPath=$env:PATH;$savedErrorMode=$null
$pins=[Collections.Generic.List[object]]::new();$results=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-client-replay-v1';success=$false;campaignComplete=$false;
  selected=$selected;fullOrderedRoster=(($selected -join '|') -ceq ($registry.orderedIds -join '|'));
  startedUtc=[DateTime]::UtcNow.ToString('o');deadlineSeconds=$CaseDeadlineSeconds;deadlineRationale=$DeadlineRationale;
  registry=$null;buildReceipt=$null;contract=$null;historicalFixtures=@();staging=@();dependencies=@();provenance=@();results=@();
  failure=$null;integrity=$null;cleanup=$null}
function Pin-Client([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
function Get-LNPin([string]$Path){return Pin-Client $Path}
function Assert-ClientPin($Pin){
  $actual=Pin-Client $Pin.path
  if($actual.sha256 -cne $Pin.sha256 -or $actual.bytes -ne $Pin.bytes){throw ('NATIVE-CLIENTS: stale build pin '+$Pin.path)}
}
function Copy-ClientFile([string]$Source,[string]$Destination){
  $before=Pin-Client $Source
  if([IO.File]::Exists($Destination)){throw 'NATIVE-CLIENTS: staging destination already exists'}
  [IO.File]::Copy($Source,$Destination,$false)
  $after=Pin-Client $Destination
  if($before.sha256 -cne $after.sha256 -or $before.bytes -ne $after.bytes){throw 'NATIVE-CLIENTS: copy identity differs'}
  return @{source=$before;staged=$after}
}
function Assert-NewArtifact([string]$Path,[object[]]$Artifacts){
  if(-not @($Artifacts|Where-Object{[string]::Equals($_.path,$Path,[StringComparison]::OrdinalIgnoreCase)}).Count){
    throw ('NATIVE-CLIENTS: artifact absent from successful build receipt '+$Path)
  }
}
function Stage-Historical([string]$Directory){
  $oldRoot=[IO.Path]::GetFullPath('C:/Users/poin/.codex/worktrees/1817/RMQ')
  $fixtures=@(
    @{directory='build';dll='packed_route.dll';schema='native1-build-v2';toolSchema='native1-toolchain-v1';sources=19;lean=9;
      dllHash='CB53991D47129B608F364A7B0525E983321215E3DACE71661C7ECE950C8E991B';
      manifestHash='B07F660A24BA5966D7CD5BDA3D2C7C7D90ECF6FDD4192DE0B709C486D5F006F9';
      excluded=@('native/packed-rmq/src/lib.rs','native/packed-rmq/Cargo.toml','scripts/packed_native_build.ps1','scripts/packed_native_identity.ps1')},
    @{directory='binary-build';dll='packed_rmq.dll';schema='native1-binary-build-v1';toolSchema='native1-toolchain-v3';sources=31;lean=19;
      dllHash='7605525E9E89540D43DFD307E84DE24F03062A9632A59062682600D20E0168C4';
      manifestHash='A4C20BCAA5E35402293DB522CE8736A81BD84FBC67FC2648693475504E5E1069';
      excluded=@('native/packed-rmq/src/lib.rs','native/packed-rmq/Cargo.toml')})
  foreach($fixture in $fixtures){
    $base=Join-Path $oldRoot ('.lake/native1/'+$fixture.directory)
    $manifest=Pin-Client (Join-Path $base 'build-manifest.json')
    if($manifest.sha256 -cne $fixture.manifestHash){throw 'NATIVE-CLIENTS: historical manifest identity differs'}
    $prior=[IO.File]::ReadAllText($manifest.path,$utf8)|ConvertFrom-Json
    if($prior.schema -cne $fixture.schema -or $prior.toolchainIdentity.schema -cne $fixture.toolSchema -or
        @($prior.sources).Count -ne $fixture.sources -or @($prior.sources|Where-Object{$_.path.EndsWith('.lean',[StringComparison]::Ordinal)}).Count -ne $fixture.lean){
      throw 'NATIVE-CLIENTS: historical source/schema roster differs'
    }
    $artifact=@($prior.artifacts|Where-Object{$_.path -ceq $fixture.dll})
    if($artifact.Count -ne 1 -or $artifact[0].sha256 -cne $fixture.dllHash){throw 'NATIVE-CLIENTS: historical DLL manifest mapping differs'}
    $dll=Pin-Client (Join-Path $base $fixture.dll)
    if($dll.sha256 -cne $fixture.dllHash){throw 'NATIVE-CLIENTS: historical DLL bytes differ'}
    $applicability=@(foreach($source in $prior.sources){
      $actual=Pin-Client (Join-Path $root $source.path)
      $excluded=$source.path -cin $fixture.excluded
      $matches=$actual.sha256 -ceq $source.sha256
      if(-not $excluded -and -not $matches){throw ('NATIVE-CLIENTS: historical applicable source changed '+$source.path)}
      @{relativePath=$source.path;current=$actual;historicalSHA256=$source.sha256;matches=$matches;excludedFromApplicability=$excluded}
    })
    $runtimePins=@(foreach($relative in @('bin/lean.exe','bin/leanc.exe','include/lean/lean.h','lib/lean/libleanrt.a',
        'bin/libInit_shared.dll','bin/libleanshared.dll','bin/libleanshared_1.dll')){
      $old=@($prior.toolchainIdentity.leanFiles|Where-Object{$_.path -ceq $relative})
      if($old.Count -ne 1){throw 'NATIVE-CLIENTS: historical selected runtime pin missing'}
      $now=Pin-Client (Join-Path $LeanRoot $relative)
      if($now.sha256 -cne $old[0].sha256 -or $now.bytes -ne $old[0].bytes){throw ('NATIVE-CLIENTS: historical runtime differs '+$relative)}
      $now
    })
    $generated=@()
    if($fixture.directory -ceq 'binary-build'){
      if(@($prior.generatedC).Count -ne 19){throw 'NATIVE-CLIENTS: binary historical generated ledger differs'}
      $generated=@(foreach($entry in $prior.generatedC){
        $now=Pin-Client (Join-Path $oldRoot $entry.path)
        if($now.sha256 -cne $entry.sha256){throw 'NATIVE-CLIENTS: historical generated C differs'};$now
      })
    }
    $copy=Copy-ClientFile $dll.path (Join-Path $Directory $fixture.dll)
    $report.historicalFixtures+=@{dll=$fixture.dll;manifest=$manifest;copy=$copy;sourceApplicability=$applicability;
      selectedRuntimePins=$runtimePins;generatedC=$generated;freshBuildClaim=$false;
      boundary='Exact historical runtime-conflict fixture only. Excluded current Rust/build-script sources are not reused. Route has no generated-C ledger; binary has19 checked old generated files. Whole-manifest fresh-build equivalence and the remaining historical compiler inventory are not asserted.'}
  }
}
try{
  $locked=$mutex.WaitOne(0);if(-not $locked){throw 'NATIVE-CLIENTS: shared heavy slot busy; no native child launched'}
  # Native loader/crash failures must return their actual exit, not wait in a
  # modal Windows dialog inherited by the owned child process tree.
  if(-not ('LN1ClientErrorMode' -as [type])){
    Add-Type -TypeDefinition @'
using System.Runtime.InteropServices;
public static class LN1ClientErrorMode {
  [DllImport("kernel32.dll")] public static extern uint SetErrorMode(uint mode);
}
'@
  }
  $savedErrorMode=[LN1ClientErrorMode]::SetErrorMode(0x8003)
  $report.childErrorMode=0x8003
  $report.contract=Assert-LN1FrozenContract $root
  $report.registry=Pin-Client $registryPath;$report.buildReceipt=Pin-Client $BuildReceipt
  foreach($path in @($PSCommandPath,(Join-Path $PSScriptRoot 'PREDECESSOR_DLL_REUSE.md'),
      (Join-Path $root 'scripts/lifecycle_native_identity.ps1'),(Join-Path $root 'scripts/owned_process_tree.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){[void](Pin-Client $path)}
  foreach($pin in @($build.sourcePins)+@($build.generatedPins)+@($build.toolPins)+@($build.artifactPins)){Assert-ClientPin $pin}
  $artifactPins=@($build.artifactPins)
  if($build.nativeReceipt){
    Assert-ClientPin $build.nativeReceipt
    $native=[IO.File]::ReadAllText($build.nativeReceipt.path,$utf8)|ConvertFrom-Json
    foreach($pin in @($native.sourcePins)+@($native.generatedPins)+@($native.artifactPins)){Assert-ClientPin $pin}
    $artifactPins+=@($native.artifactPins)
  }
  $selectedCases=@(foreach($id in $selected){@($registry.cases|Where-Object{$_.id -ceq $id})[0]})
  # Every client runs from an owned staging directory. Keep the exact pinned
  # Lean DLL adjacent, because Windows PATH lookup was observably unstable in
  # nested capture shells. Canonical build outputs remain untouched.
  $runtime=Join-Path $LeanRoot 'bin/libInit_shared.dll'
  $runtimePin=Get-LN1Pin $runtime
  if(-not @($pins|Where-Object{[string]::Equals($_.path,$runtime,[StringComparison]::OrdinalIgnoreCase) -and
      $_.sha256 -ceq $runtimePin.sha256 -and $_.bytes -eq $runtimePin.bytes}).Count){
    throw 'NATIVE-CLIENTS: adjacent runtime absent from verified build inputs'
  }
  foreach($variant in @($selectedCases.variant|Select-Object -Unique)){
    $directory=Join-Path $runRoot ($variant+'-fixtures')
    [void][IO.Directory]::CreateDirectory($directory)
    $names=@('packed_rmq_lifecycle.dll')+@($selectedCases|Where-Object{$_.variant -ceq $variant}|ForEach-Object executable|Select-Object -Unique)
    foreach($name in $names){
      $source=Join-Path $root ('.lake/lifecycle-native1/build/'+$variant+'/'+$name)
      Assert-NewArtifact $source $artifactPins
      $report.staging+=Copy-ClientFile $source (Join-Path $directory $name)
    }
    $report.staging+=Copy-ClientFile $runtime (Join-Path $directory 'libInit_shared.dll')
    if($variant -ceq 'testing'){Stage-Historical $directory}
  }
  $planned=@(foreach($id in $selected){
    $case=@($registry.cases|Where-Object{$_.id -ceq $id})[0]
    $directory=Join-Path $runRoot ($case.variant+'-fixtures')
    $client=Join-Path $directory $case.executable
    $closure=Get-LNDependencyClosure @($client) (Join-Path $LeanRoot 'bin')
    Assert-LNDependencyCoverage $closure @($pins.ToArray())
    foreach($node in $closure.nodes){
      if(-not [string]::Equals((Split-Path $node.path -Parent),$directory,[StringComparison]::OrdinalIgnoreCase)){
        throw ('NATIVE-CLIENTS: non-system dependency escaped adjacent staging '+$node.path)
      }
    }
    $direct=@($closure.nodes|Where-Object{[string]::Equals($_.path,$client,[StringComparison]::OrdinalIgnoreCase)})[0]
    $custom=@($direct.imports|Where-Object{$_ -match '^packed_.*\.dll$'}|ForEach-Object{$_.ToLowerInvariant()}|Sort-Object)
    $expected=if($case.variant -ceq 'testing'){@('packed_rmq.dll','packed_rmq_lifecycle.dll','packed_route.dll')|Sort-Object}else{@('packed_rmq_lifecycle.dll')}
    if(($custom -join '|') -cne ($expected -join '|')){throw ('NATIVE-CLIENTS: direct DLL import roster differs '+$id)}
    $report.dependencies+=@{id=$id;closure=$closure}
    @{id=$id;case=$case;client=$client;directory=$directory}
  })
  $report.provenance=@($pins.ToArray())
  [IO.File]::WriteAllText((Join-Path $runRoot 'PLAN.json'),($report|ConvertTo-Json -Depth 20),$utf8)
  foreach($entry in $planned){
    $env:PATH=$entry.directory+';'+(Join-Path $LeanRoot 'bin')+';'+$savedPath
    $result=[ordered]@{id=$entry.id;handler=$entry.case.handler;mode=$entry.case.mode;success=$false;capture=$null;failure=$null}
    try{
      $result.capture=Invoke-LN1Stage -File $entry.client -Arguments @($entry.case.mode) -Stage $entry.id `
        -DeadlineSeconds $CaseDeadlineSeconds -OutputRoot (Join-Path $runRoot $entry.id) -WorkingDirectory $root
      Assert-LNOuterCapture $result.capture $entry.case.expectedStdout $entry.case.expectedStderr $entry.case.expectedExit $entry.id
      $result.success=$true
    }catch{$result.failure=$_.Exception.Message;throw}finally{$results.Add($result)}
  }
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.sha256 -cne $pin.sha256 -or $now.bytes -ne $pin.bytes){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.provenance=@($pins.ToArray())
  $report.integrity=@{success=($errors.Count -eq 0);checkedPins=$pins.Count;errors=@($errors.ToArray());liveRestorationWrites=0}
  if($errors.Count){$report.success=$false}
  $env:PATH=$savedPath
  try{if($null -ne $savedErrorMode){[void][LN1ClientErrorMode]::SetErrorMode($savedErrorMode)}
    if($locked){$mutex.ReleaseMutex()};$mutex.Dispose();$report.cleanup=@{success=$true;mutexReleased=$locked;pathRestored=($env:PATH -ceq $savedPath);errorModeRestored=($null -ne $savedErrorMode)}}
  catch{$report.cleanup=@{success=$false;error=$_.Exception.Message};$report.success=$false}
  $report.results=@($results.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $runRoot 'RESULT.json'),($report|ConvertTo-Json -Depth 25),$utf8)
}
Write-Output ('NATIVE-CLIENTS evidence='+$runRoot)
if(-not $report.success){Write-Output ('NATIVE-CLIENTS FAIL '+$report.failure);exit 1}
Write-Output ('NATIVE-CLIENTS PASS cases='+$selected.Count+' fullOrderedRoster='+$report.fullOrderedRoster)

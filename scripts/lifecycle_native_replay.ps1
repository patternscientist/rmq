param(
  [ValidateSet('Startup','Fixtures','Validate','ControlDiscovery','AbiBoundaries')][string]$Phase='Fixtures',
  [object]$Cases,
  [string]$ControlName='',
  [ValidateSet('build','query')][string]$ControlPhase='build',
  [string]$ControlArgument='0',
  [string]$BuildReceipt='',
  [ValidateSet('production','testing')][string]$Variant='production',
  [int]$CaseDeadlineSeconds=300,
  [string]$DeadlineRationale='Initial discovery ceiling: predecessor execution 62–120 seconds plus cold margin; replace with actual LIFE-NATIVE-1 component measurements before final replay.',
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
)
# Focused development runner. The final campaign also requires export mutation,
# native control, Rust misuse, and three-client registries; a Fixtures pass is
# explicitly not a complete LIFE-NATIVE-1 campaign verdict.
$ErrorActionPreference='Stop'
if($Phase -cnotin @('Startup','Fixtures','Validate','ControlDiscovery','AbiBoundaries') -or
    $Variant -cnotin @('production','testing') -or $ControlPhase -cnotin @('build','query')){
  throw 'LIFECYCLE-REPLAY: exact phase and variant spelling required'
}
. (Join-Path $PSScriptRoot 'lifecycle_native_identity.ps1')
$root=$script:LN1Root
# Windows loader search does not accept the forward-slash PATH entry accepted
# by .NET file APIs. Resolve it before constructing the child runtime PATH.
$LeanRoot=[IO.Path]::GetFullPath($LeanRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath=Join-Path $PSScriptRoot 'lifecycle_native_cases.json'
$registryBytes=[IO.File]::ReadAllBytes($registryPath)
if((Get-LN1BytesHash $registryBytes) -cne '9dc72366b51592f18dc50e52d2b799c736dc047e6166538a0a880192062985fd'){
  throw 'LIFECYCLE-REPLAY: frozen semantic fixture registry bytes differ'
}
$registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
$selected=@(Assert-LN1FixtureRegistry $registry $PSBoundParameters.ContainsKey('Cases') $Cases)
if($Phase -in @('Startup','ControlDiscovery','AbiBoundaries')){
  if($PSBoundParameters.ContainsKey('Cases')){throw 'LIFECYCLE-REPLAY: this phase does not accept fixture selectors'}
  $selected=@()
}
$controlNames=@('none','skip-repack','extra-owner-alias','retain-input','retain-old-arena',
  'retain-keys','retain-history','wrong-copy-value','wrong-copy-offset','partial-copy',
  'fail-after-take','model-fault','exhausted','fail-before-take-alloc','fail-before-publish',
  'shared-scalar-accept','endpoint-short','endpoint-long','negative-zero','bad-sign','word-inputfits')
$controlNameSet=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
foreach($name in $controlNames){[void]$controlNameSet.Add($name)}
if($Phase -ceq 'ControlDiscovery'){
  if($Variant -cne 'testing' -or -not $controlNameSet.Contains($ControlName) -or
      $ControlArgument -cnotmatch '^(?:0|[1-9][0-9]*)$' -or
      [Numerics.BigInteger]::Parse($ControlArgument) -gt [uint64]::MaxValue){
    throw 'LIFECYCLE-REPLAY: testing variant, known control, and exact uint64 argument required'
  }
  if($ControlPhase -ceq 'query' -and $ControlName -cin @('model-fault','exhausted','negative-zero','bad-sign','word-inputfits')){
    throw 'LIFECYCLE-REPLAY: control requires build phase'
  }
}elseif($PSBoundParameters.ContainsKey('ControlName') -or $PSBoundParameters.ContainsKey('ControlPhase') -or $PSBoundParameters.ContainsKey('ControlArgument')){
  throw 'LIFECYCLE-REPLAY: control arguments require ControlDiscovery phase'
}
if($CaseDeadlineSeconds -le 0 -or [string]::IsNullOrWhiteSpace($DeadlineRationale)){throw 'LIFECYCLE-REPLAY: positive deadline and rationale required'}
if($Phase -ceq 'Validate'){
  Write-Output ('LIFECYCLE-REPLAY VALIDATED cases='+$selected.Count+' ids='+($selected -join ','))
  exit 0
}
# Selector validation precedes runtime acquisition and any output directory.
if(-not $BuildReceipt){throw 'LIFECYCLE-REPLAY: BuildReceipt required'}
$build=[IO.File]::ReadAllText($BuildReceipt,$utf8)|ConvertFrom-Json
if($build.schema -cne 'lifecycle-native1-build-v1' -or -not $build.success -or
  -not $build.integrity.success -or -not $build.cleanup.success -or $build.phase -notin @('all','clients')){
  throw 'LIFECYCLE-REPLAY: successful native client build receipt required'
}
$runRoot=Join-Path $root ('.lake/lifecycle-native1/replay/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($runRoot)
$mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
$locked=$false;$savedPath=$env:PATH;$savedErrorMode=$null
$pins=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-focused-replay-v1';phase=$Phase;variant=$Variant;
  success=$false;campaignComplete=$false;startedUtc=[DateTime]::UtcNow.ToString('o');
  selected=$selected;caseDeadlineSeconds=$CaseDeadlineSeconds;deadlineRationale=$DeadlineRationale;
  control=$(if($Phase -ceq 'ControlDiscovery'){@{name=$ControlName;phase=$ControlPhase;argument=$ControlArgument}}else{$null});
  fixtureRegistry=$null;buildReceipt=$null;dependencies=$null;results=@();failure=$null;integrity=$null;cleanup=$null}
function Pin-LN1Replay([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
function Get-LNPin([string]$Path){return Pin-LN1Replay $Path}
function Assert-LN1ReplayPin($Pin){
  $now=Pin-LN1Replay $Pin.path
  if($now.bytes -ne $Pin.bytes -or $now.sha256 -cne $Pin.sha256){throw ('LIFECYCLE-REPLAY: stale build dependency '+$Pin.path)}
}
function Write-LN1Magnitude([IO.BinaryWriter]$Writer,[string]$Decimal,[int]$Padding=0){
  if($Decimal -cnotmatch '^(?:0|[1-9][0-9]*)$' -or $Padding -lt 0){throw 'LIFECYCLE-FIXTURE: noncanonical decimal magnitude'}
  $number=[Numerics.BigInteger]::Parse($Decimal,[Globalization.CultureInfo]::InvariantCulture)
  [byte[]]$bytes=$number.ToByteArray($true,$false)
  if($bytes.Length -eq 0){$bytes=[byte[]]@(0)}
  if($bytes.Length+$Padding -gt [uint32]::MaxValue){throw 'LIFECYCLE-FIXTURE: excessive magnitude'}
  $Writer.Write([uint32]($bytes.Length+$Padding));$Writer.Write($bytes)
  if($Padding){$Writer.Write([byte[]]::new($Padding))}
}
function Write-LN1Fixture($Case,[string]$Path){
  if($Case.id -cnotmatch '^LN1-[A-Z0-9-]+$' -or $Case.model -cnotin @('word','comparison')){throw 'LIFECYCLE-FIXTURE: malformed ID/model'}
  $stream=[IO.File]::Open($Path,[IO.FileMode]::CreateNew,[IO.FileAccess]::Write,[IO.FileShare]::None)
  $writer=[IO.BinaryWriter]::new($stream,$utf8,$false)
  try{
    $writer.Write([byte[]]@(76,78,49,70,49,0))
    $writer.Write([byte]([int]($Case.model -ceq 'comparison')))
    $writer.Write([uint32]@($Case.input).Count);$writer.Write([uint32]@($Case.queries).Count)
    $id=[Text.Encoding]::ASCII.GetBytes($Case.id);$writer.Write([uint32]$id.Length);$writer.Write($id)
    foreach($value in $Case.input){
      if($value -isnot [string] -or $value -cnotmatch '^(?:0|-?[1-9][0-9]*)$'){throw 'LIFECYCLE-FIXTURE: signed decimal format'}
      $negative=$value.StartsWith('-',[StringComparison]::Ordinal)
      $writer.Write([byte]([int]$negative))
      Write-LN1Magnitude $writer $value.TrimStart('-') $Case.magnitudeHighZeroPadding
    }
    foreach($query in $Case.queries){
      Write-LN1Magnitude $writer $query.left
      Write-LN1Magnitude $writer $query.right
      Write-LN1Magnitude $writer $query.expectedPacket
    }
  }finally{$writer.Dispose();$stream.Dispose()}
  return Pin-LN1Replay $Path
}
function Assert-LN1Report($Value,$Case,[bool]$Observed){
  if($Value.schema -cne 'lifecycle-native1-actual-v1' -or $Value.id -cne $Case.id -or
    $Value.model -ne [int]($Case.model -ceq 'comparison') -or
    $Value.widthBits -le 0 -or $Value.widthBytes -ne [Math]::Ceiling($Value.widthBits/8) -or
    $Value.observed -ne $Observed -or @($Value.requests).Count -ne @($Case.queries).Count){throw 'LIFECYCLE-REPLAY: report identity/request roster differs'}
  for($i=0;$i -lt @($Case.queries).Count;$i++){
    $r=$Value.requests[$i]
    if($r.index -ne $i){throw 'LIFECYCLE-REPLAY: request order differs'}
    if($Observed -and $null -eq $r.observations){throw 'LIFECYCLE-REPLAY: missing actual observations'}
    if(-not $Observed -and $null -ne $r.observations){throw 'LIFECYCLE-REPLAY: unexpected diagnostic owner'}
  }
}
try{
  $locked=$mutex.WaitOne(0);if(-not $locked){throw 'LIFECYCLE-REPLAY: shared heavy slot busy; no child launched'}
  # Inherit noninteractive Windows failure reporting into owned native children.
  # A crash must produce its actual exit instead of waiting in a modal WER box.
  if(-not ('LN1ReplayErrorMode' -as [type])){
    Add-Type -TypeDefinition @'
using System.Runtime.InteropServices;
public static class LN1ReplayErrorMode {
  [DllImport("kernel32.dll")] public static extern uint SetErrorMode(uint mode);
}
'@
  }
  $savedErrorMode=[LN1ReplayErrorMode]::SetErrorMode(0x8003)
  $report.childErrorMode=0x8003
  $report.contract=Assert-LN1FrozenContract $root
  $report.fixtureRegistry=Pin-LN1Replay $registryPath;$report.buildReceipt=Pin-LN1Replay $BuildReceipt
  foreach($path in @('scripts/lifecycle_native_replay.ps1','scripts/lifecycle_native_identity.ps1',
      'scripts/owned_process_tree.ps1','scripts/packed_native_lifecycle_stream_check.ps1',
      'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1')){
    [void](Pin-LN1Replay (Join-Path $root $path))
  }
  foreach($pin in @($build.sourcePins)+@($build.generatedPins)+@($build.toolPins)+@($build.artifactPins)){Assert-LN1ReplayPin $pin}
  if($build.nativeReceipt){
    Assert-LN1ReplayPin $build.nativeReceipt
    $dllManifest=[IO.File]::ReadAllText($build.nativeReceipt.path,$utf8)|ConvertFrom-Json
    foreach($pin in @($dllManifest.sourcePins)+@($dllManifest.generatedPins)+@($dllManifest.artifactPins)){Assert-LN1ReplayPin $pin}
  }
  $sourceDirectory=Join-Path $root ('.lake/lifecycle-native1/build/'+$Variant)
  $clientSource=Join-Path $sourceDirectory 'lifecycle-owner.exe'
  if(-not @($build.artifactPins|Where-Object{[string]::Equals($_.path,$clientSource,[StringComparison]::OrdinalIgnoreCase)}).Count){throw 'LIFECYCLE-REPLAY: client not in build receipt'}
  # Stage the already pinned runtime beside the already pinned client/DLL.
  # Nested shell launches did not reliably preserve PATH-based loader lookup;
  # adjacent files make the actual dependency closure explicit for every run.
  $directory=Join-Path $runRoot 'native'
  [void][IO.Directory]::CreateDirectory($directory)
  $report.stagedFiles=@()
  foreach($name in @('lifecycle-owner.exe','packed_rmq_lifecycle.dll','libInit_shared.dll')){
    $source=if($name -ceq 'libInit_shared.dll'){Join-Path $LeanRoot ('bin/'+$name)}else{Join-Path $sourceDirectory $name}
    $sourcePin=Pin-LN1Replay $source
    $known=@(@($build.artifactPins)+@($build.toolPins)|Where-Object{[string]::Equals($_.path,$sourcePin.path,[StringComparison]::OrdinalIgnoreCase)})
    if($known.Count -ne 1 -or $known[0].sha256 -cne $sourcePin.sha256 -or $known[0].bytes -ne $sourcePin.bytes){
      throw ('LIFECYCLE-REPLAY: staged source not exactly bound by build receipt '+$name)
    }
    $destination=Join-Path $directory $name
    [IO.File]::Copy($source,$destination,$false)
    $copyPin=Pin-LN1Replay $destination
    if($copyPin.sha256 -cne $sourcePin.sha256 -or $copyPin.bytes -ne $sourcePin.bytes){throw ('LIFECYCLE-REPLAY: staged copy differs '+$name)}
    $report.stagedFiles+=@{source=$sourcePin;copy=$copyPin}
  }
  $client=Join-Path $directory 'lifecycle-owner.exe'
  $report.dependencies=Get-LNDependencyClosure @($client) (Join-Path $LeanRoot 'bin')
  Assert-LNDependencyCoverage $report.dependencies @($pins.ToArray())
  $env:PATH=$directory+';'+(Join-Path $LeanRoot 'bin')+';'+$savedPath
  [IO.File]::WriteAllText((Join-Path $runRoot 'PLAN.json'),($report|ConvertTo-Json -Depth 15),$utf8)
  if($Phase -ceq 'Startup'){
    $actualPath=Join-Path $runRoot 'startup.json'
    $capture=Invoke-LN1Stage -File $client -Arguments @('--startup','--report',$actualPath) -Stage 'startup' -DeadlineSeconds 120 -OutputRoot (Join-Path $runRoot 'startup') -WorkingDirectory $root
    Assert-LNOuterCapture $capture "LIFE-NATIVE1 STARTUP PASS`n" '' 0 'startup'
    $actual=[IO.File]::ReadAllText($actualPath,$utf8)|ConvertFrom-Json
    if($actual.schema -cne 'lifecycle-native1-startup-v1'){throw 'LIFECYCLE-REPLAY: startup report schema'}
    $results.Add(@{id='STARTUP';capture=$capture;actual=(Pin-LN1Replay $actualPath)})
  }elseif($Phase -ceq 'AbiBoundaries'){
    $actualPath=Join-Path $runRoot 'abi-boundaries.json'
    $capture=Invoke-LN1Stage -File $client -Arguments @('--abi-boundaries','--report',$actualPath) -Stage 'abi-boundaries' -DeadlineSeconds 120 -OutputRoot (Join-Path $runRoot 'abi-boundaries') -WorkingDirectory $root
    Assert-LNOuterCapture $capture "LIFE-NATIVE1 ABI-BOUNDARIES PASS`n" '' 0 'abi-boundaries'
    $actual=[IO.File]::ReadAllText($actualPath,$utf8)|ConvertFrom-Json
    $abiMapping=@('ABI-INIT|0','PROFILE-4096|0','PROFILE-4097|3','PROFILE-SIZE-MAX|3',
      'PROFILE-NULL-BITS|1','PROFILE-NULL-BYTES|1','PROFILE-ONE|0',
      'BUILD-NULL-OWNER|1','BUILD-NULL-ANSWER|1','BUILD-NULL-DIAGNOSTICS|1',
      'BUILD-COUNT-4097|3','BUILD-MAGNITUDE-4097|3','BUILD-SIGN-2|1','BUILD-NEGATIVE-ZERO|1',
      'BUILD-EMPTY-MAGNITUDE|1','BUILD-LEFT-SHORT|1','BUILD-LEFT-LONG|1',
      'BUILD-RIGHT-SHORT|1','BUILD-RIGHT-LONG|1','BUILD-MODEL-2|1','BUILD-OBSERVE-2|1',
      'THREAD-SECONDARY-PROFILE|4','THREAD-INITIALIZING-PROFILE|0')
    if($actual.schema -cne 'lifecycle-native1-abi-boundaries-v1' -or $actual.caseCount -ne 23 -or @($actual.cases).Count -ne 23){
      throw 'LIFECYCLE-REPLAY: ABI boundary schema/count differs'
    }
    for($i=0;$i -lt $abiMapping.Count;$i++){
      $mapping=$abiMapping[$i] -split '\|';$row=$actual.cases[$i]
      if($row.id -cne $mapping[0] -or $row.expectedStatus -ne [int]$mapping[1] -or $row.actualStatus -ne [int]$mapping[1] -or
          ($row.id.StartsWith('BUILD-',[StringComparison]::Ordinal) -and $row.handleOutputsEmpty -ne $true)){
        throw ('LIFECYCLE-REPLAY: ABI boundary verdict differs '+$mapping[0])
      }
    }
    if($actual.secondaryProfileOutputsUnchanged -ne $true -or $actual.profile4096.widthBits -le 0 -or
        $actual.profile4096.widthBytes -ne [Math]::Ceiling($actual.profile4096.widthBits/8)){
      throw 'LIFECYCLE-REPLAY: ABI profile/thread relation differs'
    }
    $results.Add(@{id='ABI-BOUNDARIES';caseCount=23;capture=$capture;actual=(Pin-LN1Replay $actualPath)})
  }elseif($Phase -ceq 'ControlDiscovery'){
    $stage='control-'+$ControlName+'-'+$ControlPhase+'-'+$ControlArgument
    $actualPath=Join-Path $runRoot ($stage+'.json')
    $capture=Invoke-LN1Stage -File $client -Arguments @('--control',$ControlName,'--phase',$ControlPhase,'--argument',$ControlArgument,'--report',$actualPath) -Stage $stage -DeadlineSeconds $CaseDeadlineSeconds -OutputRoot (Join-Path $runRoot $stage) -WorkingDirectory $root
    Assert-LNOuterCapture $capture ("LIFE-NATIVE1 CONTROL $ControlName $ControlPhase OBSERVED`n") '' 0 $stage
    $actual=[IO.File]::ReadAllText($actualPath,$utf8)|ConvertFrom-Json
    if($actual.schema -cne 'lifecycle-native1-control-discovery-v1' -or
        $actual.control -cne $ControlName -or $actual.phase -cne $ControlPhase -or
        [Numerics.BigInteger]$actual.argument -ne [Numerics.BigInteger]::Parse($ControlArgument) -or
        $actual.acceptanceVerdict -cne 'not-assigned-discovery-only'){
      throw 'LIFECYCLE-REPLAY: control discovery identity differs'
    }
    if($ControlPhase -ceq 'build' -and $ControlName -cin @('exhausted','model-fault') -and
        ($actual.baselineBuilt -or $null -ne $actual.baselineInfo -or $null -ne $actual.baselineMemoryLE)){
      throw 'LIFECYCLE-REPLAY: bounded fuel probe unexpectedly built a healthy baseline'
    }
    $results.Add(@{id=$stage;acceptanceVerdict='not-assigned-discovery-only';capture=$capture;actual=(Pin-LN1Replay $actualPath)})
  }else{
    foreach($id in $selected){
      $case=@($registry.cases|Where-Object{$_.id -ceq $id})[0]
      $fixturePath=Join-Path $runRoot ($id+'.bin');$fixture=Write-LN1Fixture $case $fixturePath
      $pair=@()
      foreach($observed in @(0,1)){
        $stage=$id+'-observed'+$observed;$actualPath=Join-Path $runRoot ($stage+'.json')
        $capture=Invoke-LN1Stage -File $client -Arguments @('--fixture',$fixturePath,'--observed',[string]$observed,'--report',$actualPath) -Stage $stage -DeadlineSeconds $CaseDeadlineSeconds -OutputRoot (Join-Path $runRoot $stage) -WorkingDirectory $root
        Assert-LNOuterCapture $capture $case.expectedStdout $case.expectedStderr $case.expectedExit $stage
        $actual=[IO.File]::ReadAllText($actualPath,$utf8)|ConvertFrom-Json
        Assert-LN1Report $actual $case ([bool]$observed)
        $pair+=@($actual)
        $results.Add(@{id=$id;observed=[bool]$observed;fixture=$fixture;capture=$capture;actual=(Pin-LN1Replay $actualPath)})
      }
      # Exclude process-specific object identities; compare the actual answer
      # and every canonical memory cell, in order, for every request.
      if($pair[0].widthBits -ne $pair[1].widthBits -or $pair[0].widthBytes -ne $pair[1].widthBytes){
        throw ('LIFECYCLE-REPLAY: observed/unobserved profile differs '+$id)
      }
      for($q=0;$q -lt @($case.queries).Count;$q++){
        foreach($field in @('answerLE','memoryLE')){
          $a=$pair[0].requests[$q].$field|ConvertTo-Json -Depth 10 -Compress
          $b=$pair[1].requests[$q].$field|ConvertTo-Json -Depth 10 -Compress
          if($a -cne $b){throw ('LIFECYCLE-REPLAY: observed/unobserved '+$field+' differs '+$id+' request '+$q)}
        }
      }
    }
  }
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  if($errors.Count){$report.success=$false}
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  $mutexReleased=$false
  try{$env:PATH=$savedPath}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($null -ne $savedErrorMode){[void][LN1ReplayErrorMode]::SetErrorMode($savedErrorMode)}}
  catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($locked){$mutex.ReleaseMutex();$mutexReleased=$true}}
  catch{$cleanupErrors.Add($_.Exception.Message)}
  try{$mutex.Dispose()}catch{$cleanupErrors.Add($_.Exception.Message)}
  $report.cleanup=@{success=($cleanupErrors.Count -eq 0);mutexReleased=$mutexReleased;errors=@($cleanupErrors.ToArray())}
  if($cleanupErrors.Count){$report.success=$false}
  $report.results=@($results.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $runRoot 'RESULT.json'),($report|ConvertTo-Json -Depth 25),$utf8)
}
Write-Output ('LIFECYCLE-REPLAY evidence='+$runRoot)
if(-not $report.success){Write-Output ('LIFECYCLE-REPLAY FAIL '+$report.failure);exit 1}
Write-Output ('LIFECYCLE-REPLAY FOCUSED PASS phase='+$Phase+' cases='+$(if($Phase -ceq 'Startup'){0}else{$selected.Count}))

#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [ValidateSet('Plan','Discovery','Replay')][string]$Mode='Plan',
  [string]$BuildReceipt,
  [string]$FrozenInventory,
  [string]$FrozenSHA256,
  [ValidateRange(1,3600)][int]$DeadlineSeconds=600,
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$prefix='RMQ.SuccinctFinal.PackedNative.Lifecycle.'
$surfaces=@(
  'cached_run','export_contract','query_contract','Repacked.eq','repack_transport',
  'answer_packet_fits','nativeBuildFirst_packet','nativeQuery_packet',
  'Observations.runAcc_exact','Observations.read_occurrence_output',
  'ContractChecks.checkO02_firstCategories','ContractChecks.checkO06_queryCategories',
  'ContractChecks.checkO04_firstRoutes','ContractChecks.checkO08_queryRoutes',
  'ContractChecks.checkO10_queryReadPosition',
  'runThin_eq_runOwner','runBoundaryThin_eq_runBoundaryOwner',
  'requestProtocolThin_eq_requestProtocolOwner','Observations.runAccThin_eq_runAcc',
  'Observations.boundaryAccThin_eq_boundaryAcc','Observations.Stats.record_eq_recordBefore'
)
$names=@($surfaces|ForEach-Object{$prefix+$_})
$allowed=@('propext','Quot.sound','Classical.choice')
$consumerSource=(@('import RMQ.Validation.LifecycleNativeContract','set_option pp.fullNames true')+
  @($names|ForEach-Object{'#print axioms '+$_}) -join [char]10)+[char]10
$pins=[Collections.Generic.List[object]]::new()
$identities=[Collections.Generic.List[string]]::new()
$evidence=$null
$shadow=$null
$createdShadow=$false
$mutex=$null
$locked=$false
$failure=$null
$report=$null
$oldLeanPath=[Environment]::GetEnvironmentVariable('LEAN_PATH','Process')
$oldThreads=[Environment]::GetEnvironmentVariable('LEAN_NUM_THREADS','Process')

function Get-AIHash([byte[]]$Bytes) {
  $sha=[Security.Cryptography.SHA256]::Create()
  try{return ([BitConverter]::ToString($sha.ComputeHash($Bytes))).Replace('-','').ToLowerInvariant()}
  finally{$sha.Dispose()}
}
function Read-AIText([string]$Path){return $utf8.GetString([IO.File]::ReadAllBytes($Path))}
function Write-AIJson([string]$Path,$Value){
  [IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 35),$utf8)
}
function Add-AIPin([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
function Make-AIPinMap([object[]]$Values) {
  $map=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach($pin in $Values){
    $path=[IO.Path]::GetFullPath($pin.path)
    if($map.ContainsKey($path)){throw ('AXIOM duplicate receipt pin '+$path)}
    $map.Add($path,$pin)
  }
  return $map
}
function Assert-AIPin($Map,[string]$Path,[string]$Identity) {
  $full=[IO.Path]::GetFullPath($Path)
  if(-not $Map.ContainsKey($full)){throw ('AXIOM missing receipt pin '+$Identity)}
  $prior=$Map[$full]
  $now=Add-AIPin $full
  if($now.bytes -ne $prior.bytes -or $now.sha256 -cne $prior.sha256){
    throw ('AXIOM stale source/import/tool '+$Identity)
  }
  $identities.Add($Identity+'|'+$now.bytes+'|'+$now.sha256.ToLowerInvariant())
}
function Read-AIInventory([string]$Raw) {
  $rows=[Collections.Generic.List[object]]::new()
  $lines=$Raw.Split([char]10)
  for($i=0;$i -lt $lines.Count;$i++){
    if($i -eq $lines.Count-1 -and $lines[$i].Length -eq 0){continue}
    if($rows.Count -ge 21 -or $lines[$i].Length -eq 0){throw 'AXIOM extra/blank diagnostic'}
    $d=$lines[$i]|ConvertFrom-Json
    $index=$rows.Count
    if($d.severity -cne 'information' -and $d.severity -cne 'info'){
      throw 'AXIOM non-information diagnostic'
    }
    if($d.fileName -cne 'AxiomInventory.lean' -or $d.pos.line -ne ($index+3) -or
       $d.pos.column -ne 0 -or $d.data -isnot [string]){
      throw 'AXIOM diagnostic not at exact command'
    }
    $name=$names[$index]
    $empty="'"+$name+"' does not depend on any axioms"
    $pattern="^'"+[regex]::Escape($name)+"' depends on axioms: \[([\s\S]*)\]$"
    $axioms=@()
    if($d.data -ceq $empty){}
    elseif($d.data -cmatch $pattern){
      $axioms=@($Matches[1].Split(',')|ForEach-Object{$_.Trim()})
      if($axioms.Count -eq 0 -or ($axioms -ccontains '')){throw 'AXIOM malformed nonempty set'}
    }else{throw ('AXIOM unexpected declaration/message '+$name)}
    $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach($axiom in $axioms){
      if(-not $seen.Add($axiom)){throw 'AXIOM duplicate set entry'}
      if(-not ($allowed -ccontains $axiom)){throw ('AXIOM outside permitted Lean trust base: '+$axiom)}
    }
    $rows.Add([ordered]@{id=('AX'+($index+1).ToString('D2'));declaration=$name;
      axioms=$axioms;line=$d.pos.line;column=$d.pos.column;
      messageSHA256=(Get-AIHash ($utf8.GetBytes($d.data)))})
  }
  if($rows.Count -ne 21){throw 'AXIOM expected exactly twenty-one declaration inventories'}
  return @($rows.ToArray())
}
function Remove-AIShadow {
  if(-not $createdShadow){return}
  $full=[IO.Path]::GetFullPath($shadow)
  $allowedRoot=[IO.Path]::GetFullPath((Join-Path $root '.lake/lifecycle-native1')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($allowedRoot,[StringComparison]::OrdinalIgnoreCase) -or
    [IO.Path]::GetFileName($full) -cne 'axiom-inventory-shadow'){throw 'AXIOM cleanup escaped owned directory'}
  if([IO.Directory]::Exists($full)){Remove-Item -LiteralPath $full -Recurse -Force}
  if([IO.Directory]::Exists($full)){throw 'AXIOM shadow not removed'}
}

try {
  if($names.Count -ne 21 -or @($names|Select-Object -Unique).Count -ne 21){
    throw 'AXIOM exact source roster differs'
  }
  $sourceSHA=Get-AIHash ($utf8.GetBytes($consumerSource))
  if($sourceSHA -cne '82206b4cb35497ec19f92ae430fd23d812ed8ab43f5381a4b95a80b8149fa54a'){
    throw 'AXIOM exact twenty-one-command source bytes differ'
  }
  if($Mode -ceq 'Plan'){
    Write-Output ('AXIOM PLAN declarations=21 sourceSHA256='+$sourceSHA+' exactSets=NOT_OBSERVED noChildLaunched=true')
    exit 0
  }
  if([string]::IsNullOrWhiteSpace($BuildReceipt) -or -not [IO.File]::Exists($BuildReceipt)){
    throw 'AXIOM successful build receipt required'
  }
  if($Mode -ceq 'Replay' -and
    ([string]::IsNullOrWhiteSpace($FrozenInventory) -or $FrozenSHA256 -cnotmatch '^[a-f0-9]{64}$')){
    throw 'AXIOM reviewed inventory path and external raw SHA256 required'
  }
  . (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
  $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  $locked=$mutex.WaitOne(0)
  if(-not $locked){throw 'AXIOM heavy slot busy; no child launched'}
  $evidence=Join-Path $root ('.lake/lifecycle-native1/axioms/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
  [void][IO.Directory]::CreateDirectory($evidence)
  $report=[ordered]@{schema='lifecycle-native1-axiom-run-v1';success=$false;mode=$Mode;
    startedUtc=[DateTime]::UtcNow.ToString('o');consumerSourceSHA256=$sourceSHA;
    declarations=$names;declarationCount=21;permittedTrustBase=$allowed;
    exactSetsObserved=$false;capture=$null;inventory=@();provenance=@();failure=$null;
    integrity=$null;cleanup=$null;deadlineSeconds=$DeadlineSeconds;
    rationale='Compiled dependency closure and 21 declaration traversals only. The independent consumer compiled in 24.8 seconds; 600 seconds is a conservative bounded first-inventory margin. No Lake or full-build fallback.'}
  foreach($path in @($PSCommandPath,$BuildReceipt)){$null=Add-AIPin $path}
  $receipt=Read-AIText $BuildReceipt|ConvertFrom-Json
  if($receipt.schema -cne 'lifecycle-native1-build-v1' -or -not $receipt.success -or
    -not $receipt.integrity.success -or -not $receipt.cleanup.success){
    throw 'AXIOM unsuccessful/incomplete build receipt'
  }
  $sources=Make-AIPinMap @($receipt.sourcePins)
  $artifacts=Make-AIPinMap @($receipt.generatedPins)
  $toolMap=Make-AIPinMap @($receipt.toolPins)
  $modules=@(Get-LN1ImportClosure @('RMQ.Validation.LifecycleNativeContract'))
  foreach($module in $modules){
    $stem=$module.Replace('.','/')
    Assert-AIPin $sources (Join-Path $root ($stem+'.lean')) ('source/'+$stem+'.lean')
    Assert-AIPin $artifacts (Join-Path $root ('.lake/build/lib/lean/'+$stem+'.olean')) ('import/'+$stem+'.olean')
  }
  foreach($relative in @('lean-toolchain','lakefile.toml','lake-manifest.json',
    'scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
    'scripts/packed_native_lifecycle_stream_check.ps1','scripts/packed_native_lifecycle_storage_replay.ps1',
    'scripts/packed_native_lifecycle_integrity_check.ps1')){
    Assert-AIPin $sources (Join-Path $root $relative) ('config-helper/'+$relative)
  }
  $toolPrefix=[IO.Path]::GetFullPath($LeanRoot).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  foreach($tool in @($receipt.toolPins)){
    $full=[IO.Path]::GetFullPath($tool.path)
    if(-not $full.StartsWith($toolPrefix,[StringComparison]::OrdinalIgnoreCase)){
      throw 'AXIOM tool receipt outside selected Lean installation'
    }
    Assert-AIPin $toolMap $full ('tool/'+$full.Substring($toolPrefix.Length).Replace('\','/'))
  }
  foreach($required in @('bin/lean.exe','bin/libleanshared.dll','bin/libInit_shared.dll','lib/lean/Init.olean','lib/lean/Std.olean')){
    if(-not $toolMap.ContainsKey([IO.Path]::GetFullPath((Join-Path $LeanRoot $required)))){
      throw ('AXIOM missing required compiler/import pin '+$required)
    }
  }
  $ordered=@($identities.ToArray())
  [Array]::Sort($ordered,[StringComparer]::Ordinal)
  $consumedIdentity=Get-AIHash ($utf8.GetBytes(($ordered -join [char]10)+[char]10))
  $lean=Join-Path $LeanRoot 'bin/lean.exe'
  $leanSHA=Get-AIHash ([IO.File]::ReadAllBytes($lean))
  $frozen=$null
  if($Mode -ceq 'Replay'){
    $bytes=[IO.File]::ReadAllBytes($FrozenInventory)
    if((Get-AIHash $bytes) -cne $FrozenSHA256){throw 'AXIOM frozen inventory raw SHA256 differs'}
    $null=Add-AIPin $FrozenInventory
    $frozen=$utf8.GetString($bytes)|ConvertFrom-Json
    if($frozen.schema -cne 'lifecycle-native1-axioms-v1' -or
      $frozen.reviewStatus -cne 'FROZEN_ROOT_REVIEWED' -or
      $frozen.consumerSourceSHA256 -cne $sourceSHA -or
      $frozen.consumedIdentitySHA256 -cne $consumedIdentity -or
      $frozen.leanSHA256 -cne $leanSHA -or
      ($frozen.declarations -join '|') -cne ($names -join '|') -or
      @($frozen.inventory).Count -ne 21){throw 'AXIOM frozen source/closure/roster differs'}
  }
  $shadow=Join-Path $root '.lake/lifecycle-native1/axiom-inventory-shadow'
  if([IO.Directory]::Exists($shadow) -or [IO.File]::Exists($shadow)){throw 'AXIOM pre-existing shadow; inspect first'}
  [void][IO.Directory]::CreateDirectory($shadow)
  $createdShadow=$true
  [IO.File]::WriteAllText((Join-Path $shadow 'AxiomInventory.lean'),$consumerSource,$utf8)
  [IO.File]::WriteAllText((Join-Path $evidence 'AxiomInventory.lean'),$consumerSource,$utf8)
  [Environment]::SetEnvironmentVariable('LEAN_PATH',(Join-Path $root '.lake/build/lib/lean'),'Process')
  [Environment]::SetEnvironmentVariable('LEAN_NUM_THREADS','1','Process')
  $arguments=@('--json',('--root='+$shadow),'AxiomInventory.lean')
  $report.capture=Invoke-LNStreamCapture $root $lean $arguments $shadow (Join-Path $evidence 'capture') $DeadlineSeconds 'export-axiom-inventory'
  $stdout=Read-LNExactStream $report.capture.spec.stdout
  Assert-LNOuterCapture $report.capture $stdout '' 0 'export-axiom-inventory'
  $inventory=@(Read-AIInventory $stdout)
  $report.inventory=$inventory
  $report.exactSetsObserved=$true
  $outBytes=[IO.File]::ReadAllBytes($report.capture.spec.stdout)
  if($Mode -ceq 'Replay'){
    Assert-LNOuterCapture $report.capture $frozen.stdout $frozen.stderr 0 'export-axiom-inventory-frozen'
    if($outBytes.Length -ne $frozen.stdoutBytes -or (Get-AIHash $outBytes) -cne $frozen.stdoutSHA256){
      throw 'AXIOM frozen raw bytes differ'
    }
    for($i=0;$i -lt 21;$i++){
      if($inventory[$i].declaration -cne $frozen.inventory[$i].declaration -or
        ($inventory[$i].axioms -join '|') -cne ($frozen.inventory[$i].axioms -join '|')){
        throw 'AXIOM exact declaration set differs'
      }
    }
  }else{
    Write-AIJson (Join-Path $evidence 'AXIOMS.candidate.json') ([ordered]@{
      schema='lifecycle-native1-axioms-v1';reviewStatus='PENDING_ROOT_REVIEW';
      consumerSourceSHA256=$sourceSHA;consumedIdentitySHA256=$consumedIdentity;leanSHA256=$leanSHA;
      declarations=$names;permittedTrustBase=$allowed;inventory=$inventory;
      stdout=$stdout;stderr='';stdoutBytes=$outBytes.Length;stderrBytes=0;
      stdoutSHA256=(Get-AIHash $outBytes);stderrSHA256=(Get-AIHash ([byte[]]@()))})
  }
  $report.success=$true
}catch{$failure=$_.Exception.Message}
finally{
  $integrityErrors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){
    try{
      $now=Get-LN1Pin $pin.path
      if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed '+$pin.path)}
    }catch{$integrityErrors.Add($_.Exception.Message)}
  }
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  try{Remove-AIShadow}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{[Environment]::SetEnvironmentVariable('LEAN_PATH',$oldLeanPath,'Process')}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{[Environment]::SetEnvironmentVariable('LEAN_NUM_THREADS',$oldThreads,'Process')}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($locked){$mutex.ReleaseMutex()};if($null -ne $mutex){$mutex.Dispose()}}catch{$cleanupErrors.Add($_.Exception.Message)}
  if($null -ne $report){
    $report.failure=$failure
    $report.provenance=@($pins.ToArray())
    $report.integrity=@{attempted=$true;success=($pins.Count -gt 0 -and $integrityErrors.Count -eq 0);
      checkedPins=$pins.Count;errors=@($integrityErrors.ToArray());liveRestorationWrites=0}
    $report.cleanup=@{attempted=$true;success=($cleanupErrors.Count -eq 0);errors=@($cleanupErrors.ToArray());
      shadowRemoved=(-not $createdShadow -or -not [IO.Directory]::Exists($shadow));mutexReleased=$locked}
    $report.success=$report.success -and $null -eq $failure -and $report.integrity.success -and $report.cleanup.success
    $report.completedUtc=[DateTime]::UtcNow.ToString('o')
    Write-AIJson (Join-Path $evidence 'RESULT.json') $report
    if(-not $report.success -and $null -eq $failure){$failure='AXIOM final integrity/cleanup failed'}
  }
}
if($null -ne $failure){[Console]::Error.WriteLine('AXIOM ERROR: '+$failure);exit 1}
Write-Output ('AXIOM PASS mode='+$Mode+' declarations=21 evidence='+$evidence)
exit 0

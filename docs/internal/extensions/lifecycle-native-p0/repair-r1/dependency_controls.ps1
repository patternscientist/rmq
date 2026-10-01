param([string]$OutputRoot)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r1/dependencies-'+[Guid]::NewGuid().ToString('N'))}
[void][IO.Directory]::CreateDirectory($OutputRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
# LIFE-1-R3: once OutputRoot exists, every exit path writes RESULTS.json. Every
# installed-tool pin, the historical inputs and the owned fixture are re-checked
# independently in finally; the stage error, every integrity difference and
# every fixture-restoration error are recorded separately.
$captured=[Collections.Generic.List[object]]::new()
function Get-LNPin([string]$Path){$pin=Get-LNRawPin $Path;$captured.Add($pin);return $pin}
$bin='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$resultsInput=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/RESULTS.json'
$inputPins=[Collections.Generic.List[object]]::new()
$closure=$null;$pins=@();$oldPin=$null;$missing=$null;$state=$null
$results=[Collections.Generic.List[object]]::new()
$stageError=$null;$stageRecord=$null;$completed=$false
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$finalPins=[ordered]@{}
$fixtureCheck=$null
$durableFailed=$false
try {
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
$inputPins.Add((Get-LNRawPin $resultsInput))
$closure=Get-LNDependencyClosure @('lean.exe','leanc.exe','clang.exe','ld.lld.exe'|ForEach-Object {Join-Path $bin $_}) $bin
$pins=@($captured.ToArray())
Assert-LNDependencyCoverage $closure $pins
if($closure.nodes.Count -ne 11){throw 'measured closure differs; inspect before changing expectation'}
$results.Add(@{id='complete-inventory';outcome='accept';nodes=$closure.nodes.Count})
function Reject([string]$Id,[scriptblock]$Action,[string]$Prefix) {
  $errorText=$null
  try{& $Action}catch{$errorText=$_.Exception.Message}
  if($null -eq $errorText -or -not $errorText.StartsWith($Prefix)){throw "control $Id failed: $errorText"}
  $results.Add(@{id=$Id;outcome='reject';surface=$errorText})
}
$oldResults=Get-Content $resultsInput -Raw|ConvertFrom-Json
$oldPin=Get-LNRawPin $oldResults.rawSummary.path
if($oldPin.sha256 -cne $oldResults.rawSummary.sha256 -or $oldPin.bytes -ne $oldResults.rawSummary.bytes){throw 'historical raw summary identity changed'}
$inputPins.Add($oldPin)
$old=Get-Content $oldPin.path -Raw|ConvertFrom-Json
$oldPins=@($old.identity.files)+@($old.identity.linkerInputs)+@($old.identity.includedHeaders)
$missing=@($closure.nodes|Where-Object {$p=$_.path;-not @($oldPins|Where-Object {$_.path -ieq $p}).Count}|ForEach-Object {Split-Path $_.path -Leaf}|Sort-Object)
if(($missing -join ',') -cne 'libc++.dll,libclang-cpp.dll,libLLVM-19.dll,zlib1.dll'){throw 'historical measured omission differs'}
Reject 'bea5ce75-incomplete' {Assert-LNDependencyCoverage $closure $oldPins} 'DEPENDENCY: incomplete local inventory:'
foreach($node in $closure.nodes){
  $rest=@($pins|Where-Object {$_.path -ine $node.path})
  Reject ('omit-'+(Split-Path $node.path -Leaf)) {Assert-LNDependencyCoverage $closure $rest} 'DEPENDENCY: incomplete local inventory:'
}
$wrong=@($pins|ForEach-Object {@{path=$_.path;bytes=$_.bytes;sha256=$_.sha256}})
$wrong[0].path=Join-Path $OutputRoot (Split-Path $wrong[0].path -Leaf)
Reject 'same-name-wrong-path' {Assert-LNDependencyCoverage $closure $wrong} 'DEPENDENCY: incomplete local inventory:'
# Actual copied compiler dependency and map fixture, never installed mutation.
$fixture=Join-Path $OutputRoot 'fixture'
[void][IO.Directory]::CreateDirectory($fixture)
[IO.File]::WriteAllText((Join-Path $fixture '.gitignore'),".lake/`n",$utf8)
$dll=Join-Path $fixture 'zlib1.dll';$map=Join-Path $fixture 'link.map'
[IO.File]::WriteAllBytes($dll,[IO.File]::ReadAllBytes((Join-Path $bin 'zlib1.dll')))
[IO.File]::WriteAllText($map,'measured-link-map-fixture',$utf8)
& git -C $fixture init -q
& git -C $fixture config core.autocrlf false
& git -C $fixture -c core.excludesfile= add --all
& git -C $fixture -c user.name=RMQFixture -c user.email=fixture@invalid commit -qm baseline
if($LASTEXITCODE){throw 'fixture initialization failed'}
$state=@{root=$fixture;temp=(Join-Path $fixture '.lake/git');baseline=$null;pins=[Collections.Generic.List[object]]::new();captureErrors=@()}
$state.baseline=Get-LNTreeSnapshot $fixture $state.temp
$state.pins.Add((Get-LNRawPin $dll));$state.pins.Add((Get-LNRawPin $map))
$intact=Complete-LNIntegrity $state
if(-not $intact.success){throw 'unchanged fixture rejected'}
$results.Add(@{id='complete-unchanged-finalizer';outcome='accept';integrity=$intact})
foreach($path in @($dll,$map)) {
  $bytes=[IO.File]::ReadAllBytes($path)
  try {
    [IO.File]::WriteAllBytes($path,($bytes+[byte]1))
    $r=Complete-LNIntegrity $state
    $expected=@(('INTEGRITY: changed captured pin: '+$path),'INTEGRITY: live tracked/index/untracked baseline changed')
    if($r.success -or (@($r.errors|Sort-Object)|ConvertTo-Json -Compress) -cne (@($expected|Sort-Object)|ConvertTo-Json -Compress)){throw 'tamper accepted or wrong/additional surface'}
    $results.Add(@{id=('tamper-'+(Split-Path $path -Leaf));outcome='reject';integrity=$r})
  } finally {try{[IO.File]::WriteAllBytes($path,$bytes)}catch{$cleanupErrors.Add('fixture byte restoration '+$path+': '+$_.Exception.Message)}}
}
$originalHash=$state.pins[0].sha256
try {
  $state.pins[0].sha256='0'*64
  $r=Complete-LNIntegrity $state
  if($r.success -or $r.errors.Count -ne 1 -or $r.errors[0] -cne ('INTEGRITY: changed captured pin: '+$dll)){throw 'manifest tamper accepted or additional error'}
  $results.Add(@{id='tamper-manifest-hash';outcome='reject';integrity=$r})
} finally {try{$state.pins[0].sha256=$originalHash}catch{$cleanupErrors.Add('fixture manifest restoration: '+$_.Exception.Message)}}
$restored=Complete-LNIntegrity $state
if(-not $restored.success){throw 'fixture restoration failed'}
$results.Add(@{id='restored-finalizer';outcome='accept';integrity=$restored})
$completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  # Every captured installed-tool pin (including a partial inventory) and every
  # historical input pin, each in its own guard, continuing past failures.
  foreach($pin in @($captured.ToArray())+@($inputPins.ToArray())){
    $final=$null;$status='verified'
    try {
      $final=Get-LNRawPin $pin.path
      if($final.sha256 -cne $pin.sha256 -or $final.bytes -ne $pin.bytes){$status='changed';$integrityErrors.Add('INTEGRITY: changed captured pin: '+$pin.path)}
    } catch {$status='unreadable-final';$integrityErrors.Add($_.Exception.Message)}
    $finalPins[$pin.path]=if($null -ne $final){[ordered]@{path=$final.path;bytes=$final.bytes;sha256=$final.sha256;state=$status}}
      else{[ordered]@{path=$pin.path;bytes=$null;sha256=$null;state='unreadable-final'}}
    $pinChecks.Add([ordered]@{path=$pin.path;entrySha256=$pin.sha256;finalSha256=$(if($null -ne $final){$final.sha256}else{$null});status=$status})
  }
  if(@($inputPins|Where-Object {$_.path -ieq [IO.Path]::GetFullPath($resultsInput)}).Count -eq 0){
    $pinChecks.Add([ordered]@{path=[IO.Path]::GetFullPath($resultsInput);entrySha256=$null;finalSha256=$null;status='not-captured'})
  }
  if($null -ne $state -and $null -ne $state.baseline){
    try {
      $fixtureCheck=Complete-LNIntegrity $state
      foreach($message in @($fixtureCheck.errors)){$cleanupErrors.Add('fixture restoration: '+$message)}
    } catch {$cleanupErrors.Add('fixture restoration check: '+$_.Exception.Message)}
  }
  $passed=$completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    fixtureCheck=$fixtureCheck;entryPinCount=($captured.Count+$inputPins.Count);verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count}
  try {
    # V1 REQ-EH2: entry* keys retain the entry snapshots. The unprefixed keys
    # are reconstructed from the same final reads recorded by pinChecks; an
    # unreadable final state is explicit instead of silently presenting entry.
    $finalClosurePins=@(foreach($pin in @($pins)){$finalPins[$pin.path]})
    $finalOldSummary=if($null -ne $oldPin){$finalPins[$oldPin.path]}else{$null}
    $record=@{closure=$closure;entryPins=$pins;pins=$finalClosurePins;entryOldSummary=$oldPin;oldSummary=$finalOldSummary;oldMissing=$missing;controls=@($results.ToArray());
      installedToolsUnchanged=($integrityErrors.Count -eq 0 -and $captured.Count -gt 0);fixtureRestored=($null -ne $fixtureCheck -and $fixtureCheck.success);
      finalization=$finalization}
    [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($record|ConvertTo-Json -Depth 30),$utf8)
  } catch {$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('DEPENDENCY CONTROLS: durable result write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('DEPENDENCY CONTROLS PASS evidence='+$OutputRoot)

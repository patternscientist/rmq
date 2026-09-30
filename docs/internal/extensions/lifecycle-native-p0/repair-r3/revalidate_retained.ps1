param([Parameter(Mandatory)][string]$ContractPath,[string]$OutputRoot)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$nl="`r`n" # Original Windows producing runtime; never rebase historical text.
$base='9519b2c1af5e2cf59536b311db5e8dc81376a32f'
$oldRoot='C:\Users\poin\.codex\worktrees\eafd\RMQ'
$review='C:\Users\poin\Documents\RMQ\lifecycle-implementation-20260920\native-p0-r2-review'
$currentHelper=Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1'
$oldHelper=Join-Path $oldRoot 'scripts/packed_native_lifecycle_stream_check.ps1'
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r3/retained-'+[Guid]::NewGuid().ToString('N'))}
$OutputRoot=[IO.Path]::GetFullPath($OutputRoot)
$allowed=[IO.Path]::GetFullPath((Join-Path $repo '.lake/repair-r3')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $OutputRoot.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $OutputRoot)){
  throw 'R3-RETAINED: output must be a fresh directory inside this checkout .lake/repair-r3'
}
[void][IO.Directory]::CreateDirectory($OutputRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
$pins=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::OrdinalIgnoreCase)
$rows=[Collections.Generic.List[object]]::new()
$failure=$null;$finalErrors=[Collections.Generic.List[string]]::new();$before=$null

function Add-Pin([string]$Path,[object]$Expected=$null) {
  $pin=Get-LNRawPin $Path
  if($null -ne $Expected -and ($pin.bytes -ne $Expected.bytes -or
      -not [string]::Equals($pin.sha256,[string]$Expected.sha256,[StringComparison]::OrdinalIgnoreCase))){throw ('R3-RETAINED: pin differs '+$Path)}
  if($pins.ContainsKey($pin.path)){
    $prior=$pins[$pin.path]
    if($pin.bytes -ne $prior.bytes -or $pin.sha256 -cne $prior.sha256){throw ('R3-RETAINED: conflicting pin '+$Path)}
  }else{$pins.Add($pin.path,$pin)}
  return $pin
}
function Read-PinnedJson([string]$Path,[long]$Bytes,[string]$Hash) {
  $null=Add-Pin $Path @{bytes=$Bytes;sha256=$Hash}
  return $utf8.GetString([IO.File]::ReadAllBytes($Path))|ConvertFrom-Json
}
function Same([object]$Actual,[object]$Expected,[string]$Surface) {
  if(-not [string]::Equals([string]$Actual,[string]$Expected,[StringComparison]::Ordinal)){throw ('R3-RETAINED: '+$Surface+' differs')}
}
function Check-Roster($Actual,$Expected,[string]$Surface) {
  if(@($Actual).Count -ne @($Expected).Count){throw ('R3-RETAINED: '+$Surface+' count differs')}
  for($i=0;$i -lt @($Expected).Count;$i++){Same $Actual[$i] $Expected[$i] ($Surface+' order')}
}
function Pin-Capture($Capture) {
  foreach($pin in @($Capture.raw)){$null=Add-Pin $pin.path $pin}
  foreach($path in @($Capture.spec.stdout,$Capture.spec.stderr,$Capture.launcher.RawStandardOutput,$Capture.launcher.RawStandardError)){
    $null=Add-Pin $path
  }
  $hasExit=if($Capture.spec -is [Collections.IDictionary]){$Capture.spec.Contains('exit')}else{$null -ne $Capture.spec.PSObject.Properties['exit']}
  if($hasExit){
    $null=Add-Pin $Capture.spec.exit
    $actual=$utf8.GetString([IO.File]::ReadAllBytes($Capture.spec.exit))|ConvertFrom-Json
    Same $actual.exitCode $Capture.actual.exitCode 'ordinary exit artifact'
  }
}
function Observe([string]$Helper,$Capture,[string]$Out,[string]$Err,[int]$Exit,[string]$Profile,[switch]$Wrapper) {
  # Each function definition is scoped to this call. P and Q use the actual
  # historical/current caller with the identical object, expected strings and
  # ordinary-exit/transport guards. No copied comparison implements either one.
  . $Helper
  try {
    if($Wrapper){$null=Assert-LNWrapperCapture $Capture 'focused' $oldRoot}
    else{Assert-LNOuterCapture $Capture $Out $Err $Exit $Profile}
    return @{accepted=$true;failure=$null}
  }catch{return @{accepted=$false;failure=$_.Exception.Message}}
}
function Compare-Case($Definition,$Capture,[string]$Out,[string]$Err,[int]$Exit,[string]$Profile,[string]$Tier,[switch]$Wrapper) {
  Pin-Capture $Capture
  $p=Observe $oldHelper $Capture $Out $Err $Exit $Profile -Wrapper:$Wrapper
  $q=Observe $currentHelper $Capture $Out $Err $Exit $Profile -Wrapper:$Wrapper
  if($p.accepted -ne $Definition.oldAccept -or $q.accepted -ne $Definition.currentAccept){throw ('R3-RETAINED: unexpected P/Q verdict '+$Definition.id)}
  Same $q.failure $Definition.failure ($Definition.id+' current failure')
  if(-not $Definition.oldAccept){Same $p.failure $Definition.failure ($Definition.id+' historical failure')}
  $rows.Add([ordered]@{id=$Tier+'/'+$Definition.id;tier=$Tier;predicate=$(if($Wrapper){'Assert-LNWrapperCapture focused -> Assert-LNOuterCapture'}else{'Assert-LNOuterCapture'});
    profile=$Profile;expectedStdout=$Out;expectedStderr=$Err;expectedExit=$Exit;capture=$Capture;P=$p;Q=$q})
}

try {
  $before=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'before')
  foreach($path in @($PSCommandPath,$currentHelper,(Join-Path $repo 'scripts/owned_process_tree.ps1'),
      (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1'),$ContractPath)){$null=Add-Pin $path}
  $registryPath=Join-Path $PSScriptRoot 'retained_registry.json'
  $null=Add-Pin $registryPath @{bytes=3340;sha256='521BFA0CD6DEE84383AB41F8B7D6CC0F226EEFABFC96113EF5EBE835A48A20EB'}
  $registry=$utf8.GetString([IO.File]::ReadAllBytes($registryPath))|ConvertFrom-Json
  Same $registry.oldHead $base 'registry historical head'
  Same ([IO.Path]::GetFullPath($registry.historicalRoot)) $oldRoot 'registry historical root'
  $null=Add-Pin $oldHelper @{bytes=11037;sha256='5CACC1BFE9C9B9E7AB2044E2B28E8BE5F447B75AB863264A463FB2089B073347'}
  $oldBlob=(& git -C $repo rev-parse ($base+':scripts/packed_native_lifecycle_stream_check.ps1')).Trim()
  if($LASTEXITCODE){throw 'R3-RETAINED: old Git source unavailable'}
  $workingBlob=(& git -C $repo hash-object --path=scripts/packed_native_lifecycle_stream_check.ps1 $oldHelper).Trim()
  if($LASTEXITCODE){throw 'R3-RETAINED: old working source identity unavailable'}
  Same $workingBlob $oldBlob 'historical Git/check-out source identity'

  # The successor preservation verifier reconstructs these contracts with the
  # unchanged R2 semantic parsers and the exact producing root. Historical
  # checks use 2307..9519, and the claims matcher consumes its independently
  # source-derived expectation. Nothing below treats old checks as current.
  $contracts=$utf8.GetString([IO.File]::ReadAllBytes($ContractPath))|ConvertFrom-Json
  if(-not $contracts.success){throw 'R3-RETAINED: preservation verifier did not pass'}
  Same $contracts.mode 'full-contract' 'preservation verifier mode'
  Same $contracts.base $base 'preservation verifier base'
  Same ([IO.Path]::GetFullPath($contracts.worktree)) $repo 'preservation verifier worktree'
  Same $contracts.historicalR2.packageCommit $base 'historical package identity'
  Same $contracts.historicalR2.historicalBase '2307e3ad0739e0e1d9c3f186cdc568631086fddf' 'historical check base'
  foreach($pin in @($contracts.currentOwnedSources)){$null=Add-Pin $pin.path $pin}
  $retained=@($contracts.retainedContracts)
  $expectedIds=@($registry.profiles|ForEach-Object {'profile-'+$_})+@($registry.integrity|ForEach-Object {'integrity-'+$_})
  Check-Roster @($retained.id) $expectedIds 'retained contracts'
  foreach($contract in $retained){
    Same ([IO.Path]::GetFullPath($contract.producingRoot)) $oldRoot 'contract producing root'
    foreach($pin in @($contract.sourcePins)){$null=Add-Pin $pin.path $pin}
    foreach($pin in @($contract.rawPins)){$null=Add-Pin $pin.path $pin}
    Pin-Capture $contract.capture
    $q=Observe $currentHelper $contract.capture $contract.expectedStdout $contract.expectedStderr $contract.expectedExit $contract.id
    if(-not $q.accepted){throw ('R3-RETAINED: historical legitimate rejected '+$contract.id+'; '+$q.failure)}
    $rows.Add([ordered]@{id=$contract.id;tier='retained-historical-capture';predicate='Assert-LNOuterCapture';
      expectedStdout=$contract.expectedStdout;expectedStderr=$contract.expectedStderr;expectedExit=$contract.expectedExit;
      producingRoot=$contract.producingRoot;capture=$contract.capture;Q=$q})
  }

  $rootManifest=Read-PinnedJson (Join-Path $review 'ROOT_COUNTEREXAMPLE_PINS.json') 11921 '082365E5E6DAB0E92D23C4D2D35B89DB238090058585D6F6885D6204D9127622'
  if(@($rootManifest).Count -ne 41){throw 'R3-RETAINED: root manifest roster differs'}
  foreach($pin in $rootManifest){$null=Add-Pin $pin.path $pin}
  $root=Read-PinnedJson (Join-Path $review 'ordinal-capture-647ce95dae85469e85586548d4ed9496/RESULT.json') 14113 '7CB4B0F64197973D37CC640C43AEFBB59FC61515CC58E360A19E844FB1BEE4A9'
  Check-Roster @($root.cases.id) @($registry.root.id) 'root named cases'
  for($i=0;$i -lt $registry.root.Count;$i++){
    $definition=$registry.root[$i];$record=$root.cases[$i]
    $capture=$utf8.GetString([IO.File]::ReadAllBytes($record.capture))|ConvertFrom-Json
    $out='';$err=if($definition.id -ceq 'otherwise-empty-bom'){''}else{'PROCESS: expected failure'+$nl}
    $exit=if($definition.id -ceq 'otherwise-empty-bom'){0}else{7}
    $actualErr=switch -CaseSensitive ($definition.id){
      'expected-error' {$err}
      'error-plus-ascii' {$err+'UNEXPECTED OUTER DIAGNOSTIC'+$nl}
      'error-plus-bom' {$err+[char]0xFEFF}
      'otherwise-empty-bom' {[string][char]0xFEFF}
    }
    Same ($utf8.GetString([IO.File]::ReadAllBytes($capture.spec.stdout))) $out 'prescribed root emitted stdout'
    Same ($utf8.GetString([IO.File]::ReadAllBytes($capture.spec.stderr))) $actualErr 'prescribed root emitted stderr'
    Compare-Case $definition $capture $out $err $exit $definition.id 'historical-actual-root-child'
  }

  $leaf=Read-PinnedJson (Join-Path $review 'stream-process-f023afa2f19b43cda8980f8f59f724a3/RESULT.json') 26231 'A53216543CFE84C830861332912C4D57A525381E33019AE7AAE17F438ADA9361'
  Check-Roster @($leaf.records.id) @($registry.leaf.id) 'leaf emitted cases'
  for($i=0;$i -lt $registry.leaf.Count;$i++){
    $definition=$registry.leaf[$i];$record=$leaf.records[$i]
    $null=Add-Pin $record.child.path $record.child
    $out='component evidence'+$nl;$err='PROCESS: declared component failure'+$nl
    $actualOut=switch -CaseSensitive ($definition.id){'nul-stdout' {$out+[char]0};'bom-stdout' {([string][char]0xFEFF)+$out};default {$out}}
    $actualErr=if($definition.id -ceq 'extra-error-words'){$err+'UNEXPECTED OUTER DIAGNOSTIC'+$nl}else{$err}
    Same ($utf8.GetString([IO.File]::ReadAllBytes($record.capture.spec.stdout))) $actualOut 'prescribed leaf emitted stdout'
    Same ($utf8.GetString([IO.File]::ReadAllBytes($record.capture.spec.stderr))) $actualErr 'prescribed leaf emitted stderr'
    Compare-Case $definition $record.capture $out $err 1 'process-component' 'historical-actual-leaf-child'
  }

  $wrapper=Read-PinnedJson (Join-Path $review 'stream-wrapper-16987dad0e7f455cbd45e64b6fb6e11b/RESULT.json') 7598 'BA143B9F0A4D100115A90F82507DD3647E9F089821A2F10BB328D798679EFA21'
  Check-Roster @($wrapper.records.id) @($registry.copiedFocused.id) 'copied focused cases'
  $null=Add-Pin $wrapper.baseline.path $wrapper.baseline
  $baseline=$utf8.GetString([IO.File]::ReadAllBytes($wrapper.baseline.path))|ConvertFrom-Json
  foreach($pin in $baseline.raw){$null=Add-Pin $pin.path $pin}
  $nativeRoot=[IO.Path]::GetFullPath((Join-Path $oldRoot '.lake/lifecycle-native-p0/runs/5b2d10d020e64c24b8d81f8278eb39a7'))
  $null=Add-Pin (Join-Path $nativeRoot 'SUMMARY.json') @{bytes=117086;sha256='B71497497654E9544C07B73A693A411AAC20713495EBE5716CF93D8CEFEE9934'}
  $out='LIFECYCLE-REPLAY evidence='+$nativeRoot+$nl+'LIFECYCLE-REPLAY PASS cases=1 selfTest=False'+$nl
  for($i=0;$i -lt $registry.copiedFocused.Count;$i++){
    $definition=$registry.copiedFocused[$i];$record=$wrapper.records[$i]
    foreach($pin in $record.raw){$null=Add-Pin $pin.path $pin}
    $dir=Split-Path $record.raw[0].path -Parent
    $launcher=$baseline.outer|ConvertTo-Json -Depth 20|ConvertFrom-Json
    $launcher.RawStandardOutput=Join-Path $dir 'launcher.stdout.raw';$launcher.RawStandardError=Join-Path $dir 'launcher.stderr.raw'
    $capture=@{launcher=$launcher;actual=$baseline.actual;raw=$record.raw;
      spec=@{stdout=(Join-Path $dir 'stdout.raw');stderr=(Join-Path $dir 'stderr.raw');error=(Join-Path $dir 'child-error');overflow=(Join-Path $dir 'overflow')}}
    $actualOut=switch -CaseSensitive ($definition.id){'trailing-nul-stdout' {$out+[char]0};'leading-bom-stdout' {([string][char]0xFEFF)+$out};default {$out}}
    $actualErr=switch -CaseSensitive ($definition.id){'nul-only-stderr' {[string][char]0};'extra-error-words' {'UNEXPECTED OUTER DIAGNOSTIC'+$nl};default {''}}
    Same ($utf8.GetString([IO.File]::ReadAllBytes($capture.spec.stdout))) $actualOut 'prescribed copied stdout'
    Same ($utf8.GetString([IO.File]::ReadAllBytes($capture.spec.stderr))) $actualErr 'prescribed copied stderr'
    Compare-Case $definition $capture $out '' 0 'wrapper-focused' 'historical-copied-focused' -Wrapper
  }
  # These six launcher components are freshly written copies. They are not
  # actual launcher emissions; child transport/ordinary exits still come from
  # the immutable positive receipt, and the complete focused predicate is used.
  foreach($definition in $registry.syntheticLauncher){
    $dir=Join-Path $OutputRoot ('synthetic-launcher/'+$definition.id)
    [void][IO.Directory]::CreateDirectory($dir)
    $baselineDir=Split-Path $wrapper.baseline.path -Parent
    $launcher=$baseline.outer|ConvertTo-Json -Depth 20|ConvertFrom-Json
    $launcher.RawStandardOutput=Join-Path $dir 'launcher.stdout.raw';$launcher.RawStandardError=Join-Path $dir 'launcher.stderr.raw'
    $spec=@{stdout=(Join-Path $dir 'stdout.raw');stderr=(Join-Path $dir 'stderr.raw');error=(Join-Path $dir 'child-error');overflow=(Join-Path $dir 'overflow')}
    [IO.File]::WriteAllBytes($spec.stdout,[IO.File]::ReadAllBytes((Join-Path $baselineDir 'stdout.log')))
    [IO.File]::WriteAllBytes($spec.stderr,[IO.File]::ReadAllBytes((Join-Path $baselineDir 'stderr.log')))
    [IO.File]::WriteAllBytes($launcher.RawStandardOutput,[IO.File]::ReadAllBytes($baseline.outer.RawStandardOutput))
    [IO.File]::WriteAllBytes($launcher.RawStandardError,[IO.File]::ReadAllBytes($baseline.outer.RawStandardError))
    $target=if($definition.channel -ceq 'stdout'){$launcher.RawStandardOutput}else{$launcher.RawStandardError}
    [IO.File]::WriteAllBytes($target,$utf8.GetBytes([string][char]$definition.codepoint))
    $raw=@($spec.stdout,$spec.stderr,$launcher.RawStandardOutput,$launcher.RawStandardError)|ForEach-Object {Get-LNRawPin $_}
    $capture=@{launcher=$launcher;actual=$baseline.actual;raw=$raw;spec=$spec}
    Compare-Case $definition $capture $out '' 0 'wrapper-focused' 'synthetic-launcher-component' -Wrapper
  }
  if($rows.Count -ne 40){throw 'R3-RETAINED: complete 21/4/4/5/6 registry did not execute'}
}catch{$failure=$_.Exception.Message}
finally {
  foreach($pin in @($pins.Values)){
    try{$now=Get-LNRawPin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}
    catch{$finalErrors.Add($_.Exception.Message)}
  }
  try{
    if($null -eq $before){throw 'initial candidate snapshot unavailable'}
    $after=Get-LNTreeSnapshot $repo (Join-Path $OutputRoot 'after')
    Same ($after|ConvertTo-Json -Depth 8 -Compress) ($before|ConvertTo-Json -Depth 8 -Compress) 'live candidate finally'
  }catch{$finalErrors.Add($_.Exception.Message)}
  $result=[ordered]@{success=($null -eq $failure -and $finalErrors.Count -eq 0);failure=$failure;finalIntegrity=@{attempted=$true;success=($finalErrors.Count -eq 0);errors=@($finalErrors.ToArray());checkedPins=$pins.Count;restorationWrites=0};
    oldHead=$base;historicalRoot=$oldRoot;currentHead=$(if($null -ne $before){$before.head}else{$null});
    runtime=@{shell=(Get-Process -Id $PID).Path;PowerShell=$PSVersionTable.PSVersion.ToString();DotNet=[Environment]::Version.ToString()};
    sourceGitWorkingRelation='Old helper exact raw hash plus Git check-out filter identity; raw captures never normalized.';
    registry=@($rows.ToArray());pins=@($pins.Values|Sort-Object path);scope='Retained capture components only. No new native run; historical checks do not certify current HEAD. Actual-child and copied-focused evidence tiers remain separate.'}
  [IO.File]::WriteAllText((Join-Path $OutputRoot 'RESULTS.json'),($result|ConvertTo-Json -Depth 30),$utf8)
}
if(-not $result.success){throw ('R3-RETAINED: '+$failure+'; finally='+($finalErrors -join '; '))}
Write-Output ('R3 RETAINED PASS cases='+$rows.Count+' evidence='+$OutputRoot)

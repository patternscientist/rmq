#!/usr/bin/env pwsh
[CmdletBinding()]
param([ValidateRange(1,60)][int]$DeadlineSeconds=30)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$runner=Join-Path $PSScriptRoot 'rust_misuse_replay.ps1'
$expectedMappingSHA='8c5f71775d51a892b23267b79ddf60982b77bdb1174ca83ee7efe0e977ec7de6'
$ids=@('RS-RUNTIME-SEND','RS-RUNTIME-SYNC','RS-OWNER-SEND','RS-OWNER-SYNC',
  'RS-OBSERVATION-SEND','RS-OBSERVATION-SYNC','RS-NATURAL-SEND','RS-NATURAL-SYNC',
  'RS-RESULT-SEND','RS-RESULT-SYNC','RS-OWNER-CLONE','RS-IMMUTABLE-QUERY',
  'RS-BYTES-ESCAPE','RS-RAW-ALIAS','RS-RUNTIME-ESCAPE','RS-ACCEPT-MUTABLE','RS-ACCEPT-BORROW')
$expectedControls=@('selector-omitted','selector-focused','selector-null','selector-empty-array',
  'selector-empty-string','selector-whitespace','selector-unknown','selector-duplicate',
  'mapping-delete-middle','mapping-duplicate-middle','mapping-permute-middle',
  'selector-known-plus-nul','selector-known-plus-soft-hyphen',
  'selector-known-plus-zero-width-space','selector-known-plus-bom')
$pins=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$shadow=$null
$createdShadow=$false
$failure=$null
$run=Join-Path $root ('.lake/lifecycle-native1/rust-selector-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$report=[ordered]@{schema='lifecycle-native1-rust-selector-controls-v1';success=$false;
  startedUtc=[DateTime]::UtcNow.ToString('o');expectedMappingSHA256=$expectedMappingSHA;
  expectedControlIds=$expectedControls;expectedCount=15;results=@();stages=@();pins=@();failure=$null;
  integrity=$null;cleanup=$null;heavyMutexAcquired=$false;compilerInvocations=0;
  deadlineSeconds=$DeadlineSeconds;
  rationale='Actual PowerShell caller probes only; eight selector probes previously completed in the export runner controls. Thirty seconds per bounded caller gives margin; no compiler or semantic Rust run is requested.'}
function Add-RSCPin([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
function Write-RSCJson([string]$Path,$Value){[IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 35),$utf8)}
function Remove-RSCShadow {
  if(-not $createdShadow){return}
  $full=[IO.Path]::GetFullPath($shadow)
  $prefix=[IO.Path]::GetFullPath((Join-Path $root '.lake/lifecycle-native1')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
    [IO.Path]::GetFileName($full) -cne 'rust-selector-shadow'){throw 'RUST-CONTROLS cleanup escaped owned root'}
  if([IO.Directory]::Exists($full)){Remove-Item -LiteralPath $full -Recurse -Force}
  if([IO.Directory]::Exists($full)){throw 'RUST-CONTROLS shadow not removed'}
}
function Invoke-RSCCaller([object]$Case,[string]$Target) {
  $quotedTarget=$Target.Replace("'","''")
  $callerSource=@(
    '$ErrorActionPreference = ''Stop'''
    'try {'
    ("  & '"+$quotedTarget+"' -SelectorProbeOnly -RustRoot '"+$missingToolRoot.Replace("'","''")+"'"+$Case.argument)
    '  exit $LASTEXITCODE'
    '} catch {'
    '  [Console]::Error.WriteLine(''RUST-CONTROLS REJECT: ''+$_.Exception.Message)'
    '  exit 1'
    '}'
  ) -join [Environment]::NewLine
  $caller=Join-Path $run ($Case.id+'-caller.ps1')
  [IO.File]::WriteAllText($caller,$callerSource+[Environment]::NewLine,$utf8)
  $callerPin=Get-LN1Pin $caller
  $stage=[ordered]@{id=$Case.id;capture=$null;error=$null}
  try {
    $stage.capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$caller) $root (Join-Path $run $Case.id) $DeadlineSeconds $Case.id
    Assert-LNOuterCapture $stage.capture $Case.stdout $Case.stderr $Case.exit $Case.id
    return [ordered]@{id=$Case.id;passed=$true;expectedExit=$Case.exit;expectedStdout=$Case.stdout;
      expectedStderr=$Case.stderr;caller=$callerPin;target=(Get-LN1Pin $Target);capture=$stage.capture}
  }catch{$stage.error=$_.Exception.Message;throw}
  finally{$stages.Add($stage)}
}
try{
  $shell=(Get-Process -Id $PID).Path
  foreach($path in @($PSCommandPath,$runner,$shell,(Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
    (Join-Path $root 'scripts/owned_process_tree.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
    (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){
    $null=Add-RSCPin $path
  }
  $source=$utf8.GetString([IO.File]::ReadAllBytes($runner))
  if([regex]::Matches($source,[regex]::Escape("'"+$expectedMappingSHA+"'")).Count -ne 1){
    throw 'RUST-CONTROLS expected fixed17 mapping guard missing or duplicated'
  }
  $caseLines=[regex]::Matches($source,"(?m)^  @\{id='([^']+)';code='[^']*';source=.*\},?\r?$")
  if($caseLines.Count -ne 17 -or
    ((@($caseLines|ForEach-Object{$_.Groups[1].Value})) -join '|') -cne ($ids -join '|')){
    throw 'RUST-CONTROLS exact literal case roster differs'
  }
  $shadow=Join-Path $root '.lake/lifecycle-native1/rust-selector-shadow'
  if([IO.Directory]::Exists($shadow) -or [IO.File]::Exists($shadow)){throw 'RUST-CONTROLS shadow pre-exists; inspect first'}
  [void][IO.Directory]::CreateDirectory($shadow)
  $createdShadow=$true
  $missingToolRoot=Join-Path $shadow 'NONEXISTENT-TOOLCHAIN'
  if([IO.Directory]::Exists($missingToolRoot)){throw 'RUST-CONTROLS no-compiler sentinel exists'}
  $rootExpression='$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot ''../../../..''))'
  if([regex]::Matches($source,[regex]::Escape($rootExpression)).Count -ne 1){
    throw 'RUST-CONTROLS root expression changed; review literal substitution'
  }
  $rootReplacement='$root='''+$root.Replace("'","''")+''''
  $shadowSource=$source.Replace($rootExpression,$rootReplacement)
  $original=Join-Path $shadow 'original.ps1'
  [IO.File]::WriteAllText($original,$shadowSource,$utf8)
  $newline=[Environment]::NewLine
  $invalid='RUST-CONTROLS REJECT: RUST-MISUSE: invalid or duplicate selector'+$newline
  $empty='RUST-CONTROLS REJECT: RUST-MISUSE: empty bound selector'+$newline
  $fixtures=@(
    @{id='selector-omitted';argument='';exit=0;stdout=('RUST-MISUSE SELECTED '+($ids -join ',')+$newline);stderr=''},
    @{id='selector-focused';argument=" -OnlyCase 'RS-IMMUTABLE-QUERY'";exit=0;stdout=('RUST-MISUSE SELECTED RS-IMMUTABLE-QUERY'+$newline);stderr=''},
    @{id='selector-null';argument=' -OnlyCase $null';exit=1;stdout='';stderr=$empty},
    @{id='selector-empty-array';argument=' -OnlyCase @()';exit=1;stdout='';stderr=$empty},
    @{id='selector-empty-string';argument=" -OnlyCase ''";exit=1;stdout='';stderr=$invalid},
    @{id='selector-whitespace';argument=" -OnlyCase ' '";exit=1;stdout='';stderr=$invalid},
    @{id='selector-unknown';argument=" -OnlyCase 'RS-UNKNOWN'";exit=1;stdout='';stderr=$invalid},
    @{id='selector-duplicate';argument=" -OnlyCase @('RS-OWNER-SEND','RS-OWNER-SEND')";exit=1;stdout='';stderr=$invalid}
  )
  foreach($fixture in $fixtures){$results.Add((Invoke-RSCCaller $fixture $original))}
  # Literal edits affect middle entries only. The source runner and its guard
  # stay untouched; every disposable copy differs by root substitution plus
  # the recorded mapping mutation.
  $left=$caseLines[7].Value
  $right=$caseLines[8].Value
  $mutations=@(
    @{id='mapping-delete-middle';kind='delete';find=$right;replace=''},
    @{id='mapping-duplicate-middle';kind='duplicate';find=$right;replace=$left},
    @{id='mapping-permute-middle';kind='permute';find=$left;replace=$right}
  )
  foreach($mutation in $mutations){
    $changed=$shadowSource
    if($mutation.kind -ceq 'permute'){
      $a=$caseLines[7];$b=$caseLines[8]
      $between=$source.Substring($a.Index+$a.Length,$b.Index-($a.Index+$a.Length))
      $find=$left+$between+$right
      $replace=$right+$between+$left
    }else{$find=$mutation.find;$replace=$mutation.replace}
    if([regex]::Matches($changed,[regex]::Escape($find)).Count -ne 1){throw 'RUST-CONTROLS mutation edit not unique'}
    $changed=$changed.Replace($find,$replace)
    $target=Join-Path $shadow ($mutation.id+'.ps1')
    [IO.File]::WriteAllText($target,$changed,$utf8)
    $fixture=@{id=$mutation.id;argument='';exit=1;stdout='';
      stderr=('RUST-CONTROLS REJECT: RUST-MISUSE: fixed ordered ID/code/source mapping differs'+$newline)}
    $result=Invoke-RSCCaller $fixture $target
    $result.edit=@{find=$find;replace=$replace;expectedOccurrences=1}
    $results.Add($result)
  }
  foreach($suffix in @(
    @{id='selector-known-plus-nul';codePoint=0},
    @{id='selector-known-plus-soft-hyphen';codePoint=173},
    @{id='selector-known-plus-zero-width-space';codePoint=8203},
    @{id='selector-known-plus-bom';codePoint=65279})){
    $fixture=@{id=$suffix.id;argument=(" -OnlyCase ('RS-IMMUTABLE-QUERY'+[char]"+[string]$suffix.codePoint+')');
      exit=1;stdout='';stderr=$invalid}
    $results.Add((Invoke-RSCCaller $fixture $original))
  }
  if($results.Count -ne 15 -or ($results.id -join '|') -cne ($expectedControls -join '|')){
    throw 'RUST-CONTROLS exact control result roster differs'
  }
  if([IO.Directory]::Exists($missingToolRoot)){throw 'RUST-CONTROLS unexpected toolchain path creation'}
  $report.rootSubstitution=@{find=$rootExpression;replace=$rootReplacement;expectedOccurrences=1}
  $report.success=$true
}catch{$failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){
    try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed '+$pin.path)}}
    catch{$errors.Add($_.Exception.Message)}
  }
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  try{Remove-RSCShadow}catch{$cleanupErrors.Add($_.Exception.Message)}
  $report.failure=$failure
  $report.results=@($results.ToArray());$report.stages=@($stages.ToArray());$report.pins=@($pins.ToArray())
  $report.integrity=@{attempted=$true;success=($pins.Count -gt 0 -and $errors.Count -eq 0);
    checkedPins=$pins.Count;errors=@($errors.ToArray());liveRestorationWrites=0}
  $report.cleanup=@{attempted=$true;success=($cleanupErrors.Count -eq 0);errors=@($cleanupErrors.ToArray());
    shadowRemoved=(-not $createdShadow -or -not [IO.Directory]::Exists($shadow));retainedEvidence=$run}
  $report.success=$report.success -and $null -eq $failure -and $report.integrity.success -and $report.cleanup.success
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  Write-RSCJson (Join-Path $run 'RESULT.json') $report
}
Write-Output ('RUST-CONTROLS success='+$report.success+' count='+$results.Count+' evidence='+$run)
if(-not $report.success){if($failure){[Console]::Error.WriteLine($failure)};exit 1}

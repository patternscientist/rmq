[CmdletBinding()]
param([ValidateRange(1,60)][int]$DeadlineSeconds=30)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$runner=Join-Path $PSScriptRoot 'native_clients.ps1'
$registryPath=Join-Path $PSScriptRoot 'native_clients.json'
$expectedIds=@('LN1-CPP-WORD','LN1-CPP-COMPARISON','LN1-RUST-WORD','LN1-RUST-COMPARISON',
  'LN1-RUST-OWNER-ERRORS','LN1-RUST-POST-TAKE-FAILURE','LN1-RUST-CONFLICT-NEW-FIRST',
  'LN1-RUST-CONFLICT-OLD-FIRST','LN1-RUST-CONFLICT-NATIVE-FIRST','LN1-RUST-INIT-FAILURE')
$expectedControls=@('caller-omitted','caller-known','caller-null','caller-empty-array',
  'caller-empty-string','caller-whitespace','caller-unknown','caller-duplicate',
  'registry-missing-middle','registry-duplicate-middle','registry-reorder-middle',
  'registry-handler-mismatch','registry-verdict-mismatch')
$helpers=@('scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
  'scripts/packed_native_lifecycle_stream_check.ps1','scripts/packed_native_lifecycle_integrity_check.ps1',
  'scripts/packed_native_lifecycle_storage_replay.ps1')
$run=Join-Path $root ('.lake/lifecycle-native1/client-selector-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($run)
$scratch=Join-Path $run 'disposable'
$shadowRoot=Join-Path $scratch 'repository'
$pins=[Collections.Generic.List[object]]::new();$scratchPins=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new();$stages=[Collections.Generic.List[object]]::new()
$report=[ordered]@{schema='lifecycle-native1-client-selector-controls-v1';success=$false;
  expectedIds=$expectedIds;expectedControls=$expectedControls;expectedCount=13;
  startedUtc=[DateTime]::UtcNow.ToString('o');deadlineSeconds=$DeadlineSeconds;
  deadlineRationale='Thirteen actual PowerShell validation callers; existing selector controls use30s per caller. No native executable, compiler or heavy mutex acquisition.';
  rootSubstitution=$null;helperCopies=@();results=@();stages=@();pins=@();failure=$null;integrity=$null;cleanup=$null;
  heavyMutexAcquired=$false;nativeClientInvocations=0;compilerInvocations=0}
function Pin-CSC([string]$Path){$pin=Get-LN1Pin $Path;$pins.Add($pin);return $pin}
function Quote-CSC([string]$Text){return "'"+$Text.Replace("'","''")+"'"}
function Write-CSCJson([string]$Path,$Value){[IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 25),$utf8)}
function Remove-CSCScratch {
  $full=[IO.Path]::GetFullPath($scratch)
  $prefix=[IO.Path]::GetFullPath($run).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or
      $full -cne [IO.Path]::GetFullPath((Join-Path $run 'disposable'))){throw 'CLIENT-SELECTORS: cleanup target outside owned scratch'}
  if([IO.Directory]::Exists($full)){
    $entries=@(Get-Item -LiteralPath $full)+@(Get-ChildItem -LiteralPath $full -Recurse -Force)
    foreach($entry in $entries){if($entry.Attributes -band [IO.FileAttributes]::ReparsePoint){throw 'CLIENT-SELECTORS: cleanup refuses reparse point'}}
    Remove-Item -LiteralPath $full -Recurse -Force
  }
  if([IO.Directory]::Exists($full)){throw 'CLIENT-SELECTORS: scratch remained'}
}
try{
  $shell=(Get-Process -Id $PID).Path
  foreach($path in @($PSCommandPath,$runner,$registryPath,$shell)+@($helpers|ForEach-Object{Join-Path $root $_})){
    [void](Pin-CSC $path)
  }
  $source=[IO.File]::ReadAllText($runner,$utf8)
  $registryBytes=[IO.File]::ReadAllBytes($registryPath)
  $registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
  if(($registry.orderedIds -join '|') -cne ($expectedIds -join '|') -or
      ($registry.cases.id -join '|') -cne ($expectedIds -join '|')){throw 'CLIENT-SELECTORS: fixed source registry roster differs'}
  $find='$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot ''../../../..''))'
  if([regex]::Matches($source,[regex]::Escape($find)).Count -ne 1){throw 'CLIENT-SELECTORS: root expression not unique'}
  $replace='$root='+(Quote-CSC $shadowRoot)
  $copiedSource=$source.Replace($find,$replace)
  $report.rootSubstitution=@{find=$find;replace=$replace;expectedOccurrences=1;otherRunnerEdits=0}
  [void][IO.Directory]::CreateDirectory((Join-Path $shadowRoot 'scripts'))
  foreach($relative in $helpers){
    $original=Get-LN1Pin (Join-Path $root $relative)
    $destination=Join-Path $shadowRoot $relative
    [IO.File]::Copy($original.path,$destination,$false)
    $copy=Get-LN1Pin $destination;$scratchPins.Add($copy)
    if($copy.bytes -ne $original.bytes -or $copy.sha256 -cne $original.sha256){throw 'CLIENT-SELECTORS: helper copy differs'}
    $report.helperCopies+=@{source=$original;copy=$copy;edits=0}
  }
  [IO.File]::WriteAllText((Join-Path $run 'copied-native-clients.ps1'),$copiedSource,$utf8)
  [void](Pin-CSC (Join-Path $run 'copied-native-clients.ps1'))
  $nl=[Environment]::NewLine
  $cases=@(
    @{id='caller-omitted';argument='';expectedExit=0;expectedOut=('NATIVE-CLIENTS VALIDATED cases=10 ids='+($expectedIds -join ',')+$nl);error=''},
    @{id='caller-known';argument=" -Cases 'LN1-RUST-OWNER-ERRORS'";expectedExit=0;expectedOut=('NATIVE-CLIENTS VALIDATED cases=1 ids=LN1-RUST-OWNER-ERRORS'+$nl);error=''},
    @{id='caller-null';argument=' -Cases $null';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: explicitly empty selector'},
    @{id='caller-empty-array';argument=' -Cases @()';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: explicitly empty selector'},
    @{id='caller-empty-string';argument=" -Cases ''";expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: empty or whitespace selector'},
    @{id='caller-whitespace';argument=" -Cases ' '";expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: empty or whitespace selector'},
    @{id='caller-unknown';argument=" -Cases 'LN1-UNKNOWN'";expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: unknown selector LN1-UNKNOWN'},
    @{id='caller-duplicate';argument=" -Cases @('LN1-RUST-WORD','LN1-RUST-WORD')";expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: duplicate selector LN1-RUST-WORD'},
    @{id='registry-missing-middle';argument='';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: registry schema/count differs'},
    @{id='registry-duplicate-middle';argument='';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: frozen mapping differs at LN1-RUST-POST-TAKE-FAILURE'},
    @{id='registry-reorder-middle';argument='';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: frozen mapping differs at LN1-RUST-OWNER-ERRORS'},
    @{id='registry-handler-mismatch';argument='';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: frozen mapping differs at LN1-RUST-OWNER-ERRORS'},
    @{id='registry-verdict-mismatch';argument='';expectedExit=1;expectedOut='';error='NATIVE-CLIENTS: frozen mapping differs at LN1-RUST-OWNER-ERRORS'})
  if(($cases.id -join '|') -cne ($expectedControls -join '|')){throw 'CLIENT-SELECTORS: planned control roster differs'}
  $report.plannedCases=$cases
  Write-CSCJson (Join-Path $run 'PLAN.json') $report
  foreach($case in $cases){
    $directory=Join-Path $scratch $case.id
    [void][IO.Directory]::CreateDirectory($directory)
    $entry=Join-Path $directory 'native_clients.ps1'
    [IO.File]::WriteAllText($entry,$copiedSource,$utf8);$scratchPins.Add((Get-LN1Pin $entry))
    $mutated=$utf8.GetString($registryBytes)|ConvertFrom-Json
    $mutation='none'
    switch -CaseSensitive ($case.id){
      'registry-missing-middle' {$mutated.cases=@($mutated.cases[0..3])+@($mutated.cases[5..9]);$mutated.orderedIds=@($mutated.orderedIds[0..3])+@($mutated.orderedIds[5..9]);$mutation='remove cases[4] and orderedIds[4]'}
      'registry-duplicate-middle' {$mutated.cases[5]=$mutated.cases[4];$mutated.orderedIds[5]=$mutated.orderedIds[4];$mutation='replace index5 by index4 in both rosters'}
      'registry-reorder-middle' {$x=$mutated.cases[4];$mutated.cases[4]=$mutated.cases[5];$mutated.cases[5]=$x;$x=$mutated.orderedIds[4];$mutated.orderedIds[4]=$mutated.orderedIds[5];$mutated.orderedIds[5]=$x;$mutation='swap indices4 and5 in both rosters'}
      'registry-handler-mismatch' {$mutated.cases[4].handler='cpp-production';$mutation='cases[4].handler = cpp-production'}
      'registry-verdict-mismatch' {$mutated.cases[4].expectedVerdict='reject';$mutation='cases[4].expectedVerdict = reject'}
    }
    $copyRegistry=Join-Path $directory 'native_clients.json'
    if($mutation -ceq 'none'){[IO.File]::WriteAllBytes($copyRegistry,$registryBytes)}else{Write-CSCJson $copyRegistry $mutated}
    $scratchPins.Add((Get-LN1Pin $copyRegistry))
    $retained=Join-Path $run ($case.id+'-registry.json')
    [IO.File]::Copy($copyRegistry,$retained,$false);$retainedPin=Pin-CSC $retained
    $caller=Join-Path $run ($case.id+'-caller.ps1')
    $body='$ErrorActionPreference="Stop"'+"`ntry {`n"+'& '+(Quote-CSC $entry)+' -Phase Validate -BuildReceipt '+
      (Quote-CSC (Join-Path $shadowRoot 'NONEXISTENT-RECEIPT.json'))+$case.argument+"`nexit `$LASTEXITCODE`n} catch {`n"+
      '[Console]::Error.Write("CLIENT-SELECTOR REJECT: "+$_.Exception.Message+"`n"); exit 1'+"`n}`n"
    [IO.File]::WriteAllText($caller,$body,$utf8);$callerPin=Pin-CSC $caller
    $stage=[ordered]@{id=$case.id;capture=$null;error=$null}
    try{
      $stage.capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$caller) $root (Join-Path $run $case.id) $DeadlineSeconds $case.id
      $stderr=if($case.expectedExit -eq 0){''}else{'CLIENT-SELECTOR REJECT: '+$case.error+"`n"}
      Assert-LNOuterCapture $stage.capture $case.expectedOut $stderr $case.expectedExit $case.id
      $unexpected=Join-Path $shadowRoot '.lake'
      if([IO.Directory]::Exists($unexpected) -or [IO.File]::Exists($unexpected)){throw 'CLIENT-SELECTORS: validation created runtime output'}
      $results.Add(@{id=$case.id;passed=$true;expectedStdout=$case.expectedOut;expectedStderr=$stderr;expectedExit=$case.expectedExit;
        caller=$callerPin;registry=$retainedPin;mutation=$mutation;capture=$stage.capture;runtimeOutputAbsent=$true;missingBuildReceiptUnread=$true})
    }catch{$stage.error=$_.Exception.Message;throw}finally{$stages.Add($stage)}
  }
  if($results.Count -ne 13 -or ($results.id -join '|') -cne ($expectedControls -join '|')){throw 'CLIENT-SELECTORS: actual control roster differs'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in @($pins.ToArray())+@($scratchPins.ToArray())){
    try{$now=Get-LN1Pin $pin.path;if($now.sha256 -cne $pin.sha256 -or $now.bytes -ne $pin.bytes){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}
  }
  $report.integrity=@{success=($errors.Count -eq 0);checkedPins=$pins.Count+$scratchPins.Count;errors=@($errors.ToArray());liveRestorationWrites=0}
  try{Remove-CSCScratch;$report.cleanup=@{success=$true;disposableRemoved=$true;retainedEvidence=$run}}
  catch{$report.cleanup=@{success=$false;error=$_.Exception.Message}}
  $report.success=$report.success -and $report.integrity.success -and $report.cleanup.success
  $report.results=@($results.ToArray());$report.stages=@($stages.ToArray());$report.pins=@($pins.ToArray());$report.shadowPins=@($scratchPins.ToArray())
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  Write-CSCJson (Join-Path $run 'RESULT.json') $report
}
Write-Output ('CLIENT-SELECTORS success='+$report.success+' cases='+$results.Count+' evidence='+$run)
if(-not $report.success){if($report.failure){[Console]::Error.WriteLine($report.failure)};exit 1}

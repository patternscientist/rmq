#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [ValidateSet('Discovery','Replay')][string]$Mode='Replay',
  [AllowNull()][AllowEmptyCollection()][AllowEmptyString()][object[]]$OnlyCase,
  [switch]$SelectorProbeOnly,
  [switch]$SelfTestOnly,
  [string]$BuildReceipt,
  [string]$DiagnosticsPath,
  [string]$DiagnosticsSHA256,
  [ValidateRange(1,3600)][int]$DeadlineSeconds=180,
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0',
  [string]$EvidenceDirectory='.lake/lifecycle-native1/export-mutations'
)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath=Join-Path $PSScriptRoot 'EXPORT_MUTATIONS.json'
$registryExpectedSHA='15034dc9ce6e6077d27487bc4dddd7990cef6b39c66de39dff2d9be8a6825660'
$mapping=@(
  'EX-WEAK-E01-PROGRAM|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E02-OWNER|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E03-PROJECTION|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E04-READY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E05-HALTED|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E06-MEMORY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E07-EMPTYKEYS|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E08-BANK|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E09-CAPACITY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E10-METADATA|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E11-OBSERVATIONS|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E12-CONTINUATION|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-E13-REPACKING|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q01-SOURCE|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q02-PROJECTION|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q03-READY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q04-HALTED|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q05-MEMORY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q06-OBSERVATIONS|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q07-BOUNDARY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q08-STEPS|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q09-BUDGET|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-WEAK-Q10-CAPACITY|mandatory-field-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-DELETE-E01-PROGRAM|mandatory-field-deletion|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-DELETE-Q05-MEMORY|mandatory-field-deletion|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-SIBLING-E01-FIXED-WORD|sibling-proposition-substitution|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-SIBLING-E02-OTHER-REQUEST|sibling-proposition-substitution|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-SIBLING-Q05-OUTPUT-REFLEXIVITY|sibling-proposition-substitution|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-SIBLING-Q10-INCOMING-CAPACITY|sibling-proposition-substitution|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|reject',
  'EX-ACCEPT-COMMENT|expected-accept-control|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|accept',
  'EX-ACCEPT-UNUSED-FACT|expected-accept-control|RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean|RMQ/Validation/LifecycleNativeContract.lean|accept',
  'AD-WEAK-COUNT-CONVERSION|admission-leaf-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Admission.lean|RMQ/Core/WordRAM/Native/Lifecycle/AdmissionContract.lean|reject',
  'AD-WEAK-WORD-DOMAIN|admission-leaf-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Admission.lean|RMQ/Core/WordRAM/Native/Lifecycle/AdmissionContract.lean|reject',
  'AD-WEAK-NATURAL-DECODE|admission-leaf-weakening|RMQ/Core/WordRAM/Native/Lifecycle/Codec.lean|RMQ/Core/WordRAM/Native/Lifecycle/AdmissionContract.lean|reject'
)
$ids=@($mapping|ForEach-Object{($_ -split '\|')[0]})
$producerPaths=@('RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean',
  'RMQ/Core/WordRAM/Native/Lifecycle/Admission.lean','RMQ/Core/WordRAM/Native/Lifecycle/Codec.lean')
$consumerPaths=@('RMQ/Validation/LifecycleNativeContract.lean',
  'RMQ/Core/WordRAM/Native/Lifecycle/AdmissionContract.lean')
$evidence=$null
$shadow=$null
$createdShadow=$false
$locked=$false
$mutex=$null
$failure=$null
$report=$null
$pins=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$results=[Collections.Generic.List[object]]::new()
$oldLeanPath=[Environment]::GetEnvironmentVariable('LEAN_PATH','Process')
$oldThreads=[Environment]::GetEnvironmentVariable('LEAN_NUM_THREADS','Process')
$oldPath=[Environment]::GetEnvironmentVariable('PATH','Process')
$prepared=$false

function Get-EMHash([byte[]]$Bytes) {
  $h=[Security.Cryptography.SHA256]::Create()
  try {return ([BitConverter]::ToString($h.ComputeHash($Bytes))).Replace('-','').ToLowerInvariant()}
  finally {$h.Dispose()}
}
function Read-EMText([string]$Path) {return $utf8.GetString([IO.File]::ReadAllBytes($Path))}
function Write-EMJson([string]$Path,[object]$Value) {
  [IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 60),$utf8)
}
function Assert-EMRegistry([object]$Registry) {
  if($Registry.schema -cne 'lifecycle-native1-export-mutations-v1' -or
      @($Registry.cases).Count -ne $mapping.Count -or
      $Registry.counts.total -ne $mapping.Count){throw 'REGISTRY count/schema'}
  if(($Registry.ordered_ids -join '|') -cne ($ids -join '|')){throw 'REGISTRY ordered IDs'}
  for($i=0;$i -lt $mapping.Count;$i++){
    $c=$Registry.cases[$i]
    $verdict=if($c.expected.consumer -ceq 'ordinary-exit-zero'){'accept'}elseif(
      $c.expected.consumer -ceq 'ordinary-nonzero-intended-client-rejection'){'reject'}else{throw 'REGISTRY verdict'}
    $actual=@($c.id,$c.kind,$c.producer_path,$c.consumer_path,$verdict)-join '|'
    if($actual -cne $mapping[$i]){throw 'REGISTRY ID/handler/verdict mapping'}
    if($c.expected.producer -cne 'ordinary-exit-zero' -or @($c.edits).Count -eq 0){throw 'REGISTRY producer'}
    foreach($e in $c.edits){
      if($e.path -cne $c.producer_path -or $e.expected_occurrences -ne 1 -or
          $e.find -isnot [string] -or $e.replace -isnot [string] -or
          [string]::IsNullOrEmpty($e.find) -or $e.find -ceq $e.replace){throw 'REGISTRY edit'}
    }
    if($verdict -ceq 'reject' -and
      (@($c.expected.intended_checks).Count -eq 0 -or @($c.expected.diagnostic_classes).Count -eq 0)){
      throw 'REGISTRY empty diagnostic target'
    }
  }
}
function Select-EMCases([object]$Registry,[bool]$Bound,[object]$Selector) {
  if(-not $Bound){return @($Registry.cases)}
  if($null -eq $Selector -or @($Selector).Count -eq 0){throw 'SELECTOR explicitly empty'}
  $known=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($knownId in $ids){$null=$known.Add($knownId)}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in @($Selector)){
    if($id -isnot [string] -or [string]::IsNullOrWhiteSpace($id)){throw 'SELECTOR empty/whitespace'}
    if(-not $known.Contains($id)){throw 'SELECTOR unknown'}
    if(-not $seen.Add($id)){throw 'SELECTOR duplicate'}
  }
  $selected=@($Registry.cases|Where-Object{$seen.Contains($_.id)})
  if($selected.Count -ne $seen.Count){throw 'SELECTOR mapped count differs'}
  return $selected
}
function Edit-EMSource([string]$Source,[object]$Case) {
  $changed=$Source
  foreach($e in $Case.edits){
    if([regex]::Matches($changed,[regex]::Escape($e.find)).Count -ne 1){throw ('EDIT nonunique '+$Case.id)}
    $changed=$changed.Replace($e.find,$e.replace)
  }
  if([string]::Equals($Source,$changed,[StringComparison]::Ordinal)){throw ('EDIT unchanged '+$Case.id)}
  return $changed
}
function Add-EMPin([string]$Path) {
  $pin=Get-LN1Pin $Path
  $pins.Add($pin)
  return $pin
}
function Assert-EMReceiptPin([object[]]$Expected,[string]$Path) {
  $full=[IO.Path]::GetFullPath($Path)
  $matching=@($Expected|Where-Object{[string]::Equals([IO.Path]::GetFullPath($_.path),$full,[StringComparison]::OrdinalIgnoreCase)})
  if($matching.Count -ne 1){throw ('PROVENANCE absent/duplicate build pin '+$full)}
  $current=Add-EMPin $full
  if($current.bytes -ne $matching[0].bytes -or $current.sha256 -cne $matching[0].sha256){
    throw ('PROVENANCE changed source/tool/artifact '+$full)
  }
}
function Invoke-EMStage([string]$Name,[string]$File,[string[]]$Arguments,[string]$Directory,[int]$Seconds=$DeadlineSeconds) {
  $item=[ordered]@{name=$Name;file=$File;arguments=$Arguments;cwd=$Directory;deadlineSeconds=$Seconds;
    startedUtc=[DateTime]::UtcNow.ToString('o');capture=$null;error=$null}
  try {
    $item.capture=Invoke-LNStreamCapture $root $File $Arguments $Directory (Join-Path $evidence $Name) $Seconds $Name
    $capture=$item.capture
    if($null -eq $capture.actual){throw ('CAPTURE no ordinary exit '+$Name)}
    $stdout=Read-LNExactStream $capture.spec.stdout
    $stderr=Read-LNExactStream $capture.spec.stderr
    Assert-LNOuterCapture $capture $stdout $stderr $capture.actual.exitCode $Name
    return $capture
  } catch {$item.error=$_.Exception.Message;throw}
  finally {$item.completedUtc=[DateTime]::UtcNow.ToString('o');$stages.Add($item)}
}
function Assert-EMCleanCompile([object]$Capture,[string]$Stage) {
  Assert-LNOuterCapture $Capture '' '' 0 $Stage
}
function Get-EMRanges([string]$Source) {
  $matches=[regex]::Matches($Source,'(?m)^theorem ([A-Za-z0-9_]+)\b')
  $ranges=@{}
  for($i=0;$i -lt $matches.Count;$i++){
    $a=$matches[$i].Index
    $b=if($i+1 -lt $matches.Count){$matches[$i+1].Index}else{$Source.Length}
    $ranges[$matches[$i].Groups[1].Value]=@(
      ($Source.Substring(0,$a).Split([char]10).Count),($Source.Substring(0,$b).Split([char]10).Count-1))
  }
  return $ranges
}
function Get-EMDiagnosticClass([string]$Text) {
  if($Text -cmatch '^(Type mismatch|type mismatch)\b'){return 'type-mismatch'}
  if($Text -cmatch '^Application type mismatch:'){return 'type-mismatch'}
  if($Text -cmatch '^(Function expected|function expected)\b'){return 'function-expected'}
  if($Text -cmatch '^(Invalid field|invalid field|Unknown constant|unknown constant)\b'){return 'unknown-field'}
  if($Text -cmatch '(?s)^tactic .rewrite. failed,.*(equality|iff)'){return 'rewrite-requires-equality'}
  if($Text -cmatch '^unsolved goals\b'){return 'dependent-unsolved-goal'}
  throw 'DIAGNOSTIC unrecognized class'
}
function Assert-EMDiscoveryReject([object]$Capture,[object]$Case,[string]$ConsumerSource) {
  $stdout=Read-LNExactStream $Capture.spec.stdout
  Assert-LNOuterCapture $Capture $stdout '' 1 $Case.id
  $ranges=Get-EMRanges $ConsumerSource
  $expected=@($Case.expected.intended_checks|ForEach-Object{($_.name -split '\.')[-1]})
  $found=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $diagnostics=[Collections.Generic.List[object]]::new()
  # Parsing here checks all diagnostic objects. Final replay additionally compares every original byte.
  $lines=$stdout.Split([char]10)
  for($i=0;$i -lt $lines.Length;$i++){
    $line=$lines[$i]
    if($i -eq $lines.Length-1 -and $line.Length -eq 0){continue}
    if($line.Length -eq 0){throw 'DIAGNOSTIC blank/unrelated output'}
    try {$d=$line|ConvertFrom-Json -ErrorAction Stop}catch{throw 'DIAGNOSTIC non-JSON output'}
    if($d.severity -cne 'error' -or $d.fileName -cne $Case.consumer_path -or $d.data -isnot [string]){
      throw 'DIAGNOSTIC wrong file/severity/data'
    }
    $surface=@($expected|Where-Object{$ranges.ContainsKey($_) -and
      $ranges[$_][0] -le $d.pos.line -and $d.pos.line -le $ranges[$_][1]})
    if($surface.Count -ne 1){throw 'DIAGNOSTIC unrelated theorem'}
    $class=Get-EMDiagnosticClass $d.data
    if($class -cne 'dependent-unsolved-goal' -and -not (@($Case.expected.diagnostic_classes) -ccontains $class)){
      throw 'DIAGNOSTIC unrelated class'
    }
    if($class -ceq 'dependent-unsolved-goal' -and -not $found.Contains($surface[0])){
      throw 'DIAGNOSTIC unexplained unsolved goal'
    }
    [void]$found.Add($surface[0])
    $diagnostics.Add([ordered]@{surface=$surface[0];class=$class;line=$d.pos.line;column=$d.pos.column;
      messageSHA256=(Get-EMHash ($utf8.GetBytes($d.data)))})
  }
  if($found.Count -ne $expected.Count){throw 'DIAGNOSTIC missing intended theorem'}
  return @($diagnostics.ToArray())
}
function Compare-EMFrozen([object]$Capture,[object]$Expected,[string]$Id) {
  $out=Read-LNExactStream $Capture.spec.stdout
  $err=Read-LNExactStream $Capture.spec.stderr
  Assert-LNOuterCapture $Capture $Expected.stdout $Expected.stderr $Expected.exit $Id
  foreach($part in @(@{path=$Capture.spec.stdout;expected=$Expected.stdout;bytes=$Expected.stdoutBytes;sha=$Expected.stdoutSHA256},
                     @{path=$Capture.spec.stderr;expected=$Expected.stderr;bytes=$Expected.stderrBytes;sha=$Expected.stderrSHA256})){
    $bytes=[IO.File]::ReadAllBytes($part.path)
    if($bytes.Length -ne $part.bytes -or (Get-EMHash $bytes) -cne $part.sha -or
      (Get-EMHash ($utf8.GetBytes($part.expected))) -cne $part.sha){throw ('DIAGNOSTIC exact bytes differ '+$Id)}
  }
}
function Remove-EMShadow {
  if(-not $createdShadow){return}
  $resolved=[IO.Path]::GetFullPath($shadow)
  $allowed=[IO.Path]::GetFullPath((Join-Path $root '.lake/lifecycle-native1')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $resolved.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or
      [IO.Path]::GetFileName($resolved) -cne 'export-mutation-shadow'){throw 'CLEANUP shadow escaped owned root'}
  if([IO.Directory]::Exists($resolved)){Remove-Item -LiteralPath $resolved -Recurse -Force}
  if([IO.Directory]::Exists($resolved)){throw 'CLEANUP shadow still exists'}
}
function Expect-EMFailure([scriptblock]$Run,[string]$Message) {
  try {& $Run|Out-Null}catch{if($_.Exception.Message -ceq $Message){return};throw}
  throw ('SELFTEST missing rejection '+$Message)
}
function Test-EMOwnedDescendant {
  $directory=Join-Path $evidence 'owned-descendant'
  [void][IO.Directory]::CreateDirectory($directory)
  $shell=(Get-Process -Id $PID).Path
  $childPidPath=Join-Path $directory 'grandchild.pid'
  $scriptPath=Join-Path $directory 'sleeper.ps1'
  $quotedShell=$shell.Replace("'","''")
  $quotedPid=$childPidPath.Replace("'","''")
  $source=@"
`$child=Start-Process -FilePath '$quotedShell' -ArgumentList @(
  '-NoLogo','-NoProfile','-Command','Start-Sleep -Seconds 120') -WindowStyle Hidden -PassThru
[IO.File]::WriteAllText('$quotedPid',[string]`$child.Id)
Start-Sleep -Seconds 120
"@
  [IO.File]::WriteAllText($scriptPath,$source,$utf8)
  $result=Invoke-RMQOwnedBoundedProcess -FilePath $shell `
    -Arguments @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$scriptPath) `
    -WorkingDirectory $directory -Stage 'export-descendant-self-test' `
    -DeadlineSeconds 6 -OutputLimitBytes 1000000 -TempRoot $directory
  Write-EMJson (Join-Path $directory 'barrier-result.json') $result
  if(-not $result.TimedOut){throw 'SELFTEST descendant fixture did not time out'}
  if(-not [IO.File]::Exists($childPidPath)){throw 'SELFTEST grandchild never started; no termination evidence'}
  $childId=[int]([IO.File]::ReadAllText($childPidPath))
  if($null -ne (Get-Process -Id $childId -ErrorAction SilentlyContinue)){
    Stop-Process -Id $childId -Force -ErrorAction SilentlyContinue
    throw 'SELFTEST grandchild survived owned-tree termination'
  }
  return [ordered]@{id='owned-descendant-termination';passed=$true;
    grandchild=$childId;absentImmediatelyAfterBarrier=$true;capture=$result}
}

try {
  $registryBytes=[IO.File]::ReadAllBytes($registryPath)
  if((Get-EMHash $registryBytes) -cne $registryExpectedSHA){throw 'REGISTRY raw SHA256'}
  $registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
  Assert-EMRegistry $registry
  $selected=@(Select-EMCases $registry $PSBoundParameters.ContainsKey('OnlyCase') $OnlyCase)
  if($SelectorProbeOnly -and $SelfTestOnly){throw 'SELECTOR conflicting modes'}
  if($SelfTestOnly -and $PSBoundParameters.ContainsKey('OnlyCase')){throw 'SELECTOR selftest cannot select semantic case'}
  foreach($case in $registry.cases){
    $null=Edit-EMSource (Read-EMText (Join-Path $root $case.producer_path)) $case
    $consumerText=Read-EMText (Join-Path $root $case.consumer_path)
    if($case.expected.consumer -ceq 'ordinary-nonzero-intended-client-rejection'){
      foreach($check in $case.expected.intended_checks){
        $shortName=($check.name -split '\.')[-1]
        if(-not $check.signature_source.StartsWith(('theorem '+$shortName),[StringComparison]::Ordinal) -or
          [regex]::Matches($consumerText,[regex]::Escape($check.signature_source)).Count -ne 1){
          throw ('REGISTRY expected consumer proposition changed '+$case.id)
        }
      }
    }
  }
  if($SelectorProbeOnly){Write-Output ('EXPORT-MUTATION SELECT='+($selected.id -join ','));exit 0}
  if(-not $SelfTestOnly){
    if([string]::IsNullOrWhiteSpace($BuildReceipt) -or -not [IO.File]::Exists($BuildReceipt)){throw 'PROVENANCE successful build receipt required'}
    if($Mode -ceq 'Replay' -and
      ([string]::IsNullOrWhiteSpace($DiagnosticsPath) -or $DiagnosticsSHA256 -cnotmatch '^[a-f0-9]{64}$')){
      throw 'DIAGNOSTIC frozen path and external raw SHA256 required'
    }
  }
  if([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT){throw 'PLATFORM uncovered; Windows certification only'}
  $baseEvidence=[IO.Path]::GetFullPath((Join-Path $root $EvidenceDirectory))
  $allowedEvidence=[IO.Path]::GetFullPath((Join-Path $root '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  if(-not $baseEvidence.StartsWith($allowedEvidence,[StringComparison]::OrdinalIgnoreCase)){throw 'EVIDENCE outside workspace .lake'}
  . (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
  $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  $locked=$mutex.WaitOne(0)
  if(-not $locked){throw 'MUTEX busy; no child launched'}
  $evidence=Join-Path $baseEvidence ([DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
  [void][IO.Directory]::CreateDirectory($evidence)
  $report=[ordered]@{schema='lifecycle-native1-export-replay-v1';mode=$Mode;success=$false;
    operation=$(if($SelfTestOnly){'self-tests'}else{$Mode.ToLowerInvariant()});
    registrySHA256=$registryExpectedSHA;registryCaseCount=$ids.Count;
    selected=$(if($SelfTestOnly){@()}else{@($selected.id)});
    caseCount=$(if($SelfTestOnly){0}else{$selected.Count});cases=@();stages=@();
    provenance=@();integrity=$null;cleanup=$null;failure=$null;startedUtc=[DateTime]::UtcNow.ToString('o');
    plan=@{deadlineSeconds=$DeadlineSeconds;reference='Historical focused lifecycle dependency stages use a 120-second bound; this small warm-cache producer/client pass uses 180 seconds with margin. Discovery records actual per-stage duration for final scheduling.'};
    streamBoundary='Complete raw byte captures through the existing child; strict UTF-8 decode and ordinal equality, no BOM/NUL/newline stripping. Returned-line helper text is not used as semantic output.';
    selfTests=@()}
  foreach($path in @($PSCommandPath,$registryPath,(Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
    (Join-Path $root 'scripts/owned_process_tree.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
    (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),(Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){$null=Add-EMPin $path}

  if($SelfTestOnly){
    $controls=[Collections.Generic.List[object]]::new()
    foreach($kind in @('missing-middle','duplicate-middle','reorder-middle')){
      $copy=$utf8.GetString($registryBytes)|ConvertFrom-Json
      switch($kind){
        'missing-middle'{$copy.cases=@($copy.cases[0..15]) + @($copy.cases[17..($copy.cases.Count-1)])}
        'duplicate-middle'{$copy.cases[16]=$copy.cases[15]}
        'reorder-middle'{$tmp=$copy.cases[15];$copy.cases[15]=$copy.cases[16];$copy.cases[16]=$tmp}
      }
      $message=if($kind -ceq 'missing-middle'){'REGISTRY count/schema'}else{'REGISTRY ID/handler/verdict mapping'}
      Expect-EMFailure {Assert-EMRegistry $copy} $message
      $controls.Add(@{id=$kind;passed=$true})
    }
    $quoted=$PSCommandPath.Replace("'","''")
    $shell=(Get-Process -Id $PID).Path
    $fixtures=@(
      @{id='omitted';arg='';exit=0;stdout=('EXPORT-MUTATION SELECT='+($ids -join ',')+[Environment]::NewLine);stderr=''},
      @{id='known';arg=(" -OnlyCase '"+$ids[15]+"'");exit=0;stdout=('EXPORT-MUTATION SELECT='+$ids[15]+[Environment]::NewLine);stderr=''},
      @{id='two-known-reversed';arg=(" -OnlyCase @('"+$ids[33]+"','"+$ids[29]+"')");exit=0;stdout=('EXPORT-MUTATION SELECT='+$ids[29]+','+$ids[33]+[Environment]::NewLine);stderr=''},
      @{id='null';arg=' -OnlyCase $null';exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR explicitly empty'+[Environment]::NewLine)},
      @{id='empty-array';arg=' -OnlyCase @()';exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR explicitly empty'+[Environment]::NewLine)},
      @{id='empty-string';arg=" -OnlyCase ''";exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR empty/whitespace'+[Environment]::NewLine)},
      @{id='whitespace';arg=" -OnlyCase ' '";exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR empty/whitespace'+[Environment]::NewLine)},
      @{id='unknown';arg=" -OnlyCase 'EX-UNKNOWN'";exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR unknown'+[Environment]::NewLine)},
      @{id='unknown-nul';arg=(" -OnlyCase ('"+$ids[15]+"'+[char]0)");exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR unknown'+[Environment]::NewLine)},
      @{id='unknown-soft-hyphen';arg=(" -OnlyCase ('"+$ids[15]+"'+[char]0xAD)");exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR unknown'+[Environment]::NewLine)},
      @{id='duplicate';arg=(" -OnlyCase @('"+$ids[15]+"','"+$ids[15]+"')");exit=1;stdout='';stderr=('EXPORT-MUTATION ERROR: SELECTOR duplicate'+[Environment]::NewLine)}
    )
    foreach($fixture in $fixtures){
      $caller=Join-Path $evidence ($fixture.id+'-caller.ps1')
      [IO.File]::WriteAllText($caller,("& '"+$quoted+"' -SelectorProbeOnly"+$fixture.arg+[Environment]::NewLine+'exit $LASTEXITCODE'+[Environment]::NewLine),$utf8)
      $capture=Invoke-EMStage ('selector-'+$fixture.id) $shell @('-NoProfile','-File',$caller) $root 30
      Assert-LNOuterCapture $capture $fixture.stdout $fixture.stderr $fixture.exit $fixture.id
      $controls.Add(@{id=('caller-'+$fixture.id);passed=$true})
    }
    # Existing owned-process barrier with a hidden child fixture; no semantic case
    # treats this deliberately induced timeout as an acceptable compiler result.
    $controls.Add((Test-EMOwnedDescendant))
    $expectedControls=@('missing-middle','duplicate-middle','reorder-middle',
      'caller-omitted','caller-known','caller-two-known-reversed','caller-null','caller-empty-array','caller-empty-string',
      'caller-whitespace','caller-unknown','caller-unknown-nul','caller-unknown-soft-hyphen',
      'caller-duplicate','owned-descendant-termination')
    if($controls.Count -ne 15 -or ($controls.id -join '|') -cne ($expectedControls -join '|')){
      throw 'SELFTEST exact control roster differs'
    }
    $report.selfTests=@($controls.ToArray())
    $prepared=$true
  } else {
    $receipt=Read-EMText $BuildReceipt|ConvertFrom-Json
    if(-not $receipt.success){throw 'PROVENANCE build failed/incomplete'}
    $null=Add-EMPin $BuildReceipt
    $modules=@(Get-LN1ImportClosure @('RMQ.Validation.LifecycleNativeContract','RMQ.Core.WordRAM.Native.Lifecycle.AdmissionContract'))
    $library=Join-Path $root '.lake/build/lib/lean'
    $lean=Join-Path $LeanRoot 'bin/lean.exe'
    Assert-EMReceiptPin @($receipt.toolPins) $lean
    # The standard receipt covers the entire Lean installation, including
    # transitive Init/Std imports and runtime DLLs, not only lean.exe.
    $seenTools=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
    foreach($priorTool in @($receipt.toolPins)){
      if(-not $seenTools.Add([IO.Path]::GetFullPath($priorTool.path))){throw 'PROVENANCE duplicate compiler/import pin'}
      $currentTool=Add-EMPin $priorTool.path
      if($currentTool.bytes -ne $priorTool.bytes -or $currentTool.sha256 -cne $priorTool.sha256){
        throw ('PROVENANCE changed compiler/import dependency '+$priorTool.path)
      }
    }
    foreach($module in $modules){
      Assert-EMReceiptPin @($receipt.sourcePins) (Join-Path $root ($module.Replace('.','/')+'.lean'))
      Assert-EMReceiptPin @($receipt.generatedPins) (Join-Path $library ($module.Replace('.','/')+'.olean'))
    }
    foreach($relative in @('lean-toolchain','lakefile.toml','lake-manifest.json',
      'scripts/lifecycle_native_identity.ps1','scripts/owned_process_tree.ps1',
      'scripts/packed_native_identity.ps1','scripts/packed_native_lifecycle_stream_check.ps1',
      'scripts/packed_native_lifecycle_storage_replay.ps1','scripts/packed_native_lifecycle_integrity_check.ps1')){
      Assert-EMReceiptPin @($receipt.sourcePins) (Join-Path $root $relative)
    }
    foreach($relative in @('bin/libleanshared.dll','bin/libInit_shared.dll','lib/lean/Init.olean','lib/lean/Std.olean')){
      Assert-EMReceiptPin @($receipt.toolPins) (Join-Path $LeanRoot $relative)
    }
    $manifestPins=@(@{path=$registry.source_identity.producer_path;sha256=$registry.source_identity.producer_sha256},
      @{path=$registry.source_identity.consumer_path;sha256=$registry.source_identity.consumer_sha256},
      @{path=$registry.source_identity.boundary_proofs_path;sha256=$registry.source_identity.boundary_proofs_sha256})+@($registry.source_identity.admission_sources)
    foreach($pin in $manifestPins){
      if((Get-EMHash ([IO.File]::ReadAllBytes((Join-Path $root $pin.path)))) -cne $pin.sha256){throw ('PROVENANCE registry source changed '+$pin.path)}
    }
    $frozen=$null
    if($Mode -ceq 'Replay'){
      $diagnosticBytes=[IO.File]::ReadAllBytes($DiagnosticsPath)
      if((Get-EMHash $diagnosticBytes) -cne $DiagnosticsSHA256){throw 'DIAGNOSTIC frozen raw SHA256 differs'}
      $null=Add-EMPin $DiagnosticsPath
      $frozen=$utf8.GetString($diagnosticBytes)|ConvertFrom-Json
      if($frozen.schema -cne 'lifecycle-native1-export-diagnostics-v1' -or
        $frozen.reviewStatus -cne 'FROZEN_ROOT_REVIEWED' -or
        $frozen.registrySHA256 -cne $registryExpectedSHA -or
        ($frozen.orderedIds -join '|') -cne ($ids -join '|') -or
        ($frozen.cases.id -join '|') -cne ($ids -join '|')){throw 'DIAGNOSTIC complete registry mapping differs'}
      if($frozen.leanSHA256 -cne (Get-EMHash ([IO.File]::ReadAllBytes($lean)))){throw 'DIAGNOSTIC compiler identity differs'}
    }
    $shadow=Join-Path $root '.lake/lifecycle-native1/export-mutation-shadow'
    if([IO.Directory]::Exists($shadow) -or [IO.File]::Exists($shadow)){throw 'SHADOW pre-existing; inspect before retry'}
    [void][IO.Directory]::CreateDirectory($shadow)
    $createdShadow=$true
    $imports=Join-Path $shadow 'imports'
    $sourceRoot=Join-Path $shadow 'source'
    foreach($module in $modules){
      $stem=$module.Replace('.','/')
      foreach($copy in @(@{src=(Join-Path $library ($stem+'.olean'));dst=(Join-Path $imports ($stem+'.olean'))},
                        @{src=(Join-Path $root ($stem+'.lean'));dst=(Join-Path $sourceRoot ($stem+'.lean'))})){
        [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($copy.dst))
        [IO.File]::Copy($copy.src,$copy.dst,$false)
      }
    }
    [Environment]::SetEnvironmentVariable('LEAN_PATH',($imports+[IO.Path]::PathSeparator+(Join-Path $LeanRoot 'lib/lean')),'Process')
    [Environment]::SetEnvironmentVariable('LEAN_NUM_THREADS','1','Process')
    [Environment]::SetEnvironmentVariable('PATH',((Join-Path $LeanRoot 'bin')+';'+$oldPath),'Process')
    $diagnosed=[Collections.Generic.List[object]]::new()
    foreach($case in $selected){
      # Reset the entire small mutable set before each case; all writes remain disposable.
      foreach($relative in ($producerPaths+@('RMQ/Core/WordRAM/Native/Lifecycle/BoundaryProofs.lean','RMQ/Core/WordRAM/Native/Lifecycle/Entry.lean'))){
        [IO.File]::Copy((Join-Path $root $relative),(Join-Path $sourceRoot $relative),$true)
        [IO.File]::Copy((Join-Path $library ([IO.Path]::ChangeExtension($relative,'.olean'))),(Join-Path $imports ([IO.Path]::ChangeExtension($relative,'.olean'))),$true)
      }
      $source=Read-EMText (Join-Path $root $case.producer_path)
      $changed=Edit-EMSource $source $case
      [IO.File]::WriteAllText((Join-Path $sourceRoot $case.producer_path),$changed,$utf8)
      $consumerModule=$case.consumer_path.Substring(0,$case.consumer_path.Length-5).Replace('/','.').Replace('\','.')
      $caseClosure=@(Get-LN1ImportClosure @($consumerModule))
      $affected=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
      [void]$affected.Add($case.producer_path.Substring(0,$case.producer_path.Length-5).Replace('/','.'))
      $compiled=[Collections.Generic.List[string]]::new()
      foreach($module in $caseClosure){
        if($module -ceq $consumerModule){continue}
        $relative=$module.Replace('.','/')+'.lean'
        $body=Read-EMText (Join-Path $sourceRoot $relative)
        foreach($import in [regex]::Matches($body,'(?m)^import\s+(RMQ(?:\.[A-Za-z0-9_]+)+)\s*$')){
          if($affected.Contains($import.Groups[1].Value)){[void]$affected.Add($module)}
        }
        if(-not $affected.Contains($module)){continue}
        $output=Join-Path $imports ($module.Replace('.','/')+'.olean')
        $stage=$case.id+'-producer-'+$compiled.Count
        $capture=Invoke-EMStage $stage $lean @('--json',("--root="+$sourceRoot),'-o',$output,$relative) $sourceRoot
        Assert-EMCleanCompile $capture $stage
        $compiled.Add($module)
      }
      if($compiled.Count -eq 0){throw 'PRODUCER no altered module compiled'}
      $clientSource=Read-EMText (Join-Path $sourceRoot $case.consumer_path)
      if(-not [string]::Equals($clientSource,(Read-EMText (Join-Path $root $case.consumer_path)),[StringComparison]::Ordinal)){throw 'CONSUMER changed'}
      $client=Invoke-EMStage ($case.id+'-consumer') $lean @('--json',("--root="+$sourceRoot),$case.consumer_path) $sourceRoot
      $diagnostics=@()
      if($case.expected.consumer -ceq 'ordinary-exit-zero'){Assert-EMCleanCompile $client $case.id}
      else{$diagnostics=@(Assert-EMDiscoveryReject $client $case $clientSource)}
      if($Mode -ceq 'Replay'){
        $expected=@($frozen.cases|Where-Object{$_.id -ceq $case.id})
        if($expected.Count -ne 1){throw 'DIAGNOSTIC case missing/duplicate'}
        Compare-EMFrozen $client $expected[0] $case.id
      }
      $outBytes=[IO.File]::ReadAllBytes($client.spec.stdout)
      $errBytes=[IO.File]::ReadAllBytes($client.spec.stderr)
      $diagnosed.Add([ordered]@{id=$case.id;exit=$client.actual.exitCode;
        stdout=$utf8.GetString($outBytes);stderr=$utf8.GetString($errBytes);
        stdoutBytes=$outBytes.Length;stderrBytes=$errBytes.Length;
        stdoutSHA256=(Get-EMHash $outBytes);stderrSHA256=(Get-EMHash $errBytes);diagnostics=$diagnostics})
      $results.Add([ordered]@{id=$case.id;handler=$case.kind;expected=$case.expected.consumer;success=$true;
        compiled=@($compiled.ToArray());producerSourceSHA256=(Get-EMHash ($utf8.GetBytes($changed)));
        consumerSourceSHA256=(Get-EMHash ($utf8.GetBytes($clientSource)));
        producerArtifact=(Get-LN1Pin (Join-Path $imports ([IO.Path]::ChangeExtension($case.producer_path,'.olean'))));
        consumerCapture=$client.spec;diagnostics=$diagnostics})
      Write-EMJson (Join-Path $evidence 'CASES.json') @($results.ToArray())
      Write-Output ('EXPORT-MUTATION CASE '+$case.id+' PASS')
    }
    if(($results.id -join '|') -cne ($selected.id -join '|') -or $results.Count -ne $selected.Count){throw 'RESULT ordered case roster differs'}
    if($Mode -ceq 'Discovery'){
      Write-EMJson (Join-Path $evidence 'DIAGNOSTICS.candidate.json') ([ordered]@{
        schema='lifecycle-native1-export-diagnostics-v1';reviewStatus='PENDING_ROOT_REVIEW';
        registrySHA256=$registryExpectedSHA;leanSHA256=(Get-EMHash ([IO.File]::ReadAllBytes($lean)));
        orderedIds=@($selected.id);cases=@($diagnosed.ToArray())})
    }
    $prepared=$true
  }
} catch {$failure=$_.Exception.Message}
finally {
  $integrityErrors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){
    try{
      if(-not [IO.File]::Exists($pin.path)){throw ('missing '+$pin.path)}
      $bytes=[IO.File]::ReadAllBytes($pin.path)
      if($bytes.Length -ne $pin.bytes -or (Get-EMHash $bytes) -cne $pin.sha256.ToLowerInvariant()){throw ('changed '+$pin.path)}
    }catch{$integrityErrors.Add($_.Exception.Message)}
  }
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  try{Remove-EMShadow}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{[Environment]::SetEnvironmentVariable('LEAN_PATH',$oldLeanPath,'Process')}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{[Environment]::SetEnvironmentVariable('LEAN_NUM_THREADS',$oldThreads,'Process')}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{[Environment]::SetEnvironmentVariable('PATH',$oldPath,'Process')}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($locked){$mutex.ReleaseMutex()};if($null -ne $mutex){$mutex.Dispose()}}catch{$cleanupErrors.Add($_.Exception.Message)}
  if($null -ne $report){
    $report.failure=$failure
    $report.provenance=@($pins.ToArray())
    $report.integrity=@{attempted=$true;success=($pins.Count -gt 0 -and $integrityErrors.Count -eq 0);checkedPins=$pins.Count;errors=@($integrityErrors.ToArray());liveRestorationWrites=0}
    $report.cleanup=@{attempted=$true;success=($cleanupErrors.Count -eq 0);errors=@($cleanupErrors.ToArray());shadowRemoved=(-not $createdShadow -or -not [IO.Directory]::Exists($shadow));mutexReleased=$locked}
    $report.cases=@($results.ToArray())
    $report.stages=@($stages.ToArray())
    $report.completedUtc=[DateTime]::UtcNow.ToString('o')
    $report.success=$prepared -and $null -eq $failure -and $report.integrity.success -and $report.cleanup.success
    Write-EMJson (Join-Path $evidence 'RESULT.json') $report
    if(-not $report.success -and $null -eq $failure){$failure='FINALLY integrity/cleanup failed'}
  }
}
if($null -ne $failure){[Console]::Error.WriteLine('EXPORT-MUTATION ERROR: '+$failure);exit 1}
Write-Output ('EXPORT-MUTATION PASS mode='+$Mode+' count='+$results.Count+' evidence='+$evidence)
exit 0

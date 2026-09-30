[CmdletBinding()]
param(
  [ValidateSet('Plan','Discovery','Replay')][string]$Mode='Plan',
  [AllowNull()][AllowEmptyCollection()][AllowEmptyString()][object]$Cases,
  [string]$BuildReceipt='',
  [string]$ExpectationsPath='',
  [string]$ExpectationsSHA256='',
  [int]$CaseDeadlineSeconds=300,
  [string]$DeadlineRationale='Initial native-control discovery ceiling: predecessor62-120s plus cold margin; root must replace with actual new-route measurements before final replay.',
  [string]$LeanRoot='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$LeanRoot=[IO.Path]::GetFullPath($LeanRoot)
$registryPath=Join-Path $PSScriptRoot 'native_controls.json'
function Test-NCExactString($Actual,[string]$Expected){
  return $Actual -is [string] -and [string]::Equals($Actual,$Expected,[StringComparison]::Ordinal)
}
function Test-NCExactMember($Actual,[string[]]$Expected){
  if($Actual -isnot [string]){return $false}
  foreach($item in $Expected){if([string]::Equals($Actual,$item,[StringComparison]::Ordinal)){return $true}}
  return $false
}
$registry=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
# This independent complete mapping is checked before any output or child.
# These are challenges, not predictions of rejection. Root reviews measurements.
$mapping=@(
  'NC-NONE-BUILD|none|build|0|healthy',
  'NC-NONE-QUERY|none|query|0|healthy',
  'NC-SKIP-REPACK-BUILD|skip-repack|build|0|skip-repack',
  'NC-SKIP-REPACK-QUERY|skip-repack|query|0|skip-repack',
  'NC-EXTRA-OWNER-ALIAS-BUILD|extra-owner-alias|build|0|extra-owner-alias',
  'NC-EXTRA-OWNER-ALIAS-QUERY|extra-owner-alias|query|0|extra-owner-alias',
  'NC-RETAIN-INPUT-BUILD|retain-input|build|0|retain-input',
  'NC-RETAIN-OLD-ARENA-BUILD|retain-old-arena|build|0|retain-old-arena',
  'NC-RETAIN-OLD-ARENA-QUERY|retain-old-arena|query|0|retain-old-arena',
  'NC-RETAIN-KEYS-BUILD|retain-keys|build|0|retain-keys',
  'NC-RETAIN-HISTORY-BUILD|retain-history|build|0|retain-history',
  'NC-RETAIN-HISTORY-QUERY|retain-history|query|0|retain-history',
  'NC-WRONG-COPY-VALUE-BUILD-0|wrong-copy-value|build|0|wrong-copy-value',
  'NC-WRONG-COPY-VALUE-BUILD-1|wrong-copy-value|build|1|wrong-copy-value',
  'NC-WRONG-COPY-VALUE-QUERY-0|wrong-copy-value|query|0|wrong-copy-value',
  'NC-WRONG-COPY-VALUE-QUERY-1|wrong-copy-value|query|1|wrong-copy-value',
  'NC-WRONG-COPY-OFFSET-BUILD-0|wrong-copy-offset|build|0|wrong-copy-offset',
  'NC-WRONG-COPY-OFFSET-BUILD-1|wrong-copy-offset|build|1|wrong-copy-offset',
  'NC-WRONG-COPY-OFFSET-QUERY-0|wrong-copy-offset|query|0|wrong-copy-offset',
  'NC-WRONG-COPY-OFFSET-QUERY-1|wrong-copy-offset|query|1|wrong-copy-offset',
  'NC-PARTIAL-COPY-BUILD-0|partial-copy|build|0|partial-copy',
  'NC-PARTIAL-COPY-BUILD-1|partial-copy|build|1|partial-copy',
  'NC-PARTIAL-COPY-BUILD-8272|partial-copy|build|8272|partial-copy',
  'NC-PARTIAL-COPY-BUILD-8273|partial-copy|build|8273|partial-copy',
  'NC-PARTIAL-COPY-BUILD-8274|partial-copy|build|8274|partial-copy',
  'NC-PARTIAL-COPY-QUERY-0|partial-copy|query|0|partial-copy',
  'NC-PARTIAL-COPY-QUERY-1|partial-copy|query|1|partial-copy',
  'NC-PARTIAL-COPY-QUERY-8272|partial-copy|query|8272|partial-copy',
  'NC-PARTIAL-COPY-QUERY-8273|partial-copy|query|8273|partial-copy',
  'NC-PARTIAL-COPY-QUERY-8274|partial-copy|query|8274|partial-copy',
  'NC-FAIL-AFTER-TAKE-QUERY|fail-after-take|query|0|post-take',
  'NC-MODEL-FAULT-BUILD|model-fault|build|0|model-fault',
  'NC-EXHAUSTED-BUILD-0|exhausted|build|0|fuel',
  'NC-EXHAUSTED-BUILD-20|exhausted|build|20|fuel',
  'NC-EXHAUSTED-BUILD-100|exhausted|build|100|fuel',
  'NC-FAIL-BEFORE-TAKE-ALLOC-BUILD|fail-before-take-alloc|build|0|pre-take-allocation',
  'NC-FAIL-BEFORE-TAKE-ALLOC-QUERY|fail-before-take-alloc|query|0|pre-take-allocation',
  'NC-FAIL-BEFORE-PUBLISH-BUILD|fail-before-publish|build|0|pre-publication',
  'NC-FAIL-BEFORE-PUBLISH-QUERY|fail-before-publish|query|0|pre-publication',
  'NC-SHARED-SCALAR-ACCEPT-BUILD|shared-scalar-accept|build|0|shared-scalar',
  'NC-SHARED-SCALAR-ACCEPT-QUERY|shared-scalar-accept|query|0|shared-scalar',
  'NC-ENDPOINT-SHORT-BUILD|endpoint-short|build|0|admission',
  'NC-ENDPOINT-SHORT-QUERY|endpoint-short|query|0|admission',
  'NC-ENDPOINT-LONG-BUILD|endpoint-long|build|0|admission',
  'NC-ENDPOINT-LONG-QUERY|endpoint-long|query|0|admission',
  'NC-NEGATIVE-ZERO-BUILD|negative-zero|build|0|admission',
  'NC-BAD-SIGN-BUILD|bad-sign|build|0|admission',
  'NC-WORD-INPUTFITS-BUILD|word-inputfits|build|0|admission')
$mappingSHA256=Get-LN1BytesHash ($utf8.GetBytes(($mapping -join "`n")+"`n"))
if($mapping.Count -ne 48 -or $mappingSHA256 -cne 'ea90bd61fb7d226210aa47b3afd38cbca8953debaf3246c238a5785b20e69f2d'){throw 'NATIVE-CONTROLS: fixed internal mapping differs'}
if(-not (Test-NCExactString $registry.schema 'lifecycle-native1-native-control-registry-v1') -or
    -not (Test-NCExactString $registry.status 'DISCOVERY_ROSTER_NOT_VERDICTS') -or
    @($registry.cases).Count -ne $mapping.Count -or @($registry.orderedIds).Count -ne $mapping.Count){
  throw 'NATIVE-CONTROLS: registry schema/count differs'
}
$known=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
for($i=0;$i -lt $mapping.Count;$i++){
  $m=$mapping[$i] -split '\|';$c=$registry.cases[$i]
  if(-not (Test-NCExactString $c.id $m[0]) -or -not (Test-NCExactString $registry.orderedIds[$i] $m[0]) -or -not $known.Add($c.id) -or
      -not (Test-NCExactString $c.handler 'control-discovery') -or -not (Test-NCExactString $c.control $m[1]) -or -not (Test-NCExactString $c.phase $m[2]) -or
      $c.argument -isnot [string] -or -not (Test-NCExactString $c.argument $m[3]) -or -not (Test-NCExactString $c.surface $m[4]) -or
      -not (Test-NCExactString $c.discoveryVerdict 'unassigned')){
    throw ('NATIVE-CONTROLS: frozen mapping differs at '+$m[0])
  }
}
if(-not $PSBoundParameters.ContainsKey('Cases')){$selected=@($registry.orderedIds)}else{
  if($null -eq $Cases -or @($Cases).Count -eq 0){throw 'NATIVE-CONTROLS: explicitly empty selector'}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in @($Cases)){
    if($id -isnot [string] -or [string]::IsNullOrWhiteSpace($id)){throw 'NATIVE-CONTROLS: empty or whitespace selector'}
    if(-not $known.Contains($id)){throw ('NATIVE-CONTROLS: unknown selector '+$id)}
    if(-not $seen.Add($id)){throw ('NATIVE-CONTROLS: duplicate selector '+$id)}
  }
  $selected=@($Cases)
}
if($Mode -cnotin @('Plan','Discovery','Replay') -or $CaseDeadlineSeconds -le 0 -or
    [string]::IsNullOrWhiteSpace($DeadlineRationale)){
  throw 'NATIVE-CONTROLS: exact mode, positive bounded deadline and rationale required'
}
if($Mode -ceq 'Plan'){
  Write-Output ('NATIVE-CONTROLS PLAN cases='+$selected.Count+' ids='+($selected -join ','));exit 0
}
# Root freezes the complete measured verdict roster only after review. A partial
# discovery receipt or a self-assigned measurement cannot satisfy Replay.
$frozen=$null
if($Mode -ceq 'Replay'){
  if([string]::IsNullOrWhiteSpace($ExpectationsPath) -or $ExpectationsSHA256 -notmatch '^[a-fA-F0-9]{64}$' -or
      (Get-FileHash -LiteralPath $ExpectationsPath).Hash -ine $ExpectationsSHA256){throw 'NATIVE-CONTROLS: reviewed expectation identity required'}
  $frozen=[IO.File]::ReadAllText($ExpectationsPath,$utf8)|ConvertFrom-Json
  if(-not (Test-NCExactString $frozen.schema 'lifecycle-native1-native-control-expectations-v1') -or
      -not (Test-NCExactString $frozen.status 'FROZEN_ROOT_REVIEWED') -or -not (Test-NCExactString $frozen.mappingSHA256 $mappingSHA256) -or
      @($frozen.cases).Count -ne $mapping.Count -or
      @($frozen.cases.id).Count -ne @($registry.orderedIds).Count){throw 'NATIVE-CONTROLS: complete reviewed expectation mapping required'}
  for($i=0;$i -lt $mapping.Count;$i++){
    $e=$frozen.cases[$i];$c=$registry.cases[$i]
    $allowed=switch -CaseSensitive ($c.surface){
      'healthy' {@('accept')}
      'shared-scalar' {@('accept','nondistinguishing')}
      {$_ -cin @('admission','pre-take-allocation')} {
        if($c.phase -ceq 'query'){@('reject-before-transfer','nondistinguishing')}else{@('reject-before-build','nondistinguishing')}
      }
      {$_ -cin @('partial-copy','post-take','model-fault','fuel','pre-publication')} {@('reject-operation','nondistinguishing')}
      default {@('reject-publication','nondistinguishing')}
    }
    if(-not (Test-NCExactMember $e.verdict $allowed)){throw ('NATIVE-CONTROLS: reviewed verdict does not match challenge surface '+$c.id)}
    if(-not (Test-NCExactString $e.id $c.id) -or -not (Test-NCExactString $e.control $c.control) -or -not (Test-NCExactString $e.phase $c.phase) -or -not (Test-NCExactString $e.argument $c.argument) -or
        -not (Test-NCExactString $e.surface $c.surface) -or $null -eq $e.projection -or
        -not (Test-NCExactMember $e.verdict @('accept','reject-publication','reject-before-transfer','reject-before-build','reject-operation','nondistinguishing')) -or
        [string]::IsNullOrWhiteSpace($e.oracleExplanation)){
      throw ('NATIVE-CONTROLS: missing reviewed predicate/verdict '+$c.id)
    }
  }
}elseif($PSBoundParameters.ContainsKey('ExpectationsPath') -or $PSBoundParameters.ContainsKey('ExpectationsSHA256')){
  throw 'NATIVE-CONTROLS: expectation arguments require Replay'
}
foreach($variable in @('PACKED_LIFECYCLE_FAIL_INIT','PACKED_LIFECYCLE_FAIL_AFTER_TAKE')){
  if([Environment]::GetEnvironmentVariable($variable,'Process')){throw ('NATIVE-CONTROLS: ambient test control '+$variable)}
}
if([string]::IsNullOrWhiteSpace($BuildReceipt)){throw 'NATIVE-CONTROLS: BuildReceipt required'}
$build=[IO.File]::ReadAllText($BuildReceipt,$utf8)|ConvertFrom-Json
if($build.schema -cne 'lifecycle-native1-build-v1' -or -not $build.success -or
    -not $build.integrity.success -or -not $build.cleanup.success -or $build.phase -cnotin @('all','clients')){
  throw 'NATIVE-CONTROLS: successful native client build receipt required'
}
$run=Join-Path $root ('.lake/lifecycle-native1/native-controls/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')+'-'+[Guid]::NewGuid().ToString('N').Substring(0,8))
[void][IO.Directory]::CreateDirectory($run)
$pins=[Collections.Generic.List[object]]::new();$results=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new();$candidates=[Collections.Generic.List[object]]::new()
$inputFingerprint=$null
$mutex=$null;$locked=$false;$savedPath=$env:PATH;$savedErrorMode=$null
$report=[ordered]@{schema='lifecycle-native1-native-controls-v1';mode=$Mode;success=$false;campaignComplete=$false;
  selected=$selected;completeRegistry=(($selected -join '|') -ceq ($registry.orderedIds -join '|'));
  startedUtc=[DateTime]::UtcNow.ToString('o');caseDeadlineSeconds=$CaseDeadlineSeconds;
  deadlineRationale=$DeadlineRationale;orchestration='single-stage-direct-v2';
  mappingSHA256=$mappingSHA256;mutexOwner='native_controls.ps1 for the complete selected campaign';
  stagedFiles=@();dependencies=$null;
  pins=@();results=@();stages=@();failure=$null;integrity=$null;cleanup=$null}
function Pin-Control([string]$Path){$p=Get-LN1Pin $Path;$pins.Add($p);return $p}
function Get-LNPin([string]$Path){return Pin-Control $Path}
function Assert-ControlPin($Pin){
  $p=Pin-Control $Pin.path
  if($p.sha256 -cne $Pin.sha256 -or $p.bytes -ne $Pin.bytes){throw ('NATIVE-CONTROLS: stale pin '+$Pin.path)}
}
function Get-ControlRecipe([AllowNull()][AllowEmptyCollection()][object[]]$PinItems){
  if($null -eq $PinItems -or $PinItems.Count -eq 0){throw 'NATIVE-CONTROLS: empty recipe pin roster'}
  # Pin path identity is the exact supplied absolute Windows path. Do not fold
  # case or culturally ignore characters, and do not sort dictionary properties.
  $byPath=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach($pin in $PinItems){
    if($null -eq $pin -or $pin.path -isnot [string] -or
        [string]::IsNullOrWhiteSpace($pin.path) -or -not [IO.Path]::IsPathFullyQualified($pin.path) -or
        ($pin.bytes -isnot [int] -and $pin.bytes -isnot [long]) -or $pin.bytes -lt 0 -or
        $pin.sha256 -isnot [string] -or $pin.sha256 -cnotmatch '^[0-9A-Fa-f]{64}$'){
      throw 'NATIVE-CONTROLS: malformed recipe pin'
    }
    $path=[string]$pin.path;$length=[long]$pin.bytes;$digest=[string]$pin.sha256
    if($byPath.ContainsKey($path)){
      $prior=$byPath[$path]
      if($prior.bytes -ne $length -or -not [string]::Equals($prior.sha256,$digest,[StringComparison]::Ordinal)){
        throw ('NATIVE-CONTROLS: conflicting recipe pin '+$path)
      }
    }else{$byPath.Add($path,[ordered]@{path=$path;bytes=$length;sha256=$digest})}
  }
  [string[]]$keys=@($byPath.Keys)
  [Array]::Sort($keys,[StringComparer]::Ordinal)
  $orderedPins=[Collections.Generic.List[object]]::new()
  $rows=[Collections.Generic.List[string]]::new()
  foreach($key in $keys){
    $pin=$byPath[$key];$orderedPins.Add($pin)
    $rows.Add($pin.path+"`t"+$pin.bytes.ToString([Globalization.CultureInfo]::InvariantCulture)+"`t"+$pin.sha256)
  }
  $text=($rows.ToArray() -join "`n")+"`n"
  $encoding=[Text.UTF8Encoding]::new($false,$true)
  return [ordered]@{schema='lifecycle-native1-control-input-recipe-v1';
    pathIdentity='Ordinal exact absolute supplied paths; no case folding or filesystem-alias claim';
    sourcePinCount=$PinItems.Count;uniquePinCount=$keys.Length;duplicatePinCount=($PinItems.Count-$keys.Length);
    pins=@($orderedPins.ToArray());text=$text;sha256=(Get-LN1BytesHash ($encoding.GetBytes($text)))}
}
function Canonical-Control($Value){
  # Sort object keys while retaining array order, string bytes and full integers.
  # No whitespace, newline, diagnostic or numeric normalization is performed.
  if($null -eq $Value){return 'null'}
  if($Value -is [string] -or $Value -is [bool] -or $Value -is [ValueType]){return ConvertTo-Json -InputObject $Value -Depth 60 -Compress}
  if($Value -is [Collections.IDictionary]){
    return '{'+(@($Value.Keys|Sort-Object -CaseSensitive|ForEach-Object{(ConvertTo-Json -InputObject ([string]$_) -Compress)+':'+(Canonical-Control $Value[$_])}) -join ',')+'}'
  }
  if($Value -is [Collections.IEnumerable]){return '['+(@($Value|ForEach-Object{Canonical-Control $_}) -join ',')+']'}
  return '{'+(@($Value.PSObject.Properties.Name|Sort-Object -CaseSensitive|ForEach-Object{(ConvertTo-Json -InputObject ([string]$_) -Compress)+':'+(Canonical-Control $Value.$_)}) -join ',')+'}'
}
function Project-Control($Actual){
  # Preserve every report property except process-specific absolute addresses.
  # Address liveness and bank source/replacement identity relations remain.
  function Project-Value($Value,[string]$Name=''){
    if($Name -cin @('identity','baselineOwnerIdentity','returnedOwnerIdentity')){
      if($null -eq $Value){return $null}
      if($Value -isnot [string] -or $Value -cnotmatch '^0x[0-9a-f]+$'){throw 'NATIVE-CONTROLS: malformed object identity'}
      return ($Value -cne '0x0')
    }
    if($null -eq $Value){return $null}
    if($Value -is [string] -or $Value -is [bool] -or $Value -is [ValueType]){return $Value}
    if($Value -is [Collections.IEnumerable]){return ,@($Value|ForEach-Object{Project-Value $_})}
    $out=[ordered]@{}
    foreach($property in $Value.PSObject.Properties){$out[$property.Name]=Project-Value $property.Value $property.Name}
    return $out
  }
  $projected=Project-Value $Actual
  $relations=@()
  foreach($phase in @('beforeCleanup','afterCleanup')){
    for($bank=0;$bank -lt 4;$bank++){
      $source=$Actual.$phase.source[$bank].identity;$replacement=$Actual.$phase.replacement[$bank].identity
      $relations+=@{phase=$phase;bank=$bank;bothPresent=($source -cne '0x0' -and $replacement -cne '0x0');
        sameIdentity=$(if($source -ceq '0x0' -or $replacement -ceq '0x0'){$null}else{$source -ceq $replacement})}
    }
  }
  return [ordered]@{report=$projected;arrayIdentityRelations=$relations}
}
function Assert-ControlDisposition($Actual,$Case,$Expected){
  # The successful C client invokes strict_info directly, and discovery invokes
  # that very function for any live owner. Replay does not invent a weaker clone.
  $a=$Actual;$b=$a.beforeCleanup;$z=$a.afterCleanup
  if($z.cleanupComplete -ne 1 -or $z.nativeHandlesLive -ne 0 -or $z.temporaryArraysLive -ne 0 -or
      $z.nativeHandlesCreated -ne $z.nativeHandlesReleased -or
      $z.temporaryArraysCreated -ne $z.temporaryArraysReleased -or
      $z.initializedEntries -ne $z.releasedEntries -or $z.copyCounterOverflow -ne 0){
    throw ('NATIVE-CONTROLS: resource cleanup/counter predicate differs '+$Case.id)
  }
  $empty=(-not $a.ownerPresent -and -not $a.answerPresent -and -not $a.observationPresent)
  switch -CaseSensitive ($Expected.verdict){
    {$_ -cin @('accept','nondistinguishing')} {
      if($a.actualStatus -ne 0 -or -not $a.ownerPresent -or -not $a.answerPresent -or -not $a.observationPresent -or
          -not $a.liveStrictPredicate -or $a.livePredicateDiagnostic -cne '' -or -not $a.memoryEqual -or
          $a.answerLE -cnotmatch '^02(?:00)*$' -or $b.strictPublication -ne 1 -or $b.valuesEqual -ne 1){
        throw ('NATIVE-CONTROLS: same healthy acceptance predicate differs '+$Case.id)
      }
      if($Case.surface -ceq 'shared-scalar' -and $Expected.verdict -ceq 'accept' -and $b.retainedScalarRoots -ne 1){
        throw 'NATIVE-CONTROLS: shared-scalar acceptance did not retain a boxed scalar; classify nondistinguishing'
      }
    }
    'reject-publication' {
      if($a.actualStatus -ne 10 -or -not $empty -or $b.strictPublication -ne 0){throw ('NATIVE-CONTROLS: publication rejection differs '+$Case.id)}
      $distinguished=switch -CaseSensitive ($Case.surface){
        'skip-repack' {$b.arraysExact -eq 0 -or $b.ownerExclusive -eq 0}
        'extra-owner-alias' {$b.ownerExclusive -eq 0 -and $b.retainedOwnerRoots -gt 0}
        'retain-input' {$b.retainedInputRoots -gt 0}
        'retain-old-arena' {$b.retainedArenaRoots -gt 0}
        'retain-keys' {$b.retainedKeyRoots -gt 0}
        'retain-history' {$b.retainedHistoryRoots -gt 0}
        'wrong-copy-value' {$b.valuesEqual -eq 0 -and $b.firstMismatchArray -eq 1 -and [string]$b.firstMismatchIndex -ceq $Case.argument}
        'wrong-copy-offset' {$b.valuesEqual -eq 0 -and $b.firstMismatchArray -eq 1 -and [string]$b.firstMismatchIndex -ceq $Case.argument}
        default {$false}
      }
      if(-not $distinguished){throw ('NATIVE-CONTROLS: intended state/resource oracle did not distinguish '+$Case.id)}
    }
    'reject-before-transfer' {
      if($Case.phase -cne 'query' -or $a.actualStatus -notin @(1,9) -or -not $a.ownerPresent -or
          -not $a.sameOwnerIdentity -or $a.answerPresent -or $a.observationPresent -or -not $a.memoryEqual -or
          -not $a.liveStrictPredicate -or $a.livePredicateDiagnostic -cne ''){throw ('NATIVE-CONTROLS: pre-transfer owner preservation differs '+$Case.id)}
    }
    'reject-before-build' {
      if($Case.phase -cne 'build' -or $a.actualStatus -notin @(1,2,9) -or -not $empty -or
          $b.initializedEntries -ne 0){throw ('NATIVE-CONTROLS: failed build admission/allocation differs '+$Case.id)}
    }
    'reject-operation' {
      if($a.actualStatus -notin @(7,8,10) -or -not $empty){throw ('NATIVE-CONTROLS: consuming failure did not empty outputs '+$Case.id)}
      if($Case.surface -ceq 'partial-copy' -and ($a.actualStatus -ne 10 -or
          [string]$b.copiedEntries -cne $Case.argument -or $b.initializedEntries -ne $b.releasedEntries)){
        throw ('NATIVE-CONTROLS: partial-copy cutpoint/release differs '+$Case.id)
      }
      if($Case.surface -ceq 'post-take' -and ($Case.phase -cne 'query' -or $a.actualStatus -ne 10)){
        throw 'NATIVE-CONTROLS: post-take failure predicate differs'
      }
      if($Case.surface -ceq 'pre-publication' -and ($a.actualStatus -ne 10 -or $b.strictPublication -ne 1)){
        throw 'NATIVE-CONTROLS: fail-before-publish did not reach strict publication'
      }
      if($Case.surface -cin @('fuel','model-fault') -and ($a.baselineBuilt -or $null -ne $a.baselineInfo -or
          $null -ne $a.baselineMemoryLE -or ($Case.surface -ceq 'fuel' -and $a.actualStatus -ne 8) -or
          ($Case.surface -ceq 'model-fault' -and $a.actualStatus -ne 7))){throw 'NATIVE-CONTROLS: bounded fuel/fault origin differs'}
    }
  }
}
try{
  $mutex=[Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  $locked=$mutex.WaitOne(0);if(-not $locked){throw 'NATIVE-CONTROLS: shared heavy slot busy; no native child launched'}
  # Run the same pinned C executable directly. Inherited noninteractive error
  # mode makes loader/crash errors return their actual exit rather than a dialog.
  if(-not ('LN1ControlErrorMode' -as [type])){
    Add-Type -TypeDefinition @'
using System.Runtime.InteropServices;
public static class LN1ControlErrorMode {
  [DllImport("kernel32.dll")] public static extern uint SetErrorMode(uint mode);
}
'@
  }
  $savedErrorMode=[LN1ControlErrorMode]::SetErrorMode(0x8003)
  $report.childErrorMode=0x8003
  $report.contract=Assert-LN1FrozenContract $root
  $shell=(Get-Process -Id $PID).Path
  foreach($path in @($PSCommandPath,$registryPath,$BuildReceipt,$shell,
      (Join-Path $root 'scripts/lifecycle_native_cases.json'),
      (Join-Path $PSScriptRoot 'CONTRACT_REQUIREMENTS.json'),(Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.frozen.md'),
      (Join-Path $root 'scripts/lifecycle_native_identity.ps1'),(Join-Path $root 'scripts/owned_process_tree.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'))){[void](Pin-Control $path)}
  foreach($pin in @($build.sourcePins)+@($build.generatedPins)+@($build.toolPins)+@($build.artifactPins)){Assert-ControlPin $pin}
  if($build.nativeReceipt){
    Assert-ControlPin $build.nativeReceipt
    $native=[IO.File]::ReadAllText($build.nativeReceipt.path,$utf8)|ConvertFrom-Json
    foreach($pin in @($native.sourcePins)+@($native.generatedPins)+@($native.artifactPins)){Assert-ControlPin $pin}
  }
  $inputRecipe=Get-ControlRecipe @($pins.ToArray())
  $report.inputRecipe=$inputRecipe
  $inputFingerprint=$inputRecipe.sha256
  $report.inputFingerprint=$inputFingerprint
  if($Mode -ceq 'Replay'){
    if(-not (Test-NCExactString $frozen.inputFingerprint $inputFingerprint)){throw 'NATIVE-CONTROLS: reviewed source/tool/artifact/runner recipe changed'}
    [void](Pin-Control $ExpectationsPath)
  }
  # Stage once after verifying every full build pin. Every source must be an
  # exact artifact/tool input of that build; every staged copy is pinned through
  # the finalizer. Ephemeral staging paths do not enter inputFingerprint.
  $directory=Join-Path $run 'native'
  [void][IO.Directory]::CreateDirectory($directory)
  $sourceDirectory=Join-Path $root '.lake/lifecycle-native1/build/testing'
  foreach($name in @('lifecycle-owner.exe','packed_rmq_lifecycle.dll','libInit_shared.dll')){
    $source=if($name -ceq 'libInit_shared.dll'){Join-Path $LeanRoot ('bin/'+$name)}else{Join-Path $sourceDirectory $name}
    $sourcePin=Pin-Control $source
    $known=@(@($build.artifactPins)+@($build.toolPins)|Where-Object{[string]::Equals($_.path,$sourcePin.path,[StringComparison]::OrdinalIgnoreCase)})
    if($known.Count -ne 1 -or $known[0].sha256 -cne $sourcePin.sha256 -or $known[0].bytes -ne $sourcePin.bytes){
      throw ('NATIVE-CONTROLS: staged source not exactly bound by build receipt '+$name)
    }
    $destination=Join-Path $directory $name
    [IO.File]::Copy($source,$destination,$false)
    $copyPin=Pin-Control $destination
    if($copyPin.sha256 -cne $sourcePin.sha256 -or $copyPin.bytes -ne $sourcePin.bytes){throw ('NATIVE-CONTROLS: staged copy differs '+$name)}
    $report.stagedFiles+=@{source=$sourcePin;copy=$copyPin}
  }
  $client=Join-Path $directory 'lifecycle-owner.exe'
  $report.dependencies=Get-LNDependencyClosure @($client) (Join-Path $LeanRoot 'bin')
  Assert-LNDependencyCoverage $report.dependencies @($pins.ToArray())
  foreach($node in $report.dependencies.nodes){
    if(-not [string]::Equals((Split-Path $node.path -Parent),$directory,[StringComparison]::OrdinalIgnoreCase)){
      throw ('NATIVE-CONTROLS: non-system dependency escaped adjacent staging '+$node.path)
    }
  }
  $direct=@($report.dependencies.nodes|Where-Object{[string]::Equals($_.path,$client,[StringComparison]::OrdinalIgnoreCase)})
  if($direct.Count -ne 1){throw 'NATIVE-CONTROLS: missing or duplicate executable dependency node'}
  $custom=@($direct[0].imports|Where-Object{$_ -match '^packed_.*\.dll$'}|ForEach-Object{$_.ToLowerInvariant()}|Sort-Object)
  if(($custom -join '|') -cne 'packed_rmq_lifecycle.dll'){throw 'NATIVE-CONTROLS: direct DLL import roster differs'}
  $env:PATH=$directory+';'+(Join-Path $LeanRoot 'bin')+';'+$savedPath
  [IO.File]::WriteAllText((Join-Path $run 'PLAN.json'),($report|ConvertTo-Json -Depth 30),$utf8)
  foreach($id in $selected){
    $case=@($registry.cases|Where-Object{$_.id -ceq $id})[0]
    $stage=[ordered]@{id=$id;capture=$null;caseReceipt=$null;error=$null}
    try{
      $caseDirectory=Join-Path $run $id
      [void][IO.Directory]::CreateDirectory($caseDirectory)
      $actualPath=Join-Path $caseDirectory 'actual.json'
      $argv=@('--control',$case.control,'--phase',$case.phase,'--argument',$case.argument,'--report',$actualPath)
      # Keep the returned capture even on nonzero exit or unrelated output.
      # The existing owned facility bounds and cleans only this native tree.
      $stage.capture=Invoke-LNStreamCapture $root $client $argv $root (Join-Path $caseDirectory 'capture') $CaseDeadlineSeconds $id
      foreach($raw in $stage.capture.raw){Assert-ControlPin $raw}
      Assert-LNOuterCapture $stage.capture ("LIFE-NATIVE1 CONTROL "+$case.control+' '+$case.phase+" OBSERVED`n") '' 0 $id
      $actualPin=Pin-Control $actualPath
      $actual=[IO.File]::ReadAllText($actualPath,$utf8)|ConvertFrom-Json
      if($actual.schema -cne 'lifecycle-native1-control-discovery-v1' -or $actual.control -cne $case.control -or
          $actual.phase -cne $case.phase -or [string]$actual.argument -cne $case.argument -or
          $actual.acceptanceVerdict -cne 'not-assigned-discovery-only'){
        throw ('NATIVE-CONTROLS: actual control identity differs '+$id)
      }
      if($case.phase -ceq 'build' -and $case.control -cin @('exhausted','model-fault') -and
          ($actual.baselineBuilt -or $null -ne $actual.baselineInfo -or $null -ne $actual.baselineMemoryLE)){
        throw 'NATIVE-CONTROLS: bounded fuel probe unexpectedly built a healthy baseline'
      }
      $projection=Project-Control $actual
      $verdict='UNREVIEWED';$oracle=''
      if($Mode -ceq 'Replay'){
        $expected=@($frozen.cases|Where-Object{$_.id -ceq $id})[0]
        Assert-ControlDisposition $actual $case $expected
        if(-not [string]::Equals((Canonical-Control $projection),(Canonical-Control $expected.projection),[StringComparison]::Ordinal)){
          throw ('NATIVE-CONTROLS: exact reviewed diagnostic/state/resource projection differs '+$id)
        }
        $verdict=$expected.verdict;$oracle=$expected.oracleExplanation
      }
      $receiptPath=Join-Path $caseDirectory 'CONTROL.json'
      $receipt=@{schema='lifecycle-native1-direct-control-v1';success=$true;id=$id;control=$case.control;
        phase=$case.phase;argument=$case.argument;inputFingerprint=$inputFingerprint;actual=$actualPin;
        capture=$stage.capture;verdict=$verdict;acceptanceAssigned=($Mode -ceq 'Replay')}
      [IO.File]::WriteAllText($receiptPath,($receipt|ConvertTo-Json -Depth 40),$utf8)
      $receiptPin=Pin-Control $receiptPath;$stage.caseReceipt=$receiptPin
      $candidates.Add(@{id=$id;control=$case.control;phase=$case.phase;argument=$case.argument;surface=$case.surface;
        verdict=$verdict;oracleExplanation=$oracle;projection=$projection;discoveryReceipt=$receiptPin})
      $results.Add(@{id=$id;verdict=$verdict;acceptanceAssigned=($Mode -ceq 'Replay');capture=$stage.capture;
        caseReceipt=$receiptPin;actual=$actualPin;projectionSHA256=(Get-LN1BytesHash ($utf8.GetBytes((Canonical-Control $projection))))})
    }catch{$stage.error=$_.Exception.Message;throw}finally{$stages.Add($stage)}
  }
  if($results.Count -ne $selected.Count -or (@($results.id) -join '|') -cne ($selected -join '|')){throw 'NATIVE-CONTROLS: executed roster differs'}
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  # Integrity and cleanup each run independently even after partial setup.
  $errors=[Collections.Generic.List[string]]::new()
  foreach($pin in $pins){try{$now=Get-LN1Pin $pin.path;if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256){throw ('changed pin '+$pin.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray());liveSourceWrites=0}
  $cleanupErrors=[Collections.Generic.List[string]]::new()
  $pathRestored=$false;$errorModeRestored=($null -eq $savedErrorMode);$mutexReleased=(-not $locked);$mutexDisposed=($null -eq $mutex)
  # Restore each acquired process resource independently even if another cleanup
  # action fails. Pinned staged files and raw captures deliberately remain.
  try{$env:PATH=$savedPath;$pathRestored=($env:PATH -ceq $savedPath);if(-not $pathRestored){throw 'PATH restoration differs'}}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($null -ne $savedErrorMode){[void][LN1ControlErrorMode]::SetErrorMode($savedErrorMode);$errorModeRestored=$true}}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($locked){$mutex.ReleaseMutex();$mutexReleased=$true}}catch{$cleanupErrors.Add($_.Exception.Message)}
  try{if($null -ne $mutex){$mutex.Dispose();$mutexDisposed=$true}}catch{$cleanupErrors.Add($_.Exception.Message)}
  $incomplete=@($stages|Where-Object{$null -eq $_.capture -or $_.capture.launcher.TimedOut -or $_.capture.launcher.OutputLimitExceeded})
  $report.cleanup=@{success=($cleanupErrors.Count -eq 0 -and $incomplete.Count -eq 0);errors=@($cleanupErrors.ToArray());
    mutexAcquired=$locked;mutexReleased=$mutexReleased;mutexDisposed=$mutexDisposed;
    pathRestored=$pathRestored;errorModeRestored=$errorModeRestored;
    retainedEvidence=$run;incompleteStages=@($incomplete.id);disposableWrites=0}
  $report.success=$report.success -and $report.integrity.success -and $report.cleanup.success
  $report.pins=@($pins.ToArray());$report.results=@($results.ToArray());$report.stages=@($stages.ToArray())
  $report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'EXPECTATIONS.candidate.json'),(@{schema='lifecycle-native1-native-control-expectations-v1';
    status='UNREVIEWED_DISCOVERY';mappingSHA256=$mappingSHA256;inputFingerprint=$inputFingerprint;
    completeRegistry=$report.completeRegistry;cases=@($candidates.ToArray())}|ConvertTo-Json -Depth 60),$utf8)
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 60),$utf8)
}
Write-Output ('NATIVE-CONTROLS evidence='+$run)
if(-not $report.success){Write-Output ('NATIVE-CONTROLS FAIL '+$report.failure);exit 1}
Write-Output ('NATIVE-CONTROLS '+$Mode+' PASS cases='+$results.Count)

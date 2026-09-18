#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase = '',
  [switch]$RegistryOnly,
  [switch]$SelectorProbeOnly,
  [switch]$RuntimeOnly,
  [switch]$DeadlineOnly,
  [switch]$SelectorBoundaryOnly,
  [switch]$DiagnosticOnly,
  [ValidateRange(10,7200)][int]$DeadlineSeconds = 600,
  [string]$LeanPath = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryVersion=3
# This literal list is deliberately independent of the versioned JSON and producers.
$expected=@(
  'O01-wordRoundTrip|OPTIMALITY|wordRoundTrip|REJECT|checkO01',
  'O02-wordSerializationInjective|OPTIMALITY|wordSerializationInjective|REJECT|checkO02',
  'O03-serializedLength|OPTIMALITY|serializedLength|REJECT|checkO03',
  'O04-memoryRecovery|OPTIMALITY|memoryRecovery|REJECT|checkO04',
  'O05-decoderExact|OPTIMALITY|decoderExact|REJECT|checkO05',
  'O06-decoderLeftmost|OPTIMALITY|decoderLeftmost|REJECT|checkO06',
  'O07-sameShapeMemory|OPTIMALITY|sameShapeMemory|REJECT|checkO07',
  'O08-shapeInjectivity|OPTIMALITY|shapeInjectivity|REJECT|checkO08',
  'O09-uniformBudgetCount|OPTIMALITY|uniformBudgetCount|REJECT|checkO09',
  'O10-uniformBudgetLower|OPTIMALITY|uniformBudgetLower|REJECT|checkO10',
  'O11-canonicalCount|OPTIMALITY|canonicalCount|REJECT|checkO11',
  'O12-canonicalLower|OPTIMALITY|canonicalLower|REJECT|checkO12',
  'O13-upperCapacity|OPTIMALITY|upperCapacity|REJECT|checkO13',
  'O14-allocationResidualLittleO|OPTIMALITY|allocationResidualLittleO|REJECT|checkO14',
  'O15-runIdentity|OPTIMALITY|runIdentity|REJECT|checkO15',
  'O16-machine|OPTIMALITY|machine|REJECT|checkO16',
  'M01-allocationResidualLittleO|MACHINE|allocationResidualLittleO|REJECT|checkM01',
  'M02-completeResidualLittleO|MACHINE|completeResidualLittleO|REJECT|checkM02',
  'M03-widthBounds|MACHINE|widthBounds|REJECT|checkM03',
  'M04-dataCapacity|MACHINE|dataCapacity|REJECT|checkM04',
  'M05-completeCapacity|MACHINE|completeCapacity|REJECT|checkM05',
  'M06-memoryWordsFit|MACHINE|memoryWordsFit|REJECT|checkM06',
  'M07-allocationAddressesFit|MACHINE|allocationAddressesFit|REJECT|checkM07',
  'M08-programFieldsFit|MACHINE|programFieldsFit|REJECT|checkM08',
  'M09-budgetExact|MACHINE|budgetExact|REJECT|checkM09',
  'M10-programLength|MACHINE|programLength|REJECT|checkM10',
  'M11-encodedProgramBound|MACHINE|encodedProgramBound|REJECT|checkM11',
  'M12-registerCount|MACHINE|registerCount|REJECT|checkM12',
  'M13-scratchCount|MACHINE|scratchCount|REJECT|checkM13',
  'M14-unusedRegisters|MACHINE|unusedRegisters|REJECT|checkM14',
  'M15-validInputs|MACHINE|validInputs|REJECT|checkM15',
  'M16-natContract|MACHINE|natContract|REJECT|checkM16',
  'M17-leftmost|MACHINE|leftmost|REJECT|checkM17',
  'M18-result|MACHINE|result|REJECT|checkM18',
  'M19-halt|MACHINE|halt|REJECT|checkM19',
  'M20-invalidGuard|MACHINE|invalidGuard|REJECT|checkM20',
  'M21-stepBound|MACHINE|stepBound|REJECT|checkM21',
  'M22-categoryPartition|MACHINE|categoryPartition|REJECT|checkM22',
  'M23-finalStateFit|MACHINE|finalStateFit|REJECT|checkM23',
  'M24-transitionSafety|MACHINE|transitionSafety|REJECT|checkM24',
  'M25-prefixSafety|MACHINE|prefixSafety|REJECT|checkM25',
  'M26-readWidth|MACHINE|readWidth|REJECT|checkM26',
  'M27-positionalReadBacking|MACHINE|positionalReadBacking|REJECT|checkM27',
  'M28-orderedLogicalRefinement|MACHINE|orderedLogicalRefinement|REJECT|checkM28',
  'M29-logicalReadOnly|MACHINE|logicalReadOnly|REJECT|checkM29',
  'M30-suppliedMemoryAgreement|MACHINE|suppliedMemoryAgreement|REJECT|checkM30',
  'M31-specResult|MACHINE|specResult|REJECT|checkM31',
  'M32-noFailedLoads|MACHINE|noFailedLoads|REJECT|checkM32',
  'M33-invalidGuardSteps|MACHINE|invalidGuardSteps|REJECT|checkM33',
  'A01-BASELINE|ACCEPT||ACCEPT|publicContract',
  'P01-PUBLIC-PROPOSITION|PUBLIC||REJECT|publicContract',
  'G01-LOWER-PROPOSITION|GENERIC||REJECT|genericBoundConsumer',
  'G02-DELETED-EXACTNESS|EXACTNESS||REJECT|sameRMQBehavior_of_encode_eq',
  'D01-NULL-DECODER|NULL||REJECT|allocationDecoder_exact',
  'D02-WRONG-DECODER|WRONG||REJECT|allocationDecoder_exact',
  'D03-ZERO-SERIALIZER|ZERO||REJECT|serializeWords_length',
  'F01-DELETE-MEMORY-RECOVERY|DELETE|OPTIMALITY.memoryRecovery|REJECT|checkO04',
  'F02-DELETE-READ-BACKING|DELETE|MACHINE.positionalReadBacking|REJECT|checkM27',
  'S01-SIBLING-MEMORY|SIBLING|memoryRecovery|REJECT|checkO04',
  'S02-SIBLING-RUN|SIBLING|runIdentity|REJECT|checkO15',
  'S03-SIBLING-BUDGET|SIBLING|uniformBudgetCount|REJECT|checkO09',
  'H01-EMPTY-ONLY-DECODER|GUARD|decoderExact|REJECT|checkO05',
  'A02-PROOF-ONLY-WRAPPER|WRAPPER||ACCEPT|publicContract'
)
$runtimeIDs=@('R01-EMPTY','R02-SINGLETON','R03-LEFTMOST','R04-ZERO-LENGTH','R05-ZERO-WORDS','R06-SAME-SHAPE')
function Assert-LB1Registry([object]$registry) {
  if ($registry.version -ne 3 -or $registry.cases.Count -ne 63) { throw 'LB1-REGISTRY version/count mismatch' }
  $actual=@($registry.cases|ForEach-Object{"$($_.id)|$($_.kind)|$($_.field)|$($_.verdict)|$($_.surface)"})
  if (($actual -join "~") -cne ($expected -join "~")) { throw 'LB1-REGISTRY exact case list mismatch' }
  if (($registry.runtime -join "~") -cne ($runtimeIDs -join "~")) { throw 'LB1-REGISTRY exact runtime list mismatch' }
  if (@($registry.cases.id|Select-Object -Unique).Count -ne 63) { throw 'LB1-REGISTRY duplicate ID' }
}
function Select-LB1Cases([object[]]$cases,[bool]$bound,[string]$selector) {
  if (-not $bound) { return $cases }
  if ([string]::IsNullOrWhiteSpace($selector)) { throw 'LB1-SELECTOR empty or whitespace selector' }
  if ($selector -cnotmatch '^[A-Z][0-9]{2}-[A-Za-z][A-Za-z0-9-]*$') { throw 'LB1-SELECTOR malformed selector' }
  $selected=@($cases|Where-Object{$_.id -ceq $selector})
  if ($selected.Count -ne 1) { throw 'LB1-SELECTOR unknown selector' }
  return $selected
}
$registryPath=Join-Path $repo 'docs/internal/extensions/lb1/REPLAY_REGISTRY.json'
$registry=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
Assert-LB1Registry $registry
$selectorBound=$PSBoundParameters.ContainsKey('OnlyCase')
$selectorChannel=[Environment]::GetEnvironmentVariable('LB1_REPLAY_SELECTOR')
if($null -ne $selectorChannel){
  if($selectorBound){throw 'LB1-SELECTOR supplied twice'}
  if(-not $selectorChannel.StartsWith('id:',[StringComparison]::Ordinal)){throw 'LB1-SELECTOR malformed channel'}
  $selectorBound=$true
  $OnlyCase=$selectorChannel.Substring(3)
}
$selected=@(Select-LB1Cases $registry.cases $selectorBound $OnlyCase)
if ($selected.Count -eq 0) { throw 'LB1-SELECTOR selected no cases' }
if ($SelectorProbeOnly) { "LB1-SELECTOR-PASS selected=$($selected.Count) ids=$($selected.id -join ',')"; exit 0 }
if ($RegistryOnly) {
  foreach ($bad in @('', ' ', 'not an id', 'Z99-UNKNOWN')) {
    $rejected=$false
    try { $null=Select-LB1Cases $registry.cases $true $bad } catch {
      if ($_.Exception.Message -notlike 'LB1-SELECTOR*') { throw }
      $rejected=$true
    }
    if (-not $rejected) { throw 'LB1-REGISTRY selector negative control accepted' }
  }
  if (@(Select-LB1Cases $registry.cases $false '').Count -ne 63 -or
      @(Select-LB1Cases $registry.cases $true 'A01-BASELINE').Count -ne 1) {
    throw 'LB1-REGISTRY selector positive controls failed'
  }
  $damaged=[IO.File]::ReadAllText($registryPath,$utf8)|ConvertFrom-Json
  $damaged.cases=@($damaged.cases|Select-Object -Skip 1)
  $rejected=$false
  try { Assert-LB1Registry $damaged } catch {
    if ($_.Exception.Message -notlike 'LB1-REGISTRY*') { throw }; $rejected=$true
  }
  if (-not $rejected) { throw 'LB1-REGISTRY missing case accepted' }
  "LB1-REGISTRY-PASS version=3 cases=63 runtime=6; exact missing-case and selector controls"
  exit 0
}
if (($RuntimeOnly -or $DeadlineOnly -or $SelectorBoundaryOnly -or $DiagnosticOnly) -and $selectorBound) {
  throw 'LB1-SELECTOR focused mutation selection cannot combine with runtime/deadline mode'
}
$runRoot=Join-Path $repo ('.lake/lb1-replay/' + [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($runRoot)
$cache=Join-Path $repo '.lake/build/lib/lean'
$producer='RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean'
$generic='RMQ/Core/EncodingVariableLowerBound.lean'
$consumer='RMQ/Validation/VariablePayloadLowerBound.lean'
$genericConsumer='scripts/variable_payload_generic_consumer.lean'
$stageResults=[Collections.Generic.List[object]]::new()
function Invoke-LB1Stage([string]$file,[string[]]$arguments,[string]$stage,[int]$deadline=$DeadlineSeconds,[hashtable]$environment=@{}) {
  Write-Host "LB1-STAGE $stage"
  $childEnvironment=@{LEAN_PATH=$cache}
  foreach($key in $environment.Keys){$childEnvironment[$key]=$environment[$key]}
  $result=Invoke-RMQOwnedBoundedProcess -FilePath $file -Arguments $arguments -WorkingDirectory $repo -Stage $stage -DeadlineSeconds $deadline -OutputLimitBytes 8388608 -TempRoot $runRoot -Environment $childEnvironment
  $stageResults.Add($result)
  [IO.File]::WriteAllText((Join-Path $runRoot ($stage+'.json')),($result|ConvertTo-Json -Depth 9),$utf8)
  if ($result.TimedOut -or $result.OutputLimitExceeded) { throw "LB1-INCONCLUSIVE resource limit: $stage" }
  return $result
}
function Require-LB1Pass([object]$result) {
  if ($result.ExitCode -ne 0) { throw "LB1-UNEXPECTED-FAIL $($result.Stage): $($result.Output -join ' | ')" }
}
function Invoke-LB1Lean([string]$path,[string]$stage,[bool]$writeArtifact=$false) {
  $arguments=@('-j1')
  if ($writeArtifact) { $arguments+=@('-o',(Join-Path $cache ([IO.Path]::ChangeExtension($path,'.olean')))) }
  $arguments+=@((Join-Path $repo $path))
  return Invoke-LB1Stage $LeanPath $arguments $stage
}
function Get-LB1Declaration([string]$text,[string]$name) {
  $start=[regex]::Matches($text,'(?m)^(?:theorem|def|structure) '+[regex]::Escape($name)+'\b')
  if ($start.Count -ne 1) { throw "LB1-SURFACE declaration not unique: $name" }
  $after=$start[0].Index+$start[0].Length
  $next=[regex]::Match($text.Substring($after),'(?m)^(?:theorem |def |structure |namespace |end |/--)')
  $end=if($next.Success){$after+$next.Index}else{$text.Length}
  return [pscustomobject]@{Start=$start[0].Index;End=$end;Text=$text.Substring($start[0].Index,$end-$start[0].Index)}
}
function Replace-LB1Declaration([string]$text,[string]$name,[string]$replacement) {
  $span=Get-LB1Declaration $text $name
  return $text.Substring(0,$span.Start)+$replacement+[Environment]::NewLine+[Environment]::NewLine+$text.Substring($span.End)
}
function Weaken-LB1Field([string]$text,[string]$kind,[string]$section,[string]$field,[AllowEmptyString()][string]$ReplacementText='', [switch]$Custom) {
  $begin="  -- LB1-$kind-$section-BEGIN"
  $end="  -- LB1-$kind-$section-END"
  $a=$text.IndexOf($begin,[StringComparison]::Ordinal)
  $b=$text.IndexOf($end,[StringComparison]::Ordinal)
  if($a -lt 0 -or $b -le $a -or $text.LastIndexOf($begin,[StringComparison]::Ordinal) -ne $a) { throw 'LB1-MUTATION marker mismatch' }
  $region=$text.Substring($a,$b-$a)
  $pattern=if($section -ceq 'FIELDS'){'(?m)^  ([A-Za-z][A-Za-z0-9]*) :'}else{'(?m)^  ([A-Za-z][A-Za-z0-9]*)(?: [^\r\n]*?)? :='}
  $entries=[regex]::Matches($region,$pattern)
  $target=@($entries|Where-Object{$_.Groups[1].Value -ceq $field})
  if($target.Count -ne 1){throw "LB1-MUTATION field not unique: $field"}
  $next=@($entries|Where-Object{$_.Index -gt $target[0].Index}|Select-Object -First 1)
  $finish=if($next.Count -eq 0){$region.Length}else{$next[0].Index}
  $replacement=if($Custom){$ReplacementText}elseif($section -ceq 'FIELDS'){"  $field : True"}else{"  $field := True.intro"}
  return $text.Substring(0,$a+$target[0].Index)+$replacement+[Environment]::NewLine+$text.Substring($a+$finish)
}
function Require-LB1Rejection([object]$result,[string]$path,[string]$declaration) {
  $joined=$result.Output -join [Environment]::NewLine
  if($result.ExitCode -eq 0 -or $joined -match '(?i)maximum recursion|maximum number of heartbeats|out of memory|stack overflow|unknown module|object file.*does not exist') {
    throw "LB1-REJECTION incorrect verdict/resource failure at $declaration"
  }
  $text=[IO.File]::ReadAllText((Join-Path $repo $path),$utf8)
  $span=Get-LB1Declaration $text $declaration
  $first=1+([regex]::Matches($text.Substring(0,$span.Start),'\n')).Count
  if($span.End -le $span.Start){throw 'LB1-REJECTION empty declaration span'}
  $last=1+([regex]::Matches($text.Substring(0,$span.End-1),'\n')).Count
  $filename=[IO.Path]::GetFileName($path)
  $errors=[regex]::Matches($joined,[regex]::Escape($filename)+':([0-9]+):[0-9]+: error:')
  $hits=@($errors|Where-Object{[int]$_.Groups[1].Value -ge $first -and [int]$_.Groups[1].Value -le $last})
  if($hits.Count -eq 0){throw "LB1-REJECTION no exact diagnostic in $declaration [$first,$last]: $joined"}
}
function Assert-LB1DiagnosticBoundary {
  $fixture=Join-Path $runRoot 'diagnostic-boundary.lean'
  $body=@('theorem target : True := by','  trivial','','theorem adjacent : True := by','  trivial') -join [Environment]::NewLine
  [IO.File]::WriteAllText($fixture,$body,$utf8)
  $relative=[IO.Path]::GetRelativePath($repo,$fixture)
  $inside=[pscustomobject]@{ExitCode=1;Output=@('diagnostic-boundary.lean:1:0: error: type mismatch')}
  Require-LB1Rejection $inside $relative 'target'
  $adjacent=[pscustomobject]@{ExitCode=1;Output=@('diagnostic-boundary.lean:4:0: error: type mismatch')}
  $rejected=$false
  try{Require-LB1Rejection $adjacent $relative 'target'}catch{
    if($_.Exception.Message -notlike 'LB1-REJECTION no exact diagnostic*'){throw}
    $rejected=$true
  }
  if(-not $rejected){throw 'LB1-REJECTION adjacent declaration bypass accepted'}
  Write-Host 'LB1-DIAGNOSTIC-BOUNDARY-PASS expected=2 executed=2'
}
if($DiagnosticOnly){Assert-LB1DiagnosticBoundary;exit 0}
function Run-LB1Runtime {
  Remove-Item -LiteralPath Env:LB1_RUNTIME_SELECTOR -ErrorAction SilentlyContinue
  # Bounded startup and one known selector precede the full runtime registry.
  $list=Invoke-LB1Stage $LeanPath @('-j1','--run',(Join-Path $repo $consumer),'--list') 'runtime-startup'
  Require-LB1Pass $list
  $listed=@($list.StandardOutput|Where-Object{$_ -match '^R[0-9]{2}-'})
  if(($listed -join '~') -cne ($runtimeIDs -join '~')){throw 'LB1-RUNTIME startup registry mismatch'}
  Require-LB1Pass (Invoke-LB1Stage $LeanPath @('-j1','--run',(Join-Path $repo $consumer),'--case','R04-ZERO-LENGTH') 'runtime-known-selector')
  foreach($boundary in @(
    [pscustomobject]@{Name='empty';Value='case:'},
    [pscustomobject]@{Name='whitespace';Value='case: '},
    [pscustomobject]@{Name='malformed';Value='invalid'},
    [pscustomobject]@{Name='unknown';Value='case:R99-UNKNOWN'}
  )){
    $bad=Invoke-LB1Stage $LeanPath @('-j1','--run',(Join-Path $repo $consumer)) ('runtime-selector-'+$boundary.Name) $DeadlineSeconds @{LB1_RUNTIME_SELECTOR=$boundary.Value}
    $out=$bad.Output -join [Environment]::NewLine
    if($bad.ExitCode -eq 0 -or $out -notmatch 'LB1-RUNTIME.*selector' -or $out -match 'LB1-RUNTIME CASE PASS'){throw "LB1-RUNTIME selector boundary $($boundary.Name) unproved"}
  }
  $full=Invoke-LB1Stage $LeanPath @('-j1','--run',(Join-Path $repo $consumer)) 'runtime-full'
  Require-LB1Pass $full
  $out=$full.Output -join [Environment]::NewLine
  $executed=@([regex]::Matches($out,'(?m)^LB1-RUNTIME CASE PASS (R[0-9]{2}-[A-Z-]+)')|ForEach-Object{$_.Groups[1].Value})
  if(($executed -join '~') -cne ($runtimeIDs -join '~')){throw 'LB1-RUNTIME executed/expected registry mismatch'}
}
if($SelectorBoundaryOnly){
  $shell=(Get-Process -Id $PID).Path
  $self=Join-Path $repo 'scripts/variable_payload_replay.ps1'
  Remove-Item -LiteralPath Env:LB1_REPLAY_SELECTOR -ErrorAction SilentlyContinue
  foreach($boundary in @(
    [pscustomobject]@{Name='omitted';Value=$null;Count=63},
    [pscustomobject]@{Name='valid';Value='id:A01-BASELINE';Count=1},
    [pscustomobject]@{Name='empty';Value='id:';Count=0},
    [pscustomobject]@{Name='whitespace';Value='id: ';Count=0},
    [pscustomobject]@{Name='malformed';Value='bad';Count=0},
    [pscustomobject]@{Name='unknown';Value='id:Z99-UNKNOWN';Count=0}
  )){
    $envMap=@{}
    if($null -ne $boundary.Value){$envMap.LB1_REPLAY_SELECTOR=$boundary.Value}
    $result=Invoke-LB1Stage $shell @('-NoProfile','-File',$self,'-SelectorProbeOnly') ('selector-'+$boundary.Name) 60 $envMap
    $out=$result.Output -join [Environment]::NewLine
    if($boundary.Count -gt 0){
      Require-LB1Pass $result
      if($out -notmatch ('LB1-SELECTOR-PASS selected='+$boundary.Count+' ')){throw 'LB1-SELECTOR boundary selected wrong count'}
    }elseif($result.ExitCode -eq 0 -or $out -notmatch 'LB1-SELECTOR' -or $out -match 'LB1-SELECTOR-PASS'){
      throw "LB1-SELECTOR boundary failed: $($boundary.Name)"
    }
  }
  "LB1-SELECTOR-BOUNDARIES-PASS expected=6 executed=6 evidence=$runRoot"
  exit 0
}
if($DeadlineOnly){
  Invoke-RMQOwnedProcessDeterministicTests
  $shell=(Get-Process -Id $PID).Path
  $pidFile=Join-Path $runRoot 'descendant.pid'
  $fixture=Join-Path $runRoot 'deadline-fixture.ps1'
  $escapedShell=$shell.Replace("'","''")
  $escapedPid=$pidFile.Replace("'","''")
  $body='$o=@{FilePath='+"'$escapedShell'"+';ArgumentList=@(''-NoProfile'',''-Command'',''Start-Sleep -Seconds 120'');PassThru=$true}; if($env:OS -eq ''Windows_NT''){$o.WindowStyle=''Hidden''}; $p=Start-Process @o; [IO.File]::WriteAllText('+"'$escapedPid'"+',[string]$p.Id); Start-Sleep -Seconds 120'
  [IO.File]::WriteAllText($fixture,$body,$utf8)
  # The first 10-second probe expired during this host's two-shell startup,
  # before a descendant PID was recorded. Keep that run inconclusive; use a
  # 30-second ownership probe to allow the measured startup margin.
  $result=Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments @('-NoProfile','-File',$fixture) -WorkingDirectory $repo -Stage 'deadline-descendant' -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $runRoot
  [IO.File]::WriteAllText((Join-Path $runRoot 'deadline-result.json'),($result|ConvertTo-Json -Depth 8),$utf8)
  if(-not $result.TimedOut -or -not (Test-Path -LiteralPath $pidFile)){throw 'LB1-DEADLINE INCONCLUSIVE: owned descendant condition not produced'}
  $child=[int][IO.File]::ReadAllText($pidFile)
  if($null -ne (Get-Process -Id $child -ErrorAction SilentlyContinue)){throw 'LB1-DEADLINE owned descendant survived'}
  "LB1-DEADLINE-PASS child=$child evidence=$runRoot; POSIX branch uncovered on Windows"
  exit 0
}
if($RuntimeOnly){Run-LB1Runtime; "LB1-RUNTIME-PASS expected=6 executed=6 evidence=$runRoot";exit 0}
$git=Resolve-RMQScalarApplicationPath (Get-Command git -CommandType Application) 'git'
function Assert-LB1Clean([string]$stage){
  $state=Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $git -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $runRoot -StagePrefix $stage
  Assert-RMQCleanRepositoryStateText $state $stage
}
Assert-LB1Clean 'baseline'
$head=@(Invoke-RMQCheckedGit $git $repo @('rev-parse','HEAD') 'lb1-candidate-head' 30 1048576 $runRoot)[0]
[IO.File]::WriteAllText((Join-Path $runRoot 'candidate.txt'),$head,$utf8)
# Establish the actual current producers before inspecting their metadata or
# running clients. A clean source tree alone does not make cached oleans fresh.
Require-LB1Pass (Invoke-LB1Lean $generic 'baseline-generic-producer' $true)
Require-LB1Pass (Invoke-LB1Lean $producer 'baseline-packed-producer' $true)
Require-LB1Pass (Invoke-LB1Lean 'scripts/variable_payload_inventory.lean' 'baseline-inventory')
Require-LB1Pass (Invoke-LB1Lean $consumer 'baseline-consumer' $true)
Require-LB1Pass (Invoke-LB1Lean $genericConsumer 'baseline-generic-consumer')
$sourceBackups=@{}
$artifactBackups=@{}
foreach($path in @($producer,$generic)){
  $sourceBackups[$path]=[IO.File]::ReadAllBytes((Join-Path $repo $path))
  $artifact=Join-Path $cache ([IO.Path]::ChangeExtension($path,'.olean'))
  if(-not (Test-Path -LiteralPath $artifact)){throw "LB1-BASELINE missing artifact: $artifact"}
  $artifactBackups[$artifact]=[IO.File]::ReadAllBytes($artifact)
}
function Restore-LB1Bytes {
  foreach($path in $sourceBackups.Keys){[IO.File]::WriteAllBytes((Join-Path $repo $path),$sourceBackups[$path])}
  foreach($path in $artifactBackups.Keys){[IO.File]::WriteAllBytes($path,$artifactBackups[$path])}
  foreach($path in $sourceBackups.Keys){
    $actual=[IO.File]::ReadAllBytes((Join-Path $repo $path))
    if([Convert]::ToBase64String($actual) -cne [Convert]::ToBase64String($sourceBackups[$path])){throw 'LB1-RESTORE source bytes differ'}
  }
  foreach($path in $artifactBackups.Keys){
    if([Convert]::ToBase64String([IO.File]::ReadAllBytes($path)) -cne [Convert]::ToBase64String($artifactBackups[$path])){throw 'LB1-RESTORE artifact bytes differ'}
  }
}
$executed=[Collections.Generic.List[string]]::new()
Assert-LB1DiagnosticBoundary
if(-not $selectorBound){Run-LB1Runtime}
try {
  foreach($case in $selected){
    try {
      if($case.kind -ceq 'ACCEPT'){Require-LB1Pass (Invoke-LB1Lean $consumer $case.id)}
      elseif($case.kind -ceq 'WRAPPER'){
        # An extra proof-only wrapper is intentionally outside the public
        # certificate; acceptance must survive a harmless source/artifact edit.
        $addition=@'

private structure LB1ReplayNonLoadBearingPacket : Prop where
  capstone : RMQ.SuccinctFinal.PackedWordRAM.PackedAllocationOptimality
  note : True

private theorem lb1ReplayNonLoadBearingPacket_holds :
    LB1ReplayNonLoadBearingPacket :=
  ⟨RMQ.SuccinctFinal.PackedWordRAM.packedAllocationOptimality_holds, True.intro⟩
'@
        $text=$utf8.GetString($sourceBackups[$producer])+[Environment]::NewLine+$addition+[Environment]::NewLine
        [IO.File]::WriteAllText((Join-Path $repo $producer),$text,$utf8)
        Require-LB1Pass (Invoke-LB1Lean $producer ($case.id+'-producer') $true)
        Require-LB1Pass (Invoke-LB1Lean 'scripts/variable_payload_inventory.lean' ($case.id+'-inventory'))
        Require-LB1Pass (Invoke-LB1Lean $consumer ($case.id+'-consumer'))
      }
      elseif($case.kind -in @('OPTIMALITY','MACHINE')){
        $text=$utf8.GetString($sourceBackups[$producer])
        $text=Weaken-LB1Field $text $case.kind 'FIELDS' $case.field
        $text=Weaken-LB1Field $text $case.kind 'INITIALIZERS' $case.field
        [IO.File]::WriteAllText((Join-Path $repo $producer),$text,$utf8)
        Require-LB1Pass (Invoke-LB1Lean $producer ($case.id+'-producer') $true)
        Require-LB1Rejection (Invoke-LB1Lean $consumer ($case.id+'-consumer')) $consumer $case.surface
      }
      elseif($case.kind -ceq 'PUBLIC'){
        $text=Replace-LB1Declaration ($utf8.GetString($sourceBackups[$producer])) 'packedAllocationOptimality_holds' 'theorem packedAllocationOptimality_holds : True := True.intro'
        [IO.File]::WriteAllText((Join-Path $repo $producer),$text,$utf8)
        Require-LB1Pass (Invoke-LB1Lean $producer ($case.id+'-producer') $true)
        Require-LB1Rejection (Invoke-LB1Lean $consumer ($case.id+'-consumer')) $consumer $case.surface
      }
      elseif($case.kind -in @('DELETE','SIBLING','GUARD')){
        $text=$utf8.GetString($sourceBackups[$producer])
        $group='OPTIMALITY'
        $field=$case.field
        if($case.kind -ceq 'DELETE'){
          $parts=$field.Split('.')
          $group=$parts[0];$field=$parts[1]
          $proposition='';$initializer=''
        }elseif($field -ceq 'memoryRecovery'){
          $proposition='  memoryRecovery : ∀ xs : List Int, reconstructedMemory xs = reconstructedMemory xs'
          $initializer='  memoryRecovery := by intro xs; rfl'
        }elseif($field -ceq 'runIdentity'){
          $proposition='  runIdentity : ∀ (xs : List Int) left right fuel, run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right) = run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right)'
          $initializer='  runIdentity := by intros; rfl'
        }elseif($field -ceq 'uniformBudgetCount'){
          $proposition='  uniformBudgetCount : ∀ n B, UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1'
          $initializer='  uniformBudgetCount := by intro n B budget; exact canonicalAllocation_shapeCount_le n'
        }elseif($field -ceq 'decoderExact'){
          $proposition='  decoderExact : ∀ (xs : List Int), xs.length = 0 → ∀ left right, allocationDecoder xs.length (allocationBits xs) left right = if ValidRange xs left right then some (scanWindow xs left (right - left)) else none'
          $initializer='  decoderExact := by intro xs hsize left right; exact allocationDecoder_exact xs left right'
        }else{throw 'LB1-MUTATION unknown sibling/domain case'}
        $text=Weaken-LB1Field $text $group 'FIELDS' $field $proposition -Custom
        $text=Weaken-LB1Field $text $group 'INITIALIZERS' $field $initializer -Custom
        [IO.File]::WriteAllText((Join-Path $repo $producer),$text,$utf8)
        Require-LB1Pass (Invoke-LB1Lean $producer ($case.id+'-producer') $true)
        Require-LB1Rejection (Invoke-LB1Lean $consumer ($case.id+'-consumer')) $consumer $case.surface
      }
      elseif($case.kind -ceq 'GENERIC'){
        $text=Replace-LB1Declaration ($utf8.GetString($sourceBackups[$generic])) 'doubledLogSlackLower_le' 'theorem doubledLogSlackLower_le (E : ExactRMQBoundedEncoding n B) : True := True.intro'
        [IO.File]::WriteAllText((Join-Path $repo $generic),$text,$utf8)
        Require-LB1Pass (Invoke-LB1Lean $generic ($case.id+'-producer') $true)
        Require-LB1Rejection (Invoke-LB1Lean $genericConsumer ($case.id+'-consumer')) $genericConsumer $case.surface
      }
      elseif($case.kind -ceq 'EXACTNESS'){
        $text=$utf8.GetString($sourceBackups[$generic])
        $pattern='(?ms)^  query_exact :(?![=]).*?(?=^\s*$)'
        if([regex]::Matches($text,$pattern).Count -ne 1){throw 'LB1-MUTATION exactness field not unique'}
        $text=[regex]::Replace($text,$pattern,'')
        [IO.File]::WriteAllText((Join-Path $repo $generic),$text,$utf8)
        Require-LB1Rejection (Invoke-LB1Lean $generic ($case.id+'-producer')) $generic $case.surface
      }
      else {
        $text=$utf8.GetString($sourceBackups[$producer])
        if($case.kind -ceq 'ZERO'){
          $text=Replace-LB1Declaration $text 'serializeWords' 'def serializeWords (width : Nat) (words : List Nat) : List Bool := []'
        } else {
          $answer=if($case.kind -ceq 'NULL'){'none'}else{'some 0'}
          $text=Replace-LB1Declaration $text 'allocationDecoder' ("def allocationDecoder (n : Nat) (bits : List Bool) (left right : Nat) : Option Nat := "+$answer)
        }
        [IO.File]::WriteAllText((Join-Path $repo $producer),$text,$utf8)
        Require-LB1Rejection (Invoke-LB1Lean $producer ($case.id+'-producer')) $producer $case.surface
      }
      $executed.Add($case.id)
      Write-Host "LB1-REPLAY CASE $($case.id) PASS expected=$($case.verdict)"
    } finally { Restore-LB1Bytes; Assert-LB1Clean ('restored-'+$case.id) }
  }
  if(($executed -join '~') -cne ($selected.id -join '~')){throw 'LB1-REPLAY executed/expected mismatch'}
} finally { Restore-LB1Bytes; Assert-LB1Clean 'final-restoration' }
$summary=[ordered]@{Version=3;Commit=$head;Expected=@($selected.id);Executed=@($executed);Stages=$stageResults;SourceRestored=$true;ArtifactsRestored=$true;CleanTree=$true}
[IO.File]::WriteAllText((Join-Path $runRoot 'summary.json'),($summary|ConvertTo-Json -Depth 12),$utf8)
"LB1-REPLAY-PASS expected=$($selected.Count) executed=$($executed.Count) evidence=$runRoot"

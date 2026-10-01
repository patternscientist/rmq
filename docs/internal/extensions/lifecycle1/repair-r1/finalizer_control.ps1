#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][AllowEmptyString()][string]$Case,
  [Parameter(Mandatory=$true)][string]$Shell,
  [Parameter(Mandatory=$true)][string]$EvidenceRoot,
  [Parameter(Mandatory=$true)][string]$RepositoryRoot,
  [ValidateSet('old','repaired')][string]$SourceVariant
)

Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$base='12bd7f0fc2c87f2c9bdef3825bd92477e48e3433'
$productionRelative='scripts/lifecycle_dependency_replay.ps1'
$expectedIds=@('F00_OLD_CHANGED_PIN','F01_INTACT_SUCCESS','F02_STAGE_FAILURE',
  'F03_STAGE_AND_PIN_FAILURE','F04_SUCCESS_AND_PIN_FAILURE','F05_PARTIAL_CAPTURE_FAILURE',
  'F06_PARTIAL_CAPTURE_CHANGED','F07_EMPTY_BASELINE','F08_OUTSIDE_EVIDENCE',
  'F09_WRONG_BASENAME','F10_LOCKED_CLEANUP','F11_PIN_AND_LOCKED_CLEANUP')
$registryHash='1303ecf93c0a0c74e0a48023fe52258b7e847d020d009eb2f4deba7f084ab6df'
$helperHash='6690ad4f9e3aee9596e53e89d3d242e4be59c0a04733bc50184ae35b292ff90e'
$childSeconds=30
$outputBytes=1048576

function Hash-ControlBytes([byte[]]$bytes) {
  $algorithm=[Security.Cryptography.SHA256]::Create()
  try {return ([BitConverter]::ToString($algorithm.ComputeHash($bytes))).Replace('-','').ToLowerInvariant()}
  finally {$algorithm.Dispose()}
}
function Hash-ControlFile([string]$path) {return Hash-ControlBytes ([IO.File]::ReadAllBytes($path))}
function Write-ControlJson([string]$path,[object]$value) {
  [IO.File]::WriteAllText($path,($value|ConvertTo-Json -Depth 40),$utf8)
}
function Assert-Control([bool]$condition,[string]$message) {
  if(-not $condition){throw ('L1R1-FINALIZER: '+$message)}
}
function Assert-OwnedDescendant([string]$path,[string]$parent) {
  $full=[IO.Path]::GetFullPath($path)
  $prefix=[IO.Path]::GetFullPath($parent).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
  Assert-Control ($full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase)) ('owned fixture escaped: '+$full)
  return $full
}
function Save-ProcessReceipt([string]$directory,[object]$result) {
  Write-ControlJson (Join-Path $directory 'process.json') $result
  [IO.File]::WriteAllText((Join-Path $directory 'stdout.returned-lines.txt'),(@($result.StandardOutput)-join [char]10),$utf8)
  [IO.File]::WriteAllText((Join-Path $directory 'stderr.returned-lines.txt'),(@($result.StandardError)-join [char]10),$utf8)
}
function Assert-ExactLines([object[]]$actual,[object[]]$expected,[string]$channel) {
  Assert-Control ($actual.Count -eq $expected.Count) ($channel+' exact line count differs')
  for($i=0;$i -lt $actual.Count;$i++){
    Assert-Control ([string]$actual[$i] -ceq [string]$expected[$i]) ($channel+' unexpected line '+$i+': '+$actual[$i])
  }
}

$root=[IO.Path]::GetFullPath($RepositoryRoot)
$shellPath=(Resolve-Path -LiteralPath $Shell -ErrorAction Stop).Path
$registryPath=Join-Path $PSScriptRoot 'finalizer_cases.json'
$registryBytes=[IO.File]::ReadAllBytes($registryPath)
$registry=$utf8.GetString($registryBytes)|ConvertFrom-Json
Assert-Control ((Hash-ControlBytes $registryBytes) -ceq $registryHash) 'frozen registry bytes differ'
Assert-Control ($registry.version -eq 1 -and @($registry.cases).Count -eq $expectedIds.Count) 'exact registry count differs'
for($i=0;$i -lt $expectedIds.Count;$i++){
  Assert-Control ($registry.cases[$i].id -ceq $expectedIds[$i]) 'missing, duplicate, unknown or reordered registry ID'
}
$selected=@($registry.cases|Where-Object {$_.id -ceq $Case})
Assert-Control (-not [string]::IsNullOrWhiteSpace($Case) -and $selected.Count -eq 1) 'one exact known Case is required'
$test=$selected[0]
if($PSBoundParameters.ContainsKey('SourceVariant')){
  Assert-Control ($SourceVariant -ceq $test.sourceVariant) 'source variant differs from frozen case mapping'
}else{$SourceVariant=$test.sourceVariant}
$helper=Join-Path $root 'scripts/owned_process_tree.ps1'
$production=Join-Path $root $productionRelative
$evidenceParent=Assert-OwnedDescendant $EvidenceRoot (Join-Path $root '.lake')
[void][IO.Directory]::CreateDirectory($evidenceParent)
$run=Join-Path $evidenceParent ($Case+'-'+[Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($run)
# LIFE-1-R3: once the owned run directory exists, every exit path writes
# result.json. The control error, each independent entry-pin comparison and each
# cleanup error are recorded separately, and none of them can replace another.
$sourceIdentity=$null;$childPath=$null;$workingProductionHash=$null
$pairRecords=[Collections.Generic.List[object]]::new()
$overallPassed=$false
$controlError=$null;$controlRecord=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$cleanupErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$entryPins=[ordered]@{}
$durableFailed=$false
$pinLabels=[ordered]@{}
$pinLabels[$registryPath]='frozen registry';$entryPins[$registryPath]=Hash-ControlBytes $registryBytes
$pinLabels[$PSCommandPath]='harness';$pinLabels[$helper]='protected helper';$pinLabels[$production]='production script'
try {
$entryPins[$PSCommandPath]=Hash-ControlFile $PSCommandPath
$entryPins[$helper]=Hash-ControlFile $helper
Assert-Control ($entryPins[$helper] -ceq $helperHash) 'protected owned-process helper hash differs'
. $helper
$sourceSnapshot=Join-Path $run 'production.source.ps1'
$workingProductionHash=Hash-ControlFile $production
$entryPins[$production]=$workingProductionHash
if($SourceVariant -ceq 'repaired'){
  [IO.File]::WriteAllBytes($sourceSnapshot,[IO.File]::ReadAllBytes($production))
}else{
  # A bounded shell owns git as its descendant; BaseStream preserves exact Git blob bytes.
  $export=Join-Path $run 'export-source.ps1'
  $gitPath=(Get-Command git -CommandType Application -ErrorAction Stop|Select-Object -First 1).Source
  $exportText=@'
param([string]$Git,[string]$Root,[string]$Destination,[string]$Object)
$ErrorActionPreference='Stop'
$p=[Diagnostics.Process]::new()
$p.StartInfo.FileName=$Git
$p.StartInfo.Arguments='cat-file blob '+$Object
$p.StartInfo.WorkingDirectory=$Root
$p.StartInfo.UseShellExecute=$false
$p.StartInfo.CreateNoWindow=$true
$p.StartInfo.RedirectStandardOutput=$true
$p.StartInfo.RedirectStandardError=$true
$f=$null
try {
  if(-not $p.Start()){throw 'git source export did not start'}
  $f=[IO.File]::Create($Destination)
  $p.StandardOutput.BaseStream.CopyTo($f)
  $f.Dispose();$f=$null
  $errorText=$p.StandardError.ReadToEnd()
  $p.WaitForExit()
  if($p.ExitCode -ne 0 -or $errorText.Length -ne 0){throw ('git source export: '+$errorText)}
}finally{if($null -ne $f){$f.Dispose()};$p.Dispose()}
'@
  [IO.File]::WriteAllText($export,$exportText,$utf8)
  $exportArguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$export,
    '-Git',$gitPath,'-Root',$root,'-Destination',$sourceSnapshot,'-Object',($base+':'+$productionRelative))
  $exportResult=Invoke-RMQOwnedBoundedProcess -FilePath $shellPath -Arguments $exportArguments -WorkingDirectory $root -Stage 'finalizer-old-source-export' -DeadlineSeconds $childSeconds -OutputLimitBytes $outputBytes -TempRoot (Join-Path $run 'export-process')
  [void][IO.Directory]::CreateDirectory((Join-Path $run 'export-receipt'))
  Save-ProcessReceipt (Join-Path $run 'export-receipt') $exportResult
  Assert-Control (-not $exportResult.TimedOut -and -not $exportResult.OutputLimitExceeded -and $exportResult.ExitCode -eq 0) 'old exact Git blob export failed'
  Assert-ExactLines @($exportResult.StandardOutput) @() 'old-source stdout'
  Assert-ExactLines @($exportResult.StandardError) @() 'old-source stderr'
}
$sourceBytes=[IO.File]::ReadAllBytes($sourceSnapshot)
$sourceText=$utf8.GetString($sourceBytes)
$tokens=$null;$parseErrors=$null
$ast=[Management.Automation.Language.Parser]::ParseInput($sourceText,[ref]$tokens,[ref]$parseErrors)
Assert-Control (@($parseErrors).Count -eq 0) 'production source parse failed'
$sourcePieces=[Collections.Generic.List[object]]::new()
$definitions=[Collections.Generic.List[string]]::new()
function Save-ExactPiece([string]$name,[int]$start,[int]$end) {
  $piece=$sourceText.Substring($start,$end-$start)
  $bytes=$utf8.GetBytes($piece)
  $byteStart=$utf8.GetByteCount($sourceText.Substring(0,$start))
  $actual=New-Object byte[] $bytes.Length
  [Array]::Copy($sourceBytes,$byteStart,$actual,0,$actual.Length)
  Assert-Control ([Convert]::ToBase64String($actual) -ceq [Convert]::ToBase64String($bytes)) ('AST/raw source-byte mismatch: '+$name)
  $path=Join-Path $run ($name+'.source.ps1')
  [IO.File]::WriteAllBytes($path,$bytes)
  $sourcePieces.Add([ordered]@{name=$name;path=$path;startCharacter=$start;endCharacter=$end;startByte=$byteStart;byteLength=$bytes.Length;sha256=(Hash-ControlBytes $bytes)})
  return $piece
}
foreach($name in @('Hash-Bytes','Hash-File','Write-Json','Assert-Restored','Remove-Shadow')){
  $matches=@($ast.EndBlock.Statements|Where-Object {$_ -is [Management.Automation.Language.FunctionDefinitionAst] -and $_.Name -ceq $name})
  Assert-Control ($matches.Count -eq 1) ('production function not unique: '+$name)
  $definitions.Add((Save-ExactPiece $name $matches[0].Extent.StartOffset $matches[0].Extent.EndOffset))
}
$tries=@($ast.EndBlock.Statements|Where-Object {$_ -is [Management.Automation.Language.TryStatementAst]})
Assert-Control ($tries.Count -eq 1 -and @($tries[0].CatchClauses).Count -eq 1 -and $null -ne $tries[0].Finally) 'main catch/finally shape differs'
$main=$tries[0]
$catchFinally=Save-ExactPiece 'main-catch-finally' $main.CatchClauses[0].Extent.StartOffset $main.Extent.EndOffset
$terminal=Save-ExactPiece 'post-try-terminal' $main.Extent.EndOffset $sourceText.Length
$finallyText=Save-ExactPiece 'finally' $main.Finally.Extent.StartOffset $main.Finally.Extent.EndOffset
$commands=@($main.Finally.FindAll({param($n) $n -is [Management.Automation.Language.CommandAst]},$true)|ForEach-Object {$_.GetCommandName()})
Assert-Control (@($commands|Where-Object {$_ -ceq 'Assert-Restored'}).Count -eq 1 -and @($commands|Where-Object {$_ -ceq 'Remove-Shadow'}).Count -eq 1) 'exact production integrity/cleanup call chain differs'
$sourceIdentity=[ordered]@{
  sourceVariant=$SourceVariant;base=$base;productionPath=$productionRelative
  sourceSha256=(Hash-ControlBytes $sourceBytes);sourceByteLength=$sourceBytes.Length
  workingProductionSha256=$workingProductionHash;helperSha256=(Hash-ControlFile $helper)
  registrySha256=$registryHash;harnessSha256=(Hash-ControlFile $PSCommandPath)
  shell=$shellPath;shellSha256=(Hash-ControlFile $shellPath);pieces=@($sourcePieces.ToArray())
  chain='main try fixture -> exact catch -> exact finally -> Assert-Restored -> Hash-File -> Hash-Bytes; independent/old coupled Remove-Shadow -> guarded Remove-Item; exact mutex release/dispose; exact summary and terminal exit/PASS'
  scope='Source-derived finalizer component with real bounded process and real owned scratch files; full production compiler replay is separate evidence'
  streams='Inherited helper returned nonblank lines, not original raw stream bytes; helper may throw before returning overflow/cleanup output'
}
Write-ControlJson (Join-Path $run 'source-identity.json') $sourceIdentity

# Only the main try's producer body is injected. Every predicate and the complete
# production error/finalization/verdict route below it retain exact source bytes.
$prelude=@'
param([string]$Configuration)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$cfg=[IO.File]::ReadAllText($Configuration,$utf8)|ConvertFrom-Json
$evidence=$cfg.productionEvidence
$shadow=$cfg.shadow
$registryHash=$cfg.productionRegistryHash
$selected=@([pscustomobject]@{id='D20_ACCEPT_IDENTITY'})
$results=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$baseline=@()
$completed=$false
$restored=$false
$stageError=$null
$integrityError=$null
$cleanupError=$null
$mutex=$null
$locked=$false
$lockStream=$null
$lockAcquired=$false
$enteredMain=$false
'@
$fixtureBody=@'
  $enteredMain=$true
  $baseline=@([pscustomobject]@{path=$cfg.pin;sha256=(Hash-File $cfg.pin)})
  if($cfg.mode -cnotin @('partial','partial-and-pin','empty')){
    $baseline+=@([pscustomobject]@{path=$cfg.pin2;sha256=(Hash-File $cfg.pin2)})
  }
  if($cfg.mode -ceq 'empty'){$baseline=@()}
  if($cfg.mode -cin @('stage-and-pin','success-and-pin','partial-and-pin','pin-and-locked')){
    [IO.File]::WriteAllText($cfg.pin,'changed captured fixture',$utf8)
  }
  if($cfg.mode -cin @('locked','pin-and-locked')){
    $lockStream=[IO.File]::Open($cfg.lockFile,[IO.FileMode]::Open,[IO.FileAccess]::ReadWrite,[IO.FileShare]::None)
    $lockAcquired=$true
  }
  Write-Json 'fixture-entry.json' @{baseline=$baseline;mode=$cfg.mode;pid=$PID;lockAcquired=$lockAcquired;enteredMain=$enteredMain}
  if($cfg.mode -cin @('partial','partial-and-pin')){throw 'L1R1-FIXTURE: capture-stage failure after one pin'}
  if($cfg.mode -cin @('stage','stage-and-pin')){throw 'L1R1-FIXTURE: prior stage failure'}
  $completed=$true
'@
$outerStart=@'
[IO.File]::WriteAllText($cfg.pidPath,[string]$PID,$utf8)
Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
public static class L1R1ParentProcess {
  [StructLayout(LayoutKind.Sequential)]
  private struct BasicInfo {
    public IntPtr Reserved1, PebBase, Reserved2a, Reserved2b, UniquePid, ParentPid;
  }
  [DllImport("ntdll.dll")]
  private static extern int NtQueryInformationProcess(IntPtr process, int kind,
    out BasicInfo info, int length, out int returnedLength);
  [DllImport("kernel32.dll")]
  private static extern IntPtr GetCurrentProcess();
  public static int Read() {
    BasicInfo info; int returned;
    int status=NtQueryInformationProcess(GetCurrentProcess(),0,out info,
      Marshal.SizeOf(typeof(BasicInfo)),out returned);
    if(status!=0) throw new InvalidOperationException("own parent process query failed: "+status);
    return checked((int)info.ParentPid.ToInt64());
  }
}
"@
$ownedRootPid=[L1R1ParentProcess]::Read()
Write-Json 'runtime.json' @{shell=(Get-Process -Id $PID).Path;psVersion=$PSVersionTable.PSVersion.ToString();clrVersion=[Environment]::Version.ToString();sourceSha256=$cfg.sourceSha256;requestedChildPid=$PID;ownedBootstrapRootPid=$ownedRootPid}
if($PSVersionTable.PSVersion.Major -lt $cfg.minimumShellMajor){throw 'L1R1-FIXTURE: runtime below registered support; uncovered'}
$mutex=[Threading.Mutex]::new($false,$cfg.mutexName)
$locked=$mutex.WaitOne(1000)
if(-not $locked){throw 'L1R1-FIXTURE: private mutex acquisition failed'}
try {
'@
$outerFinally=@'
} finally {
  # The production finalizer has already run (including its exit instruction).
  # This observation cannot set its verdict or restore original repository files.
  $pinBeforeRestore=[IO.File]::ReadAllText($cfg.pin,$utf8)
  $pin2BeforeRestore=[IO.File]::ReadAllText($cfg.pin2,$utf8)
  $sentinelPresent=Test-Path -LiteralPath $cfg.sentinel -PathType Leaf
  $sentinelText=if($sentinelPresent){[IO.File]::ReadAllText($cfg.sentinel,$utf8)}else{$null}
  Write-Json 'fixture-finally-entry.json' @{
    enteredMain=$enteredMain;baselineCount=@($baseline).Count;pinBeforeRestore=$pinBeforeRestore
    pin2BeforeRestore=$pin2BeforeRestore;lockAcquired=$lockAcquired
    shadowPresent=(Test-Path -LiteralPath $shadow);sentinelPresent=$sentinelPresent
    sentinelText=$sentinelText;stageError=$stageError;integrityError=$integrityError;cleanupError=$cleanupError
  }
  try {
    if($null -ne $lockStream){$lockStream.Dispose();$lockStream=$null}
  } finally {
    [IO.File]::WriteAllText($cfg.pin,$cfg.pinOriginal,$utf8)
    [IO.File]::WriteAllText($cfg.pin2,$cfg.pin2Original,$utf8)
    Write-Json 'fixture-restoration.json' @{
      ownedPinRestored=([IO.File]::ReadAllText($cfg.pin,$utf8) -ceq $cfg.pinOriginal)
      ownedSecondPinRestored=([IO.File]::ReadAllText($cfg.pin2,$utf8) -ceq $cfg.pin2Original)
      lockDisposed=($null -eq $lockStream)
      scope='Only this harness-owned scratch fixture; no production original/tracked bytes restored'
    }
  }
}
'@
$childSource=$prelude+[Environment]::NewLine+($definitions -join [Environment]::NewLine)+[Environment]::NewLine+$outerStart+[Environment]::NewLine+'try {'+[Environment]::NewLine+$fixtureBody+[Environment]::NewLine+'} '+$catchFinally+$terminal+[Environment]::NewLine+$outerFinally
$childPath=Join-Path $run 'child.ps1'
[IO.File]::WriteAllText($childPath,$childSource,$utf8)
$childTokens=$null;$childParseErrors=$null
$null=[Management.Automation.Language.Parser]::ParseInput($childSource,[ref]$childTokens,[ref]$childParseErrors)
Assert-Control (@($childParseErrors).Count -eq 0) 'generated source-bound child parse failed'
  foreach($role in @('P','Q')){
    $expected=if($role -ceq 'P'){
      [pscustomobject]@{mode='success';expectedExit=0;stageFailure=$false;integrityFailure=$false;cleanupFailure=$false;shadowRemoved=$true;baselineCount=2;minimumShellMajor=$test.minimumShellMajor}
    }else{$test}
    $fixture=Join-Path $run $role
    $productionEvidence=Join-Path $fixture 'production-evidence'
    [void][IO.Directory]::CreateDirectory($productionEvidence)
    $shadow=if($expected.mode -ceq 'outside'){Join-Path $fixture 'outside/shadow'}elseif($expected.mode -ceq 'basename'){Join-Path $productionEvidence 'not-shadow'}else{Join-Path $productionEvidence 'shadow'}
    [void][IO.Directory]::CreateDirectory($shadow)
    $pin=Join-Path $fixture 'captured-pin.txt'
    $pin2=Join-Path $fixture 'second-pin.txt'
    $sentinel=Join-Path $shadow 'sentinel.txt'
    $lockFile=Join-Path $shadow 'locked.txt'
    [IO.File]::WriteAllText($pin,'initial captured fixture',$utf8)
    [IO.File]::WriteAllText($pin2,'initial second fixture',$utf8)
    [IO.File]::WriteAllText($sentinel,'owned shadow sentinel',$utf8)
    [IO.File]::WriteAllText($lockFile,'exclusive lock target',$utf8)
    $mutexName='Local\RMQLife1FinalizerControl-'+[Guid]::NewGuid().ToString('N')
    $observer=[Threading.Mutex]::new($false,$mutexName)
    $configuration=[ordered]@{
      mode=$expected.mode;productionEvidence=$productionEvidence;shadow=$shadow
      pin=$pin;pin2=$pin2;pinOriginal='initial captured fixture';pin2Original='initial second fixture'
      sentinel=$sentinel;lockFile=$lockFile;pidPath=(Join-Path $fixture 'child.pid')
      mutexName=$mutexName;minimumShellMajor=$expected.minimumShellMajor
      productionRegistryHash='4c9c7a4259808bb64c74656fd52559752e76f02834f2ac8567f5830968a5b80d'
      sourceSha256=$sourceIdentity.sourceSha256
    }
    $configPath=Join-Path $fixture 'configuration.json'
    Write-ControlJson $configPath $configuration
    $processResult=$null;$mutexAcquired=$false;$mutexAbandoned=$false
    $harnessCleanup=$false
    try {
      $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$childPath,'-Configuration',$configPath)
      $processResult=Invoke-RMQOwnedBoundedProcess -FilePath $shellPath -Arguments $arguments -WorkingDirectory $root -Stage ($Case+'-'+$role) -DeadlineSeconds $childSeconds -OutputLimitBytes $outputBytes -TempRoot (Join-Path $fixture 'process')
      Save-ProcessReceipt $fixture $processResult
      try{$mutexAcquired=$observer.WaitOne(0)}catch [Threading.AbandonedMutexException]{$mutexAcquired=$true;$mutexAbandoned=$true}
      Write-ControlJson (Join-Path $fixture 'mutex-observation.json') @{name=$mutexName;acquired=$mutexAcquired;abandoned=$mutexAbandoned;scope='Private mutex held by actual finalizer child; retained parent handle makes abandoned release detectable'}
      Assert-Control (-not $processResult.TimedOut -and -not $processResult.OutputLimitExceeded) ($role+' timed out or exceeded output limit')
      Assert-Control ($processResult.ExitCode -eq $expected.expectedExit) ($role+' unexpected child exit: '+$processResult.ExitCode)
      Assert-Control ($mutexAcquired -and -not $mutexAbandoned) ($role+' production mutex was not released normally')
      $summaryPath=Join-Path $productionEvidence 'summary.json'
      Assert-Control (Test-Path -LiteralPath $summaryPath -PathType Leaf) ($role+' production summary missing')
      $summary=[IO.File]::ReadAllText($summaryPath,$utf8)|ConvertFrom-Json
      $observed=[IO.File]::ReadAllText((Join-Path $productionEvidence 'fixture-finally-entry.json'),$utf8)|ConvertFrom-Json
      $restoration=[IO.File]::ReadAllText((Join-Path $productionEvidence 'fixture-restoration.json'),$utf8)|ConvertFrom-Json
      $runtime=[IO.File]::ReadAllText((Join-Path $productionEvidence 'runtime.json'),$utf8)|ConvertFrom-Json
      $childPid=[int][IO.File]::ReadAllText($configuration.pidPath,$utf8)
      $rootPid=[int]$runtime.ownedBootstrapRootPid
      Assert-Control ($rootPid -gt 0 -and $childPid -eq $runtime.requestedChildPid -and $rootPid -ne $childPid) ($role+' actual root/child process identity unavailable')
      Assert-Control ($null -eq (Get-Process -Id $childPid -ErrorAction SilentlyContinue)) ($role+' requested child survived')
      Assert-Control ($null -eq (Get-Process -Id $rootPid -ErrorAction SilentlyContinue)) ($role+' owned bootstrap root survived')
      Assert-Control ($summary.passed -eq ($expected.expectedExit -eq 0)) ($role+' production passed field differs')
      Assert-Control ($summary.registrySha256 -ceq $configuration.productionRegistryHash -and @($summary.selected).Count -eq 1 -and $summary.selected[0] -ceq 'D20_ACCEPT_IDENTITY' -and @($summary.cases).Count -eq 0) ($role+' exact component summary context differs')
      Assert-Control ($summary.restored -eq (-not $expected.integrityFailure)) ($role+' production integrity disposition differs')
      Assert-Control ($summary.shadowRemoved -eq $expected.shadowRemoved -and (Test-Path -LiteralPath $shadow) -eq (-not $expected.shadowRemoved)) ($role+' production shadow disposition differs')
      Assert-Control ($observed.enteredMain -and $observed.baselineCount -eq $expected.baselineCount) ($role+' fixture body/captured baseline not reached')
      Assert-Control ($restoration.ownedPinRestored -and $restoration.ownedSecondPinRestored -and $restoration.lockDisposed) ($role+' fixture own-finally restoration failed')
      Assert-Control ([IO.File]::ReadAllText($pin,$utf8) -ceq $configuration.pinOriginal -and [IO.File]::ReadAllText($pin2,$utf8) -ceq $configuration.pin2Original) ($role+' fixture bytes not restored')
      $pinAtFinalizer=if($expected.integrityFailure){'changed captured fixture'}else{$configuration.pinOriginal}
      Assert-Control ($observed.pinBeforeRestore -ceq $pinAtFinalizer) ($role+' production unexpectedly restored/changed captured pin')
      $expectedErrors=[Collections.Generic.List[string]]::new()
      $stageMessage=if($expected.mode -cin @('partial','partial-and-pin')){'L1R1-FIXTURE: capture-stage failure after one pin'}else{'L1R1-FIXTURE: prior stage failure'}
      $integrityMessage='LIFE1-RESTORATION: original bytes changed: '+$pin
      if($expected.stageFailure){$expectedErrors.Add($stageMessage)}
      if($expected.integrityFailure){$expectedErrors.Add($integrityMessage)}
      if($SourceVariant -ceq 'repaired'){
        Assert-Control (($null -ne $summary.stageError) -eq $expected.stageFailure) ($role+' independent stage-error presence differs')
        Assert-Control (($null -ne $summary.integrityError) -eq $expected.integrityFailure) ($role+' independent integrity-error presence differs')
        Assert-Control (($null -ne $summary.cleanupError) -eq $expected.cleanupFailure) ($role+' independent cleanup-error presence differs')
        if($expected.stageFailure){Assert-Control ($summary.stageError -ceq $stageMessage) ($role+' wrong stage error')}
        if($expected.integrityFailure){Assert-Control ($summary.integrityError -ceq $integrityMessage) ($role+' wrong integrity error')}
      }
      if($expected.cleanupFailure){
        if($expected.mode -cin @('outside','basename')){
          Assert-Control ($summary.cleanupError -ceq 'LIFE1-CLEANUP: shadow path escaped evidence root') ($role+' wrong safe-path guard failure')
          Assert-Control ($observed.sentinelPresent -and $observed.sentinelText -ceq 'owned shadow sentinel') ($role+' rejected cleanup path was touched')
        }else{
          Assert-Control ($observed.lockAcquired -and (Test-Path -LiteralPath $lockFile -PathType Leaf)) ($role+' real exclusive-lock cleanup challenge not reached')
          $lockedMessageFull="The process cannot access the file '"+$lockFile+"' because it is being used by another process."
          $lockedMessageLeaf="The process cannot access the file 'locked.txt' because it is being used by another process."
          Assert-Control ($summary.cleanupError -ceq $lockedMessageFull -or $summary.cleanupError -ceq $lockedMessageLeaf) ($role+' cleanup error is not the exact locked-file surface')
        }
        $expectedErrors.Add([string]$summary.cleanupError)
      }
      Assert-ExactLines @($processResult.StandardError) @($expectedErrors.ToArray()) ($role+' stderr')
      $expectedOutput=if($expected.expectedExit -eq 0){@('LIFE1-DEPENDENCY PASS '+$productionEvidence)}else{@()}
      Assert-ExactLines @($processResult.StandardOutput) @($expectedOutput) ($role+' stdout')
      $failurePath=Join-Path $productionEvidence 'failure.json'
      Assert-Control ((Test-Path -LiteralPath $failurePath -PathType Leaf) -eq $expected.stageFailure) ($role+' production stage failure receipt presence differs')
      if($expected.stageFailure){
        $failure=[IO.File]::ReadAllText($failurePath,$utf8)|ConvertFrom-Json
        Assert-Control ($failure.message -ceq $stageMessage) ($role+' production stage failure receipt changed')
      }
      $pairRecords.Add([ordered]@{role=$role;mode=$expected.mode;pid=$childPid;ownedBootstrapRootPid=$rootPid;requestedChildAbsent=$true;rootAbsent=$true;runtime=$runtime;process=$processResult;summary=$summary;fixture=$observed;restoration=$restoration;mutexReleasedWithoutAbandonment=$true;passed=$true})
    }finally{
      # Each cleanup step is guarded separately; a cleanup failure is recorded
      # and fails the control without replacing the pair's own error.
      if($mutexAcquired){try{$observer.ReleaseMutex()}catch{$cleanupErrors.Add($role+' observer mutex release: '+$_.Exception.Message)}}
      try{$observer.Dispose()}catch{$cleanupErrors.Add($role+' observer mutex dispose: '+$_.Exception.Message)}
      # Restore only named harness-owned pins if a child died before its own finally.
      try{[IO.File]::WriteAllText($pin,$configuration.pinOriginal,$utf8)}catch{$cleanupErrors.Add($role+' owned pin restoration: '+$_.Exception.Message)}
      try{[IO.File]::WriteAllText($pin2,$configuration.pin2Original,$utf8)}catch{$cleanupErrors.Add($role+' owned second pin restoration: '+$_.Exception.Message)}
      $harnessCleanup=$false
      try{
        if(Test-Path -LiteralPath $shadow){
          $owned=Assert-OwnedDescendant $shadow $fixture
          Remove-Item -LiteralPath $owned -Recurse -Force
        }
        $harnessCleanup=(-not(Test-Path -LiteralPath $shadow))
      }catch{$cleanupErrors.Add($role+' owned shadow removal: '+$_.Exception.Message)}
      try{Write-ControlJson (Join-Path $fixture 'harness-cleanup.json') @{shadowRemoved=$harnessCleanup;ownedPinsRestored=$true;productionVerdictAlreadyRecorded=$true;scope='Final cleanup of registered scratch descendants only; never tracked source or production original files'}}
      catch{$cleanupErrors.Add($role+' harness cleanup record: '+$_.Exception.Message)}
    }
  }
  Assert-Control ($pairRecords.Count -eq 2) 'positive/challenged pair incomplete'
  $overallPassed=$true
}catch{$controlError=$_.Exception.Message;$controlRecord=$_}
finally{
  # Independent integrity on every exit path: each captured entry pin in its own
  # guard, continuing past the first difference or exception.
  foreach($path in $pinLabels.Keys){
    $label=$pinLabels[$path]
    $entry=if($entryPins.Contains($path)){$entryPins[$path]}else{$null}
    $final=$null;$status='not-captured'
    if($null -ne $entry){
      $status='verified'
      try{$final=Hash-ControlFile $path}catch{$status='unreadable-final';$integrityErrors.Add('L1R1-FINALIZER: '+$label+' final hash failed: '+$_.Exception.Message)}
      if($null -ne $final -and $final -cne $entry){
        $status='changed'
        $integrityErrors.Add($(if($label -ceq 'production script'){'L1R1-FINALIZER: production script changed during pair'}elseif($label -ceq 'protected helper'){'L1R1-FINALIZER: protected helper changed during pair'}else{'L1R1-FINALIZER: '+$label+' changed during control'}))
      }
    }
    $pinChecks.Add([ordered]@{path=$path;label=$label;entrySha256=$entry;finalSha256=$final;status=$status})
  }
  $childSourceSha256=$null
  if($null -ne $childPath -and [IO.File]::Exists($childPath)){
    try{$childSourceSha256=Hash-ControlFile $childPath}catch{$cleanupErrors.Add('child source identity: '+$_.Exception.Message)}
  }
  $overallPassed=$overallPassed -and $null -eq $controlError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$(if($overallPassed){'pass'}else{'fail'});stageError=$controlError
    integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@($cleanupErrors.ToArray());pinChecks=@($pinChecks.ToArray())
    entryPinCount=$entryPins.Count;verifiedPinCount=@($pinChecks|Where-Object {$_.status -ceq 'verified'}).Count}
  try{
    Write-ControlJson (Join-Path $run 'result.json') @{
      id=$Case;passed=$overallPassed;error=$controlError;expected=$test;source=$sourceIdentity
      childSourceSha256=$childSourceSha256;records=@($pairRecords.ToArray())
      deadlineSeconds=$childSeconds;outputLimitBytes=$outputBytes;finalization=$finalization
      emptyBaselineLimit='A successful empty baseline quantifies over no files; it cannot establish whole-tree integrity'
    }
  }catch{$durableFailed=$true;$overallPassed=$false;[Console]::Error.WriteLine('L1R1-FINALIZER: durable result write failed: '+$_.Exception.Message)}
}
if(-not $overallPassed){
  foreach($message in @($integrityErrors)+@($cleanupErrors)){[Console]::Error.WriteLine($message)}
  if($null -ne $controlRecord){throw $controlRecord}
  exit 1
}
Write-Output ('L1R1-FINALIZER CONTROL PASS '+$Case+' '+$run)

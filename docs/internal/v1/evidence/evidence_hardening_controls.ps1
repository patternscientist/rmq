[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][ValidateSet('pwsh','winps')][string]$Profile,
  [string]$OutputRoot
)

# Focused V1 controls for EH1--EH3. These controls exercise only disposable
# fixtures and command boundaries. They are not a replay of the historical
# lifecycle semantic campaigns.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
$shells=@{
  pwsh='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
  winps='C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe'
}
$shell=$shells[$Profile]
. (Join-Path $repo 'docs/internal/extensions/lifecycle1/repair-r1/runtime_profile.ps1')
$runtime=Assert-LifecycleRepairRuntime $shell $Profile
if([string]::IsNullOrWhiteSpace($OutputRoot)){
  $OutputRoot=Join-Path $repo ('.lake/v1-evidence/'+$Profile+'-'+[Guid]::NewGuid().ToString('N'))
}
$evidence=[IO.Path]::GetFullPath($OutputRoot)
$allowed=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($allowed,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){
  throw 'V1-EVIDENCE: fresh owned descendant of repository .lake required'
}
[void][IO.Directory]::CreateDirectory($evidence)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')

function Assert-V1([bool]$Condition,[string]$Message){if(-not $Condition){throw ('V1-EVIDENCE: '+$Message)}}
function Write-V1Json([string]$Path,[object]$Value){[IO.File]::WriteAllText($Path,($Value|ConvertTo-Json -Depth 80),$utf8)}
function Get-V1Hash([string]$Path){return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash}
function Copy-V1File([string]$Source,[string]$Destination){
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($Destination))
  [IO.File]::WriteAllBytes($Destination,[IO.File]::ReadAllBytes($Source))
}
function Copy-V1Relative([string]$Relative,[string]$Root){
  Copy-V1File (Join-Path $repo $Relative) (Join-Path $Root $Relative)
}
function New-V1FixtureRoot([string]$Label){
  $root=Join-Path $evidence ('fixtures/'+$Label+'/root')
  [void][IO.Directory]::CreateDirectory($root)
  return $root
}
function Invoke-V1Child([string]$Label,[string]$File,[string[]]$Arguments,[string]$WorkingDirectory,[int]$DeadlineSeconds){
  $directory=Join-Path $evidence ('processes/'+$Label)
  [void][IO.Directory]::CreateDirectory($directory)
  $result=Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $WorkingDirectory `
    -Stage $Label -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 1048576 -TempRoot (Join-Path $directory 'owned')
  Write-V1Json (Join-Path $directory 'process.json') $result
  [IO.File]::WriteAllText((Join-Path $directory 'stdout.returned-lines.txt'),(@($result.StandardOutput)-join [char]10),$utf8)
  [IO.File]::WriteAllText((Join-Path $directory 'stderr.returned-lines.txt'),(@($result.StandardError)-join [char]10),$utf8)
  Assert-V1 (-not $result.TimedOut -and -not $result.OutputLimitExceeded) ($Label+' exceeded its finite process bound')
  Assert-V1 ($result.Ownership -ceq 'kill-on-close-job' -and @($result.TerminatedIds).Count -eq 0) ($Label+' did not close its owned process tree')
  return $result
}
function Replace-V1First([string]$Text,[string]$Before,[string]$After){
  $index=$Text.IndexOf($Before,[StringComparison]::Ordinal)
  Assert-V1 ($index -ge 0) ('derived-fixture anchor absent: '+$Before)
  return $Text.Substring(0,$index)+$After+$Text.Substring($index+$Before.Length)
}

$records=[Collections.Generic.List[object]]::new()
$sourcePins=[ordered]@{}
$integrityErrors=[Collections.Generic.List[string]]::new()
$stageError=$null;$stageRecord=$null;$completed=$false;$passed=$false
$sources=@(
  'docs/internal/extensions/lifecycle1/repair-r4/predicates.ps1',
  'docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json',
  'docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1',
  'docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1',
  'docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1',
  'docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1',
  'scripts/owned_process_tree.ps1'
)
foreach($relative in $sources){$absolute=Join-Path $repo $relative;$sourcePins[$absolute]=Get-V1Hash $absolute}

try {
  # EH1: independently stated roster fixtures exercise the predicate directly.
  . (Join-Path $repo 'docs/internal/extensions/lifecycle1/repair-r4/predicates.ps1')
  $h1='1111111111111111111111111111111111111111111111111111111111111111'
  $h2='2222222222222222222222222222222222222222222222222222222222222222'
  $h3='3333333333333333333333333333333333333333333333333333333333333333'
  $git40='aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'
  function New-V1Row([string]$Path,[object]$Entry,[object]$Final,[string]$Status){
    return [pscustomobject]@{path=$Path;entrySha256=$Entry;finalSha256=$Final;status=$Status}
  }
  function New-V1Fin([object[]]$Rows,[int]$Count){return [pscustomobject]@{pinChecks=@($Rows);entryPinCount=$Count}}
  $roster=[pscustomobject]@{rows=@('a','b','c');stages=[pscustomobject]@{complete=[pscustomobject]@{capturedIndexes=@(0,1,2)}}}
  $fileRoster=[pscustomobject]@{rows=@('a');stages=[pscustomobject]@{complete=[pscustomobject]@{capturedIndexes=@(0)}}}
  $gitRoster=[pscustomobject]@{rows=@('git:HEAD');identityKinds=[pscustomobject]@{'0'='git-sha1'};stages=[pscustomobject]@{complete=[pscustomobject]@{capturedIndexes=@(0)}}}
  $predicateCases=@(
    [pscustomobject]@{id='intact';ok=$true;prefix='captured 3 of 3 rows, all re-verified, exact roster stage complete';fin=(New-V1Fin @((New-V1Row a $h1 $h1 verified),(New-V1Row b $h2 $h2 verified),(New-V1Row c $h3 $h3 verified)) 3)},
    [pscustomobject]@{id='git-intact';ok=$true;prefix='captured 1 of 1 rows, all re-verified, exact roster stage complete';roster=$gitRoster;fin=(New-V1Fin @((New-V1Row 'git:HEAD' $git40 $git40 verified)) 1)},
    [pscustomobject]@{id='file-sha1';ok=$false;prefix='malformed captured SHA256: a';roster=$fileRoster;fin=(New-V1Fin @((New-V1Row a $git40 $git40 verified)) 1)},
    [pscustomobject]@{id='git-sha256';ok=$false;prefix='malformed captured Git SHA1: git:HEAD';roster=$gitRoster;fin=(New-V1Fin @((New-V1Row 'git:HEAD' $h1 $h1 verified)) 1)},
    [pscustomobject]@{id='legacy-git-intact';ok=$true;prefix='captured 1 of 1 rows, all re-verified';roster=$null;fin=(New-V1Fin @((New-V1Row 'git:HEAD' $git40 $git40 verified)) 1)},
    [pscustomobject]@{id='legacy-file-sha1';ok=$false;prefix='malformed captured SHA256: a';roster=$null;fin=(New-V1Fin @((New-V1Row a $git40 $git40 verified)) 1)},
    [pscustomobject]@{id='missing-pin';ok=$false;prefix='required pin not captured at roster index 2: c';fin=(New-V1Fin @((New-V1Row a $h1 $h1 verified),(New-V1Row b $h2 $h2 verified),(New-V1Row c $null $null 'not-captured')) 2)},
    [pscustomobject]@{id='coordinated-count';ok=$false;prefix='pinCheck roster count 2 differs from expected 3';fin=(New-V1Fin @((New-V1Row a $h1 $h1 verified),(New-V1Row b $h2 $h2 verified)) 2)},
    [pscustomobject]@{id='empty-hash';ok=$false;prefix='malformed captured SHA256: a';fin=(New-V1Fin @((New-V1Row a '' $h1 verified),(New-V1Row b $h2 $h2 verified),(New-V1Row c $h3 $h3 verified)) 3)},
    [pscustomobject]@{id='nonhex-hash';ok=$false;prefix='malformed captured SHA256: a';fin=(New-V1Fin @((New-V1Row a ('g'*64) $h1 verified),(New-V1Row b $h2 $h2 verified),(New-V1Row c $h3 $h3 verified)) 3)},
    [pscustomobject]@{id='wrong-order';ok=$false;prefix='pinCheck path at roster index 0 differs: b';fin=(New-V1Fin @((New-V1Row b $h2 $h2 verified),(New-V1Row a $h1 $h1 verified),(New-V1Row c $h3 $h3 verified)) 3)}
  )
  foreach($case in $predicateCases){
    $caseRoster=if($null -ne $case.PSObject.Properties['roster']){$case.roster}else{$roster}
    $observed=Test-R4PinCoverage $case.fin $null $true $caseRoster 'complete'
    Assert-V1 ([bool]$observed.ok -eq [bool]$case.ok) ('EH1 predicate verdict differs for '+$case.id)
    Assert-V1 ([string]$observed.reason).StartsWith($case.prefix,[StringComparison]::Ordinal) ('EH1 predicate clause differs for '+$case.id+': '+$observed.reason)
    $records.Add([ordered]@{id=('EH1-PRED-'+$case.id);passed=$true;expected=$case.ok;observed=$observed})
  }

  # EH1 production consumer: the real failure-control loader validates the exact
  # 60-case v3 registry and its roster/stage mapping before ProbeOnly selection.
  $failureDriver=Join-Path $repo 'docs/internal/extensions/lifecycle1/repair-r3/failure_controls.ps1'
  $failureRegistry=Join-Path $repo 'docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json'
  $registry=[IO.File]::ReadAllText($failureRegistry,$utf8)|ConvertFrom-Json
  $registryIds=@($registry.controls|ForEach-Object {[string]$_.id})
  Assert-V1 ($registryIds.Count -eq 60 -and @($registryIds|Select-Object -Unique).Count -eq 60) 'EH1 registry is not exactly 60 unique ordered controls'
  $available=@($registry.controls|Where-Object {@($_.profiles) -ccontains $Profile}|ForEach-Object {[string]$_.id})
  $probeWrapper=Join-Path $evidence 'invoke-failure-probe.ps1'
  [IO.File]::WriteAllText($probeWrapper,@'
param([string]$Driver,[string]$Registry,[string]$HarnessRef,[string]$Profile,[string]$Mode,[string]$Id)
$ErrorActionPreference='Stop'
try {
  $p=@{HarnessRef=$HarnessRef;Profile=$Profile;RegistryPath=$Registry;ProbeOnly=$true}
  switch -CaseSensitive ($Mode) {
    'omitted' {}
    'exact' {$p.OnlyControl=@($Id)}
    'empty' {$p.OnlyControl=@()}
    'whitespace' {$p.OnlyControl=@(' ')}
    'zero' {$p.OnlyControl=@('0')}
    'unknown' {$p.OnlyControl=@('ZZ-UNKNOWN')}
    'duplicate' {$p.OnlyControl=@($Id,$Id)}
    default {throw 'wrapper mode unknown'}
  }
  & $Driver @p
  exit ([int]$LASTEXITCODE)
}catch{[Console]::Error.WriteLine($_.Exception.Message);exit 1}
'@,$utf8)
  $probeCases=@(
    [pscustomobject]@{mode='omitted';exit=0;stdout=('R3 SELECT '+($available -join ','));stderr=$null},
    [pscustomobject]@{mode='exact';exit=0;stdout=('R3 SELECT '+$available[0]);stderr=$null},
    [pscustomobject]@{mode='empty';exit=1;stdout=$null;stderr='R3-SELECTOR: explicitly empty selector'},
    [pscustomobject]@{mode='whitespace';exit=1;stdout=$null;stderr='R3-SELECTOR: empty or whitespace selector'},
    [pscustomobject]@{mode='zero';exit=1;stdout=$null;stderr='R3-SELECTOR: malformed selector'},
    [pscustomobject]@{mode='unknown';exit=1;stdout=$null;stderr='R3-SELECTOR: unknown selector'},
    [pscustomobject]@{mode='duplicate';exit=1;stdout=$null;stderr='R3-SELECTOR: duplicate selector'}
  )
  $pwsh=$shells.pwsh
  foreach($case in $probeCases){
    $r=Invoke-V1Child ('eh1-probe-'+$case.mode) $pwsh @('-NoLogo','-NoProfile','-File',$probeWrapper,'-Driver',$failureDriver,'-Registry',$failureRegistry,'-HarnessRef','worktree','-Profile',$Profile,'-Mode',$case.mode,'-Id',$available[0]) $repo 30
    Assert-V1 ($r.ExitCode -eq $case.exit) ('EH1 '+$case.mode+' exit differs')
    $actualOut=if(@($r.StandardOutput).Count -eq 1){[string]$r.StandardOutput[0]}else{$null}
    $actualErr=if(@($r.StandardError).Count -eq 1){[string]$r.StandardError[0]}else{$null}
    Assert-V1 ($actualOut -ceq $case.stdout -and $actualErr -ceq $case.stderr) ('EH1 '+$case.mode+' exact stream differs')
    $records.Add([ordered]@{id=('EH1-CONSUMER-'+$case.mode);passed=$true;exit=$r.ExitCode;deadlineSeconds=30;process=('processes/eh1-probe-'+$case.mode+'/process.json')})
  }
  foreach($mutation in @('missing','duplicate')){
    $copy=[IO.File]::ReadAllText($failureRegistry,$utf8)|ConvertFrom-Json
    $target=[string]$copy.controls[1].id
    if($mutation -ceq 'missing'){$copy.controls=@($copy.controls|Select-Object -Skip 1)}else{$copy.controls[1].id=$copy.controls[0].id}
    $path=Join-Path $evidence ('eh1-registry-'+$mutation+'.json')
    Write-V1Json $path $copy
    $r=Invoke-V1Child ('eh1-registry-'+$mutation) $pwsh @('-NoLogo','-NoProfile','-File',$probeWrapper,'-Driver',$failureDriver,'-Registry',$path,'-HarnessRef','worktree','-Profile',$Profile,'-Mode','omitted','-Id',$available[0]) $repo 30
    $expected=if($mutation -ceq 'missing'){'R3-REGISTRY: missing ID '+$registryIds[0]}else{'R3-REGISTRY: duplicate ID '+$registryIds[0]}
    Assert-V1 ($r.ExitCode -eq 1 -and @($r.StandardOutput).Count -eq 0 -and @($r.StandardError).Count -eq 1 -and $r.StandardError[0] -ceq $expected) ('EH1 '+$mutation+' registry guard differs')
    $records.Add([ordered]@{id=('EH1-REGISTRY-'+$mutation);passed=$true;expectedError=$expected;deadlineSeconds=30;process=('processes/eh1-registry-'+$mutation+'/process.json')})
  }

  # EH2: derive a repository-shaped fixture, copy the exact native dependency
  # closure, mutate only the copied lean.exe after entry capture, and restore it
  # after the production finally records the changed final pin.
  . (Join-Path $repo 'scripts/packed_native_lifecycle_integrity_check.ps1')
  $liveCaptured=[Collections.Generic.List[object]]::new()
  function Get-LNPin([string]$Path){$pin=Get-LNRawPin $Path;$liveCaptured.Add($pin);return $pin}
  $liveBin='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
  $liveClosure=Get-LNDependencyClosure @('lean.exe','leanc.exe','clang.exe','ld.lld.exe'|ForEach-Object {Join-Path $liveBin $_}) $liveBin
  Assert-V1 (@($liveClosure.nodes).Count -eq 11) 'EH2 live dependency closure is not the frozen 11-node prerequisite'
  $eh2Root=New-V1FixtureRoot 'eh2-entry-final'
  Copy-V1Relative 'scripts/owned_process_tree.ps1' $eh2Root
  Copy-V1Relative 'scripts/packed_native_lifecycle_integrity_check.ps1' $eh2Root
  $fixtureBin=Join-Path $eh2Root 'toolchain/bin'
  [void][IO.Directory]::CreateDirectory($fixtureBin)
  $pathMap=@{}
  foreach($node in @($liveClosure.nodes)){
    $destination=Join-Path $fixtureBin (Split-Path $node.path -Leaf)
    Copy-V1File $node.path $destination
    $pathMap[[IO.Path]::GetFullPath([string]$node.path).ToLowerInvariant()]=$destination
    $sourcePins[[string]$node.path]=Get-V1Hash $node.path
  }
  $resultsSource=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/RESULTS.json'
  $resultsDoc=[IO.File]::ReadAllText($resultsSource,$utf8)|ConvertFrom-Json
  $oldSource=[string]$resultsDoc.rawSummary.path
  $oldDoc=[IO.File]::ReadAllText($oldSource,$utf8)|ConvertFrom-Json
  function Update-V1PinPaths([object]$Node){
    if($null -eq $Node -or $Node -is [string] -or $Node -is [ValueType]){return}
    if($Node -is [Management.Automation.PSCustomObject]){
      $pathProperty=$Node.PSObject.Properties['path']
      if($null -ne $pathProperty -and $pathProperty.Value -is [string]){
        $key=[IO.Path]::GetFullPath([string]$pathProperty.Value).ToLowerInvariant()
        if($pathMap.ContainsKey($key)){$pathProperty.Value=$pathMap[$key]}
      }
      foreach($property in $Node.PSObject.Properties){Update-V1PinPaths $property.Value}
      return
    }
    if($Node -is [Collections.IEnumerable]){foreach($item in $Node){Update-V1PinPaths $item}}
  }
  Update-V1PinPaths $oldDoc
  $oldCopy=Join-Path $eh2Root 'docs/internal/extensions/lifecycle-native-p0/old-summary.fixture.json'
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($oldCopy))
  Write-V1Json $oldCopy $oldDoc
  $resultsDoc.rawSummary.path=$oldCopy
  $resultsDoc.rawSummary.bytes=([IO.FileInfo]$oldCopy).Length
  $resultsDoc.rawSummary.sha256=Get-V1Hash $oldCopy
  $resultsCopy=Join-Path $eh2Root 'docs/internal/extensions/lifecycle-native-p0/RESULTS.json'
  Write-V1Json $resultsCopy $resultsDoc
  $dependencySource=Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1'
  $derivedPath=Join-Path $eh2Root 'docs/internal/extensions/lifecycle-native-p0/repair-r1/dependency_controls.ps1'
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($derivedPath))
  $derived=[IO.File]::ReadAllText($dependencySource,$utf8).Replace("`r`n","`n")
  $derived=Replace-V1First $derived "`$bin='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'" ("`$bin='"+$fixtureBin.Replace("'","''")+"'")
  $captureAnchor='$pins=@($captured.ToArray())'
  $captureInsert=@'
$v1MutationPath=Join-Path $bin 'lean.exe'
$v1MutationEntryBytes=[IO.File]::ReadAllBytes($v1MutationPath)
[IO.File]::WriteAllBytes($v1MutationPath,([byte[]]$v1MutationEntryBytes+[byte]1))
'@
  $derived=Replace-V1First $derived $captureAnchor ($captureAnchor+"`n"+$captureInsert.TrimEnd())
  $restoreAnchor="  } catch {`$durableFailed=`$true;`$passed=`$false;[Console]::Error.WriteLine('DEPENDENCY CONTROLS: durable result write failed: '+`$_.Exception.Message)}`n}"
  $restoreReplacement=@'
  } catch {$durableFailed=$true;$passed=$false;[Console]::Error.WriteLine('DEPENDENCY CONTROLS: durable result write failed: '+$_.Exception.Message)}
  try {[IO.File]::WriteAllBytes($v1MutationPath,[byte[]]$v1MutationEntryBytes)}
  catch {$cleanupErrors.Add('V1 fixture restoration: '+$_.Exception.Message);$passed=$false}
}
'@
  $derived=Replace-V1First $derived $restoreAnchor $restoreReplacement.TrimEnd()
  [IO.File]::WriteAllText($derivedPath,$derived,$utf8)
  $leanCopy=Join-Path $fixtureBin 'lean.exe'
  $leanEntry=Get-V1Hash $leanCopy
  $dependencyOutput=Join-Path $eh2Root '.lake/dependency-result'
  $r=Invoke-V1Child 'eh2-entry-final' $shell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$derivedPath,'-OutputRoot',$dependencyOutput) $eh2Root 180
  Assert-V1 ($r.ExitCode -ne 0) 'EH2 controlled mutation did not fail closed'
  $resultPath=Join-Path $dependencyOutput 'RESULTS.json'
  Assert-V1 (Test-Path -LiteralPath $resultPath -PathType Leaf) 'EH2 durable RESULTS.json absent'
  $observed=[IO.File]::ReadAllText($resultPath,$utf8)|ConvertFrom-Json
  $entryLean=@($observed.entryPins|Where-Object {$_.path -ieq $leanCopy})
  $finalLean=@($observed.pins|Where-Object {$_.path -ieq $leanCopy})
  $checkLean=@($observed.finalization.pinChecks|Where-Object {$_.path -ieq $leanCopy})
  Assert-V1 ($entryLean.Count -eq 1 -and $finalLean.Count -eq 1 -and $checkLean.Count -eq 1) 'EH2 lean pin labels are not unique'
  Assert-V1 ($entryLean[0].sha256 -ceq $checkLean[0].entrySha256 -and $finalLean[0].sha256 -ceq $checkLean[0].finalSha256) 'EH2 labels do not match finalization reads'
  Assert-V1 ($entryLean[0].sha256 -cne $finalLean[0].sha256 -and $finalLean[0].state -ceq 'changed' -and $checkLean[0].status -ceq 'changed') 'EH2 mutation was not recorded as an entry/final difference'
  Assert-V1 ($observed.entryOldSummary.sha256 -ceq $observed.oldSummary.sha256 -and $observed.oldSummary.state -ceq 'verified') 'EH2 unchanged old-summary entry/final labels differ'
  Assert-V1 (-not [bool]$observed.installedToolsUnchanged -and $observed.finalization.verdict -ceq 'fail') 'EH2 changed copied tool did not force final failure'
  Assert-V1 ((Get-V1Hash $leanCopy) -ceq $leanEntry) 'EH2 copied lean.exe was not restored after the child returned'
  $records.Add([ordered]@{id='EH2-ENTRY-FINAL-MUTATION';passed=$true;fixtureOnly=$true;entrySha256=$entryLean[0].sha256;finalSha256=$finalLean[0].sha256;
    restoredSha256=(Get-V1Hash $leanCopy);oldSummaryState=$observed.oldSummary.state;childExit=$r.ExitCode;deadlineSeconds=180;result=$resultPath;process='processes/eh2-entry-final/process.json'})

  # EH3 run_controls: active registry and registered component failures happen
  # after the fixture's owned .lake evidence root exists and must emit summary.
  $runRel='docs/internal/extensions/lifecycle1/repair-r1'
  $runFiles=@('run_controls.ps1','runtime_profile.ps1','CONTROL_REGISTRY.json','CONTROL_REGISTRY.frozen.json','selector_cases.json','dependency_boundary_cases.json','finalizer_cases.json')
  foreach($mutation in @('frozen-registry-missing','frozen-registry-drift','registry-missing','registry-drift','component-missing','component-drift')){
    $fixtureRoot=New-V1FixtureRoot ('eh3-run-'+$mutation)
    foreach($file in $runFiles){
      if($mutation -ceq 'frozen-registry-missing' -and $file -ceq 'CONTROL_REGISTRY.frozen.json'){continue}
      if($mutation -ceq 'registry-missing' -and $file -ceq 'CONTROL_REGISTRY.json'){continue}
      if($mutation -ceq 'component-missing' -and $file -ceq 'selector_cases.json'){continue}
      Copy-V1Relative ($runRel+'/'+$file) $fixtureRoot
    }
    if($mutation -ceq 'frozen-registry-drift'){
      $path=Join-Path $fixtureRoot ($runRel+'/CONTROL_REGISTRY.frozen.json')
      [IO.File]::WriteAllText($path,'{}',$utf8)
    }elseif($mutation -ceq 'registry-drift'){
      $path=Join-Path $fixtureRoot ($runRel+'/CONTROL_REGISTRY.json')
      [IO.File]::AppendAllText($path," `n",$utf8)
    }elseif($mutation -ceq 'component-drift'){
      $path=Join-Path $fixtureRoot ($runRel+'/selector_cases.json')
      [IO.File]::AppendAllText($path," `n",$utf8)
    }
    $driver=Join-Path $fixtureRoot ($runRel+'/run_controls.ps1')
    $childEvidence=Join-Path $fixtureRoot ('.lake/'+$mutation)
    $r=Invoke-V1Child ('eh3-run-'+$mutation) $shell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$driver,'-Shell',$shell,'-Profile',$Profile,'-OnlyCase','S03_ARGUMENT_SINGLE','-EvidenceRoot',$childEvidence) $fixtureRoot 45
    Assert-V1 ($r.ExitCode -ne 0) ('EH3 run_controls '+$mutation+' did not fail')
    $summaryPath=Join-Path $childEvidence 'summary.json'
    Assert-V1 (Test-Path -LiteralPath $summaryPath -PathType Leaf) ('EH3 run_controls '+$mutation+' omitted durable summary')
    $summary=[IO.File]::ReadAllText($summaryPath,$utf8)|ConvertFrom-Json
    Assert-V1 (-not [bool]$summary.passed -and $summary.finalization.verdict -ceq 'fail' -and -not [string]::IsNullOrWhiteSpace([string]$summary.finalization.stageError)) ('EH3 run_controls '+$mutation+' summary is not fail-closed')
    Assert-V1 (@([IO.Directory]::EnumerateFiles($fixtureRoot,'summary.json',[IO.SearchOption]::AllDirectories)).Count -eq 1) ('EH3 run_controls '+$mutation+' record cardinality differs')
    $records.Add([ordered]@{id=('EH3-RUN-'+$mutation);passed=$true;childExit=$r.ExitCode;stageError=$summary.finalization.stageError;record=$summaryPath;deadlineSeconds=45;process=('processes/eh3-run-'+$mutation+'/process.json')})
  }

  # EH3 finalizer_control: its per-run result directory precedes registry/helper
  # validation, so the same four challenges leave exactly one durable result.
  foreach($mutation in @('registry-missing','registry-drift','component-missing','component-drift')){
    $fixtureRoot=New-V1FixtureRoot ('eh3-finalizer-'+$mutation)
    Copy-V1Relative ($runRel+'/finalizer_control.ps1') $fixtureRoot
    if($mutation -cne 'registry-missing'){Copy-V1Relative ($runRel+'/finalizer_cases.json') $fixtureRoot}
    if($mutation -in @('component-drift','registry-missing','registry-drift')){Copy-V1Relative 'scripts/owned_process_tree.ps1' $fixtureRoot}
    if($mutation -ceq 'registry-drift'){
      $path=Join-Path $fixtureRoot ($runRel+'/finalizer_cases.json')
      [IO.File]::WriteAllText($path,'{}',$utf8)
    }elseif($mutation -ceq 'component-drift'){
      $path=Join-Path $fixtureRoot 'scripts/owned_process_tree.ps1'
      [IO.File]::AppendAllText($path," `n",$utf8)
    }
    $driver=Join-Path $fixtureRoot ($runRel+'/finalizer_control.ps1')
    $childEvidence=Join-Path $fixtureRoot '.lake/v1-finalizer'
    $r=Invoke-V1Child ('eh3-finalizer-'+$mutation) $shell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$driver,'-Case','F01_INTACT_SUCCESS','-Shell',$shell,'-RepositoryRoot',$fixtureRoot,'-EvidenceRoot',$childEvidence) $fixtureRoot 45
    Assert-V1 ($r.ExitCode -ne 0) ('EH3 finalizer '+$mutation+' did not fail')
    $resultPaths=@([IO.Directory]::EnumerateFiles($childEvidence,'result.json',[IO.SearchOption]::AllDirectories))
    Assert-V1 ($resultPaths.Count -eq 1) ('EH3 finalizer '+$mutation+' durable record cardinality differs')
    $summary=[IO.File]::ReadAllText($resultPaths[0],$utf8)|ConvertFrom-Json
    Assert-V1 (-not [bool]$summary.passed -and $summary.finalization.verdict -ceq 'fail' -and -not [string]::IsNullOrWhiteSpace([string]$summary.finalization.stageError)) ('EH3 finalizer '+$mutation+' result is not fail-closed')
    $records.Add([ordered]@{id=('EH3-FINALIZER-'+$mutation);passed=$true;childExit=$r.ExitCode;stageError=$summary.finalization.stageError;record=$resultPaths[0];deadlineSeconds=45;process=('processes/eh3-finalizer-'+$mutation+'/process.json')})
  }
  # A legitimate SourceVariant mismatch remains a pre-root argument rejection.
  $fixtureRoot=New-V1FixtureRoot 'eh3-finalizer-sourcevariant'
  Copy-V1Relative ($runRel+'/finalizer_control.ps1') $fixtureRoot
  Copy-V1Relative ($runRel+'/finalizer_cases.json') $fixtureRoot
  $driver=Join-Path $fixtureRoot ($runRel+'/finalizer_control.ps1')
  $childEvidence=Join-Path $fixtureRoot '.lake/sourcevariant-must-not-exist'
  $r=Invoke-V1Child 'eh3-finalizer-sourcevariant' $shell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$driver,'-Case','F01_INTACT_SUCCESS','-SourceVariant','old','-Shell',$shell,'-RepositoryRoot',$fixtureRoot,'-EvidenceRoot',$childEvidence) $fixtureRoot 45
  Assert-V1 ($r.ExitCode -ne 0 -and -not (Test-Path -LiteralPath $childEvidence)) 'EH3 SourceVariant mismatch did not reject before root creation'
  Assert-V1 (@($r.StandardError|Where-Object {([string]$_).Contains('source variant differs from frozen case mapping')}).Count -gt 0) 'EH3 SourceVariant mismatch surface differs'
  $records.Add([ordered]@{id='EH3-FINALIZER-SOURCEVARIANT-PRE-ROOT';passed=$true;childExit=$r.ExitCode;evidenceRootCreated=$false;deadlineSeconds=45;process='processes/eh3-finalizer-sourcevariant/process.json'})
  Assert-V1 ($records.Count -eq 32) ('focused control roster differs: '+$records.Count)
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  foreach($path in $sourcePins.Keys){
    try {if((Get-V1Hash $path) -cne $sourcePins[$path]){$integrityErrors.Add('source/input changed: '+$path)}}
    catch {$integrityErrors.Add('source/input unreadable: '+$path+': '+$_.Exception.Message)}
  }
  $passed=$completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0
  $result=[ordered]@{
    schema='v1-evidence-hardening-controls-v1';profile=$Profile;runtime=$runtime;scope='Focused fixture controls only; not an old semantic-campaign replay.'
    category='host/runtime evidence only; no theorem, payload-bit, proof-field, model-tick, Lean-runtime, or performance implication'
    passed=$passed;expectedCount=32;executedCount=$records.Count;records=@($records.ToArray());sourcePins=$sourcePins
    finalization=[ordered]@{verdict=$(if($passed){'pass'}else{'fail'});stageError=$stageError;integrityErrors=@($integrityErrors.ToArray())}
  }
  try{Write-V1Json (Join-Path $evidence 'RESULT.json') $result}
  catch{$passed=$false;[Console]::Error.WriteLine('V1-EVIDENCE: durable result write failed: '+$_.Exception.Message)}
}
if(-not $passed){
  foreach($message in $integrityErrors){[Console]::Error.WriteLine($message)}
  if($null -ne $stageRecord){throw $stageRecord}
  exit 1
}
Write-Output ('V1 EVIDENCE CONTROLS PASS profile='+$Profile+' executed='+$records.Count+' evidence='+$evidence)

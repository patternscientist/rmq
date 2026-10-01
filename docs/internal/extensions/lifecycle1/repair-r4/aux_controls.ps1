[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$HarnessRef,
  [Parameter(Mandatory=$true)][ValidateSet('base','candidate')][string]$Expect,
  [string]$OutputRoot
)
# LIFE-1-R4 auxiliary controls. An exact ordered case list with no selector:
#  ORD-*  static ordering controls (audit P3-6): in every finally block that
#         releases a mutex, every `$integrityErrors.Add` must precede the first
#         ReleaseMutex call. They parse the exact Git blobs of -HarnessRef.
#  HR-*   heavy_run.ps1 controls (audit P3-1): the exact heavy_run.ps1 blob of
#         -HarnessRef runs in a disposable root through the owned-process helper;
#         HR-W's child turns RESULT.json into a directory so the wrapper's
#         durable write fails.
#  PRED-* synthetic mutation controls for repair-r4/predicates.ps1 at -HarnessRef
#         (audit P3-2 (b), P3-5): documents that silently drop, mislabel or
#         miscount pins must be rejected, and well-formed ones accepted. Each
#         pin case also records the verdict of the R3 predicate it replaces
#         (`pinChecks.Count -gt 0` for non-P shapes), transcribed from
#         repair-r3/failure_controls.ps1 at d27ffa34 line 468.
# -Expect base names the predicted outcome at the unrepaired ref (ORD-K1/K2/RC
# fail, HR-W shows the defect, PRED cases are not applicable because the file
# does not exist there); -Expect candidate requires every case to pass.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$here=$PSScriptRoot
$repo=[IO.Path]::GetFullPath((Join-Path $here '../../../../..'))
if($PSVersionTable.PSVersion.Major -lt 7){throw 'R4-AUX: PowerShell 7 required'}
$pwsh='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
$paths=[ordered]@{
  K1='docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1'
  K2='docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1'
  RC='docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1'
  LV='scripts/lifecycle_validator.ps1'
  HR='docs/internal/extensions/lifecycle1/repair-r3/heavy_run.ps1'
  PR='docs/internal/extensions/lifecycle1/repair-r4/predicates.ps1'
}
$expectedIds=@('ORD-K1','ORD-K2','ORD-RC','ORD-LV','HR-P','HR-W',
  'PRED-PIN-GOOD','PRED-PIN-ROSTER-GOOD','PRED-PIN-GIT-GOOD','PRED-PIN-FILE-SHA1','PRED-PIN-GIT-SHA256',
  'PRED-PIN-LEGACY-GIT-GOOD','PRED-PIN-LEGACY-FILE-SHA1',
  'PRED-PIN-DROPPED','PRED-PIN-COORDINATED','PRED-PIN-EMPTY','PRED-PIN-NONHEX',
  'PRED-PIN-ORDER','PRED-PIN-UNVERIFIED','PRED-PIN-COUNT','PRED-PIN-DUP','PRED-PIN-ALLVERIFIED',
  'PRED-LABEL-GOOD','PRED-LABEL-ENTRY','PRED-LABEL-STALE','PRED-VALUE-GOOD','PRED-VALUE-TYPE')
if([string]::IsNullOrWhiteSpace($OutputRoot)){$OutputRoot=Join-Path $repo ('.lake/life1-r4/aux-'+$Expect+'-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($OutputRoot)
$lakePrefix=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($lakePrefix,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'R4-AUX: fresh owned descendant of .lake required'}
[void][IO.Directory]::CreateDirectory($evidence)

function Get-R4Sha256File([string]$Path){return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()}
function Test-R4Order([string]$Text) {
  $tokens=$null;$errors=$null
  $ast=[Management.Automation.Language.Parser]::ParseInput($Text,[ref]$tokens,[ref]$errors)
  if(@($errors).Count){return [pscustomobject]@{ok=$false;reason='parse errors';blocks=@()}}
  $blocks=[Collections.Generic.List[object]]::new()
  foreach($try in @($ast.FindAll({param($n) $n -is [Management.Automation.Language.TryStatementAst] -and $null -ne $n.Finally},$true))){
    $release=@($try.Finally.FindAll({param($n) $n -is [Management.Automation.Language.InvokeMemberExpressionAst] -and $n.Member -is [Management.Automation.Language.StringConstantExpressionAst] -and $n.Member.Value -ceq 'ReleaseMutex'},$true))
    if($release.Count -eq 0){continue}
    $adds=@($try.Finally.FindAll({param($n) $n -is [Management.Automation.Language.InvokeMemberExpressionAst] -and $n.Member -is [Management.Automation.Language.StringConstantExpressionAst] -and $n.Member.Value -ceq 'Add' -and
      $n.Expression -is [Management.Automation.Language.VariableExpressionAst] -and $n.Expression.VariablePath.UserPath -ceq 'integrityErrors'},$true))
    $firstRelease=($release|ForEach-Object {$_.Extent.StartOffset}|Measure-Object -Minimum).Minimum
    $lastAdd=if($adds.Count){($adds|ForEach-Object {$_.Extent.StartOffset}|Measure-Object -Maximum).Maximum}else{$null}
    $releaseLine=($release|ForEach-Object {$_.Extent.StartLineNumber}|Measure-Object -Minimum).Minimum
    $addLine=if($adds.Count){($adds|ForEach-Object {$_.Extent.StartLineNumber}|Measure-Object -Maximum).Maximum}else{$null}
    $blocks.Add([ordered]@{finallyLine=$try.Finally.Extent.StartLineNumber;firstReleaseLine=$releaseLine;lastIntegrityAddLine=$addLine
      integrityAdds=$adds.Count;ok=($adds.Count -gt 0 -and $lastAdd -lt $firstRelease)})
  }
  $ok=$blocks.Count -gt 0 -and @($blocks|Where-Object {-not $_.ok}).Count -eq 0
  return [pscustomobject]@{ok=$ok;reason=$(if($blocks.Count -eq 0){'no finally block releases a mutex'}elseif($ok){'every integrity recording precedes release'}else{'a mutex is released before an integrity recording (or with none)'});blocks=@($blocks.ToArray())}
}
function Test-R3PinPredicate([object]$Fin,[bool]$IsP) {
  # Transcription of repair-r3/failure_controls.ps1 at d27ffa34, lines 466-468.
  $checks=@($Fin.pinChecks)
  if($IsP){return ($checks.Count -gt 0 -and @($checks|Where-Object {@('verified','absent-verified') -cnotcontains $_.status}).Count -eq 0)}
  return ($checks.Count -gt 0)
}
function New-R4Fin([object[]]$Rows,[int]$Count){
  return ([ordered]@{pinChecks=@($Rows);entryPinCount=$Count}|ConvertTo-Json -Depth 6|ConvertFrom-Json)
}
# Entry/final are untyped so a JSON null stays null ([string] would coerce it to '').
function Row([string]$Path,[object]$Entry,[object]$Final,[string]$Status){return [ordered]@{path=$Path;entrySha256=$Entry;finalSha256=$Final;status=$Status}}
$h1='1111111111111111111111111111111111111111111111111111111111111111'
$h2='2222222222222222222222222222222222222222222222222222222222222222'
$h3='3333333333333333333333333333333333333333333333333333333333333333'
$h4='4444444444444444444444444444444444444444444444444444444444444444'
$git40='aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'
$syntheticRoster=([ordered]@{rows=@('a','b','c');stages=[ordered]@{
  complete=[ordered]@{capturedIndexes=@(0,1,2)}
}}|ConvertTo-Json -Depth 8|ConvertFrom-Json)
$fileRoster=([ordered]@{rows=@('a');stages=[ordered]@{complete=[ordered]@{capturedIndexes=@(0)}}}|ConvertTo-Json -Depth 8|ConvertFrom-Json)
$gitRoster=([ordered]@{rows=@('git:HEAD');identityKinds=[ordered]@{'0'='git-sha1'};stages=[ordered]@{
  complete=[ordered]@{capturedIndexes=@(0)}
}}|ConvertTo-Json -Depth 8|ConvertFrom-Json)
$predCases=[ordered]@{
  'PRED-PIN-GOOD'=@{kind='pin';reason='captured 3 of 5 rows';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h4 'changed'),(Row 'c' $h3 $null 'unreadable-final'),(Row 'd' $null $null 'not-captured'),(Row 'e' $null $null 'absent-verified')) 3);captured=3;all=$false;r4=$true;isP=$false}
  'PRED-PIN-ROSTER-GOOD'=@{kind='pin';reason='captured 3 of 3 rows, all re-verified, exact roster stage complete';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified'),(Row 'c' $h3 $h3 'verified')) 3);captured=$null;all=$true;roster=$syntheticRoster;stage='complete';r4=$true;isP=$true}
  'PRED-PIN-GIT-GOOD'=@{kind='pin';reason='captured 1 of 1 rows, all re-verified, exact roster stage complete';fin=(New-R4Fin @((Row 'git:HEAD' $git40 $git40 'verified')) 1);captured=$null;all=$true;roster=$gitRoster;stage='complete';r4=$true;isP=$true}
  'PRED-PIN-FILE-SHA1'=@{kind='pin';reason='malformed captured SHA256: a';fin=(New-R4Fin @((Row 'a' $git40 $git40 'verified')) 1);captured=$null;all=$true;roster=$fileRoster;stage='complete';r4=$false;isP=$false}
  'PRED-PIN-GIT-SHA256'=@{kind='pin';reason='malformed captured Git SHA1: git:HEAD';fin=(New-R4Fin @((Row 'git:HEAD' $h1 $h1 'verified')) 1);captured=$null;all=$true;roster=$gitRoster;stage='complete';r4=$false;isP=$false}
  'PRED-PIN-LEGACY-GIT-GOOD'=@{kind='pin';reason='captured 1 of 1 rows, all re-verified';fin=(New-R4Fin @((Row 'git:HEAD' $git40 $git40 'verified')) 1);captured=$null;all=$true;r4=$true;isP=$true}
  'PRED-PIN-LEGACY-FILE-SHA1'=@{kind='pin';reason='malformed captured SHA256: a';fin=(New-R4Fin @((Row 'a' $git40 $git40 'verified')) 1);captured=$null;all=$true;r4=$false;isP=$false}
  'PRED-PIN-DROPPED'=@{kind='pin';reason='captured rows 2 differ from entryPinCount 3';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified'),(Row 'd' $null $null 'not-captured')) 3);captured=$null;all=$false;r4=$false;isP=$false}
  'PRED-PIN-COORDINATED'=@{kind='pin';reason='pinCheck roster count 2 differs from expected 3';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified')) 2);captured=$null;all=$false;roster=$syntheticRoster;stage='complete';r4=$false;isP=$false}
  'PRED-PIN-EMPTY'=@{kind='pin';reason='malformed captured SHA256: a';fin=(New-R4Fin @((Row 'a' '' $h1 'verified')) 1);captured=$null;all=$false;r4=$false;isP=$false}
  'PRED-PIN-NONHEX'=@{kind='pin';reason='malformed captured SHA256: a';fin=(New-R4Fin @((Row 'a' ('g'*64) $h1 'verified')) 1);captured=$null;all=$false;r4=$false;isP=$false}
  'PRED-PIN-ORDER'=@{kind='pin';reason='pinCheck path at roster index 0 differs: b';fin=(New-R4Fin @((Row 'b' $h2 $h2 'verified'),(Row 'a' $h1 $h1 'verified'),(Row 'c' $h3 $h3 'verified')) 3);captured=$null;all=$false;roster=$syntheticRoster;stage='complete';r4=$false;isP=$false}
  'PRED-PIN-UNVERIFIED'=@{kind='pin';reason='captured pin not re-verified: c status not-captured';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified'),(Row 'c' $h3 $null 'not-captured')) 3);captured=$null;all=$false;r4=$false;isP=$false}
  'PRED-PIN-COUNT'=@{kind='pin';reason='captured rows 3 differ from the registry count 4';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified'),(Row 'c' $h3 $h3 'verified')) 3);captured=4;all=$false;r4=$false;isP=$false}
  'PRED-PIN-DUP'=@{kind='pin';reason='duplicate pinCheck path a';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h2 'verified')) 3);captured=$null;all=$false;r4=$false;isP=$false}
  'PRED-PIN-ALLVERIFIED'=@{kind='pin';reason='captured pin not verified: b status changed';fin=(New-R4Fin @((Row 'a' $h1 $h1 'verified'),(Row 'b' $h2 $h4 'changed')) 2);captured=$null;all=$true;r4=$false;isP=$true}
}
$labelDoc=@{
  good=([ordered]@{entryHelper=@{path='x';bytes=1;sha256=$h1};helper=@{path='x';bytes=2;sha256=$h2};finalization=@{pinChecks=@((Row 'h' $h1 $h2 'changed'))}}|ConvertTo-Json -Depth 6|ConvertFrom-Json)
  entry=([ordered]@{helper=@{path='x';bytes=1;sha256=$h1};finalization=@{pinChecks=@((Row 'h' $h1 $h2 'changed'))}}|ConvertTo-Json -Depth 6|ConvertFrom-Json)
  stale=([ordered]@{entryHelper=@{path='x';bytes=1;sha256=$h1};helper=@{path='x';bytes=1;sha256=$h1};finalization=@{pinChecks=@((Row 'h' $h1 $h2 'changed'))}}|ConvertTo-Json -Depth 6|ConvertFrom-Json)
}
$labels=@([pscustomobject]@{key='helper';entryKey='entryHelper';path='h';status='changed'})
$predCases['PRED-LABEL-GOOD']=@{kind='label';doc=$labelDoc.good;r4=$true;reason='labels helper consistent'}
$predCases['PRED-LABEL-ENTRY']=@{kind='label';doc=$labelDoc.entry;r4=$false;reason='no entry label entryHelper'}
$predCases['PRED-LABEL-STALE']=@{kind='label';doc=$labelDoc.stale;r4=$false;reason='helper is not the post-run pin'}
$predCases['PRED-VALUE-GOOD']=@{kind='value';values=@([pscustomobject]@{name='TimedOut';value=$true},[pscustomobject]@{name='DeadlineSeconds';value=[long]3});r4=$true;reason='all values present'}
$predCases['PRED-VALUE-TYPE']=@{kind='value';values=@([pscustomobject]@{name='TimedOut';value='True'},[pscustomobject]@{name='DeadlineSeconds';value=[long]3});r4=$false;reason='no value TimedOut=True'}
$valueWant=@([pscustomobject]@{name='TimedOut';value=$true},[pscustomobject]@{name='DeadlineSeconds';value=[long]3})
$roster=@('ORD-K1','ORD-K2','ORD-RC','ORD-LV','HR-P','HR-W')+@($predCases.Keys)
if(($roster -join ',') -cne ($expectedIds -join ',')){throw 'R4-AUX: exact case roster differs'}

$records=[Collections.Generic.List[object]]::new()
$entryPins=[ordered]@{}
$stageError=$null;$stageRecord=$null;$completed=$false;$refSha=$null
$integrityErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$durableFailed=$false
try {
  . (Join-Path $repo 'scripts/owned_process_tree.ps1')
  foreach($p in @($PSCommandPath,(Join-Path $repo 'scripts/owned_process_tree.ps1'))){$entryPins[$p]=Get-R4Sha256File $p}
  $git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
  $work=Join-Path $evidence 'work'
  [void][IO.Directory]::CreateDirectory($work)
  $exportScript=Join-Path $work 'export.ps1'
  [IO.File]::WriteAllText($exportScript,@'
param([string]$Git,[string]$Root,[string]$Ref,[string]$Out,[string]$List)
$ErrorActionPreference='Stop'
$sha=(& $Git -C $Root rev-parse --verify ($Ref+'^{commit}')).Trim()
if($LASTEXITCODE -or $sha -cnotmatch '^[0-9a-f]{40}$'){throw 'ref resolution failed'}
[IO.File]::WriteAllText((Join-Path $Out 'ref.txt'),$sha,[Text.UTF8Encoding]::new($false))
foreach($rel in $List.Split(',')){
  & $Git -C $Root cat-file -e ($sha+':'+$rel) 2>$null
  if($LASTEXITCODE){continue}
  $p=[Diagnostics.Process]::new()
  $p.StartInfo.FileName=$Git
  $p.StartInfo.Arguments='-C "'+$Root+'" cat-file blob '+$sha+':'+$rel
  $p.StartInfo.UseShellExecute=$false
  $p.StartInfo.RedirectStandardOutput=$true
  $p.StartInfo.RedirectStandardError=$true
  $dest=Join-Path $Out ('blobs/'+$rel)
  [void][IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName($dest))
  $f=$null
  try {
    if(-not $p.Start()){throw 'git did not start'}
    $f=[IO.File]::Create($dest)
    $p.StandardOutput.BaseStream.CopyTo($f)
    $f.Dispose();$f=$null
    $err=$p.StandardError.ReadToEnd()
    $p.WaitForExit()
    if($p.ExitCode -ne 0 -or $err.Length -ne 0){throw ('blob export failed '+$rel+': '+$err)}
  } finally {if($null -ne $f){$f.Dispose()};$p.Dispose()}
}
'@,$utf8)
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $pwsh -Arguments @('-NoLogo','-NoProfile','-File',$exportScript,'-Git',$git,'-Root',$repo,'-Ref',$HarnessRef,'-Out',$work,'-List',(@($paths.Values) -join ',')) `
    -WorkingDirectory $repo -Stage 'aux-export' -DeadlineSeconds 120 -OutputLimitBytes 1048576 -TempRoot (Join-Path $work 'export-process')
  if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0){throw ('R4-AUX: blob export failed: '+(@($r.StandardError) -join ' | '))}
  $refSha=[IO.File]::ReadAllText((Join-Path $work 'ref.txt'),$utf8)
  function Get-Blob([string]$Key){$f=Join-Path $work ('blobs/'+$paths[$Key]);if([IO.File]::Exists($f)){return $f}else{return $null}}

  # ORD-*: static ordering on exact blobs.
  foreach($k in @('K1','K2','RC','LV')){
    $id='ORD-'+$k
    $blob=Get-Blob $k
    if($null -eq $blob){throw ('R4-AUX: blob missing at ref for '+$paths[$k])}
    $check=Test-R4Order ([IO.File]::ReadAllText($blob,$utf8))
    $want=if($Expect -ceq 'candidate' -or $k -ceq 'LV'){$true}else{$false}
    $records.Add([ordered]@{id=$id;path=$paths[$k];blobSha256=(Get-R4Sha256File $blob);observed=$check;expectedOk=$want;passed=([bool]$check.ok -eq $want)})
  }

  # HR-*: heavy_run.ps1 from the ref in a disposable root.
  $hr=Get-Blob 'HR'
  if($null -eq $hr){throw 'R4-AUX: heavy_run.ps1 missing at ref'}
  foreach($id in @('HR-P','HR-W')){
    $root=Join-Path $evidence ('cases/'+$id+'/root')
    $copy=Join-Path $root $paths.HR
    [void][IO.Directory]::CreateDirectory((Split-Path -Parent $copy))
    [IO.File]::WriteAllBytes($copy,[IO.File]::ReadAllBytes($hr))
    [void][IO.Directory]::CreateDirectory((Join-Path $root 'scripts'))
    [IO.File]::WriteAllBytes((Join-Path $root 'scripts/owned_process_tree.ps1'),[IO.File]::ReadAllBytes((Join-Path $repo 'scripts/owned_process_tree.ps1')))
    $out=Join-Path $root '.lake/hr-out'
    $command=if($id -ceq 'HR-W'){"[void][IO.Directory]::CreateDirectory('"+(Join-Path $out 'RESULT.json').Replace("'","''")+"'); exit 0"}else{'exit 0'}
    $spec=[ordered]@{name=$id.ToLowerInvariant();file=$pwsh;arguments=@('-NoLogo','-NoProfile','-Command',$command);cwd=$root;deadline=60
      mutexes=@();mutexWaitMilliseconds=1000;environment=@{};out=$out}
    $specPath=Join-Path $evidence ('cases/'+$id+'/spec.json')
    [IO.File]::WriteAllText($specPath,($spec|ConvertTo-Json -Depth 5),$utf8)
    $p=Invoke-RMQOwnedBoundedProcess -FilePath $pwsh -Arguments @('-NoLogo','-NoProfile','-File',$copy,'-SpecPath',$specPath) -WorkingDirectory $root `
      -Stage $id -DeadlineSeconds 120 -OutputLimitBytes 1048576 -TempRoot (Join-Path $evidence ('cases/'+$id+'/process'))
    $completedLaunch=-not $p.TimedOut -and -not $p.OutputLimitExceeded -and $p.Ownership -ceq 'kill-on-close-job' -and @($p.TerminatedIds).Count -eq 0
    $successLine=@(@($p.StandardOutput)|Where-Object {([string]$_).StartsWith('R3-HEAVY '+$spec.name+' exit=',[StringComparison]::Ordinal)}).Count -gt 0
    $writeFailed=@(@($p.StandardError)|Where-Object {([string]$_).Contains('RESULT.json write failed')}).Count -gt 0
    $resultFile=[IO.File]::Exists((Join-Path $out 'RESULT.json'))
    $defect=$p.ExitCode -eq 0 -and $successLine -and $writeFailed -and -not $resultFile
    $repaired=$p.ExitCode -ne 0 -and -not $successLine -and $writeFailed -and -not $resultFile
    $normal=$p.ExitCode -eq 0 -and $successLine -and -not $writeFailed -and $resultFile
    $ok=if($id -ceq 'HR-P'){$normal}elseif($Expect -ceq 'base'){$defect}else{$repaired}
    $records.Add([ordered]@{id=$id;heavyRunSha256=(Get-R4Sha256File $copy);process=$p;completedLaunch=$completedLaunch;successLine=$successLine;writeFailureReported=$writeFailed
      resultFileWritten=$resultFile;defectShape=$defect;repairedShape=$repaired;normalShape=$normal;passed=($completedLaunch -and $ok)})
  }

  # PRED-*: synthetic documents against the predicates at the ref.
  $pred=Get-Blob 'PR'
  if($null -ne $pred){. $pred}
  foreach($id in @($predCases.Keys)){
    $c=$predCases[$id]
    $r3=$null
    if($c.kind -ceq 'pin'){$r3=Test-R3PinPredicate $c.fin ([bool]$c.isP)}
    if($null -eq $pred){
      $records.Add([ordered]@{id=$id;predicatesAtRef=$false;r3PredicateAccepts=$r3;expectedR4=$c.r4;observedR4=$null;passed=($Expect -ceq 'base')})
      continue
    }
    $o=switch -CaseSensitive ($c.kind){
      'pin' {Test-R4PinCoverage $c.fin $c.captured ([bool]$c.all) $(if($c.ContainsKey('roster')){$c.roster}else{$null}) $(if($c.ContainsKey('stage')){$c.stage}else{$null})}
      'label' {Test-R4Labels $c.doc $labels}
      'value' {Test-R4Values @($c.values) $valueWant}
    }
    # The verdict and the exact first violated clause must both match, so a
    # rejection for an unintended reason (a malformed fixture) cannot pass.
    $reasonOk=([string]$o.reason).StartsWith([string]$c.reason,[StringComparison]::Ordinal)
    $records.Add([ordered]@{id=$id;predicatesAtRef=$true;predicatesSha256=(Get-R4Sha256File $pred);r3PredicateAccepts=$r3;expectedR4=$c.r4;expectedReason=$c.reason
      observedR4=$o;reasonMatches=$reasonOk;passed=([bool]$o.ok -eq [bool]$c.r4 -and $reasonOk)})
  }
  foreach($rec in $records){Write-Output ('R4 AUX '+$rec.id+' '+$(if($rec.passed){'PASS'}else{'FAIL'}))}
  if($records.Count -ne $expectedIds.Count -or ((@($records|ForEach-Object {$_.id}) -join ',') -cne ($expectedIds -join ','))){throw 'R4-AUX: executed cases differ from the roster'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  foreach($p in $entryPins.Keys){
    $final=$null;$status='verified'
    try{$final=Get-R4Sha256File $p;if($final -cne $entryPins[$p]){$status='changed';$integrityErrors.Add('R4-AUX-INTEGRITY: input changed '+$p)}}
    catch{$status='unreadable-final';$integrityErrors.Add('R4-AUX-INTEGRITY: final hash failed '+$p+': '+$_.Exception.Message)}
    $pinChecks.Add([ordered]@{path=$p;entrySha256=$entryPins[$p];finalSha256=$final;status=$status})
  }
  $failed=@($records|Where-Object {-not $_.passed})
  $verdict=if($completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $failed.Count -eq 0){'pass'}else{'fail'}
  $summary=[ordered]@{schema='life1-r4-aux-controls-v1';harnessRef=$HarnessRef;harnessSha=$refSha;expect=$Expect
    runnerShell=(Get-Process -Id $PID).Path;psVersion=$PSVersionTable.PSVersion.ToString()
    expectedCount=$expectedIds.Count;executedCount=$records.Count;passedCount=($records.Count-$failed.Count);failedIds=@($failed|ForEach-Object {$_.id})
    cases=@($records.ToArray())
    finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$verdict;stageError=$stageError;integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@();pinChecks=@($pinChecks.ToArray())}}
  try{[IO.File]::WriteAllText((Join-Path $evidence 'RESULT.json'),($summary|ConvertTo-Json -Depth 30),$utf8)}
  catch{$durableFailed=$true;$verdict='fail';[Console]::Error.WriteLine('R4-AUX: durable result write failed: '+$_.Exception.Message)}
}
foreach($e in $integrityErrors){[Console]::Error.WriteLine($e)}
if($null -ne $stageRecord){throw $stageRecord}
Write-Output ('R4 AUX '+$verdict.ToUpperInvariant()+' expect='+$Expect+' ref='+$refSha+' executed='+$records.Count+' expected='+$expectedIds.Count+' evidence='+$evidence)
if($verdict -cne 'pass'){exit 1}
exit 0

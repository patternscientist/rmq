[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][string]$HarnessRef,
  [Parameter(Mandatory=$true)][ValidateSet('defect','repaired')][string]$Expect,
  [string]$OutputRoot
)
# LIFE-1-R4 committed reproduction probe for audit P2-1 (both run_check.ps1
# files record verdict "pass" when the child stage fails or times out), plus the
# cheap reproductions of P3-1 (a failed durable write still exits 0) and P3-3
# (the validator's pinned-executable check runs before its evidence root).
#
# Each case copies the exact harness blob of -HarnessRef into a disposable
# git-initialized root under this worktree's .lake, adds the unchanged owned-
# process helper and a one-line stage, launches the WHOLE harness file through
# scripts/owned_process_tree.ps1 with a positive deadline, and reads its durable
# result. `defectPresent` is the audited defect's observable and `repairedShape`
# the repaired observable; -Expect names the one every case must show (defect at
# the base, repaired at the R4 tip). The case list is exact and ordered; the
# probe has no selector, so it always runs the whole list.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$here=$PSScriptRoot
$repo=[IO.Path]::GetFullPath((Join-Path $here '../../../../..'))
if($PSVersionTable.PSVersion.Major -lt 7){throw 'R4-PROBE: PowerShell 7 required'}
$pwsh='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
$k1='docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1'
$k2='docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1'
$lv='scripts/lifecycle_validator.ps1'
$cases=@(
  [ordered]@{id='P21-K1-EXIT';finding='P2-1';harness=$k1;kind='k';stage='exit 7';deadline=60}
  [ordered]@{id='P21-K2-EXIT';finding='P2-1';harness=$k2;kind='k';stage='exit 7';deadline=60}
  [ordered]@{id='P21-K1-TIMEOUT';finding='P2-1';harness=$k1;kind='k';stage='Start-Sleep -Seconds 30; exit 0';deadline=3}
  [ordered]@{id='P21-K2-TIMEOUT';finding='P2-1';harness=$k2;kind='k';stage='Start-Sleep -Seconds 30; exit 0';deadline=3}
  [ordered]@{id='P31-K2-WRITE';finding='P3-1';harness=$k2;kind='k';stage='block';deadline=60}
  [ordered]@{id='P33-LV-EXE';finding='P3-3';harness=$lv;kind='lv';stage=$null;deadline=$null}
)
$expectedIds=@('P21-K1-EXIT','P21-K2-EXIT','P21-K1-TIMEOUT','P21-K2-TIMEOUT','P31-K2-WRITE','P33-LV-EXE')
if((@($cases|ForEach-Object {$_.id}) -join ',') -cne ($expectedIds -join ',')){throw 'R4-PROBE: exact case roster differs'}
if([string]::IsNullOrWhiteSpace($OutputRoot)){$OutputRoot=Join-Path $repo ('.lake/life1-r4/probe-'+$Expect+'-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($OutputRoot)
$lakePrefix=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($lakePrefix,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'R4-PROBE: fresh owned descendant of .lake required'}
[void][IO.Directory]::CreateDirectory($evidence)

function Get-R4Sha256File([string]$Path){return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()}
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
param([string]$Git,[string]$Root,[string]$Ref,[string]$Out)
$ErrorActionPreference='Stop'
$sha=(& $Git -C $Root rev-parse --verify ($Ref+'^{commit}')).Trim()
if($LASTEXITCODE -or $sha -cnotmatch '^[0-9a-f]{40}$'){throw 'ref resolution failed'}
[IO.File]::WriteAllText((Join-Path $Out 'ref.txt'),$sha,[Text.UTF8Encoding]::new($false))
foreach($rel in @('docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1','docs/internal/extensions/lifecycle1/repair-r2/run_check.ps1','scripts/lifecycle_validator.ps1')){
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
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $pwsh -Arguments @('-NoLogo','-NoProfile','-File',$exportScript,'-Git',$git,'-Root',$repo,'-Ref',$HarnessRef,'-Out',$work) `
    -WorkingDirectory $repo -Stage 'probe-export' -DeadlineSeconds 120 -OutputLimitBytes 1048576 -TempRoot (Join-Path $work 'export-process')
  if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0){throw ('R4-PROBE: blob export failed: '+(@($r.StandardError) -join ' | '))}
  $refSha=[IO.File]::ReadAllText((Join-Path $work 'ref.txt'),$utf8)
  $setup=Join-Path $work 'git-setup.ps1'
  [IO.File]::WriteAllText($setup,@'
param([string]$Git,[string]$Root)
$ErrorActionPreference='Stop'
& $Git -C $Root init -q; if($LASTEXITCODE){throw 'git init failed'}
& $Git -C $Root config core.autocrlf false; if($LASTEXITCODE){throw 'git config failed'}
& $Git -C $Root -c core.excludesfile= add --all; if($LASTEXITCODE){throw 'git add failed'}
& $Git -C $Root -c user.name=RMQR4Probe -c user.email=probe@invalid commit -qm r4-probe-baseline; if($LASTEXITCODE){throw 'git commit failed'}
'@,$utf8)
  foreach($case in $cases){
    $root=Join-Path $evidence ('cases/'+$case.id+'/root')
    $harness=Join-Path $root $case.harness
    [void][IO.Directory]::CreateDirectory((Split-Path -Parent $harness))
    [IO.File]::WriteAllBytes($harness,[IO.File]::ReadAllBytes((Join-Path $work ('blobs/'+$case.harness))))
    [void][IO.Directory]::CreateDirectory((Join-Path $root 'scripts'))
    [IO.File]::WriteAllBytes((Join-Path $root 'scripts/owned_process_tree.ps1'),[IO.File]::ReadAllBytes((Join-Path $repo 'scripts/owned_process_tree.ps1')))
    [IO.File]::WriteAllText((Join-Path $root '.gitignore'),".lake/`n",$utf8)
    $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$harness)
    $durableDir=$null
    if($case.kind -ceq 'k'){
      $check=if($case.harness -ceq $k1){'.lake/repair-r1/checks/probe'}else{'.lake/repair-r2/checks/probe'}
      $durableDir=Join-Path $root $check
      $stagePath=Join-Path $root 'probe-stage.ps1'
      $stageText=if($case.stage -ceq 'block'){"[void][IO.Directory]::CreateDirectory('"+(Join-Path $durableDir 'result.json').Replace("'","''")+"'); exit 0"}else{$case.stage}
      [IO.File]::WriteAllText($stagePath,$stageText,$utf8)
      $spec=[ordered]@{name='probe';file=$pwsh;arguments=@('-NoLogo','-NoProfile','-File',$stagePath);mutex=$false;deadline=[int]$case.deadline}
      [IO.File]::WriteAllText((Join-Path $root 'probe-spec.json'),($spec|ConvertTo-Json -Depth 5),$utf8)
      $arguments+=@('-SpecPath',(Join-Path $root 'probe-spec.json'))
    } else {
      $arguments+=@('-Stage','startup')
    }
    $s=Invoke-RMQOwnedBoundedProcess -FilePath $pwsh -Arguments @('-NoLogo','-NoProfile','-File',$setup,'-Git',$git,'-Root',$root) -WorkingDirectory $root `
      -Stage ('setup-'+$case.id) -DeadlineSeconds 120 -OutputLimitBytes 1048576 -TempRoot (Join-Path $evidence ('cases/'+$case.id+'/setup-process'))
    if($s.TimedOut -or $s.OutputLimitExceeded -or $s.ExitCode -ne 0){throw ('R4-PROBE: disposable git baseline failed for '+$case.id)}
    $p=Invoke-RMQOwnedBoundedProcess -FilePath $pwsh -Arguments $arguments -WorkingDirectory $root -Stage $case.id `
      -DeadlineSeconds 120 -OutputLimitBytes 8388608 -TempRoot (Join-Path $evidence ('cases/'+$case.id+'/process'))
    $completedLaunch=-not $p.TimedOut -and -not $p.OutputLimitExceeded -and $p.Ownership -ceq 'kill-on-close-job' -and @($p.TerminatedIds).Count -eq 0
    $durable=$null;$doc=$null
    if($case.kind -ceq 'k'){
      $c=Join-Path $durableDir 'result.json'
      if([IO.File]::Exists($c)){$durable=$c}
    } else {
      $lvRoot=Join-Path $root '.lake/lifecycle-validator'
      $found=@(if([IO.Directory]::Exists($lvRoot)){Get-ChildItem -LiteralPath $lvRoot -Recurse -File -Filter 'RESULT.json'})
      if($found.Count -eq 1){$durable=$found[0].FullName}elseif($found.Count -gt 1){throw 'R4-PROBE: ambiguous validator result'}
    }
    if($null -ne $durable){$doc=[IO.File]::ReadAllText($durable,$utf8)|ConvertFrom-Json}
    $fin=$null;if($null -ne $doc -and $null -ne $doc.PSObject.Properties['finalization']){$fin=$doc.finalization}
    $verdict=if($null -ne $fin){[string]$fin.verdict}else{$null}
    $childFailure=if($null -ne $fin -and $null -ne $fin.PSObject.Properties['childFailure']){$fin.childFailure}else{$null}
    $timedOut=if($null -ne $doc -and $null -ne $doc.PSObject.Properties['result'] -and $null -ne $doc.result){[bool]$doc.result.TimedOut}else{$null}
    $stderr=@($p.StandardError) -join "`n"
    $defect=switch -CaseSensitive ($case.id){
      'P21-K1-EXIT' {$null -ne $doc -and $verdict -ceq 'pass' -and $null -ne $childFailure -and $p.ExitCode -eq 7}
      'P21-K2-EXIT' {$null -ne $doc -and $verdict -ceq 'pass' -and $null -ne $childFailure -and $p.ExitCode -eq 7}
      'P21-K1-TIMEOUT' {$null -ne $doc -and $verdict -ceq 'pass' -and $timedOut -eq $true -and $p.ExitCode -eq 2}
      'P21-K2-TIMEOUT' {$null -ne $doc -and $verdict -ceq 'pass' -and $timedOut -eq $true -and $p.ExitCode -eq 2}
      'P31-K2-WRITE' {$p.ExitCode -eq 0 -and $null -eq $doc -and $stderr.Contains('durable result write failed')}
      'P33-LV-EXE' {$p.ExitCode -ne 0 -and $null -eq $doc}
    }
    $repaired=switch -CaseSensitive ($case.id){
      {$_ -in @('P21-K1-EXIT','P21-K2-EXIT')} {$null -ne $doc -and $verdict -ceq 'fail' -and $null -ne $childFailure -and $p.ExitCode -eq 7}
      {$_ -in @('P21-K1-TIMEOUT','P21-K2-TIMEOUT')} {$null -ne $doc -and $verdict -ceq 'fail' -and $timedOut -eq $true -and $p.ExitCode -eq 2 -and [int]$doc.result.DeadlineSeconds -eq 3}
      'P31-K2-WRITE' {$p.ExitCode -ne 0 -and $null -eq $doc -and $stderr.Contains('durable result write failed')}
      'P33-LV-EXE' {$p.ExitCode -ne 0 -and $null -ne $doc -and [string]$doc.finalization.stageError -like 'Missing rmq_lifecycle_validate.exe*' -and $doc.finalization.verdict -ceq 'fail'}
    }
    $observed=if($Expect -ceq 'defect'){[bool]$defect}else{[bool]$repaired}
    $record=[ordered]@{id=$case.id;finding=$case.finding;harness=$case.harness;harnessSha256=(Get-R4Sha256File $harness);stage=$case.stage;deadline=$case.deadline
      process=$p;completedLaunch=$completedLaunch;durable=$durable;durableSha256=$(if($null -ne $durable){Get-R4Sha256File $durable}else{$null})
      verdict=$verdict;childFailure=$childFailure;resultTimedOut=$timedOut;defectPresent=[bool]$defect;repairedShape=[bool]$repaired
      expect=$Expect;passed=($completedLaunch -and $observed)}
    $records.Add($record)
    [IO.File]::WriteAllText((Join-Path $evidence ('cases/'+$case.id+'/CASE.json')),($record|ConvertTo-Json -Depth 30),$utf8)
    Write-Output ('R4 PROBE '+$case.id+' defectPresent='+[bool]$defect+' repairedShape='+[bool]$repaired+' '+$(if($record.passed){'PASS'}else{'FAIL'}))
  }
  if($records.Count -ne $cases.Count){throw 'R4-PROBE: executed case count differs'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  foreach($p in $entryPins.Keys){
    $final=$null;$status='verified'
    try{$final=Get-R4Sha256File $p;if($final -cne $entryPins[$p]){$status='changed';$integrityErrors.Add('R4-PROBE-INTEGRITY: input changed '+$p)}}
    catch{$status='unreadable-final';$integrityErrors.Add('R4-PROBE-INTEGRITY: final hash failed '+$p+': '+$_.Exception.Message)}
    $pinChecks.Add([ordered]@{path=$p;entrySha256=$entryPins[$p];finalSha256=$final;status=$status})
  }
  $failed=@($records|Where-Object {-not $_.passed})
  $verdict=if($completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $failed.Count -eq 0){'pass'}else{'fail'}
  $summary=[ordered]@{schema='life1-r4-base-probe-v1';harnessRef=$HarnessRef;harnessSha=$refSha;expect=$Expect
    runnerShell=(Get-Process -Id $PID).Path;psVersion=$PSVersionTable.PSVersion.ToString()
    expectedCount=$cases.Count;executedCount=$records.Count;passedCount=($records.Count-$failed.Count);failedIds=@($failed|ForEach-Object {$_.id})
    cases=@($records.ToArray())
    finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$verdict;stageError=$stageError;integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@();pinChecks=@($pinChecks.ToArray())}}
  try{[IO.File]::WriteAllText((Join-Path $evidence 'RESULT.json'),($summary|ConvertTo-Json -Depth 30),$utf8)}
  catch{$durableFailed=$true;[Console]::Error.WriteLine('R4-PROBE: durable result write failed: '+$_.Exception.Message)}
}
foreach($e in $integrityErrors){[Console]::Error.WriteLine($e)}
if($null -ne $stageRecord){throw $stageRecord}
if($durableFailed){exit 1}
Write-Output ('R4 PROBE '+$verdict.ToUpperInvariant()+' expect='+$Expect+' ref='+$refSha+' executed='+$records.Count+' expected='+$cases.Count+' evidence='+$evidence)
if($verdict -cne 'pass'){exit 1}
exit 0

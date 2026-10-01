[CmdletBinding()]
param([string]$OutputRoot,[ValidateSet('v1','v2')][string]$RegistryVersion='v1')
# LIFE-1-R3 selector and registry controls for failure_controls.ps1. Each case
# launches a driver that calls the actual runner script with the exact parameter
# binding under test, through the unchanged owned-process helper with a positive
# deadline, and checks the exact exit and diagnostic. Registry mutations are
# written only to owned copies under this run's evidence directory. The case list
# is exact and ordered; a lost or extra case fails the run.
# LIFE-1-R4: -RegistryVersion v2 runs the same fifteen cases against the R4 v2
# registry (repair-r4/FAILURE_CONTROL_REGISTRY.json), passed explicitly with
# -RegistryPath because the runner's default registry stays the R3 v1 one; v1
# (the default) is the unchanged R3 behaviour.
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$here=$PSScriptRoot
$repo=[IO.Path]::GetFullPath((Join-Path $here '../../../../..'))
$runner=Join-Path $here 'failure_controls.ps1'
$registryPath=if($RegistryVersion -ceq 'v2'){[IO.Path]::GetFullPath((Join-Path $here '../repair-r4/FAILURE_CONTROL_REGISTRY.json'))}else{Join-Path $here 'FAILURE_CONTROL_REGISTRY.json'}
if($PSVersionTable.PSVersion.Major -lt 7){throw 'R3-RUNTIME: PowerShell 7 required'}
if([string]::IsNullOrWhiteSpace($OutputRoot)){$OutputRoot=Join-Path $repo ('.lake/life1-r3/selector-controls-'+[Guid]::NewGuid().ToString('N'))}
$evidence=[IO.Path]::GetFullPath($OutputRoot)
$lakePrefix=[IO.Path]::GetFullPath((Join-Path $repo '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
if(-not $evidence.StartsWith($lakePrefix,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $evidence)){throw 'R3-EVIDENCE: fresh owned descendant of .lake required'}
[void][IO.Directory]::CreateDirectory($evidence)

$allPwsh='R3 SELECT RC-P,RC-C,RC-Q,RC-S,RC-M,FC-P,FC-C,FC-Q,FC-S,FC-M,K1-P,K1-C,K1-Q,K1-S,K1-M,K1-X,K2-P,K2-C,K2-Q,K2-S,K2-M,DC-P,DC-C,DC-Q,DC-S,DC-M,LV-P,LV-C,LV-Q,LV-S,LV-M,IC-P,IC-C,IC-Q,IC-S,IC-M,DP-P,DP-C,DP-Q,DP-S,DP-M,HS-P,HS-C,HS-Q,HS-S,HS-M,HS-R'
$validPick='K1-P'
if($RegistryVersion -ceq 'v2'){$allPwsh+=',K1-F,K2-F,K1-T,K2-T,K1-W,K2-W,LV-W,IC-U,LV-E,IC-L,HS-L,K2-G,HS-G';$validPick='K1-F'}
$cases=@(
  [ordered]@{id='SEL-01-OMITTED';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry=$null;exit=0;stdout=$allPwsh;stderr=''}
  [ordered]@{id='SEL-02-VALID';args=("-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl '"+$validPick+"'");registry=$null;exit=0;stdout=('R3 SELECT '+$validPick);stderr=''}
  [ordered]@{id='SEL-03-EMPTY-STRING';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl ''";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: empty or whitespace selector'}
  [ordered]@{id='SEL-04-EMPTY-ARRAY';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl @()";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: explicitly empty selector'}
  [ordered]@{id='SEL-05-WHITESPACE';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl ' '";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: empty or whitespace selector'}
  [ordered]@{id='SEL-06-MALFORMED';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl 'k1-p'";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: malformed selector'}
  [ordered]@{id='SEL-07-UNKNOWN';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl 'ZZ-P'";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: unknown selector'}
  [ordered]@{id='SEL-08-DUPLICATE';args="-HarnessRef base -Profile pwsh -ProbeOnly -OnlyControl 'K1-P','K1-P'";registry=$null;exit=1;stdout='';stderr='R3-SELECTOR: duplicate selector'}
  [ordered]@{id='REG-09-EXACT-COPY';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='exact-copy';exit=0;stdout=$allPwsh;stderr=''}
  [ordered]@{id='REG-10-MISSING-MIDDLE';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='missing-middle';exit=1;stdout='';stderr='R3-REGISTRY: missing ID DC-P'}
  [ordered]@{id='REG-11-DUPLICATE-MIDDLE';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='duplicate-middle';exit=1;stdout='';stderr='R3-REGISTRY: duplicate ID DC-P'}
  [ordered]@{id='REG-12-UNKNOWN-MIDDLE';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='unknown-middle';exit=1;stdout='';stderr='R3-REGISTRY: unknown ID ZZ-Z'}
  [ordered]@{id='REG-13-REORDERED';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='reordered';exit=1;stdout='';stderr='R3-REGISTRY: reordered IDs'}
  [ordered]@{id='REG-14-BYTE-DRIFT';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='byte-drift';exit=1;stdout='';stderr='R3-REGISTRY: registry bytes differ from the pinned version'}
  [ordered]@{id='REG-15-EMPTY';args="-HarnessRef base -Profile pwsh -ProbeOnly";registry='empty';exit=1;stdout='';stderr='R3-REGISTRY: empty registry'}
)
$expectedIds=@('SEL-01-OMITTED','SEL-02-VALID','SEL-03-EMPTY-STRING','SEL-04-EMPTY-ARRAY','SEL-05-WHITESPACE','SEL-06-MALFORMED',
  'SEL-07-UNKNOWN','SEL-08-DUPLICATE','REG-09-EXACT-COPY','REG-10-MISSING-MIDDLE','REG-11-DUPLICATE-MIDDLE',
  'REG-12-UNKNOWN-MIDDLE','REG-13-REORDERED','REG-14-BYTE-DRIFT','REG-15-EMPTY')
if((@($cases|ForEach-Object {$_.id}) -join ',') -cne ($expectedIds -join ',')){throw 'R3-SELECTOR-CONTROLS: exact case roster differs'}

function Get-R3Sha256File([string]$Path) {return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()}
$records=[Collections.Generic.List[object]]::new()
$stageError=$null;$stageRecord=$null;$completed=$false
$integrityErrors=[Collections.Generic.List[string]]::new()
$pinChecks=[Collections.Generic.List[object]]::new()
$entryPins=[ordered]@{}
$durableFailed=$false
try {
  . (Join-Path $repo 'scripts/owned_process_tree.ps1')
  foreach($p in @($runner,$registryPath,$PSCommandPath)){$entryPins[$p]=Get-R3Sha256File $p}
  $registryText=[IO.File]::ReadAllText($registryPath,$utf8)
  foreach($case in $cases){
    $out=Join-Path $evidence $case.id
    [void][IO.Directory]::CreateDirectory($out)
    $registryArg=''
    if($null -ne $case.registry){
      $copy=Join-Path $out 'registry.json'
      if($case.registry -ceq 'exact-copy'){[IO.File]::Copy($registryPath,$copy)}
      elseif($case.registry -ceq 'byte-drift'){
        $anchor='"rationale": "Intact harness with a passing injected stage; expected accept control."'
        if($registryText.IndexOf($anchor,[StringComparison]::Ordinal) -lt 0){throw 'R3-SELECTOR-CONTROLS: byte-drift anchor absent'}
        [IO.File]::WriteAllText($copy,$registryText.Replace($anchor,$anchor.Replace('control.','control. ')),$utf8)
      } else {
        $doc=$registryText|ConvertFrom-Json
        $list=[Collections.Generic.List[object]]::new()
        foreach($c in $doc.controls){$list.Add($c)}
        $mid=-1;for($i=0;$i -lt $list.Count;$i++){if($list[$i].id -ceq 'DC-P'){$mid=$i}}
        if($mid -lt 1 -or $mid -ge $list.Count-1){throw 'R3-SELECTOR-CONTROLS: middle anchor absent'}
        switch -CaseSensitive ($case.registry){
          'missing-middle' {$list.RemoveAt($mid)}
          'duplicate-middle' {$list[$mid+1]=($list[$mid+1]|ConvertTo-Json -Depth 20|ConvertFrom-Json);$list[$mid+1].id='DC-P'}
          'unknown-middle' {$extra=($list[$mid]|ConvertTo-Json -Depth 20|ConvertFrom-Json);$extra.id='ZZ-Z';$list.Insert($mid+1,$extra)}
          'reordered' {$a=$list[$mid];$list[$mid]=$list[$mid+1];$list[$mid+1]=$a}
          'empty' {$list.Clear()}
          default {throw 'R3-SELECTOR-CONTROLS: unknown registry mutation'}
        }
        $doc.controls=@($list.ToArray())
        [IO.File]::WriteAllText($copy,($doc|ConvertTo-Json -Depth 20),$utf8)
      }
      $registryArg=" -RegistryPath '"+$copy.Replace("'","''")+"'"
    } elseif($RegistryVersion -ceq 'v2') {$registryArg=" -RegistryPath '"+$registryPath.Replace("'","''")+"'"}
    # Each case names an explicit, not-yet-existing runner evidence root; a
    # validation rejection or probe must leave it absent (nothing executed).
    $runnerEvidence=Join-Path $out 'runner-evidence'
    $registryArg+=" -OutputRoot '"+$runnerEvidence.Replace("'","''")+"'"
    $driver=Join-Path $out 'driver.ps1'
    [IO.File]::WriteAllText($driver,("`$ErrorActionPreference='Stop'`ntry {& '"+$runner.Replace("'","''")+"' "+$case.args+$registryArg+"`nexit `$LASTEXITCODE}catch{[Console]::Error.WriteLine(`$_.Exception.Message);exit 1}"),$utf8)
    $r=Invoke-RMQOwnedBoundedProcess -FilePath (Get-Process -Id $PID).Path -Arguments @('-NoLogo','-NoProfile','-File',$driver) -WorkingDirectory $repo `
      -Stage $case.id -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot (Join-Path $out 'process')
    $stdout=@($r.StandardOutput) -join "`n"
    $stderr=@($r.StandardError) -join "`n"
    $noEvidenceCreated=-not (Test-Path -LiteralPath $runnerEvidence)
    $passed=$noEvidenceCreated -and (-not $r.TimedOut) -and (-not $r.OutputLimitExceeded) -and $r.Ownership -ceq 'kill-on-close-job' -and @($r.TerminatedIds).Count -eq 0 -and
      $r.ExitCode -eq $case.exit -and $stdout -ceq $case.stdout -and $stderr -ceq $case.stderr
    $record=[ordered]@{id=$case.id;arguments=$case.args;registryMutation=$case.registry;expectedExit=$case.exit;expectedStdout=$case.stdout;expectedStderr=$case.stderr
      process=$r;noControlEvidenceCreated=$noEvidenceCreated;passed=$passed}
    $records.Add($record)
    Write-Output ('R3 SELECTOR CONTROL '+$case.id+' '+$(if($passed){'PASS'}else{'FAIL'}))
  }
  if($records.Count -ne $cases.Count){throw 'R3-SELECTOR-CONTROLS: executed case count differs'}
  $completed=$true
} catch {$stageError=$_.Exception.Message;$stageRecord=$_}
finally {
  foreach($p in $entryPins.Keys){
    $final=$null;$status='verified'
    try{$final=Get-R3Sha256File $p;if($final -cne $entryPins[$p]){$status='changed';$integrityErrors.Add('R3-INTEGRITY: input changed '+$p)}}
    catch{$status='unreadable-final';$integrityErrors.Add('R3-INTEGRITY: final hash failed '+$p+': '+$_.Exception.Message)}
    $pinChecks.Add([ordered]@{path=$p;entrySha256=$entryPins[$p];finalSha256=$final;status=$status})
  }
  $failed=@($records|Where-Object {-not $_.passed})
  $verdict=if($completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $failed.Count -eq 0){'pass'}else{'fail'}
  $summary=[ordered]@{schema='life1-r3-selector-controls-v1';registryVersion=$RegistryVersion;registryPath=$registryPath;expectedCount=$cases.Count;executedCount=$records.Count
    passedCount=($records.Count-$failed.Count);failedIds=@($failed|ForEach-Object {$_.id});cases=@($records.ToArray())
    finalization=[ordered]@{schema='life1-r3-finalization-v1';verdict=$verdict;stageError=$stageError;integrityErrors=@($integrityErrors.ToArray());cleanupErrors=@();pinChecks=@($pinChecks.ToArray())}}
  try{[IO.File]::WriteAllText((Join-Path $evidence 'RESULT.json'),($summary|ConvertTo-Json -Depth 30),$utf8)}
  catch{$durableFailed=$true;$verdict='fail';[Console]::Error.WriteLine('R3-SELECTOR-CONTROLS: durable result write failed: '+$_.Exception.Message)}
}
foreach($e in $integrityErrors){[Console]::Error.WriteLine($e)}
if($null -ne $stageRecord){throw $stageRecord}
Write-Output ('R3 SELECTOR CONTROLS '+$verdict.ToUpperInvariant()+' executed='+$records.Count+' expected='+$cases.Count+' evidence='+$evidence)
if($verdict -cne 'pass'){exit 1}
exit 0

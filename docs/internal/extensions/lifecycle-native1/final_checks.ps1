[CmdletBinding()]
param([switch]$Committed)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $root 'scripts/lifecycle_native_identity.ps1')
. (Join-Path $PSScriptRoot 'final_streams.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$base='3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536'
$run=Join-Path $root ('.lake/lifecycle-native1/final-checks/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$pins=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$shell=(Get-Process -Id $PID).Path
$git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
$rg=(Get-Command rg -CommandType Application|Select-Object -First 1).Source
$report=[ordered]@{schema='lifecycle-native1-final-checks-v1';success=$false;base=$base;
  committed=[bool]$Committed;head=$null;startedUtc=[DateTime]::UtcNow.ToString('o');
  deadlineSeconds=600;deadlineRationale='Measured current scope91.142s and full83-path strict claim scan178.106s; final frozen diagnostic JSON adds scan input. Reserve600seconds per checker for this larger final surface, without changing the scanner/policy or adding Lean/native work.';
  claimPaths=@();pins=@();stages=@();failure=$null;integrity=$null;cleanup=$null}
function Pin-Final([string]$Path){$p=Get-LN1Pin $Path;$pins.Add($p);return $p}
function Run-Final([string]$Name,[string]$File,[string[]]$Arguments,[int]$ExpectedExit=0){
  $capture=Invoke-LNStreamCapture $root $File $Arguments $root (Join-Path $run $Name) $report.deadlineSeconds $Name
  $stages.Add(@{name=$Name;file=$File;arguments=$Arguments;capture=$capture})
  foreach($p in $capture.raw){[void](Pin-Final $p.path)}
  $stdout=Read-LNExactStream $capture.spec.stdout
  $stderr=Read-LNExactStream $capture.spec.stderr
  Assert-LNOuterCapture $capture $stdout $stderr $ExpectedExit $Name
  return $capture
}
function Git-Final([string]$Name,[string[]]$Arguments){
  $c=Run-Final $Name $git (@('-c','core.excludesfile=','-c','core.safecrlf=false')+$Arguments)
  if(-not [StringComparer]::Ordinal.Equals((Read-LNExactStream $c.spec.stderr),'')){throw ('FINAL-CHECKS: unexpected Git stderr '+$Name)}
  return Read-LNExactStream $c.spec.stdout
}
function Git-EmptyFinal([string]$Name,[string[]]$Arguments){
  $c=Run-Final $Name $git (@('-c','core.excludesfile=','-c','core.safecrlf=false')+$Arguments)
  Assert-LNOuterCapture $c '' '' 0 $Name
}
try{
  foreach($p in @($PSCommandPath,$shell,$git,$rg,
      (Join-Path $root 'scripts/lifecycle_native_identity.ps1'),
      (Join-Path $root 'scripts/owned_process_tree.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'),
      (Join-Path $root 'scripts/packed_native_lifecycle_integrity_check.ps1'),
      (Join-Path $root 'scripts/claim_drift_scan.ps1'),
      (Join-Path $root 'docs/internal/CLAIM_DRIFT_POLICY.json'),
      (Join-Path $root 'scripts/design_decision_check.ps1'),
      (Join-Path $PSScriptRoot 'scope_check.ps1'),
      (Join-Path $PSScriptRoot 'final_streams.ps1'))){[void](Pin-Final $p)}
  $report.head=(Git-Final 'head' @('rev-parse','HEAD')).Trim()
  $changed=(Git-Final 'changed' @('diff','--name-only','-z',$base)) -split [char]0|Where-Object{$_}
  $new=(Git-Final 'new' @('ls-files','--others','--exclude-standard','-z')) -split [char]0|Where-Object{$_}
  $paths=@(@($changed)+@($new)|Sort-Object -Unique)
  if($paths.Count -eq 0){throw 'FINAL-CHECKS: vacuous changed surface'}
  foreach($p in $paths){[void](Pin-Final (Join-Path $root $p))}
  $report.claimPaths=$paths
  # The scanner receives an actual structured array, including process records
  # and exact frozen JSON evidence. No renamed/omitted allowance surface.
  $quoted=@($paths|ForEach-Object{"'"+$_.Replace("'","''")+"'"}) -join ",`n"
  $driver=Join-Path $run 'claims-driver.ps1'
  $body="`$paths=@(`n"+$quoted+"`n)`n& './scripts/claim_drift_scan.ps1' -Strict -IncludeProcessRecords -Path `$paths`nexit `$LASTEXITCODE`n"
  [IO.File]::WriteAllText($driver,$body,$utf8);[void](Pin-Final $driver)
  $scope=Run-Final 'scope' $shell @('-NoProfile','-File',(Join-Path $PSScriptRoot 'scope_check.ps1'))
  $report.scope=Assert-LNFinalScope $scope $root $base $report.head $paths
  foreach($p in @($report.scope.pin)+@($report.scope.pins)){
    $now=Pin-Final $p.path
    if($now.bytes -ne $p.bytes -or $now.sha256 -cne $p.sha256){throw ('FINAL-CHECKS: scope receipt/input changed '+$p.path)}
  }
  # Only this fresh child receives Git advice/exclude overrides. Repository and
  # user configuration are unchanged; the exact driver is a pinned input.
  $designDriver=Join-Path $run 'design-driver.ps1'
  $emptyExclude=Join-Path $run 'empty-git-exclude'
  [IO.File]::WriteAllBytes($emptyExclude,[byte[]]@());[void](Pin-Final $emptyExclude)
  $designBody=@'
$count=0
$inheritedCount=[Environment]::GetEnvironmentVariable('GIT_CONFIG_COUNT','Process')
if($null -ne $inheritedCount -and (-not [int]::TryParse($inheritedCount,[ref]$count) -or $count -lt 0 -or $count -gt ([int]::MaxValue-2))){
  throw 'FINAL-DESIGN: invalid inherited Git configuration count'
}
# Preserve the sandbox's inherited safe.directory and other command-local
# entries. Replacing GIT_CONFIG_COUNT would discard that required context.
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_KEY_'+$count),'core.excludesfile','Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_VALUE_'+$count),(Join-Path $PSScriptRoot 'empty-git-exclude'),'Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_KEY_'+($count+1)),'core.safecrlf','Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_VALUE_'+($count+1)),'false','Process')
$env:GIT_CONFIG_COUNT=[string]($count+2)
& './scripts/design_decision_check.ps1' -Strict -Base '3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536'
exit $LASTEXITCODE
'@
  [IO.File]::WriteAllText($designDriver,($designBody+"`n"),$utf8);[void](Pin-Final $designDriver)
  $design=Run-Final 'design' $shell @('-NoProfile','-File',$designDriver)
  $report.design=Assert-LNFinalDesign $design $paths
  $claims=Run-Final 'claims' $shell @('-NoProfile','-File',$driver)
  $report.claims=Assert-LNFinalClaims $claims $root (Join-Path $root 'docs/internal/CLAIM_DRIFT_POLICY.json') $paths
  $trust=Run-Final 'trust' $rg @('-n','\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib','RMQ','lakefile.toml') 1
  Assert-LNOuterCapture $trust '' '' 1 'trust'
  $smoke=Run-Final 'native-decide' $rg @('-n','native_decide|Lean\.ofReduceBool','RMQ') 1
  Assert-LNOuterCapture $smoke '' '' 1 'native-decide'
  Git-EmptyFinal 'working-whitespace' @('diff','--check')
  if($Committed){
    Git-EmptyFinal 'committed-whitespace' @('diff','--check',($base+'..HEAD'))
    Git-EmptyFinal 'clean-tree' @('status','--porcelain=v1','--untracked-files=all')
  }
  $report.success=$true
}catch{$report.failure=$_.Exception.Message}
finally{
  $errors=[Collections.Generic.List[string]]::new()
  try{
    $endHead=(Git-Final 'final-head' @('rev-parse','HEAD')).Trim()
    $endChanged=(Git-Final 'final-changed' @('diff','--name-only','-z',$base)) -split [char]0|Where-Object{$_}
    $endNew=(Git-Final 'final-new' @('ls-files','--others','--exclude-standard','-z')) -split [char]0|Where-Object{$_}
    $endPaths=@(@($endChanged)+@($endNew)|Sort-Object -Unique)
    $report.finalIdentity=@{head=$endHead;paths=$endPaths}
    if($endHead -cne $report.head -or ($endPaths -join "`n") -cne ($report.claimPaths -join "`n")){
      throw 'FINAL-CHECKS: HEAD or complete changed/new roster changed during certification'
    }
  }catch{$errors.Add($_.Exception.Message)}
  foreach($p in $pins){try{$now=Get-LN1Pin $p.path;if($now.bytes -ne $p.bytes -or $now.sha256 -cne $p.sha256){throw ('changed pin '+$p.path)}}catch{$errors.Add($_.Exception.Message)}}
  $report.integrity=@{success=($errors.Count -eq 0);checked=$pins.Count;errors=@($errors.ToArray())}
  $report.cleanup=@{success=$true;disposableWrites=0;retainedEvidence=$run;liveSourceWrites=0}
  $report.success=$report.success -and $report.integrity.success
  $report.pins=@($pins.ToArray());$report.stages=@($stages.ToArray());$report.completedUtc=[DateTime]::UtcNow.ToString('o')
  [IO.File]::WriteAllText((Join-Path $run 'RESULT.json'),($report|ConvertTo-Json -Depth 40),$utf8)
}
Write-Output ('FINAL-CHECKS evidence='+$run)
if(-not $report.success){Write-Output ('FINAL-CHECKS FAIL '+$report.failure);exit 1}
Write-Output ('FINAL-CHECKS PASS files='+$report.claimPaths.Count+' committed='+[bool]$Committed)

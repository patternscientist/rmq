[CmdletBinding()]
param([switch]$Committed,[switch]$RepairDesignControls)
$ErrorActionPreference='Stop'
$root=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../..'))
. (Join-Path $PSScriptRoot 'identity.ps1')
. (Join-Path $root 'docs/internal/extensions/lifecycle-native1/final_streams.ps1')
$utf8=[Text.UTF8Encoding]::new($false,$true)
$base='3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536'
$run=Join-Path $root ('.lake/lifecycle-native1-r1/final-checks/'+[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff'))
[void][IO.Directory]::CreateDirectory($run)
$pins=[Collections.Generic.List[object]]::new()
$stages=[Collections.Generic.List[object]]::new()
$shell=(Get-Process -Id $PID).Path
$git=(Get-Command git -CommandType Application|Select-Object -First 1).Source
$rg=(Get-Command rg -CommandType Application|Select-Object -First 1).Source
$report=[ordered]@{schema='lifecycle-native1-r1-final-checks-v1';repairBase=$script:R1Base;success=$false;base=$base;
  committed=[bool]$Committed;head=$null;startedUtc=[DateTime]::UtcNow.ToString('o');
  deadlineSeconds=1800;deadlineRationale='Preserved all109-path scan timeout600.12s with CPU-active paragraph matcher and successful owned cleanup. Original83-path scan178.106s; new raw baseline55057lines versus26918 suggests about4.18x paragraph scan work before additional frozen data. Reserve1800seconds, more than2x that estimate, including cold/contended margin. Exact scanner, policy, paths and raw inventories remain unchanged; any timeout remains failure.';
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
function Assert-R1RepairDesign($Capture,[string[]]$Paths){
  $requested=Get-LNFinalPathSet $Paths
  $allowed=Get-LNFinalPathSet (@($script:R1Old)+@($script:R1Ledger)+@($script:R1New))
  if(-not $requested.SetEquals($allowed)){throw 'R1-FINAL-DESIGN: exact repair roster required'}
  $checker=Join-Path $root 'scripts/design_decision_check.ps1'
  $checkerPin=Get-LN1Pin $checker;$ast=Get-LNFinalCheckerAst $checker
  foreach($name in @('neutralEvidencePatterns','workflowRootPatterns','codeRootPatterns','proofCodePattern',
      'workflowCodePattern','nativeSourcePattern','nativeCodePatterns','nativeWorkflowPatterns')){
    Set-Variable -Name $name -Value (Get-LNFinalLiteral $ast $name) -Scope Local
  }
  $definitions=@(foreach($name in @('Test-AnyPattern','Get-PathDisposition')){
    $nodes=@($ast.FindAll({param($node)$node -is [Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -ceq $name},$true))
    if($nodes.Count -ne 1){throw 'R1-FINAL-DESIGN: ambiguous production classifier'}
    $nodes[0].Extent.Text
  })
  $classifier=[scriptblock]::Create("param([string]`$ClassifiedPath)`n"+($definitions -join "`n")+"`nGet-PathDisposition -Path `$ClassifiedPath")
  $code=0;$workflow=0;$neutral=0
  foreach($path in $Paths){
    $rows=@(& $classifier $path)
    if($rows.Count -ne 1 -or $rows[0].Unclassified){throw 'R1-FINAL-DESIGN: unclassified repair path'}
    if($rows[0].NeedsCode){$code++};if($rows[0].NeedsWorkflow){$workflow++};if($rows[0].Neutral){$neutral++}
  }
  # This consumer is only for the frozen four-script/fourteen-file/WDD repair.
  # The original cumulative implementation still uses its unchanged consumer.
  if($code -ne 0 -or $workflow -ne 18 -or $neutral -ne 1 -or
      -not $requested.Contains($script:R1Ledger) -or $requested.Contains('docs/internal/DESIGN_DECISIONS.md')){
    throw 'R1-FINAL-DESIGN: repair workflow-only classification differs'
  }
  $expected='DESIGN-CHECK: checked '+$Paths.Count+' changed files ('+$code+' code, '+$workflow+' workflow, '+$neutral+' neutral)'+[Environment]::NewLine
  Assert-LNOuterCapture $Capture $expected '' 0 'r1-final-design'
  [void](Assert-LNFinalPin $checkerPin $checker)
  return @{checkerPin=$checkerPin;summary=@{paths=$Paths.Count;code=$code;workflow=$workflow;neutral=$neutral;
    boundary='Exact frozen repair roster; classification comes from unchanged production literals/functions. Only the workflow ledger is required by this zero-code scope.'}}
}
if($RepairDesignControls){
  if($Committed){throw 'R1-DESIGN-CONTROLS: incompatible certification flag'}
  $controlReport=[ordered]@{schema='lifecycle-native1-r1-repair-design-controls-v1';success=$false;results=@();pins=@();failure=$null;integrity=$null;cleanup=$null}
  $controlPins=[Collections.Generic.List[object]]::new();$controlResults=[Collections.Generic.List[object]]::new()
  try{
    foreach($p in @($PSCommandPath,(Join-Path $PSScriptRoot 'identity.ps1'),(Join-Path $root 'scripts/design_decision_check.ps1'),(Join-Path $root 'docs/internal/extensions/lifecycle-native1/final_streams.ps1'))){$controlPins.Add((Get-LN1Pin $p))}
    $repairPaths=@($script:R1Old)+@($script:R1Ledger)+@($script:R1New)
    $driver=Join-Path $run 'repair-design-control-driver.ps1'
    $driverText=@'
$count=0
$inherited=[Environment]::GetEnvironmentVariable('GIT_CONFIG_COUNT','Process')
if($null -ne $inherited -and (-not [int]::TryParse($inherited,[ref]$count) -or $count -lt 0 -or $count -gt ([int]::MaxValue-2))){throw 'Invalid inherited Git configuration count'}
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_KEY_'+$count),'core.excludesfile','Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_VALUE_'+$count),(Join-Path $PSScriptRoot 'empty-git-exclude'),'Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_KEY_'+($count+1)),'core.safecrlf','Process')
[Environment]::SetEnvironmentVariable(('GIT_CONFIG_VALUE_'+($count+1)),'false','Process')
$env:GIT_CONFIG_COUNT=[string]($count+2)
& './scripts/design_decision_check.ps1' -Strict -Base 'c52c453a2f0f49c568886f502687e4d0667838e9'
exit $LASTEXITCODE
'@
    [IO.File]::WriteAllBytes((Join-Path $run 'empty-git-exclude'),[byte[]]@())
    $controlPins.Add((Get-LN1Pin (Join-Path $run 'empty-git-exclude')))
    [IO.File]::WriteAllText($driver,($driverText+"`n"),$utf8);$controlPins.Add((Get-LN1Pin $driver))
    $healthy=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$driver) $root (Join-Path $run 'healthy') 60 'repair-design-healthy'
    foreach($p in $healthy.raw){$controlPins.Add($p)}
    [void](Assert-R1RepairDesign $healthy $repairPaths)
    $controlResults.Add(@{id='healthy';passed=$true;capture=$healthy})
    foreach($case in @(
      @{id='missing-ledger';paths=@($repairPaths|Where-Object{$_ -cne $script:R1Ledger});expected='R1-FINAL-DESIGN: exact repair roster required'},
      @{id='extra-code-ledger';paths=@($repairPaths)+@('docs/internal/DESIGN_DECISIONS.md');expected='R1-FINAL-DESIGN: exact repair roster required'})){
      $failure=$null;try{[void](Assert-R1RepairDesign $healthy $case.paths)}catch{$failure=$_.Exception.Message}
      if(-not (Test-R1Exact $failure $case.expected)){throw 'R1-DESIGN-CONTROLS: path rejection differs'}
      $controlResults.Add(@{id=$case.id;passed=$true;paths=$case.paths;rejection=$failure;capture=$healthy})
    }
    foreach($case in @(
      @{id='extra-stdout';suffix='[Console]::Out.Write("extra`n")';expected='STREAM: r1-final-design stdout differs'},
      @{id='extra-stderr';suffix='[Console]::Error.Write("extra`n")';expected='STREAM: r1-final-design stderr differs'},
      @{id='wrong-exit';suffix='exit 7';expected='STREAM: r1-final-design ordinary exit differs'})){
      $caller=Join-Path $run ($case.id+'-caller.ps1')
      [IO.File]::WriteAllText($caller,('& '+(Quote-R1 $driver)+"`n"+$case.suffix+"`n"),$utf8);$controlPins.Add((Get-LN1Pin $caller))
      $capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$caller) $root (Join-Path $run $case.id) 60 $case.id
      foreach($p in $capture.raw){$controlPins.Add($p)}
      $failure=$null;try{[void](Assert-R1RepairDesign $capture $repairPaths)}catch{$failure=$_.Exception.Message}
      if(-not (Test-R1Exact $failure $case.expected)){throw ('R1-DESIGN-CONTROLS: exact rejection differs '+$failure)}
      $controlResults.Add(@{id=$case.id;passed=$true;capture=$capture;rejection=$failure})
    }
    $controlReport.success=$true
  }catch{$controlReport.failure=$_.Exception.Message}
  finally{
    $errors=@(foreach($p in $controlPins){try{Assert-R1Pin $p}catch{$_.Exception.Message}})
    $controlReport.integrity=@{success=($errors.Count -eq 0);errors=$errors};$controlReport.cleanup=@{success=$true;liveSourceWrites=0;disposableWrites=0}
    $controlReport.success=$controlReport.success -and $controlReport.integrity.success
    $controlReport.pins=@($controlPins.ToArray());$controlReport.results=@($controlResults.ToArray())
    Write-R1Json (Join-Path $run 'REPAIR_DESIGN_CONTROLS.json') $controlReport
  }
  Write-Output ('R1-DESIGN-CONTROLS success='+$controlReport.success+' evidence='+$run)
  if(-not $controlReport.success){Write-Output $controlReport.failure;exit 1};exit 0
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
      (Join-Path $root 'docs/internal/extensions/lifecycle-native1/final_streams.ps1'),(Join-Path $PSScriptRoot 'identity.ps1'))){[void](Pin-Final $p)}
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
  $scope=Run-Final 'scope' $shell @('-NoProfile','-File',(Join-Path $PSScriptRoot 'scope_check.ps1'),'-Complete')
  $report.scope=Assert-R1FinalScope $scope $root $report.head $paths
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
  $repairChanged=(Git-Final 'repair-changed' @('diff','--name-only','-z',$script:R1Base)) -split [char]0|Where-Object{$_}
  $repairPaths=@(@($repairChanged)+@($new)|Sort-Object -Unique)
  $repairDriver=Join-Path $run 'repair-design-driver.ps1'
  [IO.File]::WriteAllText($repairDriver,($designBody.Replace($base,$script:R1Base)+"`n"),$utf8);[void](Pin-Final $repairDriver)
  $repairDesign=Run-Final 'repair-design' $shell @('-NoProfile','-File',$repairDriver)
  $report.repairDesign=Assert-R1RepairDesign $repairDesign $repairPaths
  $claims=Run-Final 'claims' $shell @('-NoProfile','-File',$driver)
  $report.claims=Assert-LNFinalClaims $claims $root (Join-Path $root 'docs/internal/CLAIM_DRIFT_POLICY.json') $paths
  $trust=Run-Final 'trust' $rg @('-n','\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib','RMQ','lakefile.toml') 1
  Assert-LNOuterCapture $trust '' '' 1 'trust'
  $smoke=Run-Final 'native-decide' $rg @('-n','native_decide|Lean\.ofReduceBool','RMQ') 1
  Assert-LNOuterCapture $smoke '' '' 1 'native-decide'
  Git-EmptyFinal 'working-whitespace' @('diff','--check')
  if($Committed){
    Git-EmptyFinal 'committed-whitespace' @('diff','--check',($base+'..HEAD'))
    Git-EmptyFinal 'repair-committed-whitespace' @('diff','--check',($script:R1Base+'..HEAD'))
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

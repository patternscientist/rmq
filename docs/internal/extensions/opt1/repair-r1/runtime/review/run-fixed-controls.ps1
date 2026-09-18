[CmdletBinding()]
param()
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repoRoot=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../../../..'))
$target=Join-Path $repoRoot 'scripts/packed_optimized_replay_regression.ps1'
$utf8=[Text.UTF8Encoding]::new($false,$true)
$before=(Get-FileHash -LiteralPath $target).Hash
$ids=@('V01-SOLE-SETUP','V03-SUCCESS-STDOUT','V04-WRONG-STDERR','V06-DUPLICATE-PROGRESS','V07-REORDERED-PROGRESS','V08-EXTRA-STDERR','V09-PREFIX-HOLDOUT')
. (Join-Path $repoRoot 'scripts/owned_process_tree.ps1')
$root=Join-Path $repoRoot ('.lake/opt1-r1-runtime/fixed-review-'+[Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($root)
$shell=(Get-Process -Id $PID).Path
$records=[Collections.Generic.List[object]]::new()
$completed=[Collections.Generic.List[string]]::new()
$failure=$null
try{
 foreach($id in $ids){
  $caseRoot=Join-Path $root $id
  $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$target,'-OnlyCase',$id,'-ArtifactDirectory',$caseRoot,'-CampaignDeadlineSeconds','120')
  $result=Invoke-RMQOwnedBoundedProcess -FilePath $shell -Arguments $arguments -WorkingDirectory $repoRoot -Stage ('review-'+$id) -DeadlineSeconds 150 -OutputLimitBytes 1048576 -TempRoot $root
  $record=[ordered]@{ID=$id;Executable=$shell;Arguments=$arguments;DeadlineSeconds=150;OutputLimitBytes=1048576;ActualResult=$result;ProductionReceipt=$null;ClassifierVerdict=$null}
  $records.Add($record)
  if($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 0 -or @($result.StandardError).Count -ne 0){throw "Fixed control incomplete: $id"}
  if(@($result.StandardOutput | Where-Object {$_ -ceq 'OPT1-R1-REPLAY PASS executed=1 expected=1 registry=opt1-r1-production-v2'}).Count -ne 1){throw "Missing exact production completion: $id"}
  $receipt=Get-Content -LiteralPath (Join-Path $caseRoot 'RESULT.json') -Raw | ConvertFrom-Json
  $verdict=Get-Content -LiteralPath (Join-Path $caseRoot ($id+'-verdict.json')) -Raw | ConvertFrom-Json
  $record.ProductionReceipt=$receipt
  $record.ClassifierVerdict=$verdict
  if(@($receipt.Expected).Count -ne 1 -or @($receipt.Executed).Count -ne 1 -or $receipt.Expected[0] -cne $id -or $receipt.Executed[0] -cne $id -or $receipt.ExitCode -ne 0){throw "Focused registry differs: $id"}
  if($verdict.ActualAccept -ne ($id -ceq 'V01-SOLE-SETUP') -or -not $verdict.ActualOwnedChild){throw "Actual classifier verdict differs: $id"}
  $completed.Add($id)
  Write-Host "PARENT FIXED CONTROL $id PASS"
 }
}catch{$failure=$_.Exception.Message;throw}
finally{
 $after=(Get-FileHash -LiteralPath $target).Hash
 $report=@{ParentRunnerBeforeSHA256=$before;ParentRunnerAfterSHA256=$after;SourceUnchanged=($before -ceq $after);Expected=$ids;Executed=@($completed);Failure=$failure;Cases=@($records);ArtifactRoot=$root;Meaning='Independent focused actual parent-entry controls, not the later full46 production campaign';LeanLaunched=$false;POSIX='UNEXECUTED'}
 [IO.File]::WriteAllText((Join-Path $root 'fixed-controls.json'),($report | ConvertTo-Json -Depth 24),$utf8)
 Write-Host "PARENT FIXED CONTROLS ARTIFACTS $root"
 if($before -cne $after){throw 'Parent runner changed during controls'}
}
Write-Host 'PARENT FIXED CONTROLS PASS executed=7 expected=7'

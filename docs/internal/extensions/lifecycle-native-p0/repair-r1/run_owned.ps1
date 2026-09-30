param([ValidateSet('focused','full','integrity','dependencies','claims','checks')][string]$Kind,[string]$OutputRoot)
$ErrorActionPreference='Stop'
if(-not $PSBoundParameters.ContainsKey('Kind') -or [string]::IsNullOrEmpty($Kind)){throw 'STREAM: wrapper Kind is required'}
$Kind=$Kind.ToLowerInvariant()
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
if(-not $OutputRoot){$OutputRoot=Join-Path $repo ('.lake/repair-r1/'+$Kind+'-'+[Guid]::NewGuid().ToString('N'))}
[void][IO.Directory]::CreateDirectory($OutputRoot)
$utf8=[Text.UTF8Encoding]::new($false,$true)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
. (Join-Path $repo 'scripts/packed_native_lifecycle_stream_check.ps1')
$claimExpectation=$null
if($Kind -ceq 'claims'){
  . (Join-Path $repo 'docs/internal/extensions/lifecycle-native-p0/repair-r2/claim_expectations.ps1')
  $claimExpectation=Get-LNClaimStreamExpectation $repo
}
$runner=Join-Path $repo 'scripts/packed_native_lifecycle_storage_replay.ps1'
$source=[IO.File]::ReadAllText($runner,$utf8)
$match=[regex]::Match($source,"(?s)\`$taskChildScript = @'\r?\n(.*?)\r?\n'@")
if(-not $match.Success){throw 'production raw-stream child missing'}
$child=Join-Path $OutputRoot 'child.ps1'
[IO.File]::WriteAllText($child,$match.Groups[1].Value,$utf8)
$action=switch($Kind){
  'focused' {"& '$($runner.Replace("'","''"))' -Cases pop-unique; exit `$LASTEXITCODE"}
  'full' {"& '$($runner.Replace("'","''"))' -SelfTest; exit `$LASTEXITCODE"}
  'integrity' {"& '$PSScriptRoot/integrity_controls.ps1'; exit `$LASTEXITCODE"}
  'dependencies' {"& '$PSScriptRoot/dependency_controls.ps1'; exit `$LASTEXITCODE"}
  'claims' {"& '$repo/scripts/claim_drift_scan.ps1' -Strict -Path @('docs/internal/extensions/lifecycle-native-p0','docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md'); exit `$LASTEXITCODE"}
  'checks' {"& '$PSScriptRoot/final_checks.ps1'; exit `$LASTEXITCODE"}
}
if($Kind -in @('focused','full','integrity','dependencies')){
  $action=@"
`$mutex=[Threading.Mutex]::new(`$false,'Local\RMQLifecycleImplementationHeavy20260920')
`$held=`$false
try {
  try{`$held=`$mutex.WaitOne(600000)}catch [Threading.AbandonedMutexException]{`$held=`$true}
  if(-not `$held){throw 'host mutex unavailable'}
  $action
} finally {if(`$held){`$mutex.ReleaseMutex()};`$mutex.Dispose()}
"@
}
$inner=Join-Path $OutputRoot 'inner.ps1'
[IO.File]::WriteAllText($inner,("`$ErrorActionPreference='Stop'`nSet-Location -LiteralPath '"+$repo.Replace("'","''")+"'`n"+$action),$utf8)
$shell=(Get-Process -Id $PID).Path
$spec=@{file=$shell;arguments=@('-NoLogo','-NoProfile','-File',$inner);cwd=$repo;environment=@{};
  stdout=(Join-Path $OutputRoot 'stdout.log');stderr=(Join-Path $OutputRoot 'stderr.log');exit=(Join-Path $OutputRoot 'exit.json');
  pid=(Join-Path $OutputRoot 'pid');error=(Join-Path $OutputRoot 'error');overflow=(Join-Path $OutputRoot 'overflow');outputLimit=16777216}
$specPath=Join-Path $OutputRoot 'spec.json'
[IO.File]::WriteAllText($specPath,($spec|ConvertTo-Json -Depth 8),$utf8)
$deadline=if($Kind -eq 'integrity'){2400}elseif($Kind -eq 'claims'){7200}else{1200}
$r=Invoke-LNRetainedLauncher -FilePath $shell -Arguments @('-NoProfile','-File',$child,'-SpecPath',$specPath) `
  -WorkingDirectory $repo -Stage $Kind -DeadlineSeconds $deadline -OutputLimitBytes 16777216 -TempRoot (Join-Path $OutputRoot 'launcher') -ReleaseGatedScript
$record=@{kind=$Kind;command=$action;deadline=$deadline;outer=$r;actual=if([IO.File]::Exists($spec.exit)){Get-Content $spec.exit -Raw|ConvertFrom-Json}else{$null};raw=@()}
if($null -ne $claimExpectation){$record.claimExpectation=@{path=$claimExpectation.EvidencePath;bytes=([IO.FileInfo]$claimExpectation.EvidencePath).Length;sha256=(Get-FileHash -LiteralPath $claimExpectation.EvidencePath).Hash}}
foreach($p in @($spec.stdout,$spec.stderr,$spec.exit,$spec.error,$spec.overflow,$child,$inner,$specPath,$r.RawStandardOutput,$r.RawStandardError)){
  if([IO.File]::Exists($p)){$record.raw+=@{path=$p;bytes=([IO.FileInfo]$p).Length;sha256=(Get-FileHash $p).Hash}}
}
$record.streamValidation=@{validated=$false;failure=$null}
try {
  $capture=@{launcher=$r;actual=$record.actual;spec=$spec}
  $record.streamValidation=Assert-LNWrapperCapture $capture $Kind $repo $claimExpectation
} catch {$record.streamValidation=@{validated=$false;failure=$_.Exception.Message}}
[IO.File]::WriteAllText((Join-Path $OutputRoot 'RECEIPT.json'),($record|ConvertTo-Json -Depth 15),$utf8)
Write-Output ('OWNED '+$Kind+' exit='+$r.ExitCode+' evidence='+$OutputRoot)
if(-not $record.streamValidation.validated -or $r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0 -or $null -eq $record.actual -or $record.actual.exitCode -ne 0){exit 1}
exit 0

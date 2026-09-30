param([string]$RepositoryRoot,[string]$EvidenceRoot)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false)
[void][IO.Directory]::CreateDirectory($EvidenceRoot)
. (Join-Path $RepositoryRoot 'scripts/owned_process_tree.ps1')
. (Join-Path $RepositoryRoot 'scripts/lifecycle_validator_environment.ps1')
$shell=(Get-Process -Id $PID).Path
$sleeper=Join-Path $EvidenceRoot 'sleeper.ps1'
$pidFile=Join-Path $EvidenceRoot 'pids.json'
$body=@'
param([string]$Shell,[string]$PidFile)
$p=Start-Process -FilePath $Shell -ArgumentList '-NoProfile','-Command','Start-Sleep -Seconds 120' -WindowStyle Hidden -PassThru
[IO.File]::WriteAllText($PidFile,(@{root=$PID;descendant=$p.Id}|ConvertTo-Json))
Start-Sleep -Seconds 120
'@
[IO.File]::WriteAllText($sleeper,$body,$utf8)
$key='LIFE1_VALIDATE_SELECTOR'
$initial=[Environment]::GetEnvironmentVariables('Process')
$result=$null;$passed=$false
try {
  [Environment]::SetEnvironmentVariable($key,'id:L01-W-EMPTY','Process')
  $result=Invoke-LifecycleValidatorProcess -FilePath $shell -Arguments @('-NoProfile','-ExecutionPolicy','Bypass','-File',$sleeper,'-Shell',$shell,'-PidFile',$pidFile) `
    -WorkingDirectory $RepositoryRoot -Stage 'deadline-descendant' -DeadlineSeconds 6 -TempRoot $EvidenceRoot -Selector $null
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'process.json'),($result|ConvertTo-Json -Depth 20),$utf8)
  if(-not $result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne -1 -or $result.Ownership -cne 'kill-on-close-job' -or
     @($result.StandardOutput).Count -ne 0 -or @($result.StandardError).Count -ne 0 -or -not(Test-Path -LiteralPath $pidFile)) {throw 'CONTROL: intended owned timeout did not occur'}
  $pids=Get-Content -LiteralPath $pidFile -Raw|ConvertFrom-Json
  $observed=@($pids.root,$pids.descendant)+@($result.TerminatedIds)
  if(@($result.TerminatedIds).Count -lt 2 -or @($result.TerminatedIds) -notcontains $pids.descendant) {throw 'CONTROL: descendant not in owned termination receipt'}
  foreach($processId in $observed) {
    if($null -ne (Get-Process -Id $processId -ErrorAction SilentlyContinue)){throw 'CONTROL: owned root/descendant survived'}
  }
  if([Environment]::GetEnvironmentVariable($key,'Process') -cne 'id:L01-W-EMPTY'){throw 'CONTROL: timeout failed environment restoration'}
  $passed=$true
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'result.json'),([ordered]@{passed=$passed;shell=$shell;version=$PSVersionTable.PSVersion.ToString();
    dotnet=[Environment]::Version.ToString();pids=$pids;allObservedAbsent=$observed;environmentRestored=$true;result=$result;
    helperSha256=(Get-FileHash -LiteralPath (Join-Path $RepositoryRoot 'scripts/owned_process_tree.ps1')).Hash;
    adapterSha256=(Get-FileHash -LiteralPath (Join-Path $RepositoryRoot 'scripts/lifecycle_validator_environment.ps1')).Hash}|ConvertTo-Json -Depth 20),$utf8)
} finally {
  if($initial.Contains($key)){[Environment]::SetEnvironmentVariable($key,[string]$initial[$key],'Process')}
  else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
}
if(-not $passed){exit 1}
Write-Output 'L1R1-CONTROL|T01_DESCENDANT_TIMEOUT|PASS'

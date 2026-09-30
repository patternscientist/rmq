param([string]$OldRoot,[string]$EvidenceRoot)
Set-StrictMode -Version Latest
$ErrorActionPreference='Stop'
$utf8=[Text.UTF8Encoding]::new($false)
[void][IO.Directory]::CreateDirectory($EvidenceRoot)
. (Join-Path $OldRoot 'scripts/owned_process_tree.ps1')
$key='LIFE1_VALIDATE_SELECTOR'
$vars=[Environment]::GetEnvironmentVariables('Process')
$priorPresent=$vars.Contains($key);$prior=$vars[$key]
$records=@()
try {
  [Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')
  foreach($mode in @('absent','empty','explicit-id-empty')) {
    $environment=@{LEAN_NUM_THREADS='1'};$arguments=@('--registry')
    if($mode -ceq 'empty'){$environment[$key]=''}
    if($mode -ceq 'explicit-id-empty'){$environment[$key]='id:';$arguments=@()}
    $r=Invoke-RMQOwnedBoundedProcess -FilePath (Join-Path $OldRoot '.lake/build/bin/rmq_lifecycle_validate.exe') `
      -Arguments $arguments -WorkingDirectory $OldRoot -Stage $mode -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $EvidenceRoot -Environment $environment
    $records+=@([ordered]@{mode=$mode;result=$r})
    [IO.File]::WriteAllText((Join-Path $EvidenceRoot ($mode+'.json')),($records[-1]|ConvertTo-Json -Depth 20),$utf8)
    if($r.TimedOut -or $r.OutputLimitExceeded){throw 'Old environment control incomplete'}
    $reject=($mode -ceq 'explicit-id-empty' -or ($mode -ceq 'empty' -and $PSVersionTable.PSEdition -ceq 'Core'))
    if($reject) {
      $expected=if($mode -ceq 'explicit-id-empty'){'LIFE1-FAIL|empty-selector'}else{'LIFE1-FAIL|duplicate-selector-channel'}
      if($r.ExitCode -ne 1 -or @($r.StandardOutput).Count -ne 0 -or @($r.StandardError).Count -ne 1 -or $r.StandardError[0] -cne $expected){throw 'Wrong original selector rejection'}
    } else {
      if($r.ExitCode -ne 0 -or @($r.StandardError).Count -ne 0 -or @($r.StandardOutput).Count -ne 16){throw 'Wrong original registry positive'}
      for($i=0;$i -lt 16;$i++) {
        if($r.StandardOutput[$i] -cnotmatch ('^LIFE1-REGISTRY\|L'+('{0:D2}' -f ($i+1))+'-')){throw 'Wrong original ordered ID'}
      }
    }
  }
} finally {
  if($priorPresent){[Environment]::SetEnvironmentVariable($key,[string]$prior,'Process')}
  else{[Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')}
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'summary.json'),([ordered]@{shell=(Get-Process -Id $PID).Path;
    version=$PSVersionTable.PSVersion.ToString();dotnet=[Environment]::Version.ToString();records=$records;
    executableSha256=(Get-FileHash -LiteralPath (Join-Path $OldRoot '.lake/build/bin/rmq_lifecycle_validate.exe')).Hash;
    helperSha256=(Get-FileHash -LiteralPath (Join-Path $OldRoot 'scripts/owned_process_tree.ps1')).Hash}|ConvertTo-Json -Depth 30),$utf8)
}
Write-Output 'OLD-ENVIRONMENT-CONTROLS PASS'

#!/usr/bin/env pwsh
[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$repo = [IO.Path]::GetFullPath((Get-Location).Path)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$utf8 = [Text.UTF8Encoding]::new($false)
$artifact = Join-Path $repo ('.lake/opt1-final-claims/' + [Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($artifact)
$executable = Join-Path $env:SystemRoot 'System32/WindowsPowerShell/v1.0/powershell.exe'
$arguments = @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', 'scripts/claim_drift_scan.ps1', '-Strict')
$result = Invoke-RMQOwnedBoundedProcess -FilePath $executable -Arguments $arguments `
  -WorkingDirectory $repo -Stage 'opt1-final-claims' -DeadlineSeconds 900 `
  -OutputLimitBytes 33554432 -TempRoot $artifact
[IO.File]::WriteAllText((Join-Path $artifact 'raw-result.json'), ($result | ConvertTo-Json -Depth 12), $utf8)
$stdout = Join-Path $artifact 'stdout.log'
$stderr = Join-Path $artifact 'stderr.log'
[IO.File]::WriteAllLines($stdout, [string[]]$result.StandardOutput, $utf8)
[IO.File]::WriteAllLines($stderr, [string[]]$result.StandardError, $utf8)
$summary = @()
foreach ($line in $result.StandardOutput) {
  if ($line -match '^CLAIM-DRIFT:') { $summary += $line }
  elseif ($line -match '^CLAIM-DRIFT\[[^\]]*\]\[[^\]]*\]\[fail\]') { $summary += $Matches[0] }
}
$passed = $result.ExitCode -eq 0 -and -not $result.TimedOut -and -not $result.OutputLimitExceeded
$record = [ordered]@{
  Label='claims'; Command=@($executable) + $arguments; Passed=$passed
  ExitCode=$result.ExitCode; TimedOut=$result.TimedOut; OutputLimitExceeded=$result.OutputLimitExceeded
  DurationSeconds=$result.DurationSeconds; DeadlineSeconds=900; Ownership=$result.Ownership
  TerminatedIds=@($result.TerminatedIds); OutputSummary=@($summary)
  OutputSHA256=(Get-FileHash -LiteralPath $stdout -Algorithm SHA256).Hash.ToLowerInvariant()
  OutputBytes=(Get-Item -LiteralPath $stdout).Length
  StderrSHA256=(Get-FileHash -LiteralPath $stderr -Algorithm SHA256).Hash.ToLowerInvariant()
  StderrBytes=(Get-Item -LiteralPath $stderr).Length; RawArtifactDirectory=$artifact
  Scope='Final report/storage tree; production strict scanner/policy/roots unchanged'
}
[IO.File]::WriteAllText((Join-Path $repo 'docs/internal/extensions/opt1/final-report-claims.json'),
  ($record | ConvertTo-Json -Depth 8) + [Environment]::NewLine, $utf8)
Write-Output ($record | ConvertTo-Json -Depth 8)
if (-not $passed) { exit 1 }
exit 0

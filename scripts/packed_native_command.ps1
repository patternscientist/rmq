param(
  [Parameter(Mandatory=$true)][string]$FilePath,
  [Parameter(Mandatory=$true)][string[]]$Arguments,
  [Parameter(Mandatory=$true)][string]$Stage,
  [int]$DeadlineSeconds = 300
)
$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$taskOut = Join-Path $taskRoot 'docs/internal/extensions/native1/commands'
$taskTmp = Join-Path $taskRoot '.lake/native1/process'
[void](New-Item -ItemType Directory -Force -Path $taskOut, $taskTmp)
$taskWatch = [Diagnostics.Stopwatch]::StartNew()
$taskResult = Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments `
  -WorkingDirectory $taskRoot -Stage $Stage -DeadlineSeconds $DeadlineSeconds `
  -OutputLimitBytes 8388608 -TempRoot $taskTmp
$taskArtifact = [ordered]@{
  schema = 'native1-command-v1'
  platform = [Environment]::OSVersion.VersionString
  base = '0e6a00f654abc64f8b68988fa9675b9a839dca2f'
  head = ((& git -C $taskRoot rev-parse HEAD) -join '').Trim()
  command = @{ file = $FilePath; arguments = $Arguments }
  result = $taskResult
}
$taskPath = Join-Path $taskOut ($Stage + '.json')
[IO.File]::WriteAllText($taskPath, ($taskArtifact | ConvertTo-Json -Depth 12),
  [Text.UTF8Encoding]::new($false))
$taskResult.Output | Select-Object -Last 20 | Write-Output
Write-Output ("NATIVE1-COMMAND stage=" + $Stage + " exit=" + $taskResult.ExitCode +
  " seconds=" + $taskResult.DurationSeconds + " timeout=" + $taskResult.TimedOut)
if ($taskResult.TimedOut -or $taskResult.OutputLimitExceeded) { exit 124 }
exit $taskResult.ExitCode

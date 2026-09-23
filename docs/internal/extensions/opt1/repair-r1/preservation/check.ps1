# Run the byte-preservation checker under the repository's owned-tree supervisor.
[CmdletBinding()]
param(
  [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{40}$')][string]$CandidateRef,
  [string]$RepoRoot = (Get-Location).Path,
  [Parameter(Mandatory=$true)][string]$OutputDirectory,
  [switch]$SelfTestOnly,
  [ValidateRange(1,3600)][int]$DeadlineSeconds = 180,
  [ValidateRange(1024,134217728)][int]$OutputLimitBytes = 8388608,
  [string]$PythonPath = ''
)
$ErrorActionPreference = 'Stop'
$repo = [IO.Path]::GetFullPath($RepoRoot)
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'Preservation OutputDirectory must not already exist.' }
$checker = Join-Path $PSScriptRoot 'check.py'
if (-not (Test-Path -LiteralPath $checker -PathType Leaf)) { throw 'Preservation checker source is missing.' }
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($PythonPath)) {
  $PythonPath = Resolve-RMQScalarApplicationPath @(Get-Command python -CommandType Application -ErrorAction Stop) 'python'
}
[void](New-Item -ItemType Directory -Path $output)
$arguments = @($checker, '--candidate-ref', $CandidateRef, '--repo-root', $repo,
  '--output-directory', $output)
if ($SelfTestOnly) { $arguments += '--self-test-only' }
$result = Invoke-RMQOwnedBoundedProcess -FilePath $PythonPath -Arguments $arguments `
  -WorkingDirectory $repo -Stage 'opt1-r1-preservation' -DeadlineSeconds $DeadlineSeconds `
  -OutputLimitBytes $OutputLimitBytes -TempRoot (Join-Path $output 'owned-process')
$receipt = [ordered]@{
  Version='opt1-r1-preservation-process-v1'; CandidateRef=$CandidateRef; RepoRoot=$repo;
  SelfTestOnly=[bool]$SelfTestOnly; Python=$PythonPath;
  PythonSHA256=(Get-FileHash -LiteralPath $PythonPath -Algorithm SHA256).Hash;
  CheckerSHA256=(Get-FileHash -LiteralPath $checker -Algorithm SHA256).Hash;
  SupervisorSHA256=(Get-FileHash -LiteralPath (Join-Path $repo 'scripts/owned_process_tree.ps1') -Algorithm SHA256).Hash;
  DeadlineSeconds=$DeadlineSeconds; OutputLimitBytes=$OutputLimitBytes; Result=$result
}
[IO.File]::WriteAllText((Join-Path $output 'process.json'),
  ($receipt | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded) {
  $result.StandardOutput
  $result.StandardError
  exit 1
}
$result.StandardOutput

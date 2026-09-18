# Run both OPT-1-R2 preservation demonstrations under the owned-tree supervisor.
#
# Stage unchanged-r1 runs the byte-identical OPT-1-R1 wrapper
# repair-r1/preservation/check.ps1 against the candidate. It is EXPECTED to
# fail on the first relocated original (fail-fast LIVE_PROTECTED_MISSING) and
# is recorded as an expected failure, never as a pass.
# Stage controlled-difference runs the unchanged R1 comparison functions
# without the manifest mapping and requires the complete reported difference to
# equal the enumerated admitted set (status EXPECTED_CONTROLLED_DIFFERENCE).
# Stage relocated applies the manifest mapping and reproduces every R1 check;
# it must report PASS.
#
# The output directory must not exist and must lie outside the repository, so
# no receipt is an untracked file inside the protected history scope while the
# checks run. Exit 0 only when all three stages give their expected verdicts.
[CmdletBinding()]
param(
  [Parameter(Mandatory = $true)][ValidatePattern('^[0-9a-f]{40}$')][string]$CandidateRef,
  [string]$RepoRoot = (Get-Location).Path,
  [Parameter(Mandatory = $true)][string]$OutputDirectory,
  [ValidateRange(1, 3600)][int]$DeadlineSeconds = 900,
  [string]$PythonPath = '',
  [ValidatePattern('^([0-9a-f]{40})?$')][string]$FreezeRef = ''
)
$ErrorActionPreference = 'Stop'
$repo = [IO.Path]::GetFullPath($RepoRoot)
$output = [IO.Path]::GetFullPath($OutputDirectory)
if (Test-Path -LiteralPath $output) { throw 'OutputDirectory must not already exist.' }
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($output.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase)) { throw 'OutputDirectory must lie outside the repository.' }
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($PythonPath)) {
  $PythonPath = Resolve-RMQScalarApplicationPath @(Get-Command python -CommandType Application -ErrorAction Stop) 'python'
}
$hostPath = (Get-Process -Id $PID).Path
$r1Wrapper = Join-Path $repo 'docs/internal/extensions/opt1/repair-r1/preservation/check.ps1'
$checker = Join-Path $PSScriptRoot 'check_relocated.py'
[void](New-Item -ItemType Directory -Path $output)
$pyEnv = @{ PYTHONDONTWRITEBYTECODE = '1'; PYTHONIOENCODING = 'utf-8' }

function Invoke-Stage([string]$Name, [string]$File, [string[]]$Arguments, [hashtable]$Environment) {
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $repo `
    -Stage "opt1-r2-preservation-$Name" -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 8388608 `
    -TempRoot (Join-Path $output "owned-$Name") -Environment $Environment
  $resultPath = Join-Path $output "$Name/result.json"
  $status = $null; $code = $null; $detail = $null
  if (Test-Path -LiteralPath $resultPath -PathType Leaf) {
    $json = Get-Content -LiteralPath $resultPath -Raw -Encoding UTF8 | ConvertFrom-Json
    $status = [string]$json.status
    if ($null -ne $json.failure) { $code = [string]$json.failure.code; $detail = [string]$json.failure.detail }
  }
  return [ordered]@{ name = $Name; exit = $r.ExitCode; seconds = $r.DurationSeconds; deadline = $r.DeadlineSeconds;
    timedOut = $r.TimedOut; overflow = $r.OutputLimitExceeded; ownership = $r.Ownership; terminatedIds = @($r.TerminatedIds);
    stdout = @($r.StandardOutput); stderr = @($r.StandardError); status = $status; failureCode = $code; failureDetail = $detail;
    resultSha256 = if (Test-Path -LiteralPath $resultPath) { (Get-FileHash -LiteralPath $resultPath -Algorithm SHA256).Hash } else { $null } }
}

$manifest = & git -C $repo show "$($CandidateRef):docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json" | Out-String | ConvertFrom-Json
$firstOriginal = @($manifest.archives | ForEach-Object { [string]$_.originalPath } | Sort-Object -CaseSensitive)[0]

$unchanged = Invoke-Stage 'unchanged-r1' $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $r1Wrapper,
  '-CandidateRef', $CandidateRef, '-RepoRoot', $repo, '-OutputDirectory', (Join-Path $output 'unchanged-r1'), '-PythonPath', $PythonPath) $pyEnv
$unchanged.expected = "exit 1, status FAIL, code LIVE_PROTECTED_MISSING on $firstOriginal"
$unchanged.verdict = if ($unchanged.exit -eq 1 -and -not $unchanged.timedOut -and $unchanged.status -eq 'FAIL' -and
  $unchanged.failureCode -eq 'LIVE_PROTECTED_MISSING' -and $unchanged.failureDetail -like "*$firstOriginal*") { 'EXPECTED_FAILURE' } else { 'UNEXPECTED' }

$difference = Invoke-Stage 'controlled-difference' $PythonPath @('-B', $checker, '--candidate-ref', $CandidateRef,
  '--repo-root', $repo, '--output-directory', (Join-Path $output 'controlled-difference'), '--mode', 'controlled-difference') $pyEnv
$difference.expected = 'exit 0, status EXPECTED_CONTROLLED_DIFFERENCE'
$difference.verdict = if ($difference.exit -eq 0 -and -not $difference.timedOut -and $difference.status -eq 'EXPECTED_CONTROLLED_DIFFERENCE') { 'EXPECTED_CONTROLLED_DIFFERENCE' } else { 'UNEXPECTED' }

$relocatedArgs = @('-B', $checker, '--candidate-ref', $CandidateRef,
  '--repo-root', $repo, '--output-directory', (Join-Path $output 'relocated'), '--mode', 'relocated')
if ($FreezeRef -ne '') { $relocatedArgs += @('--freeze-ref', $FreezeRef) }
$relocated = Invoke-Stage 'relocated' $PythonPath $relocatedArgs $pyEnv
$relocated.expected = 'exit 0, status PASS'
$relocated.verdict = if ($relocated.exit -eq 0 -and -not $relocated.timedOut -and $relocated.status -eq 'PASS') { 'PASS' } else { 'UNEXPECTED' }

$ok = $unchanged.verdict -eq 'EXPECTED_FAILURE' -and $difference.verdict -eq 'EXPECTED_CONTROLLED_DIFFERENCE' -and $relocated.verdict -eq 'PASS'
$receipt = [ordered]@{
  Version = 'opt1-r2-preservation-process-v1'; CandidateRef = $CandidateRef; RepoRoot = $repo
  Host = [Environment]::MachineName; OS = [Environment]::OSVersion.VersionString
  PowerShell = $PSVersionTable.PSVersion.ToString(); HostPath = $hostPath
  Python = $PythonPath; PythonSHA256 = (Get-FileHash -LiteralPath $PythonPath -Algorithm SHA256).Hash
  WrapperSHA256 = (Get-FileHash -LiteralPath $PSCommandPath -Algorithm SHA256).Hash
  CheckerSHA256 = (Get-FileHash -LiteralPath $checker -Algorithm SHA256).Hash
  R1WrapperSHA256 = (Get-FileHash -LiteralPath $r1Wrapper -Algorithm SHA256).Hash
  R1CheckerSHA256 = (Get-FileHash -LiteralPath (Join-Path $repo 'docs/internal/extensions/opt1/repair-r1/preservation/check.py') -Algorithm SHA256).Hash
  SupervisorSHA256 = (Get-FileHash -LiteralPath (Join-Path $repo 'scripts/owned_process_tree.ps1') -Algorithm SHA256).Hash
  FreezeRef = $FreezeRef; DeadlineSeconds = $DeadlineSeconds; Stages = @($unchanged, $difference, $relocated); AllExpected = $ok
}
[IO.File]::WriteAllText((Join-Path $output 'process.json'), ($receipt | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
Write-Output ("OPT1-R2-PRESERVATION-DEMONSTRATIONS: unchanged-r1={0}[{1}] controlled-difference={2} relocated={3}" -f `
    $unchanged.verdict, $unchanged.failureCode, $difference.verdict, $relocated.verdict)
if ($ok) { exit 0 }
foreach ($stage in @($unchanged, $difference, $relocated)) { $stage.stdout; $stage.stderr }
exit 1

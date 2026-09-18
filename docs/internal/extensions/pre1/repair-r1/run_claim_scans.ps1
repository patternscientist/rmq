# PRE-1-R1: run the unchanged claim scanner three ways on a clean checkout and
# apply the order-independent detector to the separate runs.
#
# Runs, in this order, each as one owned bounded child of the chosen shell with
# the repository root as working directory:
#   strict   scripts/claim_drift_scan.ps1 -Strict
#   records  scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords
#   selftest scripts/claim_drift_scan.ps1 -SelfTest
# then claim_scan_detector.py over the three stdout logs with their exits.
# Logs stay under -OutDir, which must lie outside the repository and must not
# exist yet. The receipt holds exits, durations, deadlines, byte digests and
# the detector's counts; it never holds scanner text.
#
# The repository must be clean before, and its HEAD, status, worktree and index
# diffs must be identical after. Exit codes: 0 every run completed and the
# detector verdict is CLEAN; 1 a run completed with the DEFECT verdict or the
# repository state changed; 3 inconclusive (a timeout, an output-limit hit, a
# dirty start or a missing detector result).
[CmdletBinding()]
param(
  [string]$RepoRoot = '',
  [string]$OutDir = '',
  [string]$ReceiptPath = '',
  [string]$ShellPath = '',
  [string]$PythonPath = '',
  # Observed on this tree family: 5-35 s per run on a quiet host; the NATIVE-1
  # lane measured 1703 s (strict) and 2292 s (self-test) under heavy host load.
  [ValidateRange(1, 86400)][int]$StrictDeadlineSeconds = 3600,
  [ValidateRange(1, 86400)][int]$SelfTestDeadlineSeconds = 7200,
  [ValidateRange(1, 3600)][int]$DetectorDeadlineSeconds = 300
)
$ErrorActionPreference = 'Stop'
if ([string]::IsNullOrWhiteSpace($RepoRoot)) { $RepoRoot = Join-Path $PSScriptRoot '../../../../..' }
$repo = [IO.Path]::GetFullPath($RepoRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($OutDir)) {
  $OutDir = Join-Path ([IO.Path]::GetTempPath()) ('pre1-r1-claim-scans-' + [Guid]::NewGuid().ToString('N'))
}
$out = [IO.Path]::GetFullPath($OutDir)
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($out.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase) -or $out -eq $repo) {
  Write-Output "CLAIM-SCANS: ERROR -OutDir $out lies inside the repository"; exit 3
}
if (Test-Path -LiteralPath $out) { Write-Output "CLAIM-SCANS: ERROR -OutDir $out already exists"; exit 3 }
if ([string]::IsNullOrWhiteSpace($ReceiptPath)) { $ReceiptPath = Join-Path $out 'receipt.json' }
$receiptFull = [IO.Path]::GetFullPath($ReceiptPath)
if ($receiptFull.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase)) {
  Write-Output "CLAIM-SCANS: ERROR -ReceiptPath $receiptFull lies inside the repository"; exit 3
}
if ([string]::IsNullOrWhiteSpace($ShellPath)) { $ShellPath = (Get-Process -Id $PID).Path }
if ([string]::IsNullOrWhiteSpace($PythonPath)) {
  $PythonPath = Resolve-RMQScalarApplicationPath @(Get-Command python -CommandType Application -ErrorAction Stop) 'python'
}
$gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
$detector = Join-Path $PSScriptRoot 'claim_scan_detector.py'
$utf8 = [Text.UTF8Encoding]::new($false)
[void](New-Item -ItemType Directory -Path $out)
$owned = Join-Path $out 'owned'

function Get-Sha256([string]$Path) { return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash }
function Get-TextSha256([string]$Text) {
  return [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($utf8.GetBytes($Text))).Replace('-', '')
}
function Get-State([string]$Label) {
  $head = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') "$Label-head" 120 1048576 $owned) -join '').Trim()
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $gitPath -DeadlineSeconds 600 `
    -OutputLimitBytes 67108864 -TempRoot $owned -StagePrefix "$Label-state"
  return [pscustomobject]@{ Head = $head; State = [string]$state }
}
function Get-Blob([string]$Head, [string]$Rel) {
  return (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', "$Head`:$Rel") "blob-$([IO.Path]::GetFileName($Rel))" 120 1048576 $owned) -join '').Trim()
}

$before = Get-State 'before'
$lines = @($before.State -split "`r?`n" | Where-Object { $_ -ne '' })
$clean = ($lines.Count -eq 2 -and $lines[0] -eq '---WORKTREE---' -and $lines[1] -eq '---INDEX---')
$receipt = [ordered]@{
  version = 'PRE1-R1-CLAIM-SCANS-RECEIPT-V1'; head = $before.Head; cleanBefore = $clean
  stateBeforeSha256 = Get-TextSha256 $before.State
  host = [Environment]::MachineName; os = [Environment]::OSVersion.VersionString
  shell = $ShellPath; runnerPowerShell = $PSVersionTable.PSVersion.ToString()
  scanner = [ordered]@{ path = 'scripts/claim_drift_scan.ps1'; blob = (Get-Blob $before.Head 'scripts/claim_drift_scan.ps1');
    liveSha256 = Get-Sha256 (Join-Path $repo 'scripts/claim_drift_scan.ps1') }
  policy = [ordered]@{ path = 'docs/internal/CLAIM_DRIFT_POLICY.json'; blob = (Get-Blob $before.Head 'docs/internal/CLAIM_DRIFT_POLICY.json');
    liveSha256 = Get-Sha256 (Join-Path $repo 'docs/internal/CLAIM_DRIFT_POLICY.json') }
  detectorSha256 = Get-Sha256 $detector; runnerSha256 = Get-Sha256 $PSCommandPath
  python = $PythonPath; mutex = 'not taken by this runner (each run expected under five minutes)'
  runs = @(); detector = $null; stateUnchanged = $false; result = 'INCONCLUSIVE'
}
if (-not $clean) {
  Write-Output 'CLAIM-SCANS: ERROR the repository is not clean before the scans'
  [IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
  exit 3
}
$shellVersion = @(& $ShellPath -NoLogo -NoProfile -Command '$PSVersionTable.PSVersion.ToString()') -join ''
$receipt.shellVersion = $shellVersion.Trim()

$plan = @(
  [pscustomobject]@{ Name = 'strict'; Args = @('-Strict'); Deadline = $StrictDeadlineSeconds },
  [pscustomobject]@{ Name = 'records'; Args = @('-Strict', '-IncludeProcessRecords'); Deadline = $StrictDeadlineSeconds },
  [pscustomobject]@{ Name = 'selftest'; Args = @('-SelfTest'); Deadline = $SelfTestDeadlineSeconds }
)
$inconclusive = $false
$exits = @{}
foreach ($step in $plan) {
  $started = [DateTime]::UtcNow
  $run = Invoke-RMQOwnedBoundedProcess -FilePath $ShellPath `
    -Arguments (@('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', 'scripts/claim_drift_scan.ps1') + $step.Args) `
    -WorkingDirectory $repo -Stage "scan-$($step.Name)" -DeadlineSeconds $step.Deadline -OutputLimitBytes 268435456 -TempRoot $owned
  $stdoutPath = Join-Path $out "$($step.Name).stdout.log"
  $stderrPath = Join-Path $out "$($step.Name).stderr.log"
  [IO.File]::WriteAllText($stdoutPath, ((@($run.StandardOutput) -join "`n") + "`n"), $utf8)
  [IO.File]::WriteAllText($stderrPath, ((@($run.StandardError) -join "`n") + $(if (@($run.StandardError).Count) { "`n" } else { '' })), $utf8)
  $exits[$step.Name] = $run.ExitCode
  if ($run.TimedOut -or $run.OutputLimitExceeded) { $inconclusive = $true }
  $receipt.runs += [ordered]@{
    name = $step.Name; command = ('scripts/claim_drift_scan.ps1 ' + ($step.Args -join ' ')); startedUtc = $started.ToString('o')
    exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut
    outputLimitExceeded = $run.OutputLimitExceeded; ownership = $run.Ownership
    stdoutLines = @($run.StandardOutput).Count; stdoutSha256 = Get-Sha256 $stdoutPath
    stderrLines = @($run.StandardError).Count; stderrSha256 = Get-Sha256 $stderrPath
  }
  Write-Output ("CLAIM-SCANS: {0} exit {1} in {2} s (deadline {3} s, timedOut {4}, stdout lines {5}, stderr lines {6})" -f `
      $step.Name, $run.ExitCode, $run.DurationSeconds, $run.DeadlineSeconds, $run.TimedOut, @($run.StandardOutput).Count, @($run.StandardError).Count)
}

$detectorJson = Join-Path $out 'detector.json'
$det = Invoke-RMQOwnedBoundedProcess -FilePath $PythonPath `
  -Arguments @('-B', $detector, '--default', (Join-Path $out 'strict.stdout.log'), '--records', (Join-Path $out 'records.stdout.log'),
    '--selftest', (Join-Path $out 'selftest.stdout.log'), '--default-exit', [string]$exits['strict'],
    '--records-exit', [string]$exits['records'], '--selftest-exit', [string]$exits['selftest'], '--result-json', $detectorJson) `
  -WorkingDirectory $out -Stage 'detector' -DeadlineSeconds $DetectorDeadlineSeconds -OutputLimitBytes 16777216 -TempRoot $owned `
  -Environment @{ PYTHONIOENCODING = 'utf-8'; PYTHONDONTWRITEBYTECODE = '1' }
foreach ($line in @($det.StandardOutput)) { Write-Output $line }
foreach ($line in @($det.StandardError)) { Write-Output "CLAIM-SCANS: detector stderr: $line" }
$detResult = $null
if (-not $det.TimedOut -and (Test-Path -LiteralPath $detectorJson -PathType Leaf)) {
  $detResult = Get-Content -LiteralPath $detectorJson -Raw -Encoding UTF8 | ConvertFrom-Json
} else { $inconclusive = $true }
$receipt.detector = [ordered]@{ exit = $det.ExitCode; seconds = $det.DurationSeconds; deadline = $det.DeadlineSeconds;
  timedOut = $det.TimedOut; stderrLines = @($det.StandardError).Count; result = $detResult }

$after = Get-State 'after'
$receipt.stateAfterSha256 = Get-TextSha256 $after.State
$receipt.stateUnchanged = ($before.Head -ceq $after.Head) -and ($before.State -ceq $after.State)
if ($inconclusive) { $receipt.result = 'INCONCLUSIVE' }
elseif (-not $receipt.stateUnchanged) { $receipt.result = 'FAIL-STATE-CHANGED' }
elseif ($det.ExitCode -eq 0 -and $detResult.verdict -ceq 'CLEAN') { $receipt.result = 'CLEAN' }
elseif ($det.ExitCode -eq 1 -and $detResult.verdict -ceq 'DEFECT') { $receipt.result = 'DEFECT' }
else { $receipt.result = 'INCONCLUSIVE'; $inconclusive = $true }
Remove-Item -LiteralPath $owned -Recurse -Force -ErrorAction SilentlyContinue
[IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
Write-Output ("CLAIM-SCANS: RESULT: {0} head {1} state unchanged {2} receipt {3}" -f $receipt.result, $before.Head, $receipt.stateUnchanged, $receiptFull)
if ($receipt.result -ceq 'CLEAN') { exit 0 }
if ($inconclusive) { exit 3 }
exit 1

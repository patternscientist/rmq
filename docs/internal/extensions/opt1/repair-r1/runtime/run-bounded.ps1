[CmdletBinding()]
param(
  [string]$RepoRoot = ([IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../../..'))),
  [string]$ArtifactDirectory = ''
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$RepoRoot = [IO.Path]::GetFullPath($RepoRoot)
. (Join-Path $RepoRoot 'scripts/owned_process_tree.ps1')
$utf8 = [Text.UTF8Encoding]::new($false, $true)
if ($ArtifactDirectory -ceq '') { $ArtifactDirectory = Join-Path $RepoRoot ('.lake/opt1-r1-runtime/certification-' + [Guid]::NewGuid().ToString('N')) }
$artifacts = [IO.Path]::GetFullPath($ArtifactDirectory)
if (Test-Path -LiteralPath $artifacts) { throw 'OPT1-R1-WRAPPER: use a new private output directory' }
[void][IO.Directory]::CreateDirectory($artifacts)
$shellPath = (Get-Process -Id $PID).Path
$runner = Join-Path $PSScriptRoot 'replay.ps1'
$arguments = @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$runner,'-RepoRoot',$RepoRoot,'-ArtifactDirectory',(Join-Path $artifacts 'cases'))
# Development's first33 cases took149.680s total; full53 receives600s.
$result = Invoke-RMQOwnedBoundedProcess -FilePath $shellPath -Arguments $arguments -WorkingDirectory $RepoRoot -Stage 'opt1-r1-runtime-full53' -DeadlineSeconds 600 -OutputLimitBytes 1048576 -TempRoot $artifacts
$receipt = @{ Executable=$shellPath; Arguments=$arguments; DeadlineSeconds=600; OutputLimitBytes=1048576;
  MeasuredPredecessor='first33 completed development cases:149.680s total including two30s timeouts';
  CoveredRows=@('REQ-OPT-R1-EXCLUSIVE-REJECTION','CHK-OPT-R1-PRODUCTION-REPLAY','REPLAY-EXACT-REGISTRY','REPLAY-SELECTOR-NONVACUITY','REPLAY-SUBPROCESS-DEADLINE','INV-MUTATION-REPRODUCIBILITY');
  RunnerSHA256=(Get-FileHash -LiteralPath $runner -Algorithm SHA256).Hash; Result=$result }
[IO.File]::WriteAllText((Join-Path $artifacts 'WRAPPER.json'), ($receipt | ConvertTo-Json -Depth 15), $utf8)
Write-Host "OPT1-R1-RUNTIME WRAPPER ARTIFACTS $artifacts"
if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 0 -or @($result.StandardError).Count -ne 0 -or
    @($result.StandardOutput | Where-Object { $_ -ceq 'OPT1-R1-RUNTIME PASS executed=53 expected=53 registry=opt1-r1-runtime-v1' }).Count -ne 1) {
  throw 'OPT1-R1-WRAPPER: final53 incomplete; inspect preserved actual streams and case results'
}
Write-Host "OPT1-R1-RUNTIME WRAPPER PASS duration=$($result.DurationSeconds)s executed=53 expected=53"

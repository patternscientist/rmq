[CmdletBinding()]
param(
  [string]$RepoRoot = ([IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../../..'))),
  [string]$ArtifactDirectory = ''
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$utf8 = [Text.UTF8Encoding]::new($false, $true)
. (Join-Path $RepoRoot 'scripts/owned_process_tree.ps1')
if ($ArtifactDirectory -ceq '') { $ArtifactDirectory = Join-Path $RepoRoot ('.lake/opt1-r1-runtime/frozen-reproduction-' + [Guid]::NewGuid().ToString('N')) }
$receiptRoot = [IO.Path]::GetFullPath($ArtifactDirectory)
if (Test-Path -LiteralPath $receiptRoot) { throw 'Frozen reproduction requires a new private output directory' }
[void][IO.Directory]::CreateDirectory($receiptRoot)
# A fresh reproduction reads the real frozen production blob through Git.
# The historical initial RESULT.json remains immutable in frozen-reproduction/.
$gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
$archivePath = Join-Path $receiptRoot 'frozen-production.zip'
$sourceRoot = Join-Path $receiptRoot 'source'
$archiveResult = Invoke-RMQOwnedBoundedProcess -FilePath $gitPath -Arguments @('archive','--format=zip',('--output=' + $archivePath),'aecf4a580c591e8f694a3699e19e843198089194','scripts/packed_optimized_runtime.ps1') -WorkingDirectory $RepoRoot -Stage 'frozen-git-archive' -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot $receiptRoot
if ($archiveResult.TimedOut -or $archiveResult.OutputLimitExceeded -or $archiveResult.ExitCode -ne 0) { throw 'Frozen source extraction failed' }
Add-Type -AssemblyName System.IO.Compression.FileSystem
[IO.Compression.ZipFile]::ExtractToDirectory($archivePath, $sourceRoot)
$target = Join-Path $sourceRoot 'scripts/packed_optimized_runtime.ps1'
$tokens = $null; $errors = $null
$ast = [Management.Automation.Language.Parser]::ParseFile($target, [ref]$tokens, [ref]$errors)
if (@($errors).Count -ne 0) { throw 'Frozen production parse failed' }
foreach ($name in @('Assert-OPT1Bounded', 'Assert-OPT1Rejected')) {
  $matches = @($ast.FindAll({ param($node) $node -is [Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -ceq $name }, $true))
  if ($matches.Count -ne 1) { throw "Production function is not unique: $name" }
  . ([scriptblock]::Create($matches[0].Extent.Text))
}
$shellPath = (Get-Process -Id $PID).Path
$expected = 'uncaught exception: N01-JUMP: compiler observation mismatch'
$cases = @(
  @{ ID='sole-expected'; Out=@($expected); Err=@(); ExpectedAccepted=$true },
  @{ ID='mixed-streams'; Out=@($expected); Err=@('uncaught exception: independent coordinator failure'); ExpectedAccepted=$true },
  @{ ID='unrelated-only'; Out=@(); Err=@('uncaught exception: independent coordinator failure'); ExpectedAccepted=$false })
$receipts = @()
foreach ($case in $cases) {
  $fixture = Join-Path $receiptRoot ($case.ID + '.ps1')
  $lines = @($case.Out | ForEach-Object { "[Console]::Out.WriteLine('$($_.Replace("'", "''"))')" }) +
    @($case.Err | ForEach-Object { "[Console]::Error.WriteLine('$($_.Replace("'", "''"))')" }) + @('exit 1')
  [IO.File]::WriteAllLines($fixture, [string[]]$lines, $utf8)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $shellPath -Arguments @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$fixture) -WorkingDirectory $RepoRoot -Stage $case.ID -DeadlineSeconds 60 -OutputLimitBytes 1048576 -TempRoot $receiptRoot
  if ($result.TimedOut -or $result.OutputLimitExceeded -or $result.ExitCode -ne 1) { throw "Reproduction setup failed: $($case.ID)" }
  $accepted = $true; $diagnostic = ''
  try { Assert-OPT1Rejected $result 'N01-JUMP: compiler observation mismatch' } catch { $accepted = $false; $diagnostic = $_.Exception.Message }
  $receipts += [pscustomobject]@{ ID=$case.ID; Accepted=$accepted; ExpectedHistoricalAccepted=$case.ExpectedAccepted; ClassifierDiagnostic=$diagnostic; Result=$result }
  if ($accepted -ne $case.ExpectedAccepted) { throw "Frozen behavior changed: $($case.ID)" }
}
[IO.File]::WriteAllText((Join-Path $receiptRoot 'RESULT.json'), (@{ FrozenBase='aecf4a580c591e8f694a3699e19e843198089194'; SourceSerialization='Exact Git blob extracted with git archive'; SourceExtraction=$archiveResult; ProductionSHA256=(Get-FileHash -LiteralPath $target -Algorithm SHA256).Hash; ActualFunctions=@('Assert-OPT1Bounded','Assert-OPT1Rejected'); Receipts=$receipts; Verdict='REPRODUCED'; Limits='Classifier defect; not evidence original Lean negatives contained mixed failures' } | ConvertTo-Json -Depth 15), $utf8)
Write-Host 'OPT1-R1 FROZEN REPRODUCTION PASS sole-expected accepted; mixed-streams wrongly accepted; unrelated-only rejected'

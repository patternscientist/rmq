param([Parameter(Mandatory=$true)][ValidatePattern('^[a-z0-9-]+$')][string]$Stage)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$logs = Join-Path $PSScriptRoot 'commands'
$processTemp = Join-Path $repo '.lake/bv1-phase-process'
$summaryPath = Join-Path $logs ($Stage + '.json')
if (Test-Path -LiteralPath $summaryPath) { throw 'Phase evidence already exists.' }
$base = '0e6a00f654abc64f8b68988fa9675b9a839dca2f'
$checks = @(
  @{ id='trust'; exe=(Get-Command rg).Source; args=@('-n','\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib','RMQ','lakefile.toml'); expected=1 },
  @{ id='native-trust'; exe=(Get-Command rg).Source; args=@('-n','native_decide|Lean\.ofReduceBool','RMQ'); expected=1 },
  @{ id='working-diff'; exe=(Get-Command git).Source; args=@('diff','--check'); expected=0 },
  @{ id='range-diff'; exe=(Get-Command git).Source; args=@('diff','--check',($base+'..HEAD')); expected=0 },
  @{ id='design'; exe=(Get-Command pwsh).Source; args=@('-NoProfile','-File','scripts/design_decision_check.ps1','-Strict','-Base',$base); expected=0 },
  @{ id='claims'; exe=(Get-Command pwsh).Source; args=@('-NoProfile','-File','scripts/claim_drift_scan.ps1','-Strict'); expected=0 }
)
$records = @()
foreach ($check in $checks) {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $check.exe -Arguments $check.args `
    -WorkingDirectory $repo -Stage ($Stage + '-' + $check.id) -DeadlineSeconds 300 `
    -OutputLimitBytes 33554432 -TempRoot $processTemp
  $raw = [Text.UTF8Encoding]::new($false).GetBytes(($result | ConvertTo-Json -Depth 12))
  $archive = Join-Path $logs ($Stage + '-' + $check.id + '.json.gz')
  $file = [IO.File]::Create($archive)
  try {
    $zip = [IO.Compression.GZipStream]::new($file, [IO.Compression.CompressionLevel]::Optimal)
    try { $zip.Write($raw,0,$raw.Length) } finally { $zip.Dispose() }
  } finally { $file.Dispose() }
  $pass = $result.ExitCode -eq $check.expected -and -not $result.TimedOut -and -not $result.OutputLimitExceeded
  if ($check.id -in @('trust','native-trust')) { $pass = $pass -and $result.Output.Count -eq 0 }
  $records += [pscustomobject]@{
    id=$check.id; executable=$check.exe; arguments=$check.args; expectedExit=$check.expected
    passed=$pass; exit=$result.ExitCode; seconds=$result.DurationSeconds; deadlineSeconds=300
    ownership=$result.Ownership; outputArchive=$archive; sha256=(Get-FileHash -LiteralPath $archive).Hash
    outputTail=@($result.Output | Select-Object -Last 2)
  }
  Write-Output "BV1-PHASE-CHECK $($check.id) passed=$pass exit=$($result.ExitCode) seconds=$($result.DurationSeconds)"
}
$frozenHash = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.md')).Hash
$frozen = $frozenHash -eq '80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24'
$passed = $frozen -and $records.Count -eq 6 -and @($records | Where-Object { -not $_.passed }).Count -eq 0
[IO.File]::WriteAllText($summaryPath, ([ordered]@{
  stage=$Stage; base=$base; head=(& git -C $repo rev-parse HEAD).Trim()
  platform='Windows PowerShell 7'; checks=$records; expectedChecks=6; executedChecks=$records.Count
  frozenMatrixSha256=$frozenHash; frozenMatrixUnchanged=$frozen; passed=$passed
} | ConvertTo-Json -Depth 12), [Text.UTF8Encoding]::new($false))
Write-Output "BV1-PHASE-CHECKS passed=$passed executed=$($records.Count) expected=6 frozen=$frozen"
if (-not $passed) { exit 1 }

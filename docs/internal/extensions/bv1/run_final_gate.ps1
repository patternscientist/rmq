param(
  [Parameter(Mandatory=$true)][ValidatePattern('^[a-z0-9-]+$')][string]$Stage,
  [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{40}$')][string]$Commit,
  [Parameter(Mandatory=$true)][ValidateRange(300,43200)][int]$DeadlineSeconds,
  [Parameter(Mandatory=$true)][string]$CoordinatorGrant
)
# Invoke only after the coordinator grants this exact candidate a host-wide
# aggregate slot. The caller supplies the retained grant's path; this script
# records it and never infers approval from passing local tests.
# Interpreting the human grant and enforcing one aggregate per unchanged tree
# are coordinator/caller obligations; a new Stage is not permission to rerun.
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$utf8 = [Text.UTF8Encoding]::new($false)
$summaryPath = Join-Path $PSScriptRoot ('commands/' + $Stage + '.json')
$archivePath = Join-Path $PSScriptRoot ('commands/' + $Stage + '-output.json.gz')
if ((Test-Path -LiteralPath $summaryPath) -or (Test-Path -LiteralPath $archivePath)) {
  throw 'Aggregate evidence already exists; no unchanged automatic rerun.'
}
$grantPath = (Resolve-Path -LiteralPath $CoordinatorGrant).Path
if (-not (Test-Path -LiteralPath $grantPath -PathType Leaf)) { throw 'Coordinator grant is missing.' }
$grantBytes = [IO.File]::ReadAllBytes($grantPath)
if ($grantBytes.Length -eq 0) { throw 'The retained coordinator grant is empty.' }
$git = (Get-Command git).Source
$processTemp = Join-Path $repo '.lake/bv1-final-gate-process'
$head = ((Invoke-RMQCheckedGit -GitPath $git -RepositoryRoot $repo -Arguments @('rev-parse','HEAD') `
  -Stage ($Stage + '-head') -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $processTemp) -join "`n").Trim()
if ($head -cne $Commit) { throw 'Aggregate candidate commit mismatch.' }
$statusArguments = @('status','--porcelain=v1','--untracked-files=all')
$before = @(Invoke-RMQCheckedGit -GitPath $git -RepositoryRoot $repo -Arguments $statusArguments `
  -Stage ($Stage + '-status-before') -DeadlineSeconds 30 -OutputLimitBytes 8388608 -TempRoot $processTemp)
if (($before -join '').Trim().Length -ne 0) { throw 'Freeze and commit the complete candidate before aggregate.' }
$frozenHash = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.md')).Hash
if ($frozenHash -cne '80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24') {
  throw 'Frozen acceptance matrix changed.'
}
$toolBin = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin'
$started = [DateTime]::UtcNow.ToString('o')
$identity = [ordered]@{
  stage=$Stage;commit=$Commit;startedUtc=$started;
  coordinatorGrant=$grantPath;coordinatorGrantSHA256=[Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($grantBytes));
  coordinatorGrantBytesBase64=[Convert]::ToBase64String($grantBytes);
  command=@('pwsh','-NoProfile','-File','scripts/gate.ps1');leanNumThreads=1;
  deadlineSeconds=$DeadlineSeconds;outputLimitBytes=67108864;headBefore=$head;
  statusBefore=$before;frozenMatrixSHA256=$frozenHash
}
[void](New-Item -ItemType Directory -Path $processTemp -Force)
$launchPath = Join-Path $processTemp ($Stage + '-launch.json')
if (Test-Path -LiteralPath $launchPath) { throw 'An aggregate launch receipt already exists for this stage.' }
[IO.File]::WriteAllText($launchPath, ($identity | ConvertTo-Json -Depth 12), $utf8)
$result = $null; $failures = @(); $after = @(); $unexpected = @(); $headAfter = $null
$frozenAfter = $null; $archiveHash = $null; $passed = $false; $gatePassed = $false
try {
  $result = Invoke-RMQOwnedBoundedProcess -FilePath (Get-Command pwsh).Source `
    -Arguments @('-NoProfile','-File','scripts/gate.ps1') -WorkingDirectory $repo `
    -Stage $Stage -DeadlineSeconds $DeadlineSeconds -OutputLimitBytes 67108864 `
    -TempRoot $processTemp -Environment @{PATH=$toolBin+';'+$env:PATH;LEAN_NUM_THREADS='1'}
} catch { $failures += ('owned aggregate: ' + $_.ToString()) }
finally {
  # A helper/cleanup exception is failed or inconclusive evidence. Persist the
  # launch identity and every available restoration result even on that path.
  if ($null -ne $result) {
    try {
      $raw = $utf8.GetBytes(($result | ConvertTo-Json -Depth 16))
      $stream = [IO.File]::Create($archivePath)
      try {
        $gzip = [IO.Compression.GZipStream]::new($stream,[IO.Compression.CompressionLevel]::Optimal)
        try { $gzip.Write($raw,0,$raw.Length) } finally { $gzip.Dispose() }
      } finally { $stream.Dispose() }
      $archiveHash = (Get-FileHash -LiteralPath $archivePath).Hash
    } catch { $failures += ('output archive: ' + $_.ToString()) }
    $gatePassed = $result.ExitCode -eq 0 -and -not $result.TimedOut -and -not $result.OutputLimitExceeded
  }
  try {
    $headAfter = ((Invoke-RMQCheckedGit -GitPath $git -RepositoryRoot $repo -Arguments @('rev-parse','HEAD') `
      -Stage ($Stage + '-head-after') -DeadlineSeconds 30 -OutputLimitBytes 1048576 -TempRoot $processTemp) -join "`n").Trim()
  } catch { $failures += ('post-run HEAD: ' + $_.ToString()) }
  try {
    $after = @(Invoke-RMQCheckedGit -GitPath $git -RepositoryRoot $repo -Arguments $statusArguments `
      -Stage ($Stage + '-status-after') -DeadlineSeconds 30 -OutputLimitBytes 8388608 -TempRoot $processTemp)
    $expectedNewArchive = '?? ' + ('docs/internal/extensions/bv1/commands/' + $Stage + '-output.json.gz')
    $unexpected = @($after | Where-Object { $_ -cne $expectedNewArchive })
  } catch { $failures += ('post-run status: ' + $_.ToString()) }
  try { $frozenAfter = (Get-FileHash -LiteralPath (Join-Path $PSScriptRoot 'ACCEPTANCE_MATRIX.md')).Hash }
  catch { $failures += ('post-run frozen bytes: ' + $_.ToString()) }
  $passed = $gatePassed -and $failures.Count -eq 0 -and $null -ne $archiveHash -and
    $headAfter -ceq $Commit -and $unexpected.Count -eq 0 -and $frozenAfter -ceq $frozenHash
  $identity.finishedUtc = [DateTime]::UtcNow.ToString('o')
  $identity.launchReceipt = $launchPath
  $identity.result = if ($null -eq $result) { $null } else {
    [ordered]@{exitCode=$result.ExitCode;timedOut=$result.TimedOut;outputLimitExceeded=$result.OutputLimitExceeded;
      durationSeconds=$result.DurationSeconds;ownership=$result.Ownership}
  }
  $identity.headAfter=$headAfter; $identity.gatePassed=$gatePassed; $identity.passed=$passed
  $identity.statusAfter=$after; $identity.unexpectedStatus=$unexpected; $identity.failures=$failures
  $identity.frozenMatrixAfterSHA256=$frozenAfter
  $identity.outputArchive='commands/'+$Stage+'-output.json.gz'; $identity.archiveSHA256=$archiveHash
  [IO.File]::WriteAllText($summaryPath, ($identity | ConvertTo-Json -Depth 16), $utf8)
}
Write-Output "BV1-FINAL-GATE passed=$passed gatePassed=$gatePassed failures=$($failures.Count)"
if (-not $passed) { exit 1 }

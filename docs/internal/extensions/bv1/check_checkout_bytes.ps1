param(
  [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{40}$')][string]$Commit,
  [Parameter(Mandatory=$true)][ValidatePattern('^[a-z0-9-]+$')][string]$Stage,
  [Parameter(Mandatory=$true)][string[]]$DependencyRecords
)
$ErrorActionPreference = 'Stop'
$repo = (Resolve-Path (Join-Path $PSScriptRoot '../../../..')).Path
# The frozen matrix and old Get-FileHash receipts name this original checkout.
# Remap only that exact recorded root (or this invocation's root) to relative
# paths, so a fresh audit checkout never reads the old source tree by accident.
$recordedSourceRoot = 'C:\Users\poin\.codex\worktrees\c974\RMQ'
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$recordPath = Join-Path $PSScriptRoot ('commands/' + $Stage + '.json')
$checkout = Join-Path $repo ('.lake/' + $Stage + '-checkout')
if ((Test-Path -LiteralPath $recordPath) -or (Test-Path -LiteralPath $checkout)) {
  throw 'Evidence or isolated checkout already exists; choose a new stage.'
}
$git = (Get-Command git).Source
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$operations = @()
function Invoke-GitCheck([string]$Name, [string[]]$Arguments, [string]$Directory) {
  $Arguments = @('-c','core.excludesfile=') + $Arguments
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments $Arguments `
    -WorkingDirectory $Directory -Stage ($Stage + '-' + $Name) -DeadlineSeconds 300 `
    -OutputLimitBytes 33554432 -TempRoot (Join-Path $repo '.lake/bv1-byte-process')
  $script:operations += [ordered]@{name=$Name; arguments=$Arguments; result=$result}
  if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded) {
    throw ('Git byte-check operation failed: ' + $Name)
  }
  return @($result.StandardOutput)
}
function Get-SHA256([byte[]]$Bytes) {
  return [Convert]::ToHexString([Security.Cryptography.SHA256]::HashData($Bytes))
}
function Get-GitBlobId([byte[]]$Bytes) {
  # Git's blob identity hashes the exact bytes after this NUL-terminated header.
  # Comparing this with ls-tree's stored blob ID checks the real committed blob,
  # without passing binary evidence through PowerShell's text pipeline.
  $hash = [Security.Cryptography.IncrementalHash]::CreateHash(
    [Security.Cryptography.HashAlgorithmName]::SHA1)
  try {
    $hash.AppendData([Text.Encoding]::ASCII.GetBytes(('blob ' + $Bytes.Length + [char]0)))
    $hash.AppendData($Bytes)
    return [Convert]::ToHexString($hash.GetHashAndReset()).ToLowerInvariant()
  } finally { $hash.Dispose() }
}
$passed = $false
$rows = @()
$dependencyRows = @()
$dependencies = @()
$dependencyIdentities = @()
$entries = @()
$failure = $null
try {
  $resolved = ((Invoke-GitCheck 'resolve' @('rev-parse', ($Commit + '^{commit}')) $repo) -join "`n").Trim()
  if ($resolved -cne $Commit) { throw 'Exact commit resolution mismatch.' }
  $head = ((Invoke-GitCheck 'head' @('rev-parse','HEAD') $repo) -join "`n").Trim()
  if ($head -cne $Commit) { throw 'The exact candidate must be the current HEAD.' }
  $sourceStatus = Invoke-GitCheck 'source-status' @('status','--porcelain=v1','--untracked-files=all','--',
    'RMQ/Core/WordRAM/Bitvector','RMQ/Validation/PackedBitvector.lean',
    'scripts/packed_bitvector_*','docs/internal/extensions/bv1','lakefile.toml','.gitattributes') $repo
  if (($sourceStatus -join '').Trim().Length -ne 0) {
    throw 'Protected source paths contain modified or uncommitted artifacts.'
  }
  if ($DependencyRecords.Count -eq 0) { throw 'At least one replay dependency record is required.' }
  foreach ($dependencyRecord in $DependencyRecords) {
    if ($dependencyRecord -notmatch '^docs/internal/extensions/bv1/[a-zA-Z0-9_./-]+\.json$' -or
        $dependencyRecord.Contains('..')) { throw 'Dependency record must be a retained BV-1 JSON record.' }
    $dependencyBytes = [IO.File]::ReadAllBytes((Join-Path $repo $dependencyRecord))
    $dependencyEvidence = $utf8.GetString($dependencyBytes) | ConvertFrom-Json
    $recordDependencies = @($dependencyEvidence.sourceHashesBefore)
    # A file can be recorded in more than one replay role. Retain and check
    # every occurrence; conflicting hashes necessarily fail the raw-byte checks.
    if ($dependencyEvidence.passed -ne $true -or $recordDependencies.Count -eq 0) {
      throw 'Each passing replay must have a nonempty dependency registry.'
    }
    $dependencyIdentities += [ordered]@{path=$dependencyRecord;sha256=(Get-SHA256 $dependencyBytes);
      expectedCount=$recordDependencies.Count}
    foreach ($dependency in $recordDependencies) {
      $dependencyPath = [string]$dependency.path
      if ([IO.Path]::IsPathRooted($dependencyPath)) {
        $dependencyAbsolute = [IO.Path]::GetFullPath($dependencyPath)
        $repoPrefix = $repo.TrimEnd('\','/') + [IO.Path]::DirectorySeparatorChar
        $recordedPrefix = $recordedSourceRoot + [IO.Path]::DirectorySeparatorChar
        $receiptRoot = if ($dependencyAbsolute.StartsWith($repoPrefix,[StringComparison]::OrdinalIgnoreCase)) {
          $repo
        } elseif ($dependencyAbsolute.StartsWith($recordedPrefix,[StringComparison]::OrdinalIgnoreCase)) {
          $recordedSourceRoot
        } else {
          throw 'A replay dependency escapes both the current and frozen recorded source roots.'
        }
        $dependencyPath = [IO.Path]::GetRelativePath($receiptRoot,$dependencyAbsolute).Replace('\','/')
      }
      $dependencySHA = if ($null -ne $dependency.sha256) { [string]$dependency.sha256 } else {
        # Some Get-FileHash receipts retain only Path/Hash. Their SHA256
        # convention is still checked against the actual SHA256 of both files.
        if ($null -ne $dependency.Algorithm -and $dependency.Algorithm -cne 'SHA256') {
          throw 'Unsupported dependency hash algorithm.'
        }
        [string]$dependency.Hash
      }
      if ($dependencySHA -cnotmatch '^[0-9A-F]{64}$') { throw 'Invalid replay SHA256 identity.' }
      $dependencies += [ordered]@{record=$dependencyRecord;path=$dependencyPath;sha256=$dependencySHA}
    }
  }
  $format = ((Invoke-GitCheck 'object-format' @('rev-parse','--show-object-format') $repo) -join "`n").Trim()
  if ($format -cne 'sha1') { throw 'This version requires Git SHA-1 blob identities.' }
  $tree = Invoke-GitCheck 'tree' @('-c','core.quotepath=false','ls-tree','-r','--full-tree',$Commit) $repo
  foreach ($line in (($tree -join "`n") -split "`r?`n")) {
    if ($line -notmatch '^[0-9]+ blob ([0-9a-f]{40})\t(.+)$') { continue }
    $oid = $Matches[1]; $path = $Matches[2]
    if ($path -match '^(RMQ/Core/WordRAM/Bitvector/|RMQ/Validation/PackedBitvector\.lean$|scripts/packed_bitvector_[^/]+$|docs/internal/extensions/bv1/|lakefile\.toml$)') {
      $entries += [ordered]@{path=$path;blob=$oid}
    }
  }
  $mandatory = @('docs/internal/extensions/bv1/ACCEPTANCE_MATRIX.md',
    'RMQ/Core/WordRAM/Bitvector/Capstone.lean',
    'docs/internal/extensions/bv1/controls/public_expected_type.lean',
    'scripts/packed_bitvector_public_controls.ps1','lakefile.toml')
  foreach ($path in $mandatory) {
    if (@($entries | Where-Object { $_.path -ceq $path }).Count -ne 1) {
      throw ('Required committed identity missing: ' + $path)
    }
  }
  if ($entries.Count -eq 0 -or @($entries | Where-Object { $_.path.EndsWith('.gz') }).Count -eq 0) {
    throw 'Protected registry must be nonempty and include binary archives.'
  }
  # The local clone owns a separate Git directory. No shared metadata, mutable
  # object cache, cleanup, renormalization, or global Git setting is used.
  [void](Invoke-GitCheck 'clone' @('clone','--no-local','--no-checkout','--depth','1',$repo,$checkout) $repo)
  [void](Invoke-GitCheck 'checkout' @('-c','core.autocrlf=true','checkout','--detach',$Commit) $checkout)
  foreach ($entry in $entries) {
    $sourceBytes = [IO.File]::ReadAllBytes((Join-Path $repo $entry.path))
    $freshBytes = [IO.File]::ReadAllBytes((Join-Path $checkout $entry.path))
    $sourceBlob = Get-GitBlobId $sourceBytes
    $freshBlob = Get-GitBlobId $freshBytes
    $sourceSHA = Get-SHA256 $sourceBytes
    $freshSHA = Get-SHA256 $freshBytes
    $same = $sourceBlob -ceq $entry.blob -and $freshBlob -ceq $entry.blob -and $sourceSHA -ceq $freshSHA
    $rows += [ordered]@{path=$entry.path;committedBlob=$entry.blob;sourceBlob=$sourceBlob;
      checkoutBlob=$freshBlob;sourceBytes=$sourceBytes.Length;checkoutBytes=$freshBytes.Length;
      sourceSHA256=$sourceSHA;checkoutSHA256=$freshSHA;passed=$same}
  }
  foreach ($dependency in $dependencies) {
    if ($dependency.path -notmatch '^[a-zA-Z0-9_./-]+$' -or $dependency.path.Contains('..')) {
      throw 'Invalid replay dependency path.'
    }
    $sourceSHA = Get-SHA256 ([IO.File]::ReadAllBytes((Join-Path $repo $dependency.path)))
    $freshSHA = Get-SHA256 ([IO.File]::ReadAllBytes((Join-Path $checkout $dependency.path)))
    $dependencyRows += [ordered]@{record=$dependency.record;path=$dependency.path;replaySHA256=$dependency.sha256;
      sourceSHA256=$sourceSHA;checkoutSHA256=$freshSHA;
      passed=($sourceSHA -ceq $dependency.sha256 -and $freshSHA -ceq $dependency.sha256)}
  }
  $matrix = @($rows | Where-Object { $_.path -ceq $mandatory[0] })[0]
  if ($matrix.sourceSHA256 -cne '80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24') {
    throw 'Frozen acceptance bytes changed.'
  }
  $status = Invoke-GitCheck 'fresh-status' @('-c','core.autocrlf=true','status','--porcelain=v1','--untracked-files=all') $checkout
  if (($status -join '').Trim().Length -ne 0) { throw 'Fresh isolated checkout is not clean.' }
  $headAfter = ((Invoke-GitCheck 'source-head-after' @('rev-parse','HEAD') $repo) -join "`n").Trim()
  if ($headAfter -cne $Commit) { throw 'Source HEAD changed during the byte comparison.' }
  $passed = $rows.Count -eq $entries.Count -and @($rows | Where-Object { -not $_.passed }).Count -eq 0 -and
    $dependencyRows.Count -eq $dependencies.Count -and @($dependencyRows | Where-Object { -not $_.passed }).Count -eq 0
} catch { $failure = $_.Exception.Message }
[IO.File]::WriteAllText($recordPath, ([ordered]@{
  version=1;stage=$Stage;commit=$Commit;checkout=$checkout;checkoutAutoCRLF=$true;
  recordedSourceRoot=$recordedSourceRoot;
  identityMethod='Git ls-tree blob IDs versus SHA1(blob header + raw bytes), plus source/checkout SHA256';
  expectedCount=$entries.Count;executedCount=$rows.Count;passed=$passed;failure=$failure;
  dependencyRecords=$dependencyIdentities;expectedDependencies=$dependencies.Count;
  checkedDependencies=$dependencyRows.Count;dependencyRows=$dependencyRows;
  frozenMatrixExpectedSHA256='80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24';
  rows=$rows;operations=$operations
} | ConvertTo-Json -Depth 18), $utf8)
Write-Output "BV1-CHECKOUT-BYTES passed=$passed executed=$($rows.Count) expected=$($entries.Count)"
if (-not $passed) { throw ('Checkout-byte verification failed: ' + $failure) }

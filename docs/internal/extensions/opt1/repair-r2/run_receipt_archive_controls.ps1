# Replay the OPT-1-R2 receipt-archive verifier controls from the exact case registry.
#
# Every subprocess (Git state queries, the verifier, the mutation helper, the
# deadline sleeper and the selector self-invocations) runs through
# Invoke-RMQOwnedBoundedProcess from scripts/owned_process_tree.ps1 with a
# positive deadline and output ceiling. Negative cases mutate only a disposable
# copy of docs/internal/extensions/opt1/ created under -WorkRoot, which must lie
# outside the repository; the copy is removed in `finally` and its absence is
# checked. Before and after every case the runner compares the repository
# state (HEAD, status, worktree and index diffs) and the SHA-256 of every
# watched live file, so a case that touched the repository fails.
#
# Selector contract (-Case): omitted selects the full registry. A bound value
# must be a nonempty list of distinct, well-formed, registered IDs; an empty,
# whitespace, malformed, unknown or duplicated selector exits 2 before any case
# runs. Exit codes: 0 every selected case passed; 1 a case failed or the
# registry is not the pinned one; 2 selector error; 3 a selected case is
# inconclusive because this host cannot create its condition.
[CmdletBinding()]
param(
  [string[]]$Case,
  [string]$RepoRoot = '',
  [string]$WorkRoot = '',
  [string]$ReceiptPath = '',
  [string]$PythonPath = '',
  [ValidateRange(1, 7200)][int]$VerifierDeadlineSeconds = 900,
  [ValidateRange(1, 7200)][int]$HelperDeadlineSeconds = 300
)
$ErrorActionPreference = 'Stop'
$RegistryVersion = 'OPT1-R2-RECEIPT-ARCHIVE-CONTROLS-V1'
$PinnedCaseIds = @(
  'positive-tree', 'positive-committed', 'positive-copy',
  'changed-archive-header-byte', 'changed-archive-trailer-byte', 'missing-archive',
  'extra-archive', 'duplicate-manifest-entry', 'wrong-base-blob-id',
  'decompressed-byte-mismatch', 'original-restored', 'manifest-entry-removed',
  'new-result-line-file', 'deadline-descendant-cleanup',
  'selector-valid', 'selector-empty', 'selector-whitespace', 'selector-malformed',
  'selector-unknown', 'selector-duplicate'
)

function Stop-Selector([string]$Kind, [string]$Detail) {
  Write-Output "RECEIPT-CONTROLS: SELECTOR-ERROR [$Kind] $Detail"
  exit 2
}

# Selector boundary: decided from parameter binding state before any work.
$selected = @($PinnedCaseIds)
if ($PSBoundParameters.ContainsKey('Case')) {
  # Each bound element is split on commas, so `-File ... -Case a,b` (one string)
  # and `-Command ... -Case a,b` (an array) select the same cases.
  $requested = @(@($Case) | ForEach-Object { ([string]$_) -split ',' })
  if ($requested.Count -eq 0) { Stop-Selector 'empty' 'bound -Case holds no value' }
  foreach ($item in $requested) {
    if ($null -eq $item -or $item -eq '') { Stop-Selector 'empty' 'bound -Case holds an empty string' }
    if ($item.Trim() -eq '') { Stop-Selector 'whitespace' 'bound -Case holds only whitespace' }
    if ($item -cnotmatch '^[a-z0-9]+(-[a-z0-9]+)*$') { Stop-Selector 'malformed' "'$item' is not a lowercase hyphenated case id" }
    if ($PinnedCaseIds -cnotcontains $item) { Stop-Selector 'unknown' "'$item' is not a registered case id" }
  }
  $distinct = @($requested | Sort-Object -Unique -CaseSensitive)
  if ($distinct.Count -ne $requested.Count) { Stop-Selector 'duplicate' 'bound -Case repeats a case id' }
  $selected = @($PinnedCaseIds | Where-Object { $requested -ccontains $_ })
}

$scriptPath = $PSCommandPath
if ([string]::IsNullOrWhiteSpace($RepoRoot)) {
  $RepoRoot = Join-Path $PSScriptRoot '../../../../..'
}
$repo = [IO.Path]::GetFullPath($RepoRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($WorkRoot)) {
  $WorkRoot = Join-Path ([IO.Path]::GetTempPath()) ('opt1-r2-controls-' + [Guid]::NewGuid().ToString('N'))
}
$work = [IO.Path]::GetFullPath($WorkRoot)
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($work.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase) -or $work -eq $repo) {
  Write-Output "RECEIPT-CONTROLS: ERROR -WorkRoot $work lies inside the repository"
  exit 1
}
if (Test-Path -LiteralPath $work) {
  Write-Output "RECEIPT-CONTROLS: ERROR -WorkRoot $work already exists"
  exit 1
}
if ([string]::IsNullOrWhiteSpace($ReceiptPath)) { $ReceiptPath = $work + '.receipt.json' }
$receiptFull = [IO.Path]::GetFullPath($ReceiptPath)
if ([string]::IsNullOrWhiteSpace($PythonPath)) {
  $PythonPath = Resolve-RMQScalarApplicationPath @(Get-Command python -CommandType Application -ErrorAction Stop) 'python'
}
$gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
$hostPath = (Get-Process -Id $PID).Path
$packagedHost = $hostPath -like '*\WindowsApps\*'
$utf8 = [Text.UTF8Encoding]::new($false)
$rel = 'docs/internal/extensions/opt1/repair-r2/'
$verifier = Join-Path $repo ($rel + 'verify_receipt_archives.py')
$helper = Join-Path $repo ($rel + 'receipt_archive_control_helper.py')
$registryPath = Join-Path $repo ($rel + 'receipt_archive_controls.json')
$pyEnv = @{ PYTHONDONTWRITEBYTECODE = '1'; PYTHONIOENCODING = 'utf-8' }
[void](New-Item -ItemType Directory -Path $work)

$registry = Get-Content -LiteralPath $registryPath -Raw -Encoding UTF8 | ConvertFrom-Json
$registryIds = @($registry.cases | ForEach-Object { [string]$_.id })
if ([string]$registry.version -cne $RegistryVersion -or (($registryIds -join ',') -cne ($PinnedCaseIds -join ','))) {
  Write-Output "RECEIPT-CONTROLS: FAIL registry version or ordered case ids differ from the pinned $RegistryVersion list"
  Remove-Item -LiteralPath $work -Recurse -Force
  exit 1
}
$byId = @{}
foreach ($c in $registry.cases) { $byId[[string]$c.id] = $c }

$manifestRel = $rel + 'RECEIPT_ARCHIVES.json'
$manifest = Get-Content -LiteralPath (Join-Path $repo $manifestRel) -Raw -Encoding UTF8 | ConvertFrom-Json
$watched = @($rel + 'run_receipt_archive_controls.ps1', $rel + 'receipt_archive_control_helper.py',
  $rel + 'verify_receipt_archives.py', $rel + 'receipt_archive_controls.json', $manifestRel,
  'docs/internal/extensions/opt1/.gitattributes')
foreach ($entry in $manifest.archives) { $watched += [string]$entry.archivePath; $watched += [string]$entry.originalPath }

function Get-State([string]$Label, [string]$Temp) {
  $head = @(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') "$Label-head" 120 1048576 $Temp)
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $gitPath -DeadlineSeconds 300 `
    -OutputLimitBytes 8388608 -TempRoot $Temp -StagePrefix "$Label-state"
  $files = @()
  foreach ($w in $watched) {
    $full = Join-Path $repo $w
    $hash = if (Test-Path -LiteralPath $full -PathType Leaf) { (Get-FileHash -LiteralPath $full -Algorithm SHA256).Hash } else { 'ABSENT' }
    $files += ('{0} {1}' -f $hash, $w)
  }
  return ((@('HEAD ' + ($head -join '')) + @($state) + $files) -join "`n")
}

function Invoke-Owned([string]$File, [string[]]$Arguments, [string]$Stage, [int]$Deadline, [string]$Dir, [hashtable]$Environment) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $Dir -Stage $Stage `
    -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot (Join-Path $Dir 'owned') -Environment $Environment
}

function Get-FailCodes([string[]]$Lines) {
  $codes = @()
  foreach ($line in $Lines) {
    if ($line -match '^RECEIPT-ARCHIVES: FAIL \[([a-z0-9-]+)\] ') { $codes += $Matches[1] }
  }
  return @($codes | Sort-Object -Unique -CaseSensitive)
}

$headSha = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') 'controls-head' 120 1048576 (Join-Path $work 'git')) -join '').Trim()
$results = @()
$overall = 'PASS'
foreach ($id in $selected) {
  $c = $byId[$id]
  $caseDir = Join-Path $work $id
  [void](New-Item -ItemType Directory -Path $caseDir)
  $caseWatch = [Diagnostics.Stopwatch]::StartNew()
  $record = [ordered]@{ id = $id; kind = [string]$c.kind; requirement = [string]$c.requirement; verdict = 'FAIL'; detail = '' }
  $before = Get-State "$id-before" (Join-Path $work "$id-git-before")
  try {
    switch ([string]$c.kind) {
      { $_ -in @('verify-tree', 'verify-committed', 'verify-copy') } {
        $resultJson = Join-Path $caseDir 'verifier-result.json'
        $verifyArgs = @('-B', $verifier, '--repo', $repo, '--result-json', $resultJson)
        if ($c.kind -eq 'verify-tree') { $verifyArgs += @('--tree', $repo) }
        elseif ($c.kind -eq 'verify-committed') { $verifyArgs += @('--tree', $repo, '--committed', $headSha) }
        else {
          $copy = Join-Path $caseDir 'copy'
          $parent = Join-Path $copy 'docs/internal/extensions'
          [void](New-Item -ItemType Directory -Path $parent -Force)
          Copy-Item -LiteralPath (Join-Path $repo 'docs/internal/extensions/opt1') -Destination $parent -Recurse
          $mutation = Invoke-Owned $PythonPath @('-B', $helper, 'mutate', '--case', $id, '--copy', $copy, '--repo', $repo) `
            "$id-mutate" $HelperDeadlineSeconds $caseDir $pyEnv
          $record.mutation = [ordered]@{ exit = $mutation.ExitCode; seconds = $mutation.DurationSeconds; deadline = $mutation.DeadlineSeconds;
            timedOut = $mutation.TimedOut; stdout = @($mutation.StandardOutput); stderr = @($mutation.StandardError) }
          if ($mutation.ExitCode -ne 0 -or $mutation.TimedOut -or $mutation.OutputLimitExceeded) { throw "mutation helper failed for $id" }
          $verifyArgs += @('--tree', $copy)
        }
        $run = Invoke-Owned $PythonPath $verifyArgs "$id-verify" $VerifierDeadlineSeconds $caseDir $pyEnv
        $jsonCodes = @()
        if (Test-Path -LiteralPath $resultJson -PathType Leaf) {
          $jsonCodes = @((Get-Content -LiteralPath $resultJson -Raw -Encoding UTF8 | ConvertFrom-Json).failureCodes | ForEach-Object { [string]$_ })
        }
        $lineCodes = Get-FailCodes @($run.StandardOutput)
        $expectedCodes = @($c.expectedCodes | ForEach-Object { [string]$_ } | Sort-Object -Unique -CaseSensitive)
        $record.verifier = [ordered]@{ exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds;
          timedOut = $run.TimedOut; overflow = $run.OutputLimitExceeded; ownership = $run.Ownership;
          codes = @($lineCodes); jsonCodes = @($jsonCodes); expectedExit = [int]$c.expectedExit; expectedCodes = @($expectedCodes);
          stdout = @($run.StandardOutput); stderr = @($run.StandardError) }
        $resultLine = @($run.StandardOutput | Where-Object { $_ -like 'RECEIPT-ARCHIVES: RESULT: *' })
        $ok = (-not $run.TimedOut) -and (-not $run.OutputLimitExceeded) -and ($run.ExitCode -eq [int]$c.expectedExit) -and
          (($lineCodes -join ',') -ceq ($expectedCodes -join ',')) -and (($jsonCodes -join ',') -ceq ($expectedCodes -join ',')) -and
          ($resultLine.Count -eq 1) -and ($run.StandardError.Count -eq 0)
        if ([int]$c.expectedExit -eq 0) { $ok = $ok -and ($resultLine[0] -like 'RECEIPT-ARCHIVES: RESULT: PASS *') }
        $record.verdict = if ($ok) { 'PASS' } else { 'FAIL' }
        $record.detail = "exit $($run.ExitCode) codes [$($lineCodes -join ',')] expected exit $($c.expectedExit) codes [$($expectedCodes -join ',')]"
      }
      'deadline' {
        $pidFile = Join-Path $caseDir 'pids.txt'
        $run = Invoke-Owned $PythonPath @('-B', $helper, 'sleeper', '--pid-file', $pidFile) "$id-sleeper" ([int]$c.deadlineSeconds) $caseDir $pyEnv
        $pids = @()
        if (Test-Path -LiteralPath $pidFile) { $pids = @(((Get-Content -LiteralPath $pidFile -Raw) -split '\s+') | Where-Object { $_ -match '^[0-9]+$' } | ForEach-Object { [int]$_ }) }
        $alive = @($pids | Where-Object { $null -ne (Get-Process -Id $_ -ErrorAction SilentlyContinue) })
        $record.sleeper = [ordered]@{ exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds;
          timedOut = $run.TimedOut; terminatedIds = @($run.TerminatedIds); ownership = $run.Ownership; pids = @($pids); aliveAfter = @($alive);
          host = $hostPath; packagedHost = $packagedHost; stderr = @($run.StandardError) }
        if ($packagedHost) {
          $record.verdict = 'INCONCLUSIVE'
          $record.detail = 'packaged PowerShell host: kill-on-close job ownership of descendants is not established here'
        } elseif ($run.TimedOut -and $pids.Count -eq 2 -and $alive.Count -eq 0) {
          $record.verdict = 'PASS'
          $record.detail = "timed out after $($run.DurationSeconds) s; root $($pids[0]) and child $($pids[1]) both absent"
        } else {
          $record.detail = "timedOut $($run.TimedOut) pids [$($pids -join ',')] alive [$($alive -join ',')]"
        }
      }
      'selector' {
        $childWork = Join-Path $caseDir 'child-work'
        $childReceipt = Join-Path $caseDir 'child-receipt.json'
        $command = "& '$scriptPath' -Case $($c.selector) -RepoRoot '$repo' -WorkRoot '$childWork' -ReceiptPath '$childReceipt' -PythonPath '$PythonPath'; exit `$LASTEXITCODE"
        $run = Invoke-Owned $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) "$id-selector" 1800 $caseDir @{}
        $marker = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith([string]$c.expectedMarker, [StringComparison]::Ordinal) })
        $executedCases = @()
        if (Test-Path -LiteralPath $childReceipt -PathType Leaf) {
          $executedCases = @((Get-Content -LiteralPath $childReceipt -Raw -Encoding UTF8 | ConvertFrom-Json).executed | ForEach-Object { [string]$_ })
        }
        $record.selector = [ordered]@{ argument = [string]$c.selector; exit = $run.ExitCode; seconds = $run.DurationSeconds;
          deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut; expectedExit = [int]$c.expectedExit; expectedMarker = [string]$c.expectedMarker;
          childExecuted = @($executedCases); stdout = @($run.StandardOutput); stderr = @($run.StandardError) }
        $ok = (-not $run.TimedOut) -and ($run.ExitCode -eq [int]$c.expectedExit) -and ($marker.Count -eq 1)
        if ([int]$c.expectedExit -eq 2) {
          $ok = $ok -and -not (Test-Path -LiteralPath $childReceipt) -and -not (Test-Path -LiteralPath $childWork)
        } else {
          $ok = $ok -and (($executedCases -join ',') -ceq 'positive-tree')
        }
        $record.verdict = if ($ok) { 'PASS' } else { 'FAIL' }
        $record.detail = "exit $($run.ExitCode) marker $($marker.Count) executed [$($executedCases -join ',')]"
      }
      default { throw "unknown case kind $($c.kind)" }
    }
  } catch {
    $record.verdict = 'FAIL'
    $record.detail = 'runner error: ' + $_.Exception.Message
  } finally {
    Remove-Item -LiteralPath $caseDir -Recurse -Force -ErrorAction SilentlyContinue
    $record.copyRemoved = -not (Test-Path -LiteralPath $caseDir)
    $after = Get-State "$id-after" (Join-Path $work "$id-git-after")
    Remove-Item -LiteralPath (Join-Path $work "$id-git-before") -Recurse -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath (Join-Path $work "$id-git-after") -Recurse -Force -ErrorAction SilentlyContinue
    $record.repositoryStateUnchanged = ($before -ceq $after)
    $record.repositoryStateSha256 = [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($utf8.GetBytes($before))).Replace('-', '')
    if (-not $record.copyRemoved -or -not $record.repositoryStateUnchanged) {
      $record.verdict = 'FAIL'
      $record.detail += '; restoration failed'
    }
    $record.seconds = [Math]::Round($caseWatch.Elapsed.TotalSeconds, 3)
  }
  Write-Output ("RECEIPT-CONTROLS: {0} [{1}] {2} ({3} s)" -f $record.verdict, $id, $record.detail, $record.seconds)
  if ($record.verdict -eq 'FAIL') { $overall = 'FAIL' }
  elseif ($record.verdict -eq 'INCONCLUSIVE' -and $overall -eq 'PASS') { $overall = 'INCONCLUSIVE' }
  $results += $record
}

$executed = @($results | ForEach-Object { $_.id })
if (($executed -join ',') -cne ($selected -join ',')) { $overall = 'FAIL' }
Remove-Item -LiteralPath (Join-Path $work 'git') -Recurse -Force -ErrorAction SilentlyContinue
Remove-Item -LiteralPath $work -Recurse -Force -ErrorAction SilentlyContinue
$receipt = [ordered]@{
  version = 'OPT1-R2-RECEIPT-ARCHIVE-CONTROLS-RECEIPT-V1'; registryVersion = $RegistryVersion
  registrySha256 = (Get-FileHash -LiteralPath $registryPath -Algorithm SHA256).Hash
  runnerSha256 = (Get-FileHash -LiteralPath $scriptPath -Algorithm SHA256).Hash
  helperSha256 = (Get-FileHash -LiteralPath $helper -Algorithm SHA256).Hash
  verifierSha256 = (Get-FileHash -LiteralPath $verifier -Algorithm SHA256).Hash
  liveBytesNote = 'SHA-256 values are of the live checkout bytes that ran'
  repo = $repo; head = $headSha; host = [Environment]::MachineName; os = [Environment]::OSVersion.VersionString
  powershell = $PSVersionTable.PSVersion.ToString(); hostPath = $hostPath; packagedHost = $packagedHost
  python = $PythonPath; pythonSha256 = (Get-FileHash -LiteralPath $PythonPath -Algorithm SHA256).Hash
  workRoot = $work; workRootRemoved = -not (Test-Path -LiteralPath $work)
  selectorBound = $PSBoundParameters.ContainsKey('Case'); selected = @($selected); expected = @($selected); executed = @($executed)
  registryCaseCount = $PinnedCaseIds.Count; result = $overall; cases = @($results)
}
[IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
Write-Output ("RECEIPT-CONTROLS: RESULT: {0} executed {1} of {2} selected cases (registry {3}, {4} cases)" -f `
    $overall, $executed.Count, $selected.Count, $RegistryVersion, $PinnedCaseIds.Count)
if ($overall -eq 'PASS') { exit 0 }
if ($overall -eq 'INCONCLUSIVE') { exit 3 }
exit 1

#!/usr/bin/env pwsh
<#
NATIVE-1-R1 receipt-archive verifier controls.

Runs the exact versioned case registry below against verify_receipt_archives.py.
Positive cases verify the repository tree, the committed HEAD and an unmutated
disposable copy. Every negative case copies the manifest and the commands-root
archives to a disposable directory OUTSIDE the repository, applies exactly one
registered mutation there, runs the unchanged verifier on the copy, and requires
the exact exit code and the exact set of failure codes. Repository state (HEAD,
porcelain status and the bytes of every archive, manifest, verifier and control
file) must be identical before and after each case, and the copy must be gone.

Every subprocess runs through scripts/owned_process_tree.ps1
Invoke-RMQOwnedBoundedProcess with a positive deadline.

Selector -Case: omitted = the full registry; otherwise a comma-separated list of
registered ids. A bound empty string, whitespace, a malformed element, a
duplicate or an unknown id is rejected before any case runs.

Exit codes: 0 every selected case passed; 1 a case failed; 2 selector rejected
(nothing executed); 3 inconclusive host (nothing executed); 4 registry or setup
integrity failure.
#>
[CmdletBinding()]
param(
  [string]$Case,
  [string]$ReceiptPath,
  [string]$TempRoot,
  [int]$VerifierDeadlineSeconds = 900
)

$ErrorActionPreference = 'Stop'
$Prefix = 'RECEIPT-ARCHIVE-CONTROLS:'
$RegistryVersion = 'NATIVE1-R1-RECEIPT-ARCHIVE-CONTROLS-V1'
$ExpectedCaseCount = 19

function New-Case([string]$Id, [string]$Kind, [int]$ExpectedExit, [string[]]$ExpectedCodes, [string]$Selector, [string]$Marker) {
  return [pscustomobject]@{
    Id = $Id; Kind = $Kind; ExpectedExit = $ExpectedExit
    ExpectedCodes = @($ExpectedCodes | Where-Object { $_ } | Sort-Object)
    Selector = $Selector; Marker = $Marker
  }
}

# The registry. Expected exits and failure-code sets come from the manifest
# contract (REQ-NATIVE-R1-HISTORY / CHK-NATIVE-R1-VERIFICATION), not from a
# previous run of the verifier.
$Registry = @(
  (New-Case 'positive-worktree' 'verify-worktree' 0 @() '' ''),
  (New-Case 'positive-committed' 'verify-committed' 0 @() '' ''),
  (New-Case 'positive-copy' 'verify-copy' 0 @() '' ''),
  (New-Case 'changed-archive-header-byte' 'mutate' 1 @('archive-sha256-mismatch') '' ''),
  (New-Case 'changed-archive-trailer-byte' 'mutate' 1 @('archive-sha256-mismatch', 'archive-gzip-invalid') '' ''),
  (New-Case 'missing-archive' 'mutate' 1 @('archive-missing') '' ''),
  (New-Case 'extra-archive' 'mutate' 1 @('archive-extra') '' ''),
  (New-Case 'duplicate-manifest-entry' 'mutate' 1 @('manifest-duplicate-entry') '' ''),
  (New-Case 'wrong-base-blob-id' 'mutate' 1 @('base-blob-id-mismatch') '' ''),
  (New-Case 'decompressed-byte-mismatch' 'mutate' 1 @('decompressed-bytes-mismatch') '' ''),
  (New-Case 'original-restored' 'mutate' 1 @('original-present') '' ''),
  (New-Case 'manifest-entry-removed' 'mutate' 1 @('manifest-missing-entry', 'archive-extra') '' ''),
  (New-Case 'deadline-descendant-cleanup' 'hold' -1 @() '' ''),
  (New-Case 'selector-empty' 'selector' 2 @() '' 'empty'),
  (New-Case 'selector-whitespace' 'selector' 2 @() ' ' 'whitespace'),
  (New-Case 'selector-malformed' 'selector' 2 @() 'Positive-Copy!' 'malformed'),
  (New-Case 'selector-unknown' 'selector' 2 @() 'no-such-control' 'unknown'),
  (New-Case 'selector-duplicate' 'selector' 2 @() 'positive-copy,positive-copy' 'duplicate'),
  (New-Case 'selector-valid' 'selector' 0 @() 'positive-copy' 'positive-copy')
)

function Stop-Controls([int]$Code, [string]$Message) {
  Write-Host "$Prefix $Message"
  exit $Code
}

# --- registry integrity -------------------------------------------------------
$knownKinds = @('verify-worktree', 'verify-committed', 'verify-copy', 'mutate', 'hold', 'selector')
if ($Registry.Count -ne $ExpectedCaseCount) {
  Stop-Controls 4 "REGISTRY-INVALID registry $RegistryVersion has $($Registry.Count) cases; expected $ExpectedCaseCount"
}
$registryIds = @($Registry | ForEach-Object { $_.Id })
if (@($registryIds | Sort-Object -Unique).Count -ne $registryIds.Count) {
  Stop-Controls 4 "REGISTRY-INVALID duplicate case id in $RegistryVersion"
}
foreach ($entry in $Registry) {
  if ($knownKinds -notcontains $entry.Kind) { Stop-Controls 4 "REGISTRY-INVALID unknown kind $($entry.Kind) for $($entry.Id)" }
  if ($entry.Id -cnotmatch '^[a-z0-9]+(?:-[a-z0-9]+)*$') { Stop-Controls 4 "REGISTRY-INVALID malformed id $($entry.Id)" }
}

# --- selector (before any semantic execution) --------------------------------
$selectedCases = @()
if ($PSBoundParameters.ContainsKey('Case')) {
  if ($null -eq $Case -or $Case.Length -eq 0) {
    Stop-Controls 2 'SELECTOR-REJECTED [empty] -Case was bound to the empty string; omit it to run the full registry'
  }
  if ($Case.Trim().Length -eq 0) {
    Stop-Controls 2 'SELECTOR-REJECTED [whitespace] -Case contains only whitespace'
  }
  $parts = @($Case.Split(','))
  foreach ($part in $parts) {
    if ($part -cnotmatch '^[a-z0-9]+(?:-[a-z0-9]+)*$') {
      Stop-Controls 2 "SELECTOR-REJECTED [malformed] element '$part' is not a lowercase case id"
    }
  }
  $duplicates = @($parts | Group-Object -CaseSensitive | Where-Object { $_.Count -gt 1 } | ForEach-Object { $_.Name })
  if ($duplicates.Count -gt 0) {
    Stop-Controls 2 "SELECTOR-REJECTED [duplicate] $($duplicates -join ',') selected more than once"
  }
  foreach ($part in $parts) {
    if ($registryIds -cnotcontains $part) {
      Stop-Controls 2 "SELECTOR-REJECTED [unknown] '$part' is not in $RegistryVersion"
    }
  }
  $selectedCases = @($Registry | Where-Object { $parts -ccontains $_.Id })
} else {
  $selectedCases = @($Registry)
}
if ($selectedCases.Count -eq 0) {
  Stop-Controls 2 'SELECTOR-REJECTED [empty] selection resolved to no case'
}

# --- host and environment -----------------------------------------------------
$hostPath = (Get-Process -Id $PID).Path
if ($hostPath -match '[\\/]WindowsApps[\\/]') {
  Stop-Controls 3 ("INCONCLUSIVE host $hostPath is an MSIX-packaged PowerShell; processes it launches " +
    'leave the owned kill-on-close job on this host, so bounded ownership cannot be established. ' +
    'Run under Windows PowerShell 5.1 or a non-packaged pwsh.')
}
$RepoRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..\..\..\..'))
. (Join-Path $RepoRoot 'scripts/owned_process_tree.ps1')
$pythonCommand = @(Get-Command python -CommandType Application -ErrorAction SilentlyContinue)
if ($pythonCommand.Count -eq 0) { Stop-Controls 4 'SETUP-FAILED python is not on PATH' }
$Python = Resolve-RMQScalarApplicationPath $pythonCommand 'python'
if ($Python -match '[\\/]WindowsApps[\\/]') {
  Stop-Controls 3 "INCONCLUSIVE python $Python is an MSIX alias; its process tree cannot be owned on this host"
}
if ([string]::IsNullOrWhiteSpace($TempRoot)) {
  $TempRoot = Join-Path ([IO.Path]::GetTempPath()) 'rmq-native1-r1-controls'
}
$TempRoot = [IO.Path]::GetFullPath($TempRoot)
$repoWithSeparator = $RepoRoot.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($TempRoot.StartsWith($repoWithSeparator, [StringComparison]::OrdinalIgnoreCase)) {
  Stop-Controls 4 "SETUP-FAILED -TempRoot $TempRoot is inside the repository"
}
if (-not (Test-Path -LiteralPath $TempRoot -PathType Container)) {
  [void](New-Item -ItemType Directory -Path $TempRoot -Force)
}
$OwnedLogRoot = Join-Path $TempRoot 'owned'
$ManifestRel = 'docs/internal/extensions/native1/repair-r1/RECEIPT_ARCHIVES.json'
$CommandsRel = 'docs/internal/extensions/native1/commands'
$Verifier = Join-Path $PSScriptRoot 'verify_receipt_archives.py'
$Helper = Join-Path $PSScriptRoot 'receipt_archive_control_helper.py'
$PythonEnvironment = @{ PYTHONIOENCODING = 'utf-8'; PYTHONDONTWRITEBYTECODE = '1' }
$encoding = New-Object System.Text.UTF8Encoding($false)

function Invoke-Owned([string]$Stage, [string]$FilePath, [string[]]$Arguments, [int]$Deadline, [hashtable]$Environment) {
  if ($null -eq $Environment) { $Environment = @{} }
  $started = [DateTime]::UtcNow
  try {
    $r = Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments -WorkingDirectory $RepoRoot `
      -Stage $Stage -DeadlineSeconds $Deadline -OutputLimitBytes 67108864 -TempRoot $OwnedLogRoot -Environment $Environment
    return [pscustomobject]@{
      Command = (@($FilePath) + @($Arguments)) -join ' '
      ExitCode = $r.ExitCode; TimedOut = $r.TimedOut; OutputLimitExceeded = $r.OutputLimitExceeded
      DurationSeconds = $r.DurationSeconds; DeadlineSeconds = $r.DeadlineSeconds; Ownership = $r.Ownership
      TerminatedIds = @($r.TerminatedIds)
      Stdout = @($r.StandardOutput); Stderr = @($r.StandardError | Where-Object { $_ -ne '' })
      Error = ''
    }
  } catch {
    return [pscustomobject]@{
      Command = (@($FilePath) + @($Arguments)) -join ' '
      ExitCode = -1; TimedOut = $false; OutputLimitExceeded = $false
      DurationSeconds = [Math]::Round(([DateTime]::UtcNow - $started).TotalSeconds, 3); DeadlineSeconds = $Deadline
      Ownership = ''; TerminatedIds = @(); Stdout = @(); Stderr = @(); Error = $_.Exception.Message
    }
  }
}

# Ordinal prefix test. `-like` treats [ ] as a wildcard character class, so it
# cannot match the bracketed case ids these lines carry.
function Test-LinePrefix([string]$Line, [string]$Expected) {
  return ($null -ne $Line -and $Line.StartsWith($Expected, [StringComparison]::Ordinal))
}

function Get-FileDigest([string]$Path) {
  $stream = [IO.File]::OpenRead($Path)
  try {
    $sha = [Security.Cryptography.SHA256]::Create()
    return ([BitConverter]::ToString($sha.ComputeHash($stream)) -replace '-', '')
  } finally {
    $stream.Dispose()
  }
}

function Get-RelativeFiles([string]$Root, [string]$Filter) {
  $dir = Join-Path $Root $CommandsRel
  if (-not (Test-Path -LiteralPath $dir -PathType Container)) { return @() }
  $base = [IO.Path]::GetFullPath($Root).TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  return @(Get-ChildItem -LiteralPath $dir -Recurse -File -Filter $Filter | ForEach-Object {
    $_.FullName.Substring($base.Length) -replace '\\', '/'
  } | Sort-Object)
}

function Get-RepositoryState {
  $head = Invoke-Owned 'state-head' 'git' @('-C', $RepoRoot, 'rev-parse', 'HEAD') 120 @{}
  $status = Invoke-Owned 'state-status' 'git' @('-C', $RepoRoot, 'status', '--porcelain=v1', '--untracked-files=all') 300 @{}
  if ($head.ExitCode -ne 0 -or $status.ExitCode -ne 0) {
    throw "could not read repository state: head=$($head.ExitCode) status=$($status.ExitCode) $($head.Error) $($status.Error)"
  }
  $lines = New-Object System.Collections.Generic.List[string]
  $lines.Add('HEAD ' + ($head.Stdout -join ''))
  foreach ($line in $status.Stdout) { $lines.Add('STATUS ' + $line) }
  $tracked = @($ManifestRel,
    'docs/internal/extensions/native1/repair-r1/verify_receipt_archives.py',
    'docs/internal/extensions/native1/repair-r1/receipt_archive_control_helper.py',
    'docs/internal/extensions/native1/repair-r1/run_receipt_archive_controls.ps1')
  $tracked += @(Get-RelativeFiles $RepoRoot '*.gz')
  foreach ($rel in $tracked) {
    $full = Join-Path $RepoRoot $rel
    if (Test-Path -LiteralPath $full -PathType Leaf) {
      $lines.Add("FILE $rel " + (Get-FileDigest $full))
    } else {
      $lines.Add("FILE $rel ABSENT")
    }
  }
  $text = $lines -join "`n"
  $sha = [Security.Cryptography.SHA256]::Create()
  return [pscustomobject]@{
    Digest = ([BitConverter]::ToString($sha.ComputeHash($encoding.GetBytes($text))) -replace '-', '')
    Head = ($head.Stdout -join '')
    StatusLines = $status.Stdout.Count
  }
}

function Get-CopyDigest([string]$Copy) {
  $files = @(Get-ChildItem -LiteralPath $Copy -Recurse -File | Sort-Object FullName)
  $base = [IO.Path]::GetFullPath($Copy).TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
  $text = ($files | ForEach-Object { ($_.FullName.Substring($base.Length) -replace '\\', '/') + ' ' + (Get-FileDigest $_.FullName) }) -join "`n"
  $sha = [Security.Cryptography.SHA256]::Create()
  return ([BitConverter]::ToString($sha.ComputeHash($encoding.GetBytes($text))) -replace '-', '')
}

function New-DisposableCopy {
  $copy = Join-Path $TempRoot ('copy-' + [Guid]::NewGuid().ToString('N'))
  [void](New-Item -ItemType Directory -Path $copy)
  $sources = @($ManifestRel) + @(Get-RelativeFiles $RepoRoot '*.gz')
  foreach ($rel in $sources) {
    $from = Join-Path $RepoRoot $rel
    $to = Join-Path $copy $rel
    [void](New-Item -ItemType Directory -Path (Split-Path -Parent $to) -Force)
    Copy-Item -LiteralPath $from -Destination $to
    if ((Get-FileDigest $from) -ne (Get-FileDigest $to)) { throw "disposable copy of $rel differs from its source" }
  }
  return $copy
}

function Get-VerifierVerdict($Run, $Entry) {
  $codes = @($Run.Stdout | ForEach-Object {
    if ($_ -match '^RECEIPT-ARCHIVES: FAIL \[([a-z0-9-]+)\] ') { $Matches[1] }
  } | Sort-Object -Unique)
  $resultLines = @($Run.Stdout | Where-Object { $_ -match '^RECEIPT-ARCHIVES: RESULT: (PASS|FAIL) ' })
  $errors = @($Run.Stdout | Where-Object { $_ -match '^RECEIPT-ARCHIVES: ERROR' })
  $problems = @()
  if ($Run.Error) { $problems += "process error: $($Run.Error)" }
  if ($Run.TimedOut) { $problems += 'verifier timed out' }
  if ($Run.ExitCode -ne $Entry.ExpectedExit) { $problems += "exit $($Run.ExitCode) != expected $($Entry.ExpectedExit)" }
  if (($codes -join ',') -cne ($Entry.ExpectedCodes -join ',')) { $problems += "codes [$($codes -join ',')] != expected [$($Entry.ExpectedCodes -join ',')]" }
  $expectedResult = if ($Entry.ExpectedExit -eq 0) { 'PASS' } else { 'FAIL' }
  if ($resultLines.Count -ne 1 -or $resultLines[0] -notmatch "^RECEIPT-ARCHIVES: RESULT: $expectedResult ") { $problems += "missing or wrong RESULT line (expected $expectedResult)" }
  if ($errors.Count -gt 0) { $problems += "environment error lines: $($errors -join ' | ')" }
  if ($Run.Stderr.Count -gt 0) { $problems += "stderr: $($Run.Stderr -join ' | ')" }
  return [pscustomobject]@{ Codes = $codes; Problems = $problems }
}

$caseResults = New-Object System.Collections.Generic.List[object]
$failed = 0
Write-Host "$Prefix registry $RegistryVersion ($($Registry.Count) cases); selected $($selectedCases.Count); host $($PSVersionTable.PSEdition) $($PSVersionTable.PSVersion) $hostPath; python $Python"

foreach ($entry in $selectedCases) {
  $record = [ordered]@{
    id = $entry.Id; kind = $entry.Kind; expectedExit = $entry.ExpectedExit; expectedCodes = $entry.ExpectedCodes
    processes = @(); codes = @(); problems = @(); stateBefore = ''; stateAfter = ''; restored = $false; verdict = 'FAIL'
  }
  $problems = @()
  $copy = $null
  $pidDir = $null
  $childTemp = $null
  $before = $null
  try {
    $before = Get-RepositoryState
    $record.stateBefore = $before.Digest
    switch ($entry.Kind) {
      { $_ -in @('verify-worktree', 'verify-committed') } {
        $arguments = @($Verifier, '--tree', $RepoRoot, '--repo', $RepoRoot)
        if ($entry.Kind -eq 'verify-committed') { $arguments += @('--committed', 'HEAD') }
        $run = Invoke-Owned "verify-$($entry.Id)" $Python $arguments $VerifierDeadlineSeconds $PythonEnvironment
        $record.processes += $run
        $verdict = Get-VerifierVerdict $run $entry
        $record.codes = $verdict.Codes
        $problems += $verdict.Problems
      }
      { $_ -in @('verify-copy', 'mutate') } {
        $copy = New-DisposableCopy
        $pristine = Get-CopyDigest $copy
        if ($entry.Kind -eq 'mutate') {
          $mutation = Invoke-Owned "mutate-$($entry.Id)" $Python @($Helper, 'mutate', '--case', $entry.Id, '--copy', $copy, '--repo', $RepoRoot) 300 $PythonEnvironment
          $record.processes += $mutation
          $applied = @($mutation.Stdout | Where-Object { Test-LinePrefix $_ "MUTATION-APPLIED [$($entry.Id)] " })
          if ($mutation.ExitCode -ne 0 -or $applied.Count -eq 0 -or $mutation.Error) {
            $problems += "mutation setup failed (exit $($mutation.ExitCode)): $($mutation.Stdout -join ' | ') $($mutation.Stderr -join ' | ') $($mutation.Error)"
          } elseif ((Get-CopyDigest $copy) -eq $pristine) {
            $problems += 'mutation left the disposable copy unchanged'
          }
        }
        if ($problems.Count -eq 0) {
          $run = Invoke-Owned "verify-$($entry.Id)" $Python @($Verifier, '--tree', $copy, '--repo', $RepoRoot) $VerifierDeadlineSeconds $PythonEnvironment
          $record.processes += $run
          $verdict = Get-VerifierVerdict $run $entry
          $record.codes = $verdict.Codes
          $problems += $verdict.Problems
        }
      }
      'hold' {
        $pidDir = Join-Path $TempRoot ('hold-' + [Guid]::NewGuid().ToString('N'))
        [void](New-Item -ItemType Directory -Path $pidDir)
        $run = Invoke-Owned 'hold-deadline' $Python @($Helper, 'hold', '--pid-dir', $pidDir) 10 $PythonEnvironment
        $record.processes += $run
        $rootPidFile = Join-Path $pidDir 'root.pid'
        $childPidFile = Join-Path $pidDir 'child.pid'
        if ($run.Error) { $problems += "owned process error: $($run.Error)" }
        if (-not $run.TimedOut) { $problems += "deadline did not fire (exit $($run.ExitCode))" }
        if (-not (Test-Path -LiteralPath $rootPidFile) -or -not (Test-Path -LiteralPath $childPidFile)) {
          $problems += 'hold root/child did not both start before the deadline; the condition was not created'
        } else {
          $ids = @([int](Get-Content -LiteralPath $rootPidFile -Raw), [int](Get-Content -LiteralPath $childPidFile -Raw))
          $record.heldProcessIds = $ids
          $watch = [Diagnostics.Stopwatch]::StartNew()
          $alive = @($ids | Where-Object { Get-Process -Id $_ -ErrorAction SilentlyContinue })
          while ($alive.Count -gt 0 -and $watch.Elapsed.TotalSeconds -lt 10) {
            Start-Sleep -Milliseconds 100
            $alive = @($ids | Where-Object { Get-Process -Id $_ -ErrorAction SilentlyContinue })
          }
          if ($alive.Count -gt 0) {
            $problems += "held process(es) survived the owned deadline: $($alive -join ',')"
            foreach ($id in $alive) { Stop-Process -Id $id -Force -ErrorAction SilentlyContinue }
          }
        }
      }
      'selector' {
        $childTemp = Join-Path $TempRoot ('child-' + [Guid]::NewGuid().ToString('N'))
        $command = "& '$PSCommandPath' -Case '$($entry.Selector)' -TempRoot '$childTemp' -VerifierDeadlineSeconds $VerifierDeadlineSeconds; exit `$LASTEXITCODE"
        $deadline = if ($entry.ExpectedExit -eq 0) { $VerifierDeadlineSeconds + 600 } else { 300 }
        $run = Invoke-Owned "selector-$($entry.Id)" $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) $deadline @{}
        $record.processes += $run
        $caseLines = @($run.Stdout | Where-Object { $_ -match '^RECEIPT-ARCHIVE-CONTROLS: (PASS|FAIL) \[' })
        if ($run.Error) { $problems += "owned process error: $($run.Error)" }
        if ($run.TimedOut) { $problems += 'child runner timed out' }
        if ($run.ExitCode -ne $entry.ExpectedExit) { $problems += "child exit $($run.ExitCode) != expected $($entry.ExpectedExit)" }
        if ($entry.ExpectedExit -eq 2) {
          $rejections = @($run.Stdout | Where-Object { Test-LinePrefix $_ "RECEIPT-ARCHIVE-CONTROLS: SELECTOR-REJECTED [$($entry.Marker)] " })
          if ($rejections.Count -ne 1) { $problems += "expected one SELECTOR-REJECTED [$($entry.Marker)] line" }
          if ($caseLines.Count -ne 0) { $problems += 'a rejected selector executed a case' }
        } else {
          if ($caseLines.Count -ne 1 -or -not (Test-LinePrefix $caseLines[0] "RECEIPT-ARCHIVE-CONTROLS: PASS [$($entry.Marker)] ")) {
            $problems += "expected exactly one PASS [$($entry.Marker)] case line, saw $($caseLines.Count)"
          }
          $summary = @($run.Stdout | Where-Object { Test-LinePrefix $_ 'RECEIPT-ARCHIVE-CONTROLS: RESULT: PASS executed 1 of 1 selected cases ' })
          if ($summary.Count -ne 1) { $problems += 'missing child RESULT: PASS executed 1 of 1 summary' }
        }
      }
    }
  } catch {
    $problems += "case setup/execution error: $($_.Exception.Message)"
  } finally {
    foreach ($dir in @($copy, $pidDir, $childTemp)) {
      if ($dir -and (Test-Path -LiteralPath $dir)) {
        Remove-Item -LiteralPath $dir -Recurse -Force -ErrorAction SilentlyContinue
      }
      if ($dir -and (Test-Path -LiteralPath $dir)) { $problems += "disposable directory was not removed: $dir" }
    }
    try {
      $after = Get-RepositoryState
      $record.stateAfter = $after.Digest
      $record.restored = ($null -ne $before -and $after.Digest -eq $before.Digest)
      if (-not $record.restored) { $problems += 'repository state differs after the case' }
    } catch {
      $problems += "could not re-read repository state: $($_.Exception.Message)"
    }
  }
  $record.problems = $problems
  $durations = @($record.processes | ForEach-Object { $_.DurationSeconds })
  $exits = @($record.processes | ForEach-Object { $_.ExitCode })
  $deadlines = @($record.processes | ForEach-Object { $_.DeadlineSeconds })
  if ($problems.Count -eq 0) {
    $record.verdict = 'PASS'
    Write-Host ("$Prefix PASS [{0}] exits={1} codes=[{2}] durations={3}s deadlines={4}s restored={5}" -f $entry.Id, ($exits -join '/'), ($record.codes -join ','), ($durations -join '/'), ($deadlines -join '/'), $record.restored)
  } else {
    $failed += 1
    Write-Host ("$Prefix FAIL [{0}] exits={1} codes=[{2}] durations={3}s deadlines={4}s restored={5}: {6}" -f $entry.Id, ($exits -join '/'), ($record.codes -join ','), ($durations -join '/'), ($deadlines -join '/'), $record.restored, ($problems -join '; '))
  }
  $caseResults.Add([pscustomobject]$record)
}

$executed = $caseResults.Count
$passed = @($caseResults | Where-Object { $_.verdict -eq 'PASS' }).Count
if ($ReceiptPath) {
  $receipt = [ordered]@{
    registryVersion = $RegistryVersion; registryCases = $Registry.Count; selected = @($selectedCases | ForEach-Object { $_.Id })
    executed = $executed; passed = $passed; failed = $failed
    host = [ordered]@{ edition = [string]$PSVersionTable.PSEdition; version = [string]$PSVersionTable.PSVersion; path = $hostPath }
    python = $Python; repository = $RepoRoot; head = (Get-RepositoryState).Head
    finishedUtc = [DateTime]::UtcNow.ToString('o')
    # ToArray, not @(...): Windows PowerShell 5.1 ConvertTo-Json throws
    # "Argument types do not match" on an array wrapped around a generic List.
    cases = $caseResults.ToArray()
  }
  # LF line ends on every host, so a committed receipt blob equals the bytes written.
  $receiptText = (($receipt | ConvertTo-Json -Depth 8) -replace "`r`n", "`n") + "`n"
  [IO.File]::WriteAllText([IO.Path]::GetFullPath($ReceiptPath), $receiptText, $encoding)
}
if ($executed -ne $selectedCases.Count) {
  Stop-Controls 4 "RESULT: FAIL executed $executed of $($selectedCases.Count) selected cases (a case was lost)"
}
if ($failed -gt 0) {
  Stop-Controls 1 "RESULT: FAIL $failed of $executed selected cases failed (registry $RegistryVersion, $($Registry.Count) cases)"
}
Stop-Controls 0 "RESULT: PASS executed $executed of $($selectedCases.Count) selected cases (registry $RegistryVersion, $($Registry.Count) cases)"

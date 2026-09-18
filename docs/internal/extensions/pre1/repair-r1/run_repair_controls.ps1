# Replay the PRE-1-R1 archive and reword verifier controls from the exact case registry.
#
# Every subprocess (Git state queries, the exports, the verifiers, the mutation
# helper, the deadline sleeper and the selector and registry self-invocations)
# runs through Invoke-RMQOwnedBoundedProcess from scripts/owned_process_tree.ps1
# with a positive deadline and output ceiling. Copy cases export the exact
# committed blobs of the lane root and docs/internal/audit_reports/ at -Revision
# into a disposable directory under -WorkRoot, which must lie outside the
# repository; the helper mutates only that copy, the copy is removed in
# `finally` and its absence is checked. Before and after every case the runner
# compares the repository state (HEAD, status, worktree and index diffs) and
# the SHA-256 of every watched live file, so a case that touched the
# repository fails.
#
# Selector contract (-Case): omitted selects the full registry. A bound value
# must be a nonempty list of distinct, well-formed, registered IDs; an empty,
# whitespace, malformed, unknown or duplicated selector exits 2 before the
# registry is read or any case runs. -SelectorProbeOnly prints the selection
# after the registry check and exits 0 without running a case.
# Exit codes: 0 every selected case passed; 1 a case failed or the registry is
# not the pinned one; 2 selector error; 3 a selected case is inconclusive
# because this host cannot create its condition.
[CmdletBinding()]
param(
  [string[]]$Case,
  [switch]$SelectorProbeOnly,
  [string]$RepoRoot = '',
  [string]$WorkRoot = '',
  [string]$ReceiptPath = '',
  [string]$PythonPath = '',
  [string]$RegistryPath = '',
  [string]$Revision = 'HEAD',
  [ValidateRange(1, 7200)][int]$VerifierDeadlineSeconds = 900,
  [ValidateRange(1, 7200)][int]$HelperDeadlineSeconds = 300,
  [ValidateRange(1, 7200)][int]$ChildDeadlineSeconds = 1800
)
$ErrorActionPreference = 'Stop'
$RegistryVersion = 'PRE1-R1-REPAIR-CONTROLS-V1'
$PinnedCaseIds = @(
  'archives-positive-tree', 'archives-positive-committed', 'archives-positive-copy',
  'archives-changed-archive-header-byte', 'archives-changed-archive-trailer-byte', 'archives-missing-archive',
  'archives-extra-archive', 'archives-duplicate-manifest-entry', 'archives-wrong-base-blob-id',
  'archives-decompressed-byte-mismatch', 'archives-original-restored', 'archives-audit-report-restored',
  'archives-manifest-entry-removed', 'archives-result-line-file',
  'rewords-positive-committed', 'rewords-positive-copy', 'rewords-changed-integer',
  'rewords-unrecorded-line-changed', 'rewords-missing-recorded-line', 'rewords-reintroduced-pattern',
  'rewords-wrong-base-line-hash', 'rewords-manifest-entry-removed', 'rewords-pattern-in-new-file',
  'deadline-descendant-cleanup',
  'registry-missing-case', 'registry-reordered-cases', 'registry-version-changed',
  'selector-omitted', 'selector-valid', 'selector-empty', 'selector-whitespace', 'selector-malformed',
  'selector-unknown', 'selector-duplicate'
)

function Stop-Selector([string]$Kind, [string]$Detail) {
  Write-Output "REPAIR-CONTROLS: SELECTOR-ERROR [$Kind] $Detail"
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
if ([string]::IsNullOrWhiteSpace($RepoRoot)) { $RepoRoot = Join-Path $PSScriptRoot '../../../../..' }
$repo = [IO.Path]::GetFullPath($RepoRoot)
$rel = 'docs/internal/extensions/pre1/repair-r1/'
if ([string]::IsNullOrWhiteSpace($RegistryPath)) { $RegistryPath = Join-Path $repo ($rel + 'repair_controls.json') }
$registryFull = [IO.Path]::GetFullPath($RegistryPath)
$registry = Get-Content -LiteralPath $registryFull -Raw -Encoding UTF8 | ConvertFrom-Json
$registryIds = @($registry.cases | ForEach-Object { [string]$_.id })
if ([string]$registry.version -cne $RegistryVersion -or (($registryIds -join ',') -cne ($PinnedCaseIds -join ','))) {
  Write-Output "REPAIR-CONTROLS: FAIL registry version or ordered case ids differ from the pinned $RegistryVersion list ($($registryIds.Count) ids read, $($PinnedCaseIds.Count) pinned)"
  exit 1
}
if ($SelectorProbeOnly) {
  Write-Output ("REPAIR-CONTROLS: SELECTOR-PROBE selected={0} ids={1}" -f $selected.Count, ($selected -join ','))
  exit 0
}
$byId = @{}
foreach ($c in $registry.cases) { $byId[[string]$c.id] = $c }

. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($WorkRoot)) {
  $WorkRoot = Join-Path ([IO.Path]::GetTempPath()) ('pre1-r1-controls-' + [Guid]::NewGuid().ToString('N'))
}
$work = [IO.Path]::GetFullPath($WorkRoot)
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($work.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase) -or $work -eq $repo) {
  Write-Output "REPAIR-CONTROLS: ERROR -WorkRoot $work lies inside the repository"
  exit 1
}
if (Test-Path -LiteralPath $work) {
  Write-Output "REPAIR-CONTROLS: ERROR -WorkRoot $work already exists"
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
# .NET hashing rather than Get-FileHash: Windows PowerShell 5.1 started from a
# pwsh 7 parent inherits a module path under which Get-FileHash does not load.
function Get-Sha256Hex([string]$Path) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return [BitConverter]::ToString($sha.ComputeHash([IO.File]::ReadAllBytes($Path))).Replace('-', '') }
  finally { $sha.Dispose() }
}
$verifiers =@{ archives = (Join-Path $repo ($rel + 'verify_receipt_archives.py')); rewords = (Join-Path $repo ($rel + 'verify_rewords.py')) }
$failPrefix = @{ archives = 'RECEIPT-ARCHIVES'; rewords = 'REWORDS' }
$helper = Join-Path $repo ($rel + 'repair_control_helper.py')
$pyEnv = @{ PYTHONDONTWRITEBYTECODE = '1'; PYTHONIOENCODING = 'utf-8' }
[void](New-Item -ItemType Directory -Path $work)

$watched = @($rel + 'run_repair_controls.ps1', $rel + 'repair_control_helper.py', $rel + 'verify_receipt_archives.py',
  $rel + 'verify_rewords.py', $rel + 'repair_controls.json', $rel + 'RECEIPT_ARCHIVES.json', $rel + 'REWORDS.json',
  'docs/internal/extensions/pre1/.gitattributes', 'docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md',
  'docs/internal/extensions/pre1/REPORT.md')
$manifest = Get-Content -LiteralPath (Join-Path $repo ($rel + 'RECEIPT_ARCHIVES.json')) -Raw -Encoding UTF8 | ConvertFrom-Json
foreach ($entry in $manifest.archives) { $watched += [string]$entry.archivePath; $watched += [string]$entry.originalPath }

function Get-State([string]$Label, [string]$Temp) {
  $head = @(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') "$Label-head" 120 1048576 $Temp)
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $gitPath -DeadlineSeconds 300 `
    -OutputLimitBytes 8388608 -TempRoot $Temp -StagePrefix "$Label-state"
  $files = @()
  foreach ($w in $watched) {
    $full = Join-Path $repo $w
    $hash = if (Test-Path -LiteralPath $full -PathType Leaf) { (Get-Sha256Hex $full) } else { 'ABSENT' }
    $files += ('{0} {1}' -f $hash, $w)
  }
  return ((@('HEAD ' + ($head -join '')) + @($state) + $files) -join "`n")
}

function Invoke-Owned([string]$File, [string[]]$Arguments, [string]$Stage, [int]$Deadline, [string]$Dir, [hashtable]$Environment) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $Dir -Stage $Stage `
    -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot (Join-Path $Dir 'owned') -Environment $Environment
}

function Get-FailCodes([string]$Prefix, [string[]]$Lines) {
  $codes = @()
  foreach ($line in $Lines) {
    if ($line -match ('^' + [regex]::Escape($Prefix) + ': FAIL \[([a-z0-9-]+)\] ')) { $codes += $Matches[1] }
  }
  return @($codes | Sort-Object -Unique -CaseSensitive)
}

$revisionSha = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', '--verify', "$Revision^{commit}") 'controls-revision' 120 1048576 (Join-Path $work 'git')) -join '').Trim()
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
        $name = [string]$c.verifier
        $resultJson = Join-Path $caseDir 'verifier-result.json'
        $verifyArgs = @('-B', $verifiers[$name], '--repo', $repo, '--result-json', $resultJson)
        if ($c.kind -eq 'verify-tree') { $verifyArgs += @('--tree', $repo) }
        elseif ($c.kind -eq 'verify-committed') { $verifyArgs += @('--tree', $repo, '--committed', $revisionSha) }
        else {
          $copy = Join-Path $caseDir 'copy'
          $export = Invoke-Owned $PythonPath @('-B', $helper, 'export', '--repo', $repo, '--rev', $revisionSha, '--dest', $copy) `
            "$id-export" $HelperDeadlineSeconds $caseDir $pyEnv
          $mutation = Invoke-Owned $PythonPath @('-B', $helper, 'mutate', '--case', $id, '--copy', $copy, '--repo', $repo) `
            "$id-mutate" $HelperDeadlineSeconds $caseDir $pyEnv
          $record.export = [ordered]@{ exit = $export.ExitCode; seconds = $export.DurationSeconds; deadline = $export.DeadlineSeconds;
            timedOut = $export.TimedOut; stdout = @($export.StandardOutput); stderr = @($export.StandardError) }
          $record.mutation = [ordered]@{ exit = $mutation.ExitCode; seconds = $mutation.DurationSeconds; deadline = $mutation.DeadlineSeconds;
            timedOut = $mutation.TimedOut; stdout = @($mutation.StandardOutput); stderr = @($mutation.StandardError) }
          if ($export.ExitCode -ne 0 -or $export.TimedOut -or $export.OutputLimitExceeded) { throw "export failed for $id" }
          if ($mutation.ExitCode -ne 0 -or $mutation.TimedOut -or $mutation.OutputLimitExceeded) { throw "mutation helper failed for $id" }
          $verifyArgs += @('--tree', $copy)
        }
        $run = Invoke-Owned $PythonPath $verifyArgs "$id-verify" $VerifierDeadlineSeconds $caseDir $pyEnv
        $jsonCodes = @()
        if (Test-Path -LiteralPath $resultJson -PathType Leaf) {
          $jsonCodes = @((Get-Content -LiteralPath $resultJson -Raw -Encoding UTF8 | ConvertFrom-Json).failureCodes | ForEach-Object { [string]$_ })
        }
        $lineCodes = Get-FailCodes $failPrefix[$name] @($run.StandardOutput)
        $expectedCodes = @($c.expectedCodes | ForEach-Object { [string]$_ } | Sort-Object -Unique -CaseSensitive)
        $record.verifier = [ordered]@{ name = $name; exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds;
          timedOut = $run.TimedOut; overflow = $run.OutputLimitExceeded; ownership = $run.Ownership;
          codes = @($lineCodes); jsonCodes = @($jsonCodes); expectedExit = [int]$c.expectedExit; expectedCodes = @($expectedCodes);
          stdout = @($run.StandardOutput); stderr = @($run.StandardError) }
        $resultLine = @($run.StandardOutput | Where-Object { $_ -like ($failPrefix[$name] + ': RESULT: *') })
        $ok = (-not $run.TimedOut) -and (-not $run.OutputLimitExceeded) -and ($run.ExitCode -eq [int]$c.expectedExit) -and
          (($lineCodes -join ',') -ceq ($expectedCodes -join ',')) -and (($jsonCodes -join ',') -ceq ($expectedCodes -join ',')) -and
          ($resultLine.Count -eq 1) -and ($run.StandardError.Count -eq 0)
        if ([int]$c.expectedExit -eq 0) { $ok = $ok -and ($resultLine[0] -like ($failPrefix[$name] + ': RESULT: PASS *')) }
        $record.verdict = if ($ok) { 'PASS' } else { 'FAIL' }
        $record.detail = "$name exit $($run.ExitCode) codes [$($lineCodes -join ',')] expected exit $($c.expectedExit) codes [$($expectedCodes -join ',')]"
      }
      'deadline' {
        if ($packagedHost) {
          # The condition cannot be created here: under an MSIX-packaged host the
          # kill-on-close job does not hold descendants (NATIVE-1-R1 host finding),
          # and a surviving child keeps the redirected output locked. Launching the
          # sleeper would leave orphans without measuring anything, so the case is
          # reported INCONCLUSIVE without starting it.
          $record.sleeper = [ordered]@{ started = $false; host = $hostPath; packagedHost = $true }
          $record.verdict = 'INCONCLUSIVE'
          $record.detail = 'packaged PowerShell host: descendant cleanup cannot be established here; sleeper not started'
          break
        }
        $pidFile = Join-Path $caseDir 'pids.txt'
        $run = $null
        $launchError = ''
        try {
          $run = Invoke-Owned $PythonPath @('-B', $helper, 'sleeper', '--pid-file', $pidFile) "$id-sleeper" ([int]$c.deadlineSeconds) $caseDir $pyEnv
        } catch { $launchError = $_.Exception.Message }
        $pids = @()
        if (Test-Path -LiteralPath $pidFile) { $pids = @(((Get-Content -LiteralPath $pidFile -Raw) -split '\s+') | Where-Object { $_ -match '^[0-9]+$' } | ForEach-Object { [int]$_ }) }
        $alive = @($pids | Where-Object { $null -ne (Get-Process -Id $_ -ErrorAction SilentlyContinue) })
        foreach ($p in $alive) { Stop-Process -Id $p -Force -ErrorAction SilentlyContinue }
        $record.sleeper = [ordered]@{ started = $true; launchError = $launchError; host = $hostPath; packagedHost = $false; pids = @($pids); aliveAfter = @($alive) }
        if ($null -ne $run) {
          $record.sleeper.exit = $run.ExitCode; $record.sleeper.seconds = $run.DurationSeconds; $record.sleeper.deadline = $run.DeadlineSeconds
          $record.sleeper.timedOut = $run.TimedOut; $record.sleeper.terminatedIds = @($run.TerminatedIds); $record.sleeper.ownership = $run.Ownership
          $record.sleeper.stderr = @($run.StandardError)
        }
        if ($null -eq $run) {
          $record.detail = "owned launch failed: $launchError; alive [$($alive -join ',')] stopped"
        } elseif ($run.TimedOut -and $pids.Count -eq 2 -and $alive.Count -eq 0) {
          $record.verdict = 'PASS'
          $record.detail = "timed out after $($run.DurationSeconds) s; root $($pids[0]) and child $($pids[1]) both absent"
        } else {
          $record.detail = "timedOut $($run.TimedOut) pids [$($pids -join ',')] alive [$($alive -join ',')]"
          foreach ($p in $alive) { Stop-Process -Id $p -Force -ErrorAction SilentlyContinue }
        }
      }
      'registry' {
        $mutated = Get-Content -LiteralPath $registryFull -Raw -Encoding UTF8 | ConvertFrom-Json
        switch ([string]$c.mutation) {
          'remove-last' { $mutated.cases = @($mutated.cases | Select-Object -First (@($mutated.cases).Count - 1)) }
          'swap-first-two' { $all = @($mutated.cases); $mutated.cases = @($all[1], $all[0]) + @($all | Select-Object -Skip 2) }
          'version' { $mutated.version = 'PRE1-R1-REPAIR-CONTROLS-V0' }
          default { throw "unknown registry mutation $($c.mutation)" }
        }
        $mutatedPath = Join-Path $caseDir 'registry.json'
        [IO.File]::WriteAllText($mutatedPath, ($mutated | ConvertTo-Json -Depth 8), $utf8)
        $command = "& '$scriptPath' -SelectorProbeOnly -RepoRoot '$repo' -RegistryPath '$mutatedPath'; exit `$LASTEXITCODE"
        $run = Invoke-Owned $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) "$id-registry" $ChildDeadlineSeconds $caseDir @{}
        $marker = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith([string]$c.expectedMarker, [StringComparison]::Ordinal) })
        $probe = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith('REPAIR-CONTROLS: SELECTOR-PROBE', [StringComparison]::Ordinal) })
        $record.registry = [ordered]@{ mutation = [string]$c.mutation; exit = $run.ExitCode; seconds = $run.DurationSeconds;
          deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut; expectedExit = [int]$c.expectedExit;
          stdout = @($run.StandardOutput); stderr = @($run.StandardError) }
        $ok = (-not $run.TimedOut) -and ($run.ExitCode -eq [int]$c.expectedExit) -and ($marker.Count -eq 1) -and ($probe.Count -eq 0)
        $record.verdict = if ($ok) { 'PASS' } else { 'FAIL' }
        $record.detail = "exit $($run.ExitCode) marker $($marker.Count) probe $($probe.Count)"
      }
      'selector' {
        $childWork = Join-Path $caseDir 'child-work'
        $childReceipt = Join-Path $caseDir 'child-receipt.json'
        $selectorArg = if ($null -eq $c.selector) { '' } else { "-Case $($c.selector) " }
        $probeArg = if ([bool]$c.probe) { '-SelectorProbeOnly ' } else { '' }
        $command = "& '$scriptPath' $selectorArg$probeArg-RepoRoot '$repo' -WorkRoot '$childWork' -ReceiptPath '$childReceipt' -PythonPath '$PythonPath' -Revision '$revisionSha'; exit `$LASTEXITCODE"
        $run = Invoke-Owned $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) "$id-selector" $ChildDeadlineSeconds $caseDir @{}
        $marker = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith([string]$c.expectedMarker, [StringComparison]::Ordinal) })
        $executedCases = @()
        if (Test-Path -LiteralPath $childReceipt -PathType Leaf) {
          $executedCases = @((Get-Content -LiteralPath $childReceipt -Raw -Encoding UTF8 | ConvertFrom-Json).executed | ForEach-Object { [string]$_ })
        }
        $record.selector = [ordered]@{ argument = if ($null -eq $c.selector) { '(omitted)' } else { [string]$c.selector }; probe = [bool]$c.probe
          exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut
          expectedExit = [int]$c.expectedExit; expectedMarker = [string]$c.expectedMarker; childExecuted = @($executedCases)
          stdout = @($run.StandardOutput); stderr = @($run.StandardError) }
        $ok = (-not $run.TimedOut) -and ($run.ExitCode -eq [int]$c.expectedExit) -and ($marker.Count -eq 1)
        if ([int]$c.expectedExit -eq 2 -or [bool]$c.probe) {
          $ok = $ok -and -not (Test-Path -LiteralPath $childReceipt) -and -not (Test-Path -LiteralPath $childWork)
        } else {
          $ok = $ok -and (($executedCases -join ',') -ceq [string]$c.selector)
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
  Write-Output ("REPAIR-CONTROLS: {0} [{1}] {2} ({3} s)" -f $record.verdict, $id, $record.detail, $record.seconds)
  if ($record.verdict -eq 'FAIL') { $overall = 'FAIL' }
  elseif ($record.verdict -eq 'INCONCLUSIVE' -and $overall -eq 'PASS') { $overall = 'INCONCLUSIVE' }
  $results += $record
}

$executed = @($results | ForEach-Object { $_.id })
if (($executed -join ',') -cne ($selected -join ',')) { $overall = 'FAIL' }
Remove-Item -LiteralPath (Join-Path $work 'git') -Recurse -Force -ErrorAction SilentlyContinue
Remove-Item -LiteralPath $work -Recurse -Force -ErrorAction SilentlyContinue
$receipt = [ordered]@{
  version = 'PRE1-R1-REPAIR-CONTROLS-RECEIPT-V1'; registryVersion = $RegistryVersion
  registrySha256 = (Get-Sha256Hex $registryFull)
  runnerSha256 = (Get-Sha256Hex $scriptPath)
  helperSha256 = (Get-Sha256Hex $helper)
  archivesVerifierSha256 = (Get-Sha256Hex $verifiers['archives'])
  rewordsVerifierSha256 = (Get-Sha256Hex $verifiers['rewords'])
  liveBytesNote = 'SHA-256 values are of the live checkout bytes that ran'
  repo = $repo; revision = $revisionSha; host = [Environment]::MachineName; os = [Environment]::OSVersion.VersionString
  powershell = $PSVersionTable.PSVersion.ToString(); hostPath = $hostPath; packagedHost = $packagedHost
  python = $PythonPath; pythonSha256 = (Get-Sha256Hex $PythonPath)
  workRoot = $work; workRootRemoved = -not (Test-Path -LiteralPath $work)
  selectorBound = $PSBoundParameters.ContainsKey('Case'); selected = @($selected); expected = @($selected); executed = @($executed)
  registryCaseCount = $PinnedCaseIds.Count; result = $overall; cases = @($results)
}
[IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
Write-Output ("REPAIR-CONTROLS: RESULT: {0} executed {1} of {2} selected cases (registry {3}, {4} cases)" -f `
    $overall, $executed.Count, $selected.Count, $RegistryVersion, $PinnedCaseIds.Count)
if ($overall -eq 'PASS') { exit 0 }
if ($overall -eq 'INCONCLUSIVE') { exit 3 }
exit 1

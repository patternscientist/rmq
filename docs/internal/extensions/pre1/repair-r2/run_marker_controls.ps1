# Replay the PRE-1-R2 verdict-marker control matrix from its exact case registry.
#
# A consumer case copies one typed consumer from the live checkout (whose
# CRLF-normalized text must equal the committed blob at -Revision) into a
# disposable directory under -WorkRoot, which must lie outside the repository,
# applies the registered edits (each anchor must occur exactly once), and runs
# `lake env lean <copy>` from the repository root with LEAN_NUM_THREADS=1 as an
# owned bounded process. The verdict reads the exit code, the number of output
# lines carrying the consumer's marker, and the error locations of the copy:
# a failure class is exercised only if its registered diagnostics occur in an
# error line and, when required, an error is located at the first inserted line.
# Before and after every case the runner compares the repository state (HEAD,
# status, worktree and index diffs) and the SHA-256 of every watched file, and
# checks that the copy was removed.
#
# -Observe records the outcome of consumer cases without applying the repaired
# expectation (used to reproduce the defect on an unrepaired tree): a completed,
# exercised case is OBSERVED, and the receipt records whether the marker was
# printed on a failing run. Without -Case, -Observe selects the consumer cases.
#
# Selector contract (-Case): omitted selects the full registry. A bound value
# must be a nonempty list of distinct, well-formed, registered IDs; an empty,
# whitespace, malformed, unknown or duplicated selector exits 2 before the
# registry is read or any case runs. -SelectorProbeOnly prints the selection
# after the registry check and exits 0 without running a case.
# Exit codes: 0 every selected case passed (or was observed); 1 a case failed or
# the registry is not the pinned one; 2 selector error; 3 a selected case is
# inconclusive because this host cannot create its condition.
[CmdletBinding()]
param(
  [string[]]$Case,
  [switch]$SelectorProbeOnly,
  [switch]$Observe,
  [string]$RepoRoot = '',
  [string]$WorkRoot = '',
  [string]$ReceiptPath = '',
  [string]$RegistryPath = '',
  [string]$LakePath = '',
  [string]$Revision = 'HEAD',
  [ValidateRange(1, 7200)][int]$ChildDeadlineSeconds = 1800
)
$ErrorActionPreference = 'Stop'
$RegistryVersion = 'PRE1-R2-MARKER-CONTROLS-V1'
# CRLF-to-LF normalized, lowercase hex.
$RegistryContentSha256 = '11abd16938cbd0537a35460bdc203b50052bc5523b31847dc315aeec31aad81a'
$PinnedCaseIds = @(
  'builder-unchanged', 'builder-a-example', 'builder-b-guard', 'builder-b-run-cmd', 'builder-c-max-recursion',
  'builder-d-unknown-identifier', 'builder-e-unreferenced', 'builder-f-after-marker',
  'capstone-unchanged', 'capstone-a-example', 'capstone-b-guard', 'capstone-c-max-recursion',
  'capstone-d-unknown-identifier', 'capstone-e-unreferenced', 'capstone-f-after-marker',
  'contract-unchanged', 'contract-a-example', 'contract-b-guard', 'contract-c-max-recursion',
  'contract-d-unknown-identifier', 'contract-e-unreferenced',
  'spec-unchanged', 'spec-a-example', 'spec-b-guard', 'spec-c-max-recursion', 'spec-d-unknown-identifier',
  'spec-e-unreferenced',
  'stage-unchanged', 'stage-a-example', 'stage-b-guard', 'stage-c-max-recursion', 'stage-d-unknown-identifier',
  'stage-e-unreferenced',
  'deadline-descendant-cleanup',
  'registry-remove-last', 'registry-swap-first-two', 'registry-version', 'registry-content',
  'selector-omitted', 'selector-valid', 'selector-empty', 'selector-whitespace', 'selector-malformed',
  'selector-unknown', 'selector-duplicate'
)

function Stop-Selector([string]$Kind, [string]$Detail) {
  Write-Output "MARKER-CONTROLS: SELECTOR-ERROR [$Kind] $Detail"
  exit 2
}

# Selector boundary: decided from parameter binding state before any work.
$selectorBound = $PSBoundParameters.ContainsKey('Case')
$selected = @($PinnedCaseIds)
if ($selectorBound) {
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
$rel = 'docs/internal/extensions/pre1/repair-r2/'
if ([string]::IsNullOrWhiteSpace($RegistryPath)) { $RegistryPath = Join-Path $repo ($rel + 'marker_controls.json') }
$registryFull = [IO.Path]::GetFullPath($RegistryPath)
$utf8Strict = [Text.UTF8Encoding]::new($false, $true)
$utf8 = [Text.UTF8Encoding]::new($false)
# .NET hashing rather than Get-FileHash: Windows PowerShell 5.1 started from a
# pwsh 7 parent inherits a module path under which Get-FileHash does not load.
function Get-Sha256Hex([byte[]]$Bytes) {
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return [BitConverter]::ToString($sha.ComputeHash($Bytes)).Replace('-', '').ToLowerInvariant() }
  finally { $sha.Dispose() }
}
$registryBytes = [IO.File]::ReadAllBytes($registryFull)
$registryText = $utf8Strict.GetString($registryBytes)
$registryContent = Get-Sha256Hex ($utf8.GetBytes($registryText.Replace("`r`n", "`n")))
$registry = $registryText | ConvertFrom-Json
$registryIds = @($registry.cases | ForEach-Object { [string]$_.id })
if ([string]$registry.version -cne $RegistryVersion -or (($registryIds -join ',') -cne ($PinnedCaseIds -join ',')) -or
    $registryContent -cne $RegistryContentSha256) {
  Write-Output "MARKER-CONTROLS: FAIL registry version, ordered case ids or content differ from the pinned $RegistryVersion registry ($($registryIds.Count) ids read, $($PinnedCaseIds.Count) pinned, content $registryContent)"
  exit 1
}
$byId = @{}
foreach ($c in $registry.cases) { $byId[[string]$c.id] = $c }
if ($Observe -and -not $selectorBound) {
  $selected = @($PinnedCaseIds | Where-Object { [string]$byId[$_].kind -ceq 'consumer' })
}
if ($SelectorProbeOnly) {
  Write-Output ("MARKER-CONTROLS: SELECTOR-PROBE selected={0} ids={1}" -f $selected.Count, ($selected -join ','))
  exit 0
}

. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($WorkRoot)) {
  $WorkRoot = Join-Path ([IO.Path]::GetTempPath()) ('pre1-r2-marker-controls-' + [Guid]::NewGuid().ToString('N'))
}
$work = [IO.Path]::GetFullPath($WorkRoot)
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($work.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase) -or $work -eq $repo) {
  Write-Output "MARKER-CONTROLS: ERROR -WorkRoot $work lies inside the repository"
  exit 1
}
if (Test-Path -LiteralPath $work) {
  Write-Output "MARKER-CONTROLS: ERROR -WorkRoot $work already exists"
  exit 1
}
if ([string]::IsNullOrWhiteSpace($ReceiptPath)) { $ReceiptPath = $work + '.receipt.json' }
$receiptFull = [IO.Path]::GetFullPath($ReceiptPath)
$gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
$hostPath = (Get-Process -Id $PID).Path
$packagedHost = $hostPath -like '*\WindowsApps\*'
if ([string]::IsNullOrWhiteSpace($LakePath)) {
  # The installed pinned toolchain, never the elan proxy.
  $toolchain = [IO.File]::ReadAllText((Join-Path $repo 'lean-toolchain')).Trim()
  $elanRoot = [Environment]::GetEnvironmentVariable('ELAN_HOME')
  if ([string]::IsNullOrWhiteSpace($elanRoot)) { $elanRoot = Join-Path ([Environment]::GetFolderPath('UserProfile')) '.elan' }
  $binary = if (Test-RMQOwnedProcessWindows) { 'lake.exe' } else { 'lake' }
  $LakePath = Join-Path (Join-Path (Join-Path $elanRoot 'toolchains') $toolchain.Replace('/', '--').Replace(':', '---')) ('bin/' + $binary)
}
$lake = [IO.Path]::GetFullPath($LakePath)
[void](New-Item -ItemType Directory -Path $work)

$watched = @($rel + 'run_marker_controls.ps1', $rel + 'marker_controls.json')
foreach ($name in $registry.consumers.PSObject.Properties.Name) { $watched += [string]$registry.consumers.$name.path }

function Get-State([string]$Label, [string]$Temp) {
  $head = @(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') "$Label-head" 120 1048576 $Temp)
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $gitPath -DeadlineSeconds 300 `
    -OutputLimitBytes 8388608 -TempRoot $Temp -StagePrefix "$Label-state"
  $files = @()
  foreach ($w in $watched) {
    $full = Join-Path $repo $w
    $hash = if (Test-Path -LiteralPath $full -PathType Leaf) { (Get-Sha256Hex ([IO.File]::ReadAllBytes($full))) } else { 'ABSENT' }
    $files += ('{0} {1}' -f $hash, $w)
  }
  return ((@('HEAD ' + ($head -join '')) + @($state) + $files) -join "`n")
}

function Invoke-Owned([string]$File, [string[]]$Arguments, [string]$Stage, [int]$Deadline, [string]$Dir, [string]$Temp, [hashtable]$Environment) {
  return Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $Dir -Stage $Stage `
    -DeadlineSeconds $Deadline -OutputLimitBytes 33554432 -TempRoot (Join-Path $Temp 'owned') -Environment $Environment
}

function Set-Edit([string]$Text, [object]$Edit, [bool]$Crlf, [string]$CaseId) {
  $anchor = ([string]$Edit.anchor).Replace("`r`n", "`n")
  $insert = ([string]$Edit.text).Replace("`r`n", "`n")
  if ($Crlf) { $anchor = $anchor.Replace("`n", "`r`n"); $insert = $insert.Replace("`n", "`r`n") }
  $at = $Text.IndexOf($anchor, [StringComparison]::Ordinal)
  if ($at -lt 0 -or $Text.IndexOf($anchor, $at + $anchor.Length, [StringComparison]::Ordinal) -ge 0) {
    throw "anchor for $CaseId must occur exactly once"
  }
  switch ([string]$Edit.op) {
    'insert-after' { $offset = $at + $anchor.Length; return [pscustomobject]@{ Text = $Text.Substring(0, $offset) + $insert + $Text.Substring($offset); Offset = $offset } }
    'replace' { return [pscustomobject]@{ Text = $Text.Substring(0, $at) + $insert + $Text.Substring($at + $anchor.Length); Offset = $at } }
    default { throw "unknown edit op $($Edit.op) for $CaseId" }
  }
}

$revisionSha = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', '--verify', "$Revision^{commit}") 'controls-revision' 120 1048576 (Join-Path $work 'git')) -join '').Trim()
$results = @()
$overall = 'PASS'
foreach ($id in $selected) {
  $c = $byId[$id]
  $caseDir = Join-Path $work $id
  [void](New-Item -ItemType Directory -Path $caseDir)
  $caseTemp = Join-Path $work "$id-temp"
  $caseWatch = [Diagnostics.Stopwatch]::StartNew()
  $record = [ordered]@{ id = $id; kind = [string]$c.kind; requirement = [string]$c.requirement; verdict = 'FAIL'; detail = '' }
  $before = Get-State "$id-before" (Join-Path $work "$id-git-before")
  try {
    switch ([string]$c.kind) {
      'consumer' {
        $consumer = $registry.consumers.([string]$c.consumer)
        $relPath = [string]$consumer.path
        $live = [IO.File]::ReadAllBytes((Join-Path $repo $relPath))
        $liveText = $utf8Strict.GetString($live)
        # The live bytes, CRLF-normalized, must be the committed blob at the revision.
        $blobId = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', "$revisionSha`:$relPath") "$id-blob" 120 1048576 $caseTemp) -join '').Trim()
        $normalized = $utf8.GetBytes($liveText.Replace("`r`n", "`n"))
        $sha1 = [Security.Cryptography.SHA1]::Create()
        try {
          $headerBytes = [Text.Encoding]::ASCII.GetBytes("blob $($normalized.Length)" + [char]0)
          $liveBlobId = [BitConverter]::ToString($sha1.ComputeHash([byte[]]($headerBytes + $normalized))).Replace('-', '').ToLowerInvariant()
        } finally { $sha1.Dispose() }
        if ($liveBlobId -cne $blobId) { throw "live $relPath (blob $liveBlobId) differs from its blob $blobId at $revisionSha" }
        $crlf = $liveText.Contains("`r`n")
        $text = $liveText
        $firstOffset = -1
        foreach ($edit in @($c.edits)) {
          $applied = Set-Edit $text $edit $crlf $id
          $text = $applied.Text
          if ($firstOffset -lt 0) { $firstOffset = $applied.Offset }
        }
        $firstLine = if ($firstOffset -ge 0) { ($text.Substring(0, $firstOffset) -split "`n").Count } else { 0 }
        $copy = Join-Path $caseDir ([IO.Path]::GetFileName($relPath))
        [IO.File]::WriteAllBytes($copy, $utf8.GetBytes($text))
        $run = Invoke-Owned $lake @('env', 'lean', $copy) "$id-lean" ([int]$consumer.deadlineSeconds) $repo $caseTemp @{ LEAN_NUM_THREADS = '1' }
        $lines = @($run.Output | ForEach-Object { [string]$_ })
        $markerText = [string]$consumer.marker
        $markerLines = @($lines | Where-Object { $_.Contains($markerText) })
        $locationPattern = '[\\/]' + [regex]::Escape([IO.Path]::GetFileName($relPath)) + ':(\d+):(\d+): error'
        $errorLines = @($lines | Where-Object { $_ -match $locationPattern })
        $errorLocations = @($errorLines | ForEach-Object { if ($_ -match $locationPattern) { '{0}:{1}' -f $Matches[1], $Matches[2] } })
        $errorAtFirst = @($errorLines | Where-Object { ($_ -match $locationPattern) -and ([int]$Matches[1] -eq $firstLine) }).Count -gt 0
        $missingDiagnostics = @(@($c.diagnostics) | Where-Object { $d = [string]$_; @($errorLines | Where-Object { $_.Contains($d) }).Count -eq 0 })
        $exercised = ($missingDiagnostics.Count -eq 0) -and ((-not [bool]$c.errorAtFirstEdit) -or $errorAtFirst)
        $completed = (-not $run.TimedOut) -and (-not $run.OutputLimitExceeded)
        $record.lean = [ordered]@{ consumer = [string]$c.consumer; path = $relPath; class = [string]$c.class
          blob = $blobId; liveSha256 = Get-Sha256Hex $live; copySha256 = Get-Sha256Hex ([IO.File]::ReadAllBytes($copy)); firstEditLine = $firstLine
          exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut
          outputLimitExceeded = $run.OutputLimitExceeded; ownership = $run.Ownership
          markerLines = $markerLines.Count; errorLocations = @($errorLocations)
          errorHeads = @($errorLines | ForEach-Object { $h = ($_ -replace '^.*?: error: ', ''); if ($h.Length -gt 120) { $h.Substring(0, 120) } else { $h } })
          errorAtFirstEdit = $errorAtFirst; missingDiagnostics = @($missingDiagnostics); stderrLineCount = @($run.StandardError).Count
          expectedExit = [string]$c.expectedExit; expectedMarker = [bool]$c.expectedMarker }
        $exitOk = if ([string]$c.expectedExit -ceq 'zero') { $run.ExitCode -eq 0 } else { $run.ExitCode -ne 0 }
        $markerOk = if ([bool]$c.expectedMarker) { $markerLines.Count -eq 1 } else { $markerLines.Count -eq 0 }
        $cleanOk = if ([string]$c.expectedExit -ceq 'zero') { $errorLines.Count -eq 0 } else { $true }
        if ($Observe) {
          $record.lean.markerPrintedOnFailure = ($run.ExitCode -ne 0) -and ($markerLines.Count -gt 0)
          $record.verdict = if ($completed -and $exercised) { 'OBSERVED' } else { 'FAIL' }
        } else {
          $record.verdict = if ($completed -and $exercised -and $exitOk -and $markerOk -and $cleanOk) { 'PASS' } else { 'FAIL' }
        }
        $record.detail = "exit $($run.ExitCode) marker-lines $($markerLines.Count) errors [$($errorLocations -join ' ')] first-edit-line $firstLine exercised $exercised"
      }
      'deadline' {
        if ($packagedHost) {
          # Under an MSIX-packaged host the kill-on-close job does not hold
          # descendants (NATIVE-1-R1 and PRE-1-R1 host finding); the condition
          # cannot be created here, so the sleeper is not started.
          $record.sleeper = [ordered]@{ started = $false; host = $hostPath; packagedHost = $true }
          $record.verdict = 'INCONCLUSIVE'
          $record.detail = 'packaged PowerShell host: descendant cleanup cannot be established here; sleeper not started'
          break
        }
        $pidFile = Join-Path $caseDir 'child.pid'
        $sleeper = Join-Path $caseDir 'sleeper.ps1'
        $body = @'
$options = @{ FilePath = (Get-Process -Id $PID).Path; ArgumentList = @('-NoLogo', '-NoProfile', '-Command', 'Start-Sleep -Seconds 300'); PassThru = $true; WindowStyle = 'Hidden' }
$child = Start-Process @options
[IO.File]::WriteAllText('__PIDFILE__', ('{0} {1}' -f $PID, $child.Id))
Start-Sleep -Seconds 300
'@
        [IO.File]::WriteAllText($sleeper, $body.Replace('__PIDFILE__', $pidFile.Replace("'", "''")), $utf8)
        $run = $null
        $launchError = ''
        try {
          $run = Invoke-Owned $hostPath @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $sleeper) "$id-sleeper" ([int]$c.deadlineSeconds) $caseDir $caseTemp @{}
        } catch { $launchError = $_.Exception.Message }
        $pids = @()
        if (Test-Path -LiteralPath $pidFile) { $pids = @(((Get-Content -LiteralPath $pidFile -Raw) -split '\s+') | Where-Object { $_ -match '^[0-9]+$' } | ForEach-Object { [int]$_ }) }
        $alive = @(Get-RMQAliveProcessIds @($pids))
        foreach ($p in $alive) { Stop-Process -Id $p -Force -ErrorAction SilentlyContinue }
        $record.sleeper = [ordered]@{ started = $true; launchError = $launchError; host = $hostPath; packagedHost = $false; pids = @($pids); aliveAfter = @($alive) }
        if ($null -ne $run) {
          $record.sleeper.exit = $run.ExitCode; $record.sleeper.seconds = $run.DurationSeconds; $record.sleeper.deadline = $run.DeadlineSeconds
          $record.sleeper.timedOut = $run.TimedOut; $record.sleeper.ownership = $run.Ownership
        }
        if ($null -eq $run) {
          $record.detail = "owned launch failed: $launchError; alive [$($alive -join ',')] stopped"
        } elseif ($run.TimedOut -and $pids.Count -eq 2 -and $alive.Count -eq 0) {
          $record.verdict = 'PASS'
          $record.detail = "timed out after $($run.DurationSeconds) s; root $($pids[0]) and child $($pids[1]) both absent"
        } else {
          $record.detail = "timedOut $($run.TimedOut) pids [$($pids -join ',')] alive [$($alive -join ',')]"
        }
      }
      'registry' {
        $mutated = $registryText | ConvertFrom-Json
        switch ([string]$c.mutation) {
          'remove-last' { $mutated.cases = @($mutated.cases | Select-Object -First (@($mutated.cases).Count - 1)) }
          'swap-first-two' { $all = @($mutated.cases); $mutated.cases = @($all[1], $all[0]) + @($all | Select-Object -Skip 2) }
          'version' { $mutated.version = 'PRE1-R2-MARKER-CONTROLS-V0' }
          'content' { $mutated.cases[1].expectedMarker = $true }
          default { throw "unknown registry mutation $($c.mutation)" }
        }
        $mutatedPath = Join-Path $caseDir 'registry.json'
        [IO.File]::WriteAllText($mutatedPath, ($mutated | ConvertTo-Json -Depth 12), $utf8)
        $command = "& '$scriptPath' -SelectorProbeOnly -RepoRoot '$repo' -RegistryPath '$mutatedPath'; exit `$LASTEXITCODE"
        $run = Invoke-Owned $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) "$id-registry" $ChildDeadlineSeconds $caseDir $caseTemp @{}
        $marker = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith([string]$c.expectedMarker, [StringComparison]::Ordinal) })
        $probe = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith('MARKER-CONTROLS: SELECTOR-PROBE', [StringComparison]::Ordinal) })
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
        $command = "& '$scriptPath' $selectorArg$probeArg-RepoRoot '$repo' -WorkRoot '$childWork' -ReceiptPath '$childReceipt' -LakePath '$lake' -Revision '$revisionSha'; exit `$LASTEXITCODE"
        $run = Invoke-Owned $hostPath @('-NoProfile', '-ExecutionPolicy', 'Bypass', '-Command', $command) "$id-selector" $ChildDeadlineSeconds $caseDir $caseTemp @{}
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
          if ([bool]$c.probe) { $ok = $ok -and ([string]$marker[0]).Contains("selected=$($PinnedCaseIds.Count) ") }
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
    Remove-Item -LiteralPath $caseTemp -Recurse -Force -ErrorAction SilentlyContinue
    $record.copyRemoved = -not (Test-Path -LiteralPath $caseDir)
    $after = Get-State "$id-after" (Join-Path $work "$id-git-after")
    Remove-Item -LiteralPath (Join-Path $work "$id-git-before") -Recurse -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath (Join-Path $work "$id-git-after") -Recurse -Force -ErrorAction SilentlyContinue
    $record.repositoryStateUnchanged = ($before -ceq $after)
    $record.repositoryStateSha256 = Get-Sha256Hex ($utf8.GetBytes($before))
    if (-not $record.copyRemoved -or -not $record.repositoryStateUnchanged) {
      $record.verdict = 'FAIL'
      $record.detail += '; restoration failed'
    }
    $record.seconds = [Math]::Round($caseWatch.Elapsed.TotalSeconds, 3)
  }
  Write-Output ("MARKER-CONTROLS: {0} [{1}] {2} ({3} s)" -f $record.verdict, $id, $record.detail, $record.seconds)
  if ($record.verdict -eq 'FAIL') { $overall = 'FAIL' }
  elseif ($record.verdict -eq 'INCONCLUSIVE' -and $overall -eq 'PASS') { $overall = 'INCONCLUSIVE' }
  $results += $record
}

$executed = @($results | ForEach-Object { $_.id })
if (($executed -join ',') -cne ($selected -join ',')) { $overall = 'FAIL' }
Remove-Item -LiteralPath (Join-Path $work 'git') -Recurse -Force -ErrorAction SilentlyContinue
Remove-Item -LiteralPath $work -Recurse -Force -ErrorAction SilentlyContinue
$receipt = [ordered]@{
  version = 'PRE1-R2-MARKER-CONTROLS-RECEIPT-V1'; registryVersion = $RegistryVersion
  registrySha256 = (Get-Sha256Hex $registryBytes); registryContentSha256 = $registryContent
  runnerSha256 = (Get-Sha256Hex ([IO.File]::ReadAllBytes($scriptPath)))
  liveBytesNote = 'SHA-256 values are of the live checkout bytes that ran'
  repo = $repo; revision = $revisionSha; host = [Environment]::MachineName; os = [Environment]::OSVersion.VersionString
  powershell = $PSVersionTable.PSVersion.ToString(); hostPath = $hostPath; packagedHost = $packagedHost
  lake = $lake; observe = [bool]$Observe
  workRoot = $work; workRootRemoved = -not (Test-Path -LiteralPath $work)
  selectorBound = $selectorBound; selected = @($selected); expected = @($selected); executed = @($executed)
  registryCaseCount = $PinnedCaseIds.Count; result = $overall; cases = @($results)
}
[IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
Write-Output ("MARKER-CONTROLS: RESULT: {0} executed {1} of {2} selected cases (registry {3}, {4} cases)" -f `
    $overall, $executed.Count, $selected.Count, $RegistryVersion, $PinnedCaseIds.Count)
if ($overall -eq 'PASS') { exit 0 }
if ($overall -eq 'INCONCLUSIVE') { exit 3 }
exit 1

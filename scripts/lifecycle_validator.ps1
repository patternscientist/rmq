#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [ValidateSet('startup','single','full')][string]$Stage = 'full',
  [AllowEmptyString()][string]$Case,
  [ValidateRange(1,7200)][int]$DeadlineSeconds = 1800
)

# Native execution only: no implicit build, interpreter fallback, source edits,
# aggregate gate, or old validator. Every child belongs to a bounded process tree.
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$root = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$exe = Join-Path $root '.lake/build/bin/rmq_lifecycle_validate.exe'
$ids = @('L01-W-EMPTY','L02-C-EMPTY','L03-W-SINGLE','L04-C-SINGLE',
  'L05-W-REPEAT','L06-C-REPEAT','L07-W-TIE','L08-C-TIE','L09-W-INVALID',
  'L10-C-INVALID','L11-W-DIRTY','L12-C-DIRTY','L13-W-N24','L14-C-N24',
  'L15-W-N83','L16-C-N83')
if ($Stage -eq 'single') {
  if (-not $PSBoundParameters.ContainsKey('Case')) { throw 'Missing exact Case selector' }
  if ([string]::IsNullOrWhiteSpace($Case) -or $Case.Trim() -cne $Case) {
    throw 'Empty or whitespace Case selector'
  }
  if ($ids -cnotcontains $Case) { throw 'Unknown exact Case selector' }
} elseif ($PSBoundParameters.ContainsKey('Case')) { throw 'Case selector requires Stage single' }
$utf8 = [Text.UTF8Encoding]::new($false, $true)
$logRoot = Join-Path $root ('.lake/lifecycle-validator/' + [Guid]::NewGuid().ToString('N'))
[void](New-Item -ItemType Directory -Path $logRoot -Force)
$identityPaths = @('lakefile.toml','RMQ/Validation/PackedLifecycle.lean',
  'scripts/lifecycle_validator.ps1','scripts/lifecycle_validator_environment.ps1',
  'scripts/owned_process_tree.ps1','RMQ/Core/WordRAM/Lifecycle/Executable.lean',
  'RMQ/Core/WordRAM/Lifecycle/Controls.lean','RMQ/Core/WordRAM/Lifecycle/ArrayRun.lean',
  'RMQ/Core/WordRAM/Lifecycle/Machine.lean','RMQ/Core/WordRAM/Lifecycle/Program.lean',
  'RMQ/Core/WordRAM/Lifecycle/Service.lean','.lake/build/bin/rmq_lifecycle_validate.exe')
# LIFE-1-R3: from the log root on, every exit path writes RESULT.json. Each
# identity path is hashed in its own guard; the stage error, every identity
# difference and every cleanup error are recorded separately. LIFE-1-R4: the
# pinned executable's existence is checked inside that region (after the
# identity capture, before any helper is loaded), and PASS.json is written only
# after RESULT.json was.
function Get-IdentityEntry([string]$Relative) {
  try {
    return [pscustomobject]@{hash=(Get-FileHash -Algorithm SHA256 -LiteralPath (Join-Path $root $Relative)).Hash.ToLowerInvariant();error=$null}
  } catch {return [pscustomobject]@{hash=$null;error=$_.Exception.Message}}
}
$before = [ordered]@{}
$script:records = @()
$stageError = $null
$stageRecord = $null
$integrityErrors = [Collections.Generic.List[string]]::new()
$cleanupErrors = [Collections.Generic.List[string]]::new()
$pinChecks = [Collections.Generic.List[object]]::new()
$mutex = $null
$acquired = $false
$completed = $false
$durableError = $null

function Invoke-CaseProcess([string]$Name, [string[]]$Arguments, [AllowNull()][object]$Selector,
    [int]$ExpectedExit, [string[]]$ExpectedLines, [string[]]$ExpectedCases) {
  $limit = if ($Name -eq 'registry' -or $Name -eq 'startup' -or $Name.StartsWith('reject-')) { 30 } else { $DeadlineSeconds }
  $result = Invoke-LifecycleValidatorProcess -FilePath $exe -Arguments $Arguments -WorkingDirectory $root `
    -Stage $Name -DeadlineSeconds $limit -TempRoot $logRoot -Selector $Selector
  # Preserve complete returned lines before verdict parsing; these are not raw bytes.
  [IO.File]::WriteAllText((Join-Path $logRoot ($Name+'.stdout.txt')), ($result.StandardOutput -join "`n"), $utf8)
  [IO.File]::WriteAllText((Join-Path $logRoot ($Name+'.stderr.txt')), ($result.StandardError -join "`n"), $utf8)
  $record = [ordered]@{ name=$Name; exitCode=$result.ExitCode; expectedExit=$ExpectedExit;
    durationSeconds=$result.DurationSeconds; timedOut=$result.TimedOut;
    outputLimitExceeded=$result.OutputLimitExceeded; ownership=$result.Ownership;
    terminatedIds=$result.TerminatedIds; expectedCases=@($ExpectedCases);
    selectorPresent=($null -ne $Selector); selector=$Selector; result=$result }
  $script:records += $record
  [IO.File]::WriteAllText((Join-Path $logRoot 'processes.json'), (ConvertTo-Json -InputObject @($script:records) -Depth 6), $utf8)
  if ($result.TimedOut -or $result.OutputLimitExceeded) { throw "$Name uncovered: bounded execution did not complete" }
  if ($result.ExitCode -ne $ExpectedExit) { throw "$Name exit $($result.ExitCode), expected $ExpectedExit" }
  if ($result.Ownership -ne 'kill-on-close-job' -or @($result.TerminatedIds).Count -ne 0) {
    throw "$Name failed process ownership/cleanup assertion"
  }
  $stdout = @($result.StandardOutput | Where-Object { $_ -ne '' })
  $stderr = @($result.StandardError | Where-Object { $_ -ne '' })
  if ($ExpectedExit -ne 0) {
    if ($stdout.Count -ne 0 -or $stderr.Count -ne 1 -or $stderr[0] -cne $ExpectedLines[0]) {
      throw "$Name wrong rejection surface or mixed diagnostics"
    }
    return
  }
  if ($stderr.Count -ne 0) { throw "$Name unexpected stderr" }
  if (@($ExpectedCases).Count -eq 0) {
    if (($stdout -join "`n") -cne ($ExpectedLines -join "`n")) { throw "$Name registry/startup identity mismatch" }
  } else {
    if ($stdout.Count -ne $ExpectedCases.Count+1) { throw "$Name unexpected output count" }
    for ($i=0; $i -lt $ExpectedCases.Count; $i++) {
      $pattern = '^LIFE1-CASE\|' + [regex]::Escape($ExpectedCases[$i]) + '\|PASS\|steps=\d+\|queries=\d+\|querySteps=\d+\|extent=\d+\|peak=\d+\|release=\d+\|dirty=\d+$'
      if ($stdout[$i] -cnotmatch $pattern) { throw "$Name wrong case order, verdict, or diagnostic surface" }
    }
    if ($stdout[-1] -cne $ExpectedLines[0]) { throw "$Name missing exact terminal pass" }
  }
}

try {
  # LIFE-1-R4: capture every identity pin first (no helper needed), then check the
  # pinned executable exactly as the pre-root check did, then load the helpers.
  $entryFailures = @()
  foreach ($relative in $identityPaths) {
    $entry = Get-IdentityEntry $relative
    if ($null -eq $entry.error) { $before[$relative] = $entry.hash }
    else { $entryFailures += ($relative + ': ' + $entry.error) }
  }
  [IO.File]::WriteAllText((Join-Path $logRoot 'identity-before.json'), ($before | ConvertTo-Json), $utf8)
  if (-not (Test-Path -LiteralPath $exe -PathType Leaf)) {
    throw 'Missing rmq_lifecycle_validate.exe; build the named Lake target explicitly first'
  }
  if ($entryFailures.Count -ne 0) { throw ('Source/binary identity unavailable at entry: ' + ($entryFailures -join '; ')) }
  . (Join-Path $root 'scripts/owned_process_tree.ps1')
  . (Join-Path $root 'scripts/lifecycle_validator_environment.ps1')
  # Acquire exactly once; no helper invoked here takes this mutex recursively.
  $mutex = [Threading.Mutex]::new($false,'Local\RMQLifecycleImplementationHeavy20260920')
  try { $acquired = $mutex.WaitOne(7200000) } catch [Threading.AbandonedMutexException] { $acquired = $true }
  if (-not $acquired) { throw 'Heavy execution slot wait expired; no child launched' }
  $registryLines = for ($i=0; $i -lt $ids.Count; $i++) {
    $model = if ($i % 2 -eq 0) { 'word' } else { 'comparison' }
    $kind = if ($i -ge 10 -and $i -lt 12) { 'dirty-entry' } else { 'lifecycle' }
    'LIFE1-REGISTRY|'+$ids[$i]+'|'+$model+'|'+$kind+'|PASS'
  }
  Invoke-CaseProcess 'registry' @('--registry') $null 0 @($registryLines) @()
  Invoke-CaseProcess 'startup' @('--startup') $null 0 @('LIFE1-STARTUP|PASS|cases=16') @()
  if ($Stage -eq 'single') {
    Invoke-CaseProcess 'single' @($Case) $null 0 @('LIFE1-PASS|mode=single|cases=1') @($Case)
  } elseif ($Stage -eq 'full') {
    # Focused startup evidence precedes the full registry on every replay.
    Invoke-CaseProcess 'focused' @($ids[0]) $null 0 @('LIFE1-PASS|mode=single|cases=1') @($ids[0])
    Invoke-CaseProcess 'reject-empty' @() 'id:' 1 @('LIFE1-FAIL|empty-selector') @()
    Invoke-CaseProcess 'reject-whitespace' @() 'id: ' 1 @('LIFE1-FAIL|whitespace-selector') @()
    Invoke-CaseProcess 'reject-unknown' @('UNKNOWN') $null 1 @('LIFE1-FAIL|unknown-selector') @()
    Invoke-CaseProcess 'reject-duplicate' @($ids[0],$ids[0]) $null 1 @('LIFE1-FAIL|duplicate-selector') @()
    Invoke-CaseProcess 'reject-channels' @($ids[0]) ('id:'+$ids[0]) 1 @('LIFE1-FAIL|duplicate-selector-channel') @()
    Invoke-CaseProcess 'full' @() $null 0 @('LIFE1-PASS|mode=full|cases=16') $ids
  }
  $completed = $true
} catch {
  $stageError = $_.Exception.Message
  $stageRecord = $_
} finally {
  # Independent integrity first, while the slot is still held; every captured
  # identity path is compared in its own guard and all differences are kept.
  $after = [ordered]@{}
  foreach ($path in $identityPaths) {
    $entryHash = if ($before.Contains($path)) { $before[$path] } else { $null }
    $status = 'not-captured'
    $finalHash = $null
    if ($null -ne $entryHash) {
      $now = Get-IdentityEntry $path
      $finalHash = $now.hash
      $after[$path] = $finalHash
      if ($null -ne $now.error) {
        $status = 'unreadable-final'
        $integrityErrors.Add("Source/binary identity unreadable: ${path}: $($now.error)")
      } elseif ($finalHash -cne $entryHash) {
        $status = 'changed'
        $integrityErrors.Add("Source/binary identity changed: $path")
      } else { $status = 'verified' }
    }
    $pinChecks.Add([ordered]@{ path=$path; entrySha256=$entryHash; finalSha256=$finalHash; status=$status })
  }
  try { [IO.File]::WriteAllText((Join-Path $logRoot 'identity-after.json'), ($after | ConvertTo-Json), $utf8) }
  catch { $cleanupErrors.Add('identity-after record: ' + $_.Exception.Message) }
  if ($acquired) { try { $mutex.ReleaseMutex() } catch { $cleanupErrors.Add('heavy slot release: ' + $_.Exception.Message) } }
  if ($null -ne $mutex) { try { $mutex.Dispose() } catch { $cleanupErrors.Add('heavy slot dispose: ' + $_.Exception.Message) } }
  $passed = $completed -and $null -eq $stageError -and $integrityErrors.Count -eq 0 -and $cleanupErrors.Count -eq 0
  $finalization = [ordered]@{ schema='life1-r3-finalization-v1'; verdict=$(if ($passed) { 'pass' } else { 'fail' }); stageError=$stageError
    integrityErrors=@($integrityErrors.ToArray()); cleanupErrors=@($cleanupErrors.ToArray()); pinChecks=@($pinChecks.ToArray())
    entryPinCount=$before.Count; verifiedPinCount=@($pinChecks | Where-Object { $_.status -ceq 'verified' }).Count }
  try {
    [IO.File]::WriteAllText((Join-Path $logRoot 'RESULT.json'),
      (([ordered]@{stage=$Stage; case=$Case; completed=$completed; passed=$passed; processCount=@($script:records).Count;
        logRoot=$logRoot; finalization=$finalization}) | ConvertTo-Json -Depth 6), $utf8)
  } catch {
    $passed = $false
    $durableError = 'LIFE1-VALIDATOR: durable result write failed: ' + $_.Exception.Message
    [Console]::Error.WriteLine($durableError)
  }
}
if (-not $passed) {
  foreach ($message in @($integrityErrors) + @($cleanupErrors)) { [Console]::Error.WriteLine($message) }
  if ($null -ne $stageRecord) { throw $stageRecord }
  if ($integrityErrors.Count -ne 0) { throw $integrityErrors[0] }
  if ($cleanupErrors.Count -ne 0) { throw $cleanupErrors[0] }
  if ($null -ne $durableError) { throw $durableError }
  throw 'Replay did not complete'
}
[IO.File]::WriteAllText((Join-Path $logRoot 'PASS.json'),
  (([ordered]@{stage=$Stage;case=$Case;cases=$ids;expectedVerdict='PASS';identityPreserved=$true;
    processCount=$script:records.Count;logRoot=$logRoot}) | ConvertTo-Json -Depth 4), $utf8)
Write-Output "LIFE1-VALIDATOR PASS stage=$Stage processes=$($script:records.Count) logs=$logRoot"

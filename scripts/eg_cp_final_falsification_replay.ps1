<#
.SYNOPSIS
  Replay harness for the EG-CP final falsification gate (`FG-12`).

.DESCRIPTION
  Encodes the frozen replay registry of
  `docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md` section 3 literally, in the
  commissioned order, and replays each case against the working tree.

  A case is replayed by applying one textual mutation to one tracked file,
  rebuilding the named failing surface, and requiring the commissioned verdict:

    ACCEPT  the surface must still elaborate
    REJECT  the surface must fail to elaborate

  Every mutation is restored in a `finally` block, its restoration is verified by
  SHA256 against the pre-mutation content, and the run ends with a clean-tree
  check.

  Cases whose commissioned failing surface does not exist yet are reported as
  TARGET-ABSENT. They are never silently skipped and they never count as passes:
  a full-mode run with any TARGET-ABSENT case exits non-zero. That is deliberate.
  `FG-12` asks for a harness that passes in full mode on the committed clean
  candidate, and a harness that reported PASS while seven of sixteen cases had no
  target would be forging exactly the evidence the row exists to demand.

.PARAMETER Case
  Replay exactly one registry ID. Unknown, empty and whitespace selectors are
  errors. Omitting the parameter, and only omitting it, means full mode.

.PARAMETER SkipSelfTest
  Skip the descendant-termination self-test. Intended for development only; a
  full-mode run refuses it.
#>

[CmdletBinding()]
param(
  [AllowEmptyString()]
  [string] $Case,
  [switch] $SkipSelfTest
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$script:RepoRoot = Split-Path -Parent $PSScriptRoot
$script:LakePath = $null
$script:Failures = New-Object System.Collections.Generic.List[string]
$script:Results = New-Object System.Collections.Generic.List[object]

function Write-Stage {
  param([string] $Text)
  Write-Host "REPLAY: $Text"
}

function Add-Failure {
  param([string] $Text)
  $script:Failures.Add($Text) | Out-Null
  Write-Host "REPLAY-FAIL: $Text"
}

# ---------------------------------------------------------------- the registry

# Ordered exactly as commissioned. `Target` is $null when the commissioned
# failing surface does not exist on this candidate yet.
$script:Registry = @(
  @{ Order = 1;  Id = 'A01-PRODUCTION-EXPECTED-ACCEPT';
     Mutation = 'unchanged final implementation, consumer, matrix, and result';
     Verdict = 'ACCEPT'; Surface = 'none'; Target = @{ Kind = 'None' } },
  @{ Order = 2;  Id = 'A02-UNREAD-CELL-EXPECTED-ACCEPT';
     Mutation = 'mutate exactly one proved-unread allocated cell and preserve the pinned run/result';
     Verdict = 'ACCEPT'; Surface = 'none'; Target = $null },
  @{ Order = 3;  Id = 'M01-WRONG-LONG-COUNT';
     Mutation = 'alter the header count';
     Verdict = 'REJECT'; Surface = 'liveness/consumer';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/SourceGeometry.lean';
       Find  = '  | .selectLongRelative => packedLongRelativeSlots n longCount';
       Repl  = '  | .selectLongRelative => packedLongRelativeSlots n (longCount + 1)' } },
  @{ Order = 4;  Id = 'M02-HOST-LONG-COUNT-MIRROR';
     Mutation = 'bypass the header reply with preprocessing/host metadata';
     Verdict = 'REJECT'; Surface = 'structural consumer'; Target = $null },
  @{ Order = 5;  Id = 'M03-SHAPE-PARAMETER';
     Mutation = 'add or restore a semantic shape input';
     Verdict = 'REJECT'; Surface = 'exact signature';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/PhysicalRead.lean';
       Find  = 'def packedSourceRead (n longCount : Nat) (memory : List (List Bool))';
       Repl  = 'def packedSourceRead (shape : CartesianShape) (n longCount : Nat) (memory : List (List Bool))' } },
  @{ Order = 6;  Id = 'M04-CANONICAL-SHAPE-BY-N';
     Mutation = 'synthesize a canonical shape from n inside a wrapper';
     Verdict = 'REJECT'; Surface = 'structural / same-object'; Target = $null },
  @{ Order = 7;  Id = 'M05-SIBLING-STORE';
     Mutation = 'read a logical/source store beside memory xs';
     Verdict = 'REJECT'; Surface = 'store identity';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/PhysicalRead.lean';
       Find  = '    | some source => packedSourceRead n longCount memory source index';
       Repl  = '    | some source => packedSourceRead n longCount (memory.drop 1) source index' } },
  @{ Order = 8;  Id = 'M06-ANSWER-ORACLE';
     Mutation = 'call the reference/semantic answer from controller execution';
     Verdict = 'REJECT'; Surface = 'oracle independence'; Target = $null },
  @{ Order = 9;  Id = 'M07-DISCONNECTED-TRACE';
     Mutation = 'retain a correct result while forging or replaying an unrelated physical trace';
     Verdict = 'REJECT'; Surface = 'trace execution'; Target = $null },
  @{ Order = 10; Id = 'M08-FORGED-PROBE-CAP';
     Mutation = 'replace derived trace length/cap evidence with a stored number or theorem-only field';
     Verdict = 'REJECT'; Surface = 'consumer';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Probe.lean';
       Find  = 'def packedProbeCount (n bit width : Nat) : Nat :=
  (packedProbePlan n bit width).length';
       Repl  = 'def packedProbeCount (_n _bit _width : Nat) : Nat :=
  2' } },
  @{ Order = 11; Id = 'M09-WRONG-CELL-CROSSING';
     Mutation = 'mutate one crossing codec order/bit span';
     Verdict = 'REJECT'; Surface = 'exact decoded word';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Probe.lean';
       Find  = '    [bit / packedCellWidth n, bit / packedCellWidth n + 1]';
       Repl  = '    [bit / packedCellWidth n + 1, bit / packedCellWidth n]' } },
  @{ Order = 12; Id = 'M10-SPARSE-COUNT-DEPENDENCY';
     Mutation = 'introduce sparse-count metadata into a live offset';
     Verdict = 'REJECT'; Surface = 'K1 source factorization';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/SourceGeometry.lean';
       Find  = 'def packedSourceStride (n : Nat) :';
       Repl  = 'def packedSourceStride (n _sparseCount : Nat) :' } },
  @{ Order = 13; Id = 'M11-SIBLING-PAYLOAD';
     Mutation = 'prove space for one payload while executing another';
     Verdict = 'REJECT'; Surface = 'public / same-object composition';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Payload.lean';
       Find  = 'def packedPayloadBits (shape : CartesianShape) : List Bool :=
  (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload';
       Repl  = 'def packedPayloadBits (shape : CartesianShape) : List Bool :=
  (concreteBPNativeSuccinctRMQFlatPayloadLayout shape).payload ++ []' } },
  @{ Order = 14; Id = 'M12-PUBLIC-TYPE-WEAKENING';
     Mutation = 'remove one load-bearing capstone conjunct';
     Verdict = 'REJECT'; Surface = 'independently frozen expected-type consumer'; Target = $null },
  @{ Order = 15; Id = 'M13-HIDDEN-UNCOUNTED-TABLE';
     Mutation = 'add a content-dependent lookup/program constant outside memory xs';
     Verdict = 'REJECT'; Surface = 'closed controller / program accounting'; Target = $null },
  @{ Order = 16; Id = 'M14-LONG-COUNT-IGNORED';
     Mutation = 'retain the header read but make downstream offsets independent of its value';
     Verdict = 'REJECT'; Surface = 'liveness';
     Target = @{ Kind = 'Patch';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/SourceGeometry.lean';
       Find  = '  | .selectLongRelative => packedLongRelativeSlots n longCount';
       Repl  = '  | .selectLongRelative => packedLongRelativeSlots n 0' } }
)

# ------------------------------------------------------- registry self-checks

function Test-RegistryIntegrity {
  Write-Stage 'validating the frozen registry'
  $ok = $true

  if ($script:Registry.Count -ne 16) {
    Add-Failure "registry has $($script:Registry.Count) entries, expected 16"
    $ok = $false
  }

  $ids = @($script:Registry | ForEach-Object { $_.Id })
  $unique = @($ids | Sort-Object -Unique)
  if ($unique.Count -ne $ids.Count) {
    Add-Failure 'registry contains duplicate IDs'
    $ok = $false
  }

  $expectedOrder = 1
  foreach ($entry in $script:Registry) {
    if ($entry.Order -ne $expectedOrder) {
      Add-Failure "registry order broken at ID $($entry.Id): saw $($entry.Order), expected $expectedOrder"
      $ok = $false
    }
    $expectedOrder = $expectedOrder + 1
    if ($entry.Verdict -ne 'ACCEPT' -and $entry.Verdict -ne 'REJECT') {
      Add-Failure "registry entry $($entry.Id) has unmapped verdict '$($entry.Verdict)'"
      $ok = $false
    }
  }

  $accepts = @($script:Registry | Where-Object { $_.Verdict -eq 'ACCEPT' }).Count
  $rejects = @($script:Registry | Where-Object { $_.Verdict -eq 'REJECT' }).Count
  if ($accepts -ne 2) {
    Add-Failure "expected exactly 2 ACCEPT cases, found $accepts"
    $ok = $false
  }
  if ($rejects -ne 14) {
    Add-Failure "expected exactly 14 REJECT cases, found $rejects"
    $ok = $false
  }

  if ($ok) {
    Write-Stage "registry OK: 16 ordered entries, $accepts ACCEPT, $rejects REJECT"
  }
  return $ok
}

# -------------------------------------------------- descendant termination

function Invoke-DescendantSelfTest {
  param([int] $DeadlineSeconds)

  Write-Stage 'descendant-termination self-test'

  $marker = Join-Path ([System.IO.Path]::GetTempPath()) ("egcp-replay-" + [System.Guid]::NewGuid().ToString('N') + ".txt")
  # A root that spawns a detached grandchild sleeper, so killing the root alone
  # would leave the grandchild running.
  $childScript = "Start-Process -FilePath '$($PSHOME)\powershell.exe' -ArgumentList '-NoProfile','-Command','Start-Sleep -Seconds 120; Set-Content -Path ''$marker'' -Value done' -WindowStyle Hidden; Start-Sleep -Seconds 120"

  $proc = Start-Process -FilePath (Join-Path $PSHOME 'powershell.exe') `
    -ArgumentList '-NoProfile', '-Command', $childScript `
    -PassThru -WindowStyle Hidden
  Start-Sleep -Seconds 2

  $killed = Stop-ProcessTree -RootId $proc.Id
  if (-not $killed) {
    Add-Failure 'descendant self-test: could not terminate the owned process tree'
    return $false
  }

  Start-Sleep -Seconds 2
  $survivors = Get-Process -Name 'powershell' -ErrorAction SilentlyContinue |
    Where-Object { $_.Id -eq $proc.Id }
  if ($null -ne $survivors) {
    Add-Failure 'descendant self-test: the owned root survived termination'
    return $false
  }

  if (Test-Path -LiteralPath $marker) {
    Remove-Item -LiteralPath $marker -Force
    Add-Failure 'descendant self-test: a descendant outlived its root and wrote the marker'
    return $false
  }

  Write-Stage 'descendant-termination self-test: PASS'
  return $true
}

function Stop-ProcessTree {
  param([int] $RootId)

  if ($IsLinux -or $IsMacOS) {
    # Owned root plus descendants: negate the pid to address the process group.
    try { & kill -- "-$RootId" 2>$null } catch { }
    try { & kill -9 -- "-$RootId" 2>$null } catch { }
    return $true
  }

  try {
    & taskkill /PID $RootId /T /F | Out-Null
    return $true
  } catch {
    return $false
  }
}

# ---------------------------------------------------------- bounded stages

function Invoke-BoundedLake {
  param(
    [string] $Module,
    [int] $DeadlineSeconds
  )

  if ($null -eq $script:LakePath) {
    $cmd = Get-Command lake -ErrorAction SilentlyContinue
    if ($null -eq $cmd) {
      throw 'lake is not on PATH; the harness cannot build any surface'
    }
    $script:LakePath = $cmd.Source
  }

  $psi = New-Object System.Diagnostics.ProcessStartInfo
  $psi.FileName = $script:LakePath
  $psi.Arguments = "build $Module"
  $psi.WorkingDirectory = $script:RepoRoot
  $psi.UseShellExecute = $false
  $psi.RedirectStandardOutput = $true
  $psi.RedirectStandardError = $true
  $psi.CreateNoWindow = $true

  $proc = New-Object System.Diagnostics.Process
  $proc.StartInfo = $psi
  $proc.Start() | Out-Null

  # Drain both pipes asynchronously; a full pipe would otherwise deadlock the
  # child and turn a semantic failure into a spurious timeout.
  $outTask = $proc.StandardOutput.ReadToEndAsync()
  $errTask = $proc.StandardError.ReadToEndAsync()

  $exited = $proc.WaitForExit($DeadlineSeconds * 1000)
  if (-not $exited) {
    Stop-ProcessTree -RootId $proc.Id | Out-Null
    try { $proc.WaitForExit(10000) | Out-Null } catch { }
    return @{ TimedOut = $true; ExitCode = $null; Diagnostic = 'timeout' }
  }
  # The parameterless overload flushes the redirected streams.
  $proc.WaitForExit()

  $code = $proc.ExitCode
  $diag = ''
  if ($code -ne 0) {
    $nl = [string][char]10
    $diag = ($outTask.Result + $nl + $errTask.Result)
    $lines = @($diag -split $nl | Where-Object { $_ -match 'error' })
    if ($lines.Count -gt 0) { $diag = ($lines | Select-Object -First 6) -join $nl }
    if ($diag.Length -gt 800) { $diag = $diag.Substring(0, 800) }
  }
  return @{ TimedOut = $false; ExitCode = $code; Diagnostic = $diag }
}

# --------------------------------------------------------------- replay core

function Get-FileHashHex {
  param([string] $Path)
  return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash
}

function Invoke-RegistryCase {
  param(
    [hashtable] $Entry,
    [int] $DeadlineSeconds,
    [string] $Surface
  )

  if ($null -eq $Entry.Target) {
    Write-Stage "$($Entry.Id): TARGET-ABSENT (commissioned surface '$($Entry.Surface)' does not exist on this candidate)"
    $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'TARGET-ABSENT' }) | Out-Null
    return
  }

  if ($Entry.Target.Kind -eq 'None') {
    Write-Stage "$($Entry.Id): production accept, building $Surface"
    $run = Invoke-BoundedLake -Module $Surface -DeadlineSeconds $DeadlineSeconds
    if ($run.TimedOut) {
      Add-Failure "$($Entry.Id): timed out after $DeadlineSeconds s"
      $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'TIMEOUT' }) | Out-Null
      return
    }
    if ($run.ExitCode -ne 0) {
      Add-Failure "$($Entry.Id): expected ACCEPT, the unchanged candidate failed to build"
      $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'UNEXPECTED-REJECT' }) | Out-Null
      return
    }
    Write-Stage "$($Entry.Id): ACCEPT as commissioned"
    $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'ACCEPT' }) | Out-Null
    return
  }

  $relative = $Entry.Target.File
  $path = Join-Path $script:RepoRoot $relative
  if (-not (Test-Path -LiteralPath $path)) {
    Add-Failure "$($Entry.Id): mutation target $relative does not exist"
    $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'TARGET-MISSING' }) | Out-Null
    return
  }

  # Byte-exact capture: the working tree is CRLF and BOM-free, and a text-mode
  # round trip through PowerShell 5.1 would silently rewrite both. Restoration
  # must return the file the harness found, not an equivalent one.
  $originalBytes = [System.IO.File]::ReadAllBytes($path)
  $original = [System.Text.Encoding]::UTF8.GetString($originalBytes)
  $originalHash = Get-FileHashHex -Path $path

  $needle = $Entry.Target.Find -replace "`r`n", "`n"
  $haystack = $original -replace "`r`n", "`n"
  $occurrences = ([regex]::Matches($haystack, [regex]::Escape($needle))).Count
  if ($occurrences -ne 1) {
    Add-Failure "$($Entry.Id): mutation anchor occurs $occurrences times in $relative, expected exactly 1"
    $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'ANCHOR-DRIFT' }) | Out-Null
    return
  }

  try {
    $mutated = $haystack -replace [regex]::Escape($needle), ($Entry.Target.Repl -replace "`r`n", "`n")
    $utf8NoBom = New-Object System.Text.UTF8Encoding $false
    [System.IO.File]::WriteAllText($path, $mutated, $utf8NoBom)
    Write-Stage "$($Entry.Id): mutated $relative, rebuilding $Surface"

    $run = Invoke-BoundedLake -Module $Surface -DeadlineSeconds $DeadlineSeconds
    if ($run.TimedOut) {
      Add-Failure "$($Entry.Id): timed out after $DeadlineSeconds s"
      $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'TIMEOUT' }) | Out-Null
      return
    }

    if ($Entry.Verdict -eq 'REJECT') {
      if ($run.ExitCode -eq 0) {
        Add-Failure "$($Entry.Id): expected REJECT at surface '$($Entry.Surface)', but the mutated candidate built"
        $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'UNEXPECTED-ACCEPT' }) | Out-Null
      } else {
        Write-Stage "$($Entry.Id): REJECT as commissioned, surface '$($Entry.Surface)'"
        $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'REJECT' }) | Out-Null
      }
    } else {
      if ($run.ExitCode -ne 0) {
        Add-Failure "$($Entry.Id): expected ACCEPT, the mutated candidate failed"
        $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'UNEXPECTED-REJECT' }) | Out-Null
      } else {
        Write-Stage "$($Entry.Id): ACCEPT as commissioned"
        $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'ACCEPT' }) | Out-Null
      }
    }
  } finally {
    [System.IO.File]::WriteAllBytes($path, $originalBytes)
    $restoredHash = Get-FileHashHex -Path $path
    if ($restoredHash -ne $originalHash) {
      Add-Failure "$($Entry.Id): restoration hash mismatch for $relative ($restoredHash vs $originalHash)"
    } else {
      Write-Stage "$($Entry.Id): restored $relative, SHA256 verified"
    }
  }
}

# ------------------------------------------------------------------- driver

$fullMode = -not $PSBoundParameters.ContainsKey('Case')

if (-not $fullMode) {
  if ($null -eq $Case -or $Case.Trim().Length -eq 0) {
    Write-Host 'REPLAY-FAIL: an explicitly supplied selector must not be empty or whitespace'
    exit 2
  }
  $known = @($script:Registry | Where-Object { $_.Id -eq $Case })
  if ($known.Count -eq 0) {
    Write-Host "REPLAY-FAIL: unknown selector '$Case'"
    exit 2
  }
}

if (-not (Test-RegistryIntegrity)) {
  Write-Host 'REPLAY-FAIL: registry integrity check failed'
  exit 3
}

$surfaceModule = 'RMQ.Validation.EGCPFinalFalsification'

# Evidence-based deadline: measure the clean surface build once, then allow four
# times that plus a floor. A mutated build can be slower than a clean one, and a
# deadline shorter than the measurement it is derived from would be a race.
Write-Stage "measuring the clean build of $surfaceModule for the deadline"
$sw = [System.Diagnostics.Stopwatch]::StartNew()
$baseline = Invoke-BoundedLake -Module $surfaceModule -DeadlineSeconds 3600
$sw.Stop()
if ($baseline.TimedOut -or $baseline.ExitCode -ne 0) {
  Write-Host 'REPLAY-FAIL: the clean candidate does not build; nothing can be replayed against it'
  if (-not $baseline.TimedOut) { Write-Host $baseline.Diagnostic }
  exit 4
}
$baselineSeconds = [int][Math]::Ceiling($sw.Elapsed.TotalSeconds)
$deadline = [Math]::Max($baselineSeconds * 4, 300)
Write-Stage "clean build took $baselineSeconds s; per-case deadline $deadline s"

if ($fullMode -and $SkipSelfTest) {
  Write-Host 'REPLAY-FAIL: full mode refuses -SkipSelfTest'
  exit 5
}

if (-not $SkipSelfTest) {
  if (-not (Invoke-DescendantSelfTest -DeadlineSeconds $deadline)) {
    Write-Host 'REPLAY-FAIL: descendant-termination self-test failed'
    exit 6
  }
}

$cases = $script:Registry
if (-not $fullMode) {
  $cases = @($script:Registry | Where-Object { $_.Id -eq $Case })
}

foreach ($entry in $cases) {
  Invoke-RegistryCase -Entry $entry -DeadlineSeconds $deadline -Surface $surfaceModule
}

# ------------------------------------------------------------ terminal checks

Write-Stage 'terminal clean-state check'
$dirty = @(& git -C $script:RepoRoot status --porcelain)
if ($dirty.Count -gt 0) {
  Add-Failure "tree is not clean after replay: $($dirty -join '; ')"
}

$ran = $script:Results.Count
$absent = @($script:Results | Where-Object { $_.Outcome -eq 'TARGET-ABSENT' }).Count
$asCommissioned = @($script:Results | Where-Object { $_.Outcome -eq 'ACCEPT' -or $_.Outcome -eq 'REJECT' }).Count

Write-Host ''
Write-Host "REPLAY-SUMMARY: cases considered $ran, as commissioned $asCommissioned, target absent $absent"
foreach ($r in $script:Results) {
  Write-Host ("REPLAY-CASE: {0,-34} {1}" -f $r.Id, $r.Outcome)
}

if (-not $fullMode) {
  if ($script:Failures.Count -gt 0) {
    Write-Host "REPLAY: SELECTED CASE FAILED ($($script:Failures.Count) failures)"
    exit 1
  }
  Write-Host 'REPLAY: SELECTED CASE OK'
  exit 0
}

if ($script:Failures.Count -gt 0) {
  Write-Host "REPLAY: FULL MODE FAILED ($($script:Failures.Count) failures)"
  exit 1
}

if ($absent -gt 0) {
  Write-Host "REPLAY: FULL MODE INCOMPLETE - $absent commissioned cases have no failing surface on this candidate"
  Write-Host 'REPLAY: this is not a pass, and FG-12 stays Open'
  exit 7
}

Write-Host 'REPLAY: FULL MODE PASS'
exit 0

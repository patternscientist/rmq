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

.PARAMETER Stage
  Replay one literal owned campaign. `R2-ALLSIZE` selects exactly the seven
  final-controller anti-bypass cases. Stage and Case are mutually exclusive;
  an explicitly empty, whitespace, or unknown stage is an error.

.PARAMETER SkipSelfTest
  Skip the descendant-termination self-test. Intended for development only; a
  full-mode run refuses it.

.PARAMETER SelfTestOnly
  Validate the selectors, check registry integrity, run the
  descendant-termination self-test, and exit without building anything. This
  is the build-free leg that exercises owned root-plus-descendant termination
  on a gate OS without a Lean toolchain (the Ubuntu contract of
  `REPLAY-SUBPROCESS-DEADLINE`). It refuses -Case, -Stage, and -SkipSelfTest,
  and changes no registry, selector, deadline, restoration, or full-mode
  semantics.
#>

[CmdletBinding()]
param(
  [AllowEmptyString()]
  [string] $Case,
  [AllowEmptyString()]
  [string] $Stage,
  [switch] $SkipSelfTest,
  [switch] $SelfTestOnly
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
     Verdict = 'ACCEPT'; Surface = 'none';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'none';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean';
       Find  = 'def egcpStageFUnreadReplacementCell : List Bool :=
  List.replicate (packedReviewerCellWidth 3) true';
       Repl  = 'def egcpStageFUnreadReplacementCell : List Bool :=
  false :: List.replicate (packedReviewerCellWidth 3 - 1) true' };
     Activation = @(
       'false :: List.replicate (packedReviewerCellWidth 3 - 1) true') },
  @{ Order = 3;  Id = 'M01-WRONG-LONG-COUNT';
     Mutation = 'alter the header count';
     Verdict = 'REJECT'; Surface = 'liveness/consumer';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '      let longCount := SuccinctSpace.bitsToNatLE cell';
       Repl  = '      let longCount := SuccinctSpace.bitsToNatLE cell + 1' };
     Activation = @(
       'let longCount := SuccinctSpace.bitsToNatLE cell + 1') },
  @{ Order = 4;  Id = 'M02-HOST-LONG-COUNT-MIRROR';
     Mutation = 'bypass the header reply with preprocessing/host metadata';
     Verdict = 'REJECT'; Surface = 'structural consumer';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerController.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = 'def packedReviewerRunAgainstMemory
    (memory : List (List Bool)) (n left right : Nat) : PackedReviewerRun :=
  let controller := packedReviewerController n left right
  packedReviewerDriveAgainstMemoryAux memory
    (packedReviewerControllerMeasure controller) controller';
       Repl  = 'def packedReviewerRunAgainstMemory
    (memory : List (List Bool)) (n left right : Nat) : PackedReviewerRun :=
  let hostLongCountMirror := SuccinctSpace.bitsToNatLE ((memory[0]?).getD [])
  let controller :=
    match packedReviewerController n left right with
    | .header nStart leftStart rightStart =>
        packedReviewerNormalizePrelude
          (packedReviewerSparsePreludeRemaining
            (packedReviewerSparsePreludeInit nStart hostLongCountMirror))
          nStart leftStart rightStart hostLongCountMirror
          (packedReviewerSparsePreludeInit nStart hostLongCountMirror)
    | state => state
  packedReviewerDriveAgainstMemoryAux memory
    (packedReviewerControllerMeasure controller) controller' };
     Activation = @(
       'let hostLongCountMirror := SuccinctSpace.bitsToNatLE ((memory[0]?).getD [])',
       'packedReviewerSparsePreludeInit nStart hostLongCountMirror') },
  @{ Order = 5;  Id = 'M03-SHAPE-PARAMETER';
     Mutation = 'add or restore a semantic shape input';
     Verdict = 'REJECT'; Surface = 'exact signature';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerCapstone.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = 'def packedReviewerController (n left right : Nat) :
    PackedReviewerControllerState :=';
       Repl  = 'def packedReviewerController (n left right : Nat)
    (_shape : Option Cartesian.CartesianShape := none) :
    PackedReviewerControllerState :=' } },
  @{ Order = 6;  Id = 'M04-CANONICAL-SHAPE-BY-N';
     Mutation = 'synthesize a canonical shape from n inside a wrapper';
     Verdict = 'REJECT'; Surface = 'structural / same-object';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerController.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '  let controller := packedReviewerController n left right
  packedReviewerDriveAgainstMemoryAux memory
    (packedReviewerControllerMeasure controller) controller';
       Repl  = '  let controller := packedReviewerController n left right
  let canonicalShapeFromN := packedSpine n
  let canonicalMemoryFromN := packedReviewerMemory canonicalShapeFromN
  packedReviewerDriveAgainstMemoryAux canonicalMemoryFromN
    (packedReviewerControllerMeasure controller) controller' };
     Activation = @(
       'let canonicalShapeFromN := packedSpine n',
       'packedReviewerDriveAgainstMemoryAux canonicalMemoryFromN') },
  @{ Order = 7;  Id = 'M05-SIBLING-STORE';
     Mutation = 'read a logical/source store beside memory xs';
     Verdict = 'REJECT'; Surface = 'store identity';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerController.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = 'def packedReviewerRunAgainstMemory
    (memory : List (List Bool)) (n left right : Nat) : PackedReviewerRun :=
  let controller := packedReviewerController n left right
  packedReviewerDriveAgainstMemoryAux memory
    (packedReviewerControllerMeasure controller) controller';
       Repl  = 'def packedReviewerRunAgainstMemory
    (memory : List (List Bool)) (n left right : Nat) : PackedReviewerRun :=
  let controller := packedReviewerController n left right
  let siblingLogicalStore := memory ++ [[]]
  packedReviewerDriveAgainstMemoryAux siblingLogicalStore
    (packedReviewerControllerMeasure controller) controller' };
     Activation = @(
       'let siblingLogicalStore := memory ++ [[]]',
       'packedReviewerDriveAgainstMemoryAux siblingLogicalStore') },
  @{ Order = 8;  Id = 'M06-ANSWER-ORACLE';
     Mutation = 'call the reference/semantic answer from controller execution';
     Verdict = 'REJECT'; Surface = 'oracle independence';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '  | fuel + 1, n, left, right, longCount, sparseCount, state =>
      match packedReviewerWholeResult state with
      | some value => .done value';
       Repl  = '  | fuel + 1, n, left, right, longCount, sparseCount, state =>
      match packedReviewerWholeResult state with
      | some _value =>
          let semanticAnswerOracle := some n
          .done semanticAnswerOracle' };
     Activation = @(
       'let semanticAnswerOracle := some n',
       '.done semanticAnswerOracle') },
  @{ Order = 9;  Id = 'M07-DISCONNECTED-TRACE';
     Mutation = 'retain a correct result while forging or replaying an unrelated physical trace';
     Verdict = 'REJECT'; Surface = 'trace execution';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerControllerProof.lean';
       Find  = '    packedReviewerHeaderPhysicalTrace shape ++
      packedReviewerSparsePreludePhysicalTrace shape ++
        packedReviewerLogicalTracePhysicalTrace shape
          (packedReviewerDriveLogical
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
            (packedReviewerWholeStart shape.size left right)).trace
  else
    []';
       Repl  = '    (let disconnectedForgedTrace : List PackedReviewerPhysicalEvent := []; disconnectedForgedTrace)
  else
    []' };
     Activation = @(
       'let disconnectedForgedTrace : List PackedReviewerPhysicalEvent := []',
       '; disconnectedForgedTrace)') },
  @{ Order = 10; Id = 'M08-FORGED-PROBE-CAP';
     Mutation = 'replace derived trace length/cap evidence with a stored number or theorem-only field';
     Verdict = 'REJECT'; Surface = 'consumer';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'Validation/EGCPFinalFalsification.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '  | .header n left right =>
      1 + 2 * packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeInit n 0) +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right)';
       Repl  = '  | .header _ _ _ =>
      427' } },
  @{ Order = 11; Id = 'M09-WRONG-CELL-CROSSING';
     Mutation = 'mutate one crossing codec order/bit span';
     Verdict = 'REJECT'; Surface = 'exact decoded word';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/Probe.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/Probe.lean';
       Find  = '    [bit / packedCellWidth n, bit / packedCellWidth n + 1]';
       Repl  = '    [bit / packedCellWidth n + 1, bit / packedCellWidth n]' } },
  @{ Order = 12; Id = 'M10-SPARSE-COUNT-DEPENDENCY';
     Mutation = 'introduce sparse-count metadata into a live offset';
     Verdict = 'REJECT'; Surface = 'K1 source factorization';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/SourceGeometry.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/SourceGeometry.lean';
       Find  = 'def packedSourceStride (n : Nat) :';
       Repl  = 'def packedSourceStride (n _sparseCount : Nat) :' } },
  @{ Order = 13; Id = 'M11-SIBLING-PAYLOAD';
     Mutation = 'prove space for one payload while executing another';
     Verdict = 'REJECT'; Surface = 'public / same-object composition';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerMemory.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerMemory.lean';
       Find  = 'def packedReviewerSerializedBits (shape : CartesianShape) : List Bool :=
  packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape';
       Repl  = 'def packedReviewerSerializedBits (shape : CartesianShape) : List Bool :=
  let siblingExecutionPayload := packedReviewerPayloadBits shape ++ [false]
  packedReviewerHeaderBits shape ++ siblingExecutionPayload' };
     Activation = @(
       'let siblingExecutionPayload := packedReviewerPayloadBits shape ++ [false]',
       '++ siblingExecutionPayload') },
  @{ Order = 14; Id = 'M12-PUBLIC-TYPE-WEAKENING';
     Mutation = 'remove one load-bearing capstone conjunct';
     Verdict = 'REJECT'; Surface = 'independently frozen expected-type consumer';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'Validation/EGCPFinalFalsification.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerControllerStateProof.lean';
       Find  = 'theorem packedReviewerRunAgainstMemory_public_certificate
    (xs : List Int) (left right : Nat) :
    PackedReviewerPublicRunCertificate xs left right := by';
       Repl  = 'theorem packedReviewerRunAgainstMemory_public_certificate
    (_xs : List Int) (_left _right : Nat) : True := by
  trivial

private theorem packedReviewerRunAgainstMemory_public_certificate_original
    (xs : List Int) (left right : Nat) :
    PackedReviewerPublicRunCertificate xs left right := by' } },
  @{ Order = 15; Id = 'M13-HIDDEN-UNCOUNTED-TABLE';
     Mutation = 'add a content-dependent lookup/program constant outside memory xs';
     Verdict = 'REJECT'; Surface = 'closed controller / program accounting';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerController.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '          | some request =>
              let reply := memory[request.address]?';
       Repl  = '          | some request =>
              let hiddenUncountedTable := memory.take 1
              let reply :=
                if request.address < hiddenUncountedTable.length then
                  hiddenUncountedTable[request.address]?
                else
                  memory[request.address]?' };
     Activation = @(
       'let hiddenUncountedTable := memory.take 1',
       'hiddenUncountedTable[request.address]?') },
  @{ Order = 16; Id = 'M14-LONG-COUNT-IGNORED';
     Mutation = 'retain the header read but make downstream offsets independent of its value';
     Verdict = 'REJECT'; Surface = 'liveness';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '      let longCount := SuccinctSpace.bitsToNatLE cell';
       Repl  = '      let longCount := 0' };
     Activation = @(
       'let longCount := 0') }
)

# One literal owned campaign over the existing frozen registry.  This does not
# add, remove, or reorder a registry entry and does not change full-mode scope.
$script:Stages = @{
  'R2-ALLSIZE' = @(
    'M03-SHAPE-PARAMETER',
    'M05-SIBLING-STORE',
    'M06-ANSWER-ORACLE',
    'M07-DISCONNECTED-TRACE',
    'M08-FORGED-PROBE-CAP',
    'M11-SIBLING-PAYLOAD',
    'M12-PUBLIC-TYPE-WEAKENING'
  )
}

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

  foreach ($stageName in @($script:Stages.Keys)) {
    $stageIds = @($script:Stages[$stageName])
    if ([string]::IsNullOrWhiteSpace($stageName)) {
      Add-Failure 'stage registry contains an empty or whitespace name'
      $ok = $false
    }
    if ($stageIds.Count -eq 0) {
      Add-Failure "stage '$stageName' has an empty ID list"
      $ok = $false
      continue
    }

    $stageUnique = @($stageIds | Sort-Object -Unique)
    if ($stageUnique.Count -ne $stageIds.Count) {
      Add-Failure "stage '$stageName' contains duplicate IDs"
      $ok = $false
    }

    foreach ($stageId in $stageIds) {
      $known = @($script:Registry | Where-Object { $_.Id -eq $stageId })
      if ($known.Count -ne 1) {
        Add-Failure "stage '$stageName' ID '$stageId' occurs $($known.Count) times in the registry, expected exactly once"
        $ok = $false
        continue
      }
      $entry = $known[0]
      if ($entry.Verdict -ne 'REJECT') {
        Add-Failure "stage '$stageName' ID '$stageId' is not a REJECT case"
        $ok = $false
      }
      if ($null -eq $entry.Target) {
        Add-Failure "stage '$stageName' ID '$stageId' has no mutation target"
        $ok = $false
      }
    }
  }

  if ($ok) {
    Write-Stage "registry OK: 16 ordered entries, $accepts ACCEPT, $rejects REJECT; stage maps nonempty, unique, known, targeted REJECT IDs"
  }
  return $ok
}

# -------------------------------------------------- descendant termination

function Invoke-DescendantSelfTest {
  param([int] $DeadlineSeconds)

  Write-Stage 'descendant-termination self-test'

  # The grandchild's pid is reported through a file, so absence of BOTH the
  # owned root and the named descendant is checked directly by pid. The prior
  # marker-file check could fire only 120 s after spawn and therefore could
  # not observe a surviving grandchild at all; and on a non-Windows host the
  # prior body spawned 'powershell.exe' (absent) and name-grepped 'powershell'
  # (never matching), so the Ubuntu leg could have reported a pass without
  # ever exercising the kill. This body is the honest portable replacement.
  $pidFile = Join-Path ([System.IO.Path]::GetTempPath()) ("egcp-replay-" + [System.Guid]::NewGuid().ToString('N') + ".pid")
  $onWindows = Test-OnWindows
  $shellExe = if ($onWindows) { Join-Path $PSHOME 'powershell.exe' }
    else { Join-Path $PSHOME 'pwsh' }
  # A root that spawns a detached grandchild sleeper and records its pid, so
  # killing the root alone would leave a running grandchild whose pid we know.
  $childScript = "`$grandchild = Start-Process -FilePath '$shellExe' -ArgumentList '-NoProfile','-Command','Start-Sleep -Seconds 120' -PassThru; Set-Content -Path '$pidFile' -Value `$grandchild.Id; Start-Sleep -Seconds 120"

  if ($onWindows) {
    $proc = Start-Process -FilePath $shellExe `
      -ArgumentList '-NoProfile', '-Command', $childScript `
      -PassThru -WindowStyle Hidden
  } else {
    # `setsid` gives the root its own process group -- the object the Unix
    # branch of Stop-ProcessTree addresses by negated pid.
    $proc = Start-Process -FilePath 'setsid' `
      -ArgumentList $shellExe, '-NoProfile', '-Command', $childScript `
      -PassThru
  }

  $grandchildId = $null
  for ($i = 0; $i -lt 100; $i++) {
    if (Test-Path -LiteralPath $pidFile) {
      $raw = @(Get-Content -LiteralPath $pidFile -ErrorAction SilentlyContinue)
      if ($raw.Count -gt 0 -and $null -ne $raw[0] -and $raw[0].ToString().Trim().Length -gt 0) {
        $grandchildId = [int] $raw[0].ToString().Trim()
        break
      }
    }
    Start-Sleep -Milliseconds 200
  }
  if ($null -eq $grandchildId) {
    try { Stop-ProcessTree -RootId $proc.Id | Out-Null } catch { }
    if (Test-Path -LiteralPath $pidFile) { Remove-Item -LiteralPath $pidFile -Force }
    Add-Failure 'descendant self-test: the grandchild sleeper did not report a pid'
    return $false
  }

  $killed = Stop-ProcessTree -RootId $proc.Id
  if (-not $killed) {
    Add-Failure 'descendant self-test: could not terminate the owned process tree'
    return $false
  }

  Start-Sleep -Seconds 2
  $rootSurvivor = Get-Process -Id $proc.Id -ErrorAction SilentlyContinue
  if ($null -ne $rootSurvivor) {
    Add-Failure 'descendant self-test: the owned root survived termination'
    return $false
  }
  $grandchildSurvivor = Get-Process -Id $grandchildId -ErrorAction SilentlyContinue
  if ($null -ne $grandchildSurvivor) {
    try { Stop-ProcessTree -RootId $grandchildId | Out-Null } catch { }
    Add-Failure 'descendant self-test: the grandchild sleeper outlived its root'
    return $false
  }

  if (Test-Path -LiteralPath $pidFile) { Remove-Item -LiteralPath $pidFile -Force }
  Write-Stage 'descendant-termination self-test: PASS'
  return $true
}

function Test-OnWindows {
  # `$IsWindows` exists only on PowerShell Core. Under Windows PowerShell 5.1 it
  # is undefined, and `Set-StrictMode` makes a bare reference a terminating
  # error -- so probe for it instead of reading it.
  $flag = Get-Variable -Name 'IsWindows' -ValueOnly -ErrorAction SilentlyContinue
  if ($null -eq $flag) { return $true }
  return [bool] $flag
}

function Stop-ProcessTree {
  param([int] $RootId)

  if (-not (Test-OnWindows)) {
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

    # Mechanical activation check: a semantic mutant must actually contain and
    # use its illicit source/oracle/trace/payload in the written body. A
    # signature-only or unused-parameter edit cannot pass this check, so a
    # REJECT verdict cannot be produced by vacuous evidence.
    if ($Entry.ContainsKey('Activation') -and $null -ne $Entry.Activation) {
      $writtenBody = [System.Text.Encoding]::UTF8.GetString(
        [System.IO.File]::ReadAllBytes($path)) -replace "`r`n", "`n"
      foreach ($activationNeedle in @($Entry.Activation)) {
        $normalizedNeedle = $activationNeedle -replace "`r`n", "`n"
        if (-not $writtenBody.Contains($normalizedNeedle)) {
          Add-Failure "$($Entry.Id): activation needle absent from mutated body: $normalizedNeedle"
          $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'ACTIVATION-MISSING' }) | Out-Null
          return
        }
      }
      Write-Stage "$($Entry.Id): activation check passed ($(@($Entry.Activation).Count) needles present and used)"
    }

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
        # A build that fails somewhere is not evidence that the NAMED surface
        # failed. Require the diagnostic to name the expected file, so a
        # rejection caused by unrelated breakage is not read as the commissioned
        # verdict.
        $expected = $Entry.Target.ExpectFile
        $seen = $run.Diagnostic.Replace([char]92, [char]47)
        if ($seen -notlike ('*' + $expected + '*')) {
          Add-Failure "$($Entry.Id): rejected, but not at the named surface; expected a diagnostic naming $expected"
          Write-Host ('REPLAY-DIAG: ' + $run.Diagnostic)
          $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'WRONG-SURFACE' }) | Out-Null
        } else {
          Write-Stage "$($Entry.Id): REJECT as commissioned at $expected, surface '$($Entry.Surface)'"
          $script:Results.Add(@{ Id = $Entry.Id; Outcome = 'REJECT' }) | Out-Null
        }
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

$caseMode = $PSBoundParameters.ContainsKey('Case')
$stageMode = $PSBoundParameters.ContainsKey('Stage')
$fullMode = -not $caseMode -and -not $stageMode

if ($caseMode -and $stageMode) {
  Write-Host 'REPLAY-FAIL: -Case and -Stage are mutually exclusive'
  exit 2
}

if ($SelfTestOnly -and ($caseMode -or $stageMode)) {
  Write-Host 'REPLAY-FAIL: -SelfTestOnly is exclusive with -Case and -Stage'
  exit 2
}

if ($SelfTestOnly -and $SkipSelfTest) {
  Write-Host 'REPLAY-FAIL: -SelfTestOnly refuses -SkipSelfTest'
  exit 2
}

if ($caseMode) {
  if ($null -eq $Case -or $Case.Trim().Length -eq 0) {
    Write-Host 'REPLAY-FAIL: an explicitly supplied case selector must not be empty or whitespace'
    exit 2
  }
  $known = @($script:Registry | Where-Object { $_.Id -eq $Case })
  if ($known.Count -ne 1) {
    Write-Host "REPLAY-FAIL: unknown or non-unique case selector '$Case'"
    exit 2
  }
}

if ($stageMode) {
  if ($null -eq $Stage -or $Stage.Trim().Length -eq 0) {
    Write-Host 'REPLAY-FAIL: an explicitly supplied stage selector must not be empty or whitespace'
    exit 2
  }
  if (-not $script:Stages.ContainsKey($Stage)) {
    Write-Host "REPLAY-FAIL: unknown stage selector '$Stage'"
    exit 2
  }
}

if (-not (Test-RegistryIntegrity)) {
  Write-Host 'REPLAY-FAIL: registry integrity check failed'
  exit 3
}

if ($SelfTestOnly) {
  if (-not (Invoke-DescendantSelfTest -DeadlineSeconds 300)) {
    Write-Host 'REPLAY-FAIL: descendant-termination self-test failed'
    exit 6
  }
  Write-Host 'REPLAY: SELF-TEST-ONLY PASS - registry integrity and descendant termination verified'
  exit 0
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

if (($fullMode -or $stageMode) -and $SkipSelfTest) {
  if ($stageMode) {
    Write-Host "REPLAY-FAIL: stage '$Stage' refuses -SkipSelfTest"
  } else {
    Write-Host 'REPLAY-FAIL: full mode refuses -SkipSelfTest'
  }
  exit 5
}

if (-not $SkipSelfTest) {
  if (-not (Invoke-DescendantSelfTest -DeadlineSeconds $deadline)) {
    Write-Host 'REPLAY-FAIL: descendant-termination self-test failed'
    exit 6
  }
}

$cases = $script:Registry
if ($caseMode) {
  $cases = @($script:Registry | Where-Object { $_.Id -eq $Case })
} elseif ($stageMode) {
  # A generic List[object] under the Windows PowerShell 5.1 dynamic binder
  # fails to convert through `@(...)`; accumulate a plain array instead.
  $selected = @()
  foreach ($stageId in @($script:Stages[$Stage])) {
    $entry = @($script:Registry | Where-Object { $_.Id -eq $stageId })[0]
    $selected += , $entry
  }
  $cases = $selected
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

if ($caseMode) {
  if ($script:Failures.Count -gt 0) {
    Write-Host "REPLAY: SELECTED CASE FAILED ($($script:Failures.Count) failures)"
    exit 1
  }
  Write-Host 'REPLAY: SELECTED CASE OK'
  exit 0
}

if ($stageMode) {
  $expectedStageCount = @($script:Stages[$Stage]).Count
  $stageRejects = @($script:Results | Where-Object { $_.Outcome -eq 'REJECT' }).Count
  if ($ran -ne $expectedStageCount) {
    Add-Failure "stage '$Stage' produced $ran results, expected $expectedStageCount"
  }
  if ($stageRejects -ne $expectedStageCount) {
    Add-Failure "stage '$Stage' recorded $stageRejects REJECT outcomes, expected $expectedStageCount"
  }
  if ($script:Failures.Count -gt 0) {
    Write-Host "REPLAY: STAGE $Stage FAILED ($($script:Failures.Count) failures)"
    exit 1
  }
  Write-Host "REPLAY: STAGE $Stage PASS - all $expectedStageCount mutations rejected and tracked state restored"
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

<#
.SYNOPSIS
  Replay harness for the EG-CP Stage-A architecture campaign (`EG-CP-A12`).

.DESCRIPTION
  Encodes the frozen replay registry of
  `docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` section 4 literally, in the
  commissioned order, and replays each case against the working tree.

  A case is replayed by applying one textual mutation to one tracked file,
  rebuilding the Stage-A surface `RMQ.Validation.EGCPStageA`, and requiring the
  commissioned verdict:

    ACCEPT  the surface must still elaborate
    REJECT  the surface must fail to elaborate, with a diagnostic naming the
            frozen first failing file

  Every mutation is restored in a `finally` block, its restoration is verified
  by SHA256 against the pre-mutation content, and the run ends with a
  clean-tree check.  Twelve REJECT bodies and the `A02`-style expected-accept
  patch are byte-reused from the frozen Stage-F campaign
  (`scripts/eg_cp_final_falsification_replay.ps1`, which this script never
  edits); seven REJECT bodies are new Stage-A enactments.  Semantic mutants
  carry mechanical activation needles (`WDD-20260805-002`): every declared
  needle must be present in the written body before any build is attempted.

  A full-mode run with any TARGET-ABSENT case exits non-zero; on the committed
  Stage-A candidate every target exists.

.PARAMETER Case
  Replay exactly one registry ID.  Unknown, empty and whitespace selectors are
  errors.  Omitting every selector, and only that, means full mode.

.PARAMETER SelfTestOnly
  Validate the selectors, check registry integrity, run the
  descendant-termination self-test, and exit without building anything.
  Refuses -Case, -IntegrityProbe, and -SkipSelfTest.

.PARAMETER IntegrityProbe
  `OmitMiddle` or `DuplicateMiddle`: corrupt an in-memory copy of the frozen
  registry (drop or duplicate a middle entry) and require
  `Test-RegistryIntegrity` to fail on it while the real registry passes.  This
  exercises the omitted/duplicate middle-ID rejections of
  `REPLAY-SELECTOR-NONVACUITY` at the real script boundary without touching
  the frozen registry literal.  Builds nothing.  Refuses -Case, -SelfTestOnly,
  and -SkipSelfTest.

.PARAMETER SkipSelfTest
  Skip the descendant-termination self-test.  Development only; a full-mode
  run refuses it.

.NOTES
  Process-tree termination is certified on Windows, the required gate platform
  for this task.  The non-Windows branch of Stop-ProcessTree is carried but
  uncertified here; this script makes no cross-platform claim.
#>

[CmdletBinding()]
param(
  [AllowEmptyString()]
  [string] $Case,
  [switch] $SelfTestOnly,
  [AllowEmptyString()]
  [string] $IntegrityProbe,
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

# Ordered exactly as frozen by matrix section 4.  `Rows` and `Fields` are the
# frozen case-to-row and case-to-field/object mappings; `Test-RegistryIntegrity`
# rejects an entry without them.
$script:Registry = @(
  @{ Order = 1;  Id = 'SA-A01-PRODUCTION-EXPECTED-ACCEPT';
     Mutation = 'unchanged final implementation, consumer, matrix, and result';
     Verdict = 'ACCEPT'; Surface = 'none';
     Rows = 'all rows (control)'; Fields = 'all fields';
     Target = @{ Kind = 'None' } },
  @{ Order = 2;  Id = 'SA-A02-UNREAD-CELL-EXPECTED-ACCEPT';
     Mutation = 'patch the frozen unread replacement value (inherited Stage-F A02 body)';
     Verdict = 'ACCEPT'; Surface = 'none';
     Rows = 'EG-CP-A10, INV-STORE-AGREEMENT'; Fields = 'field 37 / fixture cell u0 = 4';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'none';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean';
       Find  = 'def egcpStageFUnreadReplacementCell : List Bool :=
  List.replicate (packedReviewerCellWidth 3) true';
       Repl  = 'def egcpStageFUnreadReplacementCell : List Bool :=
  false :: List.replicate (packedReviewerCellWidth 3 - 1) true' };
     Activation = @(
       'false :: List.replicate (packedReviewerCellWidth 3 - 1) true') },
  @{ Order = 3;  Id = 'SA-M01-SIBLING-STORE';
     Mutation = 'driver binds a sibling store beside the counted memory (inherited M05 body)';
     Verdict = 'REJECT'; Surface = 'one-object identity';
     Rows = 'EG-CP-A01, INV-READ-BACKING'; Fields = 'fields 5, 20 / memory vs sibling';
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
  @{ Order = 4;  Id = 'SA-M02-SIBLING-PAYLOAD';
     Mutation = 'execution consumes a sibling payload while the public chain stays pinned (inherited M11 body)';
     Verdict = 'REJECT'; Surface = 'same-object composition';
     Rows = 'EG-CP-A01, EG-CP-A02, INV-PUBLIC-COMPOSITION'; Fields = 'fields 1-3 / payload identity';
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
  @{ Order = 5;  Id = 'SA-M03-CANONICAL-SHAPE-BY-N';
     Mutation = 'run drives a canonical memory synthesized from n (inherited M04 body)';
     Verdict = 'REJECT'; Surface = 'structural / same-object';
     Rows = 'EG-CP-A01, EG-CP-A09'; Fields = 'field 5 / supplied vs synthesized memory';
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
  @{ Order = 6;  Id = 'SA-M04-ALLOCATION-HEADER-CELL-DROP';
     Mutation = 'the cell count drops the header cell, so allocation undercounts (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'allocated capacity';
     Rows = 'EG-CP-A02'; Fields = 'fields 3, 7, 8 / allocated capacity';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerMemory.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerMemory.lean';
       Find  = 'def packedReviewerCellCount (n longCount sparseCount : Nat) : Nat :=
  1 + GenericSelect.selectCeilDiv
    (packedReviewerPayloadLength n longCount sparseCount)
    (packedReviewerCellWidth n)';
       Repl  = 'def packedReviewerCellCount (n longCount sparseCount : Nat) : Nat :=
  GenericSelect.selectCeilDiv
    (packedReviewerPayloadLength n longCount sparseCount)
    (packedReviewerCellWidth n)' };
     Activation = @(
       'def packedReviewerCellCount (n longCount sparseCount : Nat) : Nat :=
  GenericSelect.selectCeilDiv') },
  @{ Order = 7;  Id = 'SA-M05-WIDTH-SUBSTITUTION';
     Mutation = 'the one width function is replaced by a different size-only value (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'exact width identity';
     Rows = 'EG-CP-A03'; Fields = 'fields 11-15 / the one width function';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerWidth.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerWidth.lean';
       Find  = 'def packedReviewerCellWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedReviewerCellBound n + 2)';
       Repl  = 'def packedReviewerCellWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (n + 2)' };
     Activation = @(
       'SuccinctRank.machineWordBits (n + 2)') },
  @{ Order = 8;  Id = 'SA-M06-WRONG-LONG-COUNT';
     Mutation = 'the executed controller consumes an altered header count (inherited M01 body)';
     Verdict = 'REJECT'; Surface = 'liveness/consumer';
     Rows = 'EG-CP-A04, INV-VALUE-DEPENDENCY'; Fields = 'fields 17, 19 / decoded header value';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '      let longCount := SuccinctSpace.bitsToNatLE cell';
       Repl  = '      let longCount := SuccinctSpace.bitsToNatLE cell + 1' };
     Activation = @(
       'let longCount := SuccinctSpace.bitsToNatLE cell + 1') },
  @{ Order = 9;  Id = 'SA-M07-HOST-LONG-COUNT-MIRROR';
     Mutation = 'the header reply is bypassed by preprocessing/host metadata (inherited M02 body)';
     Verdict = 'REJECT'; Surface = 'structural consumer';
     Rows = 'EG-CP-A04, EG-CP-A09'; Fields = 'fields 16, 18 / charged header read';
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
  @{ Order = 10; Id = 'SA-M08-LONG-COUNT-IGNORED';
     Mutation = 'the header read is retained but downstream offsets ignore its value (inherited M14 body)';
     Verdict = 'REJECT'; Surface = 'liveness';
     Rows = 'EG-CP-A04, INV-VALUE-DEPENDENCY'; Fields = 'field 19 / downstream address dependency';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '      let longCount := SuccinctSpace.bitsToNatLE cell';
       Repl  = '      let longCount := 0' };
     Activation = @(
       'let longCount := 0') },
  @{ Order = 11; Id = 'SA-M09-CROSSING-SWAP';
     Mutation = 'the reviewer probe plan issues the two crossing cells in the wrong order (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'crossing expansion';
     Rows = 'EG-CP-A05'; Fields = 'field 25 / crossing expansion order';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerProbe.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerProbe.lean';
       Find  = '    [bit / packedReviewerCellWidth n, bit / packedReviewerCellWidth n + 1]';
       Repl  = '    [bit / packedReviewerCellWidth n + 1, bit / packedReviewerCellWidth n]' };
     Activation = @(
       '[bit / packedReviewerCellWidth n + 1, bit / packedReviewerCellWidth n]') },
  @{ Order = 12; Id = 'SA-M10-DISCONNECTED-TRACE';
     Mutation = 'the expected physical trace is forged while the result path is untouched (inherited M07 body)';
     Verdict = 'REJECT'; Surface = 'trace execution';
     Rows = 'EG-CP-A05, EG-CP-A10, INV-SEMANTIC-NONVACUITY'; Fields = 'field 24 / ordered grouping';
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
  @{ Order = 13; Id = 'SA-M11-FORGED-PROBE-CAP';
     Mutation = 'the derived measure arm is replaced by a stored literal 427 (inherited M08 body)';
     Verdict = 'REJECT'; Surface = 'derived-measure consumer';
     Rows = 'EG-CP-A06'; Fields = 'field 27 / derived measure';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerCapstone.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '  | .header n left right =>
      1 + 2 * packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeInit n 0) +
        2 * packedReviewerWholeRemaining
          (packedReviewerWholeStart n left right)';
       Repl  = '  | .header _ _ _ =>
      427' } },
  @{ Order = 14; Id = 'SA-M12-RESULT-OFFSET';
     Mutation = 'the whole-result completion arm offsets every returned index by one (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'valid result correctness';
     Rows = 'EG-CP-A07, INV-VALUE-DEPENDENCY'; Fields = 'fields 28-29 / returned index';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = '  | fuel + 1, n, left, right, longCount, sparseCount, state =>
      match packedReviewerWholeResult state with
      | some value => .done value';
       Repl  = '  | fuel + 1, n, left, right, longCount, sparseCount, state =>
      match packedReviewerWholeResult state with
      | some value => .done (value.map (fun index => index + 1))' };
     Activation = @(
       'value.map (fun index => index + 1)') },
  @{ Order = 15; Id = 'SA-M13-INVALID-GUARD-RESULT';
     Mutation = 'the invalid entry arm fabricates the answer some 0 (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'invalid-domain contract';
     Rows = 'EG-CP-A08'; Fields = 'fields 30-31 / invalid-domain result';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerControllerProof.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       # ASCII-only anchor: Windows PowerShell 5.1 decodes a BOM-free script
       # as ANSI, so a non-ASCII character in a needle would be corrupted
       # before matching (the SA-M13 anchor-drift repair; the guard line with
       # its Unicode conjunction is deliberately not part of the needle).
       Find  = '    .header n left right
  else
    .done none';
       Repl  = '    .header n left right
  else
    .done (some 0)' };
     Activation = @(
       '.done (some 0)') },
  @{ Order = 16; Id = 'SA-M14-SHAPE-PARAMETER';
     Mutation = 'the controller gains an optional semantic shape parameter (inherited M03 body)';
     Verdict = 'REJECT'; Surface = 'exact signature';
     Rows = 'EG-CP-A09'; Fields = 'field 32 / exact input boundary';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerCapstone.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean';
       Find  = 'def packedReviewerController (n left right : Nat) :
    PackedReviewerControllerState :=';
       Repl  = 'def packedReviewerController (n left right : Nat)
    (_shape : Option Cartesian.CartesianShape := none) :
    PackedReviewerControllerState :=' } },
  @{ Order = 17; Id = 'SA-M15-HIDDEN-UNCOUNTED-TABLE';
     Mutation = 'the driver serves replies from a content-dependent table outside the counted memory (inherited M13 body)';
     Verdict = 'REJECT'; Surface = 'closed controller / program accounting';
     Rows = 'EG-CP-A09, INV-READ-BACKING'; Fields = 'field 20 / reply provenance';
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
  @{ Order = 18; Id = 'SA-M16-ANSWER-ORACLE';
     Mutation = 'the completion arm discards the computed value for a metadata oracle (inherited M06 body; the frozen SF-M06-BRIDGE covers the reference-oracle direction)';
     Verdict = 'REJECT'; Surface = 'oracle independence';
     Rows = 'EG-CP-A07, EG-CP-A10'; Fields = 'fields 28, 38 / metadata completion';
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
  @{ Order = 19; Id = 'SA-M17-DECISIVE-MUTANT-NEUTRALIZED';
     Mutation = 'the frozen decisive mutant cell is set to the canonical cell-8 value, so the corruption is a no-op (new Stage-A body)';
     Verdict = 'REJECT'; Surface = 'decisive corruption reality';
     Rows = 'EG-CP-A10, INV-SEMANTIC-NONVACUITY'; Fields = 'field 36 / decisive corruption reality';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerCapstone.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerCapstone.lean';
       Find  = 'def egcpDecisiveMutantCell : List Bool := [true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]';
       Repl  = 'def egcpDecisiveMutantCell : List Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]' };
     Activation = @(
       'def egcpDecisiveMutantCell : List Bool := [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false]') },
  @{ Order = 20; Id = 'SA-M18-PUBLIC-CERTIFICATE-WEAKENING';
     Mutation = 'the public run certificate is weakened to True with the original kept private (inherited M12 body)';
     Verdict = 'REJECT'; Surface = 'independently frozen expected-type consumer';
     Rows = 'EG-CP-A11, INV-PUBLIC-COMPOSITION'; Fields = 'certificate-projected fields';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'PackedCellProbe/ReviewerCapstone.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerControllerStateProof.lean';
       Find  = 'theorem packedReviewerRunAgainstMemory_public_certificate
    (xs : List Int) (left right : Nat) :
    PackedReviewerPublicRunCertificate xs left right := by';
       Repl  = 'theorem packedReviewerRunAgainstMemory_public_certificate
    (_xs : List Int) (_left _right : Nat) : True := by
  trivial

private theorem packedReviewerRunAgainstMemory_public_certificate_original
    (xs : List Int) (left right : Nat) :
    PackedReviewerPublicRunCertificate xs left right := by' };
     Activation = @(
       'packedReviewerRunAgainstMemory_public_certificate_original') },
  @{ Order = 21; Id = 'SA-M19-ARCHITECTURE-PROPOSITION-WEAKENING';
     Mutation = 'the Stage-A capstone producer is weakened to True with the original kept private (new Stage-A body, M12-style)';
     Verdict = 'REJECT'; Surface = 'the committed Stage-A consumer';
     Rows = 'EG-CP-A11'; Fields = 'the entire combined proposition';
     Target = @{ Kind = 'Patch';
       ExpectFile = 'Validation/EGCPStageA.lean';
       File = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerArchitectureCapstone.lean';
       Find  = 'theorem packedReviewerArchitectureCapstone_holds
    (xs : List Int) (left right : Nat) :
    PackedReviewerArchitectureCapstone xs left right := by';
       Repl  = 'theorem packedReviewerArchitectureCapstone_holds
    (_xs : List Int) (_left _right : Nat) : True := by
  trivial

private theorem packedReviewerArchitectureCapstone_holds_original
    (xs : List Int) (left right : Nat) :
    PackedReviewerArchitectureCapstone xs left right := by' };
     Activation = @(
       'packedReviewerArchitectureCapstone_holds_original') }
)

# ------------------------------------------------------- registry self-checks

function Test-RegistryIntegrity {
  param(
    $Entries = $null
  )
  if ($null -eq $Entries) { $Entries = $script:Registry }
  Write-Stage 'validating the frozen registry'
  $ok = $true

  if (@($Entries).Count -ne 21) {
    Add-Failure "registry has $(@($Entries).Count) entries, expected 21"
    $ok = $false
  }

  $ids = @($Entries | ForEach-Object { $_.Id })
  $unique = @($ids | Sort-Object -Unique)
  if ($unique.Count -ne $ids.Count) {
    Add-Failure 'registry contains duplicate IDs'
    $ok = $false
  }

  $expectedOrder = 1
  foreach ($entry in $Entries) {
    if ($entry.Order -ne $expectedOrder) {
      Add-Failure "registry order broken at ID $($entry.Id): saw $($entry.Order), expected $expectedOrder"
      $ok = $false
    }
    $expectedOrder = $expectedOrder + 1
    if ($entry.Verdict -ne 'ACCEPT' -and $entry.Verdict -ne 'REJECT') {
      Add-Failure "registry entry $($entry.Id) has unmapped verdict '$($entry.Verdict)'"
      $ok = $false
    }
    if (-not $entry.ContainsKey('Rows') -or
        [string]::IsNullOrWhiteSpace([string]$entry.Rows)) {
      Add-Failure "registry entry $($entry.Id) has no frozen row mapping"
      $ok = $false
    }
    if (-not $entry.ContainsKey('Fields') -or
        [string]::IsNullOrWhiteSpace([string]$entry.Fields)) {
      Add-Failure "registry entry $($entry.Id) has no frozen field/object mapping"
      $ok = $false
    }
  }

  $accepts = @($Entries | Where-Object { $_.Verdict -eq 'ACCEPT' }).Count
  $rejects = @($Entries | Where-Object { $_.Verdict -eq 'REJECT' }).Count
  if ($accepts -ne 2) {
    Add-Failure "expected exactly 2 ACCEPT cases, found $accepts"
    $ok = $false
  }
  if ($rejects -ne 19) {
    Add-Failure "expected exactly 19 REJECT cases, found $rejects"
    $ok = $false
  }

  if ($ok) {
    Write-Stage "registry OK: 21 ordered entries, $accepts ACCEPT, $rejects REJECT; every entry carries its frozen row and field/object mapping"
  }
  return $ok
}

# -------------------------------------------------- descendant termination

function Test-OnWindows {
  $flag = Get-Variable -Name 'IsWindows' -ValueOnly -ErrorAction SilentlyContinue
  if ($null -eq $flag) { return $true }
  return [bool] $flag
}

function Stop-ProcessTree {
  param([int] $RootId)

  if (-not (Test-OnWindows)) {
    # Carried but uncertified on this task: the required gate platform is
    # Windows.  No cross-platform claim is made.
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

function Invoke-DescendantSelfTest {
  param([int] $DeadlineSeconds)

  Write-Stage 'descendant-termination self-test'

  $pidFile = Join-Path ([System.IO.Path]::GetTempPath()) ("egcp-stagea-replay-" + [System.Guid]::NewGuid().ToString('N') + ".pid")
  $onWindows = Test-OnWindows
  $shellExe = if ($onWindows) { Join-Path $PSHOME 'powershell.exe' }
    else { Join-Path $PSHOME 'pwsh' }
  $childScript = "`$grandchild = Start-Process -FilePath '$shellExe' -ArgumentList '-NoProfile','-Command','Start-Sleep -Seconds 120' -PassThru; Set-Content -Path '$pidFile' -Value `$grandchild.Id; Start-Sleep -Seconds 120"

  if ($onWindows) {
    $proc = Start-Process -FilePath $shellExe `
      -ArgumentList '-NoProfile', '-Command', $childScript `
      -PassThru -WindowStyle Hidden
  } else {
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

  $outTask = $proc.StandardOutput.ReadToEndAsync()
  $errTask = $proc.StandardError.ReadToEndAsync()

  $exited = $proc.WaitForExit($DeadlineSeconds * 1000)
  if (-not $exited) {
    Stop-ProcessTree -RootId $proc.Id | Out-Null
    try { $proc.WaitForExit(10000) | Out-Null } catch { }
    return @{ TimedOut = $true; ExitCode = $null; Diagnostic = 'timeout' }
  }
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
    Write-Stage "$($Entry.Id): TARGET-ABSENT (frozen surface '$($Entry.Surface)' does not exist on this candidate)"
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
        Write-Host ('REPLAY-DIAG: ' + $run.Diagnostic)
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
$probeMode = $PSBoundParameters.ContainsKey('IntegrityProbe')
$fullMode = -not $caseMode -and -not $probeMode -and -not $SelfTestOnly

if ($caseMode -and $probeMode) {
  Write-Host 'REPLAY-FAIL: -Case and -IntegrityProbe are mutually exclusive'
  exit 2
}

if ($SelfTestOnly -and ($caseMode -or $probeMode)) {
  Write-Host 'REPLAY-FAIL: -SelfTestOnly is exclusive with -Case and -IntegrityProbe'
  exit 2
}

if ($SelfTestOnly -and $SkipSelfTest) {
  Write-Host 'REPLAY-FAIL: -SelfTestOnly refuses -SkipSelfTest'
  exit 2
}

if ($probeMode -and $SkipSelfTest) {
  Write-Host 'REPLAY-FAIL: -IntegrityProbe refuses -SkipSelfTest'
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

if ($probeMode) {
  if ($null -eq $IntegrityProbe -or $IntegrityProbe.Trim().Length -eq 0) {
    Write-Host 'REPLAY-FAIL: an explicitly supplied integrity probe must not be empty or whitespace'
    exit 2
  }
  if ($IntegrityProbe -ne 'OmitMiddle' -and $IntegrityProbe -ne 'DuplicateMiddle') {
    Write-Host "REPLAY-FAIL: unknown integrity probe '$IntegrityProbe' (expected OmitMiddle or DuplicateMiddle)"
    exit 2
  }
}

if (-not (Test-RegistryIntegrity)) {
  Write-Host 'REPLAY-FAIL: registry integrity check failed'
  exit 3
}

if ($probeMode) {
  # Corrupt an in-memory copy around the middle entry (index 10 of 21) and
  # require the integrity check to fail on it.  The frozen literal is untouched.
  $middleIndex = 10
  $corrupted = @()
  for ($i = 0; $i -lt @($script:Registry).Count; $i++) {
    if ($IntegrityProbe -eq 'OmitMiddle' -and $i -eq $middleIndex) { continue }
    $corrupted += , $script:Registry[$i]
    if ($IntegrityProbe -eq 'DuplicateMiddle' -and $i -eq $middleIndex) {
      $corrupted += , $script:Registry[$i]
    }
  }
  Write-Stage "integrity probe '$IntegrityProbe': validating the deliberately corrupted registry copy (middle ID $($script:Registry[$middleIndex].Id))"
  $preFailures = $script:Failures.Count
  $corruptedOk = Test-RegistryIntegrity -Entries $corrupted
  if ($corruptedOk) {
    Write-Host "REPLAY-FAIL: integrity probe '$IntegrityProbe' was NOT rejected"
    exit 3
  }
  # The corruption diagnostics above are the probe's expected output, not run
  # failures; drop them so the probe itself can report success.
  while ($script:Failures.Count -gt $preFailures) {
    $script:Failures.RemoveAt($script:Failures.Count - 1)
  }
  Write-Host "REPLAY: INTEGRITY PROBE '$IntegrityProbe' OK - the corrupted registry copy is rejected and the frozen registry passes"
  exit 0
}

if ($SelfTestOnly) {
  if (-not (Invoke-DescendantSelfTest -DeadlineSeconds 300)) {
    Write-Host 'REPLAY-FAIL: descendant-termination self-test failed'
    exit 6
  }
  Write-Host 'REPLAY: SELF-TEST-ONLY PASS - registry integrity and descendant termination verified'
  exit 0
}

$surfaceModule = 'RMQ.Validation.EGCPStageA'

# Evidence-based deadline: measure the clean surface build, then a
# representative mutated-chain rebuild (probe on the controller module, the
# deepest common import of every mutation target), and allow four times the
# larger measurement with a floor of 300 s.
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

$probeRelative = 'RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReviewerController.lean'
$probePath = Join-Path $script:RepoRoot $probeRelative
$probeOriginalBytes = [System.IO.File]::ReadAllBytes($probePath)
$probeOriginalHash = Get-FileHashHex -Path $probePath
$probeSeconds = 0
try {
  $probeText = [System.Text.Encoding]::UTF8.GetString($probeOriginalBytes)
  $utf8NoBomProbe = New-Object System.Text.UTF8Encoding $false
  # A private definition changes the compiled artifact and forces the whole
  # downstream chain, unlike a comment-only edit.
  [System.IO.File]::WriteAllText($probePath,
    ($probeText + "`nprivate def egcpStageADeadlineCalibrationProbe : Nat := 0`n"), $utf8NoBomProbe)
  Write-Stage "measuring a representative mutated-chain rebuild (probe on $probeRelative)"
  $swProbe = [System.Diagnostics.Stopwatch]::StartNew()
  $probeRun = Invoke-BoundedLake -Module $surfaceModule -DeadlineSeconds 3600
  $swProbe.Stop()
  if ($probeRun.TimedOut -or $probeRun.ExitCode -ne 0) {
    Write-Host 'REPLAY-FAIL: the deadline calibration probe rebuild failed'
    if (-not $probeRun.TimedOut) { Write-Host $probeRun.Diagnostic }
    exit 4
  }
  $probeSeconds = [int][Math]::Ceiling($swProbe.Elapsed.TotalSeconds)
} finally {
  [System.IO.File]::WriteAllBytes($probePath, $probeOriginalBytes)
  $probeRestoredHash = Get-FileHashHex -Path $probePath
  if ($probeRestoredHash -ne $probeOriginalHash) {
    Write-Host "REPLAY-FAIL: probe restoration hash mismatch for $probeRelative"
    exit 4
  }
}
$rebase = Invoke-BoundedLake -Module $surfaceModule -DeadlineSeconds 3600
if ($rebase.TimedOut -or $rebase.ExitCode -ne 0) {
  Write-Host 'REPLAY-FAIL: the post-probe clean rebuild failed'
  if (-not $rebase.TimedOut) { Write-Host $rebase.Diagnostic }
  exit 4
}
$deadline = [Math]::Max([Math]::Max($baselineSeconds, $probeSeconds) * 4, 300)
Write-Stage "clean build took $baselineSeconds s; mutated-chain probe took $probeSeconds s; per-case deadline $deadline s"

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
if ($caseMode) {
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
  Write-Host ("REPLAY-CASE: {0,-42} {1}" -f $r.Id, $r.Outcome)
}

if ($caseMode) {
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
  Write-Host "REPLAY: FULL MODE INCOMPLETE - $absent frozen cases have no failing surface on this candidate"
  Write-Host 'REPLAY: this is not a pass, and EG-CP-A12 stays Open'
  exit 7
}

Write-Host 'REPLAY: FULL MODE PASS'
exit 0

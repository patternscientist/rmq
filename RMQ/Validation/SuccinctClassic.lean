import RMQ.Core.SuccinctRMQClassic

/-!
# Executable validation for the classic public succinct RMQ API

This module is an executable differential harness.  It computes
`SuccinctClassic.queryCosted xs left right` directly and compares its erased
answer with the independent `List Int` contract on deterministic small inputs,
including valid windows and empty, reversed, and out-of-bounds ranges.  It also
checks the canonical same/cross-block routes and genuine flat-store backing and
dependency evidence.
-/

namespace RMQ.Validation.SuccinctClassic

structure Mismatch where
  xs : List Int
  left : Nat
  right : Nat
  got : Option Nat
  expected : Option Nat
deriving Repr

inductive CanonicalQueryRoute where
  | invalid
  | sameBlock
  | crossBlock
deriving Repr, DecidableEq, BEq

def generatedInput (len seed : Nat) : List Int :=
  (List.range len).map fun i =>
    Int.ofNat ((seed * 5 + len * 3 + i * i + 2 * i) % 7) - 3

def tieInputs : List (List Int) :=
  [[],
    [0],
    [1, 1],
    [2, 2, 1, 1],
    [5, 4, 4],
    [4, 4, 5],
    [3, 1, 4, 1, 5],
    [8, 6, 7, 6, 9],
    [-1, -1, 0, -1],
    [2, -3, -3, 4, -3]]

def generatedInputs : List (List Int) :=
  tieInputs ++
    (List.range 6).flatMap fun len =>
      (List.range (len + 3)).map fun seed =>
        generatedInput len seed

def validWindowsFor (xs : List Int) : List (Prod Nat Nat) :=
  (List.range xs.length).flatMap fun left =>
    (List.range (xs.length - left)).map fun offset =>
      (left, left + offset + 1)

def invalidWindowsFor (xs : List Int) : List (Prod Nat Nat) :=
  [ (0, 0)
  , (xs.length, xs.length)
  , (1, 0)
  , (0, xs.length + 1)
  ]

def windowsFor (xs : List Int) : List (Prod Nat Nat) :=
  validWindowsFor xs ++ invalidWindowsFor xs

def expectedAnswer (xs : List Int) (left right : Nat) : Option Nat :=
  if RMQ.ValidRange xs left right then
    some (RMQ.scanWindow xs left (right - left))
  else
    none

def checkWindow (xs : List Int) (window : Prod Nat Nat) : Option Mismatch :=
  let left := window.1
  let right := window.2
  let got := (RMQ.SuccinctClassic.queryCosted xs left right).erase
  let expected := expectedAnswer xs left right
  if got == expected then
    none
  else
    some { xs, left, right, got, expected }

def firstWindowMismatch (xs : List Int) : List (Prod Nat Nat) -> Option Mismatch
  | [] => none
  | window :: windows =>
      match checkWindow xs window with
      | some mismatch => some mismatch
      | none => firstWindowMismatch xs windows

def firstMismatch : List (List Int) -> Option Mismatch
  | [] => none
  | xs :: inputs =>
      match firstWindowMismatch xs (windowsFor xs) with
      | some mismatch => some mismatch
      | none => firstMismatch inputs

def totalWindowCount : Nat :=
  generatedInputs.foldl (fun total xs => total + (windowsFor xs).length) 0

/-- Executable inspection of the actual canonical close/LCA route. -/
def canonicalQueryRoute
    (xs : List Int) (left right : Nat) : CanonicalQueryRoute :=
  if _hvalid : RMQ.ValidRange xs left right then
    let shape := RMQ.SuccinctClassic.cartesianShape xs
    match RMQ.SuccinctSpace.bpCloseOfInorder? shape left,
        RMQ.SuccinctSpace.bpCloseOfInorder? shape (right - 1) with
    | some leftClose, some rightClose =>
        let blockSize :=
          RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
        if RMQ.SuccinctClose.blockOfClose blockSize leftClose =
            RMQ.SuccinctClose.blockOfClose blockSize rightClose then
          .sameBlock
        else
          .crossBlock
    | _, _ => .invalid
  else
    .invalid

/-- Canonical physical store with the first execution-derived address removed. -/
def dropFirstConsumedPhysicalWord
    (xs : List Int) (left right : Nat) : RMQ.WordRAM.ReadStore :=
  let canonical := RMQ.SuccinctClassic.reviewerPhysicalReadStore xs
  let first? :=
    (RMQ.SuccinctClassic.reviewerPhysicalFootprint xs left right).head?
  { readWord? := fun segment address =>
      if segment == 0 && some address == first? then none
      else canonical.readWord? segment address }

def physicalReadsMatchCanonicalStore
    (xs : List Int) (left right : Nat) : Bool :=
  let result :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right
  let words := RMQ.SuccinctClassic.reviewerPhysicalWords xs
  result.trace.all fun event =>
    match event with
    | RMQ.WordRAM.TraceEvent.readWord segment address word? =>
        segment == 0 && words[address]? == word?
    | _ => true

def routeEvidenceOK : Bool :=
  canonicalQueryRoute ([3, 1, 4, 1, 5] : List Int) 2 4 ==
      .sameBlock &&
    canonicalQueryRoute ([3, 1, 4, 1, 5] : List Int) 0 5 ==
      .crossBlock &&
    canonicalQueryRoute ([3, 1, 4, 1, 5] : List Int) 1 1 == .invalid

def physicalErasureOK : Bool :=
  let xs : List Int := [3, 1, 4, 1, 5]
  RMQ.SuccinctSpace.flattenPayloadWords
      (RMQ.SuccinctClassic.reviewerPhysicalWords xs) ==
    RMQ.SuccinctClassic.buildPayload xs

def physicalBackingOK : Bool :=
  physicalReadsMatchCanonicalStore ([7] : List Int) 0 1

/--
Anti-vacuity mutant for the supplied-word-value subclaim: preserve the trace
from the supplied physical-store execution, but ignore its returned value and
substitute the canonical-store value.  The singleton corruption below kills
this mutant at the `.value` projection.
-/
def ignoreSuppliedStoreReturnedValueMutation
    (xs : List Int) (physicalStore : RMQ.WordRAM.ReadStore)
    (left right : Nat) : RMQ.WordRAM.TraceResult (Option Nat) :=
  let supplied :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
      xs physicalStore left right
  let canonical :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right
  { value := canonical.value, trace := supplied.trace }

def singletonCanonicalPhysicalResult :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([7] : List Int) 0 1

def singletonDroppedPhysicalStore :=
  dropFirstConsumedPhysicalWord ([7] : List Int) 0 1

def singletonCorruptedPhysicalResult :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
    ([7] : List Int) singletonDroppedPhysicalStore 0 1

def singletonIgnoreReturnedValueMutationResult :=
  ignoreSuppliedStoreReturnedValueMutation
    ([7] : List Int) singletonDroppedPhysicalStore 0 1

/-- The decisive word is actually consumed by the canonical execution. -/
def singletonDecisiveReadConsumedOK : Bool :=
  singletonCanonicalPhysicalResult.trace.contains
    (RMQ.WordRAM.TraceEvent.readWord 0 7
      ((RMQ.SuccinctClassic.reviewerPhysicalWords ([7] : List Int))[7]?))

/-- The physical corruption really changes the word returned at the consumed
address, rather than merely changing an unrelated store cell. -/
def singletonDecisiveStoreWordChangedOK : Bool :=
  (RMQ.SuccinctClassic.reviewerPhysicalReadStore ([7] : List Int)).readWord?
      0 7 !=
    singletonDroppedPhysicalStore.readWord? 0 7

/- Kernel-reduced corruption witness at the answer projection. -/
#guard singletonCanonicalPhysicalResult.value == some 0
#guard singletonCorruptedPhysicalResult.value == none
#guard singletonDecisiveReadConsumedOK
#guard singletonDecisiveStoreWordChangedOK

/- The returned-value-ignoring mutant keeps the stale canonical answer and is
therefore rejected by the same decisive corruption. -/
#guard singletonIgnoreReturnedValueMutationResult.value == some 0
#guard singletonCorruptedPhysicalResult.value !=
  singletonIgnoreReturnedValueMutationResult.value

/- Guarded/unguarded composition mutation: the raw shape evaluator still has
an internal answer on this empty range, while the public physical execution is
the required guarded `none`.  Substituting raw adequacy on all inputs therefore
changes the public execution. -/
def invalidEmptyRawPhysicalResult :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
    (RMQ.SuccinctClassic.cartesianShape ([9, 8, 7] : List Int)) 1 1

def invalidEmptyPublicPhysicalResult :=
  RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([9, 8, 7] : List Int) 1 1

#guard invalidEmptyRawPhysicalResult.value !=
  invalidEmptyPublicPhysicalResult.value

/- Separate invalid-branch mutations for every public execution projection. -/
#guard invalidEmptyPublicPhysicalResult.value != some 0
#guard invalidEmptyPublicPhysicalResult.trace !=
  [RMQ.WordRAM.TraceEvent.syntheticCostOnlyPrimitive]
#guard (RMQ.SuccinctClassic.queryCosted
  ([9, 8, 7] : List Int) 1 1).cost != 1
#guard (RMQ.SuccinctClassic.reviewerPhysicalFootprint
  ([9, 8, 7] : List Int) 1 1) != [0]
#guard (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
  ([9, 8, 7] : List Int) singletonDroppedPhysicalStore 1 1).value != some 0

/- Occurrence-level provenance must not collapse equal event values.  The two
select-close invocations in this valid singleton query emit identical
fifteen-event component traces, so global positions `0` and `15` carry the same
successful read value while remaining distinct provenance obligations.  The
closed program check pins those occurrences to its distinct instruction
positions `0` and `1`, rather than inferring instruction distinctness from the
global trace positions alone. -/
def singletonLogicalTrace :=
  (RMQ.SuccinctClassic.queryTraceResult ([7] : List Int) 0 1).trace

def singletonFirstSelectInstructionTrace :=
  match
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram[0]? with
  | some instr =>
      (instr.evalGlobalWordTrace (RMQ.Cartesian.shape ([7] : List Int)) 0 1
        RMQ.SuccinctFinal.WholeQueryState.empty).trace
  | none => []

def singletonAfterFirstSelectState :=
  (RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace
    (RMQ.Cartesian.shape ([7] : List Int)) 0 1
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram.take 1)
    RMQ.SuccinctFinal.WholeQueryState.empty).value

def singletonSecondSelectInstructionTrace :=
  match
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram[1]? with
  | some instr =>
      (instr.evalGlobalWordTrace (RMQ.Cartesian.shape ([7] : List Int)) 0 1
        singletonAfterFirstSelectState).trace
  | none => []

def singletonRepeatedEqualReadInstructionPositionsOK : Bool :=
  match
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram[0]?,
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram[1]? with
  | some firstInstr, some secondInstr =>
      firstInstr.reviewerReadLeaf? == some .selectClose &&
        secondInstr.reviewerReadLeaf? == some .selectClose &&
        (0 : Nat) != 1 &&
        singletonFirstSelectInstructionTrace.length == 15 &&
        singletonFirstSelectInstructionTrace[0]? == singletonLogicalTrace[0]? &&
        singletonSecondSelectInstructionTrace[0]? == singletonLogicalTrace[15]?
  | _, _ => false

def singletonRepeatedEqualReadPositionsOK : Bool :=
  (singletonLogicalTrace[0]?).isSome &&
    singletonLogicalTrace[0]? == singletonLogicalTrace[15]? &&
    (0 : Nat) != 15 &&
    singletonRepeatedEqualReadInstructionPositionsOK &&
    match singletonLogicalTrace[0]? with
    | some (RMQ.WordRAM.TraceEvent.readWord _ _ (some _)) => true
    | _ => false

#guard singletonRepeatedEqualReadPositionsOK

def physicalDependencyOK : Bool :=
  (RMQ.SuccinctClassic.reviewerPhysicalFootprint
      ([7] : List Int) 0 1).head?.isSome &&
    singletonDecisiveReadConsumedOK && singletonDecisiveStoreWordChangedOK &&
    singletonCanonicalPhysicalResult.value == some 0 &&
    singletonCorruptedPhysicalResult.value == none &&
    singletonIgnoreReturnedValueMutationResult.value == some 0 &&
    singletonCorruptedPhysicalResult.value !=
      singletonIgnoreReturnedValueMutationResult.value

def canonicalBoundOK : Bool :=
  RMQ.SuccinctClassic.queryCost == 207 &&
    RMQ.SuccinctClassic.canonicalSilentWordRankSelectQueryCost == 142 &&
    RMQ.SuccinctClassic.canonicalSilentFringeQueryCost == 76 &&
    RMQ.SuccinctClassic.canonicalTransitionalQueryCost == 328

def structuralEvidenceOK : Bool :=
  routeEvidenceOK && physicalErasureOK && physicalBackingOK &&
    physicalDependencyOK && singletonRepeatedEqualReadPositionsOK &&
    canonicalBoundOK

def mismatchMessage (mismatch : Mismatch) : String :=
  "mismatch: xs=" ++ reprStr mismatch.xs ++
    " window=[" ++ toString mismatch.left ++ ", " ++
      toString mismatch.right ++ ")" ++
    " got=" ++ reprStr mismatch.got ++
    " expected=" ++ reprStr mismatch.expected

def mainImpl : IO Unit := do
  match firstMismatch generatedInputs with
  | some mismatch =>
      IO.eprintln (mismatchMessage mismatch)
      IO.Process.exit 1
  | none =>
      if structuralEvidenceOK then
        IO.println
          ("validated " ++ toString totalWindowCount ++
            " SuccinctClassic valid/invalid query windows across " ++
            toString generatedInputs.length ++
            " deterministic inputs; canonical same/cross routes, principled 207 charged-trace bound, " ++
            "physical erasure/backing, and flat-store dependency checked")
      else
        IO.eprintln
          "canonical route, bound, physical erasure/backing, or dependency evidence failed"
        IO.Process.exit 1

end RMQ.Validation.SuccinctClassic

def main : IO Unit :=
  RMQ.Validation.SuccinctClassic.mainImpl

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

def physicalDependencyOK : Bool :=
  let xs : List Int := [7]
  let canonical :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs 0 1
  let corrupted :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore xs
      (dropFirstConsumedPhysicalWord xs 0 1) 0 1
  (RMQ.SuccinctClassic.reviewerPhysicalFootprint xs 0 1).head?.isSome &&
    canonical.value == some 0 && corrupted.value == none

def canonicalBoundOK : Bool :=
  RMQ.SuccinctClassic.queryCost == 328

def structuralEvidenceOK : Bool :=
  routeEvidenceOK && physicalErasureOK && physicalBackingOK &&
    physicalDependencyOK && canonicalBoundOK

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
            " deterministic inputs; canonical same/cross routes, 328 bound, " ++
            "physical erasure/backing, and flat-store dependency checked")
      else
        IO.eprintln
          "canonical route, bound, physical erasure/backing, or dependency evidence failed"
        IO.Process.exit 1

end RMQ.Validation.SuccinctClassic

def main : IO Unit :=
  RMQ.Validation.SuccinctClassic.mainImpl

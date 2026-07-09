import RMQ.Core.SuccinctRMQClassic

/-!
# Reviewer-facing executable cost report for SuccinctClassic

This executable runs the public list-facing succinct RMQ construction and
query path on deterministic fixtures.  It reports the modeled event cost stored
in `SuccinctClassic.queryCosted`; it is not a Lean runtime benchmark and is not
part of the theorem trust base.
-/

namespace RMQ.Validation.SuccinctClassicCostHarness

structure Window where
  left : Nat
  right : Nat
deriving Repr

structure Fixture where
  name : String
  xs : List Int
  windows : List Window
deriving Repr

def generatedInput (len seed : Nat) : List Int :=
  (List.range len).map fun i =>
    Int.ofNat ((seed * 11 + len * 7 + i * i + 3 * i) % 17) - 8

def zigZagInput (len : Nat) : List Int :=
  (List.range len).map fun i =>
    if i % 2 = 0 then
      Int.ofNat (len - i)
    else
      Int.ofNat i - Int.ofNat len

def expectedAnswer (xs : List Int) (left right : Nat) : Option Nat :=
  if left < right /\ right <= xs.length then
    some (RMQ.scanWindow xs left (right - left))
  else
    none

def routeKind (xs : List Int) : String :=
  let shape := RMQ.SuccinctClassic.cartesianShape xs
  if RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize shape = 0 then
    "zero-block"
  else if RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReady shape then
    "ready"
  else if RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    "active-not-ready"
  else
    "inactive-not-ready"

def boolString (b : Bool) : String :=
  if b then "true" else "false"

def windowLabel (window : Window) : String :=
  "[" ++ toString window.left ++ ", " ++ toString window.right ++ ")"

def reportWindow (xs : List Int) (window : Window) : IO Bool := do
  let query := RMQ.SuccinctClassic.queryCosted xs window.left window.right
  let expected := expectedAnswer xs window.left window.right
  let agrees := query.erase == expected
  IO.println
    ("  window=" ++ windowLabel window ++
      " answer=" ++ reprStr query.erase ++
      " expected=" ++ reprStr expected ++
      " agrees=" ++ boolString agrees ++
      " modeledTraceCost=" ++ toString query.cost)
  pure agrees

def reportWindows (xs : List Int) : List Window -> IO Bool
  | [] => pure true
  | window :: rest => do
      let okHere <- reportWindow xs window
      let okRest <- reportWindows xs rest
      pure (okHere && okRest)

def reportFixture (fixture : Fixture) : IO Bool := do
  let payloadBits := (RMQ.SuccinctClassic.buildPayload fixture.xs).length
  let shape := RMQ.SuccinctClassic.cartesianShape fixture.xs
  IO.println
    ("input=" ++ fixture.name ++
      " n=" ++ toString fixture.xs.length ++
      " shapeSize=" ++ toString shape.size ++
      " payloadBits=" ++ toString payloadBits ++
      " route=" ++ routeKind fixture.xs ++
      " routeSplitBound=" ++
        toString (RMQ.SuccinctClassic.routeSplitQueryCost fixture.xs) ++
      " cleanAllSizeBound=" ++ toString RMQ.SuccinctClassic.queryCost ++
      " readyThreshold=" ++
        toString RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold)
  reportWindows fixture.xs fixture.windows

def defaultFixtures : List Fixture :=
  [
    {
      name := "tiny-leftmost-ties",
      xs := [3, 1, 4, 1, 5],
      windows := [
        { left := 0, right := 5 },
        { left := 2, right := 4 }
      ]
    },
    {
      name := "tie-boundary",
      xs := [5, 4, 4, 6, 4, 7],
      windows := [
        { left := 0, right := 6 },
        { left := 1, right := 5 },
        { left := 2, right := 3 }
      ]
    },
    {
      name := "generated-64-route-split",
      xs := generatedInput 64 9,
      windows := [
        { left := 0, right := 64 },
        { left := 7, right := 39 },
        { left := 31, right := 32 }
      ]
    },
    {
      name := "zigzag-128-route-split",
      xs := zigZagInput 128,
      windows := [
        { left := 0, right := 128 },
        { left := 17, right := 97 },
        { left := 64, right := 65 }
      ]
    },
    {
      name := "generated-1024-route-split",
      xs := generatedInput 1024 13,
      windows := [
        { left := 0, right := 1024 },
        { left := 127, right := 640 },
        { left := 511, right := 512 }
      ]
    }
  ]

def reportFixtures : List Fixture -> IO Bool
  | [] => pure true
  | fixture :: rest => do
      let okHere <- reportFixture fixture
      let okRest <- reportFixtures rest
      pure (okHere && okRest)

def mainImpl : IO Unit := do
  IO.println "SuccinctClassic executable cost harness"
  IO.println
    "modeledTraceCost is queryCosted.cost, i.e. the checked WordRAM trace/event count; it is not wall-clock runtime."
  let ok <- reportFixtures defaultFixtures
  if ok then
    IO.println "all reported windows agree with reference List Int RMQ semantics"
  else
    IO.eprintln "at least one reported window disagreed with reference List Int RMQ semantics"
    IO.Process.exit 1

end RMQ.Validation.SuccinctClassicCostHarness

def main : IO Unit :=
  RMQ.Validation.SuccinctClassicCostHarness.mainImpl

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

def balancedInputCore : Nat -> Nat -> List Int
  | 0, _depth => []
  | len + 1, depth =>
      let leftLen := len / 2
      let rightLen := len - leftLen
      balancedInputCore leftLen (depth + 1) ++
        [Int.ofNat depth] ++
          balancedInputCore rightLen (depth + 1)
termination_by len _depth => len
decreasing_by
  all_goals omega

def balancedInput (len : Nat) : List Int :=
  balancedInputCore len 0

def expectedAnswer (xs : List Int) (left right : Nat) : Option Nat :=
  if left < right /\ right <= xs.length then
    some (RMQ.scanWindow xs left (right - left))
  else
    none

def routeKindOfShape (shape : RMQ.Cartesian.CartesianShape) : String :=
  if RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize shape = 0 then
    "zero-block"
  else if RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReady shape then
    "ready"
  else if RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    "active-not-ready"
  else
    "inactive-not-ready"

def routeKind (xs : List Int) : String :=
  routeKindOfShape (RMQ.SuccinctClassic.cartesianShape xs)

def preparedRouteKind
    (prepared : RMQ.SuccinctClassic.PreparedInput) : String :=
  routeKindOfShape prepared.shape

def boolString (b : Bool) : String :=
  if b then "true" else "false"

def appliesString (applies ok : Bool) : String :=
  if applies then boolString ok else "not-applicable"

def windowLabel (window : Window) : String :=
  "[" ++ toString window.left ++ ", " ++ toString window.right ++ ")"

def fastRegimeQueryCost : Nat :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost

def reportWindow
    (emitPhases : Bool) (prepared : RMQ.SuccinctClassic.PreparedInput)
    (routeBound : Nat)
    (fastRegimeApplies : Bool) (window : Window) : IO Bool := do
  if emitPhases then
    IO.println
      ("phase=queryCosted start window=" ++ windowLabel window ++
        " note=preparedQueryCosted reuses the prepared cartesianShape")
  let query :=
    RMQ.SuccinctClassic.preparedQueryCosted
      prepared window.left window.right
  if emitPhases then
    IO.println
      ("phase=queryCosted done window=" ++ windowLabel window ++
        " modeledTraceCost=" ++ toString query.cost)
  let expected := expectedAnswer prepared.xs window.left window.right
  let agrees := query.erase == expected
  let underRouteBound := query.cost <= routeBound
  let underFastRegimeBound := query.cost <= fastRegimeQueryCost
  IO.println
    ("  window=" ++ windowLabel window ++
      " answer=" ++ reprStr query.erase ++
      " expected=" ++ reprStr expected ++
      " agrees=" ++ boolString agrees ++
      " modeledTraceCost=" ++ toString query.cost ++
      " underRouteSplitBound=" ++ boolString underRouteBound ++
      " underFastRegimeBound=" ++
        appliesString fastRegimeApplies underFastRegimeBound)
  pure agrees

def reportWindows
    (emitPhases : Bool) (prepared : RMQ.SuccinctClassic.PreparedInput)
    (routeBound : Nat)
    (fastRegimeApplies : Bool) : List Window -> IO Bool
  | [] => pure true
  | window :: rest => do
      let okHere <-
        reportWindow emitPhases prepared routeBound fastRegimeApplies window
      let okRest <-
        reportWindows emitPhases prepared routeBound fastRegimeApplies rest
      pure (okHere && okRest)

def reportFixture (emitPhases : Bool) (fixture : Fixture) : IO Bool := do
  if emitPhases then
    IO.println
      ("phase=shapeMetadata start input=" ++ fixture.name ++
        " note=prepareInput uses theorem-backed stackCartesianShape once")
  let prepared := RMQ.SuccinctClassic.prepareInput fixture.xs
  let shape := prepared.shape
  if emitPhases then
    IO.println
      ("phase=shapeMetadata done input=" ++ fixture.name ++
        " shapeSize=" ++ toString shape.size ++
        " bpCodeLength=" ++ toString shape.bpCode.length ++
        " preparedArrayValues=" ++ toString prepared.values.size)
  if emitPhases then
    IO.println
      ("phase=buildPayload start input=" ++ fixture.name ++
        " note=preparedBuildPayload reuses the prepared cartesianShape")
  let payloadBits :=
    (RMQ.SuccinctClassic.preparedBuildPayload prepared).length
  if emitPhases then
    IO.println
      ("phase=buildPayload done input=" ++ fixture.name ++
        " payloadBits=" ++ toString payloadBits)
  let routeBound := RMQ.SuccinctClassic.preparedRouteSplitQueryCost prepared
  let fastRegimeApplies :=
    RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= shape.size
  IO.println
    ("input=" ++ fixture.name ++
      " n=" ++ toString fixture.xs.length ++
      " shapeSize=" ++ toString shape.size ++
      " payloadBits=" ++ toString payloadBits ++
      " preparedArrayValues=" ++ toString prepared.values.size ++
      " route=" ++ preparedRouteKind prepared ++
      " routeSplitBound=" ++
        toString routeBound ++
      " cleanAllSizeBound=" ++ toString RMQ.SuccinctClassic.queryCost ++
      " fastRegimeBound=" ++ toString fastRegimeQueryCost ++
      " fastRegimeApplies=" ++ boolString fastRegimeApplies ++
      " readyThreshold=" ++
        toString RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold)
  reportWindows emitPhases prepared routeBound fastRegimeApplies
    fixture.windows

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

def profileFixture (n : Nat) : Fixture :=
  {
    name := "balanced-profile-" ++ toString n,
    xs := balancedInput n,
    windows := [
      { left := 0, right := n },
      { left := n / 3, right := (2 * n) / 3 },
      { left := n / 2, right := n / 2 + 1 }
    ]
  }

def reportFixtures : List Fixture -> IO Bool
  | [] => pure true
  | fixture :: rest => do
      let okHere <- reportFixture false fixture
      let okRest <- reportFixtures rest
      pure (okHere && okRest)

def usage : String :=
  "usage:\n" ++
  "  lake exe rmq_succinct_classic_cost_harness\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --profile-size N\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --shape-profile-size N\n\n" ++
  "--profile-size N runs one deterministic balanced fixture through the " ++
  "theorem-backed prepared buildPayload/queryCosted mirror with phase markers. " ++
  "--shape-profile-size N runs only prepared shape construction for bottleneck " ++
  "diagnosis. Use N=32768 only as an opt-in ready-threshold profiling run."

def runDefault : IO Unit := do
  IO.println "SuccinctClassic executable cost harness"
  IO.println
    "modeledTraceCost is preparedQueryCosted.cost, theorem-equal to queryCosted.cost; it is not wall-clock runtime."
  let ok <- reportFixtures defaultFixtures
  if ok then
    IO.println "all reported windows agree with reference List Int RMQ semantics"
  else
    IO.eprintln "at least one reported window disagreed with reference List Int RMQ semantics"
    IO.Process.exit 1

def runProfileSize (n : Nat) : IO Unit := do
  IO.println "SuccinctClassic executable construction/profile mode"
  IO.println
    "This mode reports phase markers for the theorem-backed prepared mirror; wall-clock timing is external runtime evidence, not a model-cost theorem."
  IO.println
    ("requestedSize=" ++ toString n ++
      " readyThreshold=" ++
        toString RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold ++
      " thresholdRun=" ++
        boolString
          (RMQ.SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <= n))
  let fixture := profileFixture n
  let ok <- reportFixture true fixture
  if ok then
    IO.println "profiled windows agree with reference List Int RMQ semantics"
  else
    IO.eprintln "at least one profiled window disagreed with reference List Int RMQ semantics"
    IO.Process.exit 1

def runShapeProfileSize (n : Nat) : IO Unit := do
  IO.println "SuccinctClassic executable shape-construction profile mode"
  IO.println
    "This mode runs prepareInput only; wall-clock timing is external runtime evidence, not a model-cost theorem."
  let fixture := profileFixture n
  let prepared := RMQ.SuccinctClassic.prepareInput fixture.xs
  IO.println
    ("input=" ++ fixture.name ++
      " n=" ++ toString fixture.xs.length ++
      " shapeSize=" ++ toString prepared.shape.size ++
      " bpCodeLength=" ++ toString prepared.shape.bpCode.length ++
      " preparedArrayValues=" ++ toString prepared.values.size ++
      " route=" ++ preparedRouteKind prepared)

def normalizeArgs : List String -> List String
  | "--" :: rest => rest
  | args => args

def mainImpl (args : List String) : IO Unit := do
  match normalizeArgs args with
  | [] => runDefault
  | ["--help"] => IO.println usage
  | ["--profile-size", nText] =>
      match nText.toNat? with
      | some n => runProfileSize n
      | none =>
          IO.eprintln ("invalid --profile-size value: " ++ nText)
          IO.eprintln usage
          IO.Process.exit 2
  | ["--shape-profile-size", nText] =>
      match nText.toNat? with
      | some n => runShapeProfileSize n
      | none =>
          IO.eprintln ("invalid --shape-profile-size value: " ++ nText)
          IO.eprintln usage
          IO.Process.exit 2
  | _ =>
      IO.eprintln usage
      IO.Process.exit 2

end RMQ.Validation.SuccinctClassicCostHarness

def main (args : List String) : IO Unit :=
  RMQ.Validation.SuccinctClassicCostHarness.mainImpl args

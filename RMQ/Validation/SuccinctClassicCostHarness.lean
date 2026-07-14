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

/-- The only live canonical query-route classification. -/
inductive CanonicalQueryRoute where
  | invalid
  | sameBlock
  | crossBlock
deriving Repr, DecidableEq, BEq

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
  if RMQ.ValidRange xs left right then
    some (RMQ.scanWindow xs left (right - left))
  else
    none

def canonicalQueryRoute
    (prepared : RMQ.SuccinctClassic.PreparedInput)
    (window : Window) : CanonicalQueryRoute :=
  if _hvalid : RMQ.ValidRange prepared.xs window.left window.right then
    match RMQ.SuccinctSpace.bpCloseOfInorder? prepared.shape window.left,
        RMQ.SuccinctSpace.bpCloseOfInorder?
          prepared.shape (window.right - 1) with
    | some leftClose, some rightClose =>
        let blockSize :=
          RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
            prepared.shape
        if RMQ.SuccinctClose.blockOfClose blockSize leftClose =
            RMQ.SuccinctClose.blockOfClose blockSize rightClose then
          .sameBlock
        else
          .crossBlock
    | _, _ => .invalid
  else
    .invalid

def canonicalQueryRouteString : CanonicalQueryRoute -> String
  | .invalid => "invalid"
  | .sameBlock => "sameBlock"
  | .crossBlock => "crossBlock"

def boolString (b : Bool) : String :=
  if b then "true" else "false"

def windowLabel (window : Window) : String :=
  "[" ++ toString window.left ++ ", " ++ toString window.right ++ ")"

def reportWindow
    (emitPhases : Bool) (prepared : RMQ.SuccinctClassic.PreparedInput)
    (window : Window) : IO Bool := do
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
  let route := canonicalQueryRoute prepared window
  let routeAgrees :=
    match route, expected with
    | .invalid, none => true
    | .sameBlock, some _ => true
    | .crossBlock, some _ => true
    | _, _ => false
  let canonicalBoundIs76 := RMQ.SuccinctClassic.queryCost == 76
  let underCanonicalBound := query.cost <= RMQ.SuccinctClassic.queryCost
  IO.println
    ("  window=" ++ windowLabel window ++
      " answer=" ++ reprStr query.erase ++
      " expected=" ++ reprStr expected ++
      " agrees=" ++ boolString agrees ++
      " canonicalRoute=" ++ canonicalQueryRouteString route ++
      " routeAgrees=" ++ boolString routeAgrees ++
      " modeledTraceCost=" ++ toString query.cost ++
      " canonicalBound=" ++ toString RMQ.SuccinctClassic.queryCost ++
      " canonicalBoundIs76=" ++ boolString canonicalBoundIs76 ++
      " underCanonicalBound=" ++ boolString underCanonicalBound)
  pure (agrees && routeAgrees && canonicalBoundIs76 && underCanonicalBound)

def reportWindows
    (emitPhases : Bool)
    (prepared : RMQ.SuccinctClassic.PreparedInput) : List Window -> IO Bool
  | [] => pure true
  | window :: rest => do
      let okHere <-
        reportWindow emitPhases prepared window
      let okRest <-
        reportWindows emitPhases prepared rest
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
  IO.println
    ("input=" ++ fixture.name ++
      " n=" ++ toString fixture.xs.length ++
      " shapeSize=" ++ toString shape.size ++
      " payloadBits=" ++ toString payloadBits ++
      " preparedArrayValues=" ++ toString prepared.values.size ++
      " canonicalQueryBound=" ++ toString RMQ.SuccinctClassic.queryCost)
  reportWindows emitPhases prepared fixture.windows

def defaultFixtures : List Fixture :=
  [
    {
      name := "tiny-leftmost-ties",
      xs := [3, 1, 4, 1, 5],
      windows := [
        { left := 0, right := 5 },
        { left := 2, right := 4 },
        { left := 1, right := 1 },
        { left := 2, right := 1 },
        { left := 0, right := 6 }
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
      name := "generated-64-canonical",
      xs := generatedInput 64 9,
      windows := [
        { left := 0, right := 64 },
        { left := 7, right := 39 },
        { left := 31, right := 32 }
      ]
    },
    {
      name := "zigzag-128-canonical",
      xs := zigZagInput 128,
      windows := [
        { left := 0, right := 128 },
        { left := 17, right := 97 },
        { left := 64, right := 65 }
      ]
    },
    {
      name := "generated-128-canonical-alternate",
      xs := generatedInput 128 13,
      windows := [
        { left := 0, right := 128 },
        { left := 15, right := 96 },
        { left := 63, right := 64 }
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
  "diagnosis."

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
  IO.println ("requestedSize=" ++ toString n)
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
      " preparedArrayValues=" ++ toString prepared.values.size)

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

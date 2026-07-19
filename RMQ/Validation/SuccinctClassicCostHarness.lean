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

inductive FixtureId where
  | tinyLeftmostTies
  | tieBoundary
  | tieBoundaryLiveInterior
  | generated64
  | zigzag128
  | generated128Alternate
deriving Repr, DecidableEq, BEq

inductive CostDisposition where
  | unchangedInvalid
  | unchangedSameBlock
  | unchangedNoInterior
  | chargedSparseLevel
deriving Repr, DecidableEq, BEq

/-- One exact replay contract.  In addition to the current executable facts,
`preRepairCost` pins the observed pre-swap comparison datum and `disposition`
states why equality or a charged increase is expected. -/
structure ReplayCase where
  id : String
  fixture : FixtureId
  window : Window
  answer : Option Nat
  route : CanonicalQueryRoute
  preRepairCost : Nat
  postRepairCost : Nat
  disposition : CostDisposition
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
  let canonicalBoundIs210 := RMQ.SuccinctClassic.queryCost == 210
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
      " canonicalBoundIs210=" ++ boolString canonicalBoundIs210 ++
      " underCanonicalBound=" ++ boolString underCanonicalBound)
  pure (agrees && routeAgrees && canonicalBoundIs210 && underCanonicalBound)

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
    -- Tie-boundary coverage with a LIVE interior.
    --
    -- The fixture above has `shape.size = 6`, hence
    -- `canonicalBPRelativeSummaryBase = Nat.log2 6 + 1 = 3` and
    -- `canonicalBPRelativeSummaryBlockCountRaw = 6 / 3 = 2`.  With only two
    -- blocks a crossBlock query has no block STRICTLY between its endpoint
    -- blocks, so `canonicalCrossBlockCloseCostedWithRankSeed`
    -- (`RelativeRmmMacro/ConcreteDirectoryRAM.lean:2336-2340`) takes its
    -- `Costed.pure none` branch and the interior range-min is never entered.
    -- That fixture therefore exercises leftmost tie-breaking on the FRINGE
    -- decoders only; it is kept because the zero-interior path is real
    -- coverage, but on its own it leaves tie-breaking with a participating
    -- interior untested.
    --
    -- This fixture closes that gap.  `shape.size = 24` gives `base = 5`,
    -- `blockSize = 10`, `blockCountRaw = 4`, and the windows below invoke the
    -- interior with `count = 3`, `2` and `1` respectively, plus one
    -- `count = 0` sameBlock control.  The values are chosen so the minimum
    -- (`4`) occurs ONLY at indices 5, 7, 9, 11, 13, 16 and 18 -- every one of
    -- them inside an interior block for the full window -- while the two
    -- fringe blocks (indices 0-3 and 19-23) carry no minimum at all.  The
    -- leftmost-tie answer for `[0, 24)` is therefore produced by the interior
    -- range-min breaking ties ACROSS blocks 1, 2 and 3, not by either fringe.
    {
      name := "tie-boundary-live-interior",
      xs := [9, 8, 9, 7, 9,
             4, 6, 4, 9, 4,
             8, 4, 9, 4, 6,
             8, 4, 9, 4, 8,
             9, 7, 9, 8],
      windows := [
        { left := 0, right := 24 },
        { left := 4, right := 20 },
        { left := 10, right := 20 },
        { left := 11, right := 12 }
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

def fixtureName : FixtureId -> String
  | .tinyLeftmostTies => "tiny-leftmost-ties"
  | .tieBoundary => "tie-boundary"
  | .tieBoundaryLiveInterior => "tie-boundary-live-interior"
  | .generated64 => "generated-64-canonical"
  | .zigzag128 => "zigzag-128-canonical"
  | .generated128Alternate => "generated-128-canonical-alternate"

def fixtureInput : FixtureId -> List Int
  | .tinyLeftmostTies => [3, 1, 4, 1, 5]
  | .tieBoundary => [5, 4, 4, 6, 4, 7]
  | .tieBoundaryLiveInterior =>
      [9, 8, 9, 7, 9,
       4, 6, 4, 9, 4,
       8, 4, 9, 4, 6,
       8, 4, 9, 4, 8,
       9, 7, 9, 8]
  | .generated64 => generatedInput 64 9
  | .zigzag128 => zigZagInput 128
  | .generated128Alternate => generatedInput 128 13

/-- Canonical B7 replay registry, in its required execution order. -/
def replayRegistry : List ReplayCase :=
  [
    { id := "tiny-full-leftmost", fixture := .tinyLeftmostTies,
      window := { left := 0, right := 5 }, answer := some 1,
      route := .crossBlock, preRepairCost := 68, postRepairCost := 68,
      disposition := .unchangedNoInterior },
    { id := "tiny-sameblock-tie", fixture := .tinyLeftmostTies,
      window := { left := 2, right := 4 }, answer := some 3,
      route := .sameBlock, preRepairCost := 57, postRepairCost := 57,
      disposition := .unchangedSameBlock },
    { id := "tiny-empty", fixture := .tinyLeftmostTies,
      window := { left := 1, right := 1 }, answer := none,
      route := .invalid, preRepairCost := 0, postRepairCost := 0,
      disposition := .unchangedInvalid },
    { id := "tiny-reversed", fixture := .tinyLeftmostTies,
      window := { left := 2, right := 1 }, answer := none,
      route := .invalid, preRepairCost := 0, postRepairCost := 0,
      disposition := .unchangedInvalid },
    { id := "tiny-out-of-bounds", fixture := .tinyLeftmostTies,
      window := { left := 0, right := 6 }, answer := none,
      route := .invalid, preRepairCost := 0, postRepairCost := 0,
      disposition := .unchangedInvalid },
    { id := "tie-full-leftmost", fixture := .tieBoundary,
      window := { left := 0, right := 6 }, answer := some 1,
      route := .crossBlock, preRepairCost := 76, postRepairCost := 76,
      disposition := .unchangedNoInterior },
    { id := "tie-subwindow-leftmost", fixture := .tieBoundary,
      window := { left := 1, right := 5 }, answer := some 1,
      route := .crossBlock, preRepairCost := 72, postRepairCost := 72,
      disposition := .unchangedNoInterior },
    { id := "tie-singleton", fixture := .tieBoundary,
      window := { left := 2, right := 3 }, answer := some 2,
      route := .sameBlock, preRepairCost := 54, postRepairCost := 54,
      disposition := .unchangedSameBlock },
    { id := "interior-full-leftmost", fixture := .tieBoundaryLiveInterior,
      window := { left := 0, right := 24 }, answer := some 5,
      route := .crossBlock, preRepairCost := 112, postRepairCost := 114,
      disposition := .chargedSparseLevel },
    { id := "interior-cropped-leftmost", fixture := .tieBoundaryLiveInterior,
      window := { left := 4, right := 20 }, answer := some 5,
      route := .crossBlock, preRepairCost := 107, postRepairCost := 109,
      disposition := .chargedSparseLevel },
    { id := "interior-tail-leftmost", fixture := .tieBoundaryLiveInterior,
      window := { left := 10, right := 20 }, answer := some 11,
      route := .crossBlock, preRepairCost := 105, postRepairCost := 107,
      disposition := .chargedSparseLevel },
    { id := "interior-singleton", fixture := .tieBoundaryLiveInterior,
      window := { left := 11, right := 12 }, answer := some 11,
      route := .sameBlock, preRepairCost := 73, postRepairCost := 73,
      disposition := .unchangedSameBlock },
    { id := "generated64-full", fixture := .generated64,
      window := { left := 0, right := 64 }, answer := some 15,
      route := .crossBlock, preRepairCost := 116, postRepairCost := 118,
      disposition := .chargedSparseLevel },
    { id := "generated64-subwindow", fixture := .generated64,
      window := { left := 7, right := 39 }, answer := some 15,
      route := .crossBlock, preRepairCost := 126, postRepairCost := 128,
      disposition := .chargedSparseLevel },
    { id := "generated64-singleton", fixture := .generated64,
      window := { left := 31, right := 32 }, answer := some 31,
      route := .sameBlock, preRepairCost := 62, postRepairCost := 62,
      disposition := .unchangedSameBlock },
    { id := "zigzag128-full", fixture := .zigzag128,
      window := { left := 0, right := 128 }, answer := some 1,
      route := .crossBlock, preRepairCost := 92, postRepairCost := 93,
      disposition := .chargedSparseLevel },
    { id := "zigzag128-subwindow", fixture := .zigzag128,
      window := { left := 17, right := 97 }, answer := some 17,
      route := .crossBlock, preRepairCost := 96, postRepairCost := 97,
      disposition := .chargedSparseLevel },
    { id := "zigzag128-singleton", fixture := .zigzag128,
      window := { left := 64, right := 65 }, answer := some 64,
      route := .sameBlock, preRepairCost := 57, postRepairCost := 57,
      disposition := .unchangedSameBlock },
    { id := "generated128-full", fixture := .generated128Alternate,
      window := { left := 0, right := 128 }, answer := some 15,
      route := .crossBlock, preRepairCost := 93, postRepairCost := 94,
      disposition := .chargedSparseLevel },
    { id := "generated128-subwindow", fixture := .generated128Alternate,
      window := { left := 15, right := 96 }, answer := some 15,
      route := .crossBlock, preRepairCost := 95, postRepairCost := 96,
      disposition := .chargedSparseLevel },
    { id := "generated128-singleton", fixture := .generated128Alternate,
      window := { left := 63, right := 64 }, answer := some 63,
      route := .sameBlock, preRepairCost := 57, postRepairCost := 57,
      disposition := .unchangedSameBlock }
  ]

def expectedRegistryIds : List String :=
  ["tiny-full-leftmost", "tiny-sameblock-tie", "tiny-empty",
   "tiny-reversed", "tiny-out-of-bounds", "tie-full-leftmost",
   "tie-subwindow-leftmost", "tie-singleton", "interior-full-leftmost",
   "interior-cropped-leftmost", "interior-tail-leftmost",
   "interior-singleton", "generated64-full", "generated64-subwindow",
   "generated64-singleton", "zigzag128-full", "zigzag128-subwindow",
   "zigzag128-singleton", "generated128-full",
   "generated128-subwindow", "generated128-singleton"]

def expectedPreRepairCosts : List Nat :=
  [68, 57, 0, 0, 0, 76, 72, 54, 112, 107, 105, 73, 116, 126, 62,
   92, 96, 57, 93, 95, 57]

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

def replayDispositionOK (entry : ReplayCase) : Bool :=
  match entry.disposition with
  | .unchangedInvalid =>
      entry.route == .invalid && entry.answer == none &&
        entry.preRepairCost == 0 && entry.postRepairCost == 0
  | .unchangedSameBlock =>
      entry.route == .sameBlock &&
        entry.preRepairCost == entry.postRepairCost
  | .unchangedNoInterior =>
      entry.route == .crossBlock &&
        entry.preRepairCost == entry.postRepairCost
  | .chargedSparseLevel =>
      entry.route == .crossBlock &&
        decide (entry.preRepairCost < entry.postRepairCost)

/-- Structural anti-vacuity check for the single ordered registry.  Exact ID
equality rejects missing, extra, or reordered cases; the explicit de-dup check
rejects duplicates; the second pinned vector protects the historical pre-cost
field, which cannot be recomputed on the repaired tree. -/
def replayRegistryStructureOK : Bool :=
  let ids := replayRegistry.map (fun entry => entry.id)
  replayRegistry.length == 21 &&
    ids == expectedRegistryIds &&
    ids.eraseDups.length == 21 &&
    replayRegistry.map (fun entry => entry.preRepairCost) ==
      expectedPreRepairCosts &&
    replayRegistry.all replayDispositionOK

def reportReplayCase
    (prepared : RMQ.SuccinctClassic.PreparedInput)
    (entry : ReplayCase) : IO Bool := do
  let xs := prepared.xs
  let query :=
    RMQ.SuccinctClassic.preparedQueryCosted
      prepared entry.window.left entry.window.right
  let reference := expectedAnswer xs entry.window.left entry.window.right
  let route := canonicalQueryRoute prepared entry.window
  let answerOK := query.erase == entry.answer
  let referenceOK := reference == entry.answer
  let routeOK := route == entry.route
  let postCostOK := query.cost == entry.postRepairCost
  let boundOK :=
    RMQ.SuccinctClassic.queryCost == 210 &&
      decide (query.cost <= RMQ.SuccinctClassic.queryCost)
  let dispositionOK := replayDispositionOK entry
  IO.println
    ("case=" ++ entry.id ++
      " fixture=" ++ fixtureName entry.fixture ++
      " window=" ++ windowLabel entry.window ++
      " answer=" ++ reprStr query.erase ++
      " expectedAnswer=" ++ reprStr entry.answer ++
      " referenceAnswer=" ++ reprStr reference ++
      " route=" ++ canonicalQueryRouteString route ++
      " expectedRoute=" ++ canonicalQueryRouteString entry.route ++
      " preRepairCost=" ++ toString entry.preRepairCost ++
      " postRepairCost=" ++ toString query.cost ++
      " expectedPostRepairCost=" ++ toString entry.postRepairCost ++
      " disposition=" ++ reprStr entry.disposition ++
      " answerOK=" ++ boolString answerOK ++
      " referenceOK=" ++ boolString referenceOK ++
      " routeOK=" ++ boolString routeOK ++
      " postCostOK=" ++ boolString postCostOK ++
      " dispositionOK=" ++ boolString dispositionOK ++
      " boundOK=" ++ boolString boundOK)
  pure
    (answerOK && referenceOK && routeOK && postCostOK &&
      dispositionOK && boundOK)

abbrev ReplayPreparedCache :=
  List (FixtureId × RMQ.SuccinctClassic.PreparedInput)

structure ReplayRunResult where
  ok : Bool
  count : Nat
  preparedCache : ReplayPreparedCache

def findReplayPrepared
    (fixture : FixtureId) : ReplayPreparedCache ->
      Option RMQ.SuccinctClassic.PreparedInput
  | [] => none
  | (cachedFixture, prepared) :: rest =>
      if cachedFixture == fixture then
        some prepared
      else
        findReplayPrepared fixture rest

/-- Reuse the theorem-backed prepared input across adjacent registry entries
for the same typed fixture.  The registry remains the sole execution order;
this cache removes only repeated pure construction work. -/
def getReplayPrepared
    (cache : ReplayPreparedCache) (fixture : FixtureId) :
      RMQ.SuccinctClassic.PreparedInput × ReplayPreparedCache :=
  match findReplayPrepared fixture cache with
  | some prepared => (prepared, cache)
  | none =>
      let prepared :=
        RMQ.SuccinctClassic.prepareInput (fixtureInput fixture)
      (prepared, (fixture, prepared) :: cache)

def reportReplayCasesCached
    (cache : ReplayPreparedCache) : List ReplayCase -> IO ReplayRunResult
  | [] => pure { ok := true, count := 0, preparedCache := cache }
  | entry :: rest => do
      let preparedAndCache := getReplayPrepared cache entry.fixture
      let okHere <- reportReplayCase preparedAndCache.1 entry
      let result <- reportReplayCasesCached preparedAndCache.2 rest
      pure {
        ok := okHere && result.ok
        count := result.count + 1
        preparedCache := result.preparedCache
      }

def reportReplayCases (entries : List ReplayCase) : IO ReplayRunResult :=
  reportReplayCasesCached [] entries

def runReplaySelection (selector : String) (selected : List ReplayCase) : IO Unit := do
  if !replayRegistryStructureOK then
    IO.eprintln
      "replay registry invalid: expected exactly 21 ordered unique stable IDs and pinned pre-costs"
    IO.Process.exit 3
  else if selected.isEmpty then
    IO.eprintln ("selector matched zero cases: " ++ selector)
    IO.Process.exit 4
  else
    let result <- reportReplayCases selected
    let exactCount := result.count == selected.length
    let expectedPreparedCount :=
      (selected.map (fun entry => entry.fixture)).eraseDups.length
    let exactPreparedCount :=
      result.preparedCache.length == expectedPreparedCount
    IO.println
      ("selector=" ++ selector ++
        " selectedCases=" ++ toString selected.length ++
        " executedCases=" ++ toString result.count ++
        " exactExecutionCount=" ++ boolString exactCount ++
        " preparedFixtures=" ++ toString result.preparedCache.length ++
        " expectedPreparedFixtures=" ++ toString expectedPreparedCount ++
        " exactPreparedFixtureCount=" ++ boolString exactPreparedCount)
    if result.ok && exactCount && exactPreparedCount then
      IO.println "all selected replay cases matched the exact registry"
    else
      IO.eprintln "at least one selected replay case violated the exact registry"
      IO.Process.exit 1

def usage : String :=
  "usage:\n" ++
  "  lake exe rmq_succinct_classic_cost_harness\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --case ID\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --fixture NAME\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --profile-size N\n" ++
  "  lake exe rmq_succinct_classic_cost_harness -- --shape-profile-size N\n\n" ++
  "Default mode executes the exact 21-case registry in order. --case must " ++
  "select exactly one stable ID; --fixture rejects a zero-match selection. " ++
  "--profile-size N runs one deterministic balanced fixture through the " ++
  "theorem-backed prepared buildPayload/queryCosted mirror with phase markers. " ++
  "--shape-profile-size N runs only prepared shape construction for bottleneck " ++
  "diagnosis."

def runDefault : IO Unit := do
  IO.println "SuccinctClassic exact 21-case replay harness"
  IO.println
    "modeledTraceCost is preparedQueryCosted.cost, theorem-equal to queryCosted.cost; it is not wall-clock runtime."
  runReplaySelection "default-registry" replayRegistry

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
  | ["--case", id] =>
      match replayRegistry.filter (fun entry => entry.id == id) with
      | [entry] => runReplaySelection ("case:" ++ id) [entry]
      | [] =>
          IO.eprintln ("unknown case id: " ++ id)
          IO.Process.exit 4
      | _ =>
          IO.eprintln ("duplicate case id in registry: " ++ id)
          IO.Process.exit 3
  | ["--fixture", name] =>
      runReplaySelection ("fixture:" ++ name)
        (replayRegistry.filter fun entry => fixtureName entry.fixture == name)
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

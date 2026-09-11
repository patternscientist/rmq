import RMQ.Core.WordRAM.Packed.QueryObservations
import RMQ.Core.WordRAM.Packed.ArrayRun

/-! Deterministic execution checks for the new numeric-memory primitive run.
Expected indices are literal fixture data. Universal route coverage is supplied
by the proofs; these small executions are regression and dependency checks.

Fixtures execute `runArray` on `queryProgram.toArray`, which `runArray_toArray`
proves equal to `run` on the list program; two fixtures are also executed by
`run` itself and compared on every observation. Route assertions are computed
from the input's Cartesian shape and the RC6 reference trace, never from the
machine. The negative control N01 carries a deliberately wrong expected answer,
runs only when selected explicitly, and must fail with a result mismatch. -/

namespace RMQ.Validation.PackedQueryRuntime

open RMQ.SuccinctFinal.PackedWordRAM

inductive CheckKind where
  | machine | outer | corruptMetadata | unreadReplacement
deriving BEq

/-- Expected route of a query through the RC6 close/LCA controller. -/
inductive Route where
  | unchecked
  /-- Rejected before any logical read: the reference trace is empty. -/
  | rejected
  /-- Both endpoint closes lie in one summary block; no interior read. -/
  | sameBlock
  /-- Endpoint closes in adjacent summary blocks; no interior read. -/
  | adjacentBlocks
  /-- Endpoint closes in different blocks with segment-20 interior reads. -/
  | crossBlockInterior
deriving BEq

def Route.name : Route → String
  | .unchecked => "unchecked"
  | .rejected => "rejected"
  | .sameBlock => "same-block"
  | .adjacentBlocks => "adjacent-blocks"
  | .crossBlockInterior => "cross-block-interior"

structure Fixture where
  id : String
  xs : List Int
  left : Nat
  right : Nat
  expected : Option Nat
  kind : CheckKind := .machine
  route : Route := .unchecked

/-- The closes of these twelve elements span three summary blocks of the
balanced-parenthesis code; the minimum 2 occurs at index 5, whose close lies in
the second block, and again at index 9, in the third. -/
def crossBlockInput : List Int := [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

def fixtures : List Fixture := [
  ⟨"S01-EMPTY", [], 0, 0, none, .machine, .unchecked⟩,
  ⟨"S02-SINGLE", [7], 0, 1, some 0, .machine, .unchecked⟩,
  ⟨"S03-LEFTMOST-TIE", [4, -3, -3, 8], 0, 4, some 1, .machine, .unchecked⟩,
  ⟨"S04-SLICE", [4, -3, -3, 8], 2, 4, some 2, .machine, .unchecked⟩,
  ⟨"S05-REVERSED", [4, -3, -3, 8], 3, 1, none, .machine, .unchecked⟩,
  ⟨"S06-OUT-OF-RANGE", [4, -3, -3, 8], 0, 5, none, .machine, .unchecked⟩,
  ⟨"S07-WORD-MAX", [4, -3, -3, 8], 2 ^ wordWidth 4 - 1, 2 ^ wordWidth 4 - 1, none, .machine,
    .unchecked⟩,
  ⟨"S08-OUTER-CAPACITY", [4, -3, -3, 8], 2 ^ wordWidth 4, 2 ^ wordWidth 4, none, .outer,
    .unchecked⟩,
  ⟨"S09-LONG-INTERVAL", (List.range 24).map Int.ofNat, 0, 24, some 0, .machine, .unchecked⟩,
  ⟨"S10-CORRUPT-METADATA", [7], 0, 1, some 0, .corruptMetadata, .unchecked⟩,
  ⟨"S11-UNREAD-REPLACEMENT", (List.range 24).map Int.ofNat, 0, 1, some 0, .unreadReplacement,
    .unchecked⟩,
  ⟨"S12-EMPTY-INTERVAL", [4, -3, -3, 8], 2, 2, none, .machine, .rejected⟩,
  ⟨"S13-CROSS-BLOCK", crossBlockInput, 1, 11, some 5, .machine, .crossBlockInterior⟩,
  ⟨"S14-SAME-BLOCK", crossBlockInput, 6, 10, some 9, .machine, .sameBlock⟩,
  ⟨"S15-ADJACENT-BLOCKS", crossBlockInput, 4, 8, some 5, .machine, .adjacentBlocks⟩]

def requiredIDs : List String := [
  "S01-EMPTY", "S02-SINGLE", "S03-LEFTMOST-TIE", "S04-SLICE", "S05-REVERSED",
  "S06-OUT-OF-RANGE", "S07-WORD-MAX", "S08-OUTER-CAPACITY", "S09-LONG-INTERVAL",
  "S10-CORRUPT-METADATA", "S11-UNREAD-REPLACEMENT", "S12-EMPTY-INTERVAL",
  "S13-CROSS-BLOCK", "S14-SAME-BLOCK", "S15-ADJACENT-BLOCKS"]

/-- The true leftmost minimum of `[4, -3, -3, 8]` is index 1, not 2. -/
def negativeFixtures : List Fixture := [
  ⟨"N01-WRONG-EXPECTED", [4, -3, -3, 8], 0, 4, some 2, .machine, .unchecked⟩]

def negativeIDs : List String := ["N01-WRONG-EXPECTED"]

/-- These fixtures are also executed by `run` on the list program. -/
def listRunIDs : List String := ["S02-SINGLE", "S05-REVERSED"]

def selectorVariable : String := "PQ1_RUNTIME_SELECTOR"

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def expectedPacket (expected : Option Nat) : Nat :=
  match expected with | none => 0 | some index => index + 1

def specAnswer (xs : List Int) (left right : Nat) : Option Nat :=
  if left < right ∧ right ≤ xs.length then some (RMQ.scanWindow xs left (right - left)) else none

def interiorReads (trace : List RMQ.WordRAM.TraceEvent) : Nat :=
  trace.countP fun event => match event with
    | .readWord 20 _ _ => true
    | _ => false

/-- Summary blocks of the two endpoint closes, as the RC6 controller compares
them, computed from the Cartesian shape alone. -/
def endpointBlocks (xs : List Int) (left right : Nat) : Option (Nat × Nat) :=
  let shape := RMQ.SuccinctClassic.cartesianShape xs
  let blockSize := RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  match RMQ.SuccinctSpace.bpCloseOfInorder? shape left,
      RMQ.SuccinctSpace.bpCloseOfInorder? shape (right - 1) with
  | some leftClose, some rightClose =>
      some (RMQ.SuccinctClose.blockOfClose blockSize leftClose,
        RMQ.SuccinctClose.blockOfClose blockSize rightClose)
  | _, _ => none

def checkRoute (fixture : Fixture) : IO String := do
  if fixture.route == .unchecked then return ""
  let reference := RMQ.SuccinctClassic.queryTraceResult fixture.xs fixture.left fixture.right
  check (reference.value == fixture.expected) (fixture.id ++ ": reference answer mismatch")
  let reads := interiorReads reference.trace
  let blocks := endpointBlocks fixture.xs fixture.left fixture.right
  let ok := match fixture.route, blocks with
    | .rejected, _ => reference.trace.isEmpty
    | .sameBlock, some (l, r) => l == r && reads == 0
    | .adjacentBlocks, some (l, r) => l + 1 == r && reads == 0
    | .crossBlockInterior, some (l, r) => l + 1 < r && reads > 0
    | _, _ => false
  check ok (fixture.id ++ ": route assertion failed")
  return " route=" ++ fixture.route.name ++ " interiorReads=" ++ toString reads

/-- Every observation of the array evaluator agrees with `run` itself. -/
def checkListRun (fixture : Fixture) (memory : Memory) (actual : Run) : IO Unit := do
  let listed := queryRun memory fixture.xs.length fixture.left fixture.right
  check (listed.result == actual.result && listed.final.status == actual.final.status &&
    listed.steps == actual.steps && listed.categories == actual.categories &&
    listed.reads == actual.reads) (fixture.id ++ ": list evaluator disagrees with array evaluator")
  IO.println ("PQ1-RUNTIME LIST-RUN " ++ fixture.id ++ " PASS steps=" ++ toString listed.steps)

def runFixture (program : Array Instruction) (memory : Memory) (fixture : Fixture) : IO Unit := do
  let runOn (memory : Memory) : Run :=
    runArray memory program queryBudget (initialState fixture.xs.length fixture.left fixture.right)
  if fixture.kind == .outer then
    check (encodeInputs fixture.xs.length fixture.left fixture.right).isNone
      (fixture.id ++ ": expected word-domain rejection")
    check (queryNat memory fixture.xs.length fixture.left fixture.right == fixture.expected)
      (fixture.id ++ ": outer API result mismatch")
    IO.println ("PQ1-RUNTIME CASE " ++ fixture.id ++ " PASS outer-value-check")
  else
    check (decide (fixture.left < 2 ^ wordWidth fixture.xs.length ∧
      fixture.right < 2 ^ wordWidth fixture.xs.length)) (fixture.id ++ ": fixture is not representable")
    let actual := runOn memory
    check (actual.result == some (expectedPacket fixture.expected)) (fixture.id ++ ": result mismatch")
    check (fixture.expected == specAnswer fixture.xs fixture.left fixture.right)
      (fixture.id ++ ": literal answer disagrees with scanWindow")
    check (actual.final.status == .halted (expectedPacket fixture.expected)) (fixture.id ++ ": did not halt")
    check (actual.steps ≤ queryBudget) (fixture.id ++ ": primitive budget exceeded")
    check (actual.steps == actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control) (fixture.id ++ ": category mismatch")
    check (actual.reads.all fun receipt => receipt.reply == memory[receipt.address]?)
      (fixture.id ++ ": raw reply mismatch")
    check (actual.reads.all fun receipt => receipt.reply.isSome)
      (fixture.id ++ ": failed physical load")
    if fixture.expected == none then
      check actual.reads.isEmpty (fixture.id ++ ": invalid guard read memory")
      check (actual.steps == if fixture.left < fixture.right then 6 else 4)
        (fixture.id ++ ": guard step count mismatch")
    if fixture.kind == .corruptMetadata then
      let changed := 0 :: memory.tail
      let corrupted := runOn changed
      check (corrupted.result == some 0 && corrupted.result != actual.result)
        (fixture.id ++ ": changed size reply did not affect returned result")
    if fixture.kind == .unreadReplacement then
      let unused := (List.range memory.length).find? fun address =>
        !(actual.reads.any fun receipt => receipt.address == address)
      match unused with
      | none => throw (IO.userError (fixture.id ++ ": no allocated unread cell found"))
      | some address =>
          let changed := memory.set address ((memory[address]?.getD 0 + 1) % 2 ^ wordWidth fixture.xs.length)
          check (changed != memory) (fixture.id ++ ": replacement was unchanged")
          let repeated := runOn changed
          check (repeated.result == actual.result && repeated.steps == actual.steps &&
            repeated.categories == actual.categories && repeated.reads == actual.reads)
            (fixture.id ++ ": unread-cell agreement failed")
    if listRunIDs.contains fixture.id then checkListRun fixture memory actual
    let route ← checkRoute fixture
    IO.println ("PQ1-RUNTIME CASE " ++ fixture.id ++ " PASS steps=" ++ toString actual.steps ++
      " reads=" ++ toString actual.reads.length ++ " answer=" ++ reprStr fixture.expected ++ route)

/-- One preprocessing per distinct input list. -/
def memoryFor (cache : IO.Ref (List (List Int × Memory))) (xs : List Int) : IO Memory := do
  match (← cache.get).find? (·.1 == xs) with
  | some (_, memory) => pure memory
  | none =>
      let memory := buildMemory xs
      cache.modify ((xs, memory) :: ·)
      pure memory

def findFixture (id : String) : IO Fixture := do
  if id.trim.isEmpty then throw (IO.userError "PQ1-RUNTIME explicitly empty selector")
  match (fixtures ++ negativeFixtures).find? (fun fixture => fixture.id == id) with
  | none => throw (IO.userError ("PQ1-RUNTIME unknown selector: " ++ id))
  | some fixture => pure fixture

/-- A selector arrives either as the only argument or, so that an empty value
survives hosts that drop empty native arguments, through `PQ1_RUNTIME_SELECTOR`
spelled `id:<ID>`. -/
def selection (args : List String) : IO (Option Fixture) := do
  let channel ← IO.getEnv selectorVariable
  match args, channel with
  | [], none => pure none
  | [id], none => some <$> findFixture id
  | [], some value =>
      if value.startsWith "id:" then some <$> findFixture (value.drop 3)
      else throw (IO.userError "PQ1-RUNTIME malformed selector channel")
  | _ :: _, some _ => throw (IO.userError "PQ1-RUNTIME selector given twice")
  | _, _ => throw (IO.userError "PQ1-RUNTIME expects zero or one selector")

def mainImpl (args : List String) : IO Unit := do
  check (fixtures.map (·.id) == requiredIDs) "PQ1-RUNTIME registry mismatch, missing or duplicate case"
  check (negativeFixtures.map (·.id) == negativeIDs) "PQ1-RUNTIME negative registry mismatch"
  check (negativeIDs.all fun id => !requiredIDs.contains id) "PQ1-RUNTIME negative control in full registry"
  let chosen ← selection args
  let selected := match chosen with | none => fixtures | some fixture => [fixture]
  let program := queryProgram.toArray
  let cache ← IO.mkRef ([] : List (List Int × Memory))
  for fixture in selected do
    let memory ← memoryFor cache fixture.xs
    runFixture program memory fixture
  let mode := if chosen.isNone then "full" else "selected"
  IO.println ("PQ1-RUNTIME PASS cases=" ++ toString selected.length ++ " mode=" ++ mode)

end RMQ.Validation.PackedQueryRuntime

def main (args : List String) : IO Unit := RMQ.Validation.PackedQueryRuntime.mainImpl args

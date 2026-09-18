import RMQ.Core.WordRAM.Optimization.Capstone
import RMQ.Core.WordRAM.Optimization.Query
import RMQ.Core.WordRAM.Packed.ArrayRun

/-!
# Deterministic controls for actual compact emission

Compiler controls have literal independent answers and ordered receipts, and
also compare the independent structured evaluator. Query controls use the
ordinary scanWindow specification and the accepted original run. Negative
controls deliberately corrupt actual jumps, counters or fuel and must fail
the same observation checks as their positive control.
-/

namespace RMQ.Validation.PackedOptimized

open RMQ RMQ.SuccinctFinal.PackedWordRAM
open Structured Optimization

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def zeroState : State := ⟨fun _ => 0, 0, .running⟩

structure CompilerFixture where
  id : String
  source : Block
  memory : Memory := []
  state : State := zeroState
  expected : Status
  receipts : List Receipt := []
  steps : Nat

def branchSource : Block :=
  .seq (.ifZero 0 (.action (.constant 1 7)) (.action (.constant 1 8))) (.exit 1)

def loadLoop (count : Nat) : Block :=
  .seq (.repeat count (.action (.load 1 0))) (.exit 1)

def compilerFixtures : List CompilerFixture := [
  ⟨"C01-ZERO-BRANCH", branchSource, [], zeroState, .halted 7, [], 3⟩,
  ⟨"C02-NONZERO-BRANCH", branchSource, [], { zeroState with regs := zeroState.regs.write 0 1 },
    .halted 8, [], 4⟩,
  ⟨"C03-ZERO-LOOP", loadLoop 0, [7], zeroState, .halted 0, [], 1⟩,
  ⟨"C04-ONE-LOOP", loadLoop 1, [7], zeroState, .halted 7, [⟨0, some 7⟩], 8⟩,
  ⟨"C05-REPEATED-LOAD", loadLoop 3, [7], zeroState, .halted 7,
    [⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩], 16⟩,
  ⟨"C06-NESTED-LOOP", .seq (.repeat 2 (.repeat 3 (.action (.load 1 0)))) (.exit 1),
    [7], zeroState, .halted 7, List.replicate 6 ⟨0, some 7⟩, 40⟩,
  ⟨"C07-EARLY-HALT", .seq (.repeat 3 (.exit 0)) (.action (.load 1 0)),
    [], zeroState, .halted 0, [], 4⟩,
  ⟨"C08-FAILED-LOAD", loadLoop 3, [], zeroState, .fault, [⟨0, none⟩], 4⟩,
  ⟨"C09-EMPTY-BODY-BOUNDARY", .seq (.repeat 4 .skip) (.exit 0),
    [], zeroState, .halted 0, [], 16⟩,
  ⟨"C10-NESTED-SEQUENCE", .seq (.seq (.action (.constant 1 9)) .skip)
      (.seq (.action (.move 2 1)) (.exit 2)), [], zeroState, .halted 9, [], 3⟩,
  ⟨"C11-INITIALLY-HALTED", loadLoop 3, [], { zeroState with status := .halted 42 },
    .halted 42, [], 0⟩,
  ⟨"C12-INITIALLY-FAULTED", loadLoop 3, [], { zeroState with status := .fault },
    .fault, [], 0⟩,
  ⟨"C13-EMPTY-BRANCHES", .seq (.ifZero 0 .skip .skip) (.exit 0),
    [], zeroState, .halted 0, [], 2⟩]

structure QueryFixture where
  id : String
  xs : List Int
  left : Nat
  right : Nat
  expectedIndex : Option Nat
  corrupt : Bool := false

def crossBlockInput : List Int := [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

def queryFixtures : List QueryFixture := [
  ⟨"Q01-EMPTY", [], 0, 0, none, false⟩,
  ⟨"Q02-SINGLE", [7], 0, 1, some 0, false⟩,
  ⟨"Q03-LEFTMOST-TIE", [4, -3, -3, 8], 0, 4, some 1, false⟩,
  ⟨"Q04-REVERSED", [4, -3, -3, 8], 3, 1, none, false⟩,
  ⟨"Q05-OUT-OF-RANGE", [4, -3, -3, 8], 0, 5, none, false⟩,
  ⟨"Q06-DIFFERENT-BLOCKS", crossBlockInput, 1, 11, some 5, false⟩,
  ⟨"Q07-SAME-BLOCK", crossBlockInput, 6, 10, some 9, false⟩,
  ⟨"Q08-ADJACENT-BLOCKS", crossBlockInput, 4, 8, some 5, false⟩,
  ⟨"Q09-MALFORMED-METADATA", [7], 0, 1, some 0, true⟩,
  ⟨"Q10-WORD-MAX", [7], 2 ^ wordWidth 1 - 1, 2 ^ wordWidth 1 - 1, none, false⟩]

def requiredIDs : List String := [
  "C01-ZERO-BRANCH", "C02-NONZERO-BRANCH", "C03-ZERO-LOOP", "C04-ONE-LOOP",
  "C05-REPEATED-LOAD", "C06-NESTED-LOOP", "C07-EARLY-HALT", "C08-FAILED-LOAD",
  "C09-EMPTY-BODY-BOUNDARY", "C10-NESTED-SEQUENCE", "C11-INITIALLY-HALTED",
  "C12-INITIALLY-FAULTED", "C13-EMPTY-BRANCHES", "Q01-EMPTY", "Q02-SINGLE",
  "Q03-LEFTMOST-TIE", "Q04-REVERSED", "Q05-OUT-OF-RANGE", "Q06-DIFFERENT-BLOCKS",
  "Q07-SAME-BLOCK", "Q08-ADJACENT-BLOCKS", "Q09-MALFORMED-METADATA", "Q10-WORD-MAX"]

def negativeIDs : List String := [
  "N01-JUMP", "N02-COUNTER", "N03-BUDGET", "N04-FRESH-COLLISION"]

def selectorVariable : String := "OPT1_RUNTIME_SELECTOR"

def verifyCompiler (fixture : CompilerFixture) (program : Program) (fuel : Nat) : IO Unit := do
  let expected := fixture.source.eval fixture.memory (Data.ofState fixture.state)
  check (expected.final.status == fixture.expected && expected.reads == fixture.receipts)
    (fixture.id ++ ": independent fixture mismatch")
  let actual := runArray fixture.memory program.toArray fuel fixture.state
  check (actual.final.status == fixture.expected && actual.reads == fixture.receipts)
    (fixture.id ++ ": compiler observation mismatch")
  check (actual.steps == fixture.steps) (fixture.id ++ ": compiler step mismatch")
  check ((List.range 8).all fun r => actual.final.regs r == expected.final.regs r)
    (fixture.id ++ ": protected register mismatch")
  check (actual.steps ≤ compactBound fixture.source) (fixture.id ++ ": compact bound exceeded")
  let listed := run fixture.memory program fuel fixture.state
  check (listed.final.status == actual.final.status && listed.reads == actual.reads &&
    listed.steps == actual.steps) (fixture.id ++ ": array/list mismatch")
  IO.println s!"OPT1 CASE {fixture.id} PASS steps={actual.steps} reads={actual.reads.length}"

def runCompiler (fixture : CompilerFixture) : IO Unit :=
  verifyCompiler fixture (compactAt fixture.source 8 0 0) (compactBound fixture.source)

def runNegative (id : String) : IO Unit := do
  let fixture : CompilerFixture := ⟨id, loadLoop 3, [7], zeroState, .halted 7,
    [⟨0, some 7⟩, ⟨0, some 7⟩, ⟨0, some 7⟩], 16⟩
  let program := compactAt fixture.source 8 0 0
  let changed := match id with
    | "N01-JUMP" => program.set 2 (.branchZero 8 0)
    | "N02-COUNTER" => program.set 0 (.constant 8 0)
    | "N04-FRESH-COLLISION" => compactAt fixture.source 0 0 0
    | _ => program
  let fuel := if id == "N03-BUDGET" then 0 else compactBound fixture.source
  verifyCompiler fixture changed fuel

def expectedPacket : Option Nat → Nat
  | none => 0
  | some index => index + 1

/-- The route oracle uses Cartesian shape and logical close positions, not
the compact execution being checked. -/
def endpointBlocks (xs : List Int) (left right : Nat) : Option (Nat × Nat) :=
  let shape := SuccinctClassic.cartesianShape xs
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  match SuccinctSpace.bpCloseOfInorder? shape left,
      SuccinctSpace.bpCloseOfInorder? shape (right - 1) with
  | some leftClose, some rightClose =>
      some (SuccinctClose.blockOfClose blockSize leftClose,
        SuccinctClose.blockOfClose blockSize rightClose)
  | _, _ => none

def checkQueryRoute (fixture : QueryFixture) : IO Unit := do
  if ["Q06-DIFFERENT-BLOCKS", "Q07-SAME-BLOCK", "Q08-ADJACENT-BLOCKS"].contains fixture.id then
    let reference := SuccinctClassic.queryTraceResult fixture.xs fixture.left fixture.right
    check (reference.value == fixture.expectedIndex) (fixture.id ++ ": independent route answer mismatch")
    let interior := reference.trace.countP fun event => match event with
      | .readWord 20 _ _ => true
      | _ => false
    let route := match fixture.id, endpointBlocks fixture.xs fixture.left fixture.right with
      | "Q06-DIFFERENT-BLOCKS", some (left, right) => left + 1 < right && interior > 0
      | "Q07-SAME-BLOCK", some (left, right) => left == right && interior == 0
      | "Q08-ADJACENT-BLOCKS", some (left, right) => left + 1 == right && interior == 0
      | _, _ => false
    check route (fixture.id ++ ": independent route mismatch")

/-- Each distinct input list is preprocessed once. Cached memories are
immutable; malformed-metadata controls construct separate lists. -/
def memoryFor (cache : IO.Ref (List (List Int × Memory))) (xs : List Int) : IO Memory := do
  match (← cache.get).find? (·.1 == xs) with
  | some (_, memory) => pure memory
  | none =>
      let memory := buildMemory xs
      cache.modify ((xs, memory) :: ·)
      pure memory

def runQuery (program baseline : Array Instruction) (memory : Memory) (fixture : QueryFixture) : IO Unit := do
  let xs := fixture.xs
  let spec := if fixture.left < fixture.right ∧ fixture.right ≤ xs.length then
    some (scanWindow xs fixture.left (fixture.right - fixture.left)) else none
  check (spec == fixture.expectedIndex) (fixture.id ++ ": literal reference mismatch")
  let state := initialState xs.length fixture.left fixture.right
  let actual := runArray memory program compactQueryBudget state
  let original := runArray memory baseline queryBudget state
  check (actual.final.status == .halted (expectedPacket spec)) (fixture.id ++ ": query halt mismatch")
  check (actual.result == original.result && actual.reads == original.reads)
    (fixture.id ++ ": original ordered observation mismatch")
  check (original.steps ≤ 150739) (fixture.id ++ ": original branch bound exceeded")
  check (actual.steps ≤ compactQueryBudget) (fixture.id ++ ": compact query bound exceeded")
  check (actual.reads.all fun receipt => receipt.reply == memory[receipt.address]?)
    (fixture.id ++ ": positional reply mismatch")
  checkQueryRoute fixture
  if fixture.corrupt then
    let changed := 0 :: memory.tail
    let damaged := runArray changed program compactQueryBudget state
    let oldDamaged := runArray changed baseline queryBudget state
    check (damaged.result == some 0 && damaged.result != actual.result)
      (fixture.id ++ ": malformed metadata did not affect answer")
    check (damaged.final.status == oldDamaged.final.status && damaged.reads == oldDamaged.reads)
      (fixture.id ++ ": malformed ordered observations mismatch")
    let missing := runArray [] program compactQueryBudget state
    let oldMissing := runArray [] baseline queryBudget state
    check (missing.final.status == .fault && missing.reads == oldMissing.reads)
      (fixture.id ++ ": missing metadata fault mismatch")
  IO.println s!"OPT1 CASE {fixture.id} PASS steps={actual.steps} reads={actual.reads.length}"

def selection (args : List String) : IO (Option String) := do
  let channel ← IO.getEnv selectorVariable
  let selected ← match args, channel with
    | [], none => pure none
    | [id], none => pure (some id)
    | [], some value =>
        if value.startsWith "id:" then pure (some (value.drop 3))
        else throw (IO.userError "OPT1 malformed selector channel")
    | _, _ => throw (IO.userError "OPT1 duplicate or multiple selectors")
  if let some id := selected then
    if id.trim.isEmpty then throw (IO.userError "OPT1 explicitly empty selector")
    check ((requiredIDs ++ negativeIDs).contains id) ("OPT1 unknown selector: " ++ id)
  pure selected

def mainImpl (args : List String) : IO Unit := do
  check (compilerFixtures.map (·.id) ++ queryFixtures.map (·.id) == requiredIDs)
    "OPT1 registry mismatch"
  check (requiredIDs.length == 23 && negativeIDs.length == 4 &&
    negativeIDs == ["N01-JUMP", "N02-COUNTER", "N03-BUDGET", "N04-FRESH-COLLISION"])
    "OPT1 exact registry version mismatch"
  let chosen ← selection args
  let selected := match chosen with | none => requiredIDs | some id => [id]
  check (!selected.isEmpty) "OPT1 empty selection"
  let cache ← IO.mkRef ([] : List (List Int × Memory))
  let program := compactQueryProgram.toArray
  let baseline := queryProgram.toArray
  let mut executed : List String := []
  for id in selected do
    if negativeIDs.contains id then runNegative id
    else if let some fixture := compilerFixtures.find? (·.id == id) then runCompiler fixture
    else if let some fixture := queryFixtures.find? (·.id == id) then
      let memory ← memoryFor cache fixture.xs
      runQuery program baseline memory fixture
    else throw (IO.userError ("OPT1 missing executable case " ++ id))
    executed := executed ++ [id]
  check (executed == selected) "OPT1 executed/expected registry mismatch"
  IO.println s!"OPT1 PASS executed={executed.length} expected={selected.length} registry=v1"

end RMQ.Validation.PackedOptimized

def main (args : List String) : IO Unit := RMQ.Validation.PackedOptimized.mainImpl args

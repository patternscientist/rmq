import RMQ.Core.WordRAM.Packed.QueryObservations

/-! Deterministic execution checks for the new numeric-memory primitive run.
Expected indices are literal fixture data. Universal route coverage is supplied
by the proofs; these small executions are regression and dependency checks. -/

namespace RMQ.Validation.PackedQueryRuntime

open RMQ.SuccinctFinal.PackedWordRAM

inductive CheckKind where
  | machine | outer | corruptMetadata | unreadReplacement
deriving BEq

structure Fixture where
  id : String
  xs : List Int
  left : Nat
  right : Nat
  expected : Option Nat
  kind : CheckKind := .machine

def fixtures : List Fixture := [
  ⟨"S01-EMPTY", [], 0, 0, none, .machine⟩,
  ⟨"S02-SINGLE", [7], 0, 1, some 0, .machine⟩,
  ⟨"S03-LEFTMOST-TIE", [4, -3, -3, 8], 0, 4, some 1, .machine⟩,
  ⟨"S04-SLICE", [4, -3, -3, 8], 2, 4, some 2, .machine⟩,
  ⟨"S05-REVERSED", [4, -3, -3, 8], 3, 1, none, .machine⟩,
  ⟨"S06-OUT-OF-RANGE", [4, -3, -3, 8], 0, 5, none, .machine⟩,
  ⟨"S07-WORD-MAX", [4, -3, -3, 8], 2 ^ wordWidth 4 - 1, 2 ^ wordWidth 4 - 1, none, .machine⟩,
  ⟨"S08-OUTER-CAPACITY", [4, -3, -3, 8], 2 ^ wordWidth 4, 2 ^ wordWidth 4, none, .outer⟩,
  ⟨"S09-LONG-INTERVAL", (List.range 24).map Int.ofNat, 0, 24, some 0, .machine⟩,
  ⟨"S10-CORRUPT-METADATA", [7], 0, 1, some 0, .corruptMetadata⟩,
  ⟨"S11-UNREAD-REPLACEMENT", [7], 0, 1, some 0, .unreadReplacement⟩]

def requiredIDs : List String := [
  "S01-EMPTY", "S02-SINGLE", "S03-LEFTMOST-TIE", "S04-SLICE", "S05-REVERSED",
  "S06-OUT-OF-RANGE", "S07-WORD-MAX", "S08-OUTER-CAPACITY", "S09-LONG-INTERVAL",
  "S10-CORRUPT-METADATA", "S11-UNREAD-REPLACEMENT"]

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def expectedPacket (expected : Option Nat) : Nat :=
  match expected with | none => 0 | some index => index + 1

def runFixture (fixture : Fixture) : IO Unit := do
  let memory := buildMemory fixture.xs
  if fixture.kind == .outer then
    check (encodeInputs fixture.xs.length fixture.left fixture.right).isNone
      (fixture.id ++ ": expected word-domain rejection")
    check (queryNat memory fixture.xs.length fixture.left fixture.right == fixture.expected)
      (fixture.id ++ ": outer API result mismatch")
    IO.println ("PQ1-RUNTIME CASE " ++ fixture.id ++ " PASS outer-value-check")
  else
    check (decide (fixture.left < 2 ^ wordWidth fixture.xs.length ∧
      fixture.right < 2 ^ wordWidth fixture.xs.length)) (fixture.id ++ ": fixture is not representable")
    let actual := queryRun memory fixture.xs.length fixture.left fixture.right
    check (actual.result == some (expectedPacket fixture.expected)) (fixture.id ++ ": result mismatch")
    check (actual.final.status == .halted (expectedPacket fixture.expected)) (fixture.id ++ ": did not halt")
    check (actual.steps ≤ queryBudget) (fixture.id ++ ": primitive budget exceeded")
    check (actual.steps == actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control) (fixture.id ++ ": category mismatch")
    check (actual.reads.all fun receipt => receipt.reply == memory[receipt.address]?)
      (fixture.id ++ ": raw reply mismatch")
    if fixture.expected == none then
      check actual.reads.isEmpty (fixture.id ++ ": invalid guard read memory")
    if fixture.kind == .corruptMetadata then
      let changed := 0 :: memory.tail
      let corrupted := queryRun changed fixture.xs.length fixture.left fixture.right
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
          let repeated := queryRun changed fixture.xs.length fixture.left fixture.right
          check (repeated.result == actual.result && repeated.steps == actual.steps &&
            repeated.categories == actual.categories && repeated.reads == actual.reads)
            (fixture.id ++ ": unread-cell agreement failed")
    IO.println ("PQ1-RUNTIME CASE " ++ fixture.id ++ " PASS steps=" ++ toString actual.steps ++
      " reads=" ++ toString actual.reads.length ++ " answer=" ++ reprStr fixture.expected)

def mainImpl (args : List String) : IO Unit := do
  check (fixtures.map (·.id) == requiredIDs) "PQ1-RUNTIME registry mismatch, missing or duplicate case"
  let selected ← match args with
    | [] => pure fixtures
    | [id] =>
        if id.trim.isEmpty then
          throw (IO.userError "PQ1-RUNTIME explicitly empty selector")
        match fixtures.find? (fun fixture => fixture.id == id) with
        | none => throw (IO.userError ("PQ1-RUNTIME unknown selector: " ++ id))
        | some fixture => pure [fixture]
    | _ => throw (IO.userError "PQ1-RUNTIME expects zero or one selector")
  for fixture in selected do runFixture fixture
  IO.println ("PQ1-RUNTIME PASS cases=" ++ toString selected.length)

end RMQ.Validation.PackedQueryRuntime

def main (args : List String) : IO Unit := RMQ.Validation.PackedQueryRuntime.mainImpl args

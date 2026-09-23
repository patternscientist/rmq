import RMQ.Core.WordRAM.Bitvector.SelectExperiment

/-! Initial exact registry for the generic physical select route experiment.
This executable is finite feasibility evidence, not a proof of the BV-1 capstone.
-/

open RMQ RMQ.PackedBitvector.Experiment RMQ.SuccinctFinal.PackedWordRAM

structure SelectCase where
  name : String
  bits : List Bool
  target : Bool
  occurrence : Nat

def alternating (n : Nat) : List Bool := (List.range n).map fun i => i % 2 == 1

def selectCases : List SelectCase := [
  ⟨"empty-false", [], false, 0⟩,
  ⟨"empty-true", [], true, 0⟩,
  ⟨"singleton-zero", [false], false, 0⟩,
  ⟨"singleton-one", [true], true, 0⟩,
  ⟨"singleton-missing", [true], false, 0⟩,
  ⟨"size-two-false", [true, false], false, 0⟩,
  ⟨"size-two-true", [false, true], true, 0⟩,
  ⟨"size-two-invalid", [true, true], true, 2⟩,
  ⟨"zeros-last", List.replicate 8 false, false, 7⟩,
  ⟨"zeros-missing-true", List.replicate 8 false, true, 0⟩,
  ⟨"ones-last", List.replicate 8 true, true, 7⟩,
  ⟨"ones-missing-false", List.replicate 8 true, false, 0⟩,
  ⟨"alternating-false", alternating 17, false, 7⟩,
  ⟨"alternating-true", alternating 17, true, 7⟩,
  ⟨"mixed-false", [true,false,true,true,false,false,true,false,true], false, 2⟩,
  ⟨"mixed-true", [true,false,true,true,false,false,true,false,true], true, 3⟩,
  ⟨"threshold-minus-one", alternating 127, true, 60⟩,
  ⟨"threshold", alternating 128, false, 60⟩]

/-- Independent literal registry prevents silent loss or accidental duplication. -/
def expectedCaseNames : List String := [
  "empty-false", "empty-true", "singleton-zero", "singleton-one", "singleton-missing",
  "size-two-false", "size-two-true", "size-two-invalid", "zeros-last", "zeros-missing-true",
  "ones-last", "ones-missing-false", "alternating-false", "alternating-true",
  "mixed-false", "mixed-true", "threshold-minus-one", "threshold"]

def runCase (fixture : SelectCase) : IO Bool := do
  let mem := memory fixture.bits
  let actual := runArray mem program.toArray (source.size + 1)
    (initial fixture.target fixture.occurrence)
  let expected := ((Succinct.select fixture.target fixture.bits fixture.occurrence).map
    (fun x => x + 1)).getD 0
  let correct := actual.result == some expected
  let backed := actual.reads.all fun receipt => receipt.reply == mem[receipt.address]?
  let successful := actual.reads.all fun receipt => receipt.reply.isSome
  let stepOK := actual.steps <= source.size + 1
  let partition := actual.steps == actual.categoryCount .memoryRead +
    actual.categoryCount .registerWrite + actual.categoryCount .arithmetic +
    actual.categoryCount .comparison + actual.categoryCount .branch + actual.categoryCount .control
  let ok := correct && backed && successful && stepOK && partition
  IO.println s!"BV1-CASE {fixture.name} {(if ok then "PASS" else "FAIL")} n={fixture.bits.length} target={fixture.target} occurrence={fixture.occurrence} expected={expected} actual={repr actual.result} steps={actual.steps} reads={actual.reads.length} capacity={mem.length * width fixture.bits.length}"
  return ok

def main (args : List String) : IO UInt32 := do
  if selectCases.map SelectCase.name != expectedCaseNames || expectedCaseNames.isEmpty then
    IO.eprintln "BV1-REGISTRY FAIL version=1"
    return 2
  if args == ["--startup"] then
    IO.println s!"BV1-STARTUP PASS version=1 expected={expectedCaseNames.length}"
    return 0
  if args == ["--list"] then
    for name in expectedCaseNames do IO.println name
    return 0
  let selected : Option (List SelectCase) := match args with
    | [] => some selectCases
    | ["--case", name] =>
        if name.isEmpty || name.trim != name then none
        else (selectCases.find? fun fixture => fixture.name == name).map fun fixture => [fixture]
    | _ => none
  match selected with
  | none =>
      IO.eprintln "BV1-SELECTOR FAIL: expected omitted selector or --case followed by one exact registry name"
      return 2
  | some fixtures =>
      if fixtures.isEmpty then
        IO.eprintln "BV1-SELECTOR FAIL: empty selection"
        return 2
      let mut passed := 0
      for fixture in fixtures do
        if ← runCase fixture then passed := passed + 1
      IO.println s!"BV1-REGISTRY version=1 executed={fixtures.length} expected={fixtures.length} passed={passed} total={expectedCaseNames.length}"
      return if passed == fixtures.length then 0 else 1

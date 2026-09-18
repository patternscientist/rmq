import RMQ.Core.WordRAM.Bitvector.Source

/-! Version 2 exact registry for the complete shared physical allocation.
Finite cases exercise actual new programs against independent List semantics.
Canonical-global rare exceptions remain universal-proof obligations. Separate
parameterized exception controls are required to validate those physical branches.
-/

open RMQ RMQ.PackedBitvector RMQ.SuccinctFinal.PackedWordRAM

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
def expectedSelectCaseNames : List String := [
  "empty-false", "empty-true", "singleton-zero", "singleton-one", "singleton-missing",
  "size-two-false", "size-two-true", "size-two-invalid", "zeros-last", "zeros-missing-true",
  "ones-last", "ones-missing-false", "alternating-false", "alternating-true",
  "mixed-false", "mixed-true", "threshold-minus-one", "threshold"]

structure QueryCase where
  name : String
  operation : PackedBitvector.Operation
  bits : List Bool
  target : Bool
  argument : Nat
  crossingSegment : Option Nat
  apiOnly : Bool

def extraCases : List QueryCase := [
  ⟨"access-empty", .access, [], false, 0, none, false⟩,
  ⟨"access-singleton-zero", .access, [false], false, 0, none, false⟩,
  ⟨"access-singleton-one", .access, [true], false, 0, none, false⟩,
  ⟨"access-length", .access, [true,false], false, 2, none, false⟩,
  ⟨"access-length-plus-one", .access, [false,true], false, 3, none, false⟩,
  ⟨"access-mixed-last", .access, [true,false,true,true,false], false, 4, none, false⟩,
  ⟨"rank-empty-false", .rank, [], false, 0, none, false⟩,
  ⟨"rank-empty-true", .rank, [], true, 0, none, false⟩,
  ⟨"rank-empty-invalid", .rank, [], true, 1, none, false⟩,
  ⟨"rank-zero-prefix", .rank, [true,false,true], true, 0, none, false⟩,
  ⟨"rank-singleton-false", .rank, [false], false, 1, none, false⟩,
  ⟨"rank-singleton-true", .rank, [true], true, 1, none, false⟩,
  ⟨"rank-length-false", .rank, [true,false,true,false,false], false, 5, none, false⟩,
  ⟨"rank-length-true", .rank, [true,false,true,false,false], true, 5, none, false⟩,
  ⟨"rank-length-plus-one", .rank, [true,false,true], true, 4, none, false⟩,
  ⟨"rank-zeros", .rank, List.replicate 17 false, false, 9, none, false⟩,
  ⟨"rank-ones", .rank, List.replicate 17 true, true, 9, none, false⟩,
  ⟨"rank-threshold-minus-one", .rank, alternating 127, true, 127, none, false⟩,
  ⟨"rank-threshold", .rank, alternating 128, false, 128, none, false⟩,
  ⟨"access-crossing", .access, alternating 511, false, 171, some 19, false⟩,
  ⟨"rank-crossing", .rank, alternating 511, true, 175, some 19, false⟩,
  ⟨"select-false-crossing", .select, alternating 511, false, 86, some 0, false⟩,
  ⟨"select-true-crossing", .select, alternating 511, true, 85, some 0, false⟩,
  ⟨"rank-max-representable", .rank, [], false, 2^48-1, none, false⟩,
  ⟨"select-max-representable", .select, [], true, 2^48-1, none, false⟩,
  ⟨"api-access-unrepresentable", .access, [true], false, 2^48, none, true⟩,
  ⟨"api-rank-unrepresentable", .rank, [true], true, 2^48, none, true⟩,
  ⟨"api-select-unrepresentable", .select, [true], true, 2^48, none, true⟩]

def queryCases : List QueryCase :=
  selectCases.map (fun fixture => ⟨fixture.name, .select, fixture.bits,
    fixture.target, fixture.occurrence, none, false⟩) ++ extraCases

/-- Kept independent from the constructed fixture list, including its order. -/
def expectedCaseNames : List String := expectedSelectCaseNames ++ [
  "access-empty", "access-singleton-zero", "access-singleton-one", "access-length",
  "access-length-plus-one", "access-mixed-last", "rank-empty-false", "rank-empty-true",
  "rank-empty-invalid", "rank-zero-prefix", "rank-singleton-false", "rank-singleton-true",
  "rank-length-false", "rank-length-true", "rank-length-plus-one", "rank-zeros", "rank-ones",
  "rank-threshold-minus-one", "rank-threshold", "access-crossing", "rank-crossing",
  "select-false-crossing", "select-true-crossing", "rank-max-representable",
  "select-max-representable", "api-access-unrepresentable", "api-rank-unrepresentable",
  "api-select-unrepresentable"]

def expectedPacket (fixture : QueryCase) : Nat := match fixture.operation with
  | .access => ((fixture.bits[fixture.argument]?).map fun bit => bit.toNat+1).getD 0
  | .rank => if fixture.argument ≤ fixture.bits.length then
      Succinct.rankPrefix fixture.target fixture.bits fixture.argument + 1 else 0
  | .select => ((Succinct.select fixture.target fixture.bits fixture.argument).map
      (fun x => x+1)).getD 0

def runCase (fixture : QueryCase) : IO Bool := do
  let expected := expectedPacket fixture
  if fixture.apiOnly then
    let actual := queryPacket fixture.bits fixture.operation fixture.target fixture.argument
    let outside := fixture.argument >= 2 ^ Experiment.width fixture.bits.length
    let ok := outside && actual == expected
    IO.println s!"BV1-CASE {fixture.name} {(if ok then "PASS" else "FAIL")} backend=guarded-api expected={expected} actual={actual}"
    return ok
  let mem := Allocation.memory fixture.bits
  let code := PackedBitvector.program fixture.operation
  let budget := (PackedBitvector.source fixture.operation).size + 1
  let actual := runArray mem code.toArray budget
    (PackedBitvector.initial fixture.operation fixture.target fixture.argument)
  let correct := actual.result == some expected
  let outputOK := actual.final.regs (resultRegister fixture.operation) == expected
  let halted := actual.final.status == .halted expected
  let backed := actual.reads.all fun receipt => receipt.reply == mem[receipt.address]?
  let successful := actual.reads.all fun receipt => receipt.reply.isSome
  let stepOK := actual.steps <= budget
  let partition := actual.steps == actual.categoryCount .memoryRead +
    actual.categoryCount .registerWrite + actual.categoryCount .arithmetic +
    actual.categoryCount .comparison + actual.categoryCount .branch + actual.categoryCount .control
  let crossing := match fixture.crossingSegment with
    | none => true
    | some segment => actual.transitions.any fun transition =>
        transition.instruction == .load 8266 8261 &&
        transition.before.regs 8192 == segment && transition.before.regs 8193 == 20 &&
        transition.receipt == some ⟨208, mem[208]?⟩ && transition.before.regs 8261 == 208
  let ok := correct && outputOK && halted && backed && successful && stepOK && partition && crossing
  IO.println s!"BV1-CASE {fixture.name} {(if ok then "PASS" else "FAIL")} backend=primitive n={fixture.bits.length} operation={repr fixture.operation} target={fixture.target} argument={fixture.argument} expected={expected} actual={repr actual.result} steps={actual.steps} reads={actual.reads.length} crossing={crossing} capacity={mem.length * Experiment.width fixture.bits.length}"
  return ok

def main (args : List String) : IO UInt32 := do
  if queryCases.map QueryCase.name != expectedCaseNames || expectedCaseNames.isEmpty then
    IO.eprintln "BV1-REGISTRY FAIL version=2"
    return 2
  if args == ["--startup"] then
    IO.println s!"BV1-STARTUP PASS version=2 expected={expectedCaseNames.length}"
    return 0
  if args == ["--list"] then
    for name in expectedCaseNames do IO.println name
    return 0
  let selected : Option (List QueryCase) := match args with
    | [] => some queryCases
    | ["--case", name] =>
        if name.isEmpty || name.trim != name then none
        else (queryCases.find? fun fixture => fixture.name == name).map fun fixture => [fixture]
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
      IO.println s!"BV1-REGISTRY version=2 executed={fixtures.length} expected={fixtures.length} passed={passed} total={expectedCaseNames.length}"
      return if passed == fixtures.length then 0 else 1

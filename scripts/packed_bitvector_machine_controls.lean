import RMQ.Core.WordRAM.Bitvector.Source

/-! Version1 exact supplied-memory and static-instruction controls.
These fixtures execute the actual shared Source.program; they do not mutate it.
-/

open RMQ RMQ.PackedBitvector RMQ.SuccinctFinal.PackedWordRAM

namespace BV1MachineControls

def instructionFitsB (width : Nat) (instruction : Instruction) : Bool :=
  instruction.encoding.all fun operand => decide (operand < 2 ^ width)

theorem instructionFitsB_correct (width : Nat) (instruction : Instruction) :
    instructionFitsB width instruction = true ↔ instruction.Fits width := by
  simp [instructionFitsB, Instruction.Fits, List.all_eq_true]

def programFitsB (width : Nat) (code : Program) : Bool := code.all (instructionFitsB width)

theorem programFitsB_correct (width : Nat) (code : Program) :
    programFitsB width code = true ↔ ∀ instruction ∈ code, instruction.Fits width := by
  simp [programFitsB, List.all_eq_true, instructionFitsB_correct]

theorem dormant_rejects_static_fits (operation : Operation) (width : Nat) :
    ¬ (∀ instruction ∈ PackedBitvector.program operation ++ [.constant 0 (2 ^ width)],
      instruction.Fits width) := by
  intro h
  have hi := h (.constant 0 (2 ^ width)) (by simp)
  exact Nat.lt_irrefl (2 ^ width) (hi (2 ^ width)
    (by simp [Instruction.encoding, Instruction.operands]))

theorem raw_increment_preserves_other_bits (value : Nat) (heven : value % 2 = 0) :
    (value + 1) / 2 = value / 2 ∧ (value + 1) % 2 = 1 := by omega

example (memory : Memory) (code : Program) (fuel : Nat) (state : State) :
    runArray memory code.toArray fuel state = run memory code fuel state :=
  runArray_toArray memory code fuel state

inductive Kind where
  | original | rawCell | lengthCell | countCell | emptyMemory | dormant
  deriving DecidableEq, Repr

structure Fixture where
  name : String
  operation : Operation
  argument : Nat
  originalPacket : Nat
  kind : Kind
  expectedPacket : Nat

def fixtures : List Fixture := [
  ⟨"access-original", .access, 0, 1, .original, 1⟩,
  ⟨"access-raw-cell", .access, 0, 1, .rawCell, 2⟩,
  ⟨"rank-original", .rank, 1, 2, .original, 2⟩,
  ⟨"rank-length-cell", .rank, 1, 2, .lengthCell, 0⟩,
  ⟨"select-original", .select, 0, 1, .original, 1⟩,
  ⟨"select-count-cell", .select, 0, 1, .countCell, 0⟩,
  ⟨"access-empty-memory", .access, 0, 1, .emptyMemory, 0⟩,
  ⟨"rank-empty-memory", .rank, 1, 2, .emptyMemory, 0⟩,
  ⟨"select-empty-memory", .select, 0, 1, .emptyMemory, 0⟩,
  ⟨"access-dormant-oversized", .access, 0, 1, .dormant, 1⟩,
  ⟨"rank-dormant-oversized", .rank, 1, 2, .dormant, 2⟩,
  ⟨"select-dormant-oversized", .select, 0, 1, .dormant, 1⟩]

/-- Literal order and cardinality are independent of fixture construction. -/
def expectedNames : List String := [
  "access-original", "access-raw-cell", "rank-original", "rank-length-cell",
  "select-original", "select-count-cell", "access-empty-memory", "rank-empty-memory",
  "select-empty-memory", "access-dormant-oversized", "rank-dormant-oversized",
  "select-dormant-oversized"]

def packetOK (actual : Run) (operation : Operation) (packet : Nat) : Bool :=
  actual.result == some packet && actual.final.status == .halted packet &&
    actual.final.regs (resultRegister operation) == packet

def readsBacked (actual : Run) (memory : Memory) : Bool :=
  actual.reads.all fun receipt => receipt.reply == memory[receipt.address]?

def readAt (actual : Run) (address value : Nat) : Bool :=
  actual.reads.any fun receipt => receipt.address == address && receipt.reply == some value

def runFixture (fixture : Fixture) : IO Bool := do
  let original := Allocation.memory [false]
  let code := PackedBitvector.program fixture.operation
  let width := Experiment.width 1
  let budget := (PackedBitvector.source fixture.operation).size + 1
  let entry := PackedBitvector.initial fixture.operation false fixture.argument
  let baseline := runArray original code.toArray budget entry
  let baselineOK := packetOK baseline fixture.operation fixture.originalPacket &&
    readsBacked baseline original && programFitsB width code
  let mut passed := false
  match fixture.kind with
  | .original =>
    passed := baselineOK && fixture.expectedPacket == fixture.originalPacket
    IO.println s!"BV1-MACHINE-DETAIL {fixture.name} surface=canonical-packet expected={fixture.originalPacket} actual={repr baseline.result} staticFits={programFitsB width code}"
  | .rawCell | .lengthCell | .countCell =>
    let cell := if fixture.kind == .rawCell then 207 else if fixture.kind == .lengthCell then 2 else 0
    let old := original[cell]?.getD 0
    let replacement := if fixture.kind == .rawCell then old + 1 else 0
    let fixtureOK := original[cell]?.isSome &&
      (if fixture.kind == .rawCell then old % 2 == 0 else old == 1)
    let highBitsPreserved := fixture.kind != .rawCell ||
      (replacement / 2 == old / 2 && replacement % 2 == 1)
    let changed := original.set cell replacement
    let oneCell := changed.length == original.length &&
      (List.range original.length).all fun index =>
        changed[index]? == (if index == cell then some replacement else original[index]?)
    let actual := runArray changed code.toArray budget entry
    passed := baselineOK && fixtureOK && highBitsPreserved && oneCell &&
      packetOK actual fixture.operation fixture.expectedPacket &&
      !(packetOK actual fixture.operation fixture.originalPacket) &&
      actual.result != baseline.result && readsBacked actual changed &&
      readAt baseline cell old && readAt actual cell replacement
    IO.println s!"BV1-MACHINE-DETAIL {fixture.name} surface=supplied-memory-result cell={cell} old={old} new={replacement} expected-original={fixture.originalPacket} actual-original={repr baseline.result} expected-mutant={fixture.expectedPacket} actual-mutant={repr actual.result} canonical-packet-accepted={packetOK actual fixture.operation fixture.originalPacket} oneCell={oneCell} highBitsPreserved={highBitsPreserved} original-read={readAt baseline cell old} mutant-read={readAt actual cell replacement} backed={readsBacked actual changed}"
  | .emptyMemory =>
    let actual := runArray [] code.toArray budget entry
    let firstLoad := match actual.transitions[1]? with
      | none => false
      | some transition => transition.before.pc == 1 && transition.before.regs 6 == 0 &&
        transition.instruction == .load 16 6 && transition.after.status == .fault &&
        transition.receipt == some ⟨0, none⟩
    passed := baselineOK && actual.final.status == .fault && actual.result == none &&
      actual.reads == [⟨0, none⟩] && actual.steps == 2 && firstLoad && readsBacked actual []
    IO.println s!"BV1-MACHINE-DETAIL {fixture.name} surface=first-setup-load expected-status=fault actual-status={repr actual.final.status} expected-result=none actual-result={repr actual.result} expected-receipts=[(0,none)] actual-receipts={repr actual.reads} transition-index=1 steps={actual.steps}"
  | .dormant =>
    let oversized := Instruction.constant 0 (2 ^ width)
    let changedCode := code ++ [oversized]
    let actual := runArray original changedCode.toArray (budget + 1) entry
    let badIndices := (List.range changedCode.length).filter fun index =>
      !(instructionFitsB width (changedCode[index]?.getD (.halt 0)))
    let unreachable := actual.transitions.all fun transition => transition.before.pc < code.length
    let executedFit := actual.transitions.all fun transition => instructionFitsB width transition.instruction
    passed := baselineOK && !(programFitsB width changedCode) &&
      badIndices == [code.length] && unreachable && executedFit &&
      packetOK actual fixture.operation fixture.expectedPacket &&
      actual.result == baseline.result && actual.reads == baseline.reads && actual.steps == baseline.steps
    IO.println s!"BV1-MACHINE-DETAIL {fixture.name} surface=whole-program-Instruction.Fits originalFits={programFitsB width code} mutantFits={programFitsB width changedCode} width={width} oversized={2^width} rejected-index={code.length} bad-indices={repr badIndices} unreachable={unreachable} executedFit={executedFit} expected-packet={fixture.expectedPacket} actual-packet={repr actual.result} sameReads={actual.reads == baseline.reads} sameSteps={actual.steps == baseline.steps}"
  IO.println s!"BV1-MACHINE-CASE {fixture.name} {(if passed then "PASS" else "FAIL")} version=1"
  return passed

def registryOK : Bool :=
  !expectedNames.isEmpty && expectedNames.length == 12 &&
    expectedNames.eraseDups.length == 12 && fixtures.map (·.name) == expectedNames

#print axioms instructionFitsB_correct
#print axioms programFitsB_correct
#print axioms dormant_rejects_static_fits
#print axioms raw_increment_preserves_other_bits

end BV1MachineControls

def main (args : List String) : IO UInt32 := do
  if !BV1MachineControls.registryOK then
    IO.eprintln "BV1-MACHINE-REGISTRY FAIL version=1 expected=12"
    return 2
  if args == ["--list"] then
    IO.println s!"BV1-MACHINE-REGISTRY version=1 cases={repr BV1MachineControls.expectedNames} expected=12"
    return 0
  if args == ["--startup"] then
    IO.println "BV1-MACHINE-STARTUP version=1 expected=12"
    return 0
  let selected ← match args with
    | [] => pure BV1MachineControls.fixtures
    | ["--case", name] =>
      if BV1MachineControls.expectedNames.contains name then
        pure (BV1MachineControls.fixtures.filter fun fixture => fixture.name == name)
      else IO.eprintln "BV1-MACHINE-SELECTOR FAIL" *> pure []
    | _ => IO.eprintln "BV1-MACHINE-SELECTOR FAIL" *> pure []
  if selected.isEmpty then return 2
  let mut passed := 0
  for fixture in selected do
    if ← BV1MachineControls.runFixture fixture then passed := passed + 1
  IO.println s!"BV1-MACHINE-SUMMARY version=1 executed={selected.length} expected={selected.length} passed={passed} total=12"
  return if passed == selected.length then 0 else 1

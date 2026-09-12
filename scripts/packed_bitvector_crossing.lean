import RMQ.Core.WordRAM.Bitvector.CompleteReader

open RMQ RMQ.PackedBitvector.Experiment RMQ.SuccinctFinal.PackedWordRAM

def crossingRegistry : List String :=
  ["reader-component-crossing", "raw-false-crossing", "raw-true-crossing"]

def runCrossing (name : String) : IO Bool := do
  let raw := name != "reader-component-crossing"
  let target := name == "raw-true-crossing"
  let bits := (List.range (if raw then 511 else 127)).map fun i => i % 2 == 1
  let mem := PackedBitvector.Allocation.memory bits
  let w := width bits.length
  -- Fixture selection uses canonical descriptors before the tested run.
  -- This is component coverage, not a claim that a whole select query reaches it.
  let candidates := (List.range 23).flatMap fun segment =>
    let a := 23 + target.toNat * 92 + segment * 4
    (List.range (mem[a + 3]?.getD 0)).map fun index => (segment, index)
  let chosen := if raw then some (0, 19) else candidates.find? fun (segment, index) =>
    let a := 23 + target.toNat * 92 + segment * 4
    let stride := mem[a + 2]?.getD 0
    let pos := mem[a]?.getD 0 + index * stride
    let len := min stride (mem[a + 1]?.getD 0 - index * stride)
    0 < len && w < pos % w + len
  let some (segment, index) := chosen | do
    IO.eprintln "BV1-CROSSING FAIL: no fixture span crosses"
    return false
  let readerProgram := physicalReader.compileAt 0 ++ [.halt 8194]
  let readerInitial : State :=
    ⟨fun r => if r = 3 then target.toNat else if r = 22 then w else if r = 8192 then segment
      else if r = 8193 then index else 0, 0, .running⟩
  let actual := runArray mem readerProgram.toArray (physicalReader.size + 1) readerInitial
  let crossings := actual.transitions.filter fun transition =>
    transition.instruction == .load 8266 8261
  let backed := crossings.all fun transition =>
    match transition.receipt with
    | none => false
    | some receipt => receipt.address == transition.before.regs 8261 &&
        receipt.reply == mem[receipt.address]? && receipt.reply.isSome
  let expected := logicalPacket
    ((PackedBitvector.Allocation.readStore bits target).readWord? segment index)
  let rawPacket := logicalPacket
    ((PackedBitvector.Allocation.readStore bits false).readWord? segment index)
  let complementExercised := !target || expected != rawPacket
  let passed := !crossings.isEmpty && backed && complementExercised && actual.result == some expected
  IO.println s!"BV1-CROSSING {name} version=3 passed={passed} target={target} segment={segment} index={index} second-loads={crossings.length} complemented={target && complementExercised} expected={expected} actual={repr actual.result}"
  return passed

def main (args : List String) : IO UInt32 := do
  if crossingRegistry != ["reader-component-crossing", "raw-false-crossing", "raw-true-crossing"] then
    return 2
  if args == ["--startup"] then
    IO.println "BV1-CROSSING-STARTUP version=3 expected=3"
    return 0
  if args == ["--list"] then
    IO.println s!"BV1-CROSSING-REGISTRY version=3 cases={repr crossingRegistry} expected=3"
    return 0
  let selected ← match args with
    | [] => pure crossingRegistry
    | ["--case", name] =>
      if crossingRegistry.contains name then pure [name]
      else IO.eprintln "BV1-CROSSING-SELECTOR FAIL" *> pure []
    | _ => IO.eprintln "BV1-CROSSING-SELECTOR FAIL" *> pure []
  if selected.isEmpty then return 2
  let mut passed := 0
  for name in selected do
    if ← runCrossing name then passed := passed + 1
  IO.println s!"BV1-CROSSING-SUMMARY version=3 executed={selected.length} expected={selected.length} passed={passed}"
  return if passed == selected.length then 0 else 1

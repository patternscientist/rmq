import RMQ.Core.WordRAM.Bitvector.ReaderInterface

open RMQ RMQ.PackedBitvector.Experiment RMQ.SuccinctFinal.PackedWordRAM

def crossingRegistry : List String := ["reader-component-crossing"]

def main (args : List String) : IO UInt32 := do
  if crossingRegistry != ["reader-component-crossing"] then return 2
  if args == ["--startup"] then
    IO.println "BV1-CROSSING-STARTUP version=2 expected=1"
    return 0
  if args != [] && args != ["--case", "reader-component-crossing"] then
    IO.eprintln "BV1-CROSSING-SELECTOR FAIL"
    return 2
  let bits := (List.range 127).map fun i => i % 2 == 1
  let mem := memory bits
  let w := width bits.length
  -- Fixture selection uses canonical descriptors before the tested run.
  -- This is component coverage, not a claim that a whole select query reaches it.
  let candidates := (List.range 23).flatMap fun segment =>
    let a := 23 + segment * 4
    (List.range (mem[a + 3]?.getD 0)).map fun index => (segment, index)
  let chosen := candidates.find? fun (segment, index) =>
    let a := 23 + segment * 4
    let stride := mem[a + 2]?.getD 0
    let pos := mem[a]?.getD 0 + index * stride
    let len := min stride (mem[a + 1]?.getD 0 - index * stride)
    0 < len && w < pos % w + len
  let some (segment, index) := chosen | do
    IO.eprintln "BV1-CROSSING FAIL: no fixture span crosses"
    return 1
  let readerProgram := physicalReader.compileAt 0 ++ [.halt 8194]
  let readerInitial : State :=
    ⟨fun r => if r = 22 then w else if r = 8192 then segment
      else if r = 8193 then index else 0, 0, .running⟩
  let actual := runArray mem readerProgram.toArray (physicalReader.size + 1) readerInitial
  let crossings := actual.transitions.filter fun transition =>
    transition.instruction == .load 8266 8261
  let backed := crossings.all fun transition =>
    match transition.receipt with
    | none => false
    | some receipt => receipt.address == transition.before.regs 8261 &&
        receipt.reply == mem[receipt.address]? && receipt.reply.isSome
  let expected := PackedBitvector.readerPacket
    (PackedBitvector.genericLogicalWord bits false segment index)
  let passed := !crossings.isEmpty && backed && actual.result == some expected
  IO.println s!"BV1-CROSSING reader-component-crossing version=2 passed={passed} segment={segment} index={index} second-loads={crossings.length} expected={expected} actual={repr actual.result} executed=1 expected-cases=1"
  return if passed then 0 else 1

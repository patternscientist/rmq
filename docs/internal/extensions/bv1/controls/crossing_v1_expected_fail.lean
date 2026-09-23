import RMQ.Core.WordRAM.Bitvector.SelectExperiment

open RMQ RMQ.PackedBitvector.Experiment RMQ.SuccinctFinal.PackedWordRAM

def crossingRegistry : List String := ["canonical-crossing"]

def main (args : List String) : IO UInt32 := do
  if crossingRegistry != ["canonical-crossing"] then return 2
  if args == ["--startup"] then
    IO.println "BV1-CROSSING-STARTUP version=1 expected=1"
    return 0
  if args != [] && args != ["--case", "canonical-crossing"] then
    IO.eprintln "BV1-CROSSING-SELECTOR FAIL"
    return 2
  let bits := (List.range 128).map fun i => i % 2 == 1
  let mem := memory bits
  let actual := runArray mem program.toArray (source.size + 1) (initial false 60)
  let crossings := actual.transitions.filter fun transition =>
    transition.instruction == .load 8266 8261
  let backed := crossings.all fun transition =>
    match transition.receipt with
    | none => false
    | some receipt => receipt.address == transition.before.regs 8261 &&
        receipt.reply == mem[receipt.address]? && receipt.reply.isSome
  let expected := ((Succinct.select false bits 60).map (fun i => i + 1)).getD 0
  let passed := !crossings.isEmpty && backed && actual.result == some expected
  IO.println s!"BV1-CROSSING canonical-crossing passed={passed} second-loads={crossings.length} expected={expected} actual={repr actual.result} executed=1 expected-cases=1"
  return if passed then 0 else 1

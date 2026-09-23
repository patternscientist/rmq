import RMQ.Core.WordRAM.Bitvector.ScratchFrame
open RMQ RMQ.PackedBitvector
open RMQ.SuccinctFinal.PackedWordRAM RMQ.SuccinctFinal.PackedWordRAM.Structured
namespace BV1ScratchConsumer
example (operation : Operation) : (source operation).WritesOnly (fun r => r < 8271) :=
  source_writes_registerBank operation
example (operation : Operation) : ∀ instruction ∈ program operation,
    instruction.WritesOnly (fun r => r < 8271) := program_writes_registerBank operation
example (memory : Memory) (operation : Operation) (target : Bool)
    (argument fuel r : Nat) (hr : 8271 ≤ r) :
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 :=
  run_finite_registers memory operation target argument fuel r hr
example (bits : List Bool) (operation : Operation) (target : Bool)
    (argument r : Nat) (hr : 8271 ≤ r) :
    (execute bits operation target argument).final.regs r = 0 :=
  execute_finite_registers bits operation target argument r hr
example : scratchWords = 8274 := rfl
example : ∀ memory operation target argument fuel r, 8271 ≤ r →
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 :=
  program_preservesScratchBank
example : ¬ (∀ memory operation target argument fuel r, 8271 ≤ r →
    (run memory [.constant 8271 1] fuel (initial operation target argument)).final.regs r = 0) :=
  outOfBankWrite_rejected
#print axioms source_writes_registerBank
#print axioms program_writes_registerBank
#print axioms run_finite_registers
#print axioms execute_finite_registers
#print axioms program_preservesScratchBank
#print axioms outOfBankWrite_rejected
end BV1ScratchConsumer

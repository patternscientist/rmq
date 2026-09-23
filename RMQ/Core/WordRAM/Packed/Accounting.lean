import RMQ.Core.WordRAM.Packed.QuerySource
import RMQ.Core.WordRAM.Packed.Scratch

/-!
# Complete allocation, encoded program and finite scratch capacity

Program space is the literal sum of primitive instruction encoding lengths.
Scratch includes every possibly written register, the three input registers,
one PC and two status words. The actual-run frame theorem proves registers
outside that finite bank remain zero, including at every execution prefix.
This accounting does not by itself assert word safety or query correctness.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured SuccinctSpace

def queryProgramWords : Nat := (queryProgram.map Instruction.encoding).flatten.length
def queryRegisterCount : Nat := max 3 (querySource.maxDestination + 1)
def queryScratchWords : Nat := queryRegisterCount + 3

def queryCompleteRho : Nat → Nat :=
  allocationWithMachineRho queryProgramWords queryScratchWords

theorem queryCompleteRho_littleO : LittleOLinear queryCompleteRho :=
  allocationWithMachineRho_littleO queryProgramWords queryScratchWords

theorem queryProgram_writesOnly :
    ∀ instruction ∈ queryProgram, instruction.WritesOnly
      (fun r => r ≤ querySource.maxDestination) := by
  intro instruction h
  change instruction ∈ querySource.compileAt 0 ++ [.halt 3] at h
  rcases List.mem_append.mp h with h | h
  · exact querySource.compile_writesOnly _ querySource.writesOnly_maxDestination 0 instruction h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst instruction
    trivial

/-- All unused registers remain zero in every actual fuel prefix, including
early rejection, raw-load faults and halted suffixes. -/
theorem queryRun_finite_registers (memory : Memory) (n left right fuel r : Nat)
    (hr : queryRegisterCount ≤ r) :
    (run memory queryProgram fuel (initialState n left right)).final.regs r = 0 := by
  have h3 : 3 ≤ r := Nat.le_trans (Nat.le_max_left ..) hr
  have hm : querySource.maxDestination + 1 ≤ r := Nat.le_trans (Nat.le_max_right ..) hr
  rw [run_frame memory queryProgram fuel (initialState n left right)
    (fun r => r ≤ querySource.maxDestination) queryProgram_writesOnly r (by omega)]
  simp only [initialState, inputRegisters, Registers.write,
    if_neg (show r ≠ 2 by omega), if_neg (show r ≠ 1 by omega), if_neg (show r ≠ 0 by omega)]

/-- Same numeric memory that queryRun executes, plus actual fixed encoded code
and sufficient finite machine state, all absorbed in the checked residual. -/
theorem query_complete_capacity (xs : List Int) :
    ((buildMemory xs).length + queryProgramWords + queryScratchWords) *
      wordWidth xs.length ≤ 2 * xs.length + queryCompleteRho xs.length :=
  buildMemory_with_machine_capacity_le xs queryProgramWords queryScratchWords

end RMQ.SuccinctFinal.PackedWordRAM

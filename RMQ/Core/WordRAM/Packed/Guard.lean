import RMQ.Core.WordRAM.Packed.Structured
import RMQ.Core.WordRAM.Packed.Allocation
import RMQ.Core.WordRAM.Packed.Compiler

/-!
# Total endpoint guard for the fixed packed query

Registers 0,1,2 hold left,right,n; register3 is the result tag. Registers4,5
are guard scratch. Metadata setup starts only in the valid branch. The public
size n is a machine input; neither the value list nor its shape enters this
initial state.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def inputRegisters (n left right : Nat) : Registers :=
  Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n

def initialState (n left right : Nat) : State :=
  ⟨inputRegisters n left right, 0, .running⟩

def guardedBlock (body : Block) : Block :=
  .seq (.action (.constant 3 0))
    (.seq (.action (.comparison .lt 4 0 1))
      (.ifZero 4 (.exit 3)
        (.seq (.action (.comparison .le 5 1 2))
          (.ifZero 5 (.exit 3) body))))

@[simp] theorem inputRegisters_left (n left right : Nat) :
    inputRegisters n left right 0 = left := by simp [inputRegisters, Registers.write]

@[simp] theorem inputRegisters_right (n left right : Nat) :
    inputRegisters n left right 1 = right := by simp [inputRegisters, Registers.write]

@[simp] theorem inputRegisters_size (n left right : Nat) :
    inputRegisters n left right 2 = n := by simp [inputRegisters, Registers.write]

theorem initialState_fits (n left right : Nat)
    (hl : left < 2 ^ wordWidth n) (hr : right < 2 ^ wordWidth n) :
    (initialState n left right).Fits (wordWidth n) := by
  have hn := size_lt_wordCapacity n
  have hp : 0 < 2 ^ wordWidth n := Nat.pow_pos (by omega)
  refine ⟨hp, ?_, ?_⟩
  · intro r
    simp only [initialState, inputRegisters, Registers.write]
    split <;> try assumption
    split <;> try assumption
    split <;> assumption
  · intro value h
    cases h

/-- The source guard rejects invalid intervals without invoking its body or
making physical reads. Primitive realization follows through Compiler.lean. -/
theorem guardedBlock_invalid (body : Block) (n left right : Nat)
    (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    let evaluated := (guardedBlock body).eval [] (Data.ofState (initialState n left right))
    evaluated.final.status = .halted 0 ∧ evaluated.reads = [] := by
  by_cases hlt : left < right
  · have hle : ¬ right ≤ n := by omega
    simp [guardedBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, initialState, inputRegisters,
      Registers.write, Comparison.eval, hlt, hle]
  · simp [guardedBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, initialState, inputRegisters,
      Registers.write, Comparison.eval, hlt]

/-- The same rejection holds on arbitrary numeric memory, including corrupted
or absent metadata. Memory cannot influence a branch preceding every load. -/
theorem guardedBlock_invalid_memory (body : Block) (memory : Memory)
    (n left right : Nat) (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    let evaluated := (guardedBlock body).eval memory (Data.ofState (initialState n left right))
    evaluated.final.status = .halted 0 ∧ evaluated.reads = [] := by
  by_cases hlt : left < right
  · have hle : ¬ right ≤ n := by omega
    simp [guardedBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, initialState, inputRegisters,
      Registers.write, Comparison.eval, hlt, hle]
  · simp [guardedBlock, Block.eval, Action.eval, Action.instruction, execute,
      State.writeNext, Data.ofState, initialState, inputRegisters,
      Registers.write, Comparison.eval, hlt]

/-- Encoding unbounded mathematical endpoints is a value-level operation.
No machine-instruction bound is assigned to parsing or this outer check. -/
def encodeInputs (n left right : Nat) : Option State :=
  if left < 2 ^ wordWidth n ∧ right < 2 ^ wordWidth n then
    some (initialState n left right)
  else none

theorem valid_inputs_encode (n left right : Nat)
    (hl : left < right) (hr : right ≤ n) :
    encodeInputs n left right = some (initialState n left right) := by
  have hn := size_lt_wordCapacity n
  simp [encodeInputs, show left < 2 ^ wordWidth n by omega,
    show right < 2 ^ wordWidth n by omega]

theorem encoding_failure_invalid (n left right : Nat)
    (h : encodeInputs n left right = none) : ¬ (left < right ∧ right ≤ n) := by
  intro hvalid
  rw [valid_inputs_encode n left right hvalid.1 hvalid.2] at h
  cases h

@[simp] theorem guardedBlock_size (body : Block) :
    (guardedBlock body).size = body.size + 9 := by
  simp [guardedBlock, Block.size]
  omega

def guardedProgram (body : Block) : Program :=
  (guardedBlock body).compileAt 0 ++ [.halt 3]

/-- Invalid-input rejection by the actual primitive run, for every body and
every supplied memory. The body cannot contribute a read to this execution. -/
theorem guardedProgram_invalid (body : Block) (memory : Memory)
    (n left right : Nat) (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    let actual := run memory (guardedProgram body) (body.size + 10)
      (initialState n left right)
    actual.result = some 0 ∧ actual.reads = [] ∧ actual.steps ≤ body.size + 10 := by
  have hs := guardedBlock_invalid_memory body memory n left right hinvalid
  have hm := (guardedBlock body).compile_with_halt memory 3
    (initialState n left right) rfl
  dsimp only at hs hm ⊢
  rw [hs.1] at hm
  simpa [guardedProgram, guardedBlock_size, hs.2, Nat.add_assoc] using
    And.intro hm.2.1 (And.intro hm.2.2.1 hm.2.2.2)

end RMQ.SuccinctFinal.PackedWordRAM

import RMQ.Core.WordRAM.Lifecycle.Program
import RMQ.Core.WordRAM.Packed.Allocation

/-! # Fixed whole-owner accounting constants

All request and descriptor registers are inside the numeric bank. Eight control
words cover the PC, status tag and result, three owned extents, the numeric-bank
extent and a spare boundary-control word. Key values are a separate resource.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open SuccinctSpace

def numericBank : Nat := 8273
def controlWords : Nat := 8
def scratchWords : Nat := numericBank + controlWords
def codeWordBudget : Nat := 1116895

def encodedProgram (model : InputModel) : List Nat :=
  ((Layout.program model).map Instruction.encoding).flatten

def retainedRho : Nat → Nat :=
  PackedWordRAM.allocationWithMachineRho codeWordBudget scratchWords

theorem instruction_encoding_length (i : Instruction) : i.encoding.length ≤ 5 := by
  cases i with
  | old p =>
    cases p <;> simp [Instruction.encoding, PackedConstruction.Prim.constants]
  | releaseCell => decide
  | releaseKey => decide
  | releaseKeyRegister => decide

theorem program_encoding_length (p : List Instruction) :
    (p.map Instruction.encoding).flatten.length ≤ 5*p.length := by
  induction p with
  | nil => simp
  | cons i p ih =>
    have hi := instruction_encoding_length i
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem encodedProgram_length_le (model : InputModel) :
    (encodedProgram model).length ≤ codeWordBudget := by
  have h := program_encoding_length (Layout.program model)
  rw [Layout.program_length] at h
  cases model <;> change _ ≤ 1116895 <;> exact Nat.le_trans h (by decide)

theorem instruction_fields_fit (i : Instruction) {W : Nat} (width : 32 ≤ W) : i.Fits W := by
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) width
  cases i with
  | old p =>
    intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact Nat.lt_of_lt_of_le a.isLt hpow
  | releaseCell => intro v hv; simp [Instruction.encoding] at hv; subst v; omega
  | releaseKey => intro v hv; simp [Instruction.encoding] at hv; subst v; omega
  | releaseKeyRegister => intro v hv; simp [Instruction.encoding] at hv; subst v; omega

theorem all_encoded_fields_fit (model : InputModel) (n : Nat) :
    ∀ v ∈ encodedProgram model, v < 2 ^ PackedWordRAM.wordWidth n := by
  intro v hv
  obtain ⟨words, hw, hv⟩ := List.mem_flatten.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
  exact instruction_fields_fit i (PackedConstruction.Proof.wordWidth_ge_32 n) v hv

theorem retainedRho_littleO : LittleOLinear retainedRho :=
  PackedWordRAM.allocationWithMachineRho_littleO codeWordBudget scratchWords

theorem retained_capacity (model : InputModel) (xs : List Int) :
    ((PackedWordRAM.buildMemory xs).length + (encodedProgram model).length +
      numericBank + controlWords) * PackedWordRAM.wordWidth xs.length ≤
        2*xs.length + retainedRho xs.length := by
  have hc := encodedProgram_length_le model
  have h := PackedWordRAM.buildMemory_with_machine_capacity_le xs codeWordBudget scratchWords
  apply Nat.le_trans (Nat.mul_le_mul_right _ (show
    (PackedWordRAM.buildMemory xs).length + (encodedProgram model).length + numericBank + controlWords ≤
      (PackedWordRAM.buildMemory xs).length + codeWordBudget + scratchWords by
        unfold scratchWords; omega)) h

end RMQ.SuccinctFinal.PackedLifecycle

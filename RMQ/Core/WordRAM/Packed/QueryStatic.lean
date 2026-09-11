import RMQ.Core.WordRAM.Packed.Accounting

/-! # Constructor-complete static fields of the fixed query program

The source inventory checks every encoded scalar field, including dormant
branches. Resolved program counters are covered separately by compile_fits.
Neither computation expands the compiled instruction list.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def Instruction.maxEncodedField (instruction : Instruction) : Nat :=
  instruction.encoding.foldr max 0

private theorem member_le_foldr_max (values : List Nat) (value : Nat) (h : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => cases h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst value; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem Instruction.fits_of_maxEncodedField (instruction : Instruction) (width : Nat)
    (bound : instruction.maxEncodedField < 2 ^ width) : instruction.Fits width := by
  intro value h
  exact Nat.lt_of_le_of_lt (member_le_foldr_max instruction.encoding value h) bound

namespace Structured

def Block.maxEncodedField : Block → Nat
  | .skip => 0
  | .action op => op.instruction.maxEncodedField
  | .exit src => (Instruction.halt src).maxEncodedField
  | .seq a b => max a.maxEncodedField b.maxEncodedField
  | .ifZero condition a b =>
      max (Instruction.branchZero condition 0).maxEncodedField
        (max (Instruction.jump 0).maxEncodedField (max a.maxEncodedField b.maxEncodedField))
  | .repeat _ body => body.maxEncodedField

theorem Block.fieldsFit_of_maxEncodedField (block : Block) (width : Nat)
    (bound : block.maxEncodedField < 2 ^ width) : block.FieldsFit width := by
  revert bound
  induction block with
  | skip => intro _; trivial
  | action op => intro bound; exact Instruction.fits_of_maxEncodedField _ _ bound
  | exit src => intro bound; exact Instruction.fits_of_maxEncodedField _ _ bound
  | seq a b iha ihb =>
      intro bound
      have ha := Nat.le_max_left a.maxEncodedField b.maxEncodedField
      have hb := Nat.le_max_right a.maxEncodedField b.maxEncodedField
      exact ⟨iha (by exact Nat.lt_of_le_of_lt ha bound), ihb (by exact Nat.lt_of_le_of_lt hb bound)⟩
  | ifZero c a b iha ihb =>
      intro bound
      simp only [Block.maxEncodedField, Nat.max_lt] at bound
      exact ⟨Instruction.fits_of_maxEncodedField _ _ bound.1,
        Instruction.fits_of_maxEncodedField _ _ bound.2.1, iha bound.2.2.1, ihb bound.2.2.2⟩
  | «repeat» count body ih => exact ih

end Structured

set_option maxRecDepth 30000 in
theorem querySource_maxEncodedField : querySource.maxEncodedField = 8270 := by rfl

set_option maxRecDepth 30000 in
theorem queryBudget_eq : queryBudget = 837572 := by rfl

set_option maxRecDepth 30000 in
theorem queryRegisterCount_eq : queryRegisterCount = 8271 := by rfl

theorem queryScratchWords_eq : queryScratchWords = 8274 := by
  rw [queryScratchWords, queryRegisterCount_eq]

theorem query_small_fields_fit (n : Nat) :
    837572 < 2 ^ wordWidth n := by
  have hf : 837572 < 2 ^ 32 := by decide
  have hm : 2 ^ 32 ≤ 2 ^ wordWidth n :=
    Nat.pow_le_pow_right (by decide) (by unfold wordWidth; omega)
  exact Nat.lt_of_lt_of_le hf hm

theorem querySource_fieldsFit (n : Nat) : querySource.FieldsFit (wordWidth n) := by
  apply Block.fieldsFit_of_maxEncodedField
  rw [querySource_maxEncodedField]
  have h := query_small_fields_fit n
  omega

theorem queryBudget_fits (n : Nat) : queryBudget < 2 ^ wordWidth n := by
  rw [queryBudget_eq]
  exact query_small_fields_fit n

theorem querySource_size_lt_capacity (n : Nat) : querySource.size < 2 ^ wordWidth n := by
  have h := queryBudget_fits n
  simp only [querySource, guardedBlock_size, queryBudget] at h ⊢
  omega

/-- Every field of every actual compiled instruction fits, whether executed
or dormant. This includes resolved branch/jump PCs, operation tags and halt. -/
theorem queryProgram_fits (n : Nat) :
    ∀ instruction ∈ queryProgram, instruction.Fits (wordWidth n) := by
  intro instruction h
  change instruction ∈ querySource.compileAt 0 ++ [.halt 3] at h
  rcases List.mem_append.mp h with h | h
  · exact querySource.compile_fits (wordWidth n) 0 (querySource_fieldsFit n)
      (by simpa only [Nat.zero_add] using querySource_size_lt_capacity n) instruction h
  · simp only [List.mem_singleton] at h
    subst instruction
    have hf := query_small_fields_fit n
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega

theorem Instruction.encoding_length_le_five (instruction : Instruction) :
    instruction.encoding.length ≤ 5 := by
  cases instruction <;> simp [Instruction.encoding, Instruction.operands]

theorem program_encoding_length_le (program : Program) :
    (program.map Instruction.encoding).flatten.length ≤ 5 * program.length := by
  induction program with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have h := instruction.encoding_length_le_five
      omega

theorem queryProgramWords_le : queryProgramWords ≤ 5 * queryBudget := by
  have h := program_encoding_length_le queryProgram
  rw [queryProgram_length] at h
  exact h

end RMQ.SuccinctFinal.PackedWordRAM

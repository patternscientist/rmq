import RMQ.Core.WordRAM.Optimization.CompactStatic
import RMQ.Core.WordRAM.Packed.QueryStatic

/-!
# Fixed compact query objects

These definitions fix the same source, allocation and initial registers as
the accepted packed query. Only emitted control flow and counted scratch
change. Correctness and safety are separate theorem obligations.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Structured SuccinctSpace

def compactQuerySource : Block := .seq querySource (.exit 3)
def compactQueryFresh : Nat := queryRegisterCount
def compactQueryProgram : Program := compactAt compactQuerySource compactQueryFresh 0 0
def compactQueryBudget : Nat := compactBound compactQuerySource
def compactQueryRegisterCount : Nat := compactQueryFresh + 2 * compactDepth compactQuerySource
def compactQueryScratchWords : Nat := compactQueryRegisterCount + 3
def compactQueryProgramWords : Nat := (compactQueryProgram.map Instruction.encoding).flatten.length
def compactQueryCompleteRho : Nat → Nat :=
  allocationWithMachineRho compactQueryProgramWords compactQueryScratchWords

def compactQueryRun (memory : Memory) (n left right : Nat) : Run :=
  run memory compactQueryProgram compactQueryBudget (initialState n left right)

def compactQueryNat (memory : Memory) (n left right : Nat) : Option Nat :=
  match encodeInputs n left right with
  | none => none
  | some state =>
      (run memory compactQueryProgram compactQueryBudget state).result.bind fun packet =>
        if packet = 0 then none else some (packet - 1)

theorem compactQueryProgram_length :
    compactQueryProgram.length = compactSize compactQuerySource :=
  compactAt_length compactQuerySource compactQueryFresh 0 0

/-- The source recurrence is linked to the literal encoding actually charged
by the complete-space definition; it does not replace that definition. -/
theorem compactQueryProgramWords_eq_encoding :
    compactQueryProgramWords = compactEncodingWords compactQuerySource :=
  compactAt_encoding_length compactQuerySource compactQueryFresh 0 0

/-- Static scalar-field bounds include source reads and branch/halt operands. -/
theorem registersBelow_of_maxEncodedField (block : Block) (bound : Nat)
    (fields : block.maxEncodedField < bound) : BlockRegistersBelow bound block := by
  induction block with
  | skip => trivial
  | action op =>
      cases op <;>
        simp [Block.maxEncodedField, Action.instruction, Instruction.maxEncodedField,
          Instruction.encoding, Instruction.operands, BlockRegistersBelow,
          ActionRegistersBelow] at fields ⊢ <;> omega
  | exit src =>
      simp [Block.maxEncodedField, Instruction.maxEncodedField, Instruction.encoding,
        Instruction.operands, BlockRegistersBelow] at fields ⊢
      omega
  | seq a b iha ihb =>
      simp only [Block.maxEncodedField, Nat.max_lt] at fields
      exact ⟨iha fields.1, ihb fields.2⟩
  | ifZero c z n ihz ihn =>
      simp only [Block.maxEncodedField, Nat.max_lt] at fields
      refine ⟨?_, ihz fields.2.2.1, ihn fields.2.2.2⟩
      have h := fields.1
      simp [Instruction.maxEncodedField, Instruction.encoding, Instruction.operands] at h
      omega
  | «repeat» count body ih => exact ih fields

theorem compactQuerySource_registersBelow :
    BlockRegistersBelow compactQueryFresh compactQuerySource := by
  apply registersBelow_of_maxEncodedField
  change max querySource.maxEncodedField (Instruction.halt 3).maxEncodedField < queryRegisterCount
  rw [querySource_maxEncodedField, queryRegisterCount_eq]
  decide

theorem compactQuerySource_fieldsFit (n : Nat) :
    compactQuerySource.FieldsFit (wordWidth n) := by
  refine ⟨querySource_fieldsFit n, ?_⟩
  have h := query_small_fields_fit n
  simp [Block.FieldsFit, Instruction.Fits, Instruction.encoding, Instruction.operands]
  omega

set_option maxRecDepth 30000 in
theorem compactQuery_depth : compactDepth compactQuerySource = 1 := by rfl

set_option maxRecDepth 30000 in
theorem compactQuery_maxCount : compactMaxCount compactQuerySource = 33 := by rfl

theorem compactQueryRegisterCount_eq : compactQueryRegisterCount = 8273 := by
  simp only [compactQueryRegisterCount, compactQueryFresh, queryRegisterCount_eq, compactQuery_depth]

theorem compactQueryScratchWords_eq : compactQueryScratchWords = 8276 := by
  simp only [compactQueryScratchWords, compactQueryRegisterCount_eq]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem compactQuerySize_eq : compactSize compactQuerySource = 212964 := by rfl

/-- Concrete literal instruction count, obtained through the emitted-length
theorem and independently compared with evaluation of the actual code list. -/
theorem compactQueryProgram_length_eq : compactQueryProgram.length = 212964 :=
  compactQueryProgram_length.trans compactQuerySize_eq

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem compactQueryEncodingWords_eq : compactEncodingWords compactQuerySource = 722339 := by rfl

/-- All numeric words in the actual flattened instruction encoding are
counted, including the count constants and five-instruction loop controls. -/
theorem compactQueryProgramWords_eq : compactQueryProgramWords = 722339 :=
  compactQueryProgramWords_eq_encoding.trans compactQueryEncodingWords_eq

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
theorem compactQueryBudget_eq : compactQueryBudget = 151978 := by rfl

theorem compactQuery_size_reduction : compactQueryProgram.length < queryProgram.length := by
  rw [compactQueryProgram_length_eq, queryProgram_length, queryBudget_eq]
  decide

theorem compactQueryProgram_fits (n : Nat) :
    ∀ instruction ∈ compactQueryProgram, instruction.Fits (wordWidth n) := by
  apply compactAt_fits compactQuerySource (wordWidth n) compactQueryFresh 0 0
    (compactQuerySource_fieldsFit n)
  · rw [compactQuery_maxCount]
    have h := query_small_fields_fit n
    omega
  · have h := query_small_fields_fit n
    omega
  · simp only [Nat.zero_add, compactQueryFresh, queryRegisterCount_eq, compactQuery_depth]
    have h := query_small_fields_fit n
    omega
  · have h := compactQuery_size_reduction
    rw [compactQueryProgram_length, queryProgram_length, queryBudget_eq] at h
    have capacity := query_small_fields_fit n
    omega

theorem compactQuery_finite_registers (memory : Memory) (n left right fuel r : Nat)
    (outside : compactQueryRegisterCount ≤ r) :
    (run memory compactQueryProgram fuel (initialState n left right)).final.regs r = 0 := by
  have h := compact_run_frame memory compactQuerySource compactQueryFresh 0 0 fuel
    compactQuerySource_registersBelow (initialState n left right) r
    (by simpa only [Nat.zero_add, compactQueryRegisterCount] using outside)
  have hr : 3 ≤ r := by rw [compactQueryRegisterCount_eq] at outside; omega
  have initialZero : (initialState n left right).regs r = 0 := by
    simp only [initialState, inputRegisters, Registers.write,
      if_neg (show r ≠ 2 by omega), if_neg (show r ≠ 1 by omega), if_neg (show r ≠ 0 by omega)]
  simpa only [compactQueryProgram] using h.trans initialZero

theorem compactQueryCompleteRho_littleO : LittleOLinear compactQueryCompleteRho :=
  allocationWithMachineRho_littleO compactQueryProgramWords compactQueryScratchWords

/-- Capacity counts the literal emitted encoding and the declared scratch
bank. The finite-bank execution theorem is a separate required consumer. -/
theorem compactQuery_complete_capacity (xs : List Int) :
    ((buildMemory xs).length + compactQueryProgramWords + compactQueryScratchWords) *
      wordWidth xs.length ≤ 2 * xs.length + compactQueryCompleteRho xs.length :=
  buildMemory_with_machine_capacity_le xs compactQueryProgramWords compactQueryScratchWords

namespace CompactQueryStaticConsumers

theorem program_length_expectedType : compactQueryProgram.length = 212964 :=
  compactQueryProgram_length_eq

theorem numeric_encoded_words_expectedType :
    (compactQueryProgram.map Instruction.encoding).flatten.length = 722339 :=
  compactQueryProgramWords_eq

theorem budget_expectedType : compactBound compactQuerySource = 151978 :=
  compactQueryBudget_eq

theorem scratch_expectedType :
    compactQueryFresh + 2 * compactDepth compactQuerySource = 8273 ∧
      compactQueryScratchWords = 8276 :=
  ⟨compactQueryRegisterCount_eq, compactQueryScratchWords_eq⟩

theorem encoded_words_expectedType :
    (compactQueryProgram.map Instruction.encoding).flatten.length =
      compactEncodingWords compactQuerySource :=
  compactQueryProgramWords_eq_encoding

theorem finite_bank_expectedType (memory : Memory) (n left right fuel : Nat) :
    ∀ r, compactQueryRegisterCount ≤ r →
      (run memory compactQueryProgram fuel (initialState n left right)).final.regs r = 0 :=
  fun r outside => compactQuery_finite_registers memory n left right fuel r outside

theorem complete_capacity_expectedType (xs : List Int) :
    ((buildMemory xs).length +
      (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
      2 * xs.length + compactQueryCompleteRho xs.length :=
  compactQuery_complete_capacity xs

end CompactQueryStaticConsumers

end RMQ.SuccinctFinal.PackedWordRAM.Optimization

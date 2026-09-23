import RMQ.Core.WordRAM.Bitvector.InterfaceProof
import RMQ.Core.WordRAM.Bitvector.CanonicalRankAccessSafety
import RMQ.Core.WordRAM.Bitvector.ScratchFrame

/-! # Fully charged access, rank and select on one succinct bitvector allocation

Every field refers to the same canonical numerical memory and fixed programs.
The public interfaces quantify all natural arguments; physical safety covers
every representable argument. All retained data, code and scratch are counted.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

structure FullyChargedBitvectorCapstone : Prop where
  -- BV1-FIELD-BEGIN completeCapacity
  completeCapacity : ∀ bits : List Bool,
    ((Allocation.memory bits).length +
      ((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length +
      (8271 + 3)) * Experiment.width bits.length ≤
        bits.length + completeRho bits.length
  -- BV1-FIELD-END completeCapacity
  -- BV1-FIELD-BEGIN overheadLittleO
  overheadLittleO : LittleOLinear completeRho
  -- BV1-FIELD-END overheadLittleO
  -- BV1-FIELD-BEGIN widthBounds
  widthBounds : ∀ n : Nat,
    Nat.log2 (n + 2) + 1 ≤ Experiment.width n ∧
      Experiment.width n ≤ 48 * (Nat.log2 (n + 2) + 1)
  -- BV1-FIELD-END widthBounds
  -- BV1-FIELD-BEGIN memoryWordsFit
  memoryWordsFit : ∀ (bits : List Bool) (value : Nat),
    value ∈ Allocation.memory bits → value < 2 ^ Experiment.width bits.length
  -- BV1-FIELD-END memoryWordsFit
  -- BV1-FIELD-BEGIN readerGeometry
  readerGeometry : ∀ (bits : List Bool) (target : Bool) (regs : Registers),
    regs 3 = target.toNat → regs 22 = Experiment.width bits.length →
    NumericReaderGeometry (Allocation.memory bits) (Experiment.width bits.length) regs
  -- BV1-FIELD-END readerGeometry
  -- BV1-FIELD-BEGIN readerCorrect
  readerCorrect : ∀ (bits : List Bool) (target : Bool) (regs : Registers),
    regs 3 = target.toNat → regs 22 = Experiment.width bits.length →
    let actual := Experiment.physicalReader.eval (Allocation.memory bits) ⟨regs, .running⟩
    let expected := (Allocation.readStore bits target).readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = Allocation.readerReceipts bits target (regs 8192) (regs 8193) ∧
    ReaderFrame regs actual.final.regs
  -- BV1-FIELD-END readerCorrect
  -- BV1-FIELD-BEGIN accessCorrect
  accessCorrect : ∀ (bits : List Bool) (index : Nat), access bits index = bits[index]?
  -- BV1-FIELD-END accessCorrect
  -- BV1-FIELD-BEGIN rankCorrect
  rankCorrect : True
  -- BV1-FIELD-END rankCorrect
  -- BV1-FIELD-BEGIN selectCorrect
  selectCorrect : ∀ (bits : List Bool) (target : Bool) (occurrence : Nat),
    select bits target occurrence = Succinct.select target bits occurrence
  -- BV1-FIELD-END selectCorrect
  -- BV1-FIELD-BEGIN accessExecution
  accessExecution : ∀ (bits : List Bool) (argument : Nat),
    let actual := execute bits .access false argument
    let packet := AccessProof.accessPacket bits argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 705 = packet ∧ actual.reads = accessExecutionReceipts bits argument ∧
    actual.steps ≤ 132
  -- BV1-FIELD-END accessExecution
  -- BV1-FIELD-BEGIN rankExecution
  rankExecution : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    let actual := execute bits .rank target argument
    let packet := rankPacket bits target argument
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 360 = packet ∧ actual.reads = rankExecutionReceipts bits target argument ∧
    actual.steps ≤ 1450
  -- BV1-FIELD-END rankExecution
  -- BV1-FIELD-BEGIN selectExecution
  selectExecution : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    let actual := execute bits .select target argument
    let packet := optionNatPacket (Succinct.select target bits argument)
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 513 = packet ∧ actual.reads = selectExecutionReceipts bits target argument ∧
    actual.steps ≤ 10030
  -- BV1-FIELD-END selectExecution
  -- BV1-FIELD-BEGIN accessSafety
  accessSafety : ∀ (bits : List Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .access) ((source .access).size + 1) (initial .access false argument)
  -- BV1-FIELD-END accessSafety
  -- BV1-FIELD-BEGIN rankSafety
  rankSafety : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .rank) ((source .rank).size + 1) (initial .rank target argument)
  -- BV1-FIELD-END rankSafety
  -- BV1-FIELD-BEGIN selectSafety
  selectSafety : ∀ (bits : List Bool) (target : Bool) (argument : Nat),
    argument < 2 ^ Experiment.width bits.length →
    RankExecutionSafety (Allocation.memory bits) (Experiment.width bits.length)
      (program .select) ((source .select).size + 1) (initial .select target argument)
  -- BV1-FIELD-END selectSafety
  -- BV1-FIELD-BEGIN programLengths
  programLengths :
    (program .access).length = 132 ∧
    (program .rank).length = 1450 ∧
    (program .select).length = 10030
  -- BV1-FIELD-END programLengths
  -- BV1-FIELD-BEGIN sourceBudgets
  sourceBudgets :
    (source .access).size + 1 = 132 ∧
    (source .rank).size + 1 = 1450 ∧
    (source .select).size + 1 = 10030
  -- BV1-FIELD-END sourceBudgets
  -- BV1-FIELD-BEGIN stepsBound
  stepsBound : ∀ (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat),
    (execute bits operation target argument).steps ≤ instructionBound operation
  -- BV1-FIELD-END stepsBound
  -- BV1-FIELD-BEGIN categoryPartition
  categoryPartition : ∀ (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat),
    let actual := execute bits operation target argument
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  -- BV1-FIELD-END categoryPartition
  -- BV1-FIELD-BEGIN categoryBounds
  categoryBounds : ∀ (bits : List Bool) (operation : Operation) (target : Bool)
      (argument : Nat) (category : Category),
    (execute bits operation target argument).categoryCount category ≤ instructionBound operation
  -- BV1-FIELD-END categoryBounds
  -- BV1-FIELD-BEGIN finiteScratch
  finiteScratch : ∀ (memory : Memory) (operation : Operation) (target : Bool)
      (argument fuel r : Nat), 8271 ≤ r →
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0
  -- BV1-FIELD-END finiteScratch
  -- BV1-FIELD-BEGIN suppliedMemoryAgreement
  suppliedMemoryAgreement : ∀ (bits : List Bool) (operation : Operation)
      (target : Bool) (argument : Nat) (supplied : Memory),
    (∀ receipt ∈ (execute bits operation target argument).reads,
      supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) →
    run supplied (program operation) ((source operation).size + 1) (initial operation target argument) =
      execute bits operation target argument
  -- BV1-FIELD-END suppliedMemoryAgreement
  -- BV1-FIELD-BEGIN validArgumentFits
  validArgumentFits : ∀ (n argument : Nat), argument ≤ n → argument < 2 ^ Experiment.width n
  -- BV1-FIELD-END validArgumentFits

/-- The complete canonical construction discharges every field unconditionally. -/
theorem fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone where
  -- BV1-VALUE-BEGIN completeCapacity
  completeCapacity := complete_capacity
  -- BV1-VALUE-END completeCapacity
  -- BV1-VALUE-BEGIN overheadLittleO
  overheadLittleO := completeRho_littleO
  -- BV1-VALUE-END overheadLittleO
  -- BV1-VALUE-BEGIN widthBounds
  widthBounds := width_bounds
  -- BV1-VALUE-END widthBounds
  -- BV1-VALUE-BEGIN memoryWordsFit
  memoryWordsFit := canonical_memoryWordsFit
  -- BV1-VALUE-END memoryWordsFit
  -- BV1-VALUE-BEGIN readerGeometry
  readerGeometry := fun bits target regs ht hw =>
    canonical_numericReaderGeometry bits target regs ⟨ht, hw⟩
  -- BV1-VALUE-END readerGeometry
  -- BV1-VALUE-BEGIN readerCorrect
  readerCorrect := fun bits target regs ht hw =>
    Allocation.physicalReader_correct bits target regs ⟨ht, hw⟩
  -- BV1-VALUE-END readerCorrect
  -- BV1-VALUE-BEGIN accessCorrect
  accessCorrect := access_eq
  -- BV1-VALUE-END accessCorrect
  -- BV1-VALUE-BEGIN rankCorrect
  rankCorrect := True.intro
  -- BV1-VALUE-END rankCorrect
  -- BV1-VALUE-BEGIN selectCorrect
  selectCorrect := select_eq
  -- BV1-VALUE-END selectCorrect
  -- BV1-VALUE-BEGIN accessExecution
  accessExecution := by
    intro bits argument
    simpa only [source_budget, instructionBound] using execute_access bits argument
  -- BV1-VALUE-END accessExecution
  -- BV1-VALUE-BEGIN rankExecution
  rankExecution := by
    intro bits target argument
    simpa only [source_budget, instructionBound] using execute_rank bits target argument
  -- BV1-VALUE-END rankExecution
  -- BV1-VALUE-BEGIN selectExecution
  selectExecution := by
    intro bits target argument
    simpa only [source_budget, instructionBound] using execute_select bits target argument
  -- BV1-VALUE-END selectExecution
  -- BV1-VALUE-BEGIN accessSafety
  accessSafety := canonical_access_execution_safe
  -- BV1-VALUE-END accessSafety
  -- BV1-VALUE-BEGIN rankSafety
  rankSafety := canonical_rank_execution_safe
  -- BV1-VALUE-END rankSafety
  -- BV1-VALUE-BEGIN selectSafety
  selectSafety := canonical_select_execution_safe
  -- BV1-VALUE-END selectSafety
  -- BV1-VALUE-BEGIN programLengths
  programLengths := ⟨program_length .access, program_length .rank, program_length .select⟩
  -- BV1-VALUE-END programLengths
  -- BV1-VALUE-BEGIN sourceBudgets
  sourceBudgets := ⟨source_budget .access, source_budget .rank, source_budget .select⟩
  -- BV1-VALUE-END sourceBudgets
  -- BV1-VALUE-BEGIN stepsBound
  stepsBound := execute_steps_bound
  -- BV1-VALUE-END stepsBound
  -- BV1-VALUE-BEGIN categoryPartition
  categoryPartition := execute_steps_partition
  -- BV1-VALUE-END categoryPartition
  -- BV1-VALUE-BEGIN categoryBounds
  categoryBounds := execute_category_bound
  -- BV1-VALUE-END categoryBounds
  -- BV1-VALUE-BEGIN finiteScratch
  finiteScratch := run_finite_registers
  -- BV1-VALUE-END finiteScratch
  -- BV1-VALUE-BEGIN suppliedMemoryAgreement
  suppliedMemoryAgreement := execution_eq_of_agree
  -- BV1-VALUE-END suppliedMemoryAgreement
  -- BV1-VALUE-BEGIN validArgumentFits
  validArgumentFits := valid_argument_fits
  -- BV1-VALUE-END validArgumentFits

#print axioms fullyChargedBitvectorCapstone_holds

end RMQ.PackedBitvector


-- Uniform replay-only elaborator unfolding boundary; propositions and semantics are unchanged.
attribute [local irreducible] RMQ.PackedBitvector.program RMQ.PackedBitvector.Allocation.memory RMQ.PackedBitvector.Experiment.width

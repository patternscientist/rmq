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
  readerCorrect : True
  -- BV1-FIELD-END readerCorrect
  -- BV1-FIELD-BEGIN accessCorrect
  accessCorrect : ∀ (bits : List Bool) (index : Nat), access bits index = bits[index]?
  -- BV1-FIELD-END accessCorrect
  -- BV1-FIELD-BEGIN rankCorrect
  rankCorrect : ∀ (bits : List Bool) (target : Bool) (endPos : Nat),
    rank bits target endPos =
      if endPos ≤ bits.length then some (Succinct.rankPrefix target bits endPos) else none
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
  readerCorrect := True.intro
  -- BV1-VALUE-END readerCorrect
  -- BV1-VALUE-BEGIN accessCorrect
  accessCorrect := access_eq
  -- BV1-VALUE-END accessCorrect
  -- BV1-VALUE-BEGIN rankCorrect
  rankCorrect := rank_eq
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
attribute [irreducible] RMQ.PackedBitvector.program


/-! Independent required propositions. Each proof projects only its named public
field from an arbitrary certificate; implementation sibling theorems cannot
silently replace a missing or weakened public dependency. -/

namespace RMQ.PackedBitvector.PublicConsumer

open SuccinctSpace SuccinctRank
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

theorem public_completeCapacity_required (c : FullyChargedBitvectorCapstone) (bits : List Bool) :
    ((Allocation.memory bits).length +
      ((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length + (8271 + 3)) *
        Experiment.width bits.length ≤ bits.length + completeRho bits.length :=
  c.completeCapacity bits

theorem public_overheadLittleO_required (c : FullyChargedBitvectorCapstone) :
    LittleOLinear completeRho := c.overheadLittleO

theorem public_widthBounds_required (c : FullyChargedBitvectorCapstone) (n : Nat) :
    Nat.log2 (n+2)+1 ≤ Experiment.width n ∧
    Experiment.width n ≤ 48*(Nat.log2 (n+2)+1) := c.widthBounds n

theorem public_memoryWordsFit_required (c : FullyChargedBitvectorCapstone) (bits : List Bool) :
    ∀ value ∈ Allocation.memory bits, value < 2 ^ Experiment.width bits.length :=
  c.memoryWordsFit bits

theorem public_readerGeometry_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (regs : Registers)
    (ht : regs 3 = target.toNat) (hw : regs 22 = Experiment.width bits.length) :
    (regs 8192 < 23 → numericDescriptorAddress regs + 3 < 2 ^ Experiment.width bits.length) ∧
    (regs 8192 < 23 → ∀ (bitBase bitLength stride count : Nat),
      (Allocation.memory bits)[numericDescriptorAddress regs]? = some bitBase →
      (Allocation.memory bits)[numericDescriptorAddress regs + 1]? = some bitLength →
      (Allocation.memory bits)[numericDescriptorAddress regs + 2]? = some stride →
      (Allocation.memory bits)[numericDescriptorAddress regs + 3]? = some count →
      regs 8193 < count →
      bitBase + regs 8193 * stride < 2 ^ Experiment.width bits.length ∧
        stride < Experiment.width bits.length) :=
  c.readerGeometry bits target regs ht hw

theorem public_readerCorrect_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (regs : Registers)
    (ht : regs 3 = target.toNat) (hw : regs 22 = Experiment.width bits.length) :
    let actual := Experiment.physicalReader.eval (Allocation.memory bits) ⟨regs, .running⟩
    let word := Allocation.logicalWord bits target (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = (match word with | none => 0 | some xs => bitsToNatLE xs + 1) ∧
    actual.final.regs 8195 = (word.map List.length).getD 0 ∧
    actual.reads = Allocation.readerReceipts bits target (regs 8192) (regs 8193) ∧
    (∀ r, r < 8194 ∨ 8271 ≤ r → actual.final.regs r = regs r) :=
  c.readerCorrect bits target regs ht hw

theorem public_accessCorrect_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (i : Nat) : access bits i = bits[i]? := c.accessCorrect bits i

theorem public_rankCorrect_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (p : Nat) :
    rank bits target p = if p ≤ bits.length then some (Succinct.rankPrefix target bits p) else none :=
  c.rankCorrect bits target p

theorem public_selectCorrect_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (k : Nat) :
    select bits target k = Succinct.select target bits k := c.selectCorrect bits target k

theorem public_accessExecution_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (i : Nat) :
    let actual := execute bits .access false i
    let packet := ((bits[i]?).map (fun bit => bit.toNat + 1)).getD 0
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 705 = packet ∧
    actual.reads = ChargedSetup.setupReceipts bits ++ AccessProof.accessReceipts bits i ∧
    actual.steps ≤ 132 := c.accessExecution bits i

theorem public_rankExecution_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (p : Nat) :
    let actual := execute bits .rank target p
    let packet := if p ≤ bits.length then Succinct.rankPrefix target bits p + 1 else 0
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 360 = packet ∧
    actual.reads = ChargedSetup.setupReceipts bits ++
      (if p ≤ bits.length then Controller.traceReads (Allocation.readerReceipts bits target)
        (rankReadTrace bits target p).trace else []) ∧
    actual.steps ≤ 1450 := c.rankExecution bits target p

theorem public_selectExecution_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (k : Nat) :
    let actual := execute bits .select target k
    let packet := match Succinct.select target bits k with | none => 0 | some i => i+1
    actual.result = some packet ∧ actual.final.status = .halted packet ∧
    actual.final.regs 513 = packet ∧
    actual.reads = ChargedSetup.setupReceipts bits ++
      ChargedSetup.targetReceipts bits
        (ChargedSetup.setupMetadata bits (initial .select target k).regs) ++
      Controller.traceReads (Allocation.readerReceipts bits target)
        (Controller.selectReference (Allocation.readStore bits target)
          (loadedMetadata bits .select target k) k).trace ∧
    actual.steps ≤ 10030 := by
  cases hs : Succinct.select target bits k <;>
    simpa only [hs, optionNatPacket, selectExecutionReceipts] using c.selectExecution bits target k

theorem public_accessSafety_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (argument : Nat) (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .access false argument
    (∀ instruction ∈ program .access, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .access).size + 1 →
      (run (Allocation.memory bits) (program .access) index
        (initial .access false argument)).final.Fits (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  c.accessSafety bits argument ha

theorem public_rankSafety_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .rank target argument
    (∀ instruction ∈ program .rank, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .rank).size + 1 →
      (run (Allocation.memory bits) (program .rank) index
        (initial .rank target argument)).final.Fits (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  c.rankSafety bits target argument ha

theorem public_selectSafety_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (target : Bool) (argument : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length) :
    let actual := execute bits .select target argument
    (∀ instruction ∈ program .select, instruction.Fits (Experiment.width bits.length)) ∧
    actual.final.Fits (Experiment.width bits.length) ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe (Experiment.width bits.length) t.before t.instruction ∧
        t.after.Fits (Experiment.width bits.length)) ∧
    (∀ index, index ≤ (source .select).size + 1 →
      (run (Allocation.memory bits) (program .select) index
        (initial .select target argument)).final.Fits (Experiment.width bits.length)) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ Experiment.width bits.length ∧
      receipt.reply = (Allocation.memory bits)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ Experiment.width bits.length)) :=
  c.selectSafety bits target argument ha

theorem public_programLengths_required (c : FullyChargedBitvectorCapstone) :
    (program .access).length = 132 ∧ (program .rank).length = 1450 ∧ (program .select).length = 10030 :=
  c.programLengths

theorem public_sourceBudgets_required (c : FullyChargedBitvectorCapstone) :
    (source .access).size + 1 = 132 ∧ (source .rank).size + 1 = 1450 ∧ (source .select).size + 1 = 10030 :=
  c.sourceBudgets

theorem public_stepsBound_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    (execute bits operation target argument).steps ≤
      (match operation with | .access => 132 | .rank => 1450 | .select => 10030) :=
  c.stepsBound bits operation target argument

theorem public_categoryPartition_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) :
    let actual := execute bits operation target argument
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  c.categoryPartition bits operation target argument

theorem public_categoryBounds_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) (category : Category) :
    (execute bits operation target argument).categoryCount category ≤
      (match operation with | .access => 132 | .rank => 1450 | .select => 10030) :=
  c.categoryBounds bits operation target argument category

theorem public_finiteScratch_required (c : FullyChargedBitvectorCapstone)
    (memory : Memory) (operation : Operation) (target : Bool) (argument fuel r : Nat)
    (hr : 8271 ≤ r) :
    (run memory (program operation) fuel (initial operation target argument)).final.regs r = 0 :=
  c.finiteScratch memory operation target argument fuel r hr

theorem public_suppliedMemoryAgreement_required (c : FullyChargedBitvectorCapstone)
    (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) (supplied : Memory)
    (hagrees : ∀ receipt ∈ (execute bits operation target argument).reads,
      supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) :
    run supplied (program operation) ((source operation).size+1) (initial operation target argument) =
      execute bits operation target argument :=
  c.suppliedMemoryAgreement bits operation target argument supplied hagrees

theorem public_validArgumentFits_required (c : FullyChargedBitvectorCapstone)
    (n argument : Nat) (ha : argument ≤ n) : argument < 2 ^ Experiment.width n :=
  c.validArgumentFits n argument ha

theorem public_inhabitant_required : FullyChargedBitvectorCapstone :=
  fullyChargedBitvectorCapstone_holds

#print axioms public_completeCapacity_required
#print axioms public_overheadLittleO_required
#print axioms public_widthBounds_required
#print axioms public_memoryWordsFit_required
#print axioms public_readerGeometry_required
#print axioms public_readerCorrect_required
#print axioms public_accessCorrect_required
#print axioms public_rankCorrect_required
#print axioms public_selectCorrect_required
#print axioms public_accessExecution_required
#print axioms public_rankExecution_required
#print axioms public_selectExecution_required
#print axioms public_accessSafety_required
#print axioms public_rankSafety_required
#print axioms public_selectSafety_required
#print axioms public_programLengths_required
#print axioms public_sourceBudgets_required
#print axioms public_stepsBound_required
#print axioms public_categoryPartition_required
#print axioms public_categoryBounds_required
#print axioms public_finiteScratch_required
#print axioms public_suppliedMemoryAgreement_required
#print axioms public_validArgumentFits_required
#print axioms public_inhabitant_required

end RMQ.PackedBitvector.PublicConsumer

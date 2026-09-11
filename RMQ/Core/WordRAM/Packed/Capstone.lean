import RMQ.Core.WordRAM.Packed.QueryObservations
import RMQ.Core.WordRAM.Packed.RankSafety

/-! # Complete contract for the fully charged packed query

The composition theorem below has an explicit remaining runtime-safety
premise. The canonical theorem must discharge it before public export.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe

/-- Every field fixes the same builder, width, fixed code, initial state and
primitive run. Logged observations are proof data, not machine scratch. -/
structure FullyChargedPackedQueryCapstone : Prop where
  allocationResidualLittleO : LittleOLinear allocationRho
  completeResidualLittleO : LittleOLinear queryCompleteRho
  widthBounds : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)
  dataCapacity : ∀ xs : List Int, (buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length
  completeCapacity : ∀ xs : List Int,
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length +
      (queryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + queryCompleteRho xs.length
  memoryWordsFit : ∀ (xs : List Int) word, word ∈ buildMemory xs → word < 2 ^ wordWidth xs.length
  allocationAddressesFit : ∀ (xs : List Int) address, address ≤ (buildMemory xs).length →
    address < 2 ^ wordWidth xs.length
  programFieldsFit : ∀ n instruction, instruction ∈ queryProgram → instruction.Fits (wordWidth n)
  budgetExact : queryBudget = 837572
  programLength : queryProgram.length = queryBudget
  encodedProgramBound : (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget
  registerCount : queryRegisterCount = 8271
  scratchCount : queryScratchWords = 8274
  unusedRegisters : ∀ (xs : List Int) left right fuel r, queryRegisterCount ≤ r →
    (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).final.regs r = 0
  validInputs : ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
  natContract : ∀ (xs : List Int) left right,
    queryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
  leftmost : ∀ (xs : List Int) left right index,
    queryNat (buildMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index
  result : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  halt : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  invalidGuard : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads = []
  stepBound : ∀ (xs : List Int) left right,
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ queryBudget
  categoryPartition : ∀ (xs : List Int) left right,
    let actual := run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  finalStateFit : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  transitionSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length)
  prefixSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ queryBudget →
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  readWidth : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
  positionalReadBacking : ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]?
  orderedLogicalRefinement : ∀ (xs : List Int) left right,
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
  logicalReadOnly : ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace
  suppliedMemoryAgreement : ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    run memory queryProgram queryBudget (initialState xs.length left right) =
      run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)

set_option maxRecDepth 3000 in
/-- The only open producer at this composition boundary is canonical runtime
safety. This theorem is not the unconditional public milestone. -/
theorem fullyChargedPackedQueryCapstone_of_runtime_safety
    (hsafe : ∀ (xs : List Int) left right,
      left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      RankExecutionSafety (buildMemory xs) (wordWidth xs.length) queryProgram queryBudget
        (initialState xs.length left right)) : FullyChargedPackedQueryCapstone where
  allocationResidualLittleO := allocationRho_littleO
  completeResidualLittleO := queryCompleteRho_littleO
  widthBounds n := ⟨wordWidth_log_lower n, wordWidth_le_log n⟩
  dataCapacity := buildMemory_capacity_le
  completeCapacity := query_complete_capacity
  memoryWordsFit := buildMemory_words_fit
  allocationAddressesFit := buildMemory_address_fit
  programFieldsFit := queryProgram_fits
  budgetExact := queryBudget_eq
  programLength := queryProgram_length
  encodedProgramBound := queryProgramWords_le
  registerCount := queryRegisterCount_eq
  scratchCount := queryScratchWords_eq
  unusedRegisters xs left right fuel r hr := queryRun_finite_registers (buildMemory xs) xs.length left right fuel r hr
  validInputs xs left right hv := ⟨valid_inputs_encode xs.length left right hv.1 hv.2,
    validEndpoints_fit xs left right hv⟩
  natContract := queryNat_exact
  leftmost := queryNat_leftmost
  result xs left right _ _ := queryRun_result xs left right
  halt xs left right _ _ := queryRun_halts xs left right
  invalidGuard xs left right _ _ hi := ⟨(queryRun_invalid (buildMemory xs) xs.length left right hi).1,
    (queryRun_invalid (buildMemory xs) xs.length left right hi).2.1⟩
  stepBound xs left right := queryRun_steps_le (buildMemory xs) xs.length left right
  categoryPartition xs left right := queryRun_categories_partition (buildMemory xs) xs.length left right
  finalStateFit xs left right hl hr := (hsafe xs left right hl hr).2.1
  transitionSafety xs left right hl hr := (hsafe xs left right hl hr).2.2.1
  prefixSafety xs left right hl hr := (hsafe xs left right hl hr).2.2.2.1
  readWidth xs left right hl hr := (hsafe xs left right hl hr).2.2.2.2
  positionalReadBacking := queryRun_read_at
  orderedLogicalRefinement := queryRun_reference_reads
  logicalReadOnly := queryTraceResult_readOnly
  suppliedMemoryAgreement := queryRun_agreement

end RMQ.SuccinctFinal.PackedWordRAM

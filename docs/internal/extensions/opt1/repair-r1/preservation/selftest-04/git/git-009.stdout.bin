import RMQ.Core.WordRAM.Optimization.Capstone

/-! # Fixed exact-type consumers for every compact certificate field

These expected propositions are frozen source, not inferred from projections.
The mutation replay keeps this file unchanged while altering the certificate
producer. Both a generic certificate and its canonical inhabitant are consumed.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers

open Cartesian Structured SuccinctSpace PackedCellProbe

theorem allocationResidualLittleO_expectedType (certificate : CompactPackedQueryCapstone) :
    LittleOLinear allocationRho :=
  certificate.allocationResidualLittleO

theorem allocationResidualLittleO_canonical :
    LittleOLinear allocationRho :=
  allocationResidualLittleO_expectedType compactPackedQueryCapstone_holds

theorem completeResidualLittleO_expectedType (certificate : CompactPackedQueryCapstone) :
    LittleOLinear compactQueryCompleteRho :=
  certificate.completeResidualLittleO

theorem completeResidualLittleO_canonical :
    LittleOLinear compactQueryCompleteRho :=
  completeResidualLittleO_expectedType compactPackedQueryCapstone_holds

theorem widthBounds_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) :=
  certificate.widthBounds

theorem widthBounds_canonical :
    ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) :=
  widthBounds_expectedType compactPackedQueryCapstone_holds

theorem dataCapacity_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ xs : List Int, (buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length :=
  certificate.dataCapacity

theorem dataCapacity_canonical :
    ∀ xs : List Int, (buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length :=
  dataCapacity_expectedType compactPackedQueryCapstone_holds

theorem completeCapacity_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ xs : List Int,
    ((buildMemory xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + compactQueryCompleteRho xs.length :=
  certificate.completeCapacity

theorem completeCapacity_canonical :
    ∀ xs : List Int,
    ((buildMemory xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + compactQueryCompleteRho xs.length :=
  completeCapacity_expectedType compactPackedQueryCapstone_holds

theorem memoryWordsFit_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) word, word ∈ buildMemory xs → word < 2 ^ wordWidth xs.length :=
  certificate.memoryWordsFit

theorem memoryWordsFit_canonical :
    ∀ (xs : List Int) word, word ∈ buildMemory xs → word < 2 ^ wordWidth xs.length :=
  memoryWordsFit_expectedType compactPackedQueryCapstone_holds

theorem allocationAddressesFit_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) address, address ≤ (buildMemory xs).length →
    address < 2 ^ wordWidth xs.length :=
  certificate.allocationAddressesFit

theorem allocationAddressesFit_canonical :
    ∀ (xs : List Int) address, address ≤ (buildMemory xs).length →
    address < 2 ^ wordWidth xs.length :=
  allocationAddressesFit_expectedType compactPackedQueryCapstone_holds

theorem programFieldsFit_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ n instruction, instruction ∈ compactQueryProgram → instruction.Fits (wordWidth n) :=
  certificate.programFieldsFit

theorem programFieldsFit_canonical :
    ∀ n instruction, instruction ∈ compactQueryProgram → instruction.Fits (wordWidth n) :=
  programFieldsFit_expectedType compactPackedQueryCapstone_holds

theorem budgetExact_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryBudget = 151978 :=
  certificate.budgetExact

theorem budgetExact_canonical :
    compactQueryBudget = 151978 :=
  budgetExact_expectedType compactPackedQueryCapstone_holds

theorem programLength_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryProgram.length = 212964 :=
  certificate.programLength

theorem programLength_canonical :
    compactQueryProgram.length = 212964 :=
  programLength_expectedType compactPackedQueryCapstone_holds

theorem encodedProgramLength_expectedType (certificate : CompactPackedQueryCapstone) :
    (compactQueryProgram.map Instruction.encoding).flatten.length =
    722339 :=
  certificate.encodedProgramLength

theorem encodedProgramLength_canonical :
    (compactQueryProgram.map Instruction.encoding).flatten.length =
    722339 :=
  encodedProgramLength_expectedType compactPackedQueryCapstone_holds

theorem programReduction_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryProgram.length < queryProgram.length :=
  certificate.programReduction

theorem programReduction_canonical :
    compactQueryProgram.length < queryProgram.length :=
  programReduction_expectedType compactPackedQueryCapstone_holds

theorem emittedProgram_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryProgram = compactAt compactQuerySource compactQueryFresh 0 0 :=
  certificate.emittedProgram

theorem emittedProgram_canonical :
    compactQueryProgram = compactAt compactQuerySource compactQueryFresh 0 0 :=
  emittedProgram_expectedType compactPackedQueryCapstone_holds

theorem originalExecutionBound_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ memory n left right, (queryRun memory n left right).steps ≤ 150739 :=
  certificate.originalExecutionBound

theorem originalExecutionBound_canonical :
    ∀ memory n left right, (queryRun memory n left right).steps ≤ 150739 :=
  originalExecutionBound_expectedType compactPackedQueryCapstone_holds

theorem originalReducedFuel_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ memory n left right,
    run memory queryProgram 150739 (initialState n left right) = queryRun memory n left right :=
  certificate.originalReducedFuel

theorem originalReducedFuel_canonical :
    ∀ memory n left right,
    run memory queryProgram 150739 (initialState n left right) = queryRun memory n left right :=
  originalReducedFuel_expectedType compactPackedQueryCapstone_holds

theorem arbitraryMemoryObservations_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ memory n left right,
    (compactQueryRun memory n left right).result = (queryRun memory n left right).result ∧
    (compactQueryRun memory n left right).reads = (queryRun memory n left right).reads :=
  certificate.arbitraryMemoryObservations

theorem arbitraryMemoryObservations_canonical :
    ∀ memory n left right,
    (compactQueryRun memory n left right).result = (queryRun memory n left right).result ∧
    (compactQueryRun memory n left right).reads = (queryRun memory n left right).reads :=
  arbitraryMemoryObservations_expectedType compactPackedQueryCapstone_holds

theorem registerCount_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryRegisterCount = 8273 :=
  certificate.registerCount

theorem registerCount_canonical :
    compactQueryRegisterCount = 8273 :=
  registerCount_expectedType compactPackedQueryCapstone_holds

theorem scratchCount_expectedType (certificate : CompactPackedQueryCapstone) :
    compactQueryScratchWords = 8276 :=
  certificate.scratchCount

theorem scratchCount_canonical :
    compactQueryScratchWords = 8276 :=
  scratchCount_expectedType compactPackedQueryCapstone_holds

theorem unusedRegisters_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right fuel r, compactQueryRegisterCount ≤ r →
    (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.regs r = 0 :=
  certificate.unusedRegisters

theorem unusedRegisters_canonical :
    ∀ (xs : List Int) left right fuel r, compactQueryRegisterCount ≤ r →
    (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.regs r = 0 :=
  unusedRegisters_expectedType compactPackedQueryCapstone_holds

theorem validInputs_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length :=
  certificate.validInputs

theorem validInputs_canonical :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length :=
  validInputs_expectedType compactPackedQueryCapstone_holds

theorem natContract_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    compactQueryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  certificate.natContract

theorem natContract_canonical :
    ∀ (xs : List Int) left right,
    compactQueryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  natContract_expectedType compactPackedQueryCapstone_holds

theorem leftmost_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right index,
    compactQueryNat (buildMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index :=
  certificate.leftmost

theorem leftmost_canonical :
    ∀ (xs : List Int) left right index,
    compactQueryNat (buildMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index :=
  leftmost_expectedType compactPackedQueryCapstone_holds

theorem result_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  certificate.result

theorem result_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  result_expectedType compactPackedQueryCapstone_holds

theorem halt_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  certificate.halt

theorem halt_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  halt_expectedType compactPackedQueryCapstone_holds

theorem invalidGuard_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads = [] :=
  certificate.invalidGuard

theorem invalidGuard_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads = [] :=
  invalidGuard_expectedType compactPackedQueryCapstone_holds

theorem stepBound_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).steps ≤ compactQueryBudget :=
  certificate.stepBound

theorem stepBound_canonical :
    ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).steps ≤ compactQueryBudget :=
  stepBound_expectedType compactPackedQueryCapstone_holds

theorem categoryPartition_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    let actual := run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  certificate.categoryPartition

theorem categoryPartition_canonical :
    ∀ (xs : List Int) left right,
    let actual := run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  categoryPartition_expectedType compactPackedQueryCapstone_holds

theorem finalStateFit_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  certificate.finalStateFit

theorem finalStateFit_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  finalStateFit_expectedType compactPackedQueryCapstone_holds

theorem transitionSafety_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length) :=
  certificate.transitionSafety

theorem transitionSafety_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length) :=
  transitionSafety_expectedType compactPackedQueryCapstone_holds

theorem prefixSafety_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ compactQueryBudget →
      (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  certificate.prefixSafety

theorem prefixSafety_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ compactQueryBudget →
      (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  prefixSafety_expectedType compactPackedQueryCapstone_holds

theorem readWidth_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  certificate.readWidth

theorem readWidth_canonical :
    ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  readWidth_expectedType compactPackedQueryCapstone_holds

theorem positionalReadBacking_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (buildMemory xs) compactQueryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ compactQueryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]? :=
  certificate.positionalReadBacking

theorem positionalReadBacking_canonical :
    ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (buildMemory xs) compactQueryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ compactQueryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]? :=
  positionalReadBacking_expectedType compactPackedQueryCapstone_holds

theorem orderedLogicalRefinement_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] :=
  certificate.orderedLogicalRefinement

theorem orderedLogicalRefinement_canonical :
    ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] :=
  orderedLogicalRefinement_expectedType compactPackedQueryCapstone_holds

theorem logicalReadOnly_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace :=
  certificate.logicalReadOnly

theorem logicalReadOnly_canonical :
    ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace :=
  logicalReadOnly_expectedType compactPackedQueryCapstone_holds

theorem suppliedMemoryAgreement_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    run memory compactQueryProgram compactQueryBudget (initialState xs.length left right) =
      run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right) :=
  certificate.suppliedMemoryAgreement

theorem suppliedMemoryAgreement_canonical :
    ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    run memory compactQueryProgram compactQueryBudget (initialState xs.length left right) =
      run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right) :=
  suppliedMemoryAgreement_expectedType compactPackedQueryCapstone_holds

theorem specResult_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1) :=
  certificate.specResult

theorem specResult_canonical :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1) :=
  specResult_expectedType compactPackedQueryCapstone_holds

theorem noFailedLoads_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value :=
  certificate.noFailedLoads

theorem noFailedLoads_canonical :
    ∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value :=
  noFailedLoads_expectedType compactPackedQueryCapstone_holds

theorem completedExecution_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ memory n left right,
    (compactQueryRun memory n left right).final.status ≠ .running :=
  certificate.completedExecution

theorem completedExecution_canonical :
    ∀ memory n left right,
    (compactQueryRun memory n left right).final.status ≠ .running :=
  completedExecution_expectedType compactPackedQueryCapstone_holds

theorem adequateFuel_expectedType (certificate : CompactPackedQueryCapstone) :
    ∀ memory n left right fuel, compactQueryBudget ≤ fuel →
    run memory compactQueryProgram fuel (initialState n left right) =
      compactQueryRun memory n left right :=
  certificate.adequateFuel

theorem adequateFuel_canonical :
    ∀ memory n left right fuel, compactQueryBudget ≤ fuel →
    run memory compactQueryProgram fuel (initialState n left right) =
      compactQueryRun memory n left right :=
  adequateFuel_expectedType compactPackedQueryCapstone_holds

end RMQ.SuccinctFinal.PackedWordRAM.Optimization.CertificateConsumers

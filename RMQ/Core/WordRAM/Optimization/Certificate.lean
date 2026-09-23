import RMQ.Core.WordRAM.Optimization.QueryProof
import RMQ.Core.WordRAM.Optimization.QuerySafety
import RMQ.Core.WordRAM.Packed.QueryObservations

/-! # Exact compact-query certificate field contract

Every field fixes the actual compact emitter, run, original allocation and
one query-independent word width. The cost field is discharged through the
compiler simulation; space includes literal code words and the finite bank.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization

open Cartesian Structured SuccinctSpace PackedCellProbe

structure CompactPackedQueryCapstone : Prop where
  -- OPT1-REPLAY-FIELDS-BEGIN
  allocationResidualLittleO : LittleOLinear allocationRho
  completeResidualLittleO : LittleOLinear compactQueryCompleteRho
  widthBounds : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)
  dataCapacity : ∀ xs : List Int, (buildMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length
  completeCapacity : ∀ xs : List Int,
    ((buildMemory xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length +
      (compactQueryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + compactQueryCompleteRho xs.length
  memoryWordsFit : ∀ (xs : List Int) word, word ∈ buildMemory xs → word < 2 ^ wordWidth xs.length
  allocationAddressesFit : ∀ (xs : List Int) address, address ≤ (buildMemory xs).length →
    address < 2 ^ wordWidth xs.length
  programFieldsFit : ∀ n instruction, instruction ∈ compactQueryProgram → instruction.Fits (wordWidth n)
  budgetExact : compactQueryBudget = 151978
  programLength : compactQueryProgram.length = 212964
  encodedProgramLength : (compactQueryProgram.map Instruction.encoding).flatten.length =
    722339
  programReduction : compactQueryProgram.length < queryProgram.length
  emittedProgram : compactQueryProgram = compactAt compactQuerySource compactQueryFresh 0 0
  originalExecutionBound : ∀ memory n left right, (queryRun memory n left right).steps ≤ 150739
  originalReducedFuel : ∀ memory n left right,
    run memory queryProgram 150739 (initialState n left right) = queryRun memory n left right
  arbitraryMemoryObservations : ∀ memory n left right,
    (compactQueryRun memory n left right).result = (queryRun memory n left right).result ∧
    (compactQueryRun memory n left right).reads = (queryRun memory n left right).reads
  completedExecution : ∀ memory n left right,
    (compactQueryRun memory n left right).final.status ≠ .running
  adequateFuel : ∀ memory n left right fuel, compactQueryBudget ≤ fuel →
    run memory compactQueryProgram fuel (initialState n left right) =
      compactQueryRun memory n left right
  registerCount : compactQueryRegisterCount = 8273
  scratchCount : compactQueryScratchWords = 8276
  unusedRegisters : ∀ (xs : List Int) left right fuel r, compactQueryRegisterCount ≤ r →
    (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.regs r = 0
  validInputs : ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
  natContract : ∀ (xs : List Int) left right,
    compactQueryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
  leftmost : ∀ (xs : List Int) left right index,
    compactQueryNat (buildMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index
  result : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  halt : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  invalidGuard : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads = []
  stepBound : ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).steps ≤ compactQueryBudget
  categoryPartition : ∀ (xs : List Int) left right,
    let actual := run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  finalStateFit : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  transitionSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length)
  prefixSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ compactQueryBudget →
      (run (buildMemory xs) compactQueryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  readWidth : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
  positionalReadBacking : ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (buildMemory xs) compactQueryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ compactQueryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]?
  orderedLogicalRefinement : ∀ (xs : List Int) left right,
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
  logicalReadOnly : ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace
  suppliedMemoryAgreement : ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    run memory compactQueryProgram compactQueryBudget (initialState xs.length left right) =
      run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)
  specResult : ∀ (xs : List Int) left right, ValidRange xs left right →
    (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1)
  noFailedLoads : ∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (buildMemory xs) compactQueryProgram compactQueryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value
  -- OPT1-REPLAY-FIELDS-END

end RMQ.SuccinctFinal.PackedWordRAM.Optimization

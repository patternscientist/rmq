import RMQPaper

/-! Independent expected-type consumers for the fully charged public theorem.

These propositions are a frozen client contract. Each named check depends on
the actual public proof alias and explicitly fixes the counted allocation and
the executed program. The replay runner weakens one producer field at a time
and requires rejection at the corresponding declaration below.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM.ContractChecks

open Structured SuccinctSpace PackedCellProbe

theorem publicContract : FullyChargedPackedQueryCapstone :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery

theorem publicProposition : RMQ.Headlines.SuccinctRMQFullyChargedPackedQuery =
    FullyChargedPackedQueryCapstone := rfl

theorem checkC01 : LittleOLinear allocationRho :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.allocationResidualLittleO

theorem checkC02 : LittleOLinear queryCompleteRho :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.completeResidualLittleO

theorem checkC03 (n : Nat) :
    Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
      wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.widthBounds n

theorem checkC04 (xs : List Int) :
    (buildMemory xs).length * wordWidth xs.length ≤
      2 * xs.length + allocationRho xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.dataCapacity xs

theorem checkC05 (xs : List Int) :
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length +
      (queryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + queryCompleteRho xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.completeCapacity xs

theorem checkC06 (xs : List Int) (word : Nat) (h : word ∈ buildMemory xs) :
    word < 2 ^ wordWidth xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.memoryWordsFit xs word h

theorem checkC07 (xs : List Int) (address : Nat)
    (h : address ≤ (buildMemory xs).length) : address < 2 ^ wordWidth xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.allocationAddressesFit xs address h

theorem checkC08 (n : Nat) (instruction : Instruction) (h : instruction ∈ queryProgram) :
    instruction.Fits (wordWidth n) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.programFieldsFit n instruction h

theorem checkC09 : queryBudget = 837572 :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.budgetExact

theorem checkC10 : queryProgram.length = queryBudget :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.programLength

theorem checkC11 : (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.encodedProgramBound

theorem checkC12 : queryRegisterCount = 8271 :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.registerCount

theorem checkC13 : queryScratchWords = 8274 :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.scratchCount

theorem checkC14 (xs : List Int) (left right fuel r : Nat) (h : queryRegisterCount ≤ r) :
    (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).final.regs r = 0 :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.unusedRegisters xs left right fuel r h

theorem checkC15 (xs : List Int) (left right : Nat) (h : ValidRange xs left right) :
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.validInputs xs left right h

theorem checkC16 (xs : List Int) (left right : Nat) :
    queryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.natContract xs left right

theorem checkC17 (xs : List Int) (left right index : Nat)
    (h : queryNat (buildMemory xs) xs.length left right = some index) :
    LeftmostArgMin xs left right index :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.leftmost xs left right index h

theorem checkC18 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.result xs left right hl hr

theorem checkC19 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.halt xs left right hl hr

theorem checkC20 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (hi : ¬ ValidRange xs left right) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads = [] :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.invalidGuard xs left right hl hr hi

theorem checkC21 (xs : List Int) (left right : Nat) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ queryBudget :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.stepBound xs left right

theorem checkC22 (xs : List Int) (left right : Nat) :
    let actual := run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.categoryPartition xs left right

theorem checkC23 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.Fits
      (wordWidth xs.length) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.finalStateFit xs left right hl hr

theorem checkC24 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : Transition)
    (h : (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).transitions[index]? = some t) :
    Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
      t.after.Fits (wordWidth xs.length) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.transitionSafety xs left right hl hr index t h

theorem checkC25 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (fuel : Nat) (h : fuel ≤ queryBudget) :
    (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).final.Fits
      (wordWidth xs.length) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.prefixSafety xs left right hl hr fuel h

theorem checkC26 (xs : List Int) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (index : Nat) (t : Transition) (receipt : Receipt)
    (ht : (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).transitions[index]? = some t)
    (hrc : t.receipt = some receipt) :
    receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (buildMemory xs)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.readWidth xs left right hl hr index t receipt ht hrc

theorem checkC27 (xs : List Int) (left right index : Nat) (t : Transition) (receipt : Receipt)
    (ht : (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).transitions[index]? = some t)
    (hrc : t.receipt = some receipt) :
    t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]? :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.positionalReadBacking xs left right index t receipt ht hrc

theorem checkC28 (xs : List Int) (left right : Nat) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.orderedLogicalRefinement xs left right

theorem checkC29 (xs : List Int) (left right : Nat) :
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.logicalReadOnly xs left right

theorem checkC30 (xs : List Int) (memory : Memory) (left right : Nat)
    (h : ∀ receipt ∈ (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) :
    run memory queryProgram queryBudget (initialState xs.length left right) =
      run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.suppliedMemoryAgreement xs memory left right h

end RMQ.SuccinctFinal.PackedWordRAM.ContractChecks

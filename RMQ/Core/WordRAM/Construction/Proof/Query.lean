import RMQ.Core.WordRAM.Packed.Capstone
import RMQ.Core.WordRAM.Construction.Proof.Exact

/-! # PRE-1 join: the accepted packed query on the emitted cells (stage S8)

Outside the builder firewall. `PackedQueryOn memory xs` restates, for one input
list `xs` and one numeric memory `memory`, every field of
`PackedWordRAM.FullyChargedPackedQueryCapstone` that mentions the allocation,
with `buildMemory xs` replaced by `memory`. `packedQueryOn_of_eq` transports the
accepted capstone along a list equality, and `packedQueryOn_efficientBuild` and
`packedQueryOn_efficientBuildWord` instantiate it at the builder's emitted cells
through the two exactness theorems. `constructionCompleteRho` joins the
builder's two code accounts and a 400-register scratch bank with the query's
code and scratch accounts in the same little-o residual as PQ1.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

open RMQ.SuccinctFinal.PackedWordRAM hiding State Registers Transition Memory Status Run run Instruction execute
  Program initialState

/-- The accepted query's per-input facts on a given numeric memory. -/
structure PackedQueryOn (memory : List Nat) (xs : List Int) : Prop where
  dataCapacity : memory.length * wordWidth xs.length ≤ 2 * xs.length + allocationRho xs.length
  completeCapacity :
    (memory.length + (queryProgram.map PackedWordRAM.Instruction.encoding).flatten.length +
      (queryRegisterCount + 3)) * wordWidth xs.length ≤ 2 * xs.length + queryCompleteRho xs.length
  memoryWordsFit : ∀ word, word ∈ memory → word < 2 ^ wordWidth xs.length
  allocationAddressesFit : ∀ address, address ≤ memory.length → address < 2 ^ wordWidth xs.length
  unusedRegisters : ∀ left right fuel r, queryRegisterCount ≤ r →
    (PackedWordRAM.run memory queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.regs r = 0
  natContract : ∀ left right,
    queryNat memory xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
  leftmost : ∀ left right index,
    queryNat memory xs.length left right = some index → LeftmostArgMin xs left right index
  result : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  halt : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  invalidGuard : ∀ left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result = some 0 ∧
      (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads = []
  stepBound : ∀ left right,
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ queryBudget
  categoryPartition : ∀ left right,
    let actual := PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  finalStateFit : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.Fits
      (wordWidth xs.length)
  transitionSafety : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : PackedWordRAM.Transition),
      (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
        some t →
      PackedWordRAM.Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length)
  prefixSafety : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ queryBudget →
      (PackedWordRAM.run memory queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.Fits
        (wordWidth xs.length)
  readWidth : ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : PackedWordRAM.Transition) (receipt : Receipt),
      (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
        some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = memory[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
  positionalReadBacking : ∀ left right index (t : PackedWordRAM.Transition) (receipt : Receipt),
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
      some t →
    t.receipt = some receipt →
    t.before = (PackedWordRAM.run memory queryProgram index (PackedWordRAM.initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      PackedWordRAM.execute memory t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = memory[receipt.address]?
  orderedLogicalRefinement : ∀ left right,
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) memory
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
  suppliedMemoryAgreement : ∀ (other : PackedWordRAM.Memory) left right,
    (∀ receipt ∈ (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
      other[receipt.address]? = memory[receipt.address]?) →
    PackedWordRAM.run other queryProgram queryBudget (PackedWordRAM.initialState xs.length left right) =
      PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)
  specResult : ∀ left right, ValidRange xs left right →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1)
  noFailedLoads : ∀ left right, ValidRange xs left right →
    ∀ receipt ∈ (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value
  invalidGuardSteps : ∀ left right, ¬ ValidRange xs left right →
    (PackedWordRAM.run memory queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ 6

/-- The accepted capstone, at one list, on any memory equal to its allocation. -/
theorem packedQueryOn_of_eq (xs : List Int) (memory : List Nat) (h : memory = buildMemory xs) :
    PackedQueryOn memory xs := by
  subst h
  have c := fullyChargedPackedQueryCapstone_holds
  exact
    { dataCapacity := c.dataCapacity xs
      completeCapacity := c.completeCapacity xs
      memoryWordsFit := c.memoryWordsFit xs
      allocationAddressesFit := c.allocationAddressesFit xs
      unusedRegisters := c.unusedRegisters xs
      natContract := c.natContract xs
      leftmost := c.leftmost xs
      result := c.result xs
      halt := c.halt xs
      invalidGuard := c.invalidGuard xs
      stepBound := c.stepBound xs
      categoryPartition := c.categoryPartition xs
      finalStateFit := c.finalStateFit xs
      transitionSafety := c.transitionSafety xs
      prefixSafety := c.prefixSafety xs
      readWidth := c.readWidth xs
      positionalReadBacking := c.positionalReadBacking xs
      orderedLogicalRefinement := c.orderedLogicalRefinement xs
      suppliedMemoryAgreement := c.suppliedMemoryAgreement xs
      specResult := c.specResult xs
      noFailedLoads := c.noFailedLoads xs
      invalidGuardSteps := c.invalidGuardSteps xs }

/-- **The accepted query on the comparison-oracle builder's emitted cells.** -/
theorem packedQueryOn_efficientBuild (xs : List Int) : PackedQueryOn (efficientBuild xs) xs :=
  packedQueryOn_of_eq xs _ (Proof.efficientBuild_eq_buildMemory xs)

/-- **The accepted query on the word-model builder's emitted cells.** -/
theorem packedQueryOn_efficientBuildWord (xs : List Int) (h : InputFits (wordWidth xs.length) xs) :
    PackedQueryOn (efficientBuildWord (wordWidth xs.length) xs) xs :=
  packedQueryOn_of_eq xs _ (Proof.efficientBuildWord_eq_buildMemory xs h)

/-- Retained-space residual with the query's and both builder constants' code
and the query's and a 400-register builder scratch bank. -/
def constructionCompleteRho : Nat → Nat :=
  allocationWithMachineRho (queryProgramWords + 8079 + 8089) (queryScratchWords + 400)

theorem constructionCompleteRho_littleO : SuccinctSpace.LittleOLinear constructionCompleteRho :=
  allocationWithMachineRho_littleO _ _

/-- **Joint code account.** -/
theorem construction_complete_capacity (xs : List Int) :
    ((buildMemory xs).length + (queryProgramWords + programWords builderProgram + programWords builderProgramWord) +
      (queryScratchWords + 400)) * wordWidth xs.length ≤ 2 * xs.length + constructionCompleteRho xs.length := by
  rw [Proof.builderProgram_programWords, Proof.builderProgramWord_programWords]
  exact buildMemory_with_machine_capacity_le xs _ _

end RMQ.SuccinctFinal.PackedConstruction

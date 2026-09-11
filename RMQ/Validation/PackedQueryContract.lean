import RMQPaper

/-! Independent expected-type consumers for the fully charged public theorem.

These propositions are a frozen client contract. Each named check depends on
the actual public proof alias and explicitly fixes the counted allocation and
the executed program. The replay runner weakens one producer field at a time
and requires rejection at the corresponding declaration below; its
definition-collapse cases change one pinned definition and require rejection
at the matching pin.
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

theorem checkC31 (xs : List Int) (left right : Nat) (h : ValidRange xs left right) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1) :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.specResult xs left right h

theorem checkC32 (xs : List Int) (left right : Nat) (h : ValidRange xs left right)
    (receipt : Receipt)
    (hr : receipt ∈ (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).reads) :
    ∃ value, receipt.reply = some value :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.noFailedLoads xs left right h receipt hr

theorem checkC33 (xs : List Int) (left right : Nat) (h : ¬ ValidRange xs left right) :
    (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ 6 :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.invalidGuardSteps xs left right h

/-! ## Definitional pins

A field check above restates a field in the producer's own vocabulary, so a
definition changed in the producer would change the check with it. Each pin
below independently spells out the complete body of one definition reachable
from the field types and is proved by definitional unfolding alone, so changing
that definition turns the pin into a type error. Definitions not pinned here are
fixed by the fields themselves; PQ1_VALIDATION_PLAN.md lists both classes. -/

theorem pinMemory : Memory = List Nat := rfl

theorem pinRegisters : Registers = (Nat → Nat) := rfl

theorem pinProgram : Program = List Instruction := rfl

theorem pinStateShape (s : State) : s = ⟨s.regs, s.pc, s.status⟩ := rfl

theorem pinReceiptShape (receipt : Receipt) : receipt = ⟨receipt.address, receipt.reply⟩ := rfl

theorem pinTransitionShape (t : Transition) :
    t = ⟨t.before, t.instruction, t.after, t.receipt⟩ := rfl

theorem pinRunShape (r : Run) : r = ⟨r.final, r.transitions⟩ := rfl

theorem pinRegistersWrite (regs : Registers) (dst value r : Nat) :
    regs.write dst value r = if r = dst then value else regs r := rfl

theorem pinArithmeticEval (op : Arithmetic) (x y : Nat) :
    op.eval x y =
      match op with
      | .add => x + y
      | .sub => x - y
      | .mul => x * y
      | .div => x / y
      | .mod => x % y
      | .shl => Nat.shiftLeft x y
      | .shr => Nat.shiftRight x y
      | .band => Nat.land x y
      | .bor => Nat.lor x y
      | .bxor => Nat.xor x y := by
  cases op <;> rfl

theorem pinComparisonEval (op : Comparison) (x y : Nat) :
    op.eval x y =
      match op with
      | .lt => if x < y then 1 else 0
      | .le => if x ≤ y then 1 else 0
      | .eq => if x = y then 1 else 0 := by
  cases op <;> rfl

theorem pinArithmeticCode (op : Arithmetic) :
    op.code =
      match op with
      | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
      | .shl => 5 | .shr => 6 | .band => 7 | .bor => 8 | .bxor => 9 := rfl

theorem pinComparisonCode (op : Comparison) :
    op.code = match op with | .lt => 0 | .le => 1 | .eq => 2 := rfl

theorem pinInstructionCategory (i : Instruction) :
    i.category =
      match i with
      | .load .. => .memoryRead
      | .constant .. => .registerWrite
      | .move .. => .registerWrite
      | .arithmetic .. => .arithmetic
      | .comparison .. => .comparison
      | .jump .. => .branch
      | .jumpRegister .. => .branch
      | .branchZero .. => .branch
      | .halt .. => .control := rfl

theorem pinInstructionOperands (i : Instruction) :
    i.operands =
      match i with
      | .load dst address => [dst, address]
      | .constant dst value => [dst, value]
      | .move dst src => [dst, src]
      | .arithmetic _ dst lhs rhs => [dst, lhs, rhs]
      | .comparison _ dst lhs rhs => [dst, lhs, rhs]
      | .jump target => [target]
      | .jumpRegister src => [src]
      | .branchZero condition target => [condition, target]
      | .halt src => [src] := by
  cases i <;> rfl

theorem pinInstructionEncoding (i : Instruction) :
    i.encoding =
      (match i with
       | .load .. => [0]
       | .constant .. => [1]
       | .move .. => [2]
       | .arithmetic op .. => [3, op.code]
       | .comparison op .. => [4, op.code]
       | .jump .. => [5]
       | .jumpRegister .. => [6]
       | .branchZero .. => [7]
       | .halt .. => [8]) ++ i.operands := rfl

theorem pinInstructionFits (width : Nat) (i : Instruction) :
    i.Fits width = ∀ operand ∈ i.encoding, operand < 2 ^ width := rfl

theorem pinStateWriteNext (s : State) (dst value : Nat) :
    s.writeNext dst value = ⟨s.regs.write dst value, s.pc + 1, .running⟩ := rfl

theorem pinExecute (memory : Memory) (i : Instruction) (s : State) :
    execute memory i s =
      match i with
      | .load dst address =>
          (match memory[s.regs address]? with
            | some value => s.writeNext dst value
            | none => { s with status := .fault },
            some ⟨s.regs address, memory[s.regs address]?⟩)
      | .constant dst value => (s.writeNext dst value, none)
      | .move dst src => (s.writeNext dst (s.regs src), none)
      | .arithmetic op dst lhs rhs => (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs)), none)
      | .comparison op dst lhs rhs => (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs)), none)
      | .jump target => ({ s with pc := target }, none)
      | .jumpRegister src => ({ s with pc := s.regs src }, none)
      | .branchZero condition target =>
          ({ s with pc := if s.regs condition = 0 then target else s.pc + 1 }, none)
      | .halt src => ({ s with status := .halted (s.regs src) }, none) := rfl

theorem pinStep (memory : Memory) (program : Program) (s : State) :
    step memory program s =
      match s.status with
      | .running =>
          match program[s.pc]? with
          | none => none
          | some i => some ⟨s, i, (execute memory i s).1, (execute memory i s).2⟩
      | _ => none := rfl

theorem pinRunZero (memory : Memory) (program : Program) (s : State) :
    run memory program 0 s = ⟨s, []⟩ := rfl

theorem pinRunSucc (memory : Memory) (program : Program) (fuel : Nat) (s : State) :
    run memory program (fuel + 1) s =
      match step memory program s with
      | none => ⟨s, []⟩
      | some t => ⟨(run memory program fuel t.after).final,
          t :: (run memory program fuel t.after).transitions⟩ := rfl

theorem pinRunReads (r : Run) : r.reads = r.transitions.filterMap (·.receipt) := rfl

theorem pinRunCategories (r : Run) :
    r.categories = r.transitions.map (·.instruction.category) := rfl

theorem pinRunSteps (r : Run) : r.steps = r.transitions.length := rfl

theorem pinRunResult (r : Run) :
    r.result = match r.final.status with | .halted value => some value | _ => none := rfl

theorem pinRunCategoryCount (r : Run) (c : Category) :
    r.categoryCount c = r.categories.count c := rfl

theorem pinStateFits (width : Nat) (s : State) :
    s.Fits width = (s.pc < 2 ^ width ∧ (∀ r, s.regs r < 2 ^ width) ∧
      (∀ value, s.status = .halted value → value < 2 ^ width)) := rfl

theorem pinInstructionSafe (width : Nat) (s : State) (i : Instruction) :
    Instruction.Safe width s i =
      (i.Fits width ∧ s.Fits width ∧
        match i with
        | .arithmetic op _ lhs rhs =>
            op.eval (s.regs lhs) (s.regs rhs) < 2 ^ width ∧
            (op = .sub → s.regs rhs ≤ s.regs lhs) ∧
            (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
            (op = .shl ∨ op = .shr → s.regs rhs < width)
        | _ => True) := rfl

theorem pinInputRegisters (n left right : Nat) :
    inputRegisters n left right =
      Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n := rfl

theorem pinInitialState (n left right : Nat) :
    initialState n left right = ⟨inputRegisters n left right, 0, .running⟩ := rfl

theorem pinEncodeInputs (n left right : Nat) :
    encodeInputs n left right =
      if left < 2 ^ wordWidth n ∧ right < 2 ^ wordWidth n then
        some (initialState n left right)
      else none := rfl

theorem pinQueryNat (memory : Memory) (n left right : Nat) :
    queryNat memory n left right =
      match encodeInputs n left right with
      | none => none
      | some state =>
          ((run memory queryProgram queryBudget state).result).bind fun packet =>
            if packet = 0 then none else some (packet - 1) := rfl

theorem pinValidRange (xs : List Int) (left right : Nat) :
    ValidRange xs left right = (left < right ∧ right ≤ xs.length) := rfl

theorem pinLeftmostArgMin (xs : List Int) (left right idx : Nat) :
    LeftmostArgMin xs left right idx =
      (left < right ∧ right ≤ xs.length ∧ left ≤ idx ∧ idx < right ∧
        ∃ v, xs[idx]? = some v ∧
          (∀ j w, left ≤ j → j < right → xs[j]? = some w → v ≤ w) ∧
          (∀ j w, left ≤ j → j < idx → xs[j]? = some w → v < w)) := rfl

theorem pinOptionNatPacket (value : Option Nat) :
    optionNatPacket value = (value.map (· + 1)).getD 0 := rfl

theorem pinLittleOLinear (f : Nat → Nat) :
    LittleOLinear f =
      ∀ scale : Nat, 0 < scale → ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n → scale * f n ≤ n :=
  rfl

theorem pinReadOnlyTrace (trace : List WordRAM.TraceEvent) :
    ReadOnlyTrace trace = ∀ event ∈ trace, event.isReadWord := rfl

theorem pinIsReadWord (event : WordRAM.TraceEvent) :
    event.isReadWord =
      match event with
      | .readWord .. => True
      | .wordRank .. => False
      | .wordSelect .. => False
      | .syntheticCostOnlyPrimitive => False := rfl

/-! ## Negative controls for encoded-field fit

At the width used for the empty list, an operand equal to the word capacity is
rejected in a register field, a jump target and an immediate, while the largest
representable immediate is accepted. -/

theorem fitsRejectsOversizedRegister :
    ¬ (Instruction.move (2 ^ wordWidth 0) 0).Fits (wordWidth 0) := by
  intro h
  exact Nat.lt_irrefl _ (h (2 ^ wordWidth 0) (by simp [Instruction.encoding, Instruction.operands]))

theorem fitsRejectsOversizedJumpTarget :
    ¬ (Instruction.jump (2 ^ wordWidth 0)).Fits (wordWidth 0) := by
  intro h
  exact Nat.lt_irrefl _ (h (2 ^ wordWidth 0) (by simp [Instruction.encoding, Instruction.operands]))

theorem fitsRejectsOversizedImmediate :
    ¬ (Instruction.constant 0 (2 ^ wordWidth 0)).Fits (wordWidth 0) := by
  intro h
  exact Nat.lt_irrefl _ (h (2 ^ wordWidth 0) (by simp [Instruction.encoding, Instruction.operands]))

theorem fitsAcceptsLargestImmediate :
    (Instruction.constant 0 (2 ^ wordWidth 0 - 1)).Fits (wordWidth 0) := by
  have hw : 2 ^ 32 ≤ 2 ^ wordWidth 0 :=
    Nat.pow_le_pow_right (by decide) (by unfold wordWidth; omega)
  have hlarge : 2 < 2 ^ 32 := by decide
  intro operand h
  simp only [Instruction.encoding, Instruction.operands, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> subst h <;> omega

end RMQ.SuccinctFinal.PackedWordRAM.ContractChecks

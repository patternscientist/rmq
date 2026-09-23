import RMQ.Core.WordRAM.Packed.AllocationLowerBound

/-!
# Independent consumers and executable controls for variable packed payloads

The propositions below are literal frozen expected types. They are not obtained
from producer definitions during replay. Every advertised field is projected
from the named optimality theorem, including all reconstructed-machine fields.
Runtime cases invoke the actual new serialization and payload-only decoder.
-/

namespace RMQ.Validation.VariablePayloadLowerBound

open RMQ Cartesian SuccinctFinal.PackedWordRAM SuccinctSpace
open SuccinctFinal.PackedCellProbe SuccinctFinal.PackedWordRAM.Structured

theorem publicContract : PackedAllocationOptimality :=
  packedAllocationOptimality_holds

-- LB1-CONSUMER-OPTIMALITY-BEGIN
theorem checkO01 : ∀ width words, 0 < width →
    (∀ word ∈ words, word < 2 ^ width) →
    deserializeWords width (serializeWords width words) = words :=
  packedAllocationOptimality_holds.wordRoundTrip

theorem checkO02 : ∀ width first second, 0 < width →
    (∀ word ∈ first, word < 2 ^ width) →
    (∀ word ∈ second, word < 2 ^ width) →
    serializeWords width first = serializeWords width second → first = second :=
  packedAllocationOptimality_holds.wordSerializationInjective

theorem checkO03 : ∀ xs : List Int,
    (allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length :=
  packedAllocationOptimality_holds.serializedLength

theorem checkO04 : ∀ xs : List Int, reconstructedMemory xs = buildMemory xs :=
  packedAllocationOptimality_holds.memoryRecovery

theorem checkO05 : ∀ (xs : List Int) left right,
    allocationDecoder xs.length (allocationBits xs) left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  packedAllocationOptimality_holds.decoderExact

theorem checkO06 : ∀ (xs : List Int) left right index,
    allocationDecoder xs.length (allocationBits xs) left right = some index →
      LeftmostArgMin xs left right index :=
  packedAllocationOptimality_holds.decoderLeftmost

theorem checkO07 : ∀ xs ys : List Int,
    Cartesian.shape xs = Cartesian.shape ys → buildMemory xs = buildMemory ys :=
  packedAllocationOptimality_holds.sameShapeMemory

theorem checkO08 : ∀ n first second, first ∈ shapesOfSize n → second ∈ shapesOfSize n →
    allocationBits first.representative = allocationBits second.representative → first = second :=
  packedAllocationOptimality_holds.shapeInjectivity

theorem checkO09 : ∀ n B, UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (B + 1) - 1 :=
  by with_reducible exact packedAllocationOptimality_holds.uniformBudgetCount

theorem checkO10 : ∀ n B, UniformAllocationBudget n B →
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1) :=
  packedAllocationOptimality_holds.uniformBudgetLower

theorem checkO11 : ∀ n, shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1 :=
  packedAllocationOptimality_holds.canonicalCount

theorem checkO12 : ∀ n,
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (2 * n + allocationRho n + 1) :=
  packedAllocationOptimality_holds.canonicalLower

theorem checkO13 : ∀ xs : List Int,
    (allocationBits xs).length ≤ 2 * xs.length + allocationRho xs.length :=
  packedAllocationOptimality_holds.upperCapacity

theorem checkO14 : LittleOLinear allocationRho :=
  packedAllocationOptimality_holds.allocationResidualLittleO

theorem checkO15 : ∀ (xs : List Int) left right fuel,
    run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right) =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right) :=
  packedAllocationOptimality_holds.runIdentity

theorem checkO16 : ReconstructedPackedQueryCapstone :=
  packedAllocationOptimality_holds.machine

-- LB1-CONSUMER-OPTIMALITY-END

-- LB1-CONSUMER-MACHINE-BEGIN
theorem checkM01 : LittleOLinear allocationRho :=
  packedAllocationOptimality_holds.machine.allocationResidualLittleO

theorem checkM02 : LittleOLinear queryCompleteRho :=
  packedAllocationOptimality_holds.machine.completeResidualLittleO

theorem checkM03 : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) :=
  packedAllocationOptimality_holds.machine.widthBounds

theorem checkM04 : ∀ xs : List Int, (reconstructedMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length :=
  packedAllocationOptimality_holds.machine.dataCapacity

theorem checkM05 : ∀ xs : List Int,
    ((reconstructedMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length +
      (queryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + queryCompleteRho xs.length :=
  packedAllocationOptimality_holds.machine.completeCapacity

theorem checkM06 : ∀ (xs : List Int) word, word ∈ reconstructedMemory xs → word < 2 ^ wordWidth xs.length :=
  packedAllocationOptimality_holds.machine.memoryWordsFit

theorem checkM07 : ∀ (xs : List Int) address, address ≤ (reconstructedMemory xs).length →
    address < 2 ^ wordWidth xs.length :=
  packedAllocationOptimality_holds.machine.allocationAddressesFit

theorem checkM08 : ∀ n instruction, instruction ∈ queryProgram → instruction.Fits (wordWidth n) :=
  packedAllocationOptimality_holds.machine.programFieldsFit

theorem checkM09 : queryBudget = 837572 :=
  packedAllocationOptimality_holds.machine.budgetExact

theorem checkM10 : queryProgram.length = queryBudget :=
  packedAllocationOptimality_holds.machine.programLength

theorem checkM11 : (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget :=
  packedAllocationOptimality_holds.machine.encodedProgramBound

theorem checkM12 : queryRegisterCount = 8271 :=
  packedAllocationOptimality_holds.machine.registerCount

theorem checkM13 : queryScratchWords = 8274 :=
  packedAllocationOptimality_holds.machine.scratchCount

theorem checkM14 : ∀ (xs : List Int) left right fuel r, queryRegisterCount ≤ r →
    (run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right)).final.regs r = 0 :=
  packedAllocationOptimality_holds.machine.unusedRegisters

theorem checkM15 : ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length :=
  packedAllocationOptimality_holds.machine.validInputs

theorem checkM16 : ∀ (xs : List Int) left right,
    queryNat (reconstructedMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  packedAllocationOptimality_holds.machine.natContract

theorem checkM17 : ∀ (xs : List Int) left right index,
    queryNat (reconstructedMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index :=
  packedAllocationOptimality_holds.machine.leftmost

theorem checkM18 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  packedAllocationOptimality_holds.machine.result

theorem checkM19 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  packedAllocationOptimality_holds.machine.halt

theorem checkM20 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads = [] :=
  packedAllocationOptimality_holds.machine.invalidGuard

theorem checkM21 : ∀ (xs : List Int) left right,
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ queryBudget :=
  packedAllocationOptimality_holds.machine.stepBound

theorem checkM22 : ∀ (xs : List Int) left right,
    let actual := run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  packedAllocationOptimality_holds.machine.categoryPartition

theorem checkM23 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  packedAllocationOptimality_holds.machine.finalStateFit

theorem checkM24 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length) :=
  packedAllocationOptimality_holds.machine.transitionSafety

theorem checkM25 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ queryBudget →
      (run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length) :=
  packedAllocationOptimality_holds.machine.prefixSafety

theorem checkM26 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (reconstructedMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  packedAllocationOptimality_holds.machine.readWidth

theorem checkM27 : ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (reconstructedMemory xs) queryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (reconstructedMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (reconstructedMemory xs)[receipt.address]? :=
  packedAllocationOptimality_holds.machine.positionalReadBacking

theorem checkM28 : ∀ (xs : List Int) left right,
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (reconstructedMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] :=
  packedAllocationOptimality_holds.machine.orderedLogicalRefinement

theorem checkM29 : ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace :=
  packedAllocationOptimality_holds.machine.logicalReadOnly

theorem checkM30 : ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (reconstructedMemory xs)[receipt.address]?) →
    run memory queryProgram queryBudget (initialState xs.length left right) =
      run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right) :=
  packedAllocationOptimality_holds.machine.suppliedMemoryAgreement

theorem checkM31 : ∀ (xs : List Int) left right, ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1) :=
  packedAllocationOptimality_holds.machine.specResult

theorem checkM32 : ∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value :=
  packedAllocationOptimality_holds.machine.noFailedLoads

theorem checkM33 : ∀ (xs : List Int) left right, ¬ ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ 6 :=
  packedAllocationOptimality_holds.machine.invalidGuardSteps

-- LB1-CONSUMER-MACHINE-END

/-- Independent conjunction: every component depends on the named public
producer, and decoder/count/upper facts concern its actual allocation. -/
theorem composedConsumer :
    (∀ n B, (∀ xs : List Int, xs.length = n →
      (buildMemory xs).length * wordWidth n ≤ B) →
      EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1)) ∧
    (∀ (xs : List Int) left right,
      allocationDecoder xs.length (allocationBits xs) left right =
        if left < right ∧ right ≤ xs.length then
          some (scanWindow xs left (right - left)) else none) ∧
    (∀ xs : List Int,
      (allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length) ∧
    (∀ xs : List Int, reconstructedMemory xs = buildMemory xs) ∧
    (∀ xs : List Int,
      (allocationBits xs).length ≤ 2 * xs.length + allocationRho xs.length) :=
  ⟨packedAllocationOptimality_holds.uniformBudgetLower,
    packedAllocationOptimality_holds.decoderExact,
    packedAllocationOptimality_holds.serializedLength,
    packedAllocationOptimality_holds.memoryRecovery,
    packedAllocationOptimality_holds.upperCapacity⟩

theorem genericLowerConsumer {n B : Nat} (E : ExactRMQBoundedEncoding n B) :
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1) :=
  RMQ.ExactRMQBoundedEncoding.doubledLogSlackLower_le E

theorem genericCardinalConsumer (B : Nat) :
    (EncodingVariableLowerBound.boundedBitStrings B).Nodup ∧
      (EncodingVariableLowerBound.boundedBitStrings B).length = 2 ^ (B + 1) - 1 ∧
      ∀ bits, bits ∈ EncodingVariableLowerBound.boundedBitStrings B ↔ bits.length ≤ B :=
  EncodingVariableLowerBound.boundedBitStrings_cardinality B

theorem genericShapeCountConsumer {n B : Nat} (E : ExactRMQBoundedEncoding n B) :
    shapeCount n ≤ 2 ^ (B + 1) - 1 := E.shapeCount_le

/-! The left side of each generic projection pin is checked at a literal
expected type. Weakening the producer field invalidates that typed expression. -/

theorem pinGenericLengthType {n B : Nat} (E : ExactRMQBoundedEncoding n B) :
    (show ∀ xs : List Int, xs.length = n → (E.encode xs).length ≤ B
      from E.length_le) = E.length_le := rfl

theorem pinGenericQueryType {n B : Nat} (E : ExactRMQBoundedEncoding n B) :
    (show ∀ xs : List Int, xs.length = n →
      ∀ left len, 0 < len → left + len ≤ n →
        E.query (E.encode xs) left (left + len) = some (scanWindow xs left len)
      from E.query_exact) = E.query_exact := rfl

theorem pinUniformAllocationBudget (n B : Nat) :
    UniformAllocationBudget n B =
      (∀ xs : List Int, xs.length = n →
        (buildMemory xs).length * wordWidth n ≤ B) := rfl

theorem pinSerializeWords : serializeWords =
    (fun (width : Nat) (words : List Nat) =>
      (words.map (natToBitsLE width)).flatten) := rfl

theorem pinDeserializeWords : deserializeWords =
    (fun (width : Nat) (bits : List Bool) =>
      (List.range (bits.length / width)).map fun i =>
        bitsToNatLE ((bits.drop (i * width)).take width)) := rfl

theorem pinAllocationBits : allocationBits =
    (fun xs : List Int =>
      serializeWords (wordWidth xs.length) (buildMemory xs)) := rfl

theorem pinAllocationDecoder : allocationDecoder =
    (fun (n : Nat) (bits : List Bool) (left right : Nat) =>
      queryNat (deserializeWords (wordWidth n) bits) n left right) := rfl

theorem pinReconstructedMemory : reconstructedMemory =
    (fun xs : List Int =>
      deserializeWords (wordWidth xs.length) (allocationBits xs)) := rfl

theorem pinAllocationEncodingEncode (n B : Nat) (h : UniformAllocationBudget n B) :
    (allocationEncoding n B h).encode = allocationBits := rfl

theorem pinAllocationEncodingQuery (n B : Nat) (h : UniformAllocationBudget n B) :
    (allocationEncoding n B h).query = allocationDecoder n := rfl

theorem pinMemory : Memory = List Nat := rfl

theorem pinProgram : Program = List Instruction := rfl

theorem pinInstructionFits (width : Nat) (i : Instruction) :
    i.Fits width = (∀ operand ∈ i.encoding, operand < 2 ^ width) := rfl

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

theorem pinValidRange (xs : List Int) (left right : Nat) :
    ValidRange xs left right = (left < right ∧ right ≤ xs.length) := rfl

theorem pinLeftmostArgMin (xs : List Int) (left right index : Nat) :
    LeftmostArgMin xs left right index =
      (left < right ∧ right ≤ xs.length ∧ left ≤ index ∧ index < right ∧
        ∃ value : Int, xs[index]? = some value ∧
          (∀ j candidate, left ≤ j → j < right → xs[j]? = some candidate →
            value ≤ candidate) ∧
          (∀ j candidate, left ≤ j → j < index → xs[j]? = some candidate →
            value < candidate)) := rfl

theorem pinLittleOLinear (f : Nat → Nat) :
    LittleOLinear f = (∀ scale : Nat, 0 < scale → ∃ threshold : Nat,
      ∀ n : Nat, threshold ≤ n → scale * f n ≤ n) := rfl

/-- The counted store participates in both uniform counting and exact decoding. -/
theorem canonicalEncodingConsumer (n : Nat) :
    (canonicalAllocationEncoding n).encode = allocationBits ∧
    (canonicalAllocationEncoding n).query = allocationDecoder n ∧
    EncodingLowerBound.doubledLogSlackLower n ≤
      2 * (2 * n + allocationRho n + 1) :=
  ⟨rfl, rfl, genericLowerConsumer (canonicalAllocationEncoding n)⟩

theorem emptyDecoderConsumer : allocationDecoder 0 (allocationBits []) 0 0 = none := by
  simpa [ValidRange] using checkO05 [] 0 0

theorem singletonDecoderConsumer :
    allocationDecoder 1 (allocationBits [23]) 0 1 = some 0 := by
  simpa [ValidRange, scanWindow] using checkO05 [23] 0 1

theorem equalKeyDecoderConsumer :
    allocationDecoder 2 (allocationBits [7, 7]) 0 2 = some 0 := by
  simpa [ValidRange, scanWindow, betterIndex] using checkO05 [7, 7] 0 2

theorem invalidEndpointDecoderConsumer :
    allocationDecoder 1 (allocationBits [23]) 0 2 = none := by
  simpa [ValidRange] using checkO05 [23] 0 2

theorem zeroWordRoundTripConsumer :
    deserializeWords 4 (serializeWords 4 [0, 15, 1, 0, 8]) = [0, 15, 1, 0, 8] :=
  checkO01 4 [0, 15, 1, 0, 8] (by decide) (by simp)

theorem zeroWordMultiplicityConsumer :
    serializeWords 4 [] ≠ serializeWords 4 [0] ∧
      serializeWords 4 [0] ≠ serializeWords 4 [0, 0] := by
  constructor
  · intro h
    have hfalse := checkO02 4 [] [0] (by decide) (by simp) (by simp) h
    cases hfalse
  · intro h
    have hfalse := checkO02 4 [0] [0, 0] (by decide) (by simp) (by simp) h
    cases hfalse

theorem zeroWidthCollisionControl :
    serializeWords 0 [] = serializeWords 0 [0] := rfl

theorem sameShapeMemoryConsumer : buildMemory [0, 1] = buildMemory [9, 10] := by
  apply checkO07
  simpa [Cartesian.addConst] using (Cartesian.shape_addConst 9 [0, 1]).symm

theorem sameShapeBitsConsumer : allocationBits [0, 1] = allocationBits [9, 10] := by
  unfold allocationBits
  rw [sameShapeMemoryConsumer]
  rfl

/-! Runtime fixture data contains only small tags. Allocations and query runs
are constructed inside the selected case, after --list/selector validation. -/

inductive RuntimeCase where
  | empty | singleton | leftmost | zeroLength | zeroWords | sameShape
  deriving BEq, DecidableEq, Repr

def RuntimeCase.id : RuntimeCase → String
  | .empty => "R01-EMPTY"
  | .singleton => "R02-SINGLETON"
  | .leftmost => "R03-LEFTMOST"
  | .zeroLength => "R04-ZERO-LENGTH"
  | .zeroWords => "R05-ZERO-WORDS"
  | .sameShape => "R06-SAME-SHAPE"

def runtimeRegistryVersion : String := "LB1-RUNTIME-V1"

def runtimeRequiredIDs : List String :=
  ["R01-EMPTY", "R02-SINGLETON", "R03-LEFTMOST", "R04-ZERO-LENGTH",
    "R05-ZERO-WORDS", "R06-SAME-SHAPE"]

def runtimeRegistry : List RuntimeCase :=
  [.empty, .singleton, .leftmost, .zeroLength, .zeroWords, .sameShape]

theorem runtimeRegistry_exact : runtimeRegistry.map RuntimeCase.id =
    ["R01-EMPTY", "R02-SINGLETON", "R03-LEFTMOST", "R04-ZERO-LENGTH",
      "R05-ZERO-WORDS", "R06-SAME-SHAPE"] := rfl

theorem runtimeRegistry_nonempty : runtimeRegistry ≠ [] := by decide

theorem runtimeRegistry_ids_nodup : (runtimeRegistry.map RuntimeCase.id).Nodup := by decide

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError ("LB1-RUNTIME " ++ message))

@[noinline] private def checkAllocation (xs : List Int) : IO (List Bool × Memory) := do
  let memory := buildMemory xs
  let bits := allocationBits xs
  require (bits == serializeWords (wordWidth xs.length) memory)
    "actual allocation serializer mismatch"
  require (bits.length == memory.length * wordWidth xs.length)
    "actual allocation bit length mismatch"
  require (deserializeWords (wordWidth xs.length) bits == memory)
    "actual allocation round trip mismatch"
  pure (bits, memory)

def runCase (fixture : RuntimeCase) : IO Unit := do
  match fixture with
  | .empty =>
      let xs : List Int := []
      let (bits, _) ← checkAllocation xs
      require (allocationDecoder 0 bits 0 0 == none) "empty decoder expected none"
      require (allocationDecoder 0 bits 0 1 == none) "empty oversized endpoint expected none"
  | .singleton =>
      let xs : List Int := [23]
      let (bits, _) ← checkAllocation xs
      require (allocationDecoder 1 bits 0 1 == some 0) "singleton expected index zero"
      require (allocationDecoder 1 bits 0 2 == none) "singleton invalid endpoint expected none"
  | .leftmost =>
      let xs : List Int := [7, 7]
      let (bits, _) ← checkAllocation xs
      require (scanWindow xs 0 2 == 0) "independent tie specification mismatch"
      require (allocationDecoder 2 bits 0 2 == some 0) "equal keys expected leftmost zero"
  | .zeroLength =>
      require (serializeWords 4 [] == []) "empty serialization expected empty bits"
      require (deserializeWords 4 [] == []) "empty bits expected no words"
      require (serializeWords 0 [] == serializeWords 0 [0])
        "zero-width excluded-domain collision control failed"
      require (deserializeWords 0 [] == []) "zero-width empty decoder mismatch"
  | .zeroWords =>
      let empty := serializeWords 4 []
      let one := serializeWords 4 [0]
      let two := serializeWords 4 [0, 0]
      require (empty.length == 0 && one.length == 4 && two.length == 8)
        "zero-word lengths were lost"
      require (empty != one && one != two && empty != two)
        "different zero-word multiplicities collided"
      require (deserializeWords 4 one == [0] && deserializeWords 4 two == [0, 0])
        "zero words were not reconstructed"
      let words := [0, 15, 1, 0, 8]
      require (words.all (fun word => word < 2 ^ 4)) "bounded-word fixture escaped width"
      require (deserializeWords 4 (serializeWords 4 words) == words)
        "complete bounded word list failed round trip"
  | .sameShape =>
      let xs : List Int := [0, 1]
      let ys : List Int := [9, 10]
      let (first, firstMemory) ← checkAllocation xs
      let (second, secondMemory) ← checkAllocation ys
      require (xs != ys) "same-shape fixtures must have different values"
      require (scanWindow xs 0 2 == 0 && scanWindow ys 0 2 == 0)
        "independent same-shape specification mismatch"
      require (firstMemory == secondMemory && first == second)
        "same shapes did not share memory and serialized bits"
      require (allocationDecoder 2 first 0 2 == some 0)
        "shared payload decoder expected zero"
  IO.println ("LB1-RUNTIME CASE PASS " ++ fixture.id)

private def selectorWellFormed (id : String) : Bool :=
  match id.toList with
  | 'R' :: d1 :: d2 :: '-' :: rest =>
      d1.isDigit && d2.isDigit && !rest.isEmpty &&
        rest.all (fun c => c.isUpper || c == '-')
  | _ => false

private def findCase (id : String) : IO RuntimeCase := do
  if id.isEmpty then throw (IO.userError "LB1-RUNTIME empty selector")
  if id.trim.isEmpty then throw (IO.userError "LB1-RUNTIME whitespace selector")
  unless selectorWellFormed id do
    throw (IO.userError "LB1-RUNTIME malformed selector")
  match runtimeRegistry.filter (fun fixture => fixture.id == id) with
  | [fixture] => pure fixture
  | [] => throw (IO.userError ("LB1-RUNTIME unknown selector: " ++ id))
  | _ => throw (IO.userError "LB1-RUNTIME duplicate selector registry entry")

/-- The environment channel preserves explicit empty arguments on native hosts
that drop them: `LB1_RUNTIME_SELECTOR=case:` must fail, never select all cases. -/
private def runtimeArgs (args : List String) : IO (List String) := do
  let args := match args with | "--" :: rest => rest | _ => args
  let channel ← IO.getEnv "LB1_RUNTIME_SELECTOR"
  match channel with
  | none => pure args
  | some value =>
      unless args.isEmpty do
        throw (IO.userError "LB1-RUNTIME selector supplied twice")
      if value.startsWith "case:" then pure ["--case", value.drop 5]
      else throw (IO.userError "LB1-RUNTIME malformed selector channel")

def runMain (args : List String) : IO Unit := do
  require (runtimeRegistry.map RuntimeCase.id == runtimeRequiredIDs)
    "exact versioned registry mismatch"
  require (!runtimeRegistry.isEmpty) "empty runtime registry"
  require ((runtimeRegistry.map RuntimeCase.id).eraseDups.length == runtimeRequiredIDs.length)
    "duplicate runtime registry id"
  let args ← runtimeArgs args
  if args == ["--list"] then
    IO.println ("LB1-RUNTIME LIST " ++ runtimeRegistryVersion)
    for id in runtimeRequiredIDs do IO.println id
    IO.println ("LB1-RUNTIME LIST count=" ++ toString runtimeRequiredIDs.length)
  else
    let chosen ← match args with
      | [] => pure none
      | ["--case", id] => some <$> findCase id
      | _ => throw (IO.userError "LB1-RUNTIME expected no arguments, --list, or --case ID")
    let expected := match chosen with
      | none => runtimeRequiredIDs
      | some fixture => [fixture.id]
    let selected := match chosen with
      | none => runtimeRegistry
      | some fixture => [fixture]
    require (!selected.isEmpty) "selection must execute at least one case"
    require (selected.map RuntimeCase.id == expected) "selected registry mismatch"
    for fixture in selected do runCase fixture
    IO.println ("LB1-RUNTIME PASS version=" ++ runtimeRegistryVersion ++
      " executed=" ++ toString selected.length ++ " expected=" ++ toString expected.length ++
      " ids=" ++ String.intercalate "," expected)

end RMQ.Validation.VariablePayloadLowerBound

def main (args : List String) : IO Unit :=
  RMQ.Validation.VariablePayloadLowerBound.runMain args

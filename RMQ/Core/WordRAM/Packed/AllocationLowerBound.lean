import RMQ.Core.EncodingVariableLowerBound
import RMQ.Core.WordRAM.Packed.Capstone

/-!
# Information lower bound for the actual packed allocation

The serializer counts every allocated numeric word, including metadata and
padding, at the same positive width for every input of a given size. Bit-list
length is observed: zero words are retained and no padding to a common budget
is performed. The mathematical decoder reconstructs only those numeric words
and calls the existing fixed packed query with public size and endpoints.

Serialization, deserialization and the outer mathematical query wrapper have
no charged execution-time claim. Primitive execution facts below concern the
reconstructed word list, proved equal to the very allocation counted here.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe

/-- Serialize every full allocated word, preserving the number of zero words. -/
def serializeWords (width : Nat) (words : List Nat) : List Bool :=
  (words.map (natToBitsLE width)).flatten

/-- Mathematical reconstruction by fixed-width slices. The bit-list length is
available. No original input, Cartesian shape, or proof is an argument. -/
def deserializeWords (width : Nat) (bits : List Bool) : List Nat :=
  (List.range (bits.length / width)).map fun i =>
    bitsToNatLE ((bits.drop (i * width)).take width)

theorem serializeWords_length (width : Nat) (words : List Nat) :
    (serializeWords width words).length = words.length * width := by
  have h := uniform_flatten_length (words.map (natToBitsLE width)) width (by
    intro cell hcell
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hcell
    exact natToBitsLE_length width word)
  simpa only [serializeWords, List.length_map] using h

/-- Whole-list recovery, for arbitrary finite word lists rather than only the
canonical allocation. Positive width is essential for zero-word multiplicity. -/
theorem deserializeWords_serializeWords (width : Nat) (words : List Nat)
    (hw : 0 < width) (hwords : ∀ word ∈ words, word < 2 ^ width) :
    deserializeWords width (serializeWords width words) = words := by
  have hcount : (serializeWords width words).length / width = words.length := by
    rw [serializeWords_length, Nat.mul_div_cancel _ hw]
  apply List.ext_getElem
  · simp only [deserializeWords, List.length_map, List.length_range, hcount]
  · intro i hi hj
    simp only [deserializeWords, List.getElem_map, List.getElem_range]
    have hslice := uniform_flatten_slice (words.map (natToBitsLE width)) width (by
      intro cell hcell
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp hcell
      exact natToBitsLE_length width word) i
    change bitsToNatLE (((words.map (natToBitsLE width)).flatten.drop
      (i * width)).take width) = words[i]
    rw [hslice, List.getElem?_map, List.getElem?_eq_getElem hj]
    simp only [Option.map_some, Option.getD_some]
    exact bitsToNatLE_natToBitsLE_of_lt (hwords words[i] (List.mem_of_getElem rfl))

theorem serializeWords_injective (width : Nat) (first second : List Nat)
    (hw : 0 < width)
    (hfirst : ∀ word ∈ first, word < 2 ^ width)
    (hsecond : ∀ word ∈ second, word < 2 ^ width)
    (heq : serializeWords width first = serializeWords width second) :
    first = second := by
  have h := congrArg (deserializeWords width) heq
  simpa only [deserializeWords_serializeWords width first hw hfirst,
    deserializeWords_serializeWords width second hw hsecond] using h

/-- The exact bits occupied by PQ1's allocation, at its size-only word width. -/
def allocationBits (xs : List Int) : List Bool :=
  serializeWords (wordWidth xs.length) (buildMemory xs)

/-- Payload-only exact decoder. Its captured parameter is public size alone. -/
def allocationDecoder (n : Nat) (bits : List Bool) (left right : Nat) : Option Nat :=
  queryNat (deserializeWords (wordWidth n) bits) n left right

/-- Numeric memory reconstructed from the counted serialization. -/
def reconstructedMemory (xs : List Int) : Memory :=
  deserializeWords (wordWidth xs.length) (allocationBits xs)

theorem allocationBits_length (xs : List Int) :
    (allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length :=
  serializeWords_length _ _

theorem reconstructedMemory_eq_buildMemory (xs : List Int) :
    reconstructedMemory xs = buildMemory xs :=
  deserializeWords_serializeWords _ _ (wordWidth_pos xs.length) (buildMemory_words_fit xs)

theorem allocationDecoder_exact (xs : List Int) (left right : Nat) :
    allocationDecoder xs.length (allocationBits xs) left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none := by
  change queryNat (reconstructedMemory xs) xs.length left right = _
  rw [reconstructedMemory_eq_buildMemory]
  exact queryNat_exact xs left right

theorem allocationDecoder_leftmost (xs : List Int) (left right index : Nat)
    (h : allocationDecoder xs.length (allocationBits xs) left right = some index) :
    LeftmostArgMin xs left right index := by
  change queryNat (reconstructedMemory xs) xs.length left right = some index at h
  rw [reconstructedMemory_eq_buildMemory] at h
  exact queryNat_leftmost xs left right index h

/-- Equal Cartesian shapes intentionally share the numeric allocation. -/
theorem buildMemory_eq_of_shape_eq {xs ys : List Int}
    (h : Cartesian.shape xs = Cartesian.shape ys) : buildMemory xs = buildMemory ys := by
  exact congrArg shapeMemory h

theorem allocationBits_eq_of_shape_eq {xs ys : List Int}
    (h : Cartesian.shape xs = Cartesian.shape ys) : allocationBits xs = allocationBits ys := by
  have hsize := congrArg CartesianShape.size h
  have hlen : xs.length = ys.length := by simpa only [Cartesian.shape_size] using hsize
  unfold allocationBits
  rw [hlen, buildMemory_eq_of_shape_eq h]

/-- Representatives expose the identical shape builder, not a sibling payload. -/
theorem allocationBits_representative (shape : CartesianShape) :
    allocationBits shape.representative =
      serializeWords (wordWidth shape.size) (shapeMemory shape) := by
  simp only [allocationBits, CartesianShape.representative_length, buildMemory,
    SuccinctClassic.cartesianShape, CartesianShape.shape_representative]

/-- Payload equality on equal-size ordinary inputs determines their shape;
this does not assert injectivity on the input values. -/
theorem shape_eq_of_allocationBits_eq {xs ys : List Int}
    (hlen : xs.length = ys.length) (hbits : allocationBits xs = allocationBits ys) :
    Cartesian.shape xs = Cartesian.shape ys := by
  apply Cartesian.shape_eq_of_sameRMQBehavior
  refine ⟨hlen, ?_⟩
  intro left len hpos hbound
  have hvx : ValidRange xs left (left + len) := ⟨by omega, hbound⟩
  have hvy : ValidRange ys left (left + len) := ⟨by omega, by omega⟩
  have hsub : left + len - left = len := by omega
  have hx := allocationDecoder_exact xs left (left + len)
  have hy := allocationDecoder_exact ys left (left + len)
  rw [if_pos hvx, hsub] at hx
  rw [if_pos hvy, hsub] at hy
  rw [hlen, hbits] at hx
  exact Option.some.inj (hx.symm.trans hy)

theorem allocationBits_shape_injective (n : Nat) (first second : CartesianShape)
    (hfirst : first ∈ shapesOfSize n) (hsecond : second ∈ shapesOfSize n)
    (hbits : allocationBits first.representative = allocationBits second.representative) :
    first = second := by
  have hlen : first.representative.length = second.representative.length := by
    rw [CartesianShape.representative_length, CartesianShape.representative_length,
      (mem_shapesOfSize_shapeOfSize hfirst).size_eq,
      (mem_shapesOfSize_shapeOfSize hsecond).size_eq]
  have h := shape_eq_of_allocationBits_eq hlen hbits
  simpa only [CartesianShape.shape_representative] using h

/-- A uniform payload budget for every ordinary input of the fixed public size.
This is a worst-case budget, not a lower bound on each individual allocation. -/
def UniformAllocationBudget (n B : Nat) : Prop :=
  ∀ xs : List Int, xs.length = n → (buildMemory xs).length * wordWidth n ≤ B

/-- The generic bounded encoder instantiated by the actual allocated cells. -/
def allocationEncoding (n B : Nat) (budget : UniformAllocationBudget n B) :
    RMQ.ExactRMQBoundedEncoding n B where
  encode := allocationBits
  query := allocationDecoder n
  length_le xs hsize := by
    rw [allocationBits_length, hsize]
    exact budget xs hsize
  query_exact xs hsize left len hpos hbound := by
    have hv : ValidRange xs left (left + len) := ⟨by omega, by omega⟩
    have hsub : left + len - left = len := by omega
    have h := allocationDecoder_exact xs left (left + len)
    rw [if_pos hv, hsub, hsize] at h
    exact h

theorem canonicalAllocationBudget (n : Nat) :
    UniformAllocationBudget n (2 * n + allocationRho n) := by
  intro xs hsize
  simpa only [hsize] using buildMemory_capacity_le xs

def canonicalAllocationEncoding (n : Nat) :
    RMQ.ExactRMQBoundedEncoding n (2 * n + allocationRho n) :=
  allocationEncoding n _ (canonicalAllocationBudget n)

theorem uniformAllocation_shapeCount_le (n B : Nat) (budget : UniformAllocationBudget n B) :
    shapeCount n ≤ 2 ^ (B + 1) - 1 :=
  (allocationEncoding n B budget).shapeCount_le

theorem uniformAllocation_doubledLogSlackLower_le
    (n B : Nat) (budget : UniformAllocationBudget n B) :
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1) :=
  (allocationEncoding n B budget).doubledLogSlackLower_le

theorem canonicalAllocation_shapeCount_le (n : Nat) :
    shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1 :=
  (canonicalAllocationEncoding n).shapeCount_le

theorem canonicalAllocation_doubledLogSlackLower_le (n : Nat) :
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (2 * n + allocationRho n + 1) :=
  (canonicalAllocationEncoding n).doubledLogSlackLower_le

theorem allocationBits_capacity_le (xs : List Int) :
    (allocationBits xs).length ≤ 2 * xs.length + allocationRho xs.length := by
  rw [allocationBits_length]
  exact buildMemory_capacity_le xs

/-- Every fuel prefix on reconstructed memory is the corresponding PQ1 run,
including invalid endpoints. Safety below retains representability guards. -/
theorem reconstructedRun_eq (xs : List Int) (left right fuel : Nat) :
    run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right) =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right) := by
  rw [reconstructedMemory_eq_buildMemory]

/-- The complete accepted primitive-query propositions transported to the
reconstructed allocation. Every field retains its original endpoint guards,
program, width and scratch conventions. No serialization cost is asserted. -/
structure ReconstructedPackedQueryCapstone : Prop where
  -- LB1-MACHINE-FIELDS-BEGIN
  allocationResidualLittleO : LittleOLinear allocationRho
  completeResidualLittleO : LittleOLinear queryCompleteRho
  widthBounds : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)
  dataCapacity : ∀ xs : List Int, (reconstructedMemory xs).length * wordWidth xs.length ≤
    2 * xs.length + allocationRho xs.length
  completeCapacity : ∀ xs : List Int,
    ((reconstructedMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length +
      (queryRegisterCount + 3)) * wordWidth xs.length ≤
        2 * xs.length + queryCompleteRho xs.length
  memoryWordsFit : ∀ (xs : List Int) word, word ∈ reconstructedMemory xs → word < 2 ^ wordWidth xs.length
  allocationAddressesFit : ∀ (xs : List Int) address, address ≤ (reconstructedMemory xs).length →
    address < 2 ^ wordWidth xs.length
  programFieldsFit : ∀ n instruction, instruction ∈ queryProgram → instruction.Fits (wordWidth n)
  budgetExact : queryBudget = 837572
  programLength : queryProgram.length = queryBudget
  encodedProgramBound : (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget
  registerCount : queryRegisterCount = 8271
  scratchCount : queryScratchWords = 8274
  unusedRegisters : ∀ (xs : List Int) left right fuel r, queryRegisterCount ≤ r →
    (run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right)).final.regs r = 0
  validInputs : ∀ (xs : List Int) left right, ValidRange xs left right →
    encodeInputs xs.length left right = some (initialState xs.length left right) ∧
      left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
  natContract : ∀ (xs : List Int) left right,
    queryNat (reconstructedMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
  leftmost : ∀ (xs : List Int) left right index,
    queryNat (reconstructedMemory xs) xs.length left right = some index → LeftmostArgMin xs left right index
  result : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  halt : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  invalidGuard : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result = some 0 ∧
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads = []
  stepBound : ∀ (xs : List Int) left right,
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ queryBudget
  categoryPartition : ∀ (xs : List Int) left right,
    let actual := run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control
  finalStateFit : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  transitionSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length)
  prefixSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ fuel, fuel ≤ queryBudget →
      (run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right)).final.Fits (wordWidth xs.length)
  readWidth : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (reconstructedMemory xs)[receipt.address]? ∧
        (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
  positionalReadBacking : ∀ (xs : List Int) left right index (t : Transition) (receipt : Receipt),
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).transitions[index]? = some t →
    t.receipt = some receipt →
    t.before = (run (reconstructedMemory xs) queryProgram index (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (reconstructedMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (reconstructedMemory xs)[receipt.address]?
  orderedLogicalRefinement : ∀ (xs : List Int) left right,
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (reconstructedMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
  logicalReadOnly : ∀ (xs : List Int) left right,
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace
  suppliedMemoryAgreement : ∀ (xs : List Int) (memory : Memory) left right,
    (∀ receipt ∈ (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads,
      memory[receipt.address]? = (reconstructedMemory xs)[receipt.address]?) →
    run memory queryProgram queryBudget (initialState xs.length left right) =
      run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)
  specResult : ∀ (xs : List Int) left right, ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).result =
      some (scanWindow xs left (right - left) + 1)
  noFailedLoads : ∀ (xs : List Int) left right, ValidRange xs left right →
    ∀ receipt ∈ (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).reads,
      ∃ value, receipt.reply = some value
  invalidGuardSteps : ∀ (xs : List Int) left right, ¬ ValidRange xs left right →
    (run (reconstructedMemory xs) queryProgram queryBudget (initialState xs.length left right)).steps ≤ 6
  -- LB1-MACHINE-FIELDS-END

/-- Exact memory equality transports every accepted primitive proposition. -/
theorem reconstructedPackedQueryCapstone_holds : ReconstructedPackedQueryCapstone where
  -- LB1-MACHINE-INITIALIZERS-BEGIN
  allocationResidualLittleO := fullyChargedPackedQueryCapstone_holds.allocationResidualLittleO
  completeResidualLittleO := fullyChargedPackedQueryCapstone_holds.completeResidualLittleO
  widthBounds := fullyChargedPackedQueryCapstone_holds.widthBounds
  dataCapacity := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.dataCapacity
  completeCapacity := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.completeCapacity
  memoryWordsFit := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.memoryWordsFit
  allocationAddressesFit := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.allocationAddressesFit
  programFieldsFit := fullyChargedPackedQueryCapstone_holds.programFieldsFit
  budgetExact := fullyChargedPackedQueryCapstone_holds.budgetExact
  programLength := fullyChargedPackedQueryCapstone_holds.programLength
  encodedProgramBound := fullyChargedPackedQueryCapstone_holds.encodedProgramBound
  registerCount := fullyChargedPackedQueryCapstone_holds.registerCount
  scratchCount := fullyChargedPackedQueryCapstone_holds.scratchCount
  unusedRegisters := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.unusedRegisters
  validInputs := fullyChargedPackedQueryCapstone_holds.validInputs
  natContract := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.natContract
  leftmost := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.leftmost
  result := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.result
  halt := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.halt
  invalidGuard := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.invalidGuard
  stepBound := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.stepBound
  categoryPartition := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.categoryPartition
  finalStateFit := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.finalStateFit
  transitionSafety := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.transitionSafety
  prefixSafety := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.prefixSafety
  readWidth := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.readWidth
  positionalReadBacking := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.positionalReadBacking
  orderedLogicalRefinement := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.orderedLogicalRefinement
  logicalReadOnly := fullyChargedPackedQueryCapstone_holds.logicalReadOnly
  suppliedMemoryAgreement := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.suppliedMemoryAgreement
  specResult := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.specResult
  noFailedLoads := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.noFailedLoads
  invalidGuardSteps := by
    simpa only [reconstructedMemory_eq_buildMemory] using
      fullyChargedPackedQueryCapstone_holds.invalidGuardSteps
  -- LB1-MACHINE-INITIALIZERS-END

/-- Same-model information comparison. The lower bounds quantify a budget
uniform over all inputs of size n. The upper bound and primitive profile use
exactly the serialized and reconstructed PQ1 allocation. Public size is an
external input; fixed code and scratch have their separate complete capacity. -/
structure PackedAllocationOptimality : Prop where
  -- LB1-OPTIMALITY-FIELDS-BEGIN
  wordRoundTrip : ∀ width words, 0 < width →
    (∀ word ∈ words, word < 2 ^ width) →
    deserializeWords width (serializeWords width words) = words
  wordSerializationInjective : ∀ width first second, 0 < width →
    (∀ word ∈ first, word < 2 ^ width) →
    (∀ word ∈ second, word < 2 ^ width) →
    serializeWords width first = serializeWords width second → first = second
  serializedLength : ∀ xs : List Int,
    (allocationBits xs).length = (buildMemory xs).length * wordWidth xs.length
  memoryRecovery : ∀ xs : List Int, reconstructedMemory xs = buildMemory xs
  decoderExact : ∀ (xs : List Int) left right,
    allocationDecoder xs.length (allocationBits xs) left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
  decoderLeftmost : ∀ (xs : List Int) left right index,
    allocationDecoder xs.length (allocationBits xs) left right = some index →
      LeftmostArgMin xs left right index
  sameShapeMemory : ∀ xs ys : List Int,
    Cartesian.shape xs = Cartesian.shape ys → buildMemory xs = buildMemory ys
  shapeInjectivity : ∀ n first second, first ∈ shapesOfSize n → second ∈ shapesOfSize n →
    allocationBits first.representative = allocationBits second.representative → first = second
  uniformBudgetCount : ∀ n B, UniformAllocationBudget n B → shapeCount n ≤ 2 ^ (B + 1) - 1
  uniformBudgetLower : ∀ n B, UniformAllocationBudget n B →
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (B + 1)
  canonicalCount : ∀ n, shapeCount n ≤ 2 ^ (2 * n + allocationRho n + 1) - 1
  canonicalLower : ∀ n,
    EncodingLowerBound.doubledLogSlackLower n ≤ 2 * (2 * n + allocationRho n + 1)
  upperCapacity : ∀ xs : List Int,
    (allocationBits xs).length ≤ 2 * xs.length + allocationRho xs.length
  allocationResidualLittleO : LittleOLinear allocationRho
  runIdentity : ∀ (xs : List Int) left right fuel,
    run (reconstructedMemory xs) queryProgram fuel (initialState xs.length left right) =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right)
  machine : ReconstructedPackedQueryCapstone
  -- LB1-OPTIMALITY-FIELDS-END

/-- The actual packed allocation is a bounded exact RMQ encoding and satisfies
the existing 2n + o(n) upper bound in the same payload convention. Its
information lower bound is worst-case over inputs, with observed length. -/
theorem packedAllocationOptimality_holds : PackedAllocationOptimality where
  -- LB1-OPTIMALITY-INITIALIZERS-BEGIN
  wordRoundTrip := deserializeWords_serializeWords
  wordSerializationInjective := serializeWords_injective
  serializedLength := allocationBits_length
  memoryRecovery := reconstructedMemory_eq_buildMemory
  decoderExact := allocationDecoder_exact
  decoderLeftmost := allocationDecoder_leftmost
  sameShapeMemory xs ys := @buildMemory_eq_of_shape_eq xs ys
  shapeInjectivity := allocationBits_shape_injective
  uniformBudgetCount := uniformAllocation_shapeCount_le
  uniformBudgetLower := uniformAllocation_doubledLogSlackLower_le
  canonicalCount := canonicalAllocation_shapeCount_le
  canonicalLower := canonicalAllocation_doubledLogSlackLower_le
  upperCapacity := allocationBits_capacity_le
  allocationResidualLittleO := allocationRho_littleO
  runIdentity := reconstructedRun_eq
  machine := reconstructedPackedQueryCapstone_holds
  -- LB1-OPTIMALITY-INITIALIZERS-END

end RMQ.SuccinctFinal.PackedWordRAM

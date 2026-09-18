import RMQ.Core.WordRAM.Native.Execution

/-! # Native execution on the counted canonical binary image

This source theorem composes the byte-limb executor, binary loader and exported
entry declarations with the accepted PQ1 construction. Host allocation limits
are explicit on exported API fields; abstract representation/run claims cover
all sizes. Compilation, FFI pointer discipline and foreign runtime correctness
are documented assumptions, not conclusions of this Lean theorem.
-/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM Cartesian PackedWordRAM.Structured SuccinctSpace PackedCellProbe

structure NativeExecutionCapstone : Prop where
  -- NATIVE1-REPLAY-FIELDS-BEGIN
  wordRoundtrip : ∀ width value, value < 2 ^ width → LimbWord.decode (LimbWord.encode width value) = value
  wordCanonicalInverse : ∀ width word, LimbWord.Canonical width word → LimbWord.encode width (LimbWord.decode word) = word
  checkedArithmetic : ∀ width op x y,
    (∃ result, LimbWord.checkedArithmetic width op x y = .ok result) ↔
      LimbWord.Canonical width x ∧ LimbWord.Canonical width y ∧
      LimbWord.ArithmeticSafe width op (LimbWord.decode x) (LimbWord.decode y)
  serializedRoundtrip : ∀ image : StorageImage, image.Valid →
    StorageImage.decode image.encode = some image
  serializedInjective : ∀ x y : StorageImage, x.encode = y.encode → x = y
  loaderSource : ∀ bytes, nativeLoadEntry bytes =
    match StorageImage.decodeSupported nativeLimits bytes with
    | some image => .ok image
    | none => .error "invalid or unsupported binary image"
  querySource : ∀ image left right fuel reads, NativeQuerySupported image left right fuel →
    nativeQueryEntry image left right fuel reads =
      .ok (nativeObservationText (nativeCore image left.data right.data fuel reads))
  coreProjection : ∀ image left right fuel reads,
    nativeCore image left right fuel reads =
      ((LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).final,
       (LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).transitions.foldl
          (LimbMachine.recordTransition reads) {})
  defaultNoReads : ∀ image left right fuel, (nativeCore image left right fuel false).2.readsRev = []
  hostWordBytes : ∀ image : StorageImage, image.width ≤ nativeLimits.maxWidth →
    (nativeWordBytes image).toNat = LimbWord.limbCount image.width ∧
      (nativeWordBytes image).toNat ≤ 512
  canonicalValid : ∀ xs : List Int, (canonicalImage xs).Valid
  canonicalLoad : ∀ xs : List Int, (canonicalImage xs).Supported nativeLimits →
    nativeLoadEntry (canonicalImage xs).encode = .ok (canonicalImage xs)
  loadedAllocation : ∀ xs : List Int,
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.memory =
      some (LimbMachine.encodeMemory (wordWidth xs.length) (buildMemory xs)) ∧
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.code =
      some (LimbMachine.encodeCode (wordWidth xs.length) queryProgram)
  allFuelExecution : ∀ (xs : List Int) left right fuel,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalExecution xs left right fuel).decode =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right)
  canonicalSource : ∀ (xs : List Int) left right fuel reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ((canonicalObservation xs left right fuel reads).1.decode,
      (canonicalObservation xs left right fuel reads).2) =
      observeRun reads (run (buildMemory xs) queryProgram fuel
        (initialState xs.length left right)) {}
  canonicalQuery : ∀ (xs : List Int) left right fuel reads,
    (canonicalImage xs).Supported nativeLimits →
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    fuel ≤ nativeFuelLimit →
    nativeQueryEntry (canonicalImage xs) (canonicalEndpoint xs.length left)
      (canonicalEndpoint xs.length right) fuel reads =
      .ok (nativeObservationText (canonicalObservation xs left right fuel reads))
  widthBounds : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1)
  dataCapacity : ∀ xs : List Int, (canonicalImage xs).memory.size * (canonicalImage xs).width ≤
    2 * xs.length + allocationRho xs.length
  completeNumericCapacity : ∀ xs : List Int,
    (canonicalImage xs).wordCount * (canonicalImage xs).width +
      (queryRegisterCount + 3) * (canonicalImage xs).width ≤
        2 * xs.length + queryCompleteRho xs.length
  residuals : LittleOLinear allocationRho ∧ LittleOLinear queryCompleteRho
  fileAccounting : ∀ xs : List Int, 8 * (canonicalImage xs).encode.size =
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
      wordWidth xs.length +
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
      (8 * LimbWord.limbCount (wordWidth xs.length) - wordWidth xs.length) +
    8 * (canonicalImage xs).framingBytes
  machineInventory : queryBudget = 837572 ∧ queryProgram.length = queryBudget ∧
    queryRegisterCount = 8271 ∧ queryScratchWords = 8274 ∧
    (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget
  allocationAddressWidth : ∀ (xs : List Int) address, address ≤ (canonicalImage xs).memory.size →
    address < 2 ^ (canonicalImage xs).width
  programWidth : ∀ n instruction, instruction ∈ queryProgram → instruction.Fits (wordWidth n)
  validResult : ∀ (xs : List Int) left right, ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result =
      some (scanWindow xs left (right - left) + 1)
  nativeHalt : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right queryBudget reads).1.decode.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
  invalidGuard : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result = some 0 ∧
    (canonicalExecution xs left right queryBudget).decode.reads = [] ∧
    (canonicalExecution xs left right queryBudget).decode.steps ≤ 6
  stepBound : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right queryBudget reads).2.steps ≤ queryBudget
  categoryExact : ∀ (xs : List Int) left right fuel reads category,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right fuel reads).2.counts.get category =
      (canonicalExecution xs left right fuel).decode.categoryCount category
  readExact : ∀ (xs : List Int) left right fuel,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right fuel true).2.readsRev.reverse =
      (canonicalExecution xs left right fuel).decode.reads
  transitionSafety : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length)
  positionalReadBacking : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      t.receipt = some receipt →
      t.before = (canonicalExecution xs left right index).decode.final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧
        receipt.reply = (LimbMachine.decodeMemory (canonicalImage xs).memory)[receipt.address]?
  orderedLogicalReads : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalExecution xs left right queryBudget).decode.reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else []
  suppliedStoreAgreement : ∀ (xs : List Int) (memory : Memory) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (∀ value ∈ memory, value < 2 ^ wordWidth xs.length) →
    (∀ receipt ∈ (canonicalExecution xs left right queryBudget).decode.reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    (LimbMachine.run (wordWidth xs.length) (LimbMachine.encodeMemory (wordWidth xs.length) memory)
      (canonicalImage xs).code queryBudget
      (nativeInitialState (canonicalImage xs) (canonicalEndpoint xs.length left).data
        (canonicalEndpoint xs.length right).data)).decode =
      (canonicalExecution xs left right queryBudget).decode
  loadedDomain : ∀ bytes image, nativeLoadEntry bytes = .ok image →
    bytes = image.encode ∧ image.Valid ∧ image.Supported nativeLimits
  hostContainers : ∀ image : StorageImage, image.Supported nativeLimits →
    image.encode.size < USize.size ∧ image.registerCount < USize.size ∧
    image.code.size < USize.size ∧ image.memory.size < USize.size
  memoryHostAddress : ∀ (image : StorageImage) (address : Nat) (word : LimbWord.Word),
    image.Supported nativeLimits → image.memory[address]? = some word →
    address < image.memory.size ∧ address < USize.size ∧ address.toUSize.toNat = address
  codeHostAddress : ∀ (image : StorageImage) (pc : Nat) (fields : Array LimbWord.Word),
    image.Supported nativeLimits → image.code[pc]? = some fields →
    pc < image.code.size ∧ pc < USize.size ∧ pc.toUSize.toNat = pc
  leftmostResult : ∀ (xs : List Int) left right index, ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result = some (index + 1) →
    LeftmostArgMin xs left right index
  readWidth : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧
      receipt.reply = (LimbMachine.decodeMemory (canonicalImage xs).memory)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length)
  categoryPartition : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    let stats := (canonicalObservation xs left right queryBudget reads).2
    stats.steps = stats.counts.get .memoryRead + stats.counts.get .registerWrite +
      stats.counts.get .arithmetic + stats.counts.get .comparison +
      stats.counts.get .branch + stats.counts.get .control
  loadedProgram : ∀ bytes image, nativeLoadEntry bytes = .ok image →
    ∃ program : Program, image.code = LimbMachine.encodeCode image.width program ∧
      ∀ instruction ∈ program, instruction.Fits image.width
  -- NATIVE1-REPLAY-FIELDS-END

/-- Exact same canonical allocation, fixed program, word width, query state,
and execution throughout. No supplied correctness or readiness premise. -/
theorem nativeExecutionCapstone_holds : NativeExecutionCapstone where
  -- NATIVE1-REPLAY-INITIALIZERS-BEGIN
  wordRoundtrip := LimbWord.decode_encode
  wordCanonicalInverse width word hc := LimbWord.encode_decode width word hc.1
  checkedArithmetic := LimbWord.checkedArithmetic_accepts_iff
  serializedRoundtrip := StorageImage.decode_encode
  serializedInjective := StorageImage.raw_encode_injective
  loaderSource := nativeLoadEntry_source
  querySource := nativeQueryEntry_source
  coreProjection := nativeCore_source
  defaultNoReads := nativeCore_no_reads
  hostWordBytes := nativeWordBytes_exact
  canonicalValid := canonical_image_valid
  canonicalLoad := nativeLoadEntry_canonical
  loadedAllocation := canonical_loaded_cells
  allFuelExecution := canonicalExecution_decode
  canonicalSource := canonicalObservation_reference
  canonicalQuery := nativeQueryEntry_canonical
  widthBounds := fullyChargedPackedQueryCapstone_holds.widthBounds
  dataCapacity := by
    intro xs
    simpa [canonicalImage, StorageImage.fromReference] using
      fullyChargedPackedQueryCapstone_holds.dataCapacity xs
  completeNumericCapacity := canonical_complete_numeric_bits
  residuals := ⟨fullyChargedPackedQueryCapstone_holds.allocationResidualLittleO,
    fullyChargedPackedQueryCapstone_holds.completeResidualLittleO⟩
  fileAccounting := canonical_image_file_bits
  machineInventory := ⟨fullyChargedPackedQueryCapstone_holds.budgetExact,
    fullyChargedPackedQueryCapstone_holds.programLength,
    fullyChargedPackedQueryCapstone_holds.registerCount,
    fullyChargedPackedQueryCapstone_holds.scratchCount,
    fullyChargedPackedQueryCapstone_holds.encodedProgramBound⟩
  allocationAddressWidth := by
    intro xs address ha
    apply fullyChargedPackedQueryCapstone_holds.allocationAddressesFit xs address
    simpa [canonicalImage, StorageImage.fromReference] using ha
  programWidth := fullyChargedPackedQueryCapstone_holds.programFieldsFit
  validResult := canonicalExecution_spec
  nativeHalt := canonicalObservation_halts
  invalidGuard := by
    intro xs left right hl hr hi
    rw [canonicalExecution_decode xs left right queryBudget hl hr]
    exact ⟨(fullyChargedPackedQueryCapstone_holds.invalidGuard xs left right hl hr hi).1,
      (fullyChargedPackedQueryCapstone_holds.invalidGuard xs left right hl hr hi).2,
      fullyChargedPackedQueryCapstone_holds.invalidGuardSteps xs left right hi⟩
  stepBound := by
    intro xs left right reads hl hr
    rw [canonicalObservation_steps xs left right queryBudget reads hl hr]
    exact fullyChargedPackedQueryCapstone_holds.stepBound xs left right
  categoryExact := by
    intro xs left right fuel reads category hl hr
    rw [canonicalObservation_category xs left right fuel reads category hl hr,
      canonicalExecution_decode xs left right fuel hl hr]
  readExact := by
    intro xs left right fuel hl hr
    rw [canonicalObservation_reads xs left right fuel hl hr,
      canonicalExecution_decode xs left right fuel hl hr]
  transitionSafety := by
    intro xs left right hl hr index t ht
    rw [canonicalExecution_decode xs left right queryBudget hl hr] at ht
    exact fullyChargedPackedQueryCapstone_holds.transitionSafety xs left right hl hr index t ht
  positionalReadBacking := by
    intro xs left right hl hr index t receipt ht hreceipt
    rw [canonicalExecution_decode xs left right queryBudget hl hr] at ht
    rw [canonicalExecution_decode xs left right index hl hr]
    have hm : LimbMachine.decodeMemory (canonicalImage xs).memory = buildMemory xs :=
      LimbMachine.decodeMemory_encode _ _ (buildMemory_words_fit xs)
    rw [hm]
    exact fullyChargedPackedQueryCapstone_holds.positionalReadBacking xs left right index t receipt ht hreceipt
  orderedLogicalReads := by
    intro xs left right hl hr
    rw [canonicalExecution_decode xs left right queryBudget hl hr]
    exact fullyChargedPackedQueryCapstone_holds.orderedLogicalRefinement xs left right
  suppliedStoreAgreement := canonical_supplied_memory
  loadedDomain := nativeLoadEntry_success
  hostContainers := nativeHostBounds
  memoryHostAddress := nativeMemoryLookup
  codeHostAddress := nativeCodeLookup
  leftmostResult := canonicalExecution_leftmost
  readWidth := by
    intro xs left right hl hr index t receipt ht hreceipt
    rw [canonicalExecution_decode xs left right queryBudget hl hr] at ht
    have hm : LimbMachine.decodeMemory (canonicalImage xs).memory = buildMemory xs :=
      LimbMachine.decodeMemory_encode _ _ (buildMemory_words_fit xs)
    rw [hm]
    exact fullyChargedPackedQueryCapstone_holds.readWidth xs left right hl hr index t receipt ht hreceipt
  categoryPartition := by
    intro xs left right reads hl hr
    dsimp only
    rw [canonicalObservation_steps xs left right queryBudget reads hl hr]
    have hc (category : Category) :=
      canonicalObservation_category xs left right queryBudget reads category hl hr
    simp only [hc]
    exact fullyChargedPackedQueryCapstone_holds.categoryPartition xs left right
  loadedProgram := nativeLoadedProgram
  -- NATIVE1-REPLAY-INITIALIZERS-END

end RMQ.SuccinctFinal.PackedNative

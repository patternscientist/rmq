import RMQ.Core.WordRAM.Native.Capstone

/-! Independent exact-type consumers of the native public certificate.
These explicit propositions are frozen separately from the producer fields.
-/
namespace RMQ.SuccinctFinal.PackedNative.ContractChecks
open PackedWordRAM Cartesian PackedWordRAM.Structured SuccinctSpace PackedCellProbe

theorem publicContract : NativeExecutionCapstone := nativeExecutionCapstone_holds

theorem checkN01 : ∀ width value, value < 2 ^ width → LimbWord.decode (LimbWord.encode width value) = value :=
  nativeExecutionCapstone_holds.wordRoundtrip

theorem checkN02 : ∀ width word, LimbWord.Canonical width word → LimbWord.encode width (LimbWord.decode word) = word :=
  nativeExecutionCapstone_holds.wordCanonicalInverse

theorem checkN03 : ∀ width op x y,
    (∃ result, LimbWord.checkedArithmetic width op x y = .ok result) ↔
      LimbWord.Canonical width x ∧ LimbWord.Canonical width y ∧
      LimbWord.ArithmeticSafe width op (LimbWord.decode x) (LimbWord.decode y) :=
  nativeExecutionCapstone_holds.checkedArithmetic

theorem checkN04 : ∀ image : StorageImage, image.Valid →
    StorageImage.decode image.encode = some image :=
  nativeExecutionCapstone_holds.serializedRoundtrip

theorem checkN05 : ∀ x y : StorageImage, x.encode = y.encode → x = y :=
  nativeExecutionCapstone_holds.serializedInjective

theorem checkN06 : ∀ bytes, nativeLoadEntry bytes =
    match StorageImage.decodeSupported nativeLimits bytes with
    | some image => .ok image
    | none => .error "invalid or unsupported binary image" :=
  nativeExecutionCapstone_holds.loaderSource

theorem checkN07 : ∀ image left right fuel reads, NativeQuerySupported image left right fuel →
    nativeQueryEntry image left right fuel reads =
      .ok (nativeObservationText (nativeCore image left.data right.data fuel reads)) :=
  nativeExecutionCapstone_holds.querySource

theorem checkN08 : ∀ image left right fuel reads,
    nativeCore image left right fuel reads =
      ((LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).final,
       (LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).transitions.foldl
          (LimbMachine.recordTransition reads) {}) :=
  nativeExecutionCapstone_holds.coreProjection

theorem checkN09 : ∀ image left right fuel, (nativeCore image left right fuel false).2.readsRev = [] :=
  nativeExecutionCapstone_holds.defaultNoReads

theorem checkN10 : ∀ image : StorageImage, image.width ≤ nativeLimits.maxWidth →
    (nativeWordBytes image).toNat = LimbWord.limbCount image.width ∧
      (nativeWordBytes image).toNat ≤ 512 :=
  nativeExecutionCapstone_holds.hostWordBytes

theorem checkN11 : ∀ xs : List Int, (canonicalImage xs).Valid :=
  nativeExecutionCapstone_holds.canonicalValid

theorem checkN12 : ∀ xs : List Int, (canonicalImage xs).Supported nativeLimits →
    nativeLoadEntry (canonicalImage xs).encode = .ok (canonicalImage xs) :=
  nativeExecutionCapstone_holds.canonicalLoad

theorem checkN13 : ∀ xs : List Int,
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.memory =
      some (LimbMachine.encodeMemory (wordWidth xs.length) (buildMemory xs)) ∧
    (StorageImage.decode (canonicalImage xs).encode).map StorageImage.code =
      some (LimbMachine.encodeCode (wordWidth xs.length) queryProgram) :=
  nativeExecutionCapstone_holds.loadedAllocation

theorem checkN14 : ∀ (xs : List Int) left right fuel,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalExecution xs left right fuel).decode =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right) :=
  nativeExecutionCapstone_holds.allFuelExecution

theorem checkN15 : ∀ (xs : List Int) left right fuel reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ((canonicalObservation xs left right fuel reads).1.decode,
      (canonicalObservation xs left right fuel reads).2) =
      observeRun reads (run (buildMemory xs) queryProgram fuel
        (initialState xs.length left right)) {} :=
  nativeExecutionCapstone_holds.canonicalSource

theorem checkN16 : ∀ (xs : List Int) left right fuel reads,
    (canonicalImage xs).Supported nativeLimits →
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    fuel ≤ nativeFuelLimit →
    nativeQueryEntry (canonicalImage xs) (canonicalEndpoint xs.length left)
      (canonicalEndpoint xs.length right) fuel reads =
      .ok (nativeObservationText (canonicalObservation xs left right fuel reads)) :=
  nativeExecutionCapstone_holds.canonicalQuery

theorem checkN17 : ∀ n, Nat.log2 (n + 2) + 1 ≤ wordWidth n ∧
    wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) :=
  nativeExecutionCapstone_holds.widthBounds

theorem checkN18 : ∀ xs : List Int, (canonicalImage xs).memory.size * (canonicalImage xs).width ≤
    2 * xs.length + allocationRho xs.length :=
  nativeExecutionCapstone_holds.dataCapacity

theorem checkN19 : ∀ xs : List Int,
    (canonicalImage xs).wordCount * (canonicalImage xs).width +
      (queryRegisterCount + 3) * (canonicalImage xs).width ≤
        2 * xs.length + queryCompleteRho xs.length :=
  nativeExecutionCapstone_holds.completeNumericCapacity

theorem checkN20 : LittleOLinear allocationRho ∧ LittleOLinear queryCompleteRho :=
  nativeExecutionCapstone_holds.residuals

theorem checkN21 : ∀ xs : List Int, 8 * (canonicalImage xs).encode.size =
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
      wordWidth xs.length +
    ((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length) *
      (8 * LimbWord.limbCount (wordWidth xs.length) - wordWidth xs.length) +
    8 * (canonicalImage xs).framingBytes :=
  nativeExecutionCapstone_holds.fileAccounting

theorem checkN22 : queryBudget = 837572 ∧ queryProgram.length = queryBudget ∧
    queryRegisterCount = 8271 ∧ queryScratchWords = 8274 ∧
    (queryProgram.map Instruction.encoding).flatten.length ≤ 5 * queryBudget :=
  nativeExecutionCapstone_holds.machineInventory

theorem checkN23 : ∀ (xs : List Int) address, address ≤ (canonicalImage xs).memory.size →
    address < 2 ^ (canonicalImage xs).width :=
  nativeExecutionCapstone_holds.allocationAddressWidth

theorem checkN24 : ∀ n instruction, instruction ∈ queryProgram → instruction.Fits (wordWidth n) :=
  nativeExecutionCapstone_holds.programWidth

theorem checkN25 : ∀ (xs : List Int) left right, ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result =
      some (scanWindow xs left (right - left) + 1) :=
  nativeExecutionCapstone_holds.validResult

theorem checkN26 : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right queryBudget reads).1.decode.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  nativeExecutionCapstone_holds.nativeHalt

theorem checkN27 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result = some 0 ∧
    (canonicalExecution xs left right queryBudget).decode.reads = [] ∧
    (canonicalExecution xs left right queryBudget).decode.steps ≤ 6 :=
  nativeExecutionCapstone_holds.invalidGuard

theorem checkN28 : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right queryBudget reads).2.steps ≤ queryBudget :=
  nativeExecutionCapstone_holds.stepBound

theorem checkN29 : ∀ (xs : List Int) left right fuel reads category,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right fuel reads).2.counts.get category =
      (canonicalExecution xs left right fuel).decode.categoryCount category :=
  nativeExecutionCapstone_holds.categoryExact

theorem checkN30 : ∀ (xs : List Int) left right fuel,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalObservation xs left right fuel true).2.readsRev.reverse =
      (canonicalExecution xs left right fuel).decode.reads :=
  nativeExecutionCapstone_holds.readExact

theorem checkN31 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧
        t.after.Fits (wordWidth xs.length) :=
  nativeExecutionCapstone_holds.transitionSafety

theorem checkN32 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      t.receipt = some receipt →
      t.before = (canonicalExecution xs left right index).decode.final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧
        receipt.reply = (LimbMachine.decodeMemory (canonicalImage xs).memory)[receipt.address]? :=
  nativeExecutionCapstone_holds.positionalReadBacking

theorem checkN33 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (canonicalExecution xs left right queryBudget).decode.reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] :=
  nativeExecutionCapstone_holds.orderedLogicalReads

theorem checkN34 : ∀ (xs : List Int) (memory : Memory) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (∀ value ∈ memory, value < 2 ^ wordWidth xs.length) →
    (∀ receipt ∈ (canonicalExecution xs left right queryBudget).decode.reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) →
    (LimbMachine.run (wordWidth xs.length) (LimbMachine.encodeMemory (wordWidth xs.length) memory)
      (canonicalImage xs).code queryBudget
      (nativeInitialState (canonicalImage xs) (canonicalEndpoint xs.length left).data
        (canonicalEndpoint xs.length right).data)).decode =
      (canonicalExecution xs left right queryBudget).decode :=
  nativeExecutionCapstone_holds.suppliedStoreAgreement

theorem checkN35 : ∀ bytes image, nativeLoadEntry bytes = .ok image →
    bytes = image.encode ∧ image.Valid ∧ image.Supported nativeLimits :=
  nativeExecutionCapstone_holds.loadedDomain

theorem checkN36 : ∀ image : StorageImage, image.Supported nativeLimits →
    image.encode.size < USize.size ∧ image.registerCount < USize.size ∧
    image.code.size < USize.size ∧ image.memory.size < USize.size :=
  nativeExecutionCapstone_holds.hostContainers

theorem checkN37 : ∀ (image : StorageImage) (address : Nat) (word : LimbWord.Word),
    image.Supported nativeLimits → image.memory[address]? = some word →
    address < image.memory.size ∧ address < USize.size ∧ address.toUSize.toNat = address :=
  nativeExecutionCapstone_holds.memoryHostAddress

theorem checkN38 : ∀ (image : StorageImage) (pc : Nat) (fields : Array LimbWord.Word),
    image.Supported nativeLimits → image.code[pc]? = some fields →
    pc < image.code.size ∧ pc < USize.size ∧ pc.toUSize.toNat = pc :=
  nativeExecutionCapstone_holds.codeHostAddress

theorem checkN39 : ∀ (xs : List Int) left right index, ValidRange xs left right →
    (canonicalExecution xs left right queryBudget).decode.result = some (index + 1) →
    LeftmostArgMin xs left right index :=
  nativeExecutionCapstone_holds.leftmostResult

theorem checkN40 : ∀ (xs : List Int) left right,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    ∀ (index : Nat) (t : Transition) (receipt : Receipt),
      (canonicalExecution xs left right queryBudget).decode.transitions[index]? = some t →
      t.receipt = some receipt →
      receipt.address < 2 ^ wordWidth xs.length ∧
      receipt.reply = (LimbMachine.decodeMemory (canonicalImage xs).memory)[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  nativeExecutionCapstone_holds.readWidth

theorem checkN41 : ∀ (xs : List Int) left right reads,
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    let stats := (canonicalObservation xs left right queryBudget reads).2
    stats.steps = stats.counts.get .memoryRead + stats.counts.get .registerWrite +
      stats.counts.get .arithmetic + stats.counts.get .comparison +
      stats.counts.get .branch + stats.counts.get .control :=
  nativeExecutionCapstone_holds.categoryPartition

theorem checkN42 : ∀ bytes image, nativeLoadEntry bytes = .ok image →
    ∃ program : Program, image.code = LimbMachine.encodeCode image.width program ∧
      ∀ instruction ∈ program, instruction.Fits image.width :=
  nativeExecutionCapstone_holds.loadedProgram

end RMQ.SuccinctFinal.PackedNative.ContractChecks

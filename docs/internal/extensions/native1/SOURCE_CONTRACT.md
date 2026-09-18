# NATIVE-1 checked source contract

Status: SOURCE_CHECKED; full candidate replay/audit remains OPEN.

This is an exact proposition inventory, not an acceptance assertion. It quotes
all forty-two mandatory fields from the checked public record. Contract.lean
contains forty-two separately written literal expected types and projects the
public theorem. It does not infer expected types from the record. The committed
contract mutation runner must subsequently show that each weakening and the
public proposition collapse breaks its designated consumer while the modified
producer elaborates. No mutation outcome is inferred from these source checks.

Source identity:

- Capstone.lean SHA-256: `E2B2FB55223A271B3383AACB70361D85126ABEB3C252ACB0E314467729C6FA0D`.
- Contract.lean SHA-256: `A8DB1EAAC6445F2F8490A6C344A3F573FD169D3FD7B82E6637C4947159E306AE`.
- Producer check: commands/capstone-03.json, exit zero, 4.970 seconds.
- Independent consumer check: commands/contract-02.json, exit zero, 7.309 seconds.

The same objects appear throughout: `canonicalImage xs` contains
`encodeMemory (wordWidth xs.length) (buildMemory xs)` and
`encodeCode (wordWidth xs.length) queryProgram`; `canonicalExecution` runs those
very arrays from `nativeInitialState` with the two encoded endpoints.
`canonicalObservation` calls the actual `nativeCore` with that same image,
endpoints and fuel. The exported loader is the indexed bounded parser, whose
all-byte equality with `StorageImage.decodeSupported` is checked. Successful
loading reconstructs the exact original encoded image. The exported query
checks support and returns the text of `nativeCore`. Its tail-recursive fold
has the full logged-run projection below. This chain never supplies a separately
computed answer to the runtime implementation.

Abstract run and semantic fields quantify all sizes and all representable
endpoints; API fields separately require finite image and fuel support. Valid
ranges are required for leftmost minima, while representable-invalid ranges
halt with the encoded no-answer result and no reads. Canonical safety is derived
from accepted PQ1 facts. Arbitrary malformed/corrupt programs and words instead
have the checked fault behavior and the explicit generic safety guard described
in LIMB_WORDS.md and MACHINE_LEAF.md.

Compilation and ABI correctness remain explicit assumptions outside this Lean
source theorem. Numeric bit capacity, final limb rounding and binary framing are
separate quantities. Successful USize conversions do not promise allocation
availability or physical constant-time multiprecision arithmetic.

## Literal public propositions

```lean
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
```

## Exact consumer assignment

| Field | Independent consumer |
| --- | --- |
| `wordRoundtrip` | `ContractChecks.checkN01` |
| `wordCanonicalInverse` | `ContractChecks.checkN02` |
| `checkedArithmetic` | `ContractChecks.checkN03` |
| `serializedRoundtrip` | `ContractChecks.checkN04` |
| `serializedInjective` | `ContractChecks.checkN05` |
| `loaderSource` | `ContractChecks.checkN06` |
| `querySource` | `ContractChecks.checkN07` |
| `coreProjection` | `ContractChecks.checkN08` |
| `defaultNoReads` | `ContractChecks.checkN09` |
| `hostWordBytes` | `ContractChecks.checkN10` |
| `canonicalValid` | `ContractChecks.checkN11` |
| `canonicalLoad` | `ContractChecks.checkN12` |
| `loadedAllocation` | `ContractChecks.checkN13` |
| `allFuelExecution` | `ContractChecks.checkN14` |
| `canonicalSource` | `ContractChecks.checkN15` |
| `canonicalQuery` | `ContractChecks.checkN16` |
| `widthBounds` | `ContractChecks.checkN17` |
| `dataCapacity` | `ContractChecks.checkN18` |
| `completeNumericCapacity` | `ContractChecks.checkN19` |
| `residuals` | `ContractChecks.checkN20` |
| `fileAccounting` | `ContractChecks.checkN21` |
| `machineInventory` | `ContractChecks.checkN22` |
| `allocationAddressWidth` | `ContractChecks.checkN23` |
| `programWidth` | `ContractChecks.checkN24` |
| `validResult` | `ContractChecks.checkN25` |
| `nativeHalt` | `ContractChecks.checkN26` |
| `invalidGuard` | `ContractChecks.checkN27` |
| `stepBound` | `ContractChecks.checkN28` |
| `categoryExact` | `ContractChecks.checkN29` |
| `readExact` | `ContractChecks.checkN30` |
| `transitionSafety` | `ContractChecks.checkN31` |
| `positionalReadBacking` | `ContractChecks.checkN32` |
| `orderedLogicalReads` | `ContractChecks.checkN33` |
| `suppliedStoreAgreement` | `ContractChecks.checkN34` |
| `loadedDomain` | `ContractChecks.checkN35` |
| `hostContainers` | `ContractChecks.checkN36` |
| `memoryHostAddress` | `ContractChecks.checkN37` |
| `codeHostAddress` | `ContractChecks.checkN38` |
| `leftmostResult` | `ContractChecks.checkN39` |
| `readWidth` | `ContractChecks.checkN40` |
| `categoryPartition` | `ContractChecks.checkN41` |
| `loadedProgram` | `ContractChecks.checkN42` |

## Independent internal reconstruction

A separate worker reconstructed all 31 frozen requirements from the current
Capstone, Contract, executable definitions and inherited Packed modules without
editing files or running a competing compiler. It found no substantive missing
source proposition, quantifier or object-identity obligation. This is an internal
source review, not the fresh blind exact-commit audit or a campaign verdict.

The value-dependency conclusion uses the execution equation in
`positionalReadBacking`, not inequality of an enclosing log: expanding
`Primitive.execute` shows that the actual memory reply updates the destination
register, and subsequent arithmetic, branches and halt consume those registers.
`allFuelExecution` and `canonicalSource` preserve that complete state computation.
`suppliedStoreAgreement` concludes equality of the entire decoded run, including
final state, transitions and costs, for width-fitting supplied memory agreeing
at the original run's reads. Its safety premise is derived through inherited
run equality rather than assumed for an unrelated execution.

The occurrence chain additionally uses `Witnesses.stages_trace`,
`staged_receipt_at` and `occurrence_source`: semantic calls expand to ordered
physical receipts, then to an actual global transition index, producing load,
prefix pre-state and reply. Equal repeated reads remain distinct occurrences.
The seven operational fixtures and their native replay have separate evidence;
the 42 field consumers alone do not replace those obligations or generic fault
and operation checks.

The code is the closed `queryProgram`; varying geometry is loaded from counted
metadata. Complete numeric capacity and file accounting include encoded tags,
operands and the finite scratch bank. The category partition transports the
accepted word-RAM operation model. It is not a physical timing theorem for
multiprecision decoding or arithmetic.

The same reviewer inspected the narrow C/Rust boundary and emitted Entry/Runtime
C at source checkpoint `fa79233f77acbfa0470ef6203131e66784c7b014`. No concrete
boundary defect was found. The external contract still requires legitimate owned
handles and readable spans, the initializing OS thread, allocation availability,
the supported Windows x64 ABI and correctness of the pinned Lean/C/Rust compiler
and runtime. Runtime's emitted guards precede canonical-word checking and core
execution. The exact build manifest independently pins these source and generated
C bytes; review does not establish verified compilation.

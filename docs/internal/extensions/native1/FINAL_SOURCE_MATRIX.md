# NATIVE-1 source reconstruction by frozen requirement

This is an internal source reconstruction, not a fresh blind audit, an
operational-campaign verdict, or an acceptance decision. It maps all 31 IDs in
[ACCEPTANCE_MATRIX.md](ACCEPTANCE_MATRIX.md) without replacing, narrowing, or
changing any frozen requirement or status. The coordinator owns the subsequent
append-only operational evidence and final disposition. No Lean/Lake process or
native executable was run while preparing this document.

## Source identity and exact public types

The following are SHA256 hashes of the actual source bytes inspected:

| Source | SHA256 |
| --- | --- |
| `Native/Capstone.lean` | `E2B2FB55223A271B3383AACB70361D85126ABEB3C252ACB0E314467729C6FA0D` |
| `Native/Contract.lean` | `A8DB1EAAC6445F2F8490A6C344A3F573FD169D3FD7B82E6637C4947159E306AE` |
| `SOURCE_CONTRACT.md` | `8D9833471C76FD84E7C93E1387A755B063EB3307CD6ABE4B604564FAB6ABE94D` |
| `ACCEPTANCE_MATRIX.md` | `4619ED94C335B55EA18639418D2EEFC9B8B6981978BF439F5DA0C3631F5E8CE6` |
| `Native/Limbs.lean` | `06D057D0DE50E263E701D2D5FEA1A4B0E1F6C3DD9A6BFDB6F2F9EDE71A7803F1` |
| `Native/Machine.lean` | `F5286E6B52A5C5A73571BBF831E7CA9C5D731F7F5998F3ABA724E17F7AB94B3D` |
| `Native/Binary.lean` | `C50741D0A9AED1797919F405E8F7440410C0CD13DD2B9F299D0E6AB5E959AE16` |
| `Native/Binary/Bounds.lean` | `1ADF9BE737AD6C86AAC6E5FBA75ED3384876AA029CCEFBBD76CDA03DF70C339E` |
| `Native/Binary/Cursor.lean` | `FA032A73E3CAAB84A874D736D26CA8B833CECC526BBC880BDF09AC8647E68F45` |
| `Native/Canonical.lean` | `D61C7C1AA6C5FB521995A96F5EC0EBDFE8BDBE4A58CB1F6E159080E365AB857D` |
| `Native/CanonicalImage.lean` | `2A8469798F8A7700F22DA9F01AA157BFDE5F5BF7FE7282132DD53675FD74EE75` |
| `Native/Execution.lean` | `1367785E02684C7A81C93DF9815D8B736A3490F32046619C75A1838BAF469C06` |
| `Native/Witnesses.lean` | `8E732E615A9E69646AD6B6D2FDA5F632DF9826D2A22CA1B2DD71C98FF016B642` |
| `Native/WitnessExport.lean` | `4CF5C928FCD784DF112115A8BDFF87A8CA3FFC85AF04B679E320402106466F70` |
| `Packed/Capstone.lean` | `D9C7BB7D158D54C9F221080453C58F7DA6960497D287B7ACCC39BEBB3F931A2C` |
| `Packed/Primitive.lean` | `4C73250DF41AE328F6A9C6CD33FCEA48190A8A77AC81F09F1731B789D79B05C4` |
| `Packed/QueryObservations.lean` | `A51A79C3D201495A4538C7D04A7A35D9B3BEAC350C1BA01FC0F4C540891B4C05` |

Lean paths above are relative to `RMQ/Core/WordRAM/`. **The complete, verbatim
42 field types are incorporated by explicit reference to
[SOURCE_CONTRACT.md, Literal public propositions](SOURCE_CONTRACT.md#literal-public-propositions)
at the hash above.** Its
[Exact consumer assignment](SOURCE_CONTRACT.md#exact-consumer-assignment)
identifies the independently written literal type for every field. In this
document, `N01` means `ContractChecks.checkN01`, and similarly through `N42`;
the namespace is `RMQ.SuccinctFinal.PackedNative`. These are theorem consumers,
not inferred copies of the record's expected types.

| Consumers | Fields, in order |
| --- | --- |
| N01, N02, N03 | wordRoundtrip; wordCanonicalInverse; checkedArithmetic |
| N04, N05, N06, N07 | serializedRoundtrip; serializedInjective; loaderSource; querySource |
| N08, N09, N10 | coreProjection; defaultNoReads; hostWordBytes |
| N11, N12, N13 | canonicalValid; canonicalLoad; loadedAllocation |
| N14, N15, N16 | allFuelExecution; canonicalSource; canonicalQuery |
| N17, N18, N19, N20, N21, N22 | widthBounds; dataCapacity; completeNumericCapacity; residuals; fileAccounting; machineInventory |
| N23, N24, N25, N26, N27, N28 | allocationAddressWidth; programWidth; validResult; nativeHalt; invalidGuard; stepBound |
| N29, N30, N31, N32, N33, N34 | categoryExact; readExact; transitionSafety; positionalReadBacking; orderedLogicalReads; suppliedStoreAgreement |
| N35, N36, N37, N38 | loadedDomain; hostContainers; memoryHostAddress; codeHostAddress |
| N39, N40, N41, N42 | leftmostResult; readWidth; categoryPartition; loadedProgram |

## Shared objects, hypotheses, and supplemental propositions

For the descriptions below, fix `xs : List Int`, `w = wordWidth xs.length`,
`M = buildMemory xs`, `P = queryProgram`, `I = initialState xs.length left right`,
`Q_f = run M P f I`, `C = canonicalImage xs`,
`E_f = canonicalExecution xs left right f`, and
`O_f = canonicalObservation xs left right f reads`.
The representable endpoint domain `D` is exactly `left < 2^w` and `right < 2^w`.
`ValidRange xs left right` retains the inherited half-open interval contract and
implies `D`; it is not required for the all-fuel execution identity. The packet
encoding returns `index + 1` for an answer and zero for no answer.

**Object chain.** `C.width = w`, `C.inputLength = xs.length`,
`C.registerCount = queryRegisterCount`,
`C.memory = LimbMachine.encodeMemory w M`, and
`C.code = LimbMachine.encodeCode w P`. `StorageImage` uses the machine's literal
`Memory = Array (Array UInt8)` and `Code = Array (Array (Array UInt8))` aliases.
The machine's registers, PC, and halted packet also store byte words. A successful
load returns the same image represented by the accepted bytes. `nativeCore` runs
`LimbMachine.runThin` on that image's own memory/code, with `nativeInitialState`
initializing r0/r1 from endpoint bytes and r2 from **image.inputLength**, not from
memory[0]. Canonical endpoint decoding recovers the original endpoint under `D`.
Temporary Nat decoding is part of the permitted executable Lean implementation;
there is no persistent decoded Nat program or answer cache substituted here.

The following supplements are necessary: the 42 capstone fields alone are not a
complete inventory of generic fault, operation, or witness obligations.

- **G-OPS — all operations and exact rejection.** `LimbWord.Canonical w x`
  means `x.size = (w+7)/8` and `decode x < 2^w`. For every arithmetic constructor
  `op`, `checkedArithmetic_success` says success on `x,y` implies canonical
  operands/result, exact decoded result `op.eval (decode x) (decode y)`, and
  `ArithmeticSafe`: result below `2^w`, no subtraction underflow, a positive
  divisor for div/mod, and shift count below `w` for shl/shr.
  `checkedArithmetic_accepts_iff` is the converse/exact acceptance boundary;
  `checkedArithmetic_encode_of_safe` returns the encoding of the same reference
  result when both operands fit and these clauses hold. The ten constructors are
  add, sub, mul, div, mod, shl, shr, band, bor, bxor. For every comparison,
  `checkedComparison_success` gives canonical inputs/result and exact `op.eval`.
  `checkedAddress_success` gives canonical input, `address.toNat = decode word`
  and `< limit`; the implementation also checks `< USize.size` before conversion.
  `checkedInt_success` gives `0 ≤ value`, canonical result and exact equality
  `(decode result : Int) = value`. Negative Int inputs are rejected; this helper
  does not purport to store the original possibly negative `xs` in unsigned words.
- **G-FAULT — named checked fault equations.**
  `checkedNatArithmetic_underflow` assumes `x < y` and concludes sub returns
  `.error .underflow`; `checkedNatArithmetic_zero_divisor` concludes both div/mod
  by zero return `.error .zeroDivisor`; `checkedNatArithmetic_oversized_shift`
  assumes `w ≤ y` and concludes both shifts reject. `checkedNat_overflow` assumes
  `2^w ≤ value`; `checkedArithmetic_malformed` assumes at least one operand is
  noncanonical; `checkedInt_negative` assumes `value < 0`. Their respective
  errors are overflow, malformedWord, and negativeInput. Machine
  `execute_arithmetic_rejected` transports an actual checked-word error to
  `fail s (.word why)`. `execute_missing_memory` assumes a canonical address
  register and an absent indexed cell, and returns `fail s .missingMemory`
  with the attempted address and reply `none`. `step_missing_fetch` assumes
  running state, canonical PC and missing code at that PC, and concludes
  `.stopped`; `run_of_stopped` returns the unchanged state and no transitions.
  `step_malformed_code` assumes a fetched row whose decoder returns an error,
  and concludes a faulted state rejected as malformedCode. Thus missing fetch
  is not incorrectly equated with a charged failed data load. Concrete leaf
  consumers pin the different status/read/count outcomes.
- **G-MACHINE — the generic simulation's actual guard.** `execute_encode`
  quantifies every instruction constructor, width, register capacity, raw memory
  and state. Premises are memory words fitting the width, `Instruction.Safe`
  for this actual instruction/prestate, fitting raw poststate, writes within
  capacity, and zero raw registers beyond capacity. Its next-state/receipt pair
  is exactly the encoding of `PackedWordRAM.execute`'s pair. `step_encode`,
  `run_encode`, then `run_reference` extend this to every fuel. The full-run
  premises additionally quantify code Fits/WritesOnly, initial state Fits and
  `RunSafe w Q_f`, meaning every actual transition has Safe prestate/instruction
  and fitting poststate. The conclusion is equality of the **whole decoded Run**,
  not just its answer. `run_loaded_reference` starts with arbitrary actual
  canonical byte memory/state and exact `code = encodeCode w program`, with
  corresponding Fits/WritesOnly/RunSafe premises, and concludes equality with
  `run (decodeMemory memory) program fuel s.decode` on that same store. The
  canonical theorem `canonical_run_safe xs left right fuel` derives RunSafe
  from the inherited query safety, prefix and halted-run facts for every `fuel`
  under `D`; it does not add RunSafe as a caller assumption to N14/N15/N34.
- **G-FILE — actual Image codec and host refinement.** `StorageImage.decode_iff`
  states, for every bytes/image, `decode bytes = some image ↔ bytes = image.encode
  ∧ image.Valid`. `valid_iff` expands Valid to positive width, inputLength and
  registerCount below `2^width`, every code row having at most five canonical
  words and a successful actual instruction parser, and every memory word being
  canonical. `decoded_fields` preserves all five fields, including inputLength.
  `decode_bad_magic` rejects a prefix unequal to RMQN/version1;
  `decode_truncated` rejects every proper prefix `initial` of any `image.encodeList`
  (`initial ++ suffix = image.encodeList`, `suffix ≠ []`).
  `BinaryCursor.decodeSupported_eq` holds for **every** limits/ByteArray and
  equates the indexed runtime decoder to the reference supported decoder.
  `BinaryCursor.decodeSupported_iff` strengthens accepted-file identity with
  Valid and Supported. Supported means encoded byte size, width, register count,
  instruction count and memory count satisfy their five declared limits.
  `readScalarDigits_reject_count` and `readScalarLimit_reject_count` reject a
  parsed unary length exceeding the supplied digit cap **before** digit
  accumulation. Cursor's byte-offset loops and bounded array readers refine
  the reference list parser; the list parser is not used as the large native
  loader. Scalars have all-Nat minimal little-endian digits and unary byte-length
  framing, so the abstract codec has no u64 header restriction.
- **G-HOST — finite implementation domain.** `nativeLimits` is 128 MiB,
  4096 width bits, 65536 registers, 1000000 instructions and 1000000 memory
  words; fuel is at most 1000000. `NativeQuerySupported` additionally requires
  positive bounded width, at least three registers, representable inputLength,
  and canonical full-width endpoint buffers. N35/N36/N37/N38 connect success to
  these image limits and exact USize conversions. They do not promise allocation
  availability or execution of arbitrarily large mathematical inputs on a host.
- **G-WITNESS — semantic occurrences, not stage labels.** For every xs/endpoints,
  `Witnesses.stages_trace` equates `flatten (stages xs left right)` with the
  public `SuccinctClassic.queryTraceResult` trace. `queryStages_trace` expands
  the actual two `packedSelectCloseLeaf` calls at `left` and `right-1`;
  `lcaStages_trace`, `fringeStages_trace`, and `afterSelectStages_trace` expand
  the selected LCA/fringe/interior/final-rank branches. Under ValidRange, a
  decomposition `flatten stages = prior ++ readWord segment index word :: after`
  and exact indexed receipt `readerReceipts shape M segment index[offset]? =
  some receipt` give, by `staged_receipt_at`,
  `queryRun M xs.length left right.reads[174 + (logicalTraceReads shape M prior).length
  + offset]? = some receipt`. This is a positional formula retaining every
  previous occurrence, including equal repeated reads. `occurrence_source`
  assumes an actual indexed transition and its receipt, and gives its exact
  run-prefix prestate, running status, fetched instruction, execute equation,
  load destination/address register, and reply from `M[address]?`.
  `arrayRun_exact` identifies `runArray M P.toArray queryBudget I` with the same
  `queryRun M xs.length left right`.

For concrete witness export, the actual transition list is enumerated with
`zipIdx`; receipt extraction retains those original transition indices.
`WitnessExport.inspect` checks equality with the full ordered raw receipt list,
the 174 metadata prefix and the logical expansion, then slices **consecutive**
physical occurrences at cumulative offsets. It checks consumption of all logical
and physical occurrences. It does not find an arbitrary equal address/value
later in a list. Its `Logical.crosses` requires a positive span, an actual word
boundary crossing, exactly two adjacent physical addresses and two successful
replies. `checkKinds` pins seven distinct required IDs. The main routine supplies
`queryProgram.toArray` and a `buildMemory xs` cache keyed by that exact xs;
the standalone `inspect` parameters are not assumed canonical without this call
chain. Expected numeric observations come from the raw array evaluator connected
by G-WITNESS, with independent literal answer, public reference and `scanWindow`
agreement; they do not come from the limb/native output. The checked universal
theorems constrain the provenance conditions; the successful concrete exporter
execution supplies the seven actual witnesses.

## Requirement mapping

In the last column, a **rejection surface** names the exact existing proposition
that excludes the changed behavior, or the operational guard that must reject
it. This is not a claim that a new counterfactual compiler/native campaign was
executed during this review. Previously executed leaf checks are identified in
the evidence section below. The final 42-field and native campaigns remain
separate, pending coordinator evidence.

| Frozen ID | Precise proposition and same-object/consumer chain | Concrete anti-vacuity challenge and rejection surface |
| --- | --- | --- |
| `REQ-NATIVE-FINITE` | G-MACHINE covers all nine instructions and all fuel, using finite byte code/memory/registers; N14 gives `E_f.decode = Q_f` for every xs/f under D, and N15 transports the same state/statistics to the actual core. N25/N26/N27/N29/N30/N41 project result, halted status, invalid behavior, all categories and ordered attempted reads. G-FAULT states behavior outside generic safety. `run_loaded_reference → canonicalExecution_decode → N14 → nativeCore_source/N15 → Validation.PackedNative` uses C's own arrays. | Change a loaded reply or destination, reverse equal reads, drop a failed load, or change a category. `execute_encode`, `run_reference`, N14/N29/N30 and Machine/Checks' full result/status/read/steps/six-category consumer require the original projections. Missing-memory, malformed-code and zero-divisor concrete leaf examples pin distinct faults/counts; final native mutants remain pending. |
| `REQ-NATIVE-WIDTH` | N01/N02 and G-OPS establish exact little-endian limb values for every mathematical width. `arithmeticSafe_of_instructionSafe` supplies each arithmetic clause to the same machine operation; N17/N23/N24/N31/N40 discharge width/address/operand facts for C/Q. N10/N35–N38 and G-HOST are separate finite-host restrictions. N18–N21 separate numeric capacity, byte rounding and framing. | Truncate a 176-bit value at bit128, permit division by zero, accept shift count w, wrap overflow, or admit a dormant oversized code operand. The 168/176-bit Limbs/Checks examples, `checkedArithmetic_success/accepts_iff`, named G-FAULT equations, N24 and N42 exclude these cases. USize/host assertions use N10/N36–N38, not the all-size theorem. Physical constant-time multiprecision execution is not a proved conclusion. |
| `REQ-NATIVE-SERIAL` | N04/N05 plus G-FILE give actual image roundtrip, unconditional encode injectivity, exact accepted-file identity, proper-prefix rejection and canonical padding/tag validation. N11 supplies Valid for every C; N13 identifies the decoded memory/code with encodings of M/P. N06/N12/N35 and Cursor all-byte equality connect the efficient loader to those arrays; N21 accounts exact file bytes. | Change magic/version, word length, padding, width/counts, append bytes, truncate, or substitute one code/memory field. `decode_bad_magic`, `decode_truncated`, `decode_iff`, `decoded_fields`, Cursor `decodeSupported_iff` and N04/N05/N13/N35 exclude the relevant changes. Binary/Checks and Cursor/Checks have checked positive/rejection controls; whole native image campaign remains separate. |
| `REQ-NATIVE-CODE` | N06 is the exact source equation for exported `nativeLoadEntry`; N07 says supported query returns the text of the same `nativeCore`; N08 is its complete logged-run projection. N15/N16 compose this with Q_f on C. Route choice is executable Lean → generated C export → narrow C shim → Rust/C++ callers; pinned build/source identity and marshaling are operational evidence, not new Lean compilation theorems. | Redirect the exported core to a sibling evaluator, swap endpoint arguments, or compute a fixture answer outside the core. N06/N07/N08/N15/N16 and their literal consumers expose source-level changes. A C/Rust marshaling mutant instead requires the actual build/ABI comparison; the source theorem cannot itself reject an arbitrary changed foreign wrapper. Final route/source campaigns are pending here. |
| `REQ-NATIVE-API` | N07/N10/N16/N35–N38 and G-HOST describe bounded loaded/query inputs and exact conversions. N08/N09, via `runThin_projection` and `runThin_no_reads`, show default execution folds actual steps without a full transition list and leaves the read accumulator empty. Runtime's core uses the retained image and deterministic explicit endpoints/fuel. Rust/C/C++ ownership, error propagation, LF output and lifetime contracts lie in the narrow reviewed boundary and operational checks. | Make quiet mode collect transitions/reads, reconstruct a different image on repeat, accept an oversized endpoint/fuel, or retain a freed result span. N08/N09 and Machine/Checks exclude the source projection change; G-HOST/native entry guards exclude unsupported inputs. Resource lifetime and wrapper errors require actual repeated-call/native controls, not an invented Lean ownership theorem. |
| `REQ-NATIVE-JOIN` | `ContractChecks.publicContract : NativeExecutionCapstone := nativeExecutionCapstone_holds` and N01–N42 consume independently stated field types. N11/N13/N14/N15/N18/N19/N21 fix exactly C/M/P/w/I, combining `fullyChargedPackedQueryCapstone_holds` with the limb, file and source implementations. N12/N16 retain finite support only at the API boundary. | Replace the counted memory with a sibling, weaken D/validity/all-fuel quantifiers, delete a field, or collapse the public proposition to True. N13/N14/N18/N19/N21 and the corresponding literal consumers/publicContract are the exact source surfaces. Whether each chosen mutant actually breaks its designated consumer must be shown by the separately scheduled contract campaign. |
| `CHK-NATIVE-CONTROLS` | G-OPS/G-FAULT/G-FILE supply universal and concrete boundary propositions. G-WITNESS joins the two select call sites, fringes, interior/final rank and true cross-cell occurrences to actual transition indices and the independent raw oracle. N14/N15/N29/N30/N32/N33 connect those expectations to the same native source. Committed fixture/registry/replay consumers must exercise the shipped clients. | Delete one select occurrence, replace a crossing by one cell, label an unrelated read as final rank, or generate expected counts from native output. `stages_trace`, `staged_receipt_at`, `occurrence_source`, `arrayRun_exact`, `inspect`'s ordered checks, `Logical.crosses` and `checkKinds` reject the corresponding semantic/selection defects. Seven concrete exports and leaf controls are evidenced below; final source/native campaign outcomes are not inferred. |
| `REPLAY-EXACT-REGISTRY` | This is an operational requirement, not a capstone proposition. The versioned validator registry, `WitnessExport.checkKinds`, contract runner's exact baseline/42-fields/public-collapse roster, and native replay roster compare nonempty required/actual IDs. Their execution must reach the actual N06/N07 source. | Remove one ID or allow executed=0. `checkKinds` rejects its seven-ID mismatch; each production replay must reject its own exact-roster mismatch. No Lean theorem establishes OS process execution counts; final registry receipts must record the exact attempted roster. |
| `REPLAY-SELECTOR-NONVACUITY` | Operational entry-point parsing distinguishes omitted/full selection, one exact valid ID and invalid selector channels. `Validation.PackedNative` exposes the selector and compare modes on its actual loaded source; the production PowerShell runners validate bound parameters before execution. These guards complement, rather than follow from, N06/N07. | Pass explicit empty/whitespace/unknown/malformed selectors, including through the actual process boundary. Production selector guards and the committed selector-control registry are the rejection surfaces. Internal helper tests alone cannot establish empty-argument transport behavior; final process-boundary outcomes remain coordinator evidence. |
| `REPLAY-SUBPROCESS-DEADLINE` | Operational scripts use `owned_process_tree.ps1` to retain ownership, exits/stderr and bounded deadlines. Contract/native mutation runners preserve and restore source/artifact bytes in finally and check restoration. No field of NativeExecutionCapstone proves process cleanup or a particular host capability. | Spawn an owned sleeper child, force a timeout or mutation failure, lose stderr, or leave changed bytes after failure. The actual owned-process/deadline controls and restoration hash checks must reject these conditions; unsupported host creation is uncovered/inconclusive. No pending branch is relabeled as passed by this source review. |
| `INV-STORE-IDENTITY` | N13 maps decoded bytes to `encodeMemory w M` and `encodeCode w P`; N14 executes those same arrays; N18/N19/N21 count those arrays and their exact encoded fields. N32/N40 identify actual read replies as indexed lookups in `decodeMemory C.memory = M`. | Count M while executing an uncounted M′ or decoded sibling image. N13 plus `decodeMemory_encode` and N14/N18/N19/N21/N32/N40 require the original indexed store at the same xs. A matching standalone theorem about M′ does not inhabit these literal consumers. |
| `INV-VALUE-DEPENDENCY` | N32 contains `execute M t.instruction t.before = (t.after,t.receipt)`, with actual load register/address/reply. Expanding Primitive.execute writes that reply to the destination; later arithmetic, branchZero, jumpRegister and halt consume the register state. N14/N15 preserve this whole computation. Inherited `metadataSetupBlock_run_value_dependency` forces a changed metadata reply to change register16+i; `locate_run_position_dependency` forces different stored bit bases to change the returned position; `crossing_value_dependency` changes the returned span numeral on changing either crossing cell. | Keep the returned register/position/value constant while changing only the log. The three named inherited value/position theorems contradict precisely those constant projections under their stated guards (running setup with two memories of length≥174 and i<174; valid regular locate segment<23,≠20/index0/positive count/different bases; explicit two-cell numeral examples). N32's execute equation and the G-MACHINE success consumers transport actual value flow. No claim that every arbitrary irrelevant memory change must alter the final RMQ answer is made. |
| `INV-SEMANTIC-NONVACUITY` | N33 is equality with the operational public logical trace, including its 174-entry setup expansion. G-WITNESS derives stages from the actual select/LCA/fringe/rank calls and maps each ordered occurrence to physical receipts and an actual primitive transition/prestate. Valid and invalid branches have explicit different trace behavior. | Replace stage semantics by True, label any load as either select, or reuse one equal receipt for two occurrences. `stages_trace`, `staged_receipt_at`, `occurrence_source`, N32/N33 and exporter cumulative-offset checks require the original call trace and exact positions. The seven-fixture exporter guards supply nonempty concrete occurrences; labels alone do not. |
| `INV-TRACE-EXECUTION` | G-MACHINE/N14 preserve the full transition list; N08 folds that actual list, N29/N30 project categories/ordered reads, and N32 identifies each indexed prestate as the actual fuel-prefix final state. `Run.reads` is transition receipt filtering and `Run.steps` is transition length in Primitive. | Append a decorative read, reorder transitions, or invent a prestate independent of the preceding run. N14/N30/N32 and `occurrence_source` require equality at the original index/fuel. The checked `repeatedLoad_positions` example retains indices0/1 and PCs0/1 even when both receipts are identical. |
| `INV-STORE-AGREEMENT` | N34 quantifies every supplied raw memory whose values fit w and whose indexed replies agree with M at every canonical read, under D. It concludes equality of the entire decoded supplied run with E_queryBudget, using C.code and the same canonical initial state. `canonical_supplied_memory` obtains raw run equality from inherited `queryRun_agreement`/suppliedMemoryAgreement and derives safety for that equal run. | Demand an extra unproved safety premise for a sibling execution, or preserve only the answer while changing cost/trace. N34's exact whole-Run conclusion and independently written type exclude both weakenings. Agreement quantifies receipt membership only to select addresses; the conclusion still preserves the complete ordered run and every repeated occurrence. |
| `INV-READ-BACKING` | N32/N40 assume an actual transition at index and its actual receipt, then give running fetch/execute, address from the prestate register and reply from `decodeMemory C.memory[address]?`. Successful reply additionally fits w. Under ValidRange, inherited noFailedLoads and N14 establish successful backing throughout the canonical query. | Fabricate a successful reply at an absent cell, or attach a read to a non-load instruction. N32/N40 and `queryRun_read_at` force the actual indexed lookup and load constructor; G-FAULT fixes missing cells as reply none, not a fabricated value. |
| `INV-WORD-WIDTH` | N01/N02 preserve the declared width; N11 plus `valid_iff` gives canonical code/memory words in C. N24/N31/N40 cover static fields, actual transition operands/poststates and successful read values; inherited finalStateFit and G-MACHINE canonical-state preservation cover final registers/PC/halt packet. | Introduce high padding or a result≥2^w while leaving byte length unchanged. Canonical's value bound, `canonical_padding`, G-OPS success, N31/N40 and the checked nonzero-padding/overflow examples exclude it. Rounded byte capacity is not a replacement for the width predicate. |
| `INV-ADDRESS-WIDTH` | N23 covers every address≤C.memory.size, including the one-past-allocation sentinel; N24 covers every instruction in the entire P, including dormant fields. N31 expands Instruction.Safe, which includes all code fields and state Fits; N40 covers actual load addresses/replies. N37/N38 separately prove exact supported-host index conversion. | Fit an address in usize while it exceeds2^w, use an oversized dormant branch target, or omit a dead/sentinel address from the inventory. N23/N24/N31/N40 reject word-model violations; N37/N38 do not substitute for those proofs. Successful arbitrary-image code rows also satisfy N42's Fits witness. |
| `INV-INSTRUCTION-ATOMICITY` | Primitive.execute has the nine ordinary constructors; arithmetic dispatch calls one of ten declared word operations. G-MACHINE execute_encode transports that same constructor's state/receipt, and N14/N29/N41 preserve one transition and its category. Select/rank/fringe traversal is compiled into P's primitive sequence; it is not hidden inside a new native instruction constructor. | Replace one primitive with an uncharged recursive select/rank evaluator while claiming the same trace/count. `execute_encode`, Primitive.execute's equations, N14/N29/N41 and the full category consumer constrain the modeled transition. Multiprecision byte decoding/Nat arithmetic are runtime work under the accepted word-RAM primitive model, not a theorem of physical constant time. |
| `INV-PROGRAM-ACCOUNTING` | P is the closed queryProgram; geometry is loaded from counted metadata. N22 fixes budget/program length837572, register count8271, scratch8274, and encoded fields≤5*budget. N19 counts C.wordCount*w plus (queryRegisterCount+3)*w; N21 uses exactly the flattened Instruction.encoding fields of P plus M, rounding and framing; N20 supplies both LittleOLinear residuals. | Insert size-dependent constants into an uncounted native code cache or omit opcode/operand/scratch cells. C's encodeCode identity, N19/N21/N22 and their literal consumers require the code actually executed and its scratch count. No Array-header or allocator-byte bound is inferred from this numeric account. |
| `INV-ORACLE-INDEPENDENCE` | G-WITNESS's arrayRun_exact connects the raw array reference to Q. WitnessExport compares its result with both a frozen literal answer and scanWindow/public queryTraceResult, then exports actual raw counts/ordered receipts. N14/N15/N25/N39 connect the independently obtained result to the native source and leftmost List Int semantics. | Copy expected results from native output or use a semantically unrelated raw program/memory. The actual exporter main supplies P.toArray/M, pins the canonical exported program hash, and checks literal/reference/scan agreement; arrayRun_exact and N25/N39 reject a different semantic result. File/source pin checks and independent replay are still needed to validate the operational artifact chain. |
| `INV-VALIDATION-REACH` | Validation.PackedNative imports Contract and runs nativeLoadEntry then nativeQueryEntry/nativeCore on the loaded image. N06/N07/N08 specify these exact source declarations; compare mode consumes independent expectation bytes. Its imported Contract includes the composed limb/parser execution, not merely Packed.ArrayRun. | Point validation at the predecessor finite-Nat or raw evaluator while leaving the new core unused. The actual validator call sites plus N06/N07 source consumers are the source surfaces; a production entry-source mutation/control must demonstrate that the delivered route notices the redirect. The old eight reference exports alone do not discharge this ID. |
| `INV-ALL-SIZE` | N11/N13/N17–N24 hold for every List Int or n without host support. N14/N15 quantify all fuel and endpoints in D; valid queries get N25/N39, while representable-invalid queries get N26/N27. canonical_run_safe derives safety uniformly. N12/N16/N35–N38 impose host support only on the finite API, and G-FILE's scalar framing admits all Nat lengths abstractly. | Add an unmentioned readiness cutoff, require n≥some fixture size, truncate headers to64bits, or drop invalid representable endpoints. The universal literal types N11/N13/N14/N15/N17/N27 and G-FILE's image roundtrip exclude those narrowed propositions. An unsupported enormous host instance is not claimed executable. |
| `INV-PROOF-SEPARATION` | NativeCore takes only the loaded image, endpoint words, fuel and reads flag. The Capstone/Contract records and canonical safety proofs are Prop inputs to reasoning, not query arguments. N08 is a projection of actual runThin execution; N09 excludes accumulated reads in default mode. `loadedProgram`'s raw Program witness is existential in Prop, not a runtime cache. | Feed scanWindow, a proof-held answer, or the existential Program witness into the native runtime. The concrete nativeCore/entry signatures and N07/N08/N15 fix the computation without those inputs; N25 is a correctness conclusion about it. Compiler proof erasure remains part of the stated Lean compilation assumption. |
| `INV-NO-SYNTHETIC` | N32 supplies the producing instruction, prestate and execute equation for every actual receipt; N33 and G-WITNESS identify the full ordered semantic expansion. N08/N29/N30 derive observations from those same transitions. | Compute an answer elsewhere and append plausible load events afterward, or add decorative rereads. N14/N15 preserve the entire computation; N32/N33 and staged_receipt_at/occurrence_source require real producing occurrences. Equality of a surrounding trace record by itself would not establish this, so the value dependency chain above is also required. |
| `INV-CATEGORY-SEPARATION` | N18/N19/N20 concern numeric payload/code/scratch capacity and residuals; N21 adds exact limb rounding and framing. N08/N09 concern optional observations; N28/N29/N41 concern modeled steps and six categories. G-HOST concerns bounded runtime inputs. None equates these quantities with native wall time, object headers or allocator use. | Relabel model ticks as CPU instructions, omit padding from file size, or equate byte-valued Array slots with one physical byte each. N21's exact equation and N41's model partition distinguish their quantities; the source assumptions explicitly leave physical container/time claims outside their conclusions. A documentation overclaim needs claim review, not a fictitious Lean theorem rejecting prose. |
| `INV-PUBLIC-COMPOSITION` | N11–N16 join validity, serialized identity, all-fuel execution and the actual source on C/M/P/w/I; N18–N22 count the same image/program/scratch; N25/N39 give scanWindow and LeftmostArgMin for ValidRange. `publicContract` consumes the entire NativeExecutionCapstone at once. | Conjoin a storage theorem for one image with an execution theorem for another, or mix a host-limited theorem with an unguarded all-size claim. N13/N14/N15/N19/N21 and publicContract demand the same explicit arguments/quantifiers. The final field/public-collapse campaign must exercise these consumer dependencies. |
| `INV-CERTIFICATE-ANTI-BYPASS` | All42 fields have separately written literal N01–N42 consumers, and publicContract states the record proposition independently. This is checked dependency structure; the pending contract runner has baseline, every field weakening, and public-type-collapse cases with the designated consumer. | Delete/replace a mandatory field, weaken its proposition, or set the public theorem type to True while allowing the changed producer to elaborate. The corresponding Nxx/publicContract is the required rejecting surface. Stock #print axioms does not replace this dependency check, and source inspection alone does not claim the42 mutation outcomes. |
| `INV-MUTATION-REPRODUCIBILITY` | Operational registries/runners pin source paths and exact rosters, require the chosen mutation to change bytes, compile/execute the specified surfaces, and restore tracked bytes/diff state in finally. N01–N42/publicContract provide the typed target surfaces; native entry/witness consumers provide runtime targets. | Mutate only an unreferenced helper, silently omit a field, use a vacuous textual replacement, or retain edited bytes after an exception. The production exact-roster/no-op-mutation/restoration guards and designated typed consumer outcomes must reject these cases. Historical leaf examples or transcripts alone are not a substitute for the pending committed final campaigns. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | C is one pre-execution image of M/P. N14 covers the entire fuel run, N32 backs every indexed transition receipt, N33 expands the complete public query trace after the174-entry metadata prefix, and N34 handles agreeing supplied stores. G-WITNESS ties concrete select/fringe/interior/rank occurrences to that one global trace. N23/N24/N31/N40 cover the address/operand domains, including dead/sentinel cases. | Prove only a suffix, reset receipt numbering between stages, or use a new private allocation for one fringe. The full Q_f identity N14, cumulative N33/G-WITNESS offsets and N32's global prefix/prestate exclude those substitutions. The inherited word-RAM machine is the physical-cell model; native CPU microsteps are not claimed to match it one-for-one. |
| `INV-WIDTH-SCALING` | N17 proves `log2(n+2)+1 ≤ wordWidth n ≤ 192*(log2(n+2)+1)` for the same query-independent w stored in C. N11/N23/N24/N31/N40 instantiate that w on all stored values, entire code, one-past addresses and actual transitions; N18/N19/N21 use it in capacity/accounting. | State a logarithmic bound for an unused width while executing on64bits, or choose width from each query instead of xs.length. C's field identities and N14/N17/N19/N23/N24/N31/N40 tie the bound to the actual image/execution. Abstract logarithmic width does not remove fixed-host limits. |

## Existing leaf evidence and pending campaigns

These receipts were read, not rerun. They establish the indicated source/leaf
checks, with the ordinary Lean kernel trust base recorded by their inventories;
they do not certify an unchanged final executable or a pending mutation roster.

| Existing receipt under `commands/` | Recorded result | What it supports here |
| --- | --- | --- |
| `capstone-03.json`; `contract-02.json` | exit0, 4.970s; exit0, 7.309s | The joined42-field proposition and42 independently written consumers at the pinned producer/consumer bytes. |
| `limbs-checks-02.json` | exit0, 12.474s | Independent operation success/acceptance types;29 concrete arithmetic/comparison/width/fault cases. |
| `machine-checks-01.json` | exit0, 9.315s | Whole-run and every observation projection, loaded-state and quiet-fold consumers; concrete failed load/fetch/code/divisor/halt/padding behaviors. |
| `machine-codefacts-checks-01.json` | exit0, 4.320s | Successful row decoding implies exact encodeInstruction/Fits; whole code has a same-order raw-program witness. |
| `binary-checks-06.json` | exit0, 6.617s | 37 image/field/roundtrip/injectivity/truncation/validity/host-limit checks. |
| `cursor-checks-02.json` | exit0, 9.031s | Independent all-byte decoder equality, successful supported-domain and bounded scalar/word parser consumers, plus direct rejection examples. |
| `witness-proofs-02.json`; `witness-export-check-03.json` | exit0, 12.735s; exit0, 8.475s | Universal stage/receipt/transition/reference connection and exporter source elaboration. |
| `witness-export-01.json`; `witness-export-artifacts.json` | exit0, 403.369s; exact artifact inventory | Seven actual exports: canonical-select-left, canonical-select-right, canonical-left-fringe, canonical-right-fringe, canonical-rank-interior, canonical-rank-final, canonical-cross-cell. The canonical program's uncompressed SHA is `2D978D9D81CC3326F623F3A21AFCDA9FE3329E6F1DB60B2000425C4EF0A0D875`, equal to the committed gzip's decompressed bytes. |
| `native-axioms-02.json` | exit0, 141.177s | 86 printed inventories contain only propext/Classical.choice/Quot.sound; this is trust evidence, not field-mutation dependency evidence. |
| `validator-02.json`; `validator-default-01.json` | exit0, 10.122s; exit0, 6.710s | Development validator elaboration and16/16 default execution. Final selector/compare/native campaign identity remains separately recorded by the coordinator. |

The true cross-cell witness uses width184, a six-bit logical span beginning at
bit offset180, and actual adjacent successful addresses179/180 at transition
indices10378/10384. The two select witnesses retain distinct call-site/logical
ordinals and transition positions even when an early physical address/reply is
equal. These are concrete anti-vacuity evidence from the exporter; their checked
numeric expectations still must be replayed through the delivered native clients.

The **42-field weakening/public-proposition campaign and final native runtime
campaigns are pending in this document**. Their existence in source, and earlier
leaf/selector controls, do not imply that their final complete rosters passed.
The root will append exact source/artifact pins, executed/expected cases,
designated failures, positive controls and restoration evidence after execution.
The concrete operational surfaces include
`scripts/packed_native_contract_replay.ps1` (baseline, `field-n01` through
`field-n42`, and `public-type-collapse`, exact source pins, designated consumers
and finally restoration), `scripts/packed_native_binary_replay.ps1`,
`scripts/packed_native_binary_controls.ps1`, and
`scripts/packed_native_validator_controls.ps1`; their committed registries and
final receipts govern operational verdicts rather than this prose inventory.
The default build, explicit import checks, final policy/claim checks and scheduled
audit similarly retain their own evidence and authority.

## Digestion and qualifications

The reconstruction ties the substantive source propositions to one actual
allocation and execution. The important strengthening beyond an ArrayRun-style
fetch adapter is the complete stored-byte machine and loaded-image refinement,
including real value updates, all-fuel behavior, positional repeated reads,
primitive categories, and complete code/data/scratch accounting. Generic unsafe
or malformed states have explicit checked behavior; canonical safety is derived,
not assumed for an unrelated run. Mathematical all-size statements and finite
host support are visibly different propositions.

No substantive missing inherited source invariant, quantifier, or object-identity
obligation was identified in this reconstruction. This finding does not close
any full frozen criterion: foreign compilation/runtime/ABI assumptions, actual
marshaling and ownership, complete mutation/replay outcomes, source/artifact
identity, allocation availability and final audit remain separately assessed.
The C-facing contract requires valid owned handles/readable spans and the supported
runtime/thread discipline; the Lean source theorem does not prove arbitrary
foreign pointer safety. Numeric word/byte equations do not count Array headers,
boxed slots, temporary BigNat values or allocator overhead, and they do not give
physical constant-time multiprecision operations.

A skeptical reader should next compare the final operational receipts with these
same fields and objects: did each weakened proposition break its independently
typed consumer, did the actual loaded clients reproduce every ordered observation
from the independent oracle, and did all source/artifact bytes restore exactly?
Those are the coordinator's pending campaigns, not conclusions supplied by this
document.

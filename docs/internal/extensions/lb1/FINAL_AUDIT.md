# LB1-BLIND3 independent exact-commit audit

## Findings and verdict

**Verdict: INCOMPLETE.** The source audit and delivered local execution evidence support the frozen LB-1 contract. I found no load-bearing source, proof, model, or public-consumer defect. Required coordinator certification remains outstanding.

- **P0:** None found.
- **P1-01 — Required final certification is pending.** No exact-target full `lake build` or aggregate `scripts/gate.ps1` outcome was supplied. The report-containing durable tree also does not yet exist, so its strict claim, applicable design-decision, and whitespace checks cannot yet be certified. These are pending evidence conditions, not observed command failures. The smallest completion step is coordinator-owned execution and delivery of those outcomes, followed by explicit acceptance review.
- **P2:** No source defect found. Windows process ownership was exercised; POSIX ownership remains unobserved on this host. The report does not promote the Windows result into cross-platform evidence.
- **P3:** No documentation repair identified in the reviewed public addenda. Restoration evidence has the limitation stated below: source equality is independently corroborated, while restoration of the two overwritten producer oleans relies on the runner’s checked byte comparisons and successful completion. Separate baseline artifact digests were not persisted.

The weaker proposition “the local source and finite checks are satisfactory” must not be substituted for the required proposition “all required exact-target and report-containing-tree certification is complete.”

## Identity, independence, and scope

Status: CANDIDATE_COMPLETE

That parser token describes completion of this audit worker’s assigned report. It does not describe implementation acceptance and does not override the **INCOMPLETE** audit verdict.

| Item | Audited identity |
|---|---|
| Mode | Fresh blind, independent, read-only, exact-commit audit |
| Source target | `5033ce54da233fc7a3df319d50ab09a2ebee523a` |
| Base and workflow governance | `0e6a00f654abc64f8b68988fa9675b9a839dca2f` |
| Frozen contract checkpoint | `0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2` |
| Candidate branch label | `codex/lb-1-variable-payload` |
| Physical audit checkout | `C:/Users/poin/.codex/worktrees/2270/RMQ/.lake/lb1-final-audit-3/checkout` |
| Frozen prompt | `C:/Users/poin/.codex/worktrees/2270/RMQ/.lake/lb1-final-audit-3/AUDIT_PROMPT_READY.md` |
| Prompt SHA256 | `B872E9EEC5B5C4C011D109F6CA55A72E26E7AA75DFDFF566D5E39F965AD794BB` |

Every shell call used the physical audit checkout explicitly. HEAD resolved to the target; governance and contract ancestry checks passed. The checkout remained clean. I made no file edits, executed no Lean/Lake/runtime/replay command, inspected no running Lean process, and performed no integration or cleanup.

The actual nonempty runtime RMQ catalog contained the unique names `rmq-audit-prompt`, `rmq-coordinator`, and `rmq-proof-sprint`. This audit-worker contract intentionally selects no project role skill. The following no-role preflight passed against the exact governance frontier:

```powershell
& scripts/project_skill_preflight.ps1 `
  -GovernanceRef 0e6a00f654abc64f8b68988fa9675b9a839dca2f `
  -AllowNoRequiredSkills `
  -RuntimeProjectSkills 'rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint'
```

The complete canonical project skill set was present. I followed the frozen prompt and `docs/internal/AUDIT_PROTOCOL.md`; I did not substitute coordinator-side prompt authoring for audit work.

I did not read prior audit reports or verdicts, worker reports or completion narratives, session/chat logs, or parent mutable source. Completed neutral raw records were read only after delivery authorization. Parent messages identifying completed stages were treated as availability notices; their claimed outcomes were independently checked against the records. I did not call the agent-list tool or delegate another audit.

For compact citations below:

- **E** = `RMQ/Core/EncodingVariableLowerBound.lean`.
- **A** = `RMQ/Core/WordRAM/Packed/AllocationLowerBound.lean`.
- **V** = `RMQ/Validation/VariablePayloadLowerBound.lean`.
- **R** = `scripts/variable_payload_replay.ps1`.
- Other packed-machine filenames refer to `RMQ/Core/WordRAM/Packed/`; `Primitive.lean` and `Calculus.lean` refer to the WordRAM core.
- Line references identify the exact target, except explicitly marked mutated diagnostic lines.

The immutable source packet’s 33 source records matched their hashes. The three new module hashes were:

| Source | SHA256 |
|---|---|
| E | `688E98C5FBCC12D17CB475FD4B381B707EC224805C9A3C1C0B1858B3270B1FFA` |
| A | `FB78AD4A5C23709E0EAB724D02F5DEB46E23A535D5AC63CC6E2B4DE54192972D` |
| V | `092B965AB266D1578A1CDD83A05BAC31644F14CE4400C380CD78032EA5850B72` |

The audit checkout’s line-ending conversion was checked separately from raw packet equality. CRLF/LF equivalence was not described as equal raw bytes.

## Reconstructed mathematical and operational claim

The generic encoding is one fixed pair of functions for each `n,B`, with a size bound and exactness across **every** `List Int` of length `n` (E:124–130). Its decoder receives bits and endpoints; the fixed encoding object does not vary with the input being queried.

The finite universe contains every Boolean list of length at most `B`, exactly once. Its cardinality is `2^(B+1)-1` (E:23–117). Equal encodings imply equal valid RMQ answers, hence `SameRMQBehavior`, hence equal Cartesian shape. Executable size-`n` representatives then give an injection from the complete size-`n` shape universe into that bounded bitstring universe (E:137–201). Shape injectivity is derived, not inserted as an assumption.

The lower-bound bridge uses the existing Catalan counting inequality and the established doubled-log-slack bridge with bit parameter `B+1`. Thus:

```text
shapeCount n ≤ 2^(B+1)-1
doubledLogSlackLower n ≤ 2*(B+1)
```

Here `doubledLogSlackLower n` is the repository’s natural-number expression
`4*n - (3*Nat.log2 (2*n+1) + 3)`. The relevant predecessor surfaces are `EncodingLowerBound.lean:1419`, `EncodingLowerBound.lean:1654`, and `LowerBound.lean:345`. The coefficient is preserved; the observed-length model is not silently replaced by a fixed-length model.

The concrete encoding serializes **all actual** `buildMemory xs` cells at `wordWidth xs.length` (A:23–30, A:72–81). Positive width and per-word bounds yield a left inverse on arbitrary finite word lists and then injectivity (A:42–69). Retaining serialized length distinguishes `[]`, `[0]`, and `[0,0]`; zero padding to an externally chosen common length would lose this property.

The decoder is:

```text
allocationDecoder n bits left right
  = queryNat (deserializeWords (wordWidth n) bits) n left right
```

It does not receive or close over `xs` or a shape. The proof establishes:

```text
reconstructedMemory xs = buildMemory xs
```

and consequently equality of the **whole** machine run for every endpoint pair and fuel (A:83–103, A:206–209). The reconstructed machine certificate is transported through this memory equality, not assembled from a sibling store (A:214–395).

The uniform budget is explicitly:

```text
UniformAllocationBudget n B :=
  ∀ xs, xs.length = n →
    (buildMemory xs).length * wordWidth n ≤ B
```

The generic theorem is instantiated by the actual allocation encoding (A:155–202). The canonical `2*n + allocationRho n` budget is inhabited by the existing upper-capacity theorem. The result constrains a budget that works across all size-`n` inputs; it does not assert a lower bound on each input’s individual allocation.

I also followed the recovered-store consumer through the predecessor machine:

- `Primitive.lean:133–197` makes load replies affect registers, computes scalar operations from registers, branches on registers, and obtains results from halted state. Receipts and transitions arise from these steps.
- `QuerySource.lean:24–72` supplies one fixed program and invokes it on memory, `n`, and endpoints.
- `Allocation.lean:49–158` places shape-dependent descriptors, counts, and packed data in the counted allocation.
- `Setup.lean:371–393` constrains the loaded destination register; its dependency witness cannot be satisfied by a changed log alone.
- `Locate.lean:474–508` and `Locate.lean:1002–1019` constrain returned locations, with the latter’s explicit segment/index/count guards retained.
- `SpanAssembly.lean:61–78` constrains actual output registers and receipts for arbitrary supplied memory.
- `ReadInterface.lean:75–84` universally constrains reader invocation outputs and receipts. `PhysicalRead.lean:166–233` discharges that interface for the canonical store.
- `LogicalSpan.lean:24–37` and `LogicalSpan.lean:442` connect segment addressing to the global allocation.
- `Calculus.lean:176–262` proves positional load backing and equality of the entire run under supplied-memory agreement, including failed reads.
- `QuerySafety.lean:434–543` supplies canonical safety and same-allocation width/capacity facts.

The concrete dependency witnesses are supporting controls. They are not represented as universal claims that every memory cell affects every query. The general support comes from the operational evaluator and its quantified reader/refinement theorems.

## Exact public consumer propositions

The following tables reconstruct all 49 literal typed consumers. They are not merely a list of field names.

Notation used only to shorten the tables:

```text
n = xs.length
w = wordWidth n
S = buildMemory xs
A = reconstructedMemory xs
bits = allocationBits xs
U(n,B) = UniformAllocationBudget n B
L(n) = doubledLogSlackLower n
C(n) = 2*n + allocationRho n
I = initialState n left right
R_f = run A queryProgram f I
R = R_queryBudget
H = left < 2^w ∧ right < 2^w
Valid = left < right ∧ right ≤ n
Q = SuccinctClassic.queryTraceResult xs left right
```

All free inputs in each proposition are universally quantified. Conditions written in a row are retained conditions; they are not silently inferred. `LeftmostArgMin`, `Instruction.Fits`, `Instruction.Safe`, `State.Fits`, `ValidRange`, and `LittleOLinear` were expanded using V:301–369 and their defining modules.

For every O row, the consumer projects `packedAllocationOptimality_holds.<field>`. For every M row, it projects `packedAllocationOptimality_holds.machine.<field>`. In all 49 mutations, replacing the advertised field proposition with `True` and supplying `True.intro` allowed the producer to compile and caused its own literal typed consumer to fail at the line listed.

| ID / field | Required proposition P | Consumer / observed diagnostic |
|---|---|---|
| O01 `wordRoundTrip` | `0 < width` and every word `< 2^width` imply `deserializeWords width (serializeWords width words) = words`. | V:21–24 / 24 |
| O02 `wordSerializationInjective` | At positive width, two finite lists whose entries fit that width and whose serializations agree are equal. | V:26–30 / 30 |
| O03 `serializedLength` | `bits.length = S.length * w`. | V:32–34 / 34 |
| O04 `memoryRecovery` | `A = S`. | V:36–37 / 37 |
| O05 `decoderExact` | `allocationDecoder n bits left right = if ValidRange xs left right then some (scanWindow xs left (right-left)) else none`. | V:39–42 / 42 |
| O06 `decoderLeftmost` | Decoder result `some index` implies `LeftmostArgMin xs left right index`. | V:44–47 / 47 |
| O07 `sameShapeMemory` | `shape xs = shape ys → buildMemory xs = buildMemory ys`. | V:49–51 / 51 |
| O08 `shapeInjectivity` | For two members of `shapesOfSize n`, equal serialized allocations of their representatives imply equal shapes. | V:53–55 / 55 |
| O09 `uniformBudgetCount` | `∀ n B, U(n,B) → shapeCount n ≤ 2^(B+1)-1`. | V:57–58 / 58 |
| O10 `uniformBudgetLower` | `∀ n B, U(n,B) → L(n) ≤ 2*(B+1)`. | V:60–62 / 62 |
| O11 `canonicalCount` | `∀ n, shapeCount n ≤ 2^(C(n)+1)-1`. | V:64–65 / 65 |
| O12 `canonicalLower` | `∀ n, L(n) ≤ 2*(C(n)+1)`. | V:67–69 / 69 |
| O13 `upperCapacity` | `bits.length ≤ C(n)`. | V:71–73 / 73 |
| O14 `allocationResidualLittleO` | `LittleOLinear allocationRho`. | V:75–76 / 76 |
| O15 `runIdentity` | For every fuel, `R_f = run S queryProgram fuel I`. | V:78–81 / 81 |
| O16 `machine` | `ReconstructedPackedQueryCapstone`, with the 33 propositions below. | V:83–84 / 84 |
| M01 `allocationResidualLittleO` | `LittleOLinear allocationRho`. | V:89–90 / 90 |
| M02 `completeResidualLittleO` | `LittleOLinear queryCompleteRho`. | V:92–93 / 93 |
| M03 `widthBounds` | `∀ n, Nat.log2(n+2)+1 ≤ wordWidth n ≤ 192*(Nat.log2(n+2)+1)`. | V:95–97 / 97 |
| M04 `dataCapacity` | `A.length*w ≤ 2*n + allocationRho n`. | V:99–101 / 101 |
| M05 `completeCapacity` | `(A.length + (queryProgram.map Instruction.encoding).flatten.length + (queryRegisterCount+3))*w ≤ 2*n + queryCompleteRho n`. | V:103–107 / 107 |
| M06 `memoryWordsFit` | Every `word ∈ A` satisfies `word < 2^w`. | V:109–110 / 110 |
| M07 `allocationAddressesFit` | Every `address ≤ A.length` satisfies `address < 2^w`. | V:112–114 / 114 |
| M08 `programFieldsFit` | For every `n` and every instruction in the complete fixed program, `instruction.Fits (wordWidth n)`. | V:116–117 / 117 |
| M09 `budgetExact` | `queryBudget = 837572`. | V:119–120 / 120 |
| M10 `programLength` | `queryProgram.length = queryBudget`. | V:122–123 / 123 |
| M11 `encodedProgramBound` | Flattened instruction encoding length `≤ 5*queryBudget`. | V:125–126 / 126 |
| M12 `registerCount` | `queryRegisterCount = 8271`. | V:128–129 / 129 |
| M13 `scratchCount` | `queryRegisterCount + 3 = 8274`. | V:131–132 / 132 |
| M14 `unusedRegisters` | For every fuel and register `r ≥ queryRegisterCount`, `R_f.final.regs r = 0`. | V:134–136 / 136 |
| M15 `validInputs` | `ValidRange` implies `encodeInputs n left right = some I` and both endpoints fit `w`. | V:138–141 / 141 |
| M16 `natContract` | `queryNat A n left right = if ValidRange then some (scanWindow xs left (right-left)) else none`. | V:143–146 / 146 |
| M17 `leftmost` | `queryNat A n left right = some index → LeftmostArgMin xs left right index`. | V:148–150 / 150 |
| M18 `result` | `H → R.result = some (optionNatPacket Q.value)`. | V:152–156 / 156 |
| M19 `halt` | `H → R.final.status = .halted (optionNatPacket Q.value)`. | V:158–162 / 162 |
| M20 `invalidGuard` | `H → ¬ValidRange → R.result = some 0 ∧ R.reads = []`. | V:164–168 / 168 |
| M21 `stepBound` | `R.steps ≤ queryBudget`. | V:170–172 / 172 |
| M22 `categoryPartition` | `R.steps` equals the sum of memory-read, register-write, arithmetic, comparison, branch, and control category counts. | V:174–179 / 179 |
| M23 `finalStateFit` | `H → R.final.Fits w`. | V:181–184 / 184 |
| M24 `transitionSafety` | Under `H`, every indexed transition has `Instruction.Safe w before instruction` and `after.Fits w`. | V:186–191 / 191 |
| M25 `prefixSafety` | Under `H`, every fuel `≤ queryBudget` has `R_f.final.Fits w`. | V:193–197 / 197 |
| M26 `readWidth` | Under `H`, each receipt of an indexed transition has address `< 2^w`, reply `A[address]?`, and every successful returned value `< 2^w`. | V:199–206 / 206 |
| M27 `positionalReadBacking` | An indexed receipt’s transition begins at the corresponding run prefix in running status, fetches its instruction from the program, equals actual `execute A`, is a load, reads the address in its address register, and replies with `A[address]?`. | V:208–216 / 216 |
| M28 `orderedLogicalRefinement` | `R.reads` is, for a valid range, the ordered 174 metadata receipts followed by `logicalTraceReads (shape xs) A Q.trace`; otherwise it is `[]`. | V:218–225 / 225 |
| M29 `logicalReadOnly` | `ReadOnlyTrace Q.trace`, expanded to read-word events. | V:227–229 / 229 |
| M30 `suppliedMemoryAgreement` | If supplied `memory` agrees with `A` at every address in `R.reads`, including `none` replies, its whole run equals `R`. | V:231–236 / 236 |
| M31 `specResult` | `ValidRange → R.result = some (scanWindow xs left (right-left)+1)`. | V:238–241 / 241 |
| M32 `noFailedLoads` | `ValidRange → ∀ receipt ∈ R.reads, ∃ value, receipt.reply = some value`. | V:243–246 / 246 |
| M33 `invalidGuardSteps` | `¬ValidRange → R.steps ≤ 6`. | V:248–250 / 250 |

`H` is required by the raw machine’s representable-input safety/result statements. The total `queryNat` and serialized decoder statements retain their outer guard and cover every natural-number endpoint. `ValidRange` implies representability through M15. The audit does not conjoin an unguarded wrapper theorem with a differently guarded raw machine theorem while forgetting that relationship.

V:256–273 supplies a separate composed consumer containing arbitrary-budget lower bound, explicit valid-range decoder exactness, serialized length, recovered memory, and actual upper capacity. V:275–377 additionally pins generic propositions, construction definitions, and canonical encoding fields. O09’s `with_reducible exact` preserves the literal required proposition; the S03 run demonstrates that the canonical-budget sibling fact cannot satisfy it.

## All 29 frozen requirements

Each requirement below is reproduced verbatim. “Satisfied in source and local evidence” means the stated proposition and relevant delivered checks survived this independent audit. It does not clear P1-01 or record coordinator acceptance.

### REQ-LB-COUNT

> Define payload-only exact RMQ encodings by bitstrings of length at most B, allowing length to be observed. Prove the finite cardinal bound 2^(B+1)-1 and shape injectivity from valid half-open leftmost answers. Derive the coefficient-correct doubled Catalan lower bound at 2*(B+1), or a strictly sharper bound proved from the same model.

**Disposition: satisfied in source and local evidence.** E:61–117 proves complete membership, no duplicates, and exact cardinality. E:137–211 derives shape injection, count, and the doubled bound from exact answers. The fixed `query_exact` quantifies over all size-`n` inputs and nonempty valid windows. Representative length and shape facts come from `Shape.lean:966–1075`; complete shape enumeration and no duplicates are established at `Shape.lean:1228–1242` and `Shape.lean:1695`.

The generic typed consumer and V:275–299 retain these propositions. G01 changes the lower proposition to `True` and fails that consumer; G02 deletes `query_exact` and fails the derivation at `sameRMQBehavior_of_encode_eq`. Size-`n` inputs exist by replication (E:214–216). Empty-size vacuity is explicit and does not replace positive-size exactness.

### REQ-LB-PQ1

> Serialize the actual PQ1 buildMemory cells at wordWidth n, fixed for each n, and prove serialization injective on finite word lists with entries below 2^wordWidth(n), allocation encoding injective on size-n Cartesian shapes, and the decoder's exact RMQ contract using only serialized cells, n, endpoints and n-only fixed advice. The decoder must not retain xs or an uncounted shape. Distinct List Int inputs with the same shape intentionally share memory: no value-list injectivity is asserted. Address variable allocation length explicitly; plain zero padding is not injective.

**Disposition: satisfied in source and local evidence.** A:23–151 supplies the word-list left inverse/injection, actual serialized allocation, total decoder, same-shape sharing, and representative-shape injection. O01–O08 independently project the required propositions. The chain is actual `buildMemory` → serialization → exact recovered memory → `queryNat` on that recovered memory.

The decoder definition has only bits, `n`, and endpoints. Width depends only on `n`. R04/R05 distinguish positive-width empty/all-zero allocations and exhibit the excluded zero-width collision. R06 uses distinct value lists with the same memory. D01/D02 falsify the exact decoder proposition; D03 first falsifies actual serialized length.

### REQ-LB-MODEL

> Prove a worst-case-over-inputs lower bound on a uniform allocation budget and a two-sided comparison with the actual PQ1 2n+rho(n) allocation. Separate payload, fixed code, scratch and external n/advice conventions. Do not equate a fixed-length encoding with a variable-length one or assert the lower bound for every individual input.

**Disposition: satisfied in source and local evidence.** A:155–202 fixes the universal allocation-budget predicate and instantiates the generic encoder with actual serialized memory. O09/O10 use arbitrary `B`; O11/O12 specialize to the proven canonical budget; O13/O14 provide actual upper capacity and little-o residual. The budget domain is inhabited by the upper theorem.

M04 and M05 distinguish data capacity from complete machine capacity including fixed program and scratch. External `n`, common advice, serialized conversion cost, and Lean runtime remain separate. S03’s canonical-count proposition Q is strictly the wrong proposition for arbitrary-budget P and fails at V:58.

### REQ-LB-CONSUMER

> One checked capstone/typed consumer must compose the generic counting theorem, exact decoder and actual allocation object; independently expand its predicates to exclude vacuous domains and proof-only decoding oracles.

**Disposition: satisfied in source and local evidence.** A:401–458 constructs the 16-field certificate from the generic theorem, actual allocation encoding, recovered run, and reconstructed machine. V:17–18 and V:256–273 consume the public proposition and explicit conjunction. V:301–377 pins definitions and canonical encoding identity.

`ValidRange` expands to a nonempty half-open interval; `LeftmostArgMin` includes position, minimum value, and tie policy. Positive-size controls exercise those domains. P01 rejects a public theorem weakened to `True`; H01 rejects empty-only decoder exactness. S01/S02 reject sibling memory/run identities.

### CHK-LB-CONTROLS

> Persist empty/singleton, equal-key/leftmost, all-zero/empty-string collision, null/wrong-answer decoder, deleted exactness, permitted n-only advice and rejected input/shape-dependent advice controls. A mutation must fail the same proposition as the positive theorem, not merely change a surrounding log or a declaration name.

**Disposition: satisfied in source and local evidence.** E:242–325, V:379–419, the generic consumer, and runtime cases R01–R06 cover the specified controls. The n-only advice constructor fixes common advice before all-input exactness. A zero-payload, input- or shape-varying decoder oracle cannot satisfy the single universal size-two exactness proposition; the generic controls retain those quantifiers.

G02, D01/D02/D03, H01, and the exact typed field mutations have required semantic failure surfaces. Baseline and harmless proof-wrapper expected-accept controls pass. Failure is not inferred from output-record inequality.

### REPLAY-EXACT-REGISTRY

> any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

**Disposition: satisfied in source and local evidence.** R:21–137 has an independent literal v3 registry checked against `REPLAY_REGISTRY.json`, including kinds, fields, verdicts, surfaces, order, and nonemptiness. The completed run has exactly 63 expected and executed IDs, in committed order, with 134 unique raw stages. Six runtime IDs are separately fixed. Missing-case controls reject.

### REPLAY-SELECTOR-NONVACUITY

> omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

**Disposition: satisfied in source and local evidence.** R:87–137, R:229–278, and V:518–575 implement the relevant parser and entry branches. Fresh focused replay selector records show omitted selection of all 63, valid selection of exactly A01, and nonzero empty/whitespace/malformed/unknown outcomes before case execution. Runtime startup lists six without executing them; a known selection executes R04; unselected runtime executes all six.

Supplemental external CLI/environment conflicts reject in both parsers. The valid channel `case:not an id` reaches malformed-ID rejection, distinct from malformed-channel rejection. None of those three probes emits case-pass or selector-pass output.

### REPLAY-SUBPROCESS-DEADLINE

> run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.

**Disposition: satisfied for the observed Windows execution; POSIX remains uncovered.** R:150–210 uses the existing owned-process helper and excludes resource/import failures from semantic rejection. R:315–333 and R:428–432 restore both mutated sources and both producer oleans, compare exact bytes, and check repository state in case and outer `finally` paths.

The Windows focused deadline test created child PID 3892, then timed out the owned tree after 30 seconds. The raw record lists that child among terminated IDs; the wrapper’s subsequent absence check passed. Stdout, stderr, timeout, exit, and ownership fields are retained. The report does not claim independent baseline-artifact digest comparison or observed POSIX execution.

### INV-STORE-IDENTITY

> the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient;

**Disposition: satisfied in source and local evidence.** A:72–103 proves serialization and exact recovery of `buildMemory xs`; A:206–209 equates every recovered run to the actual allocation run. O03/O04/O13/O15 and M04/M05 retain that chain. S01 and S02 weaken identity to reflexivity on recovered objects and fail V:37 and V:81 respectively.

### INV-VALUE-DEPENDENCY

> returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient;

**Disposition: satisfied in source and local evidence.** `Primitive.lean:133–153` writes actual replies into registers. The setup, location, span, and physical reader sources identified above constrain destination registers and returned locations. The canonical query refinement connects those operational values to the semantic answer; M18/M19/M31 retain result/status claims on the recovered-store run.

`Setup.lean:384–393`, `Locate.lean:1002–1019`, and `SpanAssembly.lean:499–503` supply correctly scoped value/route controls. Their guards and witness-only scope are retained. No trace-record inequality is used as the sole answer-dependency argument.

### INV-SEMANTIC-NONVACUITY

> semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself;

**Disposition: satisfied in source and local evidence.** `ReaderCorrect` quantifies over actual evaluator outputs, state, invocation arguments, and receipts (`ReadInterface.lean:75–84`); the canonical implementation proves it (`PhysicalRead.lean:166–233`). Compilation and query correctness derive the corresponding run from the fixed source program. These are operational predicates, not registry membership.

V’s literal predicate pins and positive-size fixtures exclude empty-domain substitution. The 49 `True` mutations and H01 demonstrate public-consumer sensitivity. No claim that every branch executes for every input is inferred from a source enumeration.

### INV-TRACE-EXECUTION

> traces and footprints are derived from the execution they describe;

**Disposition: satisfied in source and local evidence.** `Primitive.lean:163–197` forms runs, transitions, and filtered receipts from actual steps. `Compiler.lean:236`, `Compiler.lean:354`, `Compiler.lean:382`, and `Compiler.lean:418` connect source evaluation with compiled state/read behavior. M27/M28 retain positional execution and ordered refinement for the same recovered-store run; their mutations fail the respective exact consumers.

### INV-STORE-AGREEMENT

> supplied-store agreement determines result, cost, and the relevant trace;

**Disposition: satisfied in source and local evidence.** `Calculus.lean:200–262` proves whole-run equality from agreement on the actual reads, including failed replies. `QueryObservations.lean:24–62` specializes it, and M30 projects it for `A`. Whole-run equality constrains result, transitions, reads, and steps simultaneously. The M30 weakening fails V:236.

### INV-READ-BACKING

> every successful read is backed positionally by the counted store;

**Disposition: satisfied in source and local evidence.** M27 states indexed prefix, fetched instruction, actual execution, load constructor, register address, and `A[address]?` reply. M26 additionally bounds addresses and successful values; M32 proves successful loads on valid queries. A:83–103 identifies `A` with counted memory. F02 deletes positional backing and fails the exact M27 consumer at V:216.

### INV-WORD-WIDTH

> stored and returned words fit one declared modeled machine word;

**Disposition: satisfied in source and local evidence.** M06 and M26 use the same `wordWidth xs.length`; M23–M25 preserve state fit. `Width.lean:409–474` and `QuerySafety.lean:490–543` supply the actual allocation and execution facts. O01/O02 retain positive width and entry-fit hypotheses for arbitrary word-list serialization. No host integer-width claim is inferred.

### INV-ADDRESS-WIDTH

> every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands;

**Disposition: satisfied in source and local evidence.** M07 includes `address = A.length`, the first failed address; M26 covers executed receipts. M08 quantifies over every instruction in the whole fixed program. `Primitive.lean:53–108` defines constructor-exhaustive field fit, including registers, targets, and arithmetic operands, while M24/M25 constrain executed safety and state. V:301–369 pins these predicates; the M07/M08/M24–M26 mutations fail exact consumers.

### INV-INSTRUCTION-ATOMICITY

> each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive;

**Disposition: satisfied within the stated primitive model.** `Primitive.lean:28–42` and `Primitive.lean:133–153` perform scalar modeled operations, raw loads, branches, and halt. `Structured.lean:25–102` expands structured repetition and branches into the fixed instruction program; it does not make RMQ decoding one primitive transition. M21/M22 count and partition actual transitions.

Natural-number scalar arithmetic is the declared model operation; this does not prove corresponding Lean runtime cost. Serialization/deserialization is an encoding adapter and is not advertised as a constant-time charged query instruction.

### INV-PROGRAM-ACCOUNTING

> input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation;

**Disposition: satisfied in source and local evidence.** `QuerySource.lean:24–60` defines fixed code. `Guard.lean:18–29` initializes only public size/endpoints and zeros. Input-dependent metadata, including variable counts and descriptors, lives in the actual allocation (`Allocation.lean:49–158`) and is loaded operationally. M05/M08/M10–M14 account for fixed instruction encoding and modeled scratch. O03/O04 connect serialized bits to that entire memory.

### INV-ORACLE-INDEPENDENCE

> executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested;

**Disposition: satisfied in source and local evidence.** V:467–516 uses independently specified empty/singleton/leftmost results, explicit bit lengths and distinctness, and `scanWindow` for semantic expectations. The same-shape fixtures have distinct explicit input values. Expected answers are not copied from the decoder result. The fresh R01–R06 records execute those checks.

### INV-VALIDATION-REACH

> executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine;

**Disposition: satisfied in source and local evidence.** V imports the new allocation-lower-bound layer, and V:456–516 calls actual allocation, serialization, deserialization, and serialized decoder operations. The full runtime and fresh `RuntimeOnly` executions cover the six new cases. List/startup and historical predecessor builds were kept separate from query execution evidence.

### INV-ALL-SIZE

> exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch;

**Disposition: satisfied in source and local evidence.** The public exactness and capacity propositions quantify over every `List Int`; the raw safety guards are endpoint representability, discharged for valid ranges by M15. There is no added compact-readiness predicate or compatibility dispatch in A’s decoder. Empty/singleton and invalid-endpoint controls are present; H01’s empty-only proposition cannot satisfy O05.

### INV-PROOF-SEPARATION

> proof-only fields never carry answers or uncharged routing information;

**Disposition: satisfied in source and local evidence.** The executable decoder depends on serialized cells, size, and endpoints, and invokes the fixed machine. Proof certificates justify equality/refinement; they are not inputs to that execution. V pins encoding and decoder definitions. The universal generic exactness field cannot serve as a per-input runtime oracle. A02 adds harmless private proof material and still passes producer, metadata inventory, and consumer.

### INV-NO-SYNTHETIC

> synthetic events, decorative rereads, and post-hoc replay do not support the execution claim;

**Disposition: satisfied in source and local evidence.** Actual load instructions update registers used by setup, location, span decoding, and query computation. Ordered receipt refinement is proved from compilation and execution. `SpanAssembly.lean:19–78` constrains attempted accesses and output registers together. M27/M28 retain actual indexed execution and order; the claim is not obtained by attaching a separately generated event list to an answer.

### INV-CATEGORY-SEPARATION

> payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct.

**Disposition: satisfied in source and reviewed public wording.** O03/O13 concern serialized payload; M05 separately includes fixed program and scratch; M21/M22 concern modeled steps and categories. Runtime record durations measure validation execution only. The new family summary and digestion addenda preserve these distinctions and do not charge bit conversion into the fixed query budget.

### INV-PUBLIC-COMPOSITION

> a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. Conjoining true theorems about different payloads or guarded and unguarded executions is not closure.

**Disposition: satisfied in source and local evidence.** A’s memory equality and every-fuel run equality connect the actual serialized payload to the reconstructed capstone. The O/M table retains each actual object and guard. V:256–273 gives an additional explicit composition consumer. S01/S02/S03 and H01 reject precisely the sibling-object, wrong-budget, and narrowed-domain substitutions relevant here.

### INV-CERTIFICATE-ANTI-BYPASS

> every mandatory field advertised by a public certificate is projected by a checked typed consumer at the exact proposition and object arguments required by the acceptance contract. Deleting or weakening a field, or replacing it with a sibling fact, must break that consumer rather than leave only constructor initializers and prose unchanged.

**Disposition: satisfied in source and local evidence.** V:21–250 contains all 16+33 literal typed projections reconstructed above. The metadata checker obtains actual Lean structure information and requires exact ordered, parent-free inventories of 4, 16, and 33 fields. All 49 field-to-`True` producers compile and their designated consumers fail. F01/F02, S01–S03, H01, and P01 cover deletion, sibling, guard, and public-proposition bypasses.

### INV-MUTATION-REPRODUCIBILITY

> when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean. Report prose, copied terminal output, and dangling Git objects are not replayable evidence. A public theorem additionally has a checked exact-type consumer that fails when the advertised dependency is removed; `#print axioms` over the theorem's current type is not such a consumer.

**Disposition: satisfied for the declared finite campaign.** The runner, registry, mutation construction, declaration-boundary checks, consumers, and restoration logic are committed at the target. All 63 registry cases ran with the prescribed expected outcomes. P01/G01 demonstrate public/generic proposition dependence independently of axiom printing. Raw records and copied manifests are retained. This establishes the declared 63-case campaign, not universal completeness over all possible mutations.

### INV-GLOBAL-PHYSICAL-MACHINE

> a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding.

**Disposition: satisfied in source and local evidence.** `buildMemory` is one pre-execution allocation containing metadata and repacked data. `LogicalSpan.lean:24–37` and its global-store theorem connect all relevant segments through the descriptors to that memory; dead/empty cases are explicit at `LogicalSpan.lean:454–505`. M27/M28/M30 refer to the full run and whole recovered allocation. The reader theorem is discharged canonically before the query theorem, not left as an external physical-store assumption.

### INV-WIDTH-SCALING

> one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient.

**Disposition: satisfied in source and local evidence.** `wordWidth n = 32 + 8*packedReviewerCellWidth n` is fixed by input size (`Allocation.lean:23–39`). M03 proves its logarithmic bounds. M04–M08 and M23–M26 apply that very width to capacity, allocation cells, addresses, whole-program operands, and executed states/results. The serializer uses the same width. The width theorem is therefore attached to the actual construction and execution.

## Mutation P/Q surfaces and execution reconciliation

For O01–O16 and M01–M33, **P** is the corresponding table proposition; **Q** is `True`. All 49 mutated producers exited 0; every designated consumer exited 1 with an in-declaration type mismatch at the listed line. None of those failures was a timeout, output limit, import failure, or resource-exhaustion substitute.

The remaining 14 cases complete the registry:

| Case | Mutation/control and exact distinction | Observed result |
|---|---|---|
| A01 | Unchanged public consumer. | Accept, exit 0. |
| P01 | P: public theorem has `PackedAllocationOptimality`; Q: public theorem has `True`. | Producer 0; `publicContract` rejects at V:18. |
| G01 | P: generic doubled lower bound; Q: `True`. | Generic producer 0; `genericBoundConsumer` rejects at line 7. |
| G02 | Delete the generic all-input `query_exact` field needed to derive answer agreement. | Producer rejects inside mutated `sameRMQBehavior_of_encode_eq`, line 142. |
| D01 | Replace actual decoder with `none`; retain the all-input exactness theorem. | Producer rejects inside mutated `allocationDecoder_exact`, line 93. |
| D02 | Replace actual decoder with `some 0`; retain the same exactness theorem. | Producer rejects at the same exact theorem, line 93. |
| D03 | Replace serialization with `[]`; retain actual word-list length accounting. | First required failure is mutated `serializeWords_length`, line 37. |
| F01 | Delete `memoryRecovery`, not merely its prose. | Producer 0; O04 rejects at V:37. |
| F02 | Delete `positionalReadBacking`. | Producer 0; M27 rejects at V:216. |
| S01 | P: `reconstructedMemory xs = buildMemory xs`; Q: recovered-memory reflexivity. | Producer 0; O04 rejects at V:37. |
| S02 | P: recovered run equals actual allocation run; Q: recovered-run reflexivity. | Producer 0; O15 rejects at V:81. |
| S03 | P: count bounded by arbitrary `B`; Q: count bounded by canonical `2*n+rho n`, despite retaining a budget argument. | Producer 0; O09 rejects at V:58. |
| H01 | P: decoder exact for every input; Q: exactness only after `xs.length = 0`. | Producer 0; O05 rejects at V:42. |
| A02 | Add harmless private proof-only wrapper outside mandatory public structures. | Producer, inventory, consumer all accept. |

I reconstructed the producer mutations in memory to validate diagnostic spans. G02’s required declaration occupied mutated lines 134–146; D01/D02’s occupied 90–96; D03’s occupied 31–38. Their diagnostics were inside those declarations. In D03, a later inverse-proof failure was not used to replace the required first serialized-length failure.

The full raw packet contains **137 files: 134 stage records, one summary, one candidate identity, and one diagnostic fixture**. Every copied file matched its manifest length and SHA256. Every raw stage matched its embedded summary record exactly. Expected and executed IDs matched the committed ordered registry, with 63 unique cases. The 113 retained hashes from earlier authorized raw inspections matched the final copied records.

The 134 stages comprise 69 exit-0 and 65 exit-1 outcomes: 61 semantic expected rejections and four runtime selector rejections account for the nonzero exits. There were no resource failures in this campaign. The separate focused deadline test intentionally has a timeout and is not a semantic rejection case.

## Runtime, registry, process, and frozen-row evidence

The six runtime cases executed in the full campaign and again in the fresh `RuntimeOnly` mode:

| ID | Actual checked behavior |
|---|---|
| R01-EMPTY | Actual empty-input allocation/serialization; invalid decoder windows return `none`. |
| R02-SINGLETON | `[23]` returns index 0 for `[0,1)` and rejects an invalid endpoint. |
| R03-LEFTMOST | `[7,7]` agrees with independent leftmost `scanWindow` expectation 0. |
| R04-ZERO-LENGTH | Empty bitstrings and zero-width collision/control behavior. |
| R05-ZERO-WORDS | Positive-width encodings distinguish empty, one-zero, and two-zero lists and recover explicit mixed words. |
| R06-SAME-SHAPE | `[0,1]` and `[9,10]` are distinct inputs with shared memory/bits and independently specified RMQ result. |

The committed runtime enumeration is nonempty and duplicate-free. Construction of costly fixtures occurs after selection. Startup/list does not count as case execution.

All five distinct focused modes were supplied and inspected:

| Mode | Observed evidence |
|---|---|
| `RegistryOnly` | Exact v3 63-case and six-runtime registry checks; missing-case and selector controls. |
| `SelectorBoundaryOnly` | Six actual subprocess outcomes, including omitted and one known selection, with four pre-execution rejections. |
| `DiagnosticOnly` | The boundary classifier accepts an inside-declaration diagnostic and rejects one at the following declaration. This is a classifier control, not an independent false Lean theorem. |
| `DeadlineOnly` | Existing ownership-plan checks plus actual Windows descendant creation, owned timeout, and no-survivor check. POSIX explicitly uncovered. |
| `RuntimeOnly` | Seven nested startup/selection/runtime records; exact six-case execution. |

The three supplemental parser probes use explicitly supplied external environments and CLI arguments. Their raw records match their summary. They reject duplicate replay selectors, duplicate runtime selectors, and an actual malformed runtime ID. The malformed-ID record contains `malformed selector` and excludes `malformed selector channel`.

For restoration, R:310–314 freshly establishes the two producers, inventory, validation consumer, and generic consumer before backups. Thus artifact restoration means restoration to the freshly established **pre-mutation baseline**, not preservation of an arbitrary older cache from before the runner invocation. R:315–333 saves and compares exact bytes for both mutated source files and both overwritten producer oleans; each case and the outer exit restore them. Clean checks cover worktree, index, and untracked state under the repository’s ignore rules.

The completed summary reports source/artifact restoration and a clean tree. Independently supplied current-source reconciliation covers 677 source/configuration files: 12 raw-byte matches and 665 explicitly CRLF/LF-only matches. It preserves the limitation that historical baseline artifact bytes/digests are not separately available. My own audit checkout also remained clean. These facts support the recorded restoration checks without inventing an independent pre/post artifact hash pair.

The frozen-row checker was checked against the exact contract-checkpoint Git blob:

- All 29 literal IDs and complete physical acceptance rows remained byte-identical.
- Strict UTF-8 decoding was active.
- Whitespace alteration, missing row, duplicate row, Unicode alteration, recognizable mojibake, and invalid UTF-8 were rejected by the same checker.
- The unchanged case accepted.
- No whitespace or Unicode normalization was used to declare a changed requirement unchanged.

The frozen matrix blob was `fe624ea1544556e9a4a579fbbe3c984ed7277ae5`, raw SHA256 `D1289E6A41F68DC69846B87880A33989691E5F27724210FEE8B9E5746A391B77`. The checker’s target SHA256 was `759FD6DB8CD4C45FE69394A2F653328BC4FBB2D5FB141AABC78CD0897BC9CE0F`. Seven checker controls had their prescribed outcomes.

## Trust and evidence tiers

The pinned neutral version record reports Lean 4.22.0, Windows, Lean commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`, consistent with `lean-toolchain`.

The fresh 20-name axiom inventory exactly matches the literal declarations in `scripts/variable_payload_axioms.lean:8–30`:

- Bounded-bitstring cardinality; generic shape injection, count, and doubled lower.
- Serializer left inverse and injection.
- Actual serialized length, recovered memory, decoder exactness, and shape injection.
- Arbitrary and canonical allocation count/lower, actual capacity, and run identity.
- Reconstructed machine and allocation optimality producers.
- Public and composed consumers.

The serializer inverse and injection report `[propext, Quot.sound]`. The other 18 report `[propext, Classical.choice, Quot.sound]`. There are no unexpected assumptions in these outputs. The two trust scans have no hits, both in the supplied exact-source record and in my independent read-only scans. No Mathlib import or unapproved proof/implementation escape was found.

The evidence layers remain distinct:

| Tier | Supported conclusion | Boundary |
|---|---|---|
| Kernel theorem | Finite count, shape injection, lower bound, serialization inverse, exact recovery, decoder and typed composition. | Depends on the stated Lean kernel assumptions and checked imported theory. |
| Explicit model/store/trace theorem | Same allocation, whole run, actual reads, width, safety, capacity, and modeled step bounds. | Scalar primitive model; no direct host-performance consequence. |
| Executable validation | Six declared concrete controls execute the new allocation/decoder layer. | Finite fixtures, not a replacement for universal proofs. |
| Reproducible artifact | Committed exact registry, mutation construction, consumers, declaration checks, restoration, and focused entry points. | Exhaustive only over the declared 63 cases and six runtime cases. |
| Process record | Exact identities, raw outcomes, manifests, source checks, Windows ownership and policy checks. | Delivered execution evidence was audited; I did not independently rerun Lean. Broad and report-tree certification remain pending. |

The axiom inventory does not substitute for public dependency testing; P01, G01, and the 49 field consumers provide that separate evidence.

## Delivered evidence identities

Paths below are relative to `C:/Users/poin/.codex/worktrees/2270/RMQ` unless stated otherwise.

| Evidence | SHA256 |
|---|---|
| `.lake/lb1-final-audit-3/baseline-runtime-manifest.json` | `4FF2AD65D48A36B95C6BF5B419FBE18C555E2E4FB055101F8A56CE62CAA77B10` |
| `.lake/lb1-final-audit-3/full-replay-manifest.json` | `BC23837A1B04C1714FB8CEF1E09BE14F456306419687EBCED8CA49728048AE30` |
| Copied full `summary.json` | `2747EF8ED6285B345B683D53B42A58D527B644D183DA85EBCCBCBA53B4C6062A` |
| `.lake/lb1-focused/20260912T110937881/summary.json` | `AE6C9ABCF27BCBD059AD40D011BEC743932B6B31C781039DD4ADC769F36FBDAF` |
| `.lake/lb1-conflict-controls/20260912T111828536/summary.json` | `61B0AE5B51BEA3FDDF89C998CE4F0E32D88315FA002A5A1518B87D4840E4A5A8` |
| `.lake/lb1-final-trust/20260912T112030055/axiom-inventory.json` | `C8F1257B67B481F8CCADEDD9073C96F550EF21AB683909E1F361477DDDC0DE70` |
| Same trust directory, `summary.json` | `B3231DA95191829471F5D1110F2F4545E3B4D29EB56F05B145A5A2BEABDF5641` |
| `.lake/lb1-finalization/source-5033-policy.json` | `AC5752D0902FCA77F56F5C64DA022E9343453DAAF7A4A0E4AD4FB2F3466606A2` |
| `.lake/lb1-finalization/final-replay-verification.json` | `9E12B8D8C2148F38F253E0BCBC8955C89CE371E1A641FE96D12740C3ADD12494` |

The finalization verifier is corroboration, not the basis for bypassing independent raw reconciliation. Its initial reporting-code error occurred before record checking and was not treated as a semantic campaign failure or a successful verification. The corrected receipt explicitly separates current-source checks from runner-asserted artifact restoration.

The full replay root is `.lake/lb1-replay/20260912T101947006`; its durable copied packet is `.lake/lb1-final-audit-3/delivered-evidence/completed-full-replay`. Focused child roots were:

```text
SelectorBoundaryOnly: .lake/lb1-replay/20260912T111003429
DiagnosticOnly:      .lake/lb1-replay/20260912T111052592
DeadlineOnly:        .lake/lb1-replay/20260912T111103605
RuntimeOnly:         .lake/lb1-replay/20260912T111149080
```

The earlier exact-target focused S03 packet at `.lake/lb1-replay/20260912T101606719` also passed its expected producer/consumer distinction. It was not substituted for the full campaign.

## Commands, policy checks, and remaining limits

I ran read-only identity, ancestry, exact-blob and delta inspection, source searches, line-numbered reads, SHA256/length comparisons, JSON reconciliation, registry-order checks, diagnostic-span reconstruction in memory, the authorized project preflight, clean-tree checks, and:

```powershell
git diff --check 0e6a00f654abc64f8b68988fa9675b9a839dca2f 5033ce54da233fc7a3df319d50ab09a2ebee523a

rg -n '\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib' RMQ lakefile.toml

rg -n 'native_decide|Lean\.ofReduceBool' RMQ
```

Delta whitespace passed; both searches returned no hits. A few exploratory PowerShell syntax/path errors were corrected before the affected read-only checks completed. They were not counted as semantic outcomes.

The supplied source-policy receipt binds exact source `5033ce54…` and a clean tree. Its log hashes match:

```powershell
pwsh -NoProfile -File scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords
pwsh -NoProfile -File scripts/design_decision_check.ps1 -Strict -Base 0e6a00f654abc64f8b68988fa9675b9a839dca2f
```

The strict claim check exited 0 with 2026 classified hits and zero strict failures. The strict design check exited 0, covering 185 changed files with overlapping code/workflow/neutral categories. These pre-report results do not certify future report contents.

Historical keyed build evidence was used only to corroborate predecessor dependencies and cache provenance. The current runner freshly emitted the affected generic and packed producers and validation consumer before inspecting metadata or taking mutation backups. A historical green build was not promoted to a full build of the final target.

I intentionally skipped all Lean/Lake/runtime/replay execution, full build, aggregate gate, and report writing because the frozen contract reserves those actions to the coordinator. No permission gap was counted as a pass. The remaining required outcomes are:

1. Exact-target coordinator full build and aggregate gate.
2. Copying this report verbatim into the intended durable tree.
3. Strict claim checking including process records, applicable strict design checking, and whitespace checking on that report-containing tree.
4. Coordinator acceptance after those outcomes are reconciled.

## Rejected objections and preserved caveats

These objections were examined independently and rejected for the following source reasons:

- **“Length-observable codes have only `2^B` possibilities.”** E enumerates all lengths through `B`; the exact count is `2^(B+1)-1`. The lower bridge deliberately uses `B+1`.
- **“Shape injectivity is merely assumed.”** Exact answers imply RMQ behavior agreement and shape equality; representatives and complete shape enumeration then derive the finite injection.
- **“The infinite value domain prevents the counting argument.”** The injection counts finitely many Cartesian shapes represented by size-`n` lists, not all integer-valued lists.
- **“Same-shape value lists should have distinct encodings.”** That is outside the intended claim. A:106–115 proves sharing, and R06 confirms it.
- **“The serialized allocation is a sibling payload.”** The definition serializes actual `buildMemory`, and recovery/run identities are consumed literally. S01/S02 fail.
- **“The canonical bound can satisfy the arbitrary-budget obligation.”** S03 demonstrates the exact proposition mismatch at O09.
- **“The decoder hides an input/shape oracle in its certificate.”** Its executable definition takes bits, size, and endpoints and runs fixed code. Canonical proof interfaces are discharged from the actual memory; proofs are not runtime arguments.
- **“All exactness is vacuous at size zero.”** The theorem quantifies over all lists, valid singleton and equal-key cases execute, and H01’s empty-only weakening fails.
- **“A changed read log suffices for value dependency.”** The operational reader theorems constrain registers and outputs; concrete controls constrain returned state/location. Log inequality is not the load-bearing argument.
- **“The fixed query budget proves Lean runtime or bit-conversion time.”** It bounds modeled machine transitions. Conversion and measured validation durations remain separate.
- **“Axiom printing certifies field dependence.”** It does not. Literal consumers and proposition mutations establish that separate claim.
- **“A successful Windows timeout certifies POSIX.”** It does not; POSIX remains explicitly unobserved.
- **“63 cases establish all conceivable mutations.”** They establish exactly the committed finite registry.

No broad rewrite is indicated by this audit.

## Roadmap alignment and proof digestion

The change follows the roadmap’s intended connection between the existing shape-count lower-bound framework and the actual succinct allocation. It strengthens the counting/serialization interface and preserves the reference half-open, leftmost, value-level semantics. It does not introduce a new query algorithm, native backend, preprocessing-time theorem, or changed primitive instruction set.

The reviewed additions to `docs/FAMILY_SUMMARY.md` and `docs/DIGESTION_LOG.md` describe the candidate claim with the correct scope. The digestion material includes the conceptual change, plain-English meaning, live assumptions, and skeptical next question. No missing digestion component was found in those allowed public addenda; excluded worker narratives were not used.

**Conceptual change:** The lower bound now speaks about variable-length serialized payloads with observable length, and the concrete encoding is proven to recover the actual PQ1 memory exactly.

**Plain-English meaning:** Any uniform bit budget that can store enough information to answer all size-`n` RMQ instances must satisfy the counting lower bound. The existing PQ1 allocation supplies a matching leading-term upper budget, and the same stored cells support the existing checked machine query.

**Live assumptions:** Public size and common n-only advice; the declared scalar word-RAM primitive model; the existing canonical machine/refinement theory; observable serialized length; Lean’s reported logical assumptions. Conversion cost, preprocessing time, host runtime, and POSIX process behavior are not supplied by this theorem.

**Skeptical next question:** After this exact counting-to-allocation connection, which concrete theorem will account for constructing or materializing the representation under an explicit operational model, while preserving the same payload and primitive-step accounting?

The immediate next concrete target is completion of the outstanding coordinator certification for this candidate and report. Any further machine or preprocessing work should begin from a separately frozen theorem-shaped contract after that acceptance decision.

## Report transport and readiness

Planned ignored staging path:

`C:/Users/poin/.codex/worktrees/2270/RMQ/.lake/lb1-final-audit-3/REPORT.md`

Planned durable path:

`C:/Users/poin/.codex/worktrees/2270/RMQ/docs/internal/extensions/lb1/FINAL_AUDIT.md`

I have written neither file. The coordinator is to preserve this complete response verbatim, record its digest, and run the required checks on the report-containing tree.

**Readiness summary:** All 29 frozen requirements, all 49 literal public field consumers, all 63 mutation cases, all six runtime controls, all five focused modes, the three supplemental selector probes, the 20-name trust inventory, frozen-row controls, and exact-source policy outcomes were independently reviewed. No source/proof/model defect was found. The audit remains **INCOMPLETE** pending coordinator broad build/gate and report-containing-tree certification.
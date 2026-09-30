# LIFE-NATIVE-1 compiled export proof evidence

Status: **compiled proof, default build and exact formal replays passed; not coordinator acceptance**. This note covers
the export/contract/repacking/boundary leaf and its independent consumer. The
34-case reviewed frozen replay and 21-declaration axiom replay pass. The external
delivery receipt records final committed-source certification; coordinator
acceptance is separate. The current
finite foreign/runtime measurements are recorded separately in the native
evidence notes; they are not kernel proofs of the C implementation.

Base: `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`.
Workflow governance: `7b227c49ef2ec044b702126cc41c9add847eed01`.
Branch: `codex/life-native-1-consuming-owner`.
All names below are in `RMQ.SuccinctFinal.PackedNative.Lifecycle` unless qualified.

## Compiled identity and receipts

The current standard four-root Lean pass, including the exact thin adapters,
succeeded with ordinary exit zero:

The one required final default `lake build` also passes at
`.lake/lifecycle-native1/default-build/20260927T074010540/RESULT.json`, SHA256
`3b4a40505c289403d28c71520a57c112a1a573ea7196ed13e31c1af8bf5a1eaf`.
It supplied no target list and ran after implementation, complete formal
discoveries and current native/Rust replays, before the final formal replays.
The actual build returned ordinary zero in 207.869 seconds; the entire wrapper
took 248.640 seconds. Exact raw Lean-version checking, all 6,056 integrity pins,
PATH restoration and mutex cleanup passed under the planned 3,600-second
deadline. Complete variable build output, including inherited linter warnings,
is retained. This is separate from the narrow/standard receipts below.

- Current receipt after all three validation-only transparency repairs:
  `.lake/lifecycle-native1/runs/build-20260927T062313663/RESULT.json`.
  All 5,979 integrity pins and cleanup passed; the actual standard Lean child
  took 0.890313 seconds, with 3.113 seconds for its capture launcher, after the successful narrow consumer build
  `.lake/lifecycle-native1/runs/build-20260927T062148582/RESULT.json`.
  All 48 recorded expected-signature entries (29 distinct check names) remain
  byte-identical, each matching its consumer declaration exactly once.
  The Q10 repair's failed attempt and successful proof-body ordering are
  documented below. Comparing all source/tool/generated pins with receipt
  `043614629` changes only the validation consumer `.lean` and `.olean`:
  381 source pins, 4,856 tool pins and 742 generated pins retain the same
  membership, and every production source/generated C pin remains identical.
- Earlier receipt after two validation-only transparency repairs:
  `.lake/lifecycle-native1/runs/build-20260927T060413789/RESULT.json`.
  All 5,979 integrity pins and cleanup passed; the standard Lean stage took
  3.496 seconds after the successful narrow consumer build
  `.lake/lifecycle-native1/runs/build-20260927T060246879/RESULT.json`.
  Both repairs change only independent-consumer proof bodies, preserving
  all expected theorem statements and the production native import closure.
- Earlier validation-only refresh:
  `.lake/lifecycle-native1/runs/build-20260927T055413715/RESULT.json`.
  All 5,979 integrity pins and cleanup passed; the standard Lean stage took
  2.887 seconds after the narrow consumer repair build
  `.lake/lifecycle-native1/runs/build-20260927T055249622/RESULT.json`
  (5,973 integrity pins, 19.910-second Lean stage, cleanup passed).
  The only changed pins from the earlier standard receipt below are the
  independent consumer `.lean` and its proof-bearing `.olean`; every generated
  C file and every runtime source pin is byte-identical. The production native
  import closure does not import this validation module. This proof-body-only
  repair therefore requires refreshed proof/mutation evidence, while the actual
  native source, generated C, DLL and client evidence retains its applicability.
- `.lake/lifecycle-native1/runs/build-20260927T043614629/RESULT.json`.
- Roots: `RMQ.Core.WordRAM.Native.Lifecycle`, its `Observations` and
  `AdmissionContract` modules, and `RMQ.Validation.LifecycleNativeContract`.
- Captured 381 source/config/helper pins, 4,856 Lean installation/tool/import
  pins, and 742 generated artifact pins. Final integrity checked all 5,979 pins;
  cleanup succeeded and released the campaign mutex.
- The focused Lean stage took 56.835 seconds. The preceding narrow `ThinRun`
  development build passed at
  `.lake/lifecycle-native1/runs/build-20260927T043334915/RESULT.json`, with 4,905
  intact pins, successful cleanup and a 5.352-second Lean stage.
- The resumed leaf needed no further source repair: all existing thin proofs
  and their independent fixed-type `checkT01`–`checkT07` consumers compiled.

Historical pre-thin receipt, retained for scheduling and prior evidence only:

- `.lake/lifecycle-native1/runs/build-20260923T080245826/RESULT.json`.
- Roots: `RMQ.Core.WordRAM.Native.Lifecycle`, its `Observations` and
  `AdmissionContract` modules, and `RMQ.Validation.LifecycleNativeContract`.
- It captured 380 source/config/helper pins, 4,856 Lean installation/tool/import
  pins, and 740 generated artifact pins. Final integrity checked all 5,976 pins;
  cleanup released the campaign mutex.
- Earlier direct changed-consumer check:
  `.lake/lifecycle-native1/consumer-20260923T032634365/RESULT.json`.
  This took about 24.8 seconds, returned empty stdout/stderr, and preserved 751
  source/dependency/runtime pins. It was a development check, not a replacement
  for the standard receipt.

Exact source SHA256 values for the current compiled checkpoint:

| Source | SHA256 |
| --- | --- |
| `RMQ/Core/WordRAM/Native/Lifecycle/ThinRun.lean` | `962dd0d1b1ed610835b04bae4a5309cc194e610f8b8200462b04ec03545e2602` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Run.lean` | `faa4fcabd70cf8462670691e43c1b0df9ff6d7c7ce9fc19f4ac87571910fec36` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Entry.lean` | `176189ba4c8218a6e8f397580230a4fa2fbde0be2c875741c9f7ca8d80bb0901` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Observations.lean` | `1216fe255e14175f2ee67b2c77c28cdb0509606c3be4b0063fd22d39867dbb96` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Repack.lean` | `b229bdb19781ae318694faa62a83b57802634fec27c7edb2d4b5899db56b2639` |
| `RMQ/Core/WordRAM/Native/Lifecycle/Contract.lean` | `a61d3359b1d3066abe8f8cd5d3f3be3597798ea4a2d09e0cb825f9ef5ed7baea` |
| `RMQ/Core/WordRAM/Native/Lifecycle/BoundaryProofs.lean` | `519d089c5b26c2a75153f2c6fee666333f921da3766892411178b313023cc879` |
| `RMQ/Validation/LifecycleNativeContract.lean` | `4075aa30a3587995091debe002aea8ca0b111dddbf210082f0e9a019fd6314c2` |

The receipts are durable local execution evidence under `.lake`. They are not
committed replay cases. The replay cases and runner are
`EXPORT_MUTATIONS.json` and `export_mutation_replay.ps1` in this directory.

## Actual computational objects

`materializeProgram model := (Layout.program model).toArray` is marked
`@[noinline]`. The two zero-argument constants `wordProgram` and
`comparisonProgram` call it at the respective model. `cachedProgram` selects
those constants by the input model. The source definitions are:

```lean
buildFirst model xs left right :=
  runThin (cachedProgram model) (Continuous.lifecycleBudget xs.length)
    (Executable.initialOwner model xs left right)

query model left right owner :=
  runThin (cachedProgram model) Service.budget
    (requestProtocolThin Layout.serviceEntry left right owner)
```

The thin loops erase temporary transition records and delegate every instruction
to the unchanged `executeArray`, and every boundary action to the unchanged
`executeBoundaryArray`. They do not replace primitive semantics. DD-LIFE-NATIVE1-04
records the emitted-source inspection and measured copies that activated the
frozen N1-02 permission. Cache sharing, initializer allocation, and native copy
behavior remain separate runtime observations.

The following equalities have **no input-domain, endpoint, status, success or
final-state hypotheses**:

```lean
cachedProgram_eq (model : InputModel) :
  cachedProgram model = (Layout.program model).toArray

cached_run (model : InputModel) (fuel : Nat) (owner : Owner) :
  runOwner (cachedProgram model) fuel owner =
    runOwner (Layout.program model).toArray fuel owner

buildFirst_eq (model : InputModel) (xs : List Int) (left right : Nat) :
  buildFirst model xs left right = Ownership.owner model xs left right

query_eq (model : InputModel) (left right : Nat) (owner : Owner) :
  query model left right owner = Executable.queryOwner model left right owner
```

Thus the public export object is the exact owner to which inherited
`Ownership.ready`, `Ownership.halted` and `Ownership.refinement` apply.
The first call includes construction, retirement and the first requested query
continuously. Later calls start from the caller-supplied owner and execute the
charged request protocol and service.

## Exact thin-loop refinement and compiled lifetimes

The checked theorem conclusions are unconditional; their quantifiers range over
every supplied program, owner, fuel, boundary list, and initial diagnostic value:

```lean
runThin_eq_runOwner (program : Array Instruction) (fuel : Nat) (owner : Owner) :
  runThin program fuel owner = runOwner program fuel owner

runBoundaryThin_eq_runBoundaryOwner (boundaries : List Boundary) (owner : Owner) :
  runBoundaryThin boundaries owner = runBoundaryOwner boundaries owner

requestProtocolThin_eq_requestProtocolOwner
  (entry : PackedConstruction.Operand) (left right : Nat) (owner : Owner) :
  requestProtocolThin entry left right owner = requestProtocolOwner entry left right owner

Observations.Stats.record_eq_recordBefore (stats : Observations.Stats)
  (transition : ArrayTransition) :
  stats.record transition = stats.recordBefore transition.action transition.before

Observations.runAccThin_eq_runAcc (program : Array Instruction) (fuel : Nat)
  (owner : Owner) (stats : Observations.Stats) :
  Observations.runAccThin program fuel owner stats =
    Observations.runAcc program fuel owner stats

Observations.boundaryAccThin_eq_boundaryAcc (boundaries : List Boundary)
  (owner : Owner) (stats : Observations.Stats) :
  Observations.boundaryAccThin boundaries owner stats =
    Observations.boundaryAcc boundaries owner stats

nativeRunFuel_source (comparison : Bool) (fuel : Nat) (owner : Owner) :
  nativeRunFuel comparison fuel owner =
    runOwner (Layout.program (modelOfComparison comparison)).toArray fuel owner
```

`checkT01`–`checkT07` state these propositions independently and consume their
proofs. The inductions cover zero fuel, stopped/faulted owners, missing fetches,
and primitive failures without an input-domain or successful-run premise.
For the observed runner the complete returned `Owner × Stats` is equal, including
initial nonzero counters and an existing ordered read prefix; this is stronger
than equality of the final owner alone. The observed definitions now execute
`Stats.recordBefore` before each primitive, then recurse. `Stats` contains only
the scalar counts, route counts, and numeric read/reply list. It has no owner or
transition field. Its exact bridges feed `run_owner`, all fold projections,
`buildFirst_stats`, and `queryAcc_exact`, whose existing propositions are retained.

The actual production chain is `nativeInitial → nativeRunFirst → runThin`, with
`nativeInitial_runFirst` identifying it with `nativeBuildFirst` unconditionally
at `xs.length`; successful admission supplies that length at the C boundary.
Later `nativeQuery → query → requestProtocolThin → runThin` retains the four
charged boundary events. The observed exports consume `Observations.run` and
`Observations.query`, which now call the exact thin accumulators.

The current generated C was inspected after the successful standard receipt:

| Generated file under `.lake/build/ir/RMQ/Core/WordRAM/Native/Lifecycle/` | SHA256 | Actual lifetime observation |
| --- | --- | --- |
| `ThinRun.c` | `3b1b000070a739ae3f68c88dbf6240a000edb88265c57f1851159d1d66f561b4` | `runThin` calls unchanged `executeArray(x_14, x_3)` at line 82 without incrementing owner `x_3`; PC/status scalar references have been released first. `runBoundaryThin` similarly consumes owner `x_2` at line 171. |
| `Observations.c` | `c62c6056c651ff833df6acda2c156724579d98c4fbe3c577aa7f39d9f54a63ec` | `recordBefore` at lines 7306–7318 destroys its local transition at line 7316 before returning. The call at line 7584 completes before `executeArray` at 7585; boundary calls complete at 7836/7851 before `executeBoundaryArray` at 7837/7852. Thus the temporary observation references do not cross the primitive call. |
| `Run.c` | `011c0236096139570bd9163cb34947acfe462d6f1c6ce5a264947bdaa9e8e5df` | First execution calls `runThin` at line 127; query calls `requestProtocolThin` and `runThin` at lines 149–150. |
| `Entry.c` | `47fccd0a683eb9aa64d47d39f7b8a7633dae0e5c9b4a5a7cefa2d17a9fca8178` | Actual exported first/fuel entrypoints call `runThin` at lines 248 and 269. |

The observed loop still temporarily increments the owner to call `recordBefore`.
That consuming helper releases both transition fields before returning; no such
owner alias is retained across the instruction. Numeric scalars/read replies and
fixed program objects can remain shared, as permitted by the native contract.
These observations establish the emitted call/lifetime structure, not a universal
allocator theorem. The subsequently rebuilt current client has now passed the
13-fixture paired observed/unobserved campaign: see `NATIVE_EXECUTION_EVIDENCE.md`
and `COMPILED_ROUTE_EVIDENCE.md`. The comparable actual fuel-100 probe now reports
one generated-code array copy of 8,273 cells, compared with 69 copies and 570,837
cells before the refinement. Source inspection attributes the residual copy to
the initially shared fixed register array. This bounded comparison does not
establish universal copy counts or native constant-time execution.

Proof digestion: this refinement removes the short-lived execution records from
the operational loop while preserving exactly the existing mathematical run.
Diagnostics read their producing prestate before execution and return the same
complete fold as before. The live formal assumptions are only the original
primitive definitions and Lean kernel trust; host exclusivity, FFI correctness,
and actual allocation behavior remain separately checked. The actual current
client preserves all 71 independently expected requests in each observation mode,
including exact paired answer/canonical-memory bytes. All 142 publications have
four exact-capacity arrays; publication deliberately copies their complete
initialized contents, including canonical memory, on every successful call.

## Exact all-size export and query contracts

For the next two tables, the following are textual abbreviations, not new
producer assumptions or sibling objects:

- `w := PackedWordRAM.wordWidth xs.length`.
- `B := buildFirst model xs left right`.
- `Q := query model newLeft newRight owner`.
- `mem := PackedWordRAM.buildMemory xs`.
- `packet l r := PackedWordRAM.optionNatPacket
  (SuccinctClassic.queryTraceResult xs l r).value`.
- `cr := Continuous.continuousRun model xs left right`.
- `qr := Reusable.queryRun model newLeft newRight owner.toState`.

The public producer type is:

```lean
export_contract (model : InputModel) (xs : List Int) (left right : Nat)
  (domain : InputDomain model xs)
  (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
  (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
  ExportContract model xs left right
```

The record fields, with their fixed consumer checks, are:

| Field | Exact proposition, using the abbreviations above | Independent consumer |
| --- | --- | --- |
| `program` | `cachedProgram model = (Layout.program model).toArray` | `checkE01_program` |
| `owner` | `B = Ownership.owner model xs left right` | `checkE02_owner` |
| `projection` | `B.toState = cr.final` | `checkE03_projection` |
| `ready` | `Ownership.Ready xs B` | `checkE04_ready`, with expanded expected READY |
| `halted` | `B.status = .halted (packet left right)` | `checkE05_halted` |
| `memory` | `(∀ a, B.memory.getD a none = mem[a]?) ∧ B.memory.size = mem.length` | `checkE06_memory` |
| `emptyKeys` | `B.keys = #[] ∧ B.keyRegs = #[]` | `checkE07_emptyKeys` |
| `bank` | `B.regs.size = 8273` | `checkE08_bank` |
| `capacity` | `Ownership.capacity model B * w ≤ 2 * xs.length + retainedRho xs.length` | `checkE09_capacity`, with expanded capacity |
| `metadata` | `B.memory.getD 0 none = some xs.length ∧ B.memory.getD 7 none = some B.memory.size` | `checkE10_metadata` |
| `observations` | `(Ownership.observations model xs left right).toRun = cr` | `checkE11_observations` |
| `continuation` | For every `es newLeft newRight answer`, `Ownership.Ready xs es → es.status = .halted answer → newLeft < 2 ^ w → newRight < 2 ^ w → QueryContract model xs newLeft newRight es` | Each `checkQ01` through `checkQ11` applies this field at the fixed incoming owner and endpoints |
| `repacking` | For every `source target newLeft newRight` and `Repacked source target`, exact owner/state/status equality, READY equivalence, capacity equality, and query equality as stated below | `checkE12_repacking` |

`Ownership.capacity model es` is expanded in the consumer as
`es.memory.size + (encodedProgram model).length + es.regs.size + 8`.
It is a modeled word capacity, multiplied by `w` in the bit inequality.
This is not a claim about physical allocator capacity, heap header bytes,
reference-count traffic, or fixed startup globals.

The query producer has exactly these premises:

```lean
query_contract (model : InputModel) (xs : List Int)
  (left right answer : Nat) (owner : Owner)
  (ready : Ownership.Ready xs owner)
  (halted : owner.status = .halted answer)
  (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
  (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
  QueryContract model xs left right owner
```

In the next table its `left right` are denoted `newLeft newRight` as above.

| Field | Exact proposition | Independent consumer |
| --- | --- | --- |
| `source` | `Q = Executable.queryOwner model newLeft newRight owner` | `checkQ01_source` |
| `projection` | `Q.toState = qr.final` | `checkQ02_projection` |
| `ready` | `Ownership.Ready xs Q` | `checkQ03_ready` |
| `halted` | `Q.status = .halted (packet newLeft newRight)` | `checkQ04_halted` |
| `memory` | `Q.memory = owner.memory` | `checkQ05_memory` |
| `observations` | `(Executable.queryArray model newLeft newRight owner).toRun = qr` | `checkQ06_observations` |
| `boundary` | `(requestProtocol Layout.serviceEntry newLeft newRight owner.toState).steps = 4` and its categories equal `[.requestAdmission, .requestAdmission, .controlEntry, .controlEntry]` | `checkQ07_boundary` |
| `steps` | `qr.steps = 4 + 4 + QueryEntry.setupCost + (compactQueryRun mem xs.length newLeft newRight).steps` | `checkQ08_steps` pins `QueryEntry.setupCost` as literal `8271` |
| `budget` | `qr.steps ≤ 160257` | `checkQ09_budget` |
| `capacity` | `Ownership.capacity model Q * w ≤ 2 * xs.length + retainedRho xs.length` | `checkQ10_capacity` expands capacity of the actual output |

The proof chain is `buildFirst_eq → Ownership.ready/refinement/halted` for the
first owner and `query_eq → Ownership.Ready.query` plus
`Executable.query_owner_refinement` and `Reusable.query_correct` for later
queries. No output equality is a hypothesis.

`word_export_contract` requires the inherited
`PackedConstruction.InputFits (wordWidth xs.length) xs` domain.
`comparison_export_contract` permits arbitrary `List Int` values.
Both require represented endpoints, without requiring `ValidRange`.
`checkE13_invalid` and `checkQ11_invalid` pin invalid represented requests to
`.halted 0` together with READY. `checkU02_word` and
`checkU03_comparison` pin both public model-specific wrappers.

### Independently expanded READY

The consumer does not merely accept the producer's record type. It defines:

```lean
ExpectedCanonical xs s :=
  (s.core.memory = (fun a => (buildMemory xs)[a]?) ∧
    s.core.extent = (buildMemory xs).length ∧
    s.core.keys = (fun _ => none) ∧ s.core.keyRegs = (fun _ => 0) ∧
    s.keyExtent = 0 ∧ s.keyRegExtent = 0) ∧
  (∀ r, 8273 ≤ r → s.core.regs r = 0) ∧
  s.Fits (wordWidth xs.length)

ExpectedReady xs es :=
  es.regs.size = 8273 ∧ ExpectedCanonical xs es.toState
```

The consumer's proof compilation connects this independent expected expression
to every required READY projection at the actual exported owner.

## Metadata and arbitrary-width packet boundary

`ready_metadata` proves, for every `Ownership.Ready xs owner`:

```lean
owner.memory.getD 0 none = some xs.length ∧
  owner.memory.getD 7 none = some owner.memory.size
```

It uses the actual canonical memory equality, `Builder.metadata_zero`,
`Builder.metadata_seven` and `Ownership.Ready.memory_size`.
`nativeMetadata_ready` and `producedCount_ready` transport this through the
actual metadata export; the latter concludes `producedCount owner = xs.length`.

Under READY, the exact later-admission equivalence is:

```lean
nativeQueryAdmit owner left right = true ↔
  LimbWord.Canonical (wordWidth xs.length) left.data ∧
  LimbWord.Canonical (wordWidth xs.length) right.data
```

The width comes from actual cell zero via `producedCount_ready`, not a
caller-supplied duplicate. This admits represented invalid ranges as well.

`answer_packet_fits` has no domain or endpoint premises:

```lean
∀ (xs : List Int) (left right : Nat),
  optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value <
    2 ^ wordWidth xs.length
```

Its chain is `queryTraceResult_value_reference`; valid-range
`Cartesian.scanWindow_bounds`; the index-plus-one packet bound; and
`size_lt_wordCapacity`. The invalid branch has packet zero.

`nativePacket_exact` takes READY, `owner.status = .halted packet` and
`packet < 2 ^ wordWidth xs.length`. It concludes all three of:

```lean
nativePacket owner = encodeEndpoint (wordWidth xs.length) packet ∧
LimbWord.Canonical (wordWidth xs.length) (nativePacket owner).data ∧
decodeMagnitude (nativePacket owner) = packet
```

The public first/query packet theorems derive the status and fit premises.
Specifically, `buildFirst_packet` has exactly the all-size export premises and
`query_packet` has exactly READY, incoming halted status and represented
endpoints. Their `packet` is the guarded `queryTraceResult` packet for the
actual request. No outgoing answer or encoded-output equality is assumed.

The native admitted producer chain is:

1. `nativeAdmit_source` extracts actual `count = xs.length`, the finite native
   admission conditions, source `InputDomain` and canonical endpoint bytes.
2. `nativeBuildFirst_correct` gives actual `Ownership.owner` equality, READY,
   and the correct halted packet for decoded endpoints.
3. `nativeBuildFirst_packet` gives exact encoding, canonicality, and decoding.
4. `nativeQueryAdmit_iff → nativeQuery_correct → nativeQuery_packet` supplies
   the corresponding later-request chain, preserving the incoming memory array.

The all-size source theorems remain separate from the finite host admission
ceiling. The independent `checkB01`–`checkB10` clauses pin metadata, actual
count, admission, actual output owners, and exact packet byte-array
size/decode propositions.

The native split composition is pinned unconditionally by `checkB11`–`checkB16`:
`nativeInitial` is exactly `Executable.initialOwner`;
`nativeRunFirst comparison xs.length (nativeInitial comparison xs left right)
= nativeBuildFirst comparison xs left right`; the corresponding observed
composition is equal; and observed first/query/arbitrary-initial-owner runs
have the same final production owner. `checkB17` and `checkB18` derive the
same composition using the count from a successful native admission.

## Value-preserving repacking interface

`ArrayCopy source target` requires `target.size = source.size` and equality
of every entry at every index with both bounds supplied. `ArrayCopy.eq` proves
`target = source`. `Repacked source target` consists of four such relations
for `regs`, `memory`, `keys` and `keyRegs`, plus exact `pc` and `status`
equalities. `Repacked.eq` proves the owners are equal.

The exact `repack_transport` conclusion, under only `Repacked source target`,
is:

```lean
target = source ∧ target.toState = source.toState ∧
target.status = source.status ∧
(Ownership.Ready xs target ↔ Ownership.Ready xs source) ∧
Ownership.capacity model target = Ownership.capacity model source ∧
query model left right target = query model left right source
```

The contract's `repacking` projection and `checkE12_repacking` consume this
same transport. This says what successful C copying must establish. It does
not prove C copying, allocation success, exclusivity, reference-count behavior,
native array capacity or pointer identity.

## Observations and exact native projection IDs

The independently written `checkO01`–`checkO11` clauses compile against
`Observations` and the actual native exports:

- `checkO01_firstSteps` and `checkO05_querySteps` pin ABI counter ID 15 to
  `Continuous.continuousRun.steps` and `Reusable.queryRun.steps` respectively.
- `checkO02_firstCategories` and `checkO06_queryCategories` pin all IDs 0–14
  individually: read, register, arithmetic, comparison, branch, control, write,
  allocation, keyRead, oracleComparison, numericRelease, keyRelease,
  keyRegisterRelease, requestAdmission, controlEntry.
- `checkO03_firstOrderedReads` and `checkO07_queryOrderedReads` equate the
  actual `nativeObservationReads` array with the corresponding model run's
  complete ordered read list converted to an array.
- `checkO04_firstRoutes` and `checkO08_queryRoutes` pin each ID 0–12 to
  `transitions.countP (Observations.routeMarked mark)` for the actual
  `Ownership.observations` or `Executable.queryArray` transitions. The marks
  are compactQuery, servicePrepare, serviceSetup, builder, descriptor,
  finalizer, retirement, sameBlockDecision, crossBlockDecision,
  interiorNonemptyDecision, interiorEmptyDecision, interiorReadMarker and
  crossingSecondLoad.
- `checkO09_readPosition` pins `Observations.read_occurrence_output`: a
  transition at index `i` splits the output read sequence into its preceding
  reads, its own reply and following reads, and has
  `t.before = runOwner program i owner` and
  `stepArray program t.before = some t`. Equal reply values retain distinct
  transition positions.
- `checkO10_queryReadPosition` starts with an indexed occurrence in the actual
  `Executable.queryArray`, maps that same index through
  `Executable.query_array_refinement` and `ArrayTransition.toTransition`,
  then applies `Reusable.query_read_occurrence`. It concludes `4 ≤ index`,
  the service occurrence at `index - 4`, its exact producing service prestate,
  its actual `step`, an address within the modeled word, the reply from
  `buildMemory xs` at that address, and a present reply value fitting the word.
- `checkO11_session` pins the accumulated first history followed by the later
  query transitions in order. It does not identify that concatenation with
  query-only evidence.

The observation source proofs derive these outputs by exact folding of the
executed transitions and transport to the abstract run. Final-owner equality
alone is not used to infer any count or ordered-read equality.
First-run observations include construction and the first request. A later
query's observations include its four re-entry events and service suffix.
The route equalities count the specified source predicates; they do not by
themselves prove a stronger universal route-reachability classification.
C field layout, enum range checks and actual native instrumentation are separate
boundary obligations.

## Mutation discovery, diagnostic review and exact replay passed

The complete final-consumer discovery passes at
`.lake/lifecycle-native1/export-mutations/20260927T070116393-4514a722/RESULT.json`.
All 34 cases ran in the unchanged frozen order against standard receipt
`062313663`, consumer `4075aa30...6314c2`, and raw registry
`15034dc9...825660`. The measured campaign took 1,202.241 seconds. All 5,618
source/tool/capture integrity pins remained intact, there were zero live
restoration writes, and disposable shadow removal and mutex release passed.

The 66 altered-producer/affected-descendant stages all returned ordinary zero
with empty stdout/stderr. The 34 consumer stages produced 32 intended
rejections and two ordinary-zero expected accepts. The rejection captures
contain 50 intended diagnostic objects: the continuation weakening emits
multiple diagnostics within the Q10 and Q11 checks. This is distinct from the
48 registered expected-signature entries spanning 29 distinct check names.
All diagnostics passed the actual source-range and permitted-class checks;
no timeout, overflow, crash or unrelated stream was accepted as rejection.
`DIAGNOSTICS.candidate.json` retains the full raw streams, lengths and hashes.
The root independently reviewed the first 25 cases and checked complete
diagnostic-object equality of the last nine against its previously reviewed
focused batch. It froze `EXPORT_DIAGNOSTICS.json`, 55,943 bytes, raw SHA256
`8688e2089ff225de19b741327af451eef2c019f0997e4652dfccecd181b0c542`.
The full diagnostic cases are unchanged from discovery. Final exact frozen
Replay passes at
`.lake/lifecycle-native1/export-mutations/20260927T084110803-e9431c50/RESULT.json`,
SHA256 `341c44469ecb17b4eebb2b45341a71ef8120a3b12fd0d2104496998b30d58866`.
All 34 cases ran in frozen order: 66 producer stages returned ordinary zero
with empty streams, and the 34 consumers returned 32 intended ordinary-one
rejections and two ordinary-zero accepts. All 50 diagnostic objects and complete
raw stdout/stderr match the independently frozen outcomes. No capture timed out,
overflowed or lacked an ordinary exit. The run took 712.944 seconds; all 5,619
pins, zero live restoration writes, shadow removal and mutex cleanup passed.
The earlier battery-sleep interruption and focused recovery are retained below.
This local execution evidence does not assign coordinator acceptance.

The earlier checkpoints and failed attempts below are retained as historical
evidence of the producer/consumer and checker failures that were repaired.

The candidate registry intended for version control currently has 34 expected cases:
23 mandatory-field weakenings, two field deletions, four sibling substitutions,
two expected-accept controls, and three admission/codec leaf weakenings.
Registry raw SHA256:
`15034dc9ce6e6077d27487bc4dddd7990cef6b39c66de39dff2d9be8a6825660`.

The first 2026-09-27 provenance refresh changed only the registry's
`source_identity.consumer_sha256`: the old consumer hash
`debda5401a18bf4e7bae0efe7ba09255fbed880c3adebe7a11476d2a7deefbe6`
became `4e3a18078aa253065fbec51d2149539ae5f97a84bb2b0a05fd4f0a130659b2ab`
after adding the exact thin-loop consumers. The prior raw registry SHA256 was
`a0eddcb1c44a905434f8a03abc9a532dac73e1fc03d993b9734081d0a6e98674`;
the resulting intermediate raw registry hash was
`e3289ef6d411eaa76a60dbbbfd27121fee57ead0c234917940d6311583bbd984`.
The runner's raw hash guard followed that intermediate hash. Ordered case IDs,
all 34 handlers, mutation strings, expected verdicts, and diagnostic targets are
unchanged. Reversing that single SHA replacement reconstructs the previous raw
registry bytes and hash. All 34 sequential literal-edit recipes still match
exactly once against current producer sources in memory, with no live writes.
The other registry source pins continue to match. The earlier captures remain
historical and are not relabeled as current-consumer mutation evidence.

The runner stages complete disposable source/import trees, changes only the
selected producer copy, compiles the altered producer and affected descendants
first, then compiles the unchanged consumer. It compares complete strict-UTF8
streams and final replay also compares raw byte lengths and hashes.
Every captured diagnostic must belong to the intended fixed theorem and
permitted diagnostic class. No normalized diagnostic text is substituted for
the raw stream.

The registry's `intended_checks.declaration_line` values retain the original
signature-freeze coordinates as historical metadata. The expanded Q10 proof
body shifts later declarations, including `checkE13_invalid` from line 145 to
line 149; the current E04 weakening's diagnostic within that theorem is at
152:14. Current diagnostic positions are checked against declaration ranges
reconstructed from the actual consumer by `Get-EMRanges`, together with the
exact unchanged `signature_source` guard. The preserved historical line values
do not override the current source ranges or accepted capture positions.

The current 12 runner controls passed at:
`.lake/lifecycle-native1/export-mutations/20260927T052026899-c516948d/RESULT.json`.
All controls passed against the current registry/runner, seven pinned inputs
remained intact, cleanup passed, and the mutex was released. Elapsed time was
35.870 seconds. The controls launch PowerShell caller/owned-descendant probes,
not Lean or native semantic clients; the unchanged runner still acquires the
shared mutex for this mode, so this run waited for the root to hand it over.

The historical 12 runner controls also passed at:
`.lake/lifecycle-native1/export-mutations/20260923T080458976-0d55bf5d/RESULT.json`.
They cover missing/duplicate/reordered registry entries, eight actual caller
selector cases, and an owned hidden-grandchild timeout/termination control.
Subsequent semantic-path fixes remove a PowerShell extension-removal ambiguity
and compare every compiler/import/runtime pin against the standard receipt.
The current pass supersedes that historical runner receipt for source applicability.

Only **EX-WEAK-E01-PROGRAM** has completed historical pre-thin semantic discovery:

- Receipt:
  `.lake/lifecycle-native1/export-mutations/20260923T080814002-3dc2a0c1/RESULT.json`.
- The altered `Contract` and affected `BoundaryProofs` compiled with ordinary
  exit zero and empty streams.
- The fixed consumer exited one, with exactly one `type mismatch` at
  `checkE01_program`, line 37, column 2: the projected field has type `True`,
  while the expected type is
  `cachedProgram model = (Layout.program model).toArray`.
- Raw stdout: 416 bytes, SHA256
  `16c587ab3ad0a1905362423a4e782cce36998b0a259bfd2c3531e9938e57ea24`.
  Stderr: zero bytes.
- Final integrity checked 5,616 pins, with no live restoration writes;
  the shadow tree was removed and the mutex released.
- The coordinator confirmed this is the intended public dependence.
  The diagnostic is still a discovery candidate, not a complete frozen replay.

At that historical checkpoint, remaining work was full 34-case discovery,
independent root review/freeze of every complete
diagnostic stream, final 34-case replay, and final latest runner controls.
`.lake/lifecycle-native1/export-mutations/RESUME.json` records the local
resume sequence. At that historical checkpoint, none of the pending mutation
rows was closed.

The root returned the shared slot and the following self-test command passed.
The complete-discovery command then started at
`.lake/lifecycle-native1/export-mutations/20260927T052126480-efab707d/`;
it stopped after three accepted discovery cases on a checker classification
failure at `EX-WEAK-E04-READY`. Both altered producer stages exited zero
(5.892 and 2.624 seconds); the fixed consumer exited one (15.455 seconds).
Its complete stdout contains exactly the intended `checkE04_ready` type mismatch
at line 47, column 2 and `checkE13_invalid` application type mismatch at line 148,
column 14. Both say the weakened READY field has type `True` where
`ExpectedReady xs (buildFirst model xs left right)` is required. The runner
recognized only the first diagnostic spelling and rejected the second with
`DIAGNOSTIC unrecognized class`. Final integrity preserved all 5,618 pins,
with no live restoration writes; shadow removal and mutex release passed.
This receipt is a failed full-campaign attempt, not a 34-case pass.

The coordinator authorized the minimal checker-only correction: exact anchored
`^Application type mismatch:` now maps to the existing `type-mismatch` class.
All fixed theorem ranges, expected diagnostic targets/classes, severity/file
checks, complete raw-stream checks, and the immutable 34 recipes/verdicts remain
unchanged. The Lean sources, native sources, consumer, and registry remain frozen.
After the root returned the slot, the 12 runner controls passed again at
`.lake/lifecycle-native1/export-mutations/20260927T053041737-c15be7fd/RESULT.json`
(all seven pins and cleanup passed, 36.318 seconds). Focused E04 then passed at
`.lake/lifecycle-native1/export-mutations/20260927T053143145-aff6eed4/RESULT.json`:
both intended diagnostic objects above were classified as `type-mismatch`, both
producers had ordinary zero exits, the consumer had ordinary exit one, and all
5,618 pins plus shadow/mutex cleanup passed. This material checker correction
and focused validation justify restarting complete discovery; no source proof
or mutation outcome was weakened.

The restarted full attempt
`.lake/lifecycle-native1/export-mutations/20260927T053417643-ae462ff2/RESULT.json`
then passed all 23 mandatory-field weakenings and both deletion controls, but
stopped at `EX-SIBLING-E01-FIXED-WORD`. The altered `Contract` and `BoundaryProofs`
compiled with ordinary zero exits (5.703 and 2.536 seconds). The fixed consumer
exited one after 70.724 seconds with a single `runtime.maxHeartbeats` diagnostic
at `checkE01_program`, line 36, column 0: deterministic reduction at `whnf`
exhausted 200,000 heartbeats. The runner correctly rejected this diagnostic as
an unrecognized class; it is not the required type-mismatch evidence. All
5,618 integrity pins, shadow removal and mutex release passed. This is a
25-case discovery checkpoint inside a failed full run, not a 34-case pass.
The source-level cause under investigation is default definitional-equality
reduction of the large fixed program while comparing the wrong fixed-word
proposition with the model-quantified consumer type. No deadline increase,
timeout acceptance or source repair has been applied at this checkpoint.

The coordinator then authorized one independent-consumer proof-body repair:
`checkE01_program` now uses `by with_reducible exact` for the same public field.
Its expected theorem proposition and object arguments are byte-identical.
Reversing just that proof-body string reconstructs the prior consumer SHA256
`4e3a18078aa253065fbec51d2149539ae5f97a84bb2b0a05fd4f0a130659b2ab`;
the new consumer hash is
`224dc54ffd2f110552105892c2fbe65da2f674d625ab05f80107e9832b0b9473`.
All 48 registered expected-signature entries (29 distinct check names) still
match exactly once in their unchanged expected forms. This controls reduction used
to check a proof; it neither replaces its required proposition nor accepts
resource exhaustion as a proof rejection.

The second provenance-only registry refresh changes that consumer hash and the
runner's exact raw guard, producing the current `6125922b...526774` registry.
Reversing that single hash substitution reconstructs the complete previous
`e3289ef6...bbd984` registry bytes. All 34 recipes, expected diagnostic targets,
verdicts, and ordered IDs remain exactly unchanged. Narrow consumer compilation
and the fresh standard four-root receipt are recorded at the top of this note.
The current runner's 12 controls passed at
`.lake/lifecycle-native1/export-mutations/20260927T055532791-c25170af/RESULT.json`.

The focused formerly failing E01 sibling then passed at
`.lake/lifecycle-native1/export-mutations/20260927T055623261-83fa6623/RESULT.json`:
both producers compiled, and the consumer exited one in 14.601 seconds with
one type mismatch at line 37, column 20. The projected field had type
`wordProgram = wordProgram`, while the expected proposition remained
`cachedProgram model = (Layout.program model).toArray`. All 5,618 pins and
cleanup passed. The other three sibling substitutions and both expected-accept
controls are being tested individually before a new complete campaign.

The next focused case, E02, demonstrated the same actual reduction problem at
its own field. Receipt
`.lake/lifecycle-native1/export-mutations/20260927T055841153-4dd10e69/RESULT.json`
records producer ordinary-zero durations 12.416 and 2.442 seconds, followed by
consumer ordinary exit one in 57.408 seconds with only a
`runtime.maxHeartbeats` diagnostic at `checkE02_owner`, line 39, column 0.
All 5,618 pins and shadow/mutex cleanup passed. The run is failed evidence;
the remaining focused sequence stopped immediately.

Under the coordinator's prior conditional authorization for exactly this
focused obstruction, `checkE02_owner` received the same one-line
`by with_reducible exact` proof-body repair. Its theorem proposition and object
arguments remain unchanged. The consumer hash is now
`fcc7b5f20f68409563bde4ab12e01d6376d34e1917cdf767ff96b8d5280628b3`.
The third provenance-only registry update changed that consumer hash and its
raw guard, producing
`482e90da593c401c04493b31a2aefbc3ca6f3f270ff1796028832dc5ba517d1a`;
reversing that hash substitution reconstructs the preceding `6125922b...526774`
registry exactly. No mutation recipe/verdict/expected signature or runtime
source changed. Narrow compilation, standard refresh, and focused retesting
were required after this second consumer repair. The two compile passes are
now recorded at the top of this note; focused retesting is in progress. No
heartbeat failure is assigned an accepted semantic verdict. Reversing only the
two `by with_reducible exact` proof-body prefixes reconstructs the original
thin consumer hash `4e3a1807...59b2ab`; each of the 48 registered signature
entries remains exact and matches its consumer declaration once.

On the current two-repair consumer and standard receipt `060413789`, focused
E02 now passes at
`.lake/lifecycle-native1/export-mutations/20260927T060647379-660e8eb1/RESULT.json`.
Its consumer returns ordinary exit one in 16.098 seconds with a type mismatch
at line 40, column 20: actual `buildFirst model xs 0 0` reflexivity cannot
establish the expected caller-endpoint owner identity. Focused Q05 passes at
`.lake/lifecycle-native1/export-mutations/20260927T060906123-8c7ff104/RESULT.json`:
output-memory reflexivity is rejected where equality to incoming `es.memory`
is required (line 114, column 2). No Q05 source repair was needed. Both receipts
have 5,618 intact pins and successful shadow/mutex cleanup. At that historical
checkpoint, remaining focused controls and the complete replay were pending.

The Q10 sibling test on that same two-repair consumer failed at
`.lake/lifecycle-native1/export-mutations/20260927T061128670-b20b8210/RESULT.json`.
Both altered producers compiled with ordinary zero exits (14.592 and 2.762
seconds). The consumer instead exited `-1073740791` after 39.553 seconds, with
empty stdout and a `lean::stack_space_exception` in stderr at the expression
equality test. The runner correctly refused this crash as semantic rejection;
all 5,618 pins and shadow/mutex cleanup passed.

The authorized Q10 repair preserves the fully expanded output-capacity theorem
statement and every field-projection argument. It first infers the actual
continuation `.capacity` projection at ordinary transparency, changes only the
goal spelling to `Ownership.capacity model (query model newLeft newRight es)`,
then uses `with_reducible exact projection`. The abbreviation bridge unfolds
the existing `Ownership.capacity` definition; no public or runtime definition
changes. An earlier attempted ordering restricted transparency while elaborating
the continuation arguments and failed the positive narrow build
`.lake/lifecycle-native1/runs/build-20260927T061701859/RESULT.json`: the elaborator
could not convert `ExpectedReady xs es` to `Ownership.Ready xs es`. That failed
build is retained, not treated as successful verification. Moving projection
inference before the restricted comparison passes the narrow build
`.lake/lifecycle-native1/runs/build-20260927T062148582/RESULT.json`.

The resulting consumer SHA256 is
`4075aa30a3587995091debe002aea8ca0b111dddbf210082f0e9a019fd6314c2`.
The fourth provenance-only registry refresh passed through the unsuccessful
proof attempt's consumer `83aa14cb...779ac` / raw registry `58e287c9...68dace`
to raw registry
`15034dc9ce6e6077d27487bc4dddd7990cef6b39c66de39dff2d9be8a6825660`.
Each step changes only `source_identity.consumer_sha256` and the runner's exact
raw guard; reversing the hash replacement reconstructs the prior registry
bytes. All 34 recipes/verdicts remain unchanged, and all 48 fixed expected
signature entries (29 distinct check names) remain exact, each matching once
in the current consumers.

The runner also accepts a nonempty array of distinct known `OnlyCase` IDs,
preserving frozen registry order and requiring the selected count to equal the
requested count. The original null/empty/whitespace/unknown/duplicate guards
remain before any setup or child launch. Omitting the selector still selects
all 34 cases. The durable caller-control roster now has 15 cases: the prior 12,
a two-known reversed-input control that requires registry-order output, and
unknown IDs formed by appending NUL or U+00AD to a known ID. Independent
read-only review reproduced acceptance of those nonliteral IDs by PowerShell's
culture-sensitive `-ccontains`; both membership and selection now use ordinal
hash sets. The two actual caller controls require ordinary exit one and the
exact unknown-selector diagnostic before setup.
This batches the remaining focused semantic cases under one complete setup;
it does not change any producer, consumer, deadline, diagnostic or verdict rule.

All 15 current runner controls pass at
`.lake/lifecycle-native1/export-mutations/20260927T062447298-5d548bf4/RESULT.json`.
All seven pins, zero live restoration writes, shadow cleanup, mutex release and
the owned-descendant termination barrier pass. Reversing only the three
consumer proof-body repairs reconstructs the exact initial thin consumer
`4e3a18078aa253065fbec51d2149539ae5f97a84bb2b0a05fd4f0a130659b2ab`.
This check independently confirms that the expected statements and unrelated
consumer bodies were not edited while repairing reduction behavior.

The focused nine-case discovery then passes at
`.lake/lifecycle-native1/export-mutations/20260927T062619289-c2944c55/RESULT.json`,
using standard receipt `062313663`, the current `4075aa30...6314c2` consumer and
the current raw registry above. The complete batch took 357.436 seconds. All
5,618 pins remained intact, no live restoration writes occurred, and shadow
removal and mutex release passed. Every altered producer and affected
descendant returned ordinary zero with empty stdout/stderr before its consumer
ran. Both expected-accept consumers also returned ordinary zero and empty
streams. All seven expected rejections returned ordinary one with exactly one
intended type-mismatch JSON diagnostic and empty stderr:

| Case | Fixed consumer location | Actual projected proposition rejected |
| --- | --- | --- |
| E01 fixed-word sibling | `checkE01_program`, 37:20 | `wordProgram = wordProgram` cannot establish the model-quantified cached-program equality. |
| E02 other-request sibling | `checkE02_owner`, 40:20 | Reflexivity of `buildFirst model xs 0 0` cannot establish the caller-endpoint owner equality. |
| Q05 output reflexivity | `checkQ05_memory`, 114:2 | Output memory equal to itself cannot establish equality to incoming `es.memory`. |
| Q10 incoming capacity | `checkQ10_capacity`, 146:17 | `Ownership.capacity model es * w ≤ bound` cannot establish the capacity bound for `query model newLeft newRight es`. |
| Count conversion weakened | `count_conversion`, 61:41 | `True` cannot establish `(USize.ofNat count).toNat = count`. |
| Word domain weakened | `word_domain_failure`, 129:2 | `True` cannot establish `buildAdmission InputModel.word xs count left right = false`. |
| Natural decode weakened | `natural_serialization`, 35:2 | `True` cannot establish nonempty encoding, exact encoded length and decode identity. |

In particular, the Q10 consumer now exits one in 17.817 seconds with the intended
incoming-versus-output capacity mismatch. Its expanded theorem statement still
mentions the output memory, encoded program, output registers and eight control
words; the proof abbreviation only avoids deeply reducing unequal objects.
This focused batch is not the complete 34-case final-source campaign. The heavy
slot was returned to the root for its native refresh before that full campaign.

```powershell
& 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe' `
  -NoProfile -File docs/internal/extensions/lifecycle-native1/export_mutation_replay.ps1 `
  -Mode Discovery -SelfTestOnly

& 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe' `
  -NoProfile -File docs/internal/extensions/lifecycle-native1/export_mutation_replay.ps1 `
  -Mode Discovery `
  -OnlyCase EX-WEAK-E04-READY `
  -BuildReceipt .lake/lifecycle-native1/runs/build-20260927T062313663/RESULT.json `
  -DeadlineSeconds 180

& 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe' `
  -NoProfile -File docs/internal/extensions/lifecycle-native1/export_mutation_replay.ps1 `
  -Mode Discovery `
  -BuildReceipt .lake/lifecycle-native1/runs/build-20260927T062313663/RESULT.json `
  -DeadlineSeconds 180
```

Omitting `OnlyCase` selects the independently frozen ordered 34-case registry.
The historical one-case run took 86.819 seconds overall, including staging and
tool/source pin checks; its actual compiler durations were 8.380 seconds for
`Contract`, 1.140 seconds for `BoundaryProofs`, and 7.388 seconds for the fixed
consumer. A 15–25 minute scheduling estimate for 34 cases allows per-case staging
and process overhead plus the three different admission/codec cases; it is an
estimate, not a measured full-campaign duration. Each child retains the finite
180-second deadline. There is no aggregate timeout standing in for child exit,
raw-stream checks, and owned-process cleanup. Neither command was launched
during the concurrent native build; the root explicitly returned the slot first.

## Observed axiom inventory and trust verification

The 2026-09-27 whole-`RMQ` plus `lakefile.toml` hygiene scan found no occurrences of
`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `partial`,
`extern`, `noncomputable`, `import Mathlib`, `native_decide` or
`Lean.ofReduceBool` (the latter two via their separate whole-`RMQ` scan).
`git diff --check` passed. This does not establish the transitive axiom
inventory of imported theorems.

A captured 21-declaration `#print axioms` discovery passes at
`.lake/lifecycle-native1/axioms/20260927T072200262/RESULT.json` after the complete
34-case mutation discovery. The actual compiler returned ordinary zero in
34.811 seconds; the complete run took 67.322 seconds. All 5,604 consumed pins,
zero live restoration writes, shadow removal, environment restoration and mutex
release passed. Stdout contains exactly 21 informational JSON diagnostics,
6,693 raw bytes, SHA256
`83931a56f66839913be61bf11056389b09681e1ed3f23598c8df041451983e8a`;
stderr is empty. The consumed source/import/tool identity is
`ba012458c4f3c7b379572beffbb7d9cda9aea7a8d9d4df2f8c4d9a39b95ddb76`.
`AXIOMS.candidate.json` records each actual set and its full diagnostic.
The root independently read all 21 sets and the complete raw stream, rechecked
the eight capture pins, and froze `AXIOMS.json`, 17,615 bytes, raw SHA256
`a9b0ffcd5c9527d18936d2f76a6afc4964d517c47743e895f86a1c6a59d78895`.
Final exact Replay passes at
`.lake/lifecycle-native1/axioms/20260927T085337097/RESULT.json`, SHA256
`b298894304173a52874593ee066aea530c55574aa2897aa3a14f5cc9918a967f`.
The actual Lean child returned ordinary zero in 18.961109 seconds, with a
20.151-second capture launcher and 38.301-second complete run. All 21 exact
sets and the complete 6,693-byte stdout equal the frozen inventory; stderr is
empty. All 5,605 pins, zero live restoration writes, shadow removal,
environment restoration and mutex cleanup passed under the unchanged
600-second deadline.

| Exact observed axiom set | Declarations, under the namespace at the top of this note |
| --- | --- |
| Empty | `Repacked.eq` |
| `propext` | `Observations.runAcc_exact`, `Observations.read_occurrence_output`, `runThin_eq_runOwner`, `runBoundaryThin_eq_runBoundaryOwner`, `requestProtocolThin_eq_requestProtocolOwner`, `Observations.runAccThin_eq_runAcc`, `Observations.boundaryAccThin_eq_boundaryAcc`, `Observations.Stats.record_eq_recordBefore` |
| `propext`, `Quot.sound` | `cached_run`, `ContractChecks.checkO04_firstRoutes`, `ContractChecks.checkO08_queryRoutes` |
| `propext`, `Classical.choice`, `Quot.sound` | `export_contract`, `query_contract`, `repack_transport`, `answer_packet_fits`, `nativeBuildFirst_packet`, `nativeQuery_packet`, `ContractChecks.checkO02_firstCategories`, `ContractChecks.checkO06_queryCategories`, `ContractChecks.checkO10_queryReadPosition` |

The complete generated audit file imports the fixed consumer and issues:

```lean
import RMQ.Validation.LifecycleNativeContract
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.cached_run
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.export_contract
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.query_contract
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Repacked.eq
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.repack_transport
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.answer_packet_fits
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.nativeBuildFirst_packet
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.nativeQuery_packet
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Observations.runAcc_exact
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Observations.read_occurrence_output
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks.checkO02_firstCategories
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks.checkO06_queryCategories
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks.checkO04_firstRoutes
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks.checkO08_queryRoutes
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.ContractChecks.checkO10_queryReadPosition
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.runThin_eq_runOwner
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.runBoundaryThin_eq_runBoundaryOwner
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.requestProtocolThin_eq_requestProtocolOwner
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Observations.runAccThin_eq_runAcc
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Observations.boundaryAccThin_eq_boundaryAcc
#print axioms RMQ.SuccinctFinal.PackedNative.Lifecycle.Observations.Stats.record_eq_recordBefore
```

The observed inventory is within the permitted Lean trust base. All six new
thin-runner/Stats bridges depend only on `propext`; these actual results were
not assumed from a source scan. This compiler inventory does not verify the C
ABI, runtime ownership implementation or native measurement harness.

### Replayable axiom inventory helper

`axiom_inventory.ps1` now embeds exactly the 21 commands above and generates a
disposable `AxiomInventory.lean`. Its default `-Mode Plan` is noncompiling and
reports `exactSets=NOT_OBSERVED`. The generated consumer bytes have SHA256
`82206b4cb35497ec19f92ae430fd23d812ed8ab43f5381a4b95a80b8149fa54a`.
PowerShell parsing and this noncompiling plan mode passed; Plan passed again on
2026-09-27. Discovery and reviewed frozen Replay have both passed.
Twenty-one is the bounded
audit-root roster, not a claim that there are only twenty-one public declarations
or mandatory propositions. The historical 15-command source hash was
`cd20eacb379400345b3f81ac0b4ed2762f26b40530dafa6d889a0460217cb2bf`.

The helper's expected policy is that every observed set is a subset of the
ordinary Lean trust base `{propext, Quot.sound, Classical.choice}`. The actual
sets for AX01 through AX21 are recorded above. The helper does not fill in
guessed empty or three-element sets. Discovery requires exactly one
informational diagnostic for each named declaration, at its exact generated
command line, rejects any other axiom, and preserves the complete raw streams.
It uses a successful standard receipt to compare the source/import closure and
all Lean installation pins before invoking the owned bounded compiler. Final
integrity and disposable cleanup run independently even after a failure.

The executed discovery command was:

```powershell
pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/axiom_inventory.ps1 `
  -Mode Discovery `
  -BuildReceipt .lake/lifecycle-native1/runs/build-20260927T062313663/RESULT.json `
  -DeadlineSeconds 600
```

The receipt must still match every consumed source, `.olean`, helper/config and
compiler/import/runtime file; a mismatch requires a fresh applicable receipt.
The finite compiler ceiling is 600 seconds, following the compiled warm
consumer check; the helper never falls back to a broader Lake build. A
successful discovery produces `AXIOMS.candidate.json`, with actual per-theorem
sets and complete bytes. Independent root review must precede changing its status
to `FROZEN_ROOT_REVIEWED`. `-Mode Replay` requires both `-FrozenInventory` and
the externally supplied `-FrozenSHA256`, then compares the identical command
roster, consumed identity, exact sets and raw output. This axiom audit never
substitutes for an expected-type mutation.

The compiled mathematics relies on the pinned Lean kernel and inherited
source proofs. Generated-code correctness, the FFI, native pointer validity,
correct copying and allocation, reference ownership, startup retention and
runtime measurements are not kernel conclusions of these theorems. The
approved five `macro_inline` startup-witness annotations are a separate recorded
amendment; this leaf has not strengthened their native acceptance status.

## Evidence boundaries and final certification

These are evidence distinctions under the unchanged requirements in
`CONTRACT_REQUIREMENTS.json`, not new requirements or acceptance decisions.
This note is frozen before final source certification. The external delivery
receipt is the outcome and pin authority for the actual precommit and committed
`final_checks.ps1` invocations; their later results do not require rewriting
this already-certified note. Coordinator acceptance remains separate.

| Frozen row | Available evidence | Separate final obligation or limitation |
| --- | --- | --- |
| N1-01 | All-size word/comparison export contract, actual owner identity, guarded halted answer, canonical memory/key retirement/bank/capacity, and fixed typed consumers compiled. Full exact mutation replay, axiom replay and default build pass. | Final committed-source checks and overall candidate acceptance remain. Native admission is not substituted for the all-size theorem. |
| N1-05 | Exact owner/state projection and element-plus-size repacking transport compiled. All 23 public record fields are consumed at fixed expected propositions. Full discovery and exact frozen replay pass all 34 cases. Actual copying/exact-capacity positive controls are separately reported in `NATIVE_EXECUTION_EVIDENCE.md`. | Final committed-source certification is owned by the root; mathematical repacking equality is not a theorem of C correctness. |
| N1-06 | Continuation uses the supplied READY halted owner, preserves its modeled memory, charges four boundary events, and proves the inherited setup/160257 bound. All 13 native fixtures passed in both modes: 142 actual requests/publications, later memory unchanged, exact capacities, and maximum observed later model steps 28,613. | Final whole-tree checks and candidate acceptance remain. Every publication performs an explicit separately counted replacement/copy; no unchanged-pointer or native constant-time conclusion is inferred. |
| N1-12 | Two fixed model caches, exact source-program equality and unconditional thin-runner bridges compile. `COMPILED_ROUTE_EVIDENCE.md` follows 365 actual initializer modules; current startup passes with 11,135 initialized RMQ global slots and separate overlapping program/global graph accounts. The production closure excludes reference rebuilding and the old interpreter. | Final committed-source certification and acceptance remain. Measured initialized-object bytes are not RSS, allocator usable bytes, or the formal encoded-program payload. |
| N1-18 | Exact owner/Stats bridges, all category/route IDs, ordered reads and indexed producing prestates compile. Exact export and axiom replays pass. All 71 requests per native mode have identical paired answer and canonical-memory bytes; observed diagnostics are separately owned. `ROUTE_COVERAGE_EVIDENCE.md` traces finite actual same/different close-block, interior and crossing-load occurrences. | Final source checks and acceptance remain. Finite route occurrences do not establish every reachable route or a native-space theorem. |
| INV-CERTIFICATE-ANTI-BYPASS | Independent fixed expected types compile for all mandatory fields and thin bridges. Full discovery and exact replay pass all 32 required rejections and both expected accepts, including public-object sibling substitutions. | Final committed-source certification remains; no crash or resource-exhaustion diagnostic is assigned an accepted verdict. |
| INV-MUTATION-REPRODUCIBILITY | Literal edits, fixed consumer signatures, handlers/verdicts and disposable producer-first runner are present. All 15 current harness controls, full 34-case discovery and reviewed frozen replay pass. Failed historical attempts preserve exact streams and successful cleanup. | The coordinator's committed final-tree checks remain. Harness controls are distinct from semantic field mutations. |
| CHK-LEAN | Current standard four-root build and independent consumer compile; whole-`RMQ` hygiene scans are clean. All 21 axiom sets replay exactly within the permitted Lean trust base, and all 34 exact-type mutations replay. The one final untargeted `lake build` passes with 6,056 integrity pins and cleanup. | Final source/receipt binding and coordinator acceptance remain. |

The root task owns final native-control replay. Native
successes above are taken from its separately reviewed exact receipts in
`NATIVE_EXECUTION_EVIDENCE.md`, `COMPILED_ROUTE_EVIDENCE.md`, and
`ROUTE_COVERAGE_EVIDENCE.md`; they are not inferred from compiled proofs.
The full 34-case producer-first discovery and serialized 21-declaration axiom
discovery are complete. The root independently reviewed and froze both
manifests. The first final export Replay failed at E05 after four passing cases:
`.lake/lifecycle-native1/export-mutations/20260927T074439300-7ff52e82/RESULT.json`,
SHA256 `71d77f10e3eb6b8aace2c2f78e81ba41645628353567ed1f667ae06451e0ec06`.
Both E05 producers returned ordinary zero with empty streams. Its consumer had
no ordinary exit and empty streams; the launcher recorded a timeout after
2,678.281 seconds against the unchanged 180-second deadline. The failed run
retained all 5,619 integrity pins, performed zero live restoration writes,
removed its shadow and released its mutex. All three recorded owned PIDs were
absent after cleanup. No timeout was accepted as a semantic rejection.

Windows System events establish the interruption: critical-battery event 524
at 07:48:21 UTC, sleep event 42 with reason Battery at 07:48:24 UTC, and
Power-Troubleshooter event 1 recording sleep from 07:48:21.3876846Z to
08:32:57.3826635Z on 2026-09-27. The failed run's `sleep-interruption` directory
retains `SYSTEM_EVENTS.xml` (12,996 bytes, SHA256
`671251f2530b39c0ebae3d4e0d50865cdc4d24db8d68a880f85218c06f34d696`)
and its message projection `SYSTEM_EVENTS.json` (3,083 bytes, SHA256
`15ffb2077e45317eaf3879ca97d813a9813bd6d13300d6293a5ee67785bdbb66`).
The root granted an unchanged-deadline focused E05 reproduction after this
transient diagnosis, with a full retry conditional on its exact frozen outcome.
That focused Replay passed at
`.lake/lifecycle-native1/export-mutations/20260927T083821597-51bfd2c5/RESULT.json`,
SHA256 `41ede20ddd3b154cfef2b1b041411164c3ebac42fe3bf709e62178d377bd5eab`.
Both producers returned ordinary zero with empty streams. The consumer returned
ordinary one in 7.050421 seconds; its complete 2,215-byte stdout, empty stderr
and four diagnostics equal the frozen E05 outcome. All 5,619 pins, zero live
restoration writes and cleanup passed. The root independently rehashed all
24 raw capture pins and reviewed the focused result before the complete retry.
The subsequent full 34-case Replay and serialized 21-declaration axiom Replay
both pass at the exact receipts above. The heavy slot has returned to the root;
no further builds are needed for this leaf on the unchanged source.

## Proof digestion and next skeptical questions

Conceptually, the adapter erases temporary transition retention while proving
unconditional equality to the old owner execution, then projects all required
facts from that same object. It connects
actual memory metadata and arbitrary-width output bytes back to the source
contract and supplies a precise value-preservation obligation for native
repacking. The independent consumer separately spells out the mandatory
expected propositions, numeric bank size, capacity expression and exported
observation IDs.

In plain language: for admissible source inputs and represented endpoints, the
owner that is actually returned has the promised memory and answer, including
the invalid-range answer. A later request reuses the same memory and has the
inherited model cost bound. Observation output is tied to executed transition
occurrences. These facts now survive compilation of an independent caller. The
separate current DLL campaign also executed all 13 fixtures in observed/unobserved
pairs, with exact answer/memory agreement and exact-capacity publication of all
four arrays. Native publication still copies all retained memory on every call.

Live assumptions are the stated source input domain, represented endpoints,
and, for continuation, an incoming READY halted owner. Admitted native results
add the explicit host admission conditions. No target theorem assumes its own
outgoing memory or answer equality. The repacking interface assumes entry/size
preservation of a proposed copy; verifying a C implementation establishes that
relation remains external.

A skeptical reviewer should next reconstruct how the fixed consumers use each
actual public object, check the reviewed 34-case replay and 21 exact axiom sets,
and ask whether final exact-source and committed-range checks bind the complete
reviewed proof/native evidence.
The current native execution, startup/365-module closure, separate fixed-code
and global accounting, and publication measurements already have their own
receipts. They remain finite native evidence, distinct from the kernel claims
and from coordinator acceptance.

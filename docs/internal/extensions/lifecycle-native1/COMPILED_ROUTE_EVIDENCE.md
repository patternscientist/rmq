# Current compiled lifecycle route and roots

This is a read-only inspection of the thin-runner generated C, refreshed against
the current 2026-09-27 native producer and its unchanged emitted-C closure.
It supplies the generated-call and root-layout evidence for
N1-02, N1-07 and N1-11. It does not substitute for the current DLL/object/tool
binding, native startup, actual copy measurements or semantic replay receipts.
No compiler, native client or build was launched for this inspection.

The source base is `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536` on
`codex/life-native-1-consuming-owner`. The dirty candidate includes the exact
five approved startup annotations and the proved thin runners. Canonical skill
preflight passed at governance `7b227c49ef2ec044b702126cc41c9add847eed01` with
`rmq-proof-sprint` required and all three actual RMQ runtime skills present.

## Identity and method

Unless stated otherwise, generated paths below are relative to
`.lake/build/ir/RMQ/Core/WordRAM/`. Line numbers refer to these exact bytes,
before the native build appends its separately bound read-only global visitors.
The build's derived-C hashes therefore need not equal these original-C hashes.

| Generated file | Bytes | SHA-256 |
| --- | ---: | --- |
| `Native/Lifecycle/Entry.c` | 55148 | `47fccd0a683eb9aa64d47d39f7b8a7633dae0e5c9b4a5a7cefa2d17a9fca8178` |
| `Native/Lifecycle/Run.c` | 8511 | `011c0236096139570bd9163cb34947acfe462d6f1c6ce5a264947bdaa9e8e5df` |
| `Native/Lifecycle/ThinRun.c` | 10464 | `3b1b000070a739ae3f68c88dbf6240a000edb88265c57f1851159d1d66f561b4` |
| `Native/Lifecycle/Observations.c` | 376240 | `c62c6056c651ff833df6acda2c156724579d98c4fbe3c577aa7f39d9f54a63ec` |
| `Native/Lifecycle/Admission.c` | 25307 | `ac5287c553520197b933be0a191fbeef35e428312fa4ed96454d83cce07af31e` |
| `Native/Lifecycle/Codec.c` | 12947 | `822b15e3bcd068b2f21c96ae48f5732aa1c916e7027e95f97a06b55a8ec51fa4` |
| `Lifecycle/Executable.c` | 41449 | `5a8e46003d9853ffb12d707401f89d47a3f9bcf91203853647df468eb51db024` |
| `Lifecycle/ArrayRun.c` | 96694 | `45aa5cfbe2b34c81682f3c472cc5f28bf9d2c50bc99981de2c349bbdcfa6928b` |
| `Lifecycle/Continuous.c` | 5092 | `e5f081863ebfdf235358fc0ce71cb4d2195862a64e7556b29e598ba96a92ad52` |
| `Construction/ArrayRun.c` | 115648 | `1d349e54e79e19869e9c452f4a1d93a1595c767f83c2d7763d7c8a1564282a4e` |
| `Construction/Primitive.c` | 264588 | `2ab11fabf8799d418e09212c461a467c6c5f605f873ea01f24c44414774183a4` |
| `Construction/Input.c` | 5142 | `16b74e455b84d20e9514cec65ec6debeea17a230fd61b9a41733be6b2b82772c` |
| `Native/Limbs.c` | 62390 | `750fba03d69cd8330c7ccbb19edb03aa3df21a2e13ff8be3237fe7ccd8771e74` |
| `Packed/Allocation.c` | 44352 | `783cc8b1269d095f354c15709be6c23dfdaf3b46e29eaa8fefc0008f19eb110e` |

| Native source, relative to repository root | Bytes | SHA-256 |
| --- | ---: | --- |
| `native/packed-rmq/lifecycle_shim.c` | 41735 | `3b3eca3fe1e789034e1b0c1a0cb881e15ce6443363e7e397d1313fef909acde1` |
| `native/packed-rmq/include/packed_rmq_lifecycle.h` | 11394 | `791910de0cde090add04b2d144e5a2e12081cf4caed81e8ab98febc7e76c499f` |
| `native/packed-rmq/src/lifecycle.rs` | 18498 | `19ef29ef8a6a4dc49276f1e0587819cc9317cb1aa778aed194bd13006f0ad2e1` |

The current native producer is
`.lake/lifecycle-native1/runs/build-20260927T063830290/RESULT.json`, SHA-256
`77984ad82686ce42a69e779ee2da5f4c81c1c07fce6947380056e9e2cb8f74eb`.
Its `DERIVATION.json` is SHA-256
`0d0ff9e2b53ad6d448923f5e3bf654145b54c0c118f77e8df11c610bc61e34d2`.
The independent `ROOT_DERIVATION_REVIEW.json` beside it, SHA-256
`1dd3692db1b3cc710eb52c3e1769f1c4844576eb3937a662c17c3e05c3419bb2`,
rehashed all 1,095 current original-C, derived-C and object files for the 365
modules, and compared the original/derived source, visitor, global roster,
signature and object fields with the preceding producer. All match. Four
modules changed only their build-record reuse flag. This preserves the exact
compiled bodies and line references analyzed below; it does not infer DLL
identity from source equality.

The secondary read-only review is
`.lake/lifecycle-native1/native-refresh-review/secondary-20260927/COMPILED_STARTUP_REVIEW.json`,
SHA-256 `b723d01bf6be91b597699a65ed08a94ee3cf1887921168db70edecc9fec8bcc9`.
It independently rehashed all 365 original-C files, checked the complete
inventory hash below, the two fresh producer receipts/artifacts and their 13
ordinary successful compile/link stages, and reversed the exact four changes
in `NATIVE_COMMENT_AMENDMENT.json` in memory. Header lines20/75/76 and Rust
line168 are comments; reversal reproduces the prior source byte lengths and
hashes, preserving all line counts. No native declaration or operational body
changes in that amendment. The fresh production DLL is 12,421,120 bytes,
SHA-256 `03c17dd0fbacff8f72e707f40ba737096daf096059ace99ec7a0c9fd69c1772d`;
its raw bytes differ from the historical DLL. Fresh execution is separately
bound in `NATIVE_EXECUTION_EVIDENCE.md`.

The original inspection indexed 21,638 uniquely named generated function
definitions in the available RMQ generated-C tree. Comments and string literals were excluded;
brace-matched bodies were followed through generated function references,
including named closure targets. Nonfunction globals were kept separate from
call edges. Starting at the actual exports gives the following static
overapproximations; a possible callee is not a claim that every branch executes
in every request. Standard-library/runtime functions are an explicit boundary.

| Root | Reachable generated RMQ function definitions |
| --- | ---: |
| `rmq_lifecycle_initial` | 36 |
| `rmq_lifecycle_run_first` | 13 |
| `rmq_lifecycle_run_fuel` | 11 |
| `rmq_lifecycle_query` | 18 |
| `rmq_lifecycle_packet` | 30 |
| `rmq_lifecycle_admit` | 34 |
| `rmq_lifecycle_query_admit` | 31 |
| `rmq_lifecycle_run_first_observed` | 29 |
| `rmq_lifecycle_query_observed` | 33 |

In particular, declaration names elsewhere in an imported C file, generated
proof-related match splitters, `Owner.toState`, `ExecState.abstract`, the old
transition-collecting `runAcc`, and `Stats.fold` are not thereby reached by these
production roots. The thin evaluator closures contain no allocated function
closures. Word admission has one temporary predicate closure described below.

## Actual returned route

The ordinary first C call builds and admits the decoded list at
`lifecycle_shim.c:620–631`, then calls `rmq_lifecycle_initial` at line 634 and
`rmq_lifecycle_run_first` at line 647. The optional observed branch calls
`rmq_lifecycle_run_first_observed` at line 646. The testing fuel/fault branch
uses the explicitly separate bounded export at line 644. Publication consumes
the resulting owner after `status_result` at lines 648–650.

| Link | Exact generated body |
| --- | --- |
| Input owner | `Entry.c:219–228` decodes endpoints and calls `Executable.initialOwner`; `Lifecycle/Executable.c:757–763` calls `initialOwnerAt` with construction entry 221239. |
| First execution | `Entry.c:240–250` obtains the fixed model program and actual `lifecycleBudget count`, calls `runThin`, and returns that owner. |
| Ordinary continuation | `Entry.c:353–361` decodes the new endpoints and calls `Run.query`; `Run.c:142–152` applies `requestProtocolThin` with service entry 212964, then `runThin` with `Service.budget`, returning its owner. |
| Instruction loop | `ThinRun.c:35–89` checks fuel, status and fetch bounds. Line 82 passes the live owner directly to the unchanged `executeArray`; lines 83–85 loop with its result. There is no increment or transition wrapper retaining the owner across that primitive call. |
| Four boundary events | `ThinRun.c:229–250` constructs left/right/entry/activate boundaries. `runBoundaryThin`, lines 150–183, consumes the boundary list and directly calls the unchanged `executeBoundaryArray` at line 171. |
| Returned packet | `Entry.c:374–402` projects field 5 of the same returned owner. Only the halted branch takes that status's packet and encodes it using width derived from the owner's actual memory metadata. |
| Native result | `lifecycle_shim.c:567–569` invokes that packet export on the repacked, value-preserving owner. `result_from_bytes`, lines 397–403, copies the bytes to independent native storage and decrements the Lean byte array. No reference answer is substituted. |

The combined source export also remains connected: `Run.c:118–129` is
`initialOwner -> runThin`, and `Entry.lean` proves
`nativeInitial_runFirst` for every model bit, list and endpoint byte arrays.
`runThin_eq_runOwner` quantifies over every program, fuel and owner;
`runBoundaryThin_eq_runBoundaryOwner` covers every boundary list and owner.
These are the proof bridge, including stopped/fault/missing-fetch cases, to the
original evaluator. Generated-C inspection establishes the compiled callee
identity; it does not itself prove compiler correctness or runtime complexity.

The primitive closure is particularly small. Its six generated definitions are
`Lifecycle.executeArray` (`Lifecycle/ArrayRun.c:344`),
`PackedConstruction.execPrimArray` (`Construction/ArrayRun.c:468`),
`ExecState.writeNext` (line 320), `ExecState.writeKeyNext` (line 394),
`Arithmetic.eval` (`Construction/Primitive.c:1165`) and `Comparison.eval`
(line 1590). `executeArray` dispatches old instructions to `execPrimArray` at
line 354; its three release branches use actual array pops, with calls at lines
374/414, 460/500 and 546/586. No reference payload builder, functional-state
abstraction wrapper, trace reconstruction or older native interpreter appears
in this closure.

The wider roots for initialization, admission, query and packet conversion
contain numeric `wordWidth`/size arithmetic and byte codecs. They contain no
`LimbMachine` query interpreter, `buildMemory`, `canonicalImage`, `buildPayload`,
reference RMQ answer or reference-trace reconstruction call. Reuse of
`Native/Limbs` must not be described as absent: `Codec.c:66–72` calls
`LimbWord.decode`, and packet/admission paths use its canonical encoding checks
and encoding helpers. `Native/Limbs.c:178–236` shows unsigned base-256 decoding
and fixed-width encoding, not a machine query. The functions named reviewer
overhead in the `initialOwner` closure compute the numeric width formula; they
do not build a reviewer payload or execute a reviewer query.

## Owner, input and result roots

`PackedConstruction.ExecState` is the operational `Owner`. Its compiled
constructor in `Lifecycle/Executable.c:270–276` has exactly six object fields:

| Field | Representation and meaning |
| ---: | --- |
| 0 | `Array Nat` numeric registers |
| 1 | `Array (Option Nat)` actual machine memory |
| 2 | `Array (Option Int)` comparison-key bank |
| 3 | `Array Int` comparison registers |
| 4 | `Nat` program counter |
| 5 | `Status`, including the actual halted Nat packet |

`initialOwnerAt`, lines 233–298, puts input representation and two request
cells into memory. Word input maps each integer to its admitted encoding;
comparison input puts the count in numeric memory and the keys in field 2.
The initial keys and the temporary parsed list are not a completed RMQ payload.
Registers initially contain 8273 zeros; comparison registers initially contain
two zero Int values. The READY schema later requires both key banks empty.

The C list root `t.input` is transferred and cleared at shim line 634, together
with endpoint roots. It is not copied into native metadata. In generated
`Executable.c:238–262`, one temporary list share supplies `inputArray`; the
remaining root is decremented for word input at line 252 or consumed by the
comparison map/array conversion at lines 261–262. The word map consumes/reuses
list cells (`Executable.c:68–124`); the comparison map does likewise
(`Construction/ArrayRun.c:2959–3007`). The generated `lean_array_mk` conversion
has ordinary Lean runtime ownership semantics. The only admission closure
capturing `xs` is the temporary all-element predicate in `Admission.c:194–197`,
passed to `List.decidableBAll`; admission returns a Bool, not that closure.

The native structures are explicit at `lifecycle_shim.c:59–69`:

- Owner: one Lean state root, generation, repacking/copy counters and model byte.
- Result: generation, length and native byte storage; no Lean object pointer.
- Observation: separate `stats` and `reads` Lean roots and generation.

Production publication allocates four replacement arrays, increments each
copied entry, checks exact logical entry equality, preserves pc/status and
releases `t.source` (`lifecycle_shim.c:492–539`). The source and replacement
coexist during this checked copy, so releasing the source does not invalidate
the new entries. Metadata is reread from produced memory; the constructor list,
old arena and request byte arrays are not retained in native owner fields.
The source root drops at line 539; successful publication moves only replacement
state into the handle at lines 580–582. Query clears the caller slot and frees
the old native wrapper while transferring its state at line 669.

The optional pair returned by Lean is unwrapped with increments of its two
components followed by pair decrement at shim lines 585–588. Observations move
to their own native handle at lines 570–577; when no observation is published,
the temporary stats root drops in `cleanup_transfer`. The transfer cleanup at
lines 453–476 releases remaining inputs, source/replacement, stats and injected
alias roots. Owner/result/observation destruction is explicit at lines 412–430.

Rust source independently has no input/trace cache: `Owner` at
`src/lifecycle.rs:287` contains only the optional foreign handle and runtime
borrow; `Natural` at lines 236–247 contains the result handle, its borrowed byte
view and runtime borrow. `QueryResult` at lines 257–259 explicitly owns that
answer and optional separate observation. `Observation` at line 360 contains
only its foreign handle and runtime borrow. The temporary descriptor vector in
`build_first` at lines 200–206 does not escape into the returned owner. This is
a source field inventory, not an inspection of Rust machine-code layout.

## Observed execution without retained transition owners

`Observations.c:7521–7594` is the actual observed instruction loop. Its local
extra owner reference goes into `Stats.recordBefore` at lines 7583–7584. That
function creates a temporary before/action/before record, calls `Stats.record`,
then decrements the record before returning (`Observations.c:7306–7317`). Only
after that return does line 7585 call `executeArray` on the operational owner.
The boundary loop has the same ordering at lines 7835–7837 and 7850–7852.

`Stats.record` constructs four fields at lines 7285–7292: total steps, category
counts, reversed read records and route counts. `ArrayTransition.read?`
(`Lifecycle/ArrayRun.c:1581–1684`) reads the instruction and prestate arrays and
returns only the Nat address and optional Nat reply. It does not return an
owner or memory array. The record's after field is not consulted. Immutable
Nat values and Option wrappers may be shared; that is separate from retaining
an operational owner or backing array.

`Observations.run` dispatches to `runAccThin` at lines 7666–7672. Observed query
consumes the four boundary events, extracts and decrements the intermediate
owner/stats pair, then calls `runAccThin` (`Observations.c:7947–7972`). The final
pair contains the final owner and these scalar/read diagnostics. This route
does not collect the inherited full transition list or call its later fold to
recover an owner. The optional diagnostics still have their own real memory
cost; they are not counted as production owner payload.

## Imported initialization is a separate graph

`Entry.c:1134` initializes Admission, Run and Observations plus their imports.
`Run.c:169` initializes the two program arrays once through
`materializeProgram`, whose body is `Layout.program model -> lean_array_mk`
(`Run.c:36–42`). `cachedProgram` only selects those fixed globals at lines
91–106. This fixed code includes constructor, finalizer, retirement and query
instructions; it is not per-input precomputed output.

Following actual initializer function references reaches 365 generated RMQ
modules and 12,436 generated functions, including fixed program/table builders.
This graph is deliberately separate from the much smaller request roots above.
It has no calls to `runOwner`, `runThin`, `runArray`, `buildMemory`,
`canonicalImage`, `buildPayload` or the `LimbMachine` runner. An initializer or
linker dependency on a theorem module does not make its runtime interpreter a
request callee.

The SHA-256 of the complete 365-file generated-source inventory is
`074f263ab5bb0d6b91a4af9f6e2af3650f69aaffc14ec84a9f1c2e13710b8ed4`.
Its byte format is the concatenation, in ordinal sorted repository-relative
POSIX-path order, of `path`, one NUL byte, the lowercase SHA-256 of that file's
raw bytes, and one LF. The included paths begin `.lake/build/ir/RMQ/`.
The module set comes from definitions reached from
`initialize_RMQ_Core_WordRAM_Native_Lifecycle_Entry`, following both initializer
calls and generated function references, including closure targets. The runtime
and standard library remain outside this RMQ-source inventory and are pinned
separately by the build.

The five specifically amended symbols are absent from their current generated
C, including declarations and initializers:
`canonicalRelativeRmmInteriorCost33WitnessShape`,
`canonicalRelativeRmmInteriorCost33WitnessInput`,
`reviewerSingletonBeforeLCAState`, `reviewerSingletonBeforeRankState`, and
`reviewerIncreasingSixteenBeforeLCAState`. The original-C identities are:

- `.lake/build/ir/RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth.c`:
  56072 bytes, SHA-256 `b31155c75d4e9b50ab6ace07ac23d8a3c115c41311442f6d08d3932c15639aca`.
- `.lake/build/ir/RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall.c`:
  52953 bytes, SHA-256 `5d8ddb23be58ed71f1c527d3fb1ec41c492d6e2a494384fc6526d424c7762aae`.

There remain imported proof-adjacent literals; this evidence does not claim all
such data disappeared. The corruption-table witnesses in
`SuccinctClose/RelativeRmmMacro/ChargedWordChunks.c:1006–1071`,
`ChargedFringeChunks.c:1730–1793` and
`ChargedSameBlockChunks.c:213–276` build tables at literal size parameters 1, 1
and 2. They do not execute a whole RMQ trace. The retained
`reviewerSingletonBeforeLCA`/`BeforeRank` objects are short program lists
(`ReviewerReachabilitySmall.c:548–687`), not the erased evaluated states;
`reviewerIncreasingSixteenBeforeLCA` shares the same list at lines 732–738.
For example, `Packed/LCAProof.c:41–48` constructs an empty/default
`TraceResult.pure`, rather than evaluating a reference query. These fixed
objects belong in the measured initialized-global inventory, not in a claim
that runtime proof-adjacent storage is universally zero.

Name-based scans were checked against bodies. For example, the initializer
objects named `Observations.run___closed__0/1/2` at
`Observations.c:7604–7664` contain only zero category/route counters and an empty
read list. `Lifecycle/Machine.c:577–584` constructs Int zero. The E1-machine
`execInstr___closed__0/1/2/3/4` initializers at `E1Machine.c:2726–2784` construct
small tagged constants. `SuccinctFinalRAM.c:7570–7576` and 7656–7664 allocate
fixed projection/subtraction closures: their bodies at 7540–7547 and 1287–1295
only project an existing field or subtract two Nats. Constructing those
closures does not invoke the adjacent whole-query interpreter, whose body at
7549–7559 is absent from the initializer closure. These distinctions prevent
both a misleading name-only rejection and an import-list-only acceptance.

The native global visitor traverses all initialized RMQ globals, whereas owner
inspection starts from that owner's state. The program-graph and global-graph
measurements overlap and must not be added. Source inspection supports the
absence of the specified whole-trace/payload computations at startup; the
current linked startup receipt must still establish actual initialization and
resource measurements for the rebuilt DLL.

## Bounded residual-copy investigation

The historical thin fuel-100 discovery receipt at
`.lake/lifecycle-native1/replay/20260927T045020119-a225cb45/control-exhausted-build-100.json`
(SHA-256 `95399a2365733a61cb8315acad7fb1ee1ffbe84762c1d471424d54dcdb1203ae`)
records one source copy, 8273 copied cells, capacity total/maximum 8273 and
zero expansions, with no counter overflow. This is an exhausted build
(`actualStatus = 8`), without a returned owner, answer or observation; no
repacking was reached (`copiedEntries = 0`). The receipt is explicitly
discovery-only, not an assigned acceptance verdict.

This fuel-100 run used the earlier DLL; it was not repeated for the current
producer. The unchanged emitted source supports the same bounded explanation,
without turning the old measurement into a fresh result.

The emitted source predicts a first-write copy of the initial register bank:

1. `Lifecycle/Executable.c:186–194` constructs the closed register array as
   `lean_mk_array(8273, 0)`; lines 1256–1257 mark that object persistent.
   `initialOwnerAt` takes this same global at line 237 and installs it directly
   in owner field 0 at line 271. It does not allocate a fresh register array.
2. `initialOwner` starts at PC 221239 (`Executable.c:757–763`).
   `RMQ/Core/WordRAM/Lifecycle/Program.lean:22–32,48–49` puts the compiled
   builder at that base. Its first block is `.action (.load 1 0)`
   (`Construction/Builder/Program.lean:40`); `Block.compileAt` emits that
   action first (`Construction/Structured.lean:88–93`). The initial zero
   address register points to memory cell 0, which holds `some xs.length`
   in both input models (`Executable.c:135–163`). The first successful
   instruction therefore writes register 1.
3. The successful load in `Construction/ArrayRun.c:580–601` drops its
   temporary references to the source arrays at lines 591–595 before calling
   `ExecState.writeNext` at line 599. `writeNext` consumes/releases the old
   owner fields at lines 324–346 and performs `lean_array_fset` at line 360.
   Those releases cannot make a persistent global array exclusive.
4. The pinned runtime header defines persistent objects by `m_rc == 0`
   (`lean.h:474–476`), whereas exclusivity requires `m_rc == 1`
   (lines 470–471,543–549). `lean_array_fset` reaches
   `lean_ensure_exclusive_array`, then `lean_copy_expand_array(a, false)`
   for this array (lines 838–858).

This is a source-supported explanation for the single 8273-cell copy: the
first register write must detach the persistent initializer. The receipt's
aggregate counters do not record a PC or call stack, so attribution of that
particular measured event remains an inference from this route and matching
array size. It is not evidence of an owner retained across every thin-loop
instruction. It also does not establish the copy count for a completed
construction, a different input or a subsequent query; those require their
own measurements. This investigation executed no native program or compiler
and changed no executable source.

The generated `Executable.c` and `Construction/ArrayRun.c` hashes are the
ones already pinned above. Additional source pins for this explanation are:

| Source | SHA-256 |
| --- | --- |
| `RMQ/Core/WordRAM/Lifecycle/Program.lean` | `bb40b5ab3b7532ea4f907bf1d174dd2de14013c5e022454cb7c3b99cc2707dfc` |
| `RMQ/Core/WordRAM/Construction/Builder/Program.lean` | `451ae09fa62d30b89b0cff174e977259fba58fd3d96d535caa4d59129caf436c` |
| `RMQ/Core/WordRAM/Construction/Structured.lean` | `d6321be4381e84895cc6dab6919503951def71c8a153307b1575694ff61c73b3` |
| `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/include/lean/lean.h` | `c9932086ef1625de0fba02453f53b8f6a3571ba88960b975c9e39b724f24cc4d` |

## Boundaries and remaining evidence

The C header requires live valid foreign pointers, unique access to mutable
handles, no forged/aliased owners, and operation/destruction on the initializing
thread. The source does not prove those facts about arbitrary foreign misuse.
Generated C correctness, the C compiler/linker, the pinned Lean runtime and its
reference-count/array primitives remain trusted operational assumptions.
Kernel theorems establish value refinements; they do not establish allocator
usable bytes, RSS, native capacity or arbitrary external-alias absence.

In particular, the native `no_retained_operational_roots` flag is a READY shape
check; `cleanup_complete` is a cleared-transfer-field check; handle counters are
generation-local. Their correct interpretation requires this source/root route
inventory and the actual publication/release controls. They are not a complete
process-wide reference census.

| Row | Evidence supplied here | Other required evidence |
| --- | --- | --- |
| N1-02 | Actual initialOwner/thin/primitive/query/status/packet call chain, including both observed routes; no prohibited interpreter/oracle/rebuild substitution in those closures. | Unconditional Lean refinement checks, current DLL binding, actual result/route challenges and measured copy behavior. |
| N1-07 | Generated six-field owner; native/Rust field inventory; temporary list, byte, wrapper, source and transition-root consumption; observations owned separately. | Live capacity/alias/release controls and current compiled artifact provenance. |
| N1-11 | Current generated symbol/body identities; separate request and initializer graphs; five approved expensive witness/state symbols absent; imported fixed data disclosed. | Exact source/tool/object/library/DLL/cache receipts and rebuilt DLL startup measurement. |

The next skeptical check is whether the DLL actually tested is built from these
same generated bytes and whether its measured controls agree with the resource
claims. This document adds no new design decision and changes no executable
source. It does not declare the whole native candidate or these complete frozen
rows accepted.

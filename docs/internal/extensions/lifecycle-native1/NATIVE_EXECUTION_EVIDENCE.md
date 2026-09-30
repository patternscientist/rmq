# LIFE-NATIVE-1 current native execution evidence

This is a compact account of current native producer receipts and an
independent read-only comparison of their captures and semantic reports. This
leaf ran no compiler or native process and edited only its three assigned
evidence documents. It does not declare the complete campaign accepted.
Governance is
`7b227c49ef2ec044b702126cc41c9add847eed01`; the producing working tree is based
on `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`, with exact implementation and
artifact identities in the receipts below.

## Producing chain and fresh process results

All paths in this table are under `.lake/lifecycle-native1/`.

| Receipt | What it establishes |
| --- | --- |
| `runs/build-20260927T063830290/RESULT.json` | Successful DLL phase: five owned native compile/link stages, all actual exit 0, no reported timeout/overflow; final integrity 7091 pins and cleanup pass. Production and testing DLLs consume the emitted C from Lean receipt `build-20260927T062313663`. |
| `runs/build-20260927T063830290/DERIVATION.json` | Each original emitted C module plus its appended read-only initialized-global visitor; no initializer/code removal. Original and derived bytes are pinned. |
| `runs/build-20260927T064222779/RESULT.json` | Successful client compilation phase: eight owned stages; integrity 7143 pins and cleanup pass. This is compilation evidence for the C/Rust/C++ artifacts, not execution of the separate ten-client registry. |
| `replay/20260927T064556967-9557393a/RESULT.json` | Production startup in a fresh child: actual 5.4340775s, exit 0, exact `LIFE-NATIVE1 STARTUP PASS\n`, empty stderr, no timeout/overflow; integrity 7154 pins and cleanup pass. |
| `replay/20260927T045020119-a225cb45/RESULT.json` | Historical testing-variant fuel-100 discovery (not rerun): actual 2.5108758s, exit 0, exact discovery output, no timeout/overflow. This is an exhausted-run measurement, not a successful READY publication. |
| `replay/20260927T064849543-b1d28b93/RESULT.json` | Complete frozen 13-fixture production registry in both observation modes: 26 fresh child processes, 142 requests; every actual exit 0, exact fixture stdout and empty stderr; integrity 7192 pins and cleanup pass. |
| `native-refresh-review/secondary-20260927/FIXTURE_REVIEW.json` | Independent current reconstruction of 13 cases, 26 processes, 71 requests per mode, all 142 packets/owner measurements, route/read occurrences and exact historical semantic comparison. |
| `clients/20260927T065517097-e55bf689/RESULT.json` | All ten actual C++/Rust production and control cases pass in exact frozen order on the current artifacts; integrity 7292 pins, zero live-restoration writes and cleanup pass. |
| `replay/20260927T065401229-f97e3be7/RESULT.json` | Current production DLL passes the separate 23-case ABI-boundary report; actual child 2.6355578s, exit 0, exact output, empty stderr, no timeout/overflow; integrity 7154 pins and cleanup pass. |
| `native-refresh-review/secondary-20260927/NATIVE_SEMANTIC_REVIEW.json` | Independent current fixture/ABI/client comparison: 413 checked pins, all 26 exact non-pointer fixture projections, all 23 ABI fields/cases and all ten client mappings/raw streams agree with their frozen or historical baselines. |

Fixture process durations range from 6.8472172 to 8.1477043 seconds under the
300-second per-case bound. These include process startup, multiple requests,
inspection and report serialization; they are not per-query latency
measurements. The startup capture's owned launcher bound is 120 seconds.
The fuel-100 discovery uses a 30-second case bound. No timeout is classified
as success. Captures preserve actual exit records and both complete raw
streams; the ordinary zero exits here are distinct from launcher completion.

The inherited toolchain version-display helper joins and trims returned-line
arrays. Its version metadata therefore has a line-ending/BOM fidelity limit;
it is not literal output evidence. Exact compiler/runtime bytes are bound by
the complete installed-file inventories. Actual compilation/native semantic
captures use the separate strict raw stream facility described above. The
final default-build helper separately retains the exact Lean version bytes.

The current `COMPILED_STARTUP_REVIEW.json` in
`native-refresh-review/secondary-20260927/` checks 507 distinct pins: all 365
original emitted-C files, both fresh producer receipts, their 13 actual stages,
artifacts and the startup comparison. The root's separate
`runs/build-20260927T063830290/ROOT_DERIVATION_REVIEW.json` rehashed all 1,095
original/derived/object files. `FIXTURE_REVIEW.json` checks 285 pins including
all current fixture captures/reports, staged artifacts, the registry, historical
reports and read-only verification scripts. Every non-pointer field in all 26
fresh fixture reports equals the prior report at
`replay/20260927T045754455-9f927669`; all current answers are also independently
recomputed from the frozen inputs, with exact integers.

Only program/owner-bank pointer identities are normalized. Both live program
roots must be nonzero/distinct; all four simultaneously live owner banks must
be nonzero, distinct and disjoint from those programs before normalization.
Raw pointers remain in the pinned reports. Freed-generation allocator address
reuse is not a live alias and is not required to match between processes. All
other fields, including ownership flags, array capacities, read multiplicities,
GMP sizes and arbitrarily large integers, are compared exactly. This comparison
does not infer source/replacement coexistence from the post-publication reports.

The larger original integrity counts above are producer receipt claims; this
leaf did not re-run producers or re-hash every installed tool file. The four
native comment changes are separately reversed byte-for-byte in
`COMPILED_ROUTE_EVIDENCE.md`; previous producer recipes remain historical.

The production DLL is 12,421,120 bytes, SHA-256
`03c17dd0fbacff8f72e707f40ba737096daf096059ace99ec7a0c9fd69c1772d`;
the production C fixture executable is 185,344 bytes, SHA-256
`360e9de91ba111f8aab064ee35eea9dfc0fd981b9c99f4dc8fb4c471b311b7a3`.
The current testing DLL is 12,426,240 bytes, SHA-256
`160f2b9e0beb5d25de80d3852608d5f5bb8309a860c3faee6da9c90c92736218`.
The historical fuel-100 measurement used the prior same-size testing DLL,
SHA-256 `fc8a7298b785ccb53f228b9f7c3a29e06724b7f8c8ff27f4d3d63095001276da`.
Both generations use the pinned 18,534,912-byte `libInit_shared.dll`, SHA-256
`5300b06ea3a45146c22996b0591cc6475acb5b6b77802edbecd65baad6485386`.
The recorded platform is Windows x64, Lean 4.22.0
(`ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`); OS DLL/API-set resolution is an
explicit unpinned dependency boundary. Other platforms are not certified.

## Answers, repeated requests and model counts

For every one of 71 requests, observed and unobserved runs return identical
answer bytes and canonical memory bytes. Every later request preserves the
first publication's canonical memory. Expected packets were frozen in
`scripts/lifecycle_native_cases.json` independently of the executed answer;
the separate registry/lead review establishes that oracle. Observation
objects occur only in observed mode.

Each later observed request has two request-admission and two control-entry
events, hence four boundary events; the first construction/query segment has
zero of these boundary events. Later modeled steps have maximum 28,613,
within 160,257 = the 160,253 service/query budget plus four protocol events.
The first segment includes construction/finalization and is not subject to
that later-query bound. Observed route evidence and actual interior payload
occurrences are interpreted in `ROUTE_COVERAGE_EVIDENCE.md`.

The first-publication memory geometry and graph sizes below agree between both modes. For
paired word/comparison fixtures, memory geometry and measured owner graph
sizes agree. Model steps differ by the comparison retirement path.

| Fixture size/type | Memory cells / capacity | Word width bits | First word steps | First comparison steps | Copied entries per publication | Owner runtime object bytes | Owner GMP digit backing bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Empty | 175 | 112 | 13,601 | 13,606 | 8,448 | 70,576 | 16 |
| Singleton | 176 | 144 | 24,395 | 24,400 | 8,449 | 70,600 | 24 |
| Two | 177 | 144 | 28,864 | 28,869 | 8,450 | 70,648 | 40 |
| Four, ties | 178 | 168 | 39,459 | 39,464 | 8,451 | 70,696 | 56 |
| 24 | 186 | 184 | 84,265 | 84,270 | 8,459 | 70,984 | 144 |
| 83 | 211 | 200 | 214,277 | 214,282 | 8,484 | 71,968 | 640 |
| Four, comparison wide/padded | 178 | 168 | — | 39,337 | 8,451 | 70,696 | 56 |

These graph-byte columns describe the first published owner's reachable Lean
objects and separately allocated integer digit backing. They are not payload
bit counts, total process memory, or whole-run high-water measurements.

## Actual client and ABI controls

The ten-client receipt consumes the same client-build receipt and current
DLLs above. All ten actual child exits are 0, with exact registry stdout and
empty stderr, no timeout/overflow, and durations 0.1209255–2.6918382 seconds
under a 120-second bound. This review checked the full ordered ID/handler/mode
mapping, strict UTF-8 output against `native_clients.json`, and actual source/staged-artifact byte identities. The combined secondary
review checks 413 distinct fixture/ABI/client capture, report, staging, registry
and comparison-input pins; it retains all Python integer values exactly. The roster is:

- `LN1-CPP-WORD`, `LN1-CPP-COMPARISON`, `LN1-RUST-WORD`,
  `LN1-RUST-COMPARISON` use production clients and the current production DLL.
- `LN1-RUST-OWNER-ERRORS`, `LN1-RUST-POST-TAKE-FAILURE`,
  `LN1-RUST-CONFLICT-NEW-FIRST`, `LN1-RUST-CONFLICT-OLD-FIRST`,
  `LN1-RUST-CONFLICT-NATIVE-FIRST`, `LN1-RUST-INIT-FAILURE` use the current
  Rust control executable and testing DLL.

Runtime-conflict controls additionally use historical `packed_route.dll`
(SHA-256 `cb53991d47129b608f364a7b0525e983321215e3dace71661c7ece950c8e991b`)
and `packed_rmq.dll`
(`7605525e9e89540d43dfd307e84de24f03062a9632a59062682600d20e0168c4`)
from worktree 1817. Their manifest/source applicability, selected runtime
pins and copied bytes are recorded in the client receipt; each explicitly
sets `freshBuildClaim` to false. `PREDECESSOR_DLL_REUSE.md` explains the
boundary: route has 15/19 matching source pins and no historical generated-C
ledger; binary has 29/31 matching source pins and 19 matching generated-C
pins. Changed old Rust/build files are not reused as current clients.
These are historical conflict fixtures, not replacement production backends
or fresh predecessor certifications. Production lifecycle operations use the
current `packed_rmq_lifecycle.dll`.

The ABI run is one fresh native process containing 23 exact ordered cases,
not 23 fixture processes. Its wrapper's fixture count can print 0 because ABI
cases are in `abi-boundaries.json`, whose `caseCount` is 23. The runner checks
this exact ordered ID/status mapping at
`scripts/lifecycle_native_replay.ps1:193–208`:

| Expected/actual status | Case IDs |
| --- | --- |
| 0 (4 cases) | `ABI-INIT`, `PROFILE-4096`, `PROFILE-ONE`, `THREAD-INITIALIZING-PROFILE` |
| 3 (4 cases) | `PROFILE-4097`, `PROFILE-SIZE-MAX`, `BUILD-COUNT-4097`, `BUILD-MAGNITUDE-4097` |
| 1 (14 cases) | `PROFILE-NULL-BITS`, `PROFILE-NULL-BYTES`, `BUILD-NULL-OWNER`, `BUILD-NULL-ANSWER`, `BUILD-NULL-DIAGNOSTICS`, `BUILD-SIGN-2`, `BUILD-NEGATIVE-ZERO`, `BUILD-EMPTY-MAGNITUDE`, `BUILD-LEFT-SHORT`, `BUILD-LEFT-LONG`, `BUILD-RIGHT-SHORT`, `BUILD-RIGHT-LONG`, `BUILD-MODEL-2`, `BUILD-OBSERVE-2` |
| 4 (1 case) | `THREAD-SECONDARY-PROFILE` |

All build-rejection rows have empty handle outputs; secondary-thread profile
outputs remain unchanged. The count 4096 profile reports 240 width bits and 30
bytes. The total-magnitude overflow arm is recorded as unreachable after the
individual count/magnitude bounds: 4096 × 4096 equals the 16,777,216-byte total
limit. This is a precise absence, not an executed overflow rejection. The
secondary review checked all 23 statuses, rejection-output emptiness, exact
native streams/ordinary exit, and byte equality of the entire current ABI JSON
with the historical report; those pins are in the combined secondary review.

## Publication and capacity measurements

All 142 successful publications report exactly four repacked arrays. In field
order their initialized sizes and capacities are
`[8273, memoryExtent, 0, 0]`. The first is the finite register bank; the last
two are key and key-register arrays. Each register array requests 66,208 bytes;
each empty array still requests its 24-byte header. The memory array requests
`24 + 8 * memoryExtent` bytes. Reported owner/array exclusivity and exact
capacity flags are 1 at every inspection.

This is actual native replacement, not merely a logical shrink:
`native/packed-rmq/lifecycle_shim.c:492–540` allocates a new array at exactly
each initialized source size, copies every initialized element reference,
checks value equality, creates the six-field replacement and releases the
source. `prepare_publication` always calls this routine (553–558); subsequent
requests call publication after their evaluator returns (669–677). The
`copiedEntries` value is consequently 8273 + memoryExtent at every successful
publication, including later queries and admitted invalid queries.

This copies the entire canonical memory array on every publication. It is
linear in the retained array size and is additional native work outside the
modeled160,257 query-step bound. The native API therefore has no constant-time
query claim from that theorem. Element copies retain existing immutable Lean
values; the operation replaces array containers, not every boxed scalar.
Old and replacement arrays coexist temporarily during copying. Neither the
post-publication capacity readings nor these graph sizes measure that peak.

`exclusive_owner` checks the owner and four array containers
(`lifecycle_shim.c:206–209`), not unique ownership of every immutable scalar.
The `noRetainedOperationalRoots` result is `ready_shape` (683–697), requiring
the expected operational schema and empty key stores; it is not a scan of
every reference elsewhere in the process. Foreign-pointer/thread/alias
preconditions and failure/release controls remain separate obligations.

The historical bounded fuel-100 discovery records one generated-array copy of 8,273
cells/capacity, zero expansions and no counter overflow; it reaches no
publication (`copiedEntries = 0`, no returned owner/answer/observation,
status 8). The source-supported explanation is the first write to the
persistent initial register array, documented in
`COMPILED_ROUTE_EVIDENCE.md`. It was not rerun for the current DLL. Its aggregate counters do not locate
the copying instruction; first-write attribution remains a source-supported
inference. This single partial run is not a copy bound for
a completed construction or a later query, and its test receipt is not the
production fixture publication-copy counter.

## Physical program and initialized-global accounting

Startup and all 26 fixture reports agree on the following values after
excluding process-specific pointer addresses:

| Measured graph/object | Value |
| --- | ---: |
| Word program initialized size = capacity | 223,371 |
| Word program array requested bytes | 1,786,992 |
| Comparison program initialized size = capacity | 223,379 |
| Comparison program array requested bytes | 1,787,056 |
| Deduplicated graph from both program roots: objects | 672,214 |
| Program-root graph scalar occurrences | 480,486 |
| Program-root graph runtime object bytes | 16,829,160 |
| Program-root graph boxed integers / digit backing | 0 / 0 |
| Initialized RMQ global slots visited | 11,135 |
| Deduplicated graph from initialized globals: objects | 7,154,107 |
| Initialized-global graph runtime object bytes | 179,203,176 |
| Initialized-global graph GMP digit backing bytes | 16 |

Program arrays are Lean data representing the fixed instruction programs;
their measured graph is not the DLL's native machine-code size or the formal
encoded-program-bit count. The global graph includes imported initialized
data. The two graph traversals use fresh visited sets and overlap; their
byte counts must not be added as disjoint storage. The individual array-byte
figures are also contained in their graph traversal, not an extra addend.

The visitor deduplicates boxed object pointers, counts scalar occurrences,
and calls `lean_object_byte_size` per reached object
(`lifecycle_shim.c:267–321`). Closures contribute captured Lean objects, not
function text. Initialized thunks are inspected without forcing them.
Unsupported external/task objects reject inspection rather than being
silently omitted. The separate integer backing count is GMP allocated limbs
times 8, using the pinned layout and runtime check at 71–83,330–344; it is not
just the used limb count. Program/global graph separation is explicit at
710–727.

These are runtime-reported object sizes and requested array/digit backing,
not allocator usable-size, allocator overhead, RSS or a maximum live-memory
measurement. Native handles, result buffers, observation lists, traversal
work buffers and loaded machine code are not a hidden addition to the owner
payload theorem. Their existence and scope must be reported separately;
this document does not claim a whole-process exact byte total.

## Read-only verification and scope

The secondary review checked all paired answers/memory, all 142 exact array
reports, all per-request boundary counters, the maximum later step count,
all 26 code/global inventories, all 26 exact raw fixture outputs, and the distinct reviewed pin groups
described above. The combined semantic review is
`.lake/lifecycle-native1/native-refresh-review/secondary-20260927/NATIVE_SEMANTIC_REVIEW.json`,
SHA-256 `6eafcedf3878f591daf7a4dad73fa5a798f22b4e386942bc69da9b2c96ac8eba`. The route companion contains an executable
read-only verifier for ordered read backing and route arithmetic. SHA-256,
strict UTF-8 and whitespace checks cover this document's pinned receipts and
sources. No additional aggregate run was needed for this documentation leaf.

These receipts establish finite successful production execution, startup,
ten-client execution, 23 ABI cases and measured publication geometry.
Failure/ownership mutation campaigns, Lean mutation replay, final whole-tree
certification and coordinator acceptance are separate evidence, even if
subsequently completed elsewhere. The fixture receipt sets `campaignComplete` to
false. No public performance theorem or design decision is added here.

Proof digestion: the current production path runs the actual compiled
lifecycle and preserves answers and canonical memory under optional
observations. It publishes exact-capacity native array containers, paying a
whole-memory copy each time. Compiler/FFI/runtime correctness remains assumed;
the skeptical next check is the separate negative-control evidence for the
same publication predicate and resource cleanup.

## Raw SHA-256 receipt/source pins

Paths below are repository-relative. Artifact hashes are given above; receipt
hashes remain distinct from the final report identity to avoid self-reference.

| Path | SHA-256 |
| --- | --- |
| `.lake/lifecycle-native1/runs/build-20260927T063830290/RESULT.json` | `77984ad82686ce42a69e779ee2da5f4c81c1c07fce6947380056e9e2cb8f74eb` |
| `.lake/lifecycle-native1/runs/build-20260927T063830290/DERIVATION.json` | `0d0ff9e2b53ad6d448923f5e3bf654145b54c0c118f77e8df11c610bc61e34d2` |
| `.lake/lifecycle-native1/runs/build-20260927T064222779/RESULT.json` | `6dd359050473a2604ab6370ef65813ba90ef0f3b4acd3ffaa776a08118caf699` |
| `.lake/lifecycle-native1/build/DLL_MANIFEST.json` | `3a02a4d986aa8ff7453ae26e3178bd2608c32e88586062f280d8766eb49c3174` |
| `.lake/lifecycle-native1/replay/20260927T064556967-9557393a/RESULT.json` | `bbbea35884980851f3bbe2b538929c245b7b7f0ef2444a8a05f50aec880c2fe3` |
| `.lake/lifecycle-native1/replay/20260927T064556967-9557393a/startup.json` | `51c279e2ea53f3013ea37b29ae259d9488cb56ef2d50490b03dda7652af9c6ce` |
| `.lake/lifecycle-native1/replay/20260927T045020119-a225cb45/RESULT.json` | `955669f59959cf277b75226c3e844b1fcb9e0ac6073824e9d39cdc4ead9aba2d` |
| `.lake/lifecycle-native1/replay/20260927T045020119-a225cb45/control-exhausted-build-100.json` | `95399a2365733a61cb8315acad7fb1ee1ffbe84762c1d471424d54dcdb1203ae` |
| `.lake/lifecycle-native1/replay/20260927T064849543-b1d28b93/RESULT.json` | `02060b1e4615bcb812bafff8794341271257eb447625dcfdcd62b7a319b36493` |
| `.lake/lifecycle-native1/native-refresh-review/secondary-20260927/FIXTURE_REVIEW.json` | `bbeb482b4a3b12a11f07c294de4158754ef172ad972554826393728272dac1c7` |
| `.lake/lifecycle-native1/clients/20260927T065517097-e55bf689/RESULT.json` | `769cd0530d4f69667cd49288963482fbf8678c74dc4ebd1e206c56896b5c3d34` |
| `.lake/lifecycle-native1/replay/20260927T065401229-f97e3be7/RESULT.json` | `166cc9a094bb54e9d08600182e7bf856cc2116d8262f104701015e747ef16f9b` |
| `.lake/lifecycle-native1/replay/20260927T065401229-f97e3be7/abi-boundaries.json` | `84b8cb2b305780f758ab77228fc78530256bce043b64b7b504a5c3f2b5d8ed7c` |
| `docs/internal/extensions/lifecycle-native1/native_clients.json` | `5a8b5e6a30482209ea7f75d1733dcaac5199b5468bab3d36000f364284afe3b2` |
| `native/packed-rmq/lifecycle_shim.c` | `3b3eca3fe1e789034e1b0c1a0cb881e15ce6443363e7e397d1313fef909acde1` |
| `native/packed-rmq/tests/lifecycle_owner.c` | `0cd522806030bddb51be7f55b4b8c006612c59a3d168815accfa34b9ad635ded` |
| `native/packed-rmq/include/packed_rmq_lifecycle.h` | `791910de0cde090add04b2d144e5a2e12081cf4caed81e8ab98febc7e76c499f` |
| `scripts/lifecycle_native_cases.json` | `9dc72366b51592f18dc50e52d2b799c736dc047e6166538a0a880192062985fd` |
| `.lake/lifecycle-native1/native-refresh-review/secondary-20260927/COMPILED_STARTUP_REVIEW.json` | `b723d01bf6be91b597699a65ed08a94ee3cf1887921168db70edecc9fec8bcc9` |
| `.lake/lifecycle-native1/native-refresh-review/secondary-20260927/NATIVE_SEMANTIC_REVIEW.json` | `6eafcedf3878f591daf7a4dad73fa5a798f22b4e386942bc69da9b2c96ac8eba` |
| `.lake/lifecycle-native1/runs/build-20260927T063830290/ROOT_DERIVATION_REVIEW.json` | `1dd3692db1b3cc710eb52c3e1769f1c4844576eb3937a662c17c3e05c3419bb2` |
| `docs/internal/extensions/lifecycle-native1/NATIVE_COMMENT_AMENDMENT.json` | `b69c06945a7b13843f5e78176f21624d856c318d7c4b9d0f2dabac8816bf4e18` |

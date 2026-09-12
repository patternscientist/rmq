# NATIVE-1 frozen acceptance matrix

Status: FROZEN; every acceptance row remains OPEN until evidence entails its whole requirement.

Frozen before proof edits on 2026-09-12. Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/native-1-packed-execution`. Worktree: `C:/Users/poin/.codex/worktrees/1817/RMQ`.
Template: `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`; its rules apply.
Required join: `RMQ.SuccinctFinal.PackedNative.nativeExecutionCapstone_holds` in `RMQ/Core/WordRAM/Native/Capstone.lean`, consumed by `RMQ/Validation/PackedNative.lean` and the delivered native core.

This freeze grants no acceptance. Mandatory contract/route review precedes dependent implementation; an early route experiment is required to produce that review's evidence. PRE builder work is outside this lane; no PRE implementation is planned here. Compiler/runtime assumptions remain explicit. All inherited invariants apply to the composed execution; none are marked inapplicable.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-NATIVE-FINITE` | Refine program, memory and registers to actual finite indexed containers with a declared finite word/limb representation. Prove operation-by-operation simulation and a full fuel/run theorem preserving result, status, ordered attempted reads/replies, instruction count and all six cost categories. Instantiate for every canonical PQ1 input, all valid queries and the representable-invalid domain. Retain explicit behavior on corrupt/missing data. ArrayRun currently changes instruction fetch only; reproducing that theorem is not this target. | Assigned native extension | For every width, finite code, memory, registers, fuel and related initial state: decode of native run equals the PQ1 run observations under the explicit safety/support guard. All nine constructors and ten arithmetic operations covered. | Finite decode -> execute simulation -> fuel induction -> canonical PQ1 run -> nativeExecutionCapstone_holds. | Planned, not yet attempted: Mutate a loaded value, register update, fault status, ordered receipt, or category; the corresponding exact projection consumer must fail. | None at freeze. | OPEN |
| `REQ-NATIVE-WIDTH` | Handle the real wordWidth n, not a u64/u128 surrogate. Existing fixtures reach 168-176 bits. Prove limb encode/decode, arithmetic, division/remainder, shifts, comparisons, bit operations, address conversion and overflow/fault correspondence, including signed input conversion where used. Prove the abstract refinement for all assigned sizes; the finite native API must impose and check its usize/address/allocation supported domain explicitly, without promising all-n execution on fixed hardware. Count numeric payload bits separately from limb rounding/container overhead. Do not claim physical n-independent primitive hardware time for multiprecision operations. | Assigned native extension | Limb roundtrip, exact safe-operation decoding, checked rejection otherwise; complete operand/address inventory and explicit finite host limits. | Array limbs -> decoded word -> PQ1 Instruction.Safe (wordWidth xs.length) -> canonical safety theorem -> capstone. | Planned, not yet attempted: 128-bit truncation of n9, zero divisors, oversized shifts, underflow, overflow, dormant oversized operands, impossible host lengths. | None at freeze. | OPEN |
| `REQ-NATIVE-SERIAL` | Define a versioned binary format for exact code and memory with explicit bit order, lengths and word width; prove canonical encode/decode roundtrip and injectivity and safe bounded rejection of malformed/truncated inputs. State file header and final-cell padding overhead. Prove that the loaded cells are the cells the allocation theorem counts and the executor reads. An exporter is not itself a compiler correctness theorem. | Assigned native extension | decode (encode image) = some image; encode injective on canonical images; parser bounded by input size and checked limits; exact code/cell identity. | buildMemory/queryProgram -> canonical image -> bytes -> loaded arrays -> same execution -> capstone. | Planned, not yet attempted: Wrong version/tag/width/length, truncation, nonzero padding, oversized counts and substituted cells. | None at freeze. | OPEN |
| `REQ-NATIVE-CODE` | Prove a source-level correspondence tying the delivered native executable core to the verified finite executor. First test the actual Rust verification/translation or narrow generated-code validation route and enumerate its trust base. Do not call a separately handwritten Rust-like Lean interpreter a proof of the shipped Rust. If an external tool is needed, isolate it with exact pins and a reproducible bridge; no Mathlib dependency or Lean upgrade may enter the main library. A different core dependency decision requires coordinator/user disposition before implementation. A proved executable Lean core compiled through C and called by a narrow Rust/C-ABI frontend is an allowed native route: the actual computational core must be the proved implementation, with compiler/runtime/FFI assumptions stated and the wrapper's marshaling checked. Alternatively connect the actual Rust computational core through source semantics/translation. The native artifact may rely explicitly on its documented compiler/runtime translation assumptions, but testing a separate manually reimplemented algorithm cannot close this row. | Assigned native extension | Proposed: source entry evaluates the exact proved finite run projection. Generated C is produced from that declaration; exact source/build pins and FFI marshaling correspondence are checked. Compiler/runtime correctness is an explicit assumption. | proved Lean executable declaration -> generated C exported symbol -> narrow C bridge -> Rust extern call -> delivered library. | Planned, not yet attempted: Mutate the exported Lean core and wrapper argument order; committed correspondence/build consumer must reject. | None at freeze. | OPEN |
| `REQ-NATIVE-API` | Provide a working Rust interface and C ABI with a C++ example, ownership/lifetime/error contracts, deterministic query behavior, safe handling of lengths/invalid endpoints/malformed images, and documented build/reproduction commands. Keep proof-only transition logs optional or erased with a projection theorem; default execution must not allocate the entire proof trace. Preprocessing speed is not promised by this lane. | Assigned native extension | Rust/C/C++ consumers execute same core; bounded error paths and resource release verified; trace-free fold equals result/status/count projections of logged run. | image parser -> native handle -> trace-free core -> Rust/C ABI -> C++ example -> capstone source field. | Planned, not yet attempted: Empty, invalid, malformed, repeated calls, lifetime/error controls; default code must not call trace-producing run. | None at freeze. | OPEN |
| `REQ-NATIVE-JOIN` | The final capstone must compose finite representation, serialization and source-level execution with the accepted PQ1 theorem on exactly the same allocation/program. Publish an accurate assumption table separating Lean kernel proof, generated/translated source semantics, rustc/C linker/runtime and measurements. The native verification plan and comparison evidence must not be presented as a completed Rust refinement. | Assigned native extension | RMQ.SuccinctFinal.PackedNative.nativeExecutionCapstone_holds : NativeExecutionCapstone with mandatory exact-type field consumers on identical allocation/code/width/fuel/query. | PackedWordRAM.fullyChargedPackedQueryCapstone_holds -> finite/serialization/source composition -> Native/Capstone.lean -> Validation/PackedNative.lean. | Planned, not yet attempted: Swap sibling allocation, weaken a validity guard, delete each field, change public proposition; exact-type consumers fail. | None at freeze. | OPEN |
| `CHK-NATIVE-CONTROLS` | Use the existing eight-case exported PQ1 experiment as a starting fixture only. Add cross-cell reads, both selects, fringes, interior/final rank, invalid ranges, corrupt/truncated/oversized metadata, width and address limits, shift/divisor failures and malformed binary length/padding controls. Check every ordered read/reply and category against an independent reference. Include source mutation controls that break the claimed code-correspondence check. | Assigned native extension | Versioned nonempty registry; exact executed/expected cases; independent expected values and ordered observations; source mutations with exact failure surfaces and restoration. | Committed registry -> native validation layer -> same shipped core and typed capstone consumers. | Planned, not yet attempted: Omitted/valid/empty/whitespace/malformed/unknown selectors; no zero-case success; tracked byte restoration. | None at freeze. | OPEN |
| `REPLAY-EXACT-REGISTRY` | any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure. | Assigned native extension | Exact registry equality with nonzero executed count. | script entry -> registry -> execution -> final verdict | Planned, not yet attempted: Delete a case or silently skip it; final verdict fails. | None at freeze. | OPEN |
| `REPLAY-SELECTOR-NONVACUITY` | omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing. | Assigned native extension | Omission runs full frozen registry; valid exact ID runs one; bound empty, whitespace, malformed and unknown fail before execution. | PowerShell parameter-binding boundary -> selection -> execution | Planned, not yet attempted: Exercise each at real process boundary, not only internal helper. | None at freeze. | OPEN |
| `REPLAY-SUBPROCESS-DEADLINE` | run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed. | Assigned native extension | Owned bounded process results preserve exit/stderr; timeout cleans descendants; mutation restoration hashes match. | scripts/owned_process_tree.ps1 -> native replay -> command ledger | Planned, not yet attempted: Owned child sleeper timeout; unsupported host branch recorded uncovered. | None at freeze. | OPEN |

| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-INSTRUCTION-ATOMICITY` | each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-PROGRAM-ACCOUNTING` | input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-ORACLE-INDEPENDENCE` | executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-VALIDATION-REACH` | executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim; | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. Conjoining true theorems about different payloads or guarded and unguarded executions is not closure. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-CERTIFICATE-ANTI-BYPASS` | every mandatory field advertised by a public certificate is projected by a checked typed consumer at the exact proposition and object arguments required by the acceptance contract. Deleting or weakening a field, or replacing it with a sibling fact, must break that consumer rather than leave only constructor initializers and prose unchanged. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-MUTATION-REPRODUCIBILITY` | when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean. Report prose, copied terminal output, and dangling Git objects are not replayable evidence. A public theorem additionally has a checked exact-type consumer that fails when the advertised dependency is removed; `#print axioms` over the theorem's current type is not such a consumer. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | Inherited; applicable to final execution | Exact proposition and independent exact-type consumer required at final join; expand all definitions and guards. | Same buildMemory/queryProgram/wordWidth/initialState/run through finite representation and serialized/native entry. | Planned: projection-specific mutation at identical object arguments and quantifiers; outcome pending. | None at freeze. | OPEN |

## Verification coverage plan

All commands record Windows x64, exact base plus worktree diff/source hashes, deadline, observed duration, exit, stdout/stderr artifact and unexecuted host branches in COMMANDS.md. No final or aggregate pass is inferred from a partial run.

| ID | Role | Exact command/check | Coverage and unique failure mode | Scheduling/deadline policy | State |
| --- | --- | --- | --- | --- | --- |
| CHK-PREFLIGHT | Startup | powershell -ExecutionPolicy Bypass -File scripts/project_skill_preflight.ps1 -GovernanceRef 0e6a00f654abc64f8b68988fa9675b9a839dca2f -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills 'rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint' | Exact baseline and full actual runtime skill catalog. | Read-only before any source edit. | PASS; initial HEAD exact and clean. |
| CHK-DEV | Development-loop | Narrow owned Lean module build/import and exact-type consumers | Operation/run/serialization proofs and non-vacuous observations. | One process/job; 300s first small-module cold margin, revise only from observed evidence. No mutable shared cache. | Planned |
| CHK-ROUTE | Development-loop | scripts/packed_native_route.ps1 | Actual Lean 4.22 -> C -> Rust call, complete different-block execution and source mutation; no separate algorithm substituted. | Bounded startup, known selector, then exact full registry. Own processes using shared tooling. | Planned |
| CHK-AXIOMS | Final-required | Explicit import and #print axioms for every new capstone and exact typed consumer | Kernel trust inventory plus independently pinned expected types. | Narrow owned targets; 300s after dependencies warm. | Pending |
| CHK-HYGIENE | Final-required | rg -n "\\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\\b\|import Mathlib" RMQ lakefile.toml; rg -n "native_decide\|Lean\\.ofReduceBool" RMQ | Whole-tree trust tokens; explain actual matches. | Static, 60s. | Pending |
| CHK-DIFF | Final-required | git diff --check; after commit git diff --check 0e6a00f654abc64f8b68988fa9675b9a839dca2f..HEAD | Both edited and committed whitespace. | Static, 60s. | Pending |
| CHK-DESIGN | Final-required | scripts/design_decision_check.ps1 -Strict -Base 0e6a00f654abc64f8b68988fa9675b9a839dca2f | Task-scoped design/process ledger coverage for each relevant commit. | Static policy check, 120s. | Pending |
| CHK-CLAIMS | Conditional | scripts/claim_drift_scan.ps1 -Strict | Required upon append of narrow FAMILY_SUMMARY/DIGESTION_LOG public prose. | 120s initial; inspect actual production behavior. | Pending public changes |
| CHK-FINAL-BUILD | Final-required | lake build; explicit build/import of every new capstone and typed consumer; full native registry | All assigned modules reachable and library compatibility; no default-target assumption. | Request host-wide final slot before broad run; one job. | Pending coordinator slot |
| CHK-AUDIT | Final-required | Independent exact-commit contract/route review, then fresh blind final audit and coordinator reconstruction | Tests design intent, object identity, all matrix rows. | Evidence-producing phase may return INCOMPLETE; candidate status cannot waive audit. | Pending |

## Scope and stops

Owned paths are Native modules, PackedNative validator, native/packed-rmq, packed_native scripts, this folder, append-only task-specific design/workflow/family/digestion ledger entries, and one uniquely named lake validation target. No edits to shared Packed modules, canonical skills, gate.ps1, aliases or unrelated roadmaps. Local commits authorized; pushes, merges, cleanup and branch deletion excluded.

Explicitly deferred: Final paper rewrite, publication-strategy update and combined campaign integration follow independent acceptance. Nothing needed to make an assigned theorem true may be deferred under this label.

The full native extension is the target. A helper, a test pass or a route proposal is not completion. A required contract/route review can end an evidence phase with Status: INCOMPLETE and an exact phase. A true obstruction must match the frozen objects, guards and quantifiers. Difficulty, elapsed time, or a clean checkpoint is not an obstruction.


## Phase evidence update: ROUTE_READY (no full acceptance row closed)

The initial matrix prefix is byte-preserved; ACCEPTANCE_FREEZE.json records its
length and SHA-256. This appendix changes evidence/status only, not requirements.
The independent contract audit found all 31 rows preserved. Its six concrete
route findings were repaired and reviewed; see CONTRACT_AUDIT.md.

| Acceptance IDs | Actual phase evidence and quantifiers | Actual attacks/verification | Residual gap / status |
| --- | --- | --- | --- |
| REQ-NATIVE-FINITE | runFinite_decode: every Array memory/program, fuel, finite state, with every destination below bank size; entire decoded Run equals raw run on the same toList memory/program and decoded state. runFinite_ofState additionally handles arbitrary original state with a zero tail. Full types and store chain are in FINITE_LEAF.md. | Constructor proof and full fuel induction compiled; missing-memory, invalid, corrupt metadata and complete native fixtures pass. | OPEN: Array Nat is an intermediate cell representation; limb refinement and canonical join are not yet implemented. |
| REQ-NATIVE-WIDTH; INV-WORD-WIDTH; INV-ADDRESS-WIDTH; INV-WIDTH-SCALING | No finite-limb theorem claimed. Tested fixture width is 168/176 bits; natural arithmetic preserves those values. Destination predicate has checked WritesOnly equivalence. | Both wide fixture families execute. Replacing native words by u128 was not claimed or used. | OPEN: all limb operations, overflow/shift/divisor faults, address conversion, finite host guards and payload/rounding accounting. |
| REQ-NATIVE-SERIAL | parseInstruction_encoding proves parseInstruction i.encoding = Except.ok i for every constructor/tag/operand; instruction_encoding_injective derives i=j from equal numeric encodings. | Exact-type consumer and axiom inventory pass; malformed instruction/header controls reject. | OPEN: these numeric instruction lemmas are not the required versioned binary image, memory roundtrip, padding and bounded parser proof. |
| REQ-NATIVE-CODE | routeCore_reference/routeCore_ofState quote full original-run observation equality in ROUTE_EVIDENCE.md, with identical memory/code/fuel/state and destination/zero-tail guards. routeEntry calls this actual core; emitted C prototypes and source hashes are checked. | Lean-to-C DLL and Rust build pass; 14/14 registry including core-fuel mutation rejected at the exact routeCore_source proof line; stale source/artifact inventories reject. | OPEN: canonical loaded-limb/binary source join and universal final marshaling connection. Compiler/runtime/FFI assumptions remain explicit. |
| REQ-NATIVE-API; INV-PROOF-SEPARATION | runThin_projection connects the tail-recursive accumulator to exact finite transitions; runThin_no_reads preserves the original read accumulator in default mode. Rust/C use explicit byte lengths and an owned Lean-string handle. | No-read native case, Rust complete paths, and C++ n9-full match the independent reference. Initialization order has a checked decode theorem and explicit typed consumer. | OPEN: production ownership/error/domain contract, hostile binary safety, all final status exposure and final API. Current API is single-thread experimental text execution. |
| REQ-NATIVE-JOIN; INV-PUBLIC-COMPOSITION; INV-CERTIFICATE-ANTI-BYPASS | Generic raw source equality is checked independently against PackedWordRAM.run; exact typed consumers cannot adapt to a weakened declaration silently. | Source-core mutation breaks the independently pinned proposition; a helper equality alone is not offered as the native capstone. | OPEN: nativeExecutionCapstone_holds and its mandatory record fields/consumers are absent; accepted PQ1 canonical composition and final field/dependency campaign remain required. |
| CHK-NATIVE-CONTROLS; INV-ORACLE-INDEPENDENCE; INV-VALIDATION-REACH | Exact phase registry is 14 cases; expected fixtures are copied from the baseline Lean export with source/file hashes and are never computed from the new result. All ordered receipts and all six category counts compare exactly. | 14/14 native cases and 8/8 selector/manifest controls pass. C++ complete-path output also matches. | OPEN: complete final cross-cell/select/fringe/rank, width/address/arithmetic and malformed binary/padding campaign, with operational route witnesses. |
| INV-STORE-IDENTITY; INV-READ-BACKING; INV-GLOBAL-PHYSICAL-MACHINE | Generic run equality fixes exact toArray/toList memory and code; full decoded transitions retain each load's pre-state, address and reply. | Full different-block comparison checks all 266 ordered receipts; missing-memory reply and status behavior preserved in raw simulation. | OPEN: same-object limb/binary/counted-allocation identity at canonical capstone, every physical segment and machine-width obligation. |
| INV-VALUE-DEPENDENCY; INV-SEMANTIC-NONVACUITY; INV-TRACE-EXECUTION; INV-NO-SYNTHETIC | executeFinite directly uses each loaded reply; runThin calls the actual finite step, and its full final decoded state plus fold equals the original operational run. | Corrupt-size and missing-memory native cases differ as independently expected; wrong core fuel fails the exact proof. | OPEN: consume the corresponding value/provenance/semantic obligations through the final loaded-word public join. |
| INV-STORE-AGREEMENT | Whole raw-run equality is available as a generic adapter; no separate supplied-store agreement theorem is claimed in this phase. | Ordered replies are checked on fixed fixtures. | OPEN: final agreement consumer for loaded/limb stores. |
| INV-INSTRUCTION-ATOMICITY; INV-PROGRAM-ACCOUNTING; INV-CATEGORY-SEPARATION | One finite step calls the same natural primitive operation. Stats counts its actual category. Payload bits, runtime storage, source proof and native diagnostics remain separate. | Six exact category totals match on all supplied cases; source comments and evidence explicitly deny a native hardware-time or memory-succinctness conclusion. | OPEN: limb/native accounting and final machine-model interface; no physical n-independent multiprecision primitive claim. |
| INV-ALL-SIZE | Generic natural-container equality quantifies all fuel/memory/program/states under the destination bound; it has no readiness or valid-query restriction. | Invalid endpoints, missing data, halted/fault behavior and nontrivial full queries are covered at this leaf. | OPEN: canonical all-size and representable-invalid finite-word execution plus finite host support. |
| INV-MUTATION-REPRODUCIBILITY; REPLAY-EXACT-REGISTRY; REPLAY-SELECTOR-NONVACUITY; REPLAY-SUBPROCESS-DEADLINE | Committed exact route/control registries, exact diagnostic surface matching, before/after source hash+diff restoration, exact artifact inventories and owned child deadlines. | Full route 14/14, controls 8/8; omission selects all; valid selects one; bound empty/whitespace/malformed/unknown reject. Timed-out sandbox children were cleaned, with exits/stderr/ownership retained. | Phase checks PASS; full row OPEN until final native campaign exists. Non-Windows host branch uncovered; no timeout counted as pass. |

Report/aggregate obligations: REPORT.md must begin INCOMPLETE with ROUTE_READY
and enumerate every still-open row, exact source commit, proof digestion and
command outcomes. The final task response supplies the report's actual bytes
and SHA-256. No host aggregate slot is requested for this evidence phase. Full
lake build, explicit final capstone/validator, final registry, fresh blind
exact-commit audit and coordinator-scheduled aggregate certification remain
pending for the full candidate. No PRE builder is implemented by this lane.

Submission evidence correction (requirements unchanged): strict design checking
at implementation 3329a6e fails closed on 28 unclassified native paths; the
coordinator must arrange the shared classification change. Current eight-case
selector controls call the real script in-process and do not cover OS argument
serialization. The frozen process-boundary requirement remains open. The
implementation committed-range whitespace and frozen-prefix/source/artifact
integrity checks pass. REPORT.md records the exact results and source identity.

## NATIVE-1 final owned-candidate evidence — 2026-09-12

This appendix adds evidence to the original requirements; it does not replace,
narrow, reorder or change their dispositions. It records an internal source
reconstruction and owned candidate evidence, not coordinator `ACCEPTED`, a fresh
blind audit or global target closure. The binary, contract and validator campaigns below are complete at their pinned
receipt bytes. Their outcomes were inspected directly and independently checked
by the worker lead's final integrity receipt; they are not coordinator acceptance.
No Lean or native process was run to prepare this appendix.

### Frozen source and evidence references

- The exact implementation/evidence commit is identified in the subsequent
  report and audit packet after the evidence is committed. This appendix cannot
  contain its own future commit hash as a self-referential identity claim.
- Governance/base: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- The original 31 requirements remain authoritative. Their frozen matrix prefix
  has 28,298 bytes and SHA256
  `0A5D2313CCEC30DE81AAB3B19439247C612CE4B8FC6C19C0BF51F6C3809D103E`.
- `Native/Capstone.lean` SHA256:
  `E2B2FB55223A271B3383AACB70361D85126ABEB3C252ACB0E314467729C6FA0D`.
- `Native/Contract.lean` SHA256:
  `A8DB1EAAC6445F2F8490A6C344A3F573FD169D3FD7B82E6637C4947159E306AE`.
- **All 42 complete literal field types and their exact independent consumer
  assignments are incorporated by explicit reference** to
  `docs/internal/extensions/native1/SOURCE_CONTRACT.md`, sections “Literal
  public propositions” and “Exact consumer assignment”, unchanged SHA256
  `8D9833471C76FD84E7C93E1387A755B063EB3307CD6ABE4B604564FAB6ABE94D`.
  The source inventory's historical pending-campaign prose is not used to
  determine the later campaign outcomes in this appendix.
- Supplemental operation/fault, parser, host and occurrence propositions and
  the detailed per-subclaim reconstruction are incorporated from
  `docs/internal/extensions/native1/FINAL_SOURCE_MATRIX.md`, SHA256
  `AC9259FB49DC6E0CBCDD83760AFE61FD2E76AC27979B8E2ACCDC17782C9395B5`.
  Its earlier pending campaign statements likewise remain historical.

Here `N01` through `N42` denote the independently typed
`RMQ.SuccinctFinal.PackedNative.ContractChecks.checkN01` through `checkN42`,
respectively. The public consumer is literally
`theorem publicContract : NativeExecutionCapstone := nativeExecutionCapstone_holds`.
Neither the field consumers nor the public consumer infer their expected types
from the producer.

Evidence keys used below:

| Key | Evidence and current state |
| --- | --- |
| S | Checked source at the hashes above: `commands/capstone-03.json` (exit0, 4.970s), `contract-02.json` (exit0, 7.309s), and the supplemental source/leaf receipts listed below. This is source evidence, not foreign compilation correctness. |
| L | Existing focused checks: limbs29 cases (`limbs-checks-02.json`); whole machine, observations and faults (`machine-checks-01.json`); code parser converse (`machine-codefacts-checks-01.json`); image37 checks (`binary-checks-06.json`); exact capped-cursor checks (`cursor-checks-02.json`). The source matrix identifies their checked propositions and exact outcomes. |
| W | `witness-proofs-02.json`, `witness-export-check-03.json`, `witness-export-01.json` (exit0, 403.369s), and `witness-export-artifacts.json`: seven actual independent exports. The canonical program's uncompressed SHA256 is `2D978D9D81CC3326F623F3A21AFCDA9FE3329E6F1DB60B2000425C4EF0A0D875`, equal to the committed gzip's decompressed bytes. |
| C | **PASS:** all nine contract controls, including one omitted full44 replay (baseline, every field weakening, public-type-collapse). C1/C2/C3 pin the full/control/owned-wrapper receipts. All44 producers compiled freshly; the positive consumer passed; all43 negatives rejected at their designated exact type-mismatch lines. I2 independently checks fresh private binding, changed negative objects and exact source/Git/shared-olean restoration. |
| B | **PASS:** all128 native controls with exactly one full109-logical/214-expanded replay. B1/B2/B3 pin full/control/wrapper receipts. I2 independently checks exact ordered expansion, all214 results, 210 exact raw-byte observations (including two actual FFI mutants after unchanged baselines), four source challenges and restoration. |
| I | **PASS:** I1 pins the build manifest and effective toolchain identity; I2 rehashes all31 computational sources,19 generated-C modules,three binary artifacts, the C++ import library and both public producer/consumer sources. It checks current/immutable manifest equality and frozen requirement/source-document hashes. The full replay names this same manifest. |
| V | **PASS:** V1/V2 pin the complete24-control validator campaign and owned wrapper. Expected/executed/attempted rosters agree; every control passes; source/import and literal-fixture hashes remain unchanged; the oversized temporary is removed. The omitted default runs all16 semantic cases. Non-Windows process replay remains explicitly uncovered. |
| F | **PASS — final owned checks**: Default build `commands/final-default-build.json` (3.980s), separate imports `final-native-imports.json` (7.734s) and `final-validator-import.json` (6.128s), and `native-axioms-02.json` (86 inventories, 141.177s) all PASS. Both trust scans have zero matches in `final-static-command.json`; the later default claim scan in that receipt timed out and is not counted as a pass. `final-design-base.json` PASS (7.460s), `final-diff-checks.json` PASS. The unchanged strict claim rules passed all44 public paths (403 hits/zero failures,10.380s) and26 process paths (415 hits/zero failures,7.856s), in `final-claims-public.json` and `final-claims-process.json`; their exact corpus and source pins cover all changed claim documents and all production attribution paths. See WDD-20260912-NATIVE1-012 for the retained default-scan timeout and evidence-scope rationale. |
| A | **PENDING coordinator scheduling/disposition**: separately scheduled fresh blind exact-commit audit and aggregate certification, plus coordinator disposition. No owned row below supplies this authority. |

“Source candidate complete” below means the owned source proposition chain has
been reconstructed and checked. “Campaign candidate complete” identifies the
completed pinned operational campaigns. These results do not change a frozen row
to `ACCEPTED`. Final owned static checks F passed as indexed above; A remains
separate coordinator authority. I2 is an independent check by the worker lead
within this implementation task, not a fresh blind audit.

### Completed exact receipt index

All paths below are relative to `docs/internal/extensions/native1/`. Hashes are
SHA256 of the actual complete file bytes inspected for this update. The exact
ordered rosters and every designated diagnostic/result remain in these pinned
machine-readable receipts; totals here do not replace those details.

| Reference | Exact evidence path | SHA256 |
| --- | --- | --- |
| B1 | `binary-commands/binary-replay-20260912T131712734.json` | `C159656B68A1C1757EB439277D21C36C485D39A228A516BD47995E69C8CD60EA` |
| B2 | `binary-commands/binary-controls-20260912T130603847.json` | `2BEAD2557D7CD8EA6056265636B45F05E0AF68F4E39F848441EF51F9226C06ED` |
| B3 | `binary-commands/binary-v3-final-128-20260912T130558739.json` | `ACB96574D5D43E5FAA61B1571591CBCA9AE41D29C0B27DEC3377F30C6E5CD9C6` |
| C1 | `binary-commands/contract-replay-20260912T132610808.json` | `F98F12D881F0FAF1B13A6159ED1F116009C2CD5878771093B892152ED9F894FE` |
| C2 | `binary-commands/contract-replay-20260912T132516703.json` | `65909FEE725067FEFE4D46EA196F81878A95942B399AF613209EA99A825F2C50` |
| C3 | `commands/contract-controls-all-01.json` | `68AB2A0A1092EC8CB70FAABBE8692B84C2358099AA80D339E5DF3B26F5531005` |
| I1 | `BINARY_V3_BUILD_MANIFEST.json` | `A4C20BCAA5E35402293DB522CE8736A81BD84FBC67FC2648693475504E5E1069` |
| I2 | `commands/final-integrity.json` | `71E5D1D9E8A79527D0CE39DCD4C5C5BC3DD45EE527CD0E6825B8261399514181` |
| V1 | `commands/validator-controls-20260912T130117776.json` | `ED0A09875DDB653270F58EA7FE7DF6D16C938E70E6CA0DC963F7124A2AF1D6CA` |
| V2 | `commands/validator-durable-all-02.json` | `3B3688DD7842BB0EAA8E2567BC1083EACC2BC3A433A674C8F25496748DDDA46F` |

Executed source/registry identities recorded in those receipts:

| Surface | SHA256 |
| --- | --- |
| Binary registry | `2D38A1002C1E8A72DF5E164144EC4E8F5410511F2C585831AEFBBC0D1BD4C637` |
| Binary replay runner | `36774810EB0BA670594D11D11DBD22924032CE8F67554027B5ED5F02CB80DCF6` |
| Binary control runner | `EDEE71ED973FFF4BC860E1258C6B7FED315FEE43218179C800407998AAD58104` |
| Contract registry | `6E0C8E5A73F7DE47D14F7298435E7F72F2AC82A5881AEBF3EFFE0388CBF48E2C` |
| Contract replay runner | `AE8BC171667857E693D58E74626D425AB5C7F8AB43BDA4D6996A6FF92C8C3687` |
| Validator registry | `60D07EC27D7854FEB107CE8A1148F382F17F882CD8F2F18427FBD8BDE8D755EC` |
| Effective toolchain identity digest | `2E1772C727BBEB16A0B65CFEA6902C74E8184A49CF483D65DF482A8177D84402` |

I1's three native artifacts, rehashed by I2:

| Artifact | SHA256 |
| --- | --- |
| `packed_rmq.dll` | `7605525E9E89540D43DFD307E84DE24F03062A9632A59062682600D20E0168C4` |
| `packed-rmq-native.exe` | `7A6FB03165C0DFCBD8F58D4A7E04D383019D1633CC9E28F052B57E2FA27814D7` |
| `packed-rmq-native-cpp.exe` | `74F0AE4696EBD35DF6C230D25859FA83458F62BDDD2AE8EE6CAE90E59956BEC2` |

B3/C3/V2 all exit0 with empty stderr, no timeout and no output-limit failure,
using kill-on-close process ownership: respectively2337.505/816.151/257.464
seconds under7200/2100/600-second deadlines. C1's once-created private import tree
contains410 physical olean copies (396,755,200 bytes), with matching copy hashes.
Each fresh producer replaces only its private binding before its untouched
literal consumer; every negative producer hash differs from the shared baseline
and remains identical before/after consumer execution. I2 verifies these links
and exact source/Git/shared-artifact restoration. These are the specified replay
outcomes under recorded host conditions, not verified compilation or unlimited
host capability.

## Exact shared objects and load-bearing conclusions

For arbitrary `xs : List Int`, set `w = wordWidth xs.length`,
`M = buildMemory xs`, `P = queryProgram`, `C = canonicalImage xs`,
`I = initialState xs.length left right`,
`Q_f = run M P f I`, `E_f = canonicalExecution xs left right f`, and
`O_f = canonicalObservation xs left right f reads`.
The representable endpoint domain **D** is exactly
`left < 2 ^ wordWidth xs.length` and `right < 2 ^ wordWidth xs.length`.
It includes representable-invalid endpoints. `ValidRange xs left right` is
required only where the proposition states it, and implies D.

The image identities are `C.width = w`, `C.inputLength = xs.length`,
`C.registerCount = queryRegisterCount`, `C.memory = LimbMachine.encodeMemory w M`
and `C.code = LimbMachine.encodeCode w P`. These are the machine's literal byte
array aliases, not a second decoded store. `nativeInitialState C` initializes
r0/r1 from endpoint words and r2 from **C.inputLength**. The runtime receives C's
own code and memory. Nat values temporarily used in arithmetic/decoding are not
a persistent alternate program or answer cache.

The following excerpts are literal public propositions from the incorporated
42-type inventory; all omitted fields retain their full types there.

```lean
  serializedRoundtrip : ∀ image : StorageImage, image.Valid →
    StorageImage.decode image.encode = some image
  serializedInjective : ∀ x y : StorageImage, x.encode = y.encode → x = y
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
```

Three supplemental chains are essential to the row evidence:

1. **Operations and faults.** For all ten arithmetic constructors,
   `checkedArithmetic_accepts_iff` equates success with canonical operands and
   `ArithmeticSafe`; `checkedArithmetic_success` identifies the exact decoded
   result with `op.eval`, below `2^w`. Safety includes no subtraction underflow,
   positive div/mod divisor and shift count below w. Comparison, bit operations,
   exact checked USize address conversion and nonnegative Int conversion have
   their separate success consumers. Named rejection equations distinguish
   malformed words, overflow, underflow, zero divisor and oversized shifts.
   `execute_encode` and `run_loaded_reference` preserve whole runs under their
   explicit Fits/WritesOnly/RunSafe premises. `canonical_run_safe` derives those
   premises for Q_f for every f under D; N14 does not ask callers to assume safety
   of a different run. Missing data records the attempted address/reply none;
   missing fetch stops; malformed fetched code faults. Their statuses and counts
   are separately checked by L.
2. **File and host.** For every bytes/image,
   `StorageImage.decode_iff` is `decode bytes = some image ↔ bytes = image.encode ∧ image.Valid`.
   Valid enforces positive width, fitting inputLength/registerCount, canonical
   memory and at-most-five-field canonical rows accepted by the instruction
   parser. `decoded_fields` preserves all five image fields.
   `decode_truncated` rejects every proper prefix of any encoded image.
   `BinaryCursor.decodeSupported_eq` holds for every limits and ByteArray;
   early digit caps reject before digit accumulation. RMQN/version1 uses minimal
   little-endian all-Nat scalar digits with unary byte-length framing and framed
   width-sized words. Supported limits are separately 128 MiB, width4096,
   registers65536, instructions1000000 and memory words1000000; query fuel is at
   most1000000 and endpoints must be canonical full-width buffers. These finite
   API limits do not narrow the abstract all-size theorem or promise allocation.
3. **Occurrences and independent oracle.** For every xs/endpoints,
   `Witnesses.stages_trace` identifies the flattening of actual semantic stages
   with `SuccinctClassic.queryTraceResult`'s trace. Under ValidRange, a
   decomposition `flatten stages = prior ++ readWord segment index word :: after`
   and `readerReceipts shape M segment index[offset]? = some receipt` yield
   `queryRun M xs.length left right.reads[174 + (logicalTraceReads shape M prior).length + offset]? = some receipt`
   via `staged_receipt_at`. `occurrence_source` then identifies the actual global
   transition, its prefix prestate, fetched load and M[address] reply. Equal
   repeated reads remain different positions. `arrayRun_exact` connects the raw
   array run on P.toArray/M with Q_queryBudget. Exported expectations use that
   run and independently checked literal/public/scanWindow answers, never the
   limb result. The cross-cell fixture has width184, span6 at offset180 and
   successful adjacent addresses179/180 at transitions10378/10384.

## Per-requirement evidence and owned disposition

Each challenge below is tied to its rejecting proposition or production guard.
S/L/W identify checked source/leaf evidence; C, B and V identify completed
contract, native and validator campaigns at the exact receipt index above. Merely naming
a possible challenge does not claim a newly executed mutation.

| Frozen ID | Exact source/object chain and anti-vacuity surface | Operational evidence and owned candidate status |
| --- | --- | --- |
| `REQ-NATIVE-FINITE` | N14 is whole-run `E_f.decode = Q_f` for every xs/f under D; N15 transports that run to the actual core. The nine-constructor simulation preserves final state, status, ordered failed/successful receipts, steps and all six categories on C's literal byte arrays. N25–N30/N41 expose each observation. A changed loaded destination, reversed duplicate read or category is excluded by execute_encode/run_loaded_reference and N14/N29/N30. | S/L source candidate complete; C/B/I campaigns and identity complete, including all observation projections and corruption controls. F passed; A separate. |
| `REQ-NATIVE-WIDTH` | N01/N02 give decode(encode w value)=value under value<2^w and encode(decode word)=word under Canonical. N03 and the supplemental operation/fault chain cover all arithmetic, comparisons, bit operations and exact conversions. N17/N23/N24/N31/N40 apply the same w to C/Q. Truncation above bit128, div0, shift≥w and dormant oversized operands contradict those exact predicates. | S/L source candidate complete, including168/176-bit checks and W's184-bit fixture. B passes finite API width/fault controls; C/I complete. N10/N35–N38 retain host limits. F passed; A separate. |
| `REQ-NATIVE-SERIAL` | N04/N05/N13 and decode_iff give canonical image roundtrip/injectivity, exact accepted bytes and identical loaded M/P cells. Cursor all-byte equality connects the efficient bounded parser; N21 counts rounding/framing. Wrong version, truncation, trailing data, invalid tag/length/padding or substituted fields contradict decode_iff/decoded_fields/decode_truncated and N35. | S/L source candidate complete. C/B/I complete for public dependencies, actual malformed/corrupt/limit rejections and identical loaded cells. F passed; A separate. |
| `REQ-NATIVE-CODE` | N06 states nativeLoadEntry's exact supported-decoder equation; N07 returns nativeObservationText(nativeCore image left.data right.data fuel reads) under NativeQuerySupported. N08 projects that same core to LimbMachine.run, and N15/N16 join Q_f. Redirecting Lean source to a sibling evaluator breaks those literal consumers. | S/C source and contract candidates complete; I pins executable Lean→generated C→shim→Rust/C++ and B passes actual source/FFI challenges. Compiler/runtime translation remains assumed. F passed; A separate. |
| `REQ-NATIVE-API` | N07/N10/N16/N35–N38 require checked image/fuel/endpoints and exact host conversion. N08 gives the complete runThin projection; N09 literally says `(nativeCore image left right fuel false).2.readsRev = []`. Default mode cannot substitute an answer cache or full read log while preserving these conclusions. | S/L source candidate complete. B/I pass retained-load, repeated-query, length/error/endpoint, C++ parity and exact-LF controls at the documented ownership boundary. F passed; A separate. |
| `REQ-NATIVE-JOIN` | publicContract consumes NativeExecutionCapstone; N11/N13/N14/N15/N18/N19/N21 join C/M/P/w/I with the accepted fullyChargedPackedQueryCapstone. Host support is confined to API N12/N16, while abstract fields keep their all-size guards. A sibling-store join or collapsed public proposition fails the corresponding literal type/publicContract. | S source candidate complete; C/B/I/V campaigns and identity complete. This owned result is not full-lane acceptance. F passed; A separate. |
| `CHK-NATIVE-CONTROLS` | W's actual semantic stage→ordered physical occurrence→global transition/prestate chain covers both select call sites, fringes, interior/final rank and a real two-cell crossing. N14/N15/N29/N30 transport independent expectations. staged_receipt_at, occurrence_source, crosses and checkKinds reject relabeling, missing occurrence, false crossing and empty coverage. | S/L/W source/export candidates complete; B replays all seven actual witnesses through shipped clients and passes the full invalid/image/word/source roster. C/I complete. F passed; A separate. |
| `REPLAY-EXACT-REGISTRY` | This is an executable invariant: versioned nonempty required/actual rosters must be exactly equal in order. checkKinds pins seven exports; contract registry pins baseline+42+public-collapse. Removing an ID or dispatching nothing must hit the production roster boundary. | C exact44/nine, B exact109/214/128 and V exact24 rosters PASS; I2 independently verifies binary/contract ordered expansion and all verdicts. Owned campaign candidate complete. F passed; A separate. |
| `REPLAY-SELECTOR-NONVACUITY` | Production parsing distinguishes omitted/full, one valid ID and bound empty/whitespace/malformed/unknown selectors before dispatch. Real child-process outcomes, not internal helper membership, establish argument transport. | C/B/V pass real omitted/valid/empty/whitespace/malformed/unknown selector boundaries and exact nonempty executed sets. Owned campaign candidate complete. F passed; A separate. |
| `REPLAY-SUBPROCESS-DEADLINE` | owned_process_tree owns descendants, retains exit/stdout/stderr, bounds time and rejects timeout/output-limit as completion. Mutation runners restore exact saved bytes/diff and shared artifacts in finally. Deliberate sleep, stderr loss or dirty restoration must hit these production guards. | C/B/V retain owned limits, exits/stderr and restoration; I2 verifies recorded children complete and source/artifact restoration. Non-Windows replay remains uncovered. Owned campaign candidate complete on the recorded host. F passed; A separate. |
| `INV-STORE-IDENTITY` | N13 gives decoded memory/code exactly encodeMemory w M/encodeCode w P; N14 executes them. N18/N19/N21 count those same arrays/fields; N32/N40 back reads by decodeMemory C.memory=M. Counting M while running M′ does not inhabit these literal propositions. | S/C source/contract candidates complete; I/B pin actual loaded bytes, cells and executables to the same source/counting chain. F passed; A separate. |
| `INV-VALUE-DEPENDENCY` | N32 includes `execute M t.instruction t.before = (t.after,t.receipt)` for the actual load. Primitive.execute writes its reply to the destination; later operations/routes/halt use those registers, preserved by N14/N15. Inherited metadataSetupBlock_run_value_dependency changes register16+i under its two-memory length≥174/i<174/running guards; locate_run_position_dependency changes the returned position for valid regular segments<23,≠20/index0/positive count and unequal stored bases; crossing_value_dependency changes the returned span numeral in its explicit two-cell instances. Constant values with only changed logs contradict these value projections. | S/L source candidate complete; C protects execution/provenance fields, W supplies connected occurrences and B passes runtime challenges. No finite witness implies universal sensitivity of irrelevant memory. F passed; A separate. |
| `INV-SEMANTIC-NONVACUITY` | N33 equals the actual174-prefix plus operational logical expansion. stages_trace expands real select/LCA/fringe/rank calls; staged_receipt_at/occurrence_source fix cumulative receipt positions and actual producing transitions. Replacing this by True, arbitrary labels or reused equal receipts fails those equations and exporter offset/coverage checks. | S/W source/export candidates complete; C protects public dependencies and B passes seven actual shipped-client witnesses and semantic occurrence controls. F passed; A separate. |
| `INV-TRACE-EXECUTION` | N14 preserves the transition list, N08 folds that list, N29/N30 give its categories/reads. N32 identifies `t.before = (canonicalExecution xs left right index).decode.final` at an actual indexed transition. Decorative or reordered events cannot satisfy this prefix/prestate equation and execute equation. | S/L source candidate complete; repeatedLoad_positions preserves distinct indices/PCs for equal receipts. C/B pass public dependencies and exact ordered native observations. F passed; A separate. |
| `INV-STORE-AGREEMENT` | N34, quoted above, quantifies every width-fitting supplied memory agreeing at the original run's read addresses under D, and concludes equality of the entire decoded supplied run with E_queryBudget using C.code and C's initial state. Safety follows from inherited run agreement; it is not assumed for a sibling execution. Answer-only equality or an extra unrelated safety guard weakens the literal consumer. | S/C source/contract candidates complete: N34 fixes the entire supplied run. I/B identity/operational evidence complete; the universal proposition remains source evidence. F passed; A separate. |
| `INV-READ-BACKING` | For every actual indexed transition/receipt under D, N32 gives fetched load, prefix prestate, address from its actual register and reply `decodeMemory C.memory[address]?`; N40 adds address/reply width. ValidRange plus inherited noFailedLoads gives success throughout canonical valid queries. A fabricated reply at an absent cell contradicts lookup equality; G-FAULT records none instead. | S/L/C source/contract candidates complete; W gives actual positions and B passes successful/failed ordered-read comparisons through delivered clients. F passed; A separate. |
| `INV-WORD-WIDTH` | N11/valid_iff makes all C words canonical at w, N24/N31 covers code and transition operands/poststates, N40 bounds successful replies, and inherited finalStateFit bounds final registers/PC/packet. High padding or value≥2^w violates Canonical even if byte length is unchanged. | S/L/C source/contract candidates complete; B passes width, padding and result boundary controls. Rounded byte capacity does not replace the modeled value bound. F passed; A separate. |
| `INV-ADDRESS-WIDTH` | N23 states every address≤C.memory.size is<2^C.width, including the sentinel. N24 quantifies every instruction∈P, including dormant registers, branch/jump targets and operands. N31/N40 cover executed safety/reads; N42 gives Fits for every successfully loaded row. usize conversion N37/N38 is a separate conclusion. | S/L/C source/contract candidates complete; B passes host/model-limit rejection controls. Exact usize conversion never substitutes for N23/N24/N40. F passed; A separate. |
| `INV-INSTRUCTION-ATOMICITY` | execute_encode preserves the corresponding one of nine ordinary Primitive.execute constructors; arithmetic selects one of ten declared word operations. Select/rank/fringe loops are sequences in P. N14/N29/N41 retain each charged transition/category. A hidden uncharged recursive semantic macro does not satisfy those execution equations. | S/L/C source/contract candidates complete; I/B bind execution to the primitive model and exact categories. Multiprecision runtime work is not physical constant-time evidence. F passed; A separate. |
| `INV-PROGRAM-ACCOUNTING` | P is a closed queryProgram; geometry comes from counted metadata. N22 fixes program length/budget837572, registers8271, scratch8274 and encoded fields≤5*budget. N19 counts `C.wordCount*C.width + (queryRegisterCount+3)*C.width`; N21 includes the exact flattened instruction encodings plus M, rounding and framing; N20 gives both LittleOLinear residuals. An uncounted shape-dependent code cache breaks the C.code identity and these counts. | S/C source/contract candidates complete; I/B pin actual image/code/source identity. Numeric accounting does not bound Array headers or allocator bytes. F passed; A separate. |
| `INV-ORACLE-INDEPENDENCE` | arrayRun_exact joins the raw P.toArray/M evaluator to Q. Exporter uses its actual counts/ordered reads and checks literal answer, public queryTraceResult and scanWindow agreement. N25 gives result `some(scanWindow xs left (right-left)+1)` under ValidRange; N39 derives LeftmostArgMin. Copying expected native results or using sibling raw inputs violates this exporter call/object chain. | S/W source/export candidates complete; B consumes frozen independent expectations and program/fixture/source pins; C preserves semantic types. F passed; A separate. |
| `INV-VALIDATION-REACH` | Validation.PackedNative imports Contract and actually calls nativeLoadEntry/nativeQueryEntry/nativeCore on the loaded image; compare mode consumes independent expectation bytes. N06/N07/N08 specify these exact declarations. Replacing the call with predecessor ArrayRun is not a check of this layer. | S/V/B/I source and operational candidates complete: V passes all24 controls, including real default16/16 and compare channels; B passes source-correspondence challenges. F passed; A separate. |
| `INV-ALL-SIZE` | N11/N13/N17–N24 quantify every List Int/n without support assumptions. N14/N15 cover every fuel under D; N25/N39 cover ValidRange; N27 states representable-invalid result=some0, reads=[] and steps≤6. All-Nat scalar framing has no64-bit ceiling. Hidden readiness/fixture cutoffs would weaken these literal quantifiers. | S/C source/contract candidates complete; B passes finite valid/invalid/support boundaries. N12/N16/N35–N38 retain finite API limits without narrowing abstract all-size propositions. F passed; A separate. |
| `INV-PROOF-SEPARATION` | nativeCore receives only retained image, endpoints, fuel and reads flag. N08 is its actual execution projection and N09 excludes default reads. Capstone fields and N42's existential raw Program witness are Prop evidence, not runtime arguments or caches. Supplying a proof-held/scanWindow answer would alter N07/N08/N15's fixed computation. | S/L/C source/contract candidates complete; I/B identify the tested erased computational source and default observation path. Compiler proof erasure and allocation remain explicit assumptions. F passed; A separate. |
| `INV-NO-SYNTHETIC` | N32 binds every actual receipt to its producing load/prestate/execute equation; N33 and W bind semantic expansion to ordered occurrences. N08/N29/N30 derive observations from those same transitions. Post-hoc fabricated events or decorative rereads violate N14/N15/N32/N33 and the value/state dependency chain. | S/L/W/C source/export/contract candidates complete; B passes exact ordered native observations and semantic controls, retaining value/prestate flow rather than event-set membership alone. F passed; A separate. |
| `INV-CATEGORY-SEPARATION` | N18/N19/N20 concern numeric capacity/residuals; N21 adds exact limb rounding and framing; N28/N29/N41 concern modeled steps/six categories; N08/N09 concern optional observations; N35–N38 concern finite host resources. None equates these with runtime object bytes or elapsed time. | S/C source/contract candidates complete; I/B runtime evidence remains distinct from numeric/model conclusions. Final public-claim checks remain part of F. F passed; A separate. |
| `INV-PUBLIC-COMPOSITION` | N11–N16 use C/M/P/w/I for validity, loading, all-fuel execution and exported source; N18–N22 count that same image/program/scratch; N25/N39 give the valid-range leftmost result. publicContract consumes the entire42-field record. Different payloads or mixed validity guards cannot satisfy these literal arguments. | S/C source/contract candidates complete; I/B/V identity and campaigns complete on the same source. Final acceptance authority remains separate. F passed; A separate. |
| `INV-CERTIFICATE-ANTI-BYPASS` | All42 mandatory fields have independently written literal N01–N42 consumers plus publicContract. A weakened field or public theorem must first compile in the producer and then fail the untouched consumer at its designated type mismatch, using the freshly compiled producer object. An axiom inventory alone cannot establish this dependency. | C campaign candidate complete: C1/C2/C3 and I2 establish exact44/nine, all43 designated negative surfaces, fresh/private/shared hash links and the positive baseline. No ACCEPTED state asserted. F passed; A separate. |
| `INV-MUTATION-REPRODUCIBILITY` | Versioned runners/registries pin load-bearing kind/operation/expected result/fixture fields; no-op mutations, omitted IDs, stale producer imports and dirty restoration reject. Contract's physical complete import tree binds each successful fresh producer before the unchanged literal consumer and requires negative bytes to differ from shared baseline. | C/B/V campaigns complete with versioned rosters, expected accepts/rejections and restoration; I2 checks fresh contract imports and actual FFI/source outcomes. Final committed checks remain part of F. F passed; A separate. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | C is one pre-execution M/P image. N14 covers all fuel, N32 backs each global indexed transition, N33 expands the full174-prefix plus logical query trace, N34 handles agreeing stores, and W preserves cumulative stage offsets. N23/N24/N31/N40 cover dead/sentinel/executed domains. Suffix-only proofs, reset numbering or stage-private allocations violate these same-object equations. | S/W/C source/export/contract candidates complete; B passes the complete loaded-client replay with global occurrence evidence. The physical-cell model is not a one-CPU-microstep claim. F passed; A separate. |
| `INV-WIDTH-SCALING` | N17 literally proves `Nat.log2(n+2)+1 ≤ wordWidth n` and `wordWidth n ≤ 192*(Nat.log2(n+2)+1)`. The same query-independent w is C.width in N11/N14/N19/N23/N24/N31/N40 for storage, complete code, sentinels and primitive results. An unused logarithmic width or query-selected64-bit surrogate cannot inhabit these types. | S/L/C source/contract candidates complete; I/B bind finite loaded execution to the same width declaration, preserving host restrictions. F passed; A separate. |

## Final insertion checklist and interpretation

B/C/I/V now name exact completed evidence; no campaign placeholder remains.
F is **PASS** at the exact outcomes and source records below. The final report
and this appendix receive a further focused text/diff check after insertion. A is a separate coordinator audit/gate and
acceptance disposition. The subsequent report/audit packet supplies the exact
implementation/evidence commit after committing this appendix; this document
does not attempt to contain its own future commit identity.

Conceptually, the owned source work joins one stored-byte image to the real
executor and accepted PQ1 run, including value updates, ordered repeated reads,
code/data/scratch accounting and all-size width/safety. The completed contract
campaign demonstrates dependency on every literal public field and the public
proposition. The completed native/validator campaigns replay the specified
observations and defects against pinned shipped clients and semantic source.
The final integrity check binds those outcomes to actual source/generated-C/
artifact bytes. These are owned candidate results, not coordinator acceptance.
Lean kernel/model proof, executable validation, artifact identity and process
evidence retain different roles. Compiler/runtime translation, legitimate
readable spans and owned handles, initializing-thread lifetime, supported
Windows ABI and allocation availability remain explicit assumptions. A skeptical
reader should inspect the exact receipt results and separately required final
static checks and fresh audit; no global closure follows from this appendix alone.

### Worker disposition and final-check interpretation

All 31 frozen IDs above have source and operational evidence for
`CANDIDATE_COMPLETE`. The worker lead independently checked the full31/19/3
source/generated-C/artifact inventory, exact214 binary results and raw bytes,
128 controls, all44 contract cases and nine controls, fresh producer binding
and restoration in `commands/final-integrity.json`. The full42 literal types
remain incorporated at their unchanged source hash. No requirement or original
matrix byte was changed. Coordinator ACCEPTED, fresh blind review and scheduled
aggregate certification are separate and remain unrecorded by this worker.

The default-root claim attempt timed out while recursively rescanning archived
JSON output; its failed receipt remains intact. The completed applicable-source
checks use the same production Strict rules and unchanged policy on every
current public/attribution surface and every changed authored process document.
They do not claim that the unfinished default-root invocation passed. Source
and artifact evidence are independently checked by the executable registries,
exact byte comparisons, expected-type consumers and restoration controls.

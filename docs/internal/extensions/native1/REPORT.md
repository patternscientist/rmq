Status: INCOMPLETE
Phase: APPROVED_ROUTE_IMPLEMENTATION

# NATIVE-1 worker report

## Current continuation checkpoint

The coordinator approved the Lean-to-C route and directed continuation to the
full frozen native target. Work is continuing on the same branch; this is not
a new route-review pause or a candidate completion report. The original 31
acceptance rows and frozen prefix remain unchanged.

The four requested repairs now have concrete evidence: the native path policy
passed all 98 production regression cases and strict checks of the earlier
native commits; the version-3 semantic registry passed 55 controls and all 16
native route cases; the toolchain-aware build/cache predicate passed 10 controls
and the repaired native build; and the C++ consumer correctly releases its
handle and returns failure on parser rejection. The initial version-2 output-
channel mismatch remains recorded as a failed harness run. POLICY_REPAIR.md,
REGISTRY_REPAIR.md and the commands directory contain exact source pins and
complete receipts. These repairs do not close the full native acceptance rows.

The continuation has checked byte-limb operation/full-run proofs, binary
roundtrip/injectivity/accounting, the all-byte indexed loader refinement and
the canonical exported-source join. The named target
`nativeExecutionCapstone_holds : NativeExecutionCapstone` and all 42 independent
literal field consumers now pass. The same loaded arrays carry results,
leftmost semantics, counts, ordered attempted reads, positional backing,
width/accounting and supplied-store agreement. Host conversion claims apply
to successful finite lookups and do not assert allocation availability.

Focused producer/consumer checks are complete for Limbs, Machine, CodeFacts,
Binary/Codec/Bounds and Cursor/Core. Binary Checks passed 37 controls and 13
axiom inventories; Cursor Checks passed 21 concrete controls and its independent
consumer/axiom inventory. Canonical (9.070s), CanonicalImage (8.210s), Entry
(6.328s), Host (6.138s), Execution (7.388s), the 42-field Capstone (4.970s) and
Contract (7.309s) passed. Their individual failed development attempts remain
recorded; none was a timed-out success or a weaker completion endpoint.

The first binary build passed against 31 source inputs and 19 emitted-C
modules, producing the DLL and Rust/C++ clients. All 31 source, 19 generated-C
and three artifact hashes were independently rechecked. Both clients passed
the same exact 24-byte startup observation (Rust 0.266s, C++ 0.453s), exit zero
and empty stderr. BINARY_BUILD_MANIFEST.json and the startup receipts preserve
the input and expected bytes and the checked artifact identity. The expanded
toolchain identity includes the effective C++/MSVC/SDK dependency roots; the
earlier version-1 inventory remains historical evidence. The executable Lean
validator passed 16/16 cases, and the semantic witness source proofs check.
Witness generation, expanded native/FFI and certificate mutation campaigns,
the complete axiom inventory, final audit and aggregate certification remain
open. No full frozen
acceptance row is recorded as closed. No source branch has been pushed or
merged; local commits remain checkpoints.

Claude tools were discovered after the coordinator's operational notice, but
automatic approval review rejected the one attempted external helper call;
no job started. The requested disclosure and complete attempted brief are in
CLAUDE_ASSISTANCE.md. Independent local work continues without a transport
workaround or account/billing change.

## Historical route-review submission at c8c266f

The following original phase account is retained as history. Its open policy
and process-control findings are superseded by the repair evidence above; its
source and artifact identities still describe that earlier experiment.

The mandatory contract/route-review evidence is ready for coordinator
disposition. The assigned native capstone is not complete; no full acceptance
row is closed and no formal obstruction is claimed. The frozen assignment
expressly permits this incomplete evidence phase before dependent implementation.
The strict design-policy check also has an unresolved classification failure.

## Identity and evidence

- Worker handle: NATIVE-1; requested task title: `(NATIVE-1) Verify native packed execution`.
- Branch: `codex/native-1-packed-execution`.
- Worktree: `C:/Users/poin/.codex/worktrees/1817/RMQ`.
- Exact base and workflow governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Exact implementation/evidence commit: `3329a6e90cf70bc10b3cb68b008f8a23264ce567`.
- This report and subsequent policy/review evidence form a documentation-only
  follow-up; its commit is identified in the final task response.
- Required target: `RMQ.SuccinctFinal.PackedNative.nativeExecutionCapstone_holds`
  in `RMQ/Core/WordRAM/Native/Capstone.lean`, consumed by
  `RMQ/Validation/PackedNative.lean` and the delivered native core. Those two
  final modules and the native validation lake target are not yet implemented.
- Source coordinator task: `01a0830e-2777-7e50-a800-02929dc6d724`.

The [frozen matrix](ACCEPTANCE_MATRIX.md) retains all 31 original requirement
rows, including 21 inherited invariants. Its initial 28,298-byte UTF-8 prefix
still has SHA-256
`0A5D2313CCEC30DE81AAB3B19439247C612CE4B8FC6C19C0BF51F6C3809D103E`.
Only evidence was appended. [Phase integrity](commands/phase-integrity.json)
checks that prefix, the unique IDs, all 15 source pins and both native artifact
pins against the committed implementation's current files. Tests were executed
before the implementation commit, so their recorded Git HEAD is the base plus
the then-uncommitted delta; these source/artifact pins connect that evidence to
the exact implementation commit rather than treating the old HEAD alone as its
source identity.

The exact-governance preflight passed before substantive work, requiring
`rmq-proof-sprint` with the actual runtime project catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. The canonical proof-sprint
skill and completion gate governed the work. Local commits are authorized;
there has been no push, merge, branch deletion, shared-cache link or baseline
Packed-module change.

## What is proved and actually compiled

`Native/Finite.lean` changes program, memory and register storage to Arrays of
natural cells. Its operation simulation covers the original instruction
constructors under a bounded-destination guard. The full fuel theorem identifies
the complete decoded run, including every ordered transition, with the original
PQ1 run. `FiniteState.ofState` adapts original registers with a zero tail.
This is a useful intermediate representation, not the required finite-limb
implementation.

`Native/Thin.lean` defines `runThin`, a tail-recursive execution fold that does
not construct a transition list. It derives instruction and category counts
from actual finite steps, optionally collecting ordered read receipts. Its
proofs connect the fold to the complete raw execution. `Native/Route.lean`
defines the actual `routeCore` consumed by the textual experiment entry
`routeEntry`, exported as `rmq_native_route`.

These exact checked proposition shapes use the `PackedNative` namespace and
opened `PackedWordRAM` names:

```lean
theorem runFinite_decode (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    (runFinite memory program fuel s).decode =
      run memory.toList program.toList fuel s.decode

theorem routeCore_ofState (observeReads : Bool) (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    decodeThin (routeCore observeReads memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)) =
      observeRun observeReads (run memory program fuel s) {}

theorem runThin_no_reads (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState) (a : Stats) :
    (runThin false memory program fuel s a).2.readsRev = a.readsRev
```

The independent expected-type consumer is
`scripts/packed_native_types.lean`. Additional checked declarations are
`executeFinite_decode`, `runFinite_ofState`, `runThin_projection`,
`runThin_reference`, `routeCore_source`, `routeCore_reference`,
`routeInitialState_decode`, `routeDestinationFits_iff`,
`parseInstruction_encoding` and `instruction_encoding_injective`.
The last two concern numeric instruction lists, not a binary image.
The finite leaf's detailed proposition/command account is in
[FINITE_LEAF.md](FINITE_LEAF.md); the source-chain and proposed canonical
proposition are in [ROUTE_EVIDENCE.md](ROUTE_EVIDENCE.md).

Object composition is explicit: the same original `memory` and `program` become
`toArray` values; the finite state decodes to the original state; `routeCore`
calls `runThin`; `decodeThin` returns the final state and the fold over actual
steps. Nothing computes a reference answer before the charged reads. The
canonical instantiation using `buildMemory`, `queryProgram`, `queryRegisterCount`
and `initialState` is still a proposed theorem. The slim route build imports
the baseline Scratch closure; it does not yet import the full canonical
allocation/capstone closure. Initialization quotes and proves the literal
Guard state body with r0=left, r1=right, r2=n and a zero tail.

The delivered experiment compiles that actual Lean declaration into C and a
DLL. Rust calls it through an explicit-length C ABI. The C shim returns an
owned Lean-string handle with a borrowed byte accessor and release operation;
Rust copies the output before releasing it. A single process owner and
non-Send/non-Sync marker restrict Rust use to the initializing thread. The C++
example consumes the same DLL and C exports. Build/replay commands and ownership
limits are documented in `native/packed-rmq/README.md`.

## Verification and its limits

[COMMANDS.md](COMMANDS.md) records commands, covered rows, deadlines, outcomes,
failures and durable stdout/stderr receipts. [PHASE_RESULTS.json](PHASE_RESULTS.json)
is a compact final-artifact index.

| Check | Result and exact evidence |
| --- | --- |
| Final narrow Lean/C/Rust build | PASS; `build-20260912T080927170.json`. Hash-verified local Lean/C reuse, DLL link 35.124s and offline locked Cargo release 4.8s. |
| Actual native phase registry | PASS, exact 14 expected / 14 executed; `route-20260912T081311355.json`. Eight independent PQ1 fixtures, startup, no-read mode, malformed text, source-core mutation and stale-source rejection. |
| Boundary controls | PASS, exact 8/8; `controls-20260912T081542413.json`. Empty/whitespace/malformed/unknown selectors, missing source/artifact/fixture inventory and restored smoke. These invoke the real script in-process; OS command-line serialization is not covered. |
| C++ complete path | PASS, every n9-full output line matches; `cpp-n9-full-final.json`, exit 0 in 10.318s. |
| Independent expected types and axioms | PASS, `exact-types-01.json`, 6.105s. Thirteen declaration inventories use only propext, Quot.sound and Classical.choice; numeric instruction decoding has no axioms. |
| Trust-token and native-decision scans | PASS: both prescribed scans have zero matches; `hygiene.json`. Lean source unchanged afterward. |
| Strict claim scans | Whole scan PASS with zero strict failures; lossless full receipt and hash summary retained. Focused packet scan PASS. README's first focused scan failed; explicit modeled-cost separation repaired the prose and focused rerun passed. Explicit report scan including process records PASS, one allowed hit and zero strict failures in 5.358s; `claim-drift-report.json`. |
| Frozen requirements and build identity | PASS, `phase-integrity.json`: 31 unique IDs, original prefix, 15 source hashes and two artifact hashes. |
| Working/index and implementation committed-range whitespace | PASS; `git diff --check`, staged check, and `committed-diff-phase.json` against the exact base through 3329a6e. Final report-commit range is checked again at submission. |
| Strict design policy | FAIL, `design-phase.json`, exit 1 in 10.99s without timeout: 28 authorized native paths have no classification rule. No policy pass or waiver is claimed. |
| Full lake build, native final validator/capstone, full final campaign, aggregate and fresh blind final audit | NOT RUN in this authorized route-review phase. Full target modules are absent; broad certification requires a coordinator host slot. |

For n9-full, the independently exported expected answer is index 7, packet 8,
with 13,568 instructions, 266 ordered attempted reads, and category counts
`[266,4607,2461,2315,3918,1]` in memoryRead/registerWrite/arithmetic/comparison/
branch/control order. All address/reply observations compare exactly. Supplied
fixtures exercise declared widths of 168 and 176 bits. The exporter identity
and exact fixture/program hashes are committed in the fixture manifest.

The mutation replaces the actual `routeCore` fuel by zero. Its proof check must
fail with the expected type mismatch at `routeCore_source`'s exact proof line;
the runner restores source bytes and checks the diff. This proves reach of
that phase correspondence consumer. It does not constitute the final public
field/dependency or complete native semantic mutation campaign.

Earlier build failures were diagnosed separately: a suffix path, absent general
C headers, initial-state elaboration and a runtime-init declaration. Bounded
sandbox native startup and even argument-only probes timed out with no output
and almost no CPU; owned children were cleaned. The identical argument-error
probe on the authorized host returned expected exit 2 in 4.603s. Subsequent
host execution used the same bounded ownership wrapper. These timeouts are
retained as incomplete observations; they are neither passes nor semantic
counterexamples. Non-Windows execution and process ownership remain uncovered.

## Required dispositions and every open acceptance row

The design checker fails closed before ledger coverage because
`Get-PathDisposition` has no rule for the 28 new native files. The worker's
authorized write scope excludes `scripts/design_decision_check.ps1`; the
failure is preserved rather than hidden by moving files, changing shared
policy, or inferring a waiver from the new design entries. The coordinator
must arrange an explicit native-path classification with appropriate regression
coverage and recheck the exact range. This is a process integration issue, not
a mathematical impossibility claim.

The mandatory route review must also dispose of the actual Lean-to-C route,
the raw-versus-checked fault split and the proposed canonical source theorem
before dependent limb/binary/API interfaces are fixed. No external proof tool,
Mathlib dependency or Lean upgrade is requested.

All frozen rows remain OPEN:

- `REQ-NATIVE-FINITE`, `REQ-NATIVE-WIDTH`: finite limbs, complete safe arithmetic
  and explicit checked faults, addresses/operands, canonical all-size and
  representable-invalid instantiation, finite host support and overhead.
- `REQ-NATIVE-SERIAL`: versioned bounded binary parsing, roundtrip/injectivity,
  padding/length accounting and exact counted-cell identity.
- `REQ-NATIVE-CODE`, `REQ-NATIVE-API`, `REQ-NATIVE-JOIN`: final loaded-limb source
  correspondence, full marshaling/ownership/error contract, canonical same-object
  capstone and final public typed consumers.
- `CHK-NATIVE-CONTROLS`: operational cross-cell/select/fringe/rank witnesses,
  width/address/arithmetic and malformed binary controls, complete projection
  and public-dependency mutations.
- `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`,
  `REPLAY-SUBPROCESS-DEADLINE`: current phase evidence is partial; full native
  registry and actual OS process-boundary selector coverage remain required.
- `INV-STORE-IDENTITY`, `INV-VALUE-DEPENDENCY`, `INV-SEMANTIC-NONVACUITY`,
  `INV-TRACE-EXECUTION`, `INV-STORE-AGREEMENT`, `INV-READ-BACKING`,
  `INV-WORD-WIDTH`, `INV-ADDRESS-WIDTH`, `INV-INSTRUCTION-ATOMICITY`,
  `INV-PROGRAM-ACCOUNTING`, `INV-ORACLE-INDEPENDENCE`, `INV-VALIDATION-REACH`,
  `INV-ALL-SIZE`, `INV-PROOF-SEPARATION`, `INV-NO-SYNTHETIC`,
  `INV-CATEGORY-SEPARATION`, `INV-PUBLIC-COMPOSITION`,
  `INV-CERTIFICATE-ANTI-BYPASS`, `INV-MUTATION-REPRODUCIBILITY`,
  `INV-GLOBAL-PHYSICAL-MACHINE`, `INV-WIDTH-SCALING`: each still needs its exact
  proposition consumed by the final native join. The matrix appendix maps
  current leaf evidence and residual gaps individually; no invariant is waived.

`CHK-PREFLIGHT` and the phase-local checks have the outcomes above. Final
capstone/build/axiom/audit obligations cannot be discharged by these helper
checks. Paper rewriting, publication strategy and combined-campaign integration
remain explicitly later work; no PRE builder is supplied by this lane.

## Proof digestion and trust

Conceptually, the new proof separates an actual indexed storage implementation
from its mathematical observation. An induction can forget representation while
preserving the exact original steps; a second induction erases the bulky proof
trace while keeping its result and counters. The computational declaration used
by those equalities is the one compiled and called by the experiment.

In plain English, the array interpreter performs the same natural-number
computation as the existing Lean machine, and the tested native DLL reproduces
the supplied outputs and read histories. That advances the source route but
does not yet establish a bounded-word native RMQ library.

Live proof assumptions are the bounded write destinations and, for original
register functions, a zero tail. They are not input validity/readiness guards.
Raw Nat arithmetic is total; corrupt overflow, divisor or shift inputs do not
gain new fault behavior in this leaf. Missing loads emit a failed receipt and
fault; missing instruction fetches make no step and leave status unchanged.
The future checked-word executor must define its own rejection and prove
compatibility using canonical `queryRun_execution_safe`.

Outside the kernel, the route assumes Lean 4.22 compiler correctness, bundled
Clang/C linking and Lean runtime/allocator/big-Nat correctness, Rust compiler
and FFI behavior, and the inspected single-thread marshaling contract. Pins are
Lean commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05` (Windows GNU), Clang 19.1.2
and Rust 1.89.0 commit `29483883eed69d5fb4db01964cdf2af4d86e9cb2` (Windows MSVC).
No physical constant-time, native succinct-memory or preprocessing-speed claim
follows. Modeled payload bits, multiprecision storage/runtime overhead,
proof-only fields, charged operations and measurements remain separate.

The downstream consumer now proved is the generic `routeCore_ofState` equality
and its independent expected-type script. The assigned canonical native
capstone is not closed. A skeptical graduate student should ask: which theorem
will establish that a loaded binary image contains exactly the counted cells,
that every limb operation matches the canonical safe Nat step, and that the
public source entry executes that same image without a stronger hidden guard?
Those questions are frozen requirements, not optional future hardening.

Design entries `DD-20260912-NATIVE1-001` and
`WDD-20260912-NATIVE1-001` record rationale, rejected alternatives, consequences,
repairs and evidence policy. Narrow additions to FAMILY_SUMMARY and DIGESTION_LOG
state the same incomplete scope. The independent contract/repair/packet review
is retained in CONTRACT_AUDIT.md; it is a continuation review, not a fresh blind
final audit or coordinator acceptance. After route disposition, the next crisp
consumer is the proposed canonical instantiation in ROUTE_EVIDENCE.md, followed
by the checked limb/binary construction needed by the full joined theorem.

Status: INCOMPLETE
Phase: ROUTE_READY

# NATIVE-1 route evidence

Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/native-1-packed-execution`.
Worktree: `C:/Users/poin/.codex/worktrees/1817/RMQ`.
The frozen matrix remains authoritative; this document does not close any full
native requirement. Exact implementation commit and final command receipts are
recorded in REPORT.md at phase submission.

## Route under review

Use the actual proved Lean computational declaration, emit C with the installed
Lean 4.22 compiler, compile a DLL, and call it through a narrow C ABI from Rust.
No Rust RMQ algorithm, external proof environment, new Mathlib dependency or
Lean upgrade is introduced. The user explicitly authorized this route. The
experiment supplies evidence for the coordinator's route review before the
remaining limb/binary/API construction commits to its interfaces.

Actual source chain:

1. `PackedWordRAM.execute/run` at the exact baseline supplies the reference.
2. `executeFinite`, `stepFinite` and `runFinite` in Finite.lean replace code, memory and
   registers with actual Arrays; register reads outside the bank are zero.
3. `runThin` in Thin.lean tail-recursively accumulates instruction count and all six
   category counts, with optional ordered address/reply observations. It never
   constructs a transition list.
4. `routeCore` in Route.lean calls exactly `runThin`; `routeEntry` calls the textual
   experiment parser and then `routeCore`. Its export attribute names the C
   symbol `rmq_native_route`.
5. The generated C initializer and export prototype are checked before linking.
   `route_shim.c` initializes Lean once, copies explicit-length input bytes into
   Lean strings, returns an owned Lean-string handle, exposes borrowed output
   bytes and releases the handle on request.
6. Rust's `RouteRuntime::evaluate` passes program and fixture bytes with their
   lengths, calls that symbol via the C shim, copies the output, and releases the
   handle. A process-wide atomic claim and a non-Send/non-Sync marker restrict
   the experimental runtime to one owner and its initializing OS thread.

The source is compiled, not translated into a separately handwritten Rust-like
Lean evaluator. General compiler correctness is not asserted.

## Exact checked source correspondence

Namespace below: `RMQ.SuccinctFinal.PackedNative`; reference names are opened
from `PackedWordRAM`.

```lean
theorem routeCore_reference (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    decodeThin (routeCore observeReads memory program fuel s) =
      observeRun observeReads (run memory.toList program.toList fuel s.decode) {}

theorem routeCore_ofState (observeReads : Bool) (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    decodeThin (routeCore observeReads memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)) =
      observeRun observeReads (run memory program fuel s) {}
```

These are propositions about the same memory/program, including corrupt or
missing memory, arbitrary initial status and every fuel. The only code-domain
premise is bounded destinations; all source-register indices are permitted
because the reference's zero tail is represented explicitly. `decodeThin`
retains the complete decoded final state and the Stats object.
`observeRun` folds each actual transition in order, increments the category of
that instruction, and records that transition's receipt only when requested.
Its counters are not post-hoc estimates of a separately computed answer.

The log-erasure theorem is:

```lean
theorem runThin_no_reads (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState) (a : Stats) :
    (runThin false memory program fuel s a).2.readsRev = a.readsRev
```

`runThin_projection` additionally identifies the tail-recursive result with the
fold of `runFinite`'s exact operational transitions.
`runFinite_decode` identifies that full finite run with raw PQ1.
The checked instruction-encoding lemmas establish
`parseInstruction i.encoding = Except.ok i` and injectivity of that numeric
encoding for every constructor and arithmetic/comparison tag. They are not a
binary-image roundtrip theorem.

`routeInitialState_decode` fixes r0=left, r1=right, r2=n and zero elsewhere,
using the literal state body from baseline Packed/Guard.lean:18-22.
This corrected a real marshaling bug found by independent review before the
complete-path experiment. The constant-answer smoke does not test input order.
The textual parser rejects destinations outside the bank; the corresponding
Boolean predicate is proved equivalent to `WritesOnly (· < 8271)`.

## Proposed canonical source theorem, still to be instantiated

The next exact source-consumer proposition, with all reference names fixed, is:

```lean
∀ (xs : List Int) (left right fuel : Nat) (observeReads : Bool),
  decodeThin
    (routeCore observeReads (buildMemory xs).toArray queryProgram.toArray fuel
      (FiniteState.ofState queryRegisterCount (initialState xs.length left right))) =
    observeRun observeReads
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)) {}
```

It is an intended canonical instantiation of the checked generic theorem,
using `queryProgram_writesOnly`, the definition of `queryRegisterCount` and
the initial zero tail. It is not yet a declaration checked in this worktree.
This equality itself needs no endpoint validity or word-safety guard.
For the later bounded-word refinement, the exact additional domain is
`left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length`;
`queryRun_execution_safe` must discharge safety on canonical allocation,
including representable invalid endpoints, rather than taking canonical safety
as an unexplained hypothesis. Supported host size/address/allocation limits are
a distinct runtime predicate and do not restrict the abstract all-size theorem.

The final named `nativeExecutionCapstone_holds` must then connect this same
allocation/code to proved limb encoding, canonical binary loading, native
execution and the accepted `fullyChargedPackedQueryCapstone_holds`.
No final capstone or certificate placeholder is declared in this phase.

## Corrupt-input and fault boundary

| Input/event | Current natural-cell leaf and experiment | Remaining final native obligation |
| --- | --- | --- |
| Valid/representable-invalid canonical queries | Generic raw simulation applies once canonical bank premises are instantiated. | Consume canonical safety and prove finite limb execution for every assigned size. |
| Corrupt numeric cells | Raw Nat behavior retained; cell-width parser check is not arithmetic safety. | Define checked arithmetic/fault semantics separately and prove compatibility on safe runs. |
| Missing memory load | One charged load, receipt `reply=none`, unchanged registers/PC, status fault. | Preserve in limb executor and binary-loaded allocation. |
| Missing instruction fetch | No step or charge, state/status unchanged. | State whether loader rejects or executor retains this behavior; do not silently call it a raw PQ1 fault. |
| Already halted/faulted or exhausted fuel | State preserved, no further transitions. | Preserve explicit status through final public ABI. |
| Invalid destination | Experiment parser rejects; generic theorem requires bank bound. | Prove parser-accepted image support and final API rejection. |
| Overflow/divisor/shift failure | Raw Nat semantics; no new fault behavior claimed. | Checked-fault semantics and correspondence are OPEN. |
| Malformed textual input | Experiment rejects invalid fields/tags/limits. | Versioned binary rejection and bounds are OPEN. |

The text route is for trusted experimental code. It is not the final
untrusted-image API: arbitrary huge arithmetic operands and unsafe shifts are
not yet a bounded native execution contract.

## Complete-path experiment and independent oracle

The committed fixture manifest pins the provided export to the exact baseline.
The gzip contains exactly the exported `queryProgram` text; decompression is
hash checked. Eight committed fixtures/expected outputs are copied from the
provided measured study, and all file names/case IDs are checked against exact
registries. This is reproducible finite evidence, not an unproved claim that
loaded text universally equals the canonical builder.

Before native execution, the independent reference for `n9-full` is fixed:
input [3,2,3,1,3,2,3,0,3], query [0,9), leftmost minimum index 7,
packet 8, 13,568 instructions, 266 attempted reads, and counts
[266,4607,2461,2315,3918,1] in the order
memoryRead/registerWrite/arithmetic/comparison/branch/control.
Declared width is 168 bits; other fixtures reach 176 bits.
The comparator checks every ordered address and full reply value, not only the
answer/count totals. The full registry and observed outcomes are recorded under
commands/. The host run passed all 14/14 registered cases, the boundary controls
passed 8/8, and the C++ example matched the complete n9-full reference through
the same DLL. Sandbox startup timeouts are retained as incomplete observations;
host execution was authorized after the unchanged argument-error probe isolated
the startup environment difference. See COMMANDS.md for receipt identities.

The exact fourteen-case route registry additionally includes startup smoke,
no-read mode, malformed instruction/header, a source-core mutation and stale
source rejection. This is a phase registry, not the complete final
CHK-NATIVE-CONTROLS campaign. Cross-cell/select/fringe/rank route witnesses,
width/address/arithmetic boundaries and binary padding controls remain open.

## Assumption and evidence table

| Boundary | What is established here | What is assumed or still open |
| --- | --- | --- |
| Lean kernel | Generic finite-container simulation; actual trace-free core equals raw reference observations; numeric instruction decoding. | Canonical instantiation, limb arithmetic, full binary format and final joined capstone still open. |
| Lean source -> emitted C | Actual source entry and prototypes inspected; generated from same checked files. Before/after source hashes must agree. | Lean 4.22 compiler preserves source semantics; no proved general compiler theorem. |
| C compiler/runtime | Installed bundled Clang and Lean runtime used; one explicit initialization/lifetime path. | Correct compiler, allocator, big-Nat runtime and C ABI behavior; not kernel theorems. |
| Rust/C frontend | Actual caller executes the generated core; explicit lengths and handle ownership, with source inspection and comparisons. | Universal marshaling proof and final production API contracts still open; Rust compiler/linker/FFI assumptions explicit. |
| Measurements | Exact fixture observations and diagnostics only. | No physical constant-time or native succinct-memory theorem; no preprocessing speed claim. |
| Payload | Baseline counted allocation/program remains the intended exact object. | Arrays, limb rounding, headers, runtime objects and native allocation overhead are not counted by the baseline payload theorem. |

Pins inspected locally: Lean 4.22.0 commit
ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05 (Windows GNU),
bundled Clang 19.1.2, Rust 1.89.0 commit
29483883eed69d5fb4db01964cdf2af4d86e9cb2 (Windows MSVC).
The DLL C boundary avoids linking GNU static runtime objects into Rust.
No other proof toolchain is requested by this route proposal.

## Review disposition requested

Review the actual route, the raw-versus-checked fault split and the proposed
canonical theorem before the next dependent native interface phase. The
required contract review and repair responses are in CONTRACT_AUDIT.md.
This phase cannot be called CANDIDATE_COMPLETE: all seven assigned full native
rows and all inherited execution joins remain open. Final blind exact-commit
audit and coordinator acceptance belong after those rows close.

Submission policy result: strict design checking fails on 28 new native paths
with no classifier rule. The shared checker is outside worker scope; REPORT.md
requests coordinator disposition and does not claim a pass. The eight boundary
controls execute the real script in-process, so the stronger frozen OS
process-boundary selector check remains open with the final campaign.

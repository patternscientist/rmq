# NATIVE-1 independent contract review

Review scope: exact base/governance 0e6a00f654abc64f8b68988fa9675b9a839dca2f;
frozen matrix SHA-256 0A5D2313CCEC30DE81AAB3B19439247C612CE4B8FC6C19C0BF51F6C3809D103E.
Read-only reviewer: child task /root/contract_review, rmq-proof-auditor role.
Project preflight passed. This is contract review, not candidate acceptance or
the required fresh blind exact-commit final audit.

The reviewer found all 31 assigned/inherited/replay IDs present exactly once,
with no omitted or weakened requirement-column wording. It required a narrow
specification pass before route-dependent implementation and explicitly allowed
the early actual-toolchain experiment to continue.

## Findings retained from the independent review

1. P1: the planned safety/support guard did not settle corrupt-input semantics.
   Raw Primitive.execute does not fault on arithmetic overflow, zero divisor or
   invalid shift; missing instruction fetch leaves the status unchanged, while
   missing memory emits a failed receipt and faults. Canonical simulation and
   native checked rejection need separate propositions, with mathematical
   representability distinct from finite-host support.
2. P2: the planned source-entry statement needed exact arguments, observations,
   exported declaration/symbol, trace-erasure projection, build identity and
   marshaling boundary. Source-entry equality to a sibling finite interpreter
   alone does not independently anchor PQ1. Mutation controls should distinguish
   changed core, stale artifacts, wrong symbol and swapped/truncated arguments.
3. P2: explicitly retain coordinator-scheduled aggregate ownership and report
   requirements: REPORT.md, exact status/phase/unmet rows, proof digestion,
   byte length and SHA-256.

## Producer response and scope

The requirement column is unchanged. The current natural-cell container leaf
preserves raw PQ1 behavior for arbitrary memory, status and fuel when every
destination fits the bank. It introduces no new arithmetic fault policy. Its
missing-load and missing-fetch behavior remains exactly the original behavior.
The future checked limb layer will define checked rejection separately and must
prove compatibility on all canonical representable executions by consuming
queryRun_execution_safe. No corrupt-state fault equality is claimed prematurely.

runThin_reference and routeCore_reference state final decoded state
and accumulated observation equality directly against PackedWordRAM.run, at
the identical memory.toList, program.toList, fuel and decoded initial state.
The route experiment exports the same declaration that calls this core. Its
text parsing and C/Rust marshaling are measured/source-inspected boundaries;
canonical binary-image marshaling remains open. ROUTE_EVIDENCE.md records exact
checked types and pending canonical signatures separately.

Final aggregate certification belongs to a coordinator-scheduled host slot.
This route phase requests review only; it requests no full gate and records no
acceptance. The durable WORKER_REPORT is REPORT.md, beginning with INCOMPLETE
and the exact phase. Its final task response reports actual bytes and SHA-256.
The implementation's final exact-commit blind audit remains required after all
frozen rows close. No requirement is narrowed by this response.

The reviewer ran source inspection and both trust-token scans, with no matches;
it ran no Lean build or mutation. Its evidence is an independent contract review,
not a new theorem. Its skeptical question is: if a divisor is corrupted or the
next instruction is absent, which function rejects and which observations does
the theorem preserve?

## Read-only route repair review

The independent continuation found six concrete defects: wrong endpoint
register order; post-build-only source pins; deletable manifest entries;
mutation failures accepted at any type mismatch; dropped timeout diagnostics;
and a parser that accepted out-of-bank destinations. All six were repaired.
The reviewer inspected the repairs and found no remaining concrete source
blocker in that focused scope. It did not run builds or certify ROUTE_READY.
Subsequent owned builds, exact-type checks, 14/14 host native cases, 8/8 boundary
controls and C++ complete-path output supplied the missing executable evidence.
The raw source body needed a routine explicit Registers.write elaboration fix
after the read-only review; it then checked in the final source build.

The revised explicit-length/owned-Lean-string C bridge was included in that
repair review. The reviewer found no concrete ownership or signature mismatch,
while leaving generated ABI and executable confirmation to the build owner.
Final whole-native blind exact-commit audit is still pending; this review is
not coordinator acceptance and does not close any full native row.

## Exact-commit continuation packet review

The independent reviewer inspected implementation/evidence commit
3329a6e90cf70bc10b3cb68b008f8a23264ce567 against exact governance/base
0e6a00f654abc64f8b68988fa9675b9a839dca2f. This was a read-only continuation
phase review, not a fresh blind final-capstone audit. It ran no builds, native
execution or broad scans and made no edits.

It found no new mathematical, object-composition or native-ABI overclaim.
Independent receipt comparison verified all 15 source and both native artifact
pins, exactly 14 expected/executed route cases, each saved fixture's full output
against its reference, the complete C++ n9-full output, and the source mutation's
precise routeCore_source proof-line diagnostic. Canonical instantiation, limbs,
binary loading, final marshaling and the capstone remained explicitly open.

Two reporting requirements remain material. First, design-phase.json records
exit 1 without timeout because 28 new native paths lack a shared classification
rule. This requires coordinator-owned disposition and is not a passed gate or
proof failure. Second, packed_native_controls.ps1 invokes the actual script
within its current process; 8/8 covers script parameter binding rather than
independent OS command-line serialization. The stronger frozen replay boundary
remains open. REPORT.md and the appended evidence corrections state both.

The review considered INCOMPLETE / ROUTE_READY accurate with those disclosures.
This finding does not grant coordinator route approval, full acceptance, or
permission to bypass the required dependent-interface review.

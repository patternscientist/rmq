Status: INCOMPLETE
Phase: APPROVED_ROUTE_IMPLEMENTATION

# NATIVE-1 continuation contract and work record

Reviewed start: c8c266f987d46284382cc93c5fa8e01bd7a9ffb9, clean on
codex/native-1-packed-execution. Exact original source/governance remains
0e6a00f654abc64f8b68988fa9675b9a839dca2f. Returning skill preflight PASS with
required rmq-proof-sprint and actual runtime rmq-audit-prompt, rmq-coordinator,
rmq-proof-sprint. No branch or cache reset.

Coordinator disposition: APPROVE_LEAN_C_ROUTE_AND_CONTINUE_WITH_REPAIRS.
The full 31-row matrix and original 28,298-byte prefix remain frozen. No full
row is waived, no capstone accepted, and no integration authorized. Routine
work within the approved route needs no further ROUTE_READY pause.

## Verbatim additional repair requirements

WDD-NATIVE1-PATH-ROLE: The coordinator confirms the reported 28-path failure. Your previously scoped native package needs explicit categories. Ownership now additionally includes scripts/design_decision_check.ps1 and scripts/design_decision_check_regression.ps1, solely for this native-package classification and regression. Use C:/Users/poin/Documents/RMQ/extension-coordination-20260911/NATIVE1_POLICY_REVIEW.md as the reviewed category/test contract. The existing 28-path split is 26 DD (native source/ABI, Cargo, public README, operational fixture/program bytes) and 2 WDD (route-registry.json and fixtures/manifest.json). Package-root build.rs, if introduced, needs both. Preserve existing script/Lean composition and neutral .gitignore/.gitattributes; code identity outranks evidence-like naming.

WDD-NATIVE1-REGISTRY-KIND: Fix the production registry's unpinned operation fields before relying on mutation certification. Coordinator independently reproduced, with the unchanged candidate runner and identical source/artifact pins in an isolated replica, changing only source-core-mutation.kind from source-mutation to source-pin. The real script exits 0, reports PASS source-core-mutation, and its evidence says stale-source rejected: no correspondence theorem was checked. The correctly named stale-source-rejection also passes with the untouched registry. Exact receipts: C:/Users/poin/Documents/RMQ/extension-coordination-20260911/native1-route-review/registry-kind-downgrade.json and registry-source-pin-positive.json. This is a measured dependency-coverage failure, not a theorem counterexample.

Pin the complete semantic case contract before dispatch: ID, kind, required fixture/mode and expected operation/result fields. Reject changed or missing load-bearing fields and undeclared variants. Preserve explicit versioning for intentional registry evolution. Add production-boundary controls for the measured same-ID/source-pin downgrade and the source review's same-ID/ordinary-fixture substitution; retain positive original-source-mutation and correctly named source-pin controls. The frozen selector/registry/non-vacuity rows already require this repair; no acceptance row is rewritten.

WDD-NATIVE1-TOOLCHAIN-CACHE: The inspected build cache keys omit compiler/toolchain identity, while -LeanRoot can change and old generated C can be reused. This is source-derived provenance risk; the coordinator has not run a different compiler and does not assert the current binary is mismatched. Enforce the repository Lean pin, record actual compiler/runtime/imported toolchain identity, include that identity in generated-module cache keys and invalidate reuse on a mismatch. Record actual Rust/C toolchains and include C++ source/artifact identity in the final certified consumer inventory. Test the actual production cache/identity predicate with unchanged-identity positive and changed-identity rejection/rebuild controls. General verified compilation is not newly required.

DD-NATIVE1-CPP-ERROR: The current examples/route.cpp prints any non-null result and returns 0 even for ERROR-prefixed parser rejection; Rust main returns a failure. Repair the example's error/status propagation with correct lifetime release and a malformed-input case. Prefer an explicit error/status channel in the final ABI. This was verified by source inspection; no negative C++ runtime replay is claimed yet.

## Concrete consumers and verification plan

| ID / owner | Producer and required consumer | Rejection/control and planned evidence |
| --- | --- | --- |
| PATH-ROLE / native_policy | Production Get-PathDisposition and existing production Git regression; strict per-commit native history. | Exact 26 DD/2 WDD roles, held-out source categories, missing-ledger controls, both-ledger build.rs, neutral plumbing and unknown neighbors; preserve all historical records. Freeze then full policy regression. |
| REGISTRY-KIND / registry_repair | Versioned semantic registry consumed before native dispatch. | Original source-mutation/source-pin positive; same-ID kind downgrade/fixture substitution and required-field deletion rejection; real child-process selector boundary; exact case roster and restoration. |
| TOOLCHAIN-CACHE / lead | Enforced repository Lean pin plus actual compiler/import/runtime byte identity enters every generated-module cache key and final build manifest. | Real production identity/cache predicate accepts unchanged identity and rejects/rebuilds changed identity; actual Rust/C/C++ pins; before/after input integrity. No claim a different compiler was previously executed. |
| CPP-ERROR / lead | Same C ABI consumer releases its owned result and propagates parser rejection. | Successful complete-path match and malformed-input nonzero exit through actual DLL; include C++ source and artifact in certified inventory. |
| LIMB-WORD / limb_words | Array UInt8 little-endian limbs, exact encoding, checked arithmetic/comparison/address operations, consumed by finite-limb step/run. | All-width roundtrip, canonical padding and size, all operation clauses and explicit rejected faults; no cached Nat field. |
| CANONICAL / lead | Exact buildMemory/queryProgram/initialState source theorem, with existing Run.steps/reads/category projections. | Checked expected-type consumer on those identical objects; then same loaded-byte limb runner in nativeExecutionCapstone_holds. |

The lead owns the join, native ABI, binary loading and final acceptance evidence.
Agents own disjoint leaves. One scoped Lean process at a time; the limb worker
initially owns that slot while independent script/policy work proceeds. No
native full replay during unstable source/manifest edits. Source changes trigger
the narrow changed modules, bounded startup and known selector before broader
native validation. The host aggregate slot is requested only on frozen final
content. Optional report delivery cannot block independent implementation.

All new implementation still feeds the original full finite-limb/binary/native
capstone contract. Helpers and these repair tests do not replace that target.

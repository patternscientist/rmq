# OPT-1 compact-static leaf contract

Frozen before edits, 2026-09-12. Parent matrix and adopted contract audit are
`../ACCEPTANCE_MATRIX.md` and `../CONTRACT_AUDIT.md`. Governance/base remains
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`, checkout is
`1f3a4199eaa95324cd1daaadbab89340ca8392c4` plus disjoint uncommitted lane work,
branch `codex/opt-1-packed-compiler`, worktree
`C:/Users/poin/.codex/worktrees/1580/RMQ`. The same agent already passed the
canonical exact-ref preflight and read rmq-proof-sprint/AGENTS/completion gate;
this is its next explicitly assigned independent leaf, not a fresh task.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| STATIC-WRITES | Prove actual emitted finite-register writes and constructor-complete encoded field fit, including loop COUNT constants (old Block.FieldsFit ignores counts). | Local generic emitted code | Every literal emitted instruction destination lies in the stated bank; every literal encoding operand fits the declared capacity. | compactAt -> static facts -> root complete compact capstone. | Fresh destination and oversized count controls. | Pending. | Open |
| STATIC-FRAME | Desired frame: if BlockRegistersBelow fresh block, all emitted instruction writes r<fresh+2*(depth+compactDepth block), hence for every fuel regs outside bank stay unchanged using run_frame. | Generic full execution frame | Every memory, state and fuel, outside-bank r retains entry register value. | actual compactAt program -> baseline run_frame -> complete scratch accounting. | Arbitrary starting PC/fuel, early stop and failed loads must remain covered. | Pending. | Open |
| STATIC-FIELDS | Encoded fit must include all source fields, dormant PC/register/control tags/counts and end boundary with explicit width/base/depth/fresh/max-repeat guards. Do not pretend width from maxDestination alone. | Generic all-emitted-instruction static fit | Source FieldsFit, explicit maximum count, control tag, register-bank and end-PC guards imply Instruction.Fits for every emitted instruction. | Every dormant actual instruction encoding -> root execution and space capstone. | Count guard absent from old fields; tag, counter and target boundaries. | Pending. | Open |
| STATIC-ENCODING | Expose generic source fixed-immediate/IDs bound as needed, exact encoding-length recurrence if useful; whole-query literal size/depth can remain root capstone. | Supporting exact accounting | Exact flattened literal encoding length from actual emitter, including all five wrapper instructions. | compactAt encoding -> root code words -> complete residual. | Positive loops add all wrapper words; count zero emits none. | Pending. | Open |
| STATIC-CHECK | No Lean/Lake now: root owns sole sequential cold capstone build. Draft proofs then request slot. | Verification | Root releases build slot before narrow check with exact pinned Lean -j1 and task-local artifacts. | This module and direct typed consumers. | No competing heavy build. | No Lean run. | Open |

Owned source is ONLY `RMQ/Core/WordRAM/Optimization/CompactStatic.lean`; owned
evidence is ONLY this directory. Root owns emitter and semantics, shared
ledgers and commits. Adopted audit obligations include count literals and
whole-state fit separate from low-register agreement. This static leaf does
not prove execution correctness or arithmetic safety; those parent obligations
remain open. All source/count inventory covers both branches; this is
conservative syntactic coverage, not an exact live-instruction manifest.

Verification plan: after exclusive ownership, narrow module and pinned type/
axiom check with 300-second per-process deadlines and existing owned-process
tooling. Add concrete exact-boundary controls. Reuse checked dependency
artifacts and do not run full Lake or aggregate; parent owns final joined
certification. Record all failures, source hashes, durations and scope limits.

## Lead-authorized ownership addition after resume

At resumed HEAD `8e355fda7788077f548865c1d6acf2ae5e88da55`, the lead assigned
`RMQ/Core/WordRAM/Optimization/Query.lean` to this same leaf. Existing rows
remain unchanged; the following additional row freezes the expanded target.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| STATIC-QUERY | once CompactStatic checks, repair/check Query and add exact measured program length, literal encoded-word count via compactAt_encoding_length recurrence, numeric compact query bound, fixed bank/scratch, and strict code reduction facts. Root owns QueryProof/QuerySafety/Capstone and needs these concrete facts. Keep current object definitions/route/observation unchanged; notify signatures. | Fixed query static producer | Kernel-checked numeric equalities plus independent literal emitted-list/encoding measurements; source-bound, fields-fit and finite-bank consumers on same compactQueryProgram. | CompactStatic -> Query -> root QueryProof/QuerySafety/Capstone. | Compare actual emitted length/encoding count with recurrence; no estimate substituted for code. | Pending. | Open |

No Lean/Lake may start before explicit build-slot transfer. The previous
preflight was rerun and passed on that exact resumed checkout using the actual
runtime catalog. The completion gate was reread. The query object definitions,
allocation, fresh-register origin, compiler route and observation relation
remain fixed. No numeric constant is guessed before the bounded measurements.

## Final local evidence, 2026-09-12

The frozen requirements and original pre-edit evidence cells above are
unchanged. All six local rows now have kernel-checked producer/consumer
evidence recorded in REPORT.md. Final literal query measurements match the
checked numeric equalities: 212964 instructions, 722339 encoded words,
151978 recurrence budget, depth 1, maximum count 33, bank 8273 and scratch
8276. The lead's semantic/safety/certificate composition and final acceptance
remain open; this leaf does not mark full OPT-1 complete. The build slot was
released explicitly after final checks. See REPORT.md and the timestamped
JSON artifacts for exact types, hashes, controls, diagnostics and scope.

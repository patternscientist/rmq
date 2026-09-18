# OPT-1 source-relations leaf contract

Frozen before proof edits. Parent matrix: `../ACCEPTANCE_MATRIX.md` at
`1f3a4199eaa95324cd1daaadbab89340ca8392c4`; governance/base:
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Worktree:
`C:/Users/poin/.codex/worktrees/1580/RMQ`; branch: `codex/opt-1-packed-compiler`.
Owned source: `RMQ/Core/WordRAM/Optimization/SourceRelations.lean` only.

Preflight command passed with required `rmq-proof-sprint` and actual runtime
catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; canonical skill,
AGENTS, completion gate, parent matrix and route proposal read. No shared
Packed file or ledger changes are authorized for this leaf.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REL-AGREEMENT | define Data agreement below N (same status, regs equal for all r<N), complete source-register boundedness (ALL action dst/src/address/lhs/rhs, branch and exit regs; constants values irrelevant to register bound). | Generic source leaf for REQ-OPT-COMPILE/RUN | Constructor-complete recursive predicates; no immediate-value guard. | Parent compact simulation uses fresh>N register writes. | Omitted address/branch/exit operand would invalidate source congruence. | Pending. | Open |
| REL-EVAL | Prove Block.eval congruence under register agreement when all source regs below N: equal status, registers below N, exact ordered receipt equality. | Generic source leaf | For every memory, N, block and states a,b, bounded block and agreement imply agreement of evaluated finals and equality of actual evaluator receipt lists. | Source congruence -> compact source/machine simulation -> parent capstone. | Both branches, failed loads, early exits, nested sequence and arbitrary finite repeats. | Pending. | Open |
| REL-FRAME | Also prove frame for source evaluation outside declared source register bound, preferably reuse Packed.Frame/Scratch. | Generic source leaf | For every r>=N, bounded block preserves register r under every memory/state. | Parent body execution preserves enclosing loop counters. | Destination collision at N; guard must reject it. | Pending. | Open |
| REL-SAFE | If tractable prove Block.Safe transport under two fitting Data states with matching registers below N (all action runtime operands agree) using Packed.Safety; source congruence exact signature is primary. | Optional generic source leaf | Same memory/width/block; Safe a, Fits b and register/status agreement imply Safe b. | Parent compact per-instruction safety proof. | Read reply, subtraction, zero divisor and shifts preserved through all intermediate states. | Pending. | Open |
| REL-CHECK | DO NOT run Lean/Lake yet: bound_proof owns sole build process; ask root for ownership when draft ready. | Verification | Root permission before direct narrow Lean check; exact types and axiom inventory. | This source module only. | No competing build process. | No Lean run yet. | Open |

Inherited scope: this is explicitly a proof-independent generic leaf. It adds
no emitted program, counted allocation, width convention, machine run, replay,
or public capstone. The parent's frozen inherited rows remain unchanged/open.
Locally applicable semantic non-vacuity, trace-execution and proof-separation
are supplied by exact equality of the existing evaluator's receipt lists and
constructor induction; the relation has no proof-carried computational data.
Whole-machine backing, safety, code accounting and downstream consumption
remain the parent join's obligations, not silently discharged by this helper.

Verification plan: after build ownership is granted, compile only this module
against existing dependencies using the pinned direct toolchain and task-local
output, bounded by a five-minute first-check deadline. Then check pinned exact
types, axiom inventory and scope hygiene. Full Lake/aggregate is skipped for
this leaf because the parent owns final integrated checks. No mutations or
replay campaign are claimed by this leaf.

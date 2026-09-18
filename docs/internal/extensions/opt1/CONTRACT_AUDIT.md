# OPT-1 independent contract-route audit

Auditor: independent `rmq-proof-auditor` subagent `contract_audit`, fresh context.
Persisted by the lead from its returned report because the auditor role is
read-only. No source implementation or worker completion narrative was supplied.
Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Exact target: `1f3a4199eaa95324cd1daaadbab89340ca8392c4`.
Scope: frozen matrix and CONTRACT_ROUTE plus their baseline Packed interfaces.
Uncommitted proof work was explicitly excluded.

Verdict: the counted-loop route is suitable, with two narrow proof-interface
clarifications required before its safety proof is fixed. No counterexample
to either recurrence or unjustified PRE gate bypass was found. This is route
review, not OPT-1 completion or coordinator acceptance. The exact audited
commit changes four Markdown files and no Lean, toolchain or Lake source.

## Findings

### P2: explicitly rebase source comparison state at loop-body entry

The proposed depth-d relation protects registers below fresh+2*d; body
induction at d+1 protects c and u as well. Initializing these registers changes
them only in the machine, so the unchanged original source state does not
satisfy the deeper relation. Concrete counterexample to that intermediate
premise: all-zero source registers, `.repeat 1 .skip`; the first body entry has
machine c=u=1 while source c=u=0.

Correction: apply the body theorem to a comparison state carrying the current
machine scratch values. Maintain low source-register/status agreement,
c=remaining, u=1 and preserved ancestor counters. Use source congruence and
the existing source frame theorem to recover the original iteration and exact
ordered receipts. This is an induction-interface defect, not an emitter
counterexample. Relevant surfaces: Structured.Block.eval and Frame.lean's
Block.eval_frame, including stopped/faulted/conditional/repeated evaluations.

### P2: finite register agreement does not establish global word safety

Data.Fits and State.Fits quantify over every register. At width 4 and fresh=2,
a machine with value 16 in register 2 agrees below 2 with an all-zero source,
yet fails State.Fits already at prefix zero, even for skip.

Correction: safe realization needs actual entry-state fit, actual final-state
fit and TraceSafe in addition to semantic agreement. Maintain fitted counters,
ancestor scratch and untouched registers independently. Source action operands
can use congruence; global fit cannot. Then run_prefix_fits supplies all fuel
prefixes. Repeat count literals need separate width premises because the old
FieldsFit/maxEncodedField erase repeat counts. Canonical initialState and
buildMemory can discharge the query-level premises.

### P3: state the starting PC premise explicitly

HostedAt constrains a program slice, not the starting state. The general
hosted-segment theorem needs `hpc : s.pc = base`, as in the baseline compiler.

## Positive reconstruction and limits

The branch maximum matches the emitted branch/nonzero/jump/zero layout. An
actual RunsTo witness, terminal step=None and run_add support full equality
at any adequate fuels; a small-fuel truncation bound does not. The positive
loop wrapper adds five instructions and costs at most
3+count*(bodyCost+3); count zero emits no code. Missing loads log failed attempts
before faulting, so exact ordered receipts remain the right relation. Generic
run_read_at supplies compact occurrence backing and run_frame supplies finite
register accounting. Actual compact encoding and finite scratch constants can
instantiate the existing same-allocation residual theorem.

The PRE C1-C4 gate in RMQ_PROGRAM_PLAN.md C.3 explicitly precedes builder
construction. OPT-1 retains buildMemory and changes query compilation; this
scope distinction neither satisfies nor waives PRE's gate.

These are source-grounded model and process findings. No new kernel proof,
emitted program, concrete compact size, depth, scratch count or 150739 equation
was verified by this audit. All implementation rows remain open at its target.

## Row-by-row disposition

| Frozen ID | Route disposition; exact-target implementation disposition |
| --- | --- |
| REQ-OPT-BUDGET | Recurrence/fuel bridge supported; PC premise required; execution theorem and concrete equation absent. |
| REQ-OPT-COMPILE | Five-instruction route viable with rebasing; actual emission/simulation/reduction absent. |
| REQ-OPT-RUN | Ordered attempts retained; global safe realization required; composed theorem absent. |
| REQ-OPT-SPACE | Fixed actual code/scratch residual viable; encoding, bank and prefix frame absent. |
| REQ-OPT-CONSUMER | Same-object inhabited capstone required; capstone/consumers absent. |
| CHK-OPT-CONTROLS | Principal cases covered in plan; add both finding counterexamples; optimized registry absent. |
| REPLAY-EXACT-REGISTRY | Exact nonempty registry retained; implementation absent. |
| REPLAY-SELECTOR-NONVACUITY | Real parameter-boundary requirement retained; implementation absent. |
| REPLAY-SUBPROCESS-DEADLINE | Existing ownership tooling appropriate; optimized restoration evidence absent. |
| CHK-OPT-DEVELOPMENT | Narrow build/direct-consumer plan appropriate; no new Lean at target. |
| CHK-OPT-FINAL | Explicit new imports required; candidate checks pending. |
| CHK-OPT-TRUST | Baseline scans clean; new declaration inventories pending. |
| CHK-OPT-CONDITIONAL | Public/compatibility checks appropriately conditional; candidate pending. |
| CHK-OPT-AUDIT | Route review supplied here; final exact-commit audit/aggregate pending. |
| INV-STORE-IDENTITY | Proposed construction consistently buildMemory xs; joined proof absent. |
| INV-VALUE-DEPENDENCY | Source scalar evaluation/read refinement viable; compact chain absent. |
| INV-SEMANTIC-NONVACUITY | Actual RunsTo required; compact realization absent. |
| INV-TRACE-EXECUTION | Primitive transitions retained in plan; compact execution pending. |
| INV-STORE-AGREEMENT | Generic dynamic agreement applicable; compact exact consumer absent. |
| INV-READ-BACKING | run_read_at supplies position/instruction/pre-state/lookup; compact consumer absent. |
| INV-WORD-WIDTH | Explicit whole-state fit required; finite relation insufficient; proof absent. |
| INV-ADDRESS-WIDTH | Dormant fields, counts/targets/registers/tags planned; exhaustive proof absent. |
| INV-INSTRUCTION-ATOMICITY | Existing ISA preserved; actual compact emission pending. |
| INV-PROGRAM-ACCOUNTING | No input-specialized compiler inputs proposed; actual code accounting absent. |
| INV-ORACLE-INDEPENDENCE | Source/reference oracle suitable; executable expectations absent. |
| INV-VALIDATION-REACH | New actual code must execute in validator; validator absent. |
| INV-ALL-SIZE | Representable endpoint guards/no readiness retained; compact theorem absent. |
| INV-PROOF-SEPARATION | No answer/proof runtime inputs proposed; implementation inspection pending. |
| INV-NO-SYNTHETIC | Actual primitive loads can establish it; compact chain absent. |
| INV-CATEGORY-SEPARATION | Categories kept distinct in proposal; joined evidence pending. |
| INV-PUBLIC-COMPOSITION | Same construction/guards required; capstone type absent. |
| INV-CERTIFICATE-ANTI-BYPASS | Independently pinned consumers required; consumers/mutations absent. |
| INV-MUTATION-REPRODUCIBILITY | Versioned runner/exact failures/restoration required; campaign absent. |
| INV-GLOBAL-PHYSICAL-MACHINE | One common primitive memory retained; whole-query join absent. |
| INV-WIDTH-SCALING | Existing logarithmic width viable; actual all-field/state/address proof absent. |

## Rejected objections and verification

Full compact/original machine-state equality is unnecessary because PCs,
transitions and counted scratch differ; result/status and ordered attempts
must agree. A trailing reset would be bypassed by early stops and is not a
substitute for frames. Arbitrary-memory simulation does not imply arbitrary-
memory fit or halting. Some tiny blocks can grow while the full query shrinks.
No static estimate or unchanged baseline capstone discharges compact rows.

Auditor reports preflight PASS, exact source/configuration comparison unchanged,
exact-range and working-tree diff checks PASS, exact-commit and working-tree
trust/native-decision scans with no matches. No Lean/Lake, executable campaign
or aggregate was run, as required for this read-only review. These command
summaries are audit process evidence, not candidate certification.

Proof digestion: the proposal separates executed-path cost from layout and
reuses loop bodies through charged backward branches. Its intended machine
performs the same attempted reads and returns the same answer in smaller fixed
code. The skeptical next question is whether nested-body induction preserves
parent counters and every register's width after the first fault or halt,
without assuming those properties as unproved capstone premises.

## Lead disposition after independent review

All three findings are adopted as implementation obligations without changing
any frozen row. Pin hpc explicitly. Rebase loop-body source comparisons using
machine data and use protected-register congruence to relate back to the
original iteration. Safe realization carries actual entry/final fit and
TraceSafe; low-register equality transports only observed operands and source
behavior. The five-instruction route is selected for implementation subject
to these requirements. No coordinator acceptance is recorded.

# PRE-1 frozen acceptance matrix

Frozen before any proof or construction edit, 2026-09-12. Handle PRE-1; title
`(PRE-1) Prove efficient packed preprocessing`; worktree
`C:/Users/poin/.codex/worktrees/2fb8/RMQ`; branch
`codex/pre-1-packed-preprocessing`; source/governance base
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.

This uses `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`. The verbatim
requirements below are immutable. Evidence, status and approved appended
amendments may evolve. This first phase prepares C1-C4 for independent audit;
it does not close the builder. No builder construction may begin before the
coordinator returns a passing independent contract audit.

## Verbatim assigned requirements

### REQ-PRE-CONTRACT

Before writing any builder construction, append a current contract and amendment ledger reconciling plan C1-C4 with PQ1. Freeze O-UNIF, O-WORKCAP, O-FIREWALL, O-CONTROL, and the O-POINTWISE input-length header clause. Audit the entire 15-case wf3_attack.json catalogue against named obligations. Old program-bit information-gap and getBit/setBit clauses may not be copied blindly: all-size n=0 and PQ1 fixed code require an explicit justified amendment preserving the anti-oracle intent. Submit exact contract commit, typed consumers, negative controls, 15-case table and required gate evidence as CONTRACT_READY. The coordinator commissions a fresh blind exact-commit audit before authorizing any builder construction. This phase boundary is a required prerequisite, not an alternate final endpoint.

### REQ-PRE-INPUT

For arbitrary List Int, prove the exact builder and linear work under an explicitly named unit-cost comparison-oracle model. Separately prove a signed fixed-width input encoding with the length read from a pinned header cell, pointwise element cells, order refinement, representability of every operand and a satisfiable all-size family. The word-machine corollary must state its finite-key premise. Do not assume free sorting or rank conversion; input storage, reads and comparisons have explicit units.

### REQ-PRE-MACHINE

Define a uniform finite construction program independent of xs, on a conservative mutable extension of the primitive model (the existing ISA has no store). Charge each read, write, arithmetic/comparison, branch, loop and allocation/initialization operation. Isolate interpreter semantics from RMQ imports and host List operations. Prove the reflected work bound against that interpreter, not a claimed tick total. Input-dependent tables/constants are counted data. No baked per-shape program, inherited semantic answer or macroinstruction may supply output.

### REQ-PRE-EXACT

Build the full pipeline: linear monotone-stack Cartesian construction with leftmost ties; linear shape serialization; one-pass rank/select directory builders; all five wrappers/eight encoded tables; metadata, dense repacking and padding. Prove exact ordered output equality with RMQ.SuccinctFinal.PackedWordRAM.buildMemory xs, including 174 metadata words. Pure semantic builders may be the equality specification but may not run outside the charged implementation.

### REQ-PRE-COST

Prove explicit all-size constants C,D with executed work <= C*n+D, and explicit peak temporary workspace <= Cw*n+Dw words, with all mutable storage, input retention, program and final allocation separately accounted. Prove all word/address/value bounds and live-memory ownership. Temporary O(n) words is the approved target; n+o(n) additional temporary bits is not required. Counting output size alone is not work analysis.

### REQ-PRE-JOIN

One capstone must quantify the same xs, emitted cells, width, builder execution and subsequent PQ1 query. Establish retained 2n+o(n) bits, exact leftmost half-open answers and explicit invalid handling, linear preprocessing in its stated input model, and constant fully charged queries. State the arbitrary-Int and finite-key corollaries separately.

### CHK-PRE-CONTROLS

Persist controls for increasing, decreasing and equal inputs, empty/singleton, threshold boundaries, repeated-prefix/quadratic mutations, mismatched emitted allocation, hidden semantic builder calls, write-unit confusion, missing input header and table/program payload bypass. The production builder, not a copied model, must be reached by executable validation.

### REPLAY-EXACT-REGISTRY

any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

### REPLAY-SELECTOR-NONVACUITY

omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

### REPLAY-SUBPROCESS-DEADLINE

run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.

## Requirement-to-evidence rows

The exact-requirement column points to the immutable verbatim section of this
file, rather than duplicating and risking divergent wording. All construction
rows remain OPEN until their complete statements are checked on the eventual
candidate. C1-C4 author evidence never changes that status by implication.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-PRE-CONTRACT | Verbatim section above | Contract prerequisite | C1-C4 typed contract, 15-case dispositions, author and scheduled aggregate gates, exact-commit blind audit | Contract -> coordinator audit -> builder authorization | Oracle instruction, baked code, omitted header; pending | Preflight PASS; initial clean HEAD equals base | OPEN: author phase |
| REQ-PRE-INPUT | Verbatim section above | Full extension | For every List Int exact comparison-model run; for every representable fixed-width input order-preserving cell encoding; all-size witnesses | Same input -> header/key reads -> builder run -> finite-key corollary | Empty, singleton, negative extremes, too-wide keys, missing header; pending | None | OPEN: builder prohibited before audit |
| REQ-PRE-MACHINE | Verbatim section above | Full extension | Closed code; exhaustive primitive reflection; actual interpreter work; conservative old-instruction simulation | Frozen primitive semantics -> run -> cost -> capstone | Copied semantic function, table macro, allocation burst; pending | None | OPEN |
| REQ-PRE-EXACT | Verbatim section above | Full extension | efficientBuild_eq_buildMemory: forall xs, efficientBuild xs = PackedWordRAM.buildMemory xs, with emitted-order proof from that same run | Input -> stack -> serialization -> directories/eight tables -> metadata/dense packing -> exact buildMemory | Partial allocation, permutation, padding slack; pending | None | OPEN |
| REQ-PRE-COST | Verbatim section above | Full extension | Literal C,D,Cw,Dw; forall xs, run.steps <= C*xs.length+D and every prefix live temporary words <= Cw*xs.length+Dw; width/ownership for same run | Charged instruction transitions -> linear time and peak workspace -> capstone | Repeated-prefix/quadratic loops, unbounded scratch, fuel padding; pending | None | OPEN |
| REQ-PRE-JOIN | Verbatim section above | Full extension | constructionAndQueryCapstone_holds in RMQ/Core/WordRAM/Construction/Capstone.lean; quantified same input/store/run/width/query, guarded answers | efficientBuild equality -> PQ1 fullyChargedPackedQueryCapstone_holds on emitted cells -> retained capacity/query result/cost | Sibling memory, invalid query, finite-key guard erased; pending | None | OPEN |
| CHK-PRE-CONTROLS | Verbatim section above | Full extension validation | Complete production-builder validation registry and mutation consumers | RMQ.Validation.Preprocessing -> actual builder/evaluator | Named input and mutation controls above; pending | None | OPEN |
| REPLAY-EXACT-REGISTRY | Verbatim section above | Every new replay | Executed IDs = selected expected IDs; registry version and exact contents pinned | Versioned registry -> production runner -> verdict | Missing, duplicate, unexpected case; pending | None | OPEN |
| REPLAY-SELECTOR-NONVACUITY | Verbatim section above | Every new replay | Omitted selects full; one exact known ID selects one; bound empty/whitespace/malformed/unknown reject before execution | Script parameter boundary -> selected exact IDs -> verdict | Real child-process parameter invocations; pending | None | OPEN |
| REPLAY-SUBPROCESS-DEADLINE | Verbatim section above | Every subprocess/mutation | Owned bounded child trees; stderr and exits retained; finally restores exact source bytes, checked hashes/tree | Existing owned_process_tree.ps1 -> task runner -> recorded result | Timeout descendant; known-failing subprocess; pending | None | OPEN |

## Verification coverage plan (frozen before implementation)

| Role | Command/surface | Rows and distinct purpose | Deadline / runtime basis | Initial disposition |
| --- | --- | --- | --- | --- |
| Startup | project_skill_preflight.ps1 exact governance, required rmq-proof-sprint, actual runtime all three RMQ skills | Governance and exact clean base | 60 s; observed 5.7 s exit 0 | PASS |
| Development | Direct Lean build/import of each owned contract module and scripts/preprocessing_contract_check.lean | REQ-PRE-CONTRACT, C1-C4 exact typed consumers | One job; isolated .lake; initial 600 s cold Std-only budget, revise only on evidence | Pending |
| Development | New contract replay startup, known selector, full exact registry, selector/process controls | REPLAY-* and contract counterexamples | 120 s per small Std-only elaboration; 600 s whole author campaign initially | Pending |
| Final-required | lake build, explicit new capstone and typed consumer imports, full validation and axiom inventory | Full REQ-PRE-* closure | Coordinator-scheduled host slot; observe cold dependency runtime before fixing bound | Pending external schedule; no concurrent heavy commands |
| Contract-required | scripts/gate.ps1 scheduled aggregate | Plan C.2b/C.3 prerequisite, before blind audit | Request host-wide slot on frozen content; coordinator supplies schedule | Pending external schedule |
| Final-required | Trust rg scan over RMQ and lakefile.toml; native_decide/Lean.ofReduceBool scan | Trust and category separation | 60 s | Pending |
| Final-required | git diff --check; after commit git diff --check 0e6a00f654abc64f8b68988fa9675b9a839dca2f..HEAD | Working and committed byte hygiene | 60 s | Pending |
| Final-required | scripts/design_decision_check.ps1 -Strict -Base 0e6a00f654abc64f8b68988fa9675b9a839dca2f | Task-scoped design/process entries in each relevant commit | 120 s | Pending |
| Conditional | scripts/claim_drift_scan.ps1 -Strict | Family/digestion or other current public prose change | 120 s | Pending if applicable |

Every outcome will record the exact tree/content identity, command, Windows
platform, duration, exit, deadline, output file and uncovered host branches.
An interrupted or timed-out gate cannot be recorded PASS.

## Explicitly deferred and still-required work

Final paper rewrite, publication-strategy update and combined campaign
integration are coordinator work after independent acceptance. Native backend,
optimal redundancy tradeoffs and compressed temporary workspace are separate.
No step necessary for the assigned efficient construction theorem is deferred
by these exclusions. The mandatory audit phase boundary authorizes a report
with Status: INCOMPLETE and Phase: CONTRACT_READY, never CANDIDATE_COMPLETE.

## Verbatim inherited invariants and evidence rows

All these invariants apply to the composed execution consumer. Contract-only
lemmas supply prerequisites but do not close execution claims.

### INV-STORE-IDENTITY

the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-STORE-IDENTITY | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-VALUE-DEPENDENCY

returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-VALUE-DEPENDENCY | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-SEMANTIC-NONVACUITY

semantic coverage, liveness, ownership, and
  refinement predicates are derived from the operational construction they
  describe. A predicate defined to be `True`, an enumeration restated as
  membership, or a separately hand-written consumer label does not establish
  operational liveness by itself;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-SEMANTIC-NONVACUITY | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-TRACE-EXECUTION

traces and footprints are derived from the execution
  they describe;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-TRACE-EXECUTION | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-STORE-AGREEMENT

supplied-store agreement determines result, cost, and
  the relevant trace;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-STORE-AGREEMENT | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-READ-BACKING

every successful read is backed positionally by the
  counted store;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-READ-BACKING | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-WORD-WIDTH

stored and returned words fit one declared modeled
  machine word;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-WORD-WIDTH | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-ADDRESS-WIDTH

every executed address, dead/sentinel address, and
  encoded instruction operand fits the modeled machine word, not merely the
  host array bounds. Constructor-exhaustive evidence must include register
  identifiers, branch/jump targets, dormant code, and arithmetic operands;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-ADDRESS-WIDTH | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-INSTRUCTION-ATOMICITY

each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-INSTRUCTION-ATOMICITY | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-PROGRAM-ACCOUNTING

input-dependent constants and metadata carried by
  executable code are counted machine data or are derived uniformly from
  counted/public inputs. Calling shape-specialized data "program code" does
  not remove it from the payload/state accounting obligation;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-PROGRAM-ACCOUNTING | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-ORACLE-INDEPENDENCE

executable fixtures and edge-case expected values
  come from an independent specification or a theorem already connected to it,
  never from the implementation result being tested;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-ORACLE-INDEPENDENCE | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-VALIDATION-REACH

executable validation imports and runs the new
  semantic layer. A validator for the predecessor implementation is regression
  evidence only and does not validate the new machine;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-VALIDATION-REACH | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-ALL-SIZE

exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-ALL-SIZE | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-PROOF-SEPARATION

proof-only fields never carry answers or uncharged
  routing information;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-PROOF-SEPARATION | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-NO-SYNTHETIC

synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-NO-SYNTHETIC | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-CATEGORY-SEPARATION

payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-CATEGORY-SEPARATION | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-PUBLIC-COMPOSITION

a theorem combining space, exactness, cost,
  provenance, or machine claims proves them about the same construction and
  execution and over the same validity domain. Conjoining true theorems about
  different payloads or guarded and unguarded executions is not closure.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-PUBLIC-COMPOSITION | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-CERTIFICATE-ANTI-BYPASS

every mandatory field advertised by a public
  certificate is projected by a checked typed consumer at the exact proposition
  and object arguments required by the acceptance contract. Deleting or
  weakening a field, or replacing it with a sibling fact, must break that
  consumer rather than leave only constructor initializers and prose unchanged.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-CERTIFICATE-ANTI-BYPASS | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-MUTATION-REPRODUCIBILITY

when acceptance relies on an exhaustive,
  production, or public-dependency mutation campaign, the candidate contains a
  versioned runner or fixtures that replay every claimed case, check the exact
  expected failure/acceptance surface, restore tracked state, and leave the tree
  clean. Report prose, copied terminal output, and dangling Git objects are not
  replayable evidence. A public theorem additionally has a checked exact-type
  consumer that fails when the advertised dependency is removed; `#print
  axioms` over the theorem's current type is not such a consumer.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-MUTATION-REPRODUCIBILITY | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-GLOBAL-PHYSICAL-MACHINE

a physical-machine claim supplies one
  pre-execution store/word array and a checked address translation for every
  executed segment, including failed/dead accesses. A theorem for one suffix or
  component is not a whole-machine embedding.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-GLOBAL-PHYSICAL-MACHINE | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

### INV-WIDTH-SCALING

one query-independent word-width declaration bounds all
  stored words, addresses, sentinels, operands, and primitive results, and its
  capacity/width is related to input size in the form required by the public
  word-RAM claim. A standalone asymptotic fact about an unconstrained width
  function is insufficient.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| INV-WIDTH-SCALING | Verbatim paragraph above | Composed execution | Exact proposition required by this invariant, on the frozen input/program/run/store/width | efficientBuild_eq_buildMemory -> constructionAndQueryCapstone_holds | Required matching-predicate and boundary attacks pending | None at freeze | OPEN; construction follows mandatory contract audit |

## Contract-phase evidence appendix (2026-09-12)

The verbatim frozen rows above remain unchanged. This appendix supplies author
prerequisite evidence, not closure of the efficient construction rows. All
six owned modules have passed focused builds; exact final commands, hashes,
replay outcomes and the scheduled gate disposition are indexed by REPORT.md.

| Obligation | Checked proposition and live quantifiers | Actual consumer / identity chain | Counterfactual and limits |
| --- | --- | --- | --- |
| C1 / O-UNIF | Uniform program family is forall xs : List Int, family xs = program. ProgramContract separately requires program.length = instructionLiteral and programWords program = encodedWordLiteral, plus forall width, codeBits = encodedWordLiteral*width. | Independent program_uniform/program_length/program_encoding/program_accounting projections. Every xs uses one program object. | Same-length baked programs emit canonical two-node BP words 5 versus3 in constant instructions followed by store; baked_not_uniform rejects this exact Uniform predicate. Actual builder/literal pins remain construction obligations. |
| C1 / O-POINTWISE header | forall width xs, actual header load on wordInputState has regs1=xs.length and status=running; with cell0 removed status=fault. Separate comparison_header_read/comparison_missing_header_fault prove the same facts on comparisonInputState. | ContractPrerequisites.headerRead and independent headerRead/oracle_header/oracle_missing_header consumers. Zero registers obtain length through load1,0, not a supplied length register. | Missing header includes empty xs. No implied proof of one-past-end, scratch or global width. |
| O-POINTWISE / REQ-PRE-INPUT | forall width xs i, encodeInput width xs (i+1)=(xs[i]?).map(encodeInt width). SignedFits width x/y implies encodeInt width x < encodeInt width y iff x<y; every representable encoding fits2^width. forall n, InputFits(n+2)(replicate n 0). | pointwise/signed_order/signed_width/input_all_sizes exact typed consumers; actual input definitions, not sibling encoders. | Boundary keys -128,127 and rejected128 at width8; same-key replacement locality and exact cell extent. n+2 witness is input satisfiability only; logarithmic common width remains mandatory. |
| C2 / O-WORKCAP | forall i s, bstep i s=interpretPrims i.semantics s; forall i, i.semantics.length<=1; every encoded Operand is <2^32 and hence <2^width for width>=32. | ContractPrerequisites.reflection/workCap/constantCap, each projected at independently fixed full type. Prim/execPrim are the actual scalar evaluator. | Exhaustive 13 constructors, no semantic callback or table macro; primitive hash mutation and certificate weakening reject through distinct production surfaces. Future run work/loops not yet implemented. |
| C2 conservative boundary | For every old memory/instruction with Fits32, running old state s, new execPrim of translated instruction/state equals translation of old execute(memory,i,s).1. | Conservative.execute_eq_of_fits -> independent conservative_step, same memory and state; additional theorem projects regs,PC,status,memory,extent and absent key banks. | Successful/failing loads, all old arithmetic/comparison/control constructors covered. Numeric operand width and running status explicit; not a query-simulation/cost theorem. |
| C3 / O-FIREWALL | Exact finite imports for Primitive/Input/Model plus strict-UTF8 normalized byte hashes of those three roots. | preprocessing_contract_firewall.ps1 invoked by actual replay before producer and consumer stages. Controls/Contract/Conservative outside operational closure. | Disallowed semantic import and altered constant evaluator arm target production guard. Hash manifest is an audit boundary; not an automatic semantic classifier. |
| C4 / O-CONTROL | not exists ps : List Prim, ps.length<=primCap and forall s, interpretPrims ps s=oracleSemantics s. | oracle_not_reflected -> ContractPrerequisites.oracleControl -> independent oracleControl. Uses actual existing stackCartesianShape BP code on two key cells. | Universal capped numeric-register independence + valid same-length increasing/decreasing inputs; contradiction at regs0=3 vs5. Canonical BP-word exhibit, not a claimed full physical-cell computation. |
| O-WRITE / O-NOINHERIT | For s.regs address<s.extent, actual store writes some(s.regs value) at s.regs address. CleanTail s implies reserved cell at old extent is none; store/reserve preserve CleanTail. | writeValue/freshReserve exact projections; actual State.memory before/after same primitive. | Address/value and initial-clean/absence checks prevent preseeded fresh cells. Full occurrence positions and peak ownership await the builder run. |
| O-REPLAY | not Replays empty [(0,0)] (put empty1(some7)), where Replays is exact fold of actual writes over plain memory data. | fabricated_replay_rejected -> independent replay_fake. | Expresses and rejects a forged result; no claim that replay alone rules out semantic oracle computation. |
| Code accounting anti-bypass | CodeAccounting program width bits implies bits=((program.map(fun i=>i.primitive.constants)).flatten).length*width; programWords equals that expanded encoded length. | accounting_definition/encoded_length_definition spell the raw expressions independently. | Mutating CodeAccounting to True with repaired producer and programWords to0 must fail expanded consumers. Input-dependent literal/program data remain counted. |

All 21 inherited invariant rows remain applicable to the final composed
execution. The prerequisite facts above contribute evidence to them but do
not establish a builder run, full output equality, linear work, global physical
embedding or the joined public capstone. No inherited row is marked inapplicable.

## Author replay disposition (2026-09-12)

The final contract replay passed all 18 frozen cases and 28 harness self-tests
across 198 recorded subprocess stages. Every case reached its exact named
surface, and every restored producer/consumer and final hash/Git-state check
passed. The author run restored its recorded dirty baseline exactly; the
subsequent frozen commit has its own clean-state check. REPLAY_INDEX.json and
replay-full-summary.json index the committed full receipts. These results
close the author contract-replay checks only. The independent contract audit,
all builder-specific controls and all full construction/invariant rows remain
open. The required scheduled aggregate is pending at this revision.

The initial full attempt was inconclusive before mutation when its 12-second
process test did not create a recorded child before timeout. Measured shell
startup was 8.997 seconds. A focused 30-second test passed with a real child;
the unchanged runner then passed full mode with that existing parameter
override. Both the failed attempt and the corrected runs are retained. The
initial whole-campaign runtime estimate is superseded by measured serial
stage costs; per-stage bounds and all expected failure surfaces are unchanged.

## Aggregate disposition and diagnostic hold (2026-09-12)

The author-replay disposition above predates source freeze
26d6b5c2b10ed06ae4f72d9075d746ede987bdab. Its scheduled aggregate failed:
two empty-output claim-policy fixture failures were recorded, and the
14,400-second limit expired during topology-regression startup/boundary checks.
Actual bounded duration was 14,402.710 seconds, exit -1, with no output overflow.
The frozen HEAD and clean Git state were restored; all four recorded owned
process IDs were subsequently absent. The host slot was explicitly released.

Both exact claim-policy fixtures passed focused unchanged expected-rejection
checks afterward. This does not prove the original failure cause or certify
the aggregate. The restored PRE contract build/consumer passed and all eleven
protected source hashes match the complete PRE replay. REPORT.md and the
committed evidence indexes preserve each result separately. The coordinator
has placed further aggregates on diagnostic hold and prohibited builder work.

Overall status remains INCOMPLETE, prerequisite readiness is not established,
and no frozen requirement or inherited invariant row changes status. The
independent contract audit and all construction-specific obligations remain
open. No retrospective waiver or inferred acceptance is recorded here.

## Stage 0 evidence rows (CONTRACT_AMENDED, 2026-09-13)

Appended after the fresh blind contract audit PRE-1-A1
(CONTRACT_AUDIT_PASS_WITH_REQUIRED_AMENDMENTS on
`c1c970b8bfbae03163633365e512d487ae1c98f2`) and the coordinator's binding
rulings. Every verbatim section and frozen row above is unchanged: the
LF-normalized file up to the end of the preceding appendix is byte-identical to
the `c1c970b` blob, and this appendix only adds text after it. The first column
names the frozen ID a row is evidence for; it is not a new or replacement row.
Stage 0 lands amendments and operational foundations only. No builder program,
`efficientBuild`, cost constant or capstone exists at this revision, so **no
frozen row changes status: all 31 IDs remain OPEN**. Exact commands, durations
and exits are in BUILDER_STAGE_LOG.md; the report is REPORT.md.

| Evidence for | Stage 0 checked proposition or check (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after Stage 0 |
| --- | --- | --- | --- | --- |
| S0 / REQ-PRE-CONTRACT | Append-only version-2 ledger: CONTRACT.md V2-1..V2-8, AMENDMENTS.md "Version 2 entries", ATTACK_TABLE.md "Version 2 corrections" record AMEND-1..4, R1-R4, the accepted route-study clauses and rulings Q1-Q10, each quoting the superseded version-1 sentence byte-exact. The audit report and the coordinator plan are copied byte-identical (SHA-256 `2B35DD03...EA52`, `81959334...0BF8`). AMEND-4 gate reach: `scripts/gate.ps1` gains exactly two `Invoke-Checker` call sites and two roster entries (static roster count 20). | Audit finding -> version-2 clause -> checked field, guard or registry case named in the clause -> continuation audit on the Stage 0 commit | Contract registry v1 rerun in full as regression: 18/18, registry `aaec37a6...` and runner `b85ff767...` unchanged, every case at its frozen stage/line; `PRE1-CONTRACT-GATE` executed in isolation PASS (subprocess and in-process `Invoke-Checker` mimic). | OPEN until the coordinator's continuation audit; `GATE COVERAGE: 20 of 20` is a static count now and is observed only by the coordinator's next aggregate. |
| S0 / REQ-PRE-INPUT | `structure HeaderUse (program : List BInstr) : Prop` with fields `headerFirst : program[0]? = some headerInstruction`; `tailNeverWritesR1 : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i`; `wordMissingHeaderFault : ∀ width xs fuel, 1 ≤ fuel →` (run from `{ wordInputState width xs with memory := put (encodeInput width xs) 0 none }`) `final.status = .fault ∧ steps = 1 ∧ writes = [] ∧ reserves = [] ∧ final.extent = (wordInputState width xs).extent`; `comparisonMissingHeaderFault` (same five conjuncts from `{ comparisonInputState xs with memory := put (comparisonInputState xs).memory 0 none }`); `wordHeaderReceipt`/`comparisonHeaderReceipt : ∀ ... fuel, 1 ≤ fuel → ∃ t, (run program fuel s₀).transitions[0]? = some t ∧ t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧ t.after.regs 1 = xs.length ∧ t.after.status = .running`; `oracleExtentOne : ∀ xs, (comparisonInputState xs).extent = 1`. `headerUse_of_program : program[0]? = some headerInstruction → (∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i) → HeaderUse program`. | `scripts/preprocessing_builder_check.lean` lines 19-69 restate all seven fields for every `program` at full type; the actual constants `builderProgram`/`builderProgramWord` do not exist yet, so conjuncts (a)/(b) at the constants are S7/S8 obligations. | Builder registry B04-B11 weaken or delete each field: B05-B11 fail at consumer lines 22/36/54/59/64/66/66 with set-equal failing lines; B04 (weaken `headerFirst`) fails at the producer `HeaderUse.lean:62:` because the derived defaults need it; B12 comment-only control accepts; toy `[load 1 0, reserve 2, store 2 1, halt 1]` carries `HeaderUse` and its header-removed run faults after 1 step. | OPEN: exact builder, linear work, signed-encoding corollary at `wordWidth` and finite-key corollary are builder stages. Residual limit: the `headerFirst` weakening surfaces at the producer, not the consumer. |
| S0 / REQ-PRE-MACHINE | Interpreter over the frozen ISA: `fetch program s := program[s.pc]?`; `stepProgram` applies `checkedStep`; `run : List BInstr → Nat → State → Run` records every `Transition` (before, instruction, after). `Run.steps_partition : ∀ r, r.steps = Σ over the ten categories of r.categoryCount c`. Structured IR `Block` (skip, action, exit, seq, ifZero, loop) with `compileAt` and exact-cost `EvalG P`; `EvalG.compile_realizes : EvalG P b s s' k → HostedAt program base (b.compileAt base) → base + b.size < 2^32 → ∃ s'' ts, RunsTo program {s with pc := base} s'' ts ∧ ts.length = k ∧ PcAgree s'' s' ∧ (s''.status = .running → s''.pc = base + b.size) ∧ ∀ t ∈ ts, TransitionShape P base b.size t`. | Stage theorems will be `EvalG`/`SafeEval` facts transported to the frozen interpreter by `compile_realizes`; work is `ts.length`, i.e. transitions through `checkedStep`, never a counter. | Countdown loop `while r0 ≠ 0: r1 += r0; r0 -= r2`: `countdown_cost : ∀ k s, ... → ∃ s', Eval countdown s s' (4*k+1)`; array evaluator `#guard` steps 1/5/29 at k = 0/1/7 agree. No `Prim` constructor added; contract guard bytes unchanged (C18, B03). | OPEN: no builder program, no `ProgramContract` instance, no work bound yet. |
| S0 / REQ-PRE-EXACT | `emitted (s : State) (base len : Nat) : List Nat := (List.range len).map fun i => (s.memory (base + i)).getD 0`, defined in Program.lean inside the builder closure (AMEND-3's positional projection). | Future `efficientBuild xs := emitted final outBase (extent - outBase)` inside the closure -> `efficientBuild_eq_buildMemory`. | Closure imports are checked by the layered firewall (B01 import mutation rejected), so a closure module cannot name `buildMemory` or other semantic builders. | OPEN: no emitted run, no equality. |
| S0 / REQ-PRE-COST | Loop rules: `EvalG.loop_iterate` (bound `k*(J+2)+1`), `EvalG.loop_iterate_potential_cost` (bound `k*(J+2)+1+β*Φ s`), `EvalG.loop_measure'` (bound `μ s*(J+2)+1`, exit with guard register 0). Safety vocabulary (R1): `Prim.Safe W len s p := p.OperandsFit W ∧ p.SafeAt W len s` and `Run.Safe W program r := ∀ t ∈ r.transitions, Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W`. | Stage cost sums via `compile_realizes` + loop rules; safety via `SafeEval.compile_safe`. | `safety_jumpRegister_rejected : ∀ W len s src, ¬ Prim.Safe W len s (.jumpRegister src)`; `Prim.safe_not_fault`. | OPEN: literal C, D, Cw, Dw and the workspace account are S8. |
| S0 / REQ-PRE-JOIN | None proved. Ruling Q3 recorded in CONTRACT.md V2-8: provenance on `[outBase, extent)`, PQ1 capstone transported over `efficientBuild xs = buildMemory xs`, lifted Conservative simulation on the detached list; an offset-relocated in-place query execution is not required and is an explicit limit. | `constructionAndQueryCapstone_holds` (not yet written). | n/a at Stage 0. | OPEN. |
| S0 / CHK-PRE-CONTROLS | Missing-input-header control now stated on the run of any program with `HeaderUse` (fault after exactly one transition, no writes, no reservations, unchanged extent, both models, every `xs` including `[]`). | Consumer lines 23-54. | B06/B07 weaken the two fault fields and are rejected at consumer lines 36/54. | OPEN: the production-builder validation registry and the other named controls are S3-S8. |
| S0 / REPLAY-EXACT-REGISTRY | Builder registry `builder_cases.json` version 1, 13 cases B01..B13, normalized SHA-256 `fdfcbb18...` pinned in the runner beside an independent ordered ID list; full run reports executed = expected = 13. Contract registry v1: executed = expected = 18. | Registry -> `preprocessing_builder_replay.ps1` (runner `a5cf0b4a...`) -> `report.json` | 32 registry/matcher self-tests PASS under pwsh 7.6.6 and Windows PowerShell 5.1 (missing, duplicate, extra, reordered, version, hash corruptions; R2 line-set matcher fixtures). | Evidence for the Stage 0 registry; the row stays OPEN until the final builder registry. |
| S0 / REPLAY-SELECTOR-NONVACUITY | Omitted selects all 13; `B01_FIREWALL_IMPORT` selects one; bound empty, whitespace, malformed, unknown `B99_UNKNOWN`, zero, missing and duplicate reject before semantic execution. | Real child-script parameter binding (`SelectorBoundarySelfTestOnly`) | 9 child invocations PASS under pwsh 7.6.6 (inside the full run) and under Windows PowerShell 5.1 (19.4 s); focused run `-OnlyCase B06_WORD_MISSING_WEAKEN` executed exactly 1. | Evidence for Stage 0; OPEN until final registry. |
| S0 / REPLAY-SUBPROCESS-DEADLINE | Every stage is `Invoke-RMQOwnedBoundedProcess` (kill-on-close job on Windows) with exits and stderr retained; restoration in `finally` with raw byte hash, registry hash, source hashes and Git head/status/worktree/index equality. | `owned_process_tree.ps1` -> both runners -> both gate checkers | Known-failure exit and stderr preserved; owned descendant created and absent after the intended sleeper timeout (45 s builder, 12 s contract, both PASS); every case restoration EXACT in both full runs. | Windows covered; the POSIX branch was not executed on this host (inconclusive, not passed). |
| S0 / INV-STORE-IDENTITY | `emitted` is the only extraction the builder may use (Program.lean docstring; AMEND-3/V2-3). | Future `efficientBuild` -> equality -> capstone | n/a until a run exists. | OPEN. |
| S0 / INV-VALUE-DEPENDENCY | `run_write_at`: for `(run program fuel s).transitions[k]? = some t` with `t.instruction.primitive = .store address value`, `t.before = (run program k s).final ∧ t.before.status = .running ∧ program[t.before.pc]? = some t.instruction ∧ (t.before.regs address < t.before.extent → t.after.memory (t.before.regs address) = some (t.before.regs value) ∧ ... ∧ t.write? = some (t.before.regs address, t.before.regs value)) ∧ (¬ ... → t.after.status = .fault ∧ t.after.memory = t.before.memory ∧ t.write? = none)`. | Occurrence-level (index `k`, actual pre-state, fetched instruction) write provenance for later output-cell provenance. | `writes_replay : (run program fuel s).final.memory = (run program fuel s).writes.foldl (fun m e => put m e.1 (some e.2)) s.memory` pins the final memory to exactly the recorded successful stores. | OPEN: per-output-cell provenance is S8. |
| S0 / INV-SEMANTIC-NONVACUITY | `WritesOnly allowed i := ∀ d, i.primitive.destination? = some d → allowed d.val`, with `destination?` constructor-exhaustive over the 13 `Prim` arms, and `execPrim_frame` derived from the evaluator; `Prim.SafeAt` constructor-exhaustive with `jumpRegister ↦ False`. | Consumer `calc_frame`, `safety_definition`. | `safety_definition` expands `Prim.Safe` to its raw conjunction by `Iff.rfl`; no advertised predicate is `True`-valued on a load-bearing arm except the arms whose bound follows from `Fits`/operand fit (constant, move, comparison, halt, compareKey), which `Prim.safe_fits` discharges. | OPEN at run level. |
| S0 / INV-TRACE-EXECUTION | `Run.transitions` is produced only by `run` from `stepProgram`; `writes`, `reserves`, `loads`, `keyReads`, `categories` are `filterMap`/`map` projections of it. | `run_transition_spec`, `run_write_at`, `run_load_at` | `toy_run` pins steps 4, categories `[.read, .allocation, .write, .control]`, writes `[(2, 1)]` on the mathematical run; B13 drift of the pin (4 -> 5) rejected at consumer line 84. | OPEN at builder level. |
| S0 / INV-STORE-AGREEMENT | `run_agree_of_reads : State.Agree s s' → (∀ a ∈ (run program fuel s).loads, s'.memory a = s.memory a) → (∀ i ∈ (run program fuel s).keyReads, s'.keys i = s.keys i) → Run.Agree (run program fuel s) (run program fuel s')`; `run_agree_of_supplied` (coarse form under `CleanTail` on both sides, also concluding `s'.memory = s.memory`); `Run.Agree` gives equal steps, categories, writes, reserves and result. | Consumer lines 150-166. | Agreement is required only on addresses actually loaded and keys actually read by the first run, the fine form the plan requires. | OPEN at builder level. |
| S0 / INV-READ-BACKING | `run_load_at`: a running load transition at index `k` read `t.before.memory (t.before.regs address) = some v` with `t.before.regs address < t.before.extent` and wrote `v` to its destination. | Consumer lines 110-123. | A load outside the extent or of an absent cell faults (frozen `execPrim`); `Prim.SafeAt` for `load` requires both. | OPEN at builder level. |
| S0 / INV-WORD-WIDTH | `State.Fits W s := (∀ r, s.regs r < 2^W) ∧ s.pc < 2^W ∧ s.extent < 2^W ∧ (∀ a v, s.memory a = some v → v < 2^W) ∧ (∀ v, s.status = .halted v → v < 2^W)`; `Prim.safe_fits : s.Fits W → Prim.Safe W len s p → s.pc < len → len < 2^W → (execPrim p s).Fits W`. | `SafeEval.compile_safe` concludes `Run.Safe W program (run ...) ∧ s''.Fits W`. | Arithmetic results `< 2^W`, sub non-underflow, positive divisors and shift amounts `< W` are explicit `SafeAt` conjuncts. | OPEN: instantiation at `wordWidth n` is S8. |
| S0 / INV-ADDRESS-WIDTH | `Prim.OperandsFit W p := ∀ c ∈ p.constants, c.val < 2^W` with `operandsFit_of_width` for `32 ≤ W`; store/load addresses `< extent < 2^W` by `SafeAt` and `Fits`; branch/jump targets `< program length` and `program.length < 2^W` in `compile_safe`; `compile_realizes` requires `base + b.size < 2^32` (targets are `fin` operands). | `SafeEval.compile_safe`. | `jumpRegister` is unsafe by definition, so no dynamic jump address arises. | OPEN at builder level. |
| S0 / INV-INSTRUCTION-ATOMICITY | No `Prim` constructor added (contract guard bytes unchanged). `Action.prim` maps each of nine actions to exactly one `Prim`; `compileAt` emits one instruction per action, `halt` for exit, `branchZero`/`jump` for ifZero/loop; `Block.compile_length`. | `TransitionShape` conclusion of `compile_realizes` classifies every transition as one action (satisfying `P` at its own pre-state), an in-range `branchZero`/`jump`, or `halt`. | C18/B03 reject evaluator byte or import changes. | Evidence; OPEN until the builder. |
| S0 / INV-PROGRAM-ACCOUNTING | R3 placement: `Program`, `Uniform`, `programWords`, `CodeAccounting` stay in Controls.lean; the closure operates on `List BInstr` (V2-5). V2-2 fixes one literal-pinned constant per input model. | Future `ProgramContract` instances outside the closure. | The builder firewall allows no Controls import inside the closure. | OPEN: no constant, no pins, replay cases (i)/(ii) of AMEND-2 are future. |
| S0 / INV-ORACLE-INDEPENDENCE | Toy expected values (steps 4, extent 3, writes `[(2, 1)]`, reserves `[2]`, result `some 1`; countdown steps `4k+1`) were written from the primitive semantics before execution and are checked on the mathematical run by `decide` and on the array evaluator by `#guard`. | `toy_run`, `countdown_cost`, the `#guard`s. | B13 pin drift rejected. | OPEN: builder fixtures from `buildMemory xs` are S3-S8. Note for the coordinator: `toy_run` and `toy_missing_header` evaluate a four-transition toy run in the kernel, as the plan's S0 exit requires; ruling Q9's ban concerns builder machine runs. |
| S0 / INV-VALIDATION-REACH | `scripts/gate.ps1` now invokes `preprocessing_contract_gate.ps1` (`PRE1-CONTRACT-GATE`) and `preprocessing_builder_gate.ps1` (`PRE1-BUILDER-REPLAY`, full builder replay, outer 1800 s = 3.48 x measured 516.8 s). Both executed in isolation with PASS. | Aggregate gate -> checkers -> firewall/producer/consumer and builder registry. | The builder replay's producer targets (Loop, ArrayRun, HeaderUse) and consumer import the new layer. | OPEN: the executable validator `rmq_preprocessing_validate` does not exist yet; 20-of-20 coverage awaits the coordinator aggregate. |
| S0 / INV-ALL-SIZE | Every `HeaderUse` field quantifies over every `xs : List Int` (including `[]`) and every `fuel ≥ 1`; the calculus lemmas quantify over every program, fuel and state. | Consumer. | `run_missing_header` needs only `s.memory 0 = none`, true at `[]` in both models. | OPEN at builder level. |
| S0 / INV-PROOF-SEPARATION | `HeaderUse`, `Prim.Safe`, `Run.Safe`, `EvalG` are `Prop`; `Transition`/`Run` data are produced only by `run`. | n/a | No proof field carries a register value or address used by execution. | OPEN at builder level. |
| S0 / INV-NO-SYNTHETIC | `Transition.write?` records only successful stores (address and value from the transition's own pre-state); faulting stores are not write events, which keeps `writes_replay` exact. | `writes_replay`. | A fabricated write list would contradict `writes_replay` for the actual run. | OPEN at builder level. |
| S0 / INV-CATEGORY-SEPARATION | Machine state (`State`), recorded transitions (`Run`), work (`Run.steps`), safety (`Prim.Safe`), array evaluator (`ExecState`, `runArray`) and Lean runtime are distinct; `runArray_abstract` relates the executable to the mathematical run instead of identifying them. | `arrayRun_abstract`. | n/a | OPEN at builder level. |
| S0 / INV-PUBLIC-COMPOSITION | None at Stage 0. | Capstone (future). | n/a | OPEN. |
| S0 / INV-CERTIFICATE-ANTI-BYPASS | All seven `HeaderUse` fields are projected at independently written full types (consumer lines 19-66) plus `hu_of_program`; `headerUse_of_program` sets the two syntactic fields with `first | exact h | trivial` so a field weakened to `True` reaches the consumer instead of stopping at the initializer. | Consumer -> builder registry. | B05-B11 (weaken, delete, sibling) rejected at their exact consumer lines; B04 rejected at the producer; B12 accept control. | Evidence for AMEND-1's certificate; OPEN for the final certificates. Limit: B04's surface is the producer. |
| S0 / INV-MUTATION-REPRODUCIBILITY | Versioned builder runner and registry replay all 13 cases with exact stage/surface, restoration and clean-state comparison; contract runner replays its frozen 18. | `report.json` of both full runs. | Registry/selector/process self-tests inside the full runs. | Evidence for Stage 0; OPEN for the final registry. Limit (recorded in WDD-20260912-PRE1-003): a case that mutates a closure module always stops at the manifest hash surface; producer-stage semantic mutations of closure modules need a registry-driven re-hash in a later stage. |
| S0 / INV-GLOBAL-PHYSICAL-MACHINE | Ruling Q3 recorded (V2-8). No run exists. | Capstone (future). | n/a | OPEN; the relocation non-claim must reappear in Capstone.lean comments, this matrix and the final report. |
| S0 / INV-WIDTH-SCALING | One `W` in `State.Fits W`, `Prim.Safe W`, `Run.Safe W`; `SafeEval.compile_safe` needs `32 ≤ W` and `program.length < 2^W`. | Future `Run.Safe (wordWidth n)`. | n/a | OPEN: relation to `wordWidth xs.length` is S8. |

## S1 evidence rows (S1_SPECIFICATION, 2026-09-13)

Appended after the Stage 0 appendix; every verbatim section, frozen row and
earlier appendix above is unchanged (this appendix only adds text after the end
of the file at Stage 0 commit `5f325dd`). S1 is the machine-free specification
checkpoint: it states the equality target and the reference-side laws the
builder stages will consume. No builder program, run, cost constant or
capstone exists, so **no frozen row changes status: all 31 IDs remain OPEN**.
Modules: `RMQ/Core/WordRAM/Construction/Spec/{OpenCounts,Dyck,ArgMinSplit,Positions,Plan}.lean`
(outside the builder firewall); consumer `scripts/preprocessing_spec_check.lean`;
commands in BUILDER_STAGE_LOG.md section S1.

| Evidence for | S1 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S1 |
| --- | --- | --- | --- | --- |
| S1 / REQ-PRE-EXACT | `buildMemory_eq_plan : ∀ xs : List Int, buildMemory xs = metadataOf n lc sc ++ (List.range count).map (fun i => bitsToNatLE (cellAt (natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++ List.replicate (oldBits - (oldW + packedReviewerPayloadLength n lc sc)) false ++ List.replicate (count * W - oldBits) false) W i))` with `shape = SuccinctClassic.cartesianShape xs`, `n = xs.length`, `lc = longCount shape`, `sc = packedReviewerSparseCount shape`, `oldW = packedReviewerCellWidth n`, `W = wordWidth n`, `oldBits = packedReviewerCellCount n lc sc * oldW`, `count = selectCeilDiv oldBits W`. `accessSegments` lists the 18 live sources in payload order as `tableBits entries width` (entries/widths pinned by `rfl`: final rank super/block over `bpCode` at `ws = machineWordBits (2n)`, select super/local field projections of `superEntries`/`localEntries`, long-flag rank tables over `longSuperFlagBits` with blocks-per-super 1, raw `longSuperFlagBits`, `longSuperRelativeEntries`, sparse flag-rank tables over `sparseExceptionEffectiveFlagBits`, raw `sparseExceptionEffectiveFlagBits`, `sparseExceptionRelativeEntries`); `interiorSegments` lists baseline, minRel, maxRel, argOffset, local sparse, global sparse, local level, global level over `RelativeRmm.canonicalLayout shape`. `FixedWidthNatTable.payload_eq_tableBits : ∀ (table : FixedWidthNatTable entries width), table.payload = flattenPayloadWords (entries.map (natToBitsLE width))`. `metadata_eq_metadataOf : metadata shape = metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape)` (rfl); `metadataOf_length = 174`. BP law `bpCode_eq_openCounts_flatMap : ∀ T, T.bpCode = (openCounts T).flatMap (fun c => replicate c true ++ [false])`, `openCounts_length : (openCounts T).length = T.size`, `openCounts_insertRight : ∀ t v, openCounts (t.insertRight v).shape = match insertPoint t v with \| none => openCounts t.shape ++ [1] \| some ld => (openCounts t.shape).modify ld (· + 1) ++ [0]`. One-pass directories: `selectFrom_scan`, `positionFill_spec : positionFill target bits 0 0 arr k = if k < occurrenceCount bits target then position bits target k else arr k`, `rankPrefix_running`, `rankSampleFill_spec`, `canonical{Super,Block}RankEntries_eq_fill`, `rankSampleEntries_eq_fill`. Sparse memo: `bpRangeArgMinBlock_split : 0 < b → bpRangeArgMinBlock shape bs start (a + b) = bpBetterArgMinBlock shape bs (bpRangeArgMinBlock shape bs start a) (bpRangeArgMinBlock shape bs (start + a) b)`. | `scripts/preprocessing_spec_check.lean` restates each at full type; later `efficientBuild_eq_buildMemory` will rewrite by `buildMemory_eq_plan` and discharge segment by segment. | Producer mutation S1-14 (the sparse flag leaf replaced by the non-emitted `sparseFlagBits`) rejected at `Plan.lean:216:4`; S1-15 (fringe and select chunk swapped) rejected at `Plan.lean:296:2`; both restored byte-exact. Kernel `decide` fixtures: `[4,-3,-3,8]` gives open counts `[2,0,1,1]` and BP `[T,T,F,F,T,F,T,F]` (leftmost tie), `[1,1,1,1]` gives `[1,1,1,1]` (equal keys descend right). `#guard` evaluates `buildMemory xs` against the plan for `[]`, `[7]`, `[4,-3,-3,8]`, `crossBlockInput`. | OPEN: specification half only; no charged builder. Plan S1 item 6 (literal envelopes) is not covered by this appendix. |
| S1 / REQ-PRE-COST | `bpCode_closes_le_opens : ∀ T p, rankPrefix false T.bpCode p ≤ rankPrefix true T.bpCode p`; `bpExcessAt_succ_of_close : T.bpCode[p]? = some false → 1 ≤ bpExcessAt T p ∧ bpExcessAt T (p + 1) = bpExcessAt T p - 1`; `bpExcessAt_succ_of_open`; `bpRangeArgMinBlock_pow_succ` and `bpRangeArgMinBlock_pow_succ_mul` (one `better` per memo cell). | Future running-excess counter (`sub` non-underflow obligation of `Prim.SafeAt`) and doubling memo cost. | The split law needs `0 < b`, and this premise is necessary: with `b = 0` the right-hand side still compares block `start + a`. | OPEN: no cost theorem. |
| S1 / INV-STORE-IDENTITY | The plan is stated about `PackedWordRAM.buildMemory xs` itself (the PQ1 allocation), with `packedReviewerPayloadBits` the canonical reviewer payload. | `buildMemory_eq_plan` -> future `efficientBuild_eq_buildMemory`. | Not a sibling payload: the legacy close tables bound by `let`s in `concreteBPNativeSuccinctRMQFlatPayloadSourcePayload` are not used; the interior segments are the `canonicalRelativeRmm*` tables of the executed directory. | OPEN. |
| S1 / INV-ORACLE-INDEPENDENCE | Fixture expected values in the spec consumer are reference functions (`openCounts`/`bpCode` of `insertRight` folds, `GenericSelect.position`, `rankSampleEntries`, `buildMemory`). | Consumer. | The fill scans are compared with reference `position`/`rankSampleEntries` values. | OPEN: builder fixtures are S3-S8. |
| S1 / INV-ALL-SIZE | Every S1 theorem quantifies over all `xs : List Int`, shapes or bit lists. Side conditions: `0 < b` (split; necessary), positive strides in the fill lemmas (the reference strides are `machineWordBits ≥ 1` and blocks-per-super ≥ 1), `p ≤ bits.length` for `rankPrefix_running` (the list's index domain). | Consumer. | `[]` and `[7]` are among the `#guard` fixtures; the plan has no size dispatch. | OPEN at builder level. |
| S1 / INV-SEMANTIC-NONVACUITY | `payload_eq_tableBits` is proved from `erases`, `read_exact` and `word_length_of_get?`, not from a constructor, so it pins the stored bits of every table structure. | Consumer `spec_table_payload`. | S1-14. | OPEN at builder level. |
| S1 / INV-PROGRAM-ACCOUNTING | `metadataOf n lc sc` depends only on `n`, `lc`, `sc`, the quantities ruling Q6 lets the builder obtain from its own run. | `metadata_eq_metadataOf`. | n/a | OPEN. |
| S1 / INV-MUTATION-REPRODUCIBILITY | Two ad hoc producer mutations with byte-exact restoration. | BUILDER_STAGE_LOG.md S1-14, S1-15. | Discovery evidence only; no replayable registry case exists for S1. | OPEN. |
| S1 / INV-VALIDATION-REACH | The spec consumer is run standalone; it is not reached by the builder replay or a gate checker (WDD-20260913-PRE1-004). | n/a | n/a | OPEN. |

## S1 envelope evidence rows (S1_COMPLETE, 2026-09-13)

Appended after the S1 appendix of checkpoint `b3570ac`; nothing above is
changed. These rows add plan S1 item 6 (literal all-size envelopes,
`RMQ/Core/WordRAM/Construction/Spec/Envelope.lean`). **All 31 IDs remain OPEN.**

| Evidence for | S1 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S1 |
| --- | --- | --- | --- | --- |
| S1 / REQ-PRE-COST | `planPayload_length_add_two_le : ∀ shape, (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape).length + 2 ≤ 400000 * (shape.size + 1)`; `accessEntryCounts_le`, `interiorEntryCounts_le`, `microtableRowCounts_le`: every table entry list and both raw flag vectors of the plan have length `≤ 400000 * (shape.size + 1)`; `selectSlotCounts_le`; `planBuffer_le : ∀ xs, oldBits ≤ 400384 * xs.length + 401150 ∧ selectCeilDiv oldBits (wordWidth xs.length) * wordWidth xs.length ≤ 400576 * xs.length + 401726`; `buildMemory_length_le : ∀ xs, (buildMemory xs).length ≤ 400576 * xs.length + 401900`; `wordWidth_le_linear : wordWidth n ≤ 192 * n + 576`; layout counts `blockCount ≤ size`, `superSampleCount ≤ size + 1`, `macroSampleCount ≤ size + 1`, `globalLevelCount ≤ size + 2`, `levelCount * blockCount ≤ 3 * size`; `fringeRows_mul_scan_le : bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) * (bpFringeChunkBits (2 * n) + 1) ≤ 256 * (n + 1)`; `selectRows_mul_scan_le` (`≤ 64 * (n + 1)`); `log2_rounds_le : Nat.log2 x + 1 ≤ x + 1`. | Consumer `spec_*_le` projections at full type; future `buildWork_bound`/`Workspace.lean`. | Built on the existing literal overhead bounds, not on `LittleOLinear`; entry counts follow from `tableBits_length : (tableBits e w).length = e.length * w` with each width proved positive, so a zero-width table would not satisfy the lemma. | OPEN: upper bounds on reference counts only; no work or workspace theorem; loops the machine design adds beyond these counts need their own envelopes. |
| S1 / INV-ALL-SIZE | Every envelope quantifies over all `n`, shapes or `xs` with literal constants and no size threshold; the `n = 0` cases of the microtable scans are proved separately inside the same universal theorem. | Consumer. | `n = 0`: `c = 1`, 8 fringe rows, 4 select rows. | OPEN at builder level. |
| S1 / INV-ORACLE-INDEPENDENCE | Open counts on `[]`, `[7]` and `crossBlockInput` checked by kernel `decide` on `insertRight` folds against lists derived by hand from the leftmost-minimum tree. | `openCounts_fixture_plan_lists`. | The expected lists were written before the check ran and were not taken from any evaluator output. | OPEN: builder fixtures are S3-S8. |

## S2 checkpoint evidence rows (S2_CHECKPOINT, 2026-09-13)

Appended after the S1 envelope appendix; nothing above is changed. Stage S2 has
begun under the coordinator's authorization after condition C1 (`361fe82`).
This checkpoint holds the first builder program text
(`RMQ/Core/WordRAM/Construction/Builder/{Registers,Emit,Geometry,Interior}.lean`,
inside the builder firewall) and its specifications
(`RMQ/Core/WordRAM/Construction/Proof/{Base,Emit,Interior,Geometry,Stage2}.lean`,
outside it); consumer `scripts/preprocessing_stage_check.lean`; commands in
BUILDER_STAGE_LOG.md rows S2-1..S2-14. No builder program constant, run, cost
literal or capstone exists, so **all 31 IDs remain OPEN**.

| Evidence for | S2 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S2 checkpoint |
| --- | --- | --- | --- | --- |
| S2 / REQ-PRE-EXACT | `localLevelTable_emits_payload : ∀ {W}, 32 ≤ W → ∀ (shape : CartesianShape) (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = shape.size → (shape.size + 2) * (shape.size + 2) * ((shape.size + 2) * (shape.size + 2)) < 2 ^ W → s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize * bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) < 2 ^ W → ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock 34 36)) s s' k ∧ s'.status = .running ∧ Emits s s' ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload.map bitToNat)`; `globalLevelTable_emits_payload` the same for `macroSampleCount`, `levelTableBlock 35 37` and the global table. Generic: `emitBits_spec` (appends `natToBitsLE (regs w) (regs v)` as 0/1 cells), `emitTable_spec` (appends `flattenPayloadWords (((List.range (regs count)).map f).map (natToBitsLE (regs w)))` for any entry block computing `f`). | Consumer restates each at full type (`spec_emitBits`, `spec_emitTable`, `spec_log2Block`, `spec_Emits_def`, `spec_interiorGeometry`, `spec_localLevelTable_emits_payload`, `spec_globalLevelTable_emits_payload`); the table identity is the S1 lemma `Spec.FixedWidthNatTable.payload_eq_tableBits`, so the emitted bits are the stored payload of the reference structure consumed by the interior segments of `buildMemory_eq_plan`. | Producer mutation S2-13 (`levelEntryBlock` multiplies by the power register instead of the level register) rejected at `Proof/Interior.lean:109:22`, restored byte-exact; consumer source pins `emitBits_def` and `levelEntryBlock_def` by `rfl`; `#guard` runs `evalF` on the source fragment for `n ∈ {0, 5, 24}` (local) and `n = 24` (global) against the reference payloads. | OPEN: two of the interior tables only; the remaining segments, the header, paddings and the word repack are S3-S6. |
| S2 / REQ-PRE-MACHINE | Every S2 specification is a `SafeEval W` fact: each executed action satisfies `Action.Safe W` (`Prim.Safe W 0`) at its pre-state, including the `reserve`/`store` capacity and address conditions and the `sub` non-underflow condition of the emission loop counter. | `acts_evalG`, `EvalG.regs_frame`, `EvalG.keys_eq` (Proof/Base) -> component specs -> end-to-end theorems. | The capacity premises are explicit hypotheses rather than hidden in definitions; `32 ≤ W` is required as in `SafeEval.compile_safe`. | OPEN: no compiled program or run; premises are discharged at `wordWidth n` in S8. |
| S2 / REQ-PRE-COST | `emitBits_spec`: `k ≤ 7 * s.regs w + 3`; `emitTable_spec`: `k ≤ s.regs count * (J + 7 * s.regs w + 7) + 3`; `log2Block_spec`: `k ≤ 5 * Nat.log2 (s.regs src) + 4`; `levelEntry_spec`: `j ≤ 5 * Nat.log2 (u.regs dom) + 7`; `levelTable_spec`: `k ≤ s.regs dom * (5 * Nat.log2 (s.regs dom) + 7 + 7 * s.regs wid + 7) + 3`. | Future work theorem. | Bounds come from the `loop_iterate`/`loop_measure` rules, not from a stated constant. | OPEN: `interiorGeometry_spec` and the end-to-end theorems carry no cost conjunct. |
| S2 / INV-ALL-SIZE | The end-to-end theorems quantify over every `CartesianShape` and every width `W ≥ 32` meeting the stated capacity premises; the geometry prelude has no size dispatch (`n = 0` goes through the same block, `log2 0 = 0`). | Consumer. | `#guard` at `n = 0`. | OPEN: the capacity premises are not yet related to `wordWidth xs.length`. |
| S2 / INV-SEMANTIC-NONVACUITY | The emission predicate fixes the extent and every memory cell (inside the appended range to the given value, outside it to the old value), so a block that emits nothing or other values cannot satisfy it. | `spec_Emits_def` by `Iff.rfl`. | S2-13. | OPEN at builder level. |
| S2 / INV-MUTATION-REPRODUCIBILITY | One ad hoc producer mutation of builder program text with byte-exact restoration (hash equal to the manifest value). | BUILDER_STAGE_LOG.md S2-13. | Discovery evidence only; a registered case on a closure module would stop at the manifest hash surface until C3 lands the per-mutation re-hash. | OPEN. |
| S2 / INV-VALIDATION-REACH | The four Builder modules are reached by the builder firewall (allowed-imports table and manifest, `PRE1-BUILDER-FIREWALL PASS ... 11 modules`); the Proof modules and the stage consumer are not reached by the builder replay or a gate checker (WDD-20260913-PRE1-007). | n/a | n/a | OPEN. |
| S2 / INV-WIDTH-SCALING | One width `W` throughout (`SafeEval W`); the premises are `32 ≤ W`, `(n + 2)^4 < 2 ^ W` (written as a product) and extent bounds. | Future `Run.Safe (wordWidth n)`. | n/a | OPEN: the relation to `wordWidth n = 32 + 8 * packedReviewerCellWidth n` is S8. |

## S2 completion evidence rows (S2_COMPLETE, 2026-09-13)

Appended after the S2 checkpoint appendix; nothing above is changed. Modules
added: `RMQ/Core/WordRAM/Construction/Proof/{RegSpec,Loops,GeometryBank}.lean`;
builder text changed in `Builder/{Registers,Emit,Geometry}.lean` (re-hashed);
consumer `scripts/preprocessing_stage_check.lean`; commands in
BUILDER_STAGE_LOG.md rows S2-15..S2-32. No builder program constant, run,
whole-builder cost literal or capstone exists, so **all 31 IDs remain OPEN**.

| Evidence for | S2 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S2 |
| --- | --- | --- | --- | --- |
| S2 / INV-PROGRAM-ACCOUNTING | `geometryPrelude_spec : ∀ {W n}, 32 ≤ W → 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W → ∀ s, s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = n → ∃ s' k, SafeEval W geometryPrelude s s' k ∧ k ≤ 25 * W + 40 + 39 * (5 * W + 20) ∧ s'.status = .running ∧ GeoBase n s'.regs ∧ GeoUpTo n 39 s'.regs ∧` frame outside 20-28 and 30-76 `∧` memory, extent, keys, key registers unchanged. Every size-only quantity is computed from register 1 by charged arithmetic; `GeoUpTo n 39 r` says `r (38 + i) = geoVal n i` for all `i < 39`. | `spec_geometryPrelude`, `spec_geoChain`, `spec_GeoUpTo_def`, `spec_GeoBase_def`, `spec_geoVal_pins` (35 reference identities by `rfl` at independently written terms, e.g. `geoVal n 37 = PackedCellProbe.packedReviewerCellWidth n`, `geoVal n 38 = PackedWordRAM.wordWidth n`, `geoVal n 36 = genericSparseExceptionBPCloseAccessOverhead n`, `geoVal n 31 = canonicalRelativeRmmInteriorRawPayloadOverhead n`). | Producer mutation S2-27 (budget constant of step 36) rejected in `geoStep36`; `#guard geoSmoke n` for `n ∈ {0, 1, 7, 24, 1000}` compares all 39 bank registers of an `evalF` run of the source with `geoVal n i`; source pins `geometryPrelude_def`, `geoStepBlock_36_def`. | OPEN: metadata offsets, word counts and `lc`/`sc`-dependent quantities are S6/S7. |
| S2 / REQ-PRE-COST | Literal costs: `forSlots_spec` `k ≤ regs cnt * (J + 4) + 3`; `emitFlatMap_spec` the same; `reserveArray_spec` `k ≤ 5 * regs cnt + 4`; `RegSpec.log2` `5 * log2 x + 4`; every bank step `k ≤ 5 * W + 20`; `levelWidthBlock_spec` `k ≤ 10 * W + 11`; `interiorGeometry_spec` `k ≤ 25 * W + 40`; prelude `25 * W + 40 + 39 * (5 * W + 20)`. | Consumer projections at full type. | Costs are derived through `EvalG.loop_iterate` and `acts_evalG`, not assumed. | OPEN: no whole-builder work theorem; the end-to-end level-table theorems still state no cost. |
| S2 / REQ-PRE-EXACT | `emitFlatMap_spec`: a counted loop whose body appends `g k` at slot `k` appends `(List.range (regs cnt)).flatMap g` (`Emits`); `reserveArray_spec`: `Emits s s' (List.replicate (regs cnt + 1) 0)` with the base address recorded. | `spec_emitFlatMap`, `spec_reserveArray`. | `Emits` fixes extent and every memory cell (checkpoint row). | OPEN: used by S3-S6. |
| S2 / INV-WIDTH-SCALING | One width `W` and one capacity premise for the bank, `2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W`, from which the checkpoint premise `(n + 2)^4 < 2 ^ W` is derived (`interior_cap_of_bank`). | `spec_geometryPrelude`. | n/a | OPEN: discharge at `wordWidth n` is S8 (intended argument in DD-20260913-PRE1-007, not machine-checked). |
| S2 / INV-MUTATION-REPRODUCIBILITY | One further ad hoc producer mutation with byte-exact restoration. | BUILDER_STAGE_LOG.md S2-27. | Discovery evidence only. | OPEN. |
| S2 / INV-VALIDATION-REACH | Changed Builder modules re-hashed and reached by the builder firewall (PASS, 11 modules); the three new proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-008. | n/a | OPEN. |

## S3 evidence rows (S3_COMPLETE, 2026-09-13)

Appended after the S2 completion appendix; nothing above is changed. Modules:
`Builder/{Cartesian,Program}.lean` (new, registered), `Builder/Registers.lean`
(re-hashed), `Spec/Spine.lean`, `Proof/{Leaf,Cartesian,StackPass,BPEmit}.lean`,
`Proof/Loops.lean` (potential variants); consumer
`scripts/preprocessing_stage_check.lean`; commands in BUILDER_STAGE_LOG.md rows
S3-1..S3-16. **All 31 IDs remain OPEN.**

| Evidence for | S3 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S3 |
| --- | --- | --- | --- | --- |
| S3 / REQ-PRE-INPUT | `keyLeaf_spec : ∀ {W}, 32 ≤ W → ∀ xs, KeySpec W xs (OracleInput xs) keyLeaf` with no further premise; `wordLeaf_spec : ∀ {W}, 32 ≤ W → ∀ xs, KeySpec W xs (WordInput W xs) wordLeaf`, where `WordInput` contains `InputFits W xs` and the pre-supplied encoded cells. Every S3 stage theorem takes `KeySpec` as its only key hypothesis. | `spec_keyLeaf`, `spec_wordLeaf`, `spec_KeySpec_def`, `spec_OracleInput_def`, `spec_WordInput_def`; `keyLeaf_def`, `wordLeaf_def` pin the V3-3 literals. | The comparison model reads keys only through `loadKey` (a key bank lookup); the word model compares encoded words, whose order equals `Int` order only under `SignedFits` (`encodeInt_lt_iff`). | OPEN: the capstone's input boundary is S8. |
| S3 / REQ-PRE-EXACT | `cartesianBP_key` and `cartesianBP_word`: for all `xs`, the charged fragment `stackArraysBlock; stackPassBlock leaf; bpEmitBlock` appends `(Cartesian.shape xs).bpCode.map bitToNat` right after its arrays (cells `s.extent + 3 (n + 1) + a` for `a < 2 n`), memory below the start extent unchanged. | `spec_cartesianBP_key`, `spec_cartesianBP_word`; the chain is `StackInv` → `openCounts (buildTree xs).shape` (`openCounts_insertRight`, `spineFrom_insertRight`, `insertPoint_eq_find`, `spineFrom_sorted`) → `bpCode_shape_eq_openCounts_buildTree` (S1). | Fixtures before proofs (S3-2) and consumer `#guard` in both models including ties `[1, 1, 1, 1]` and `[4, -3, -3, 8]`; mutation S3-14 rejected in `popGuard_spec`. | OPEN: the BP segment must be placed after the header reservation (S6) and consumed by S4/S5. |
| S3 / REQ-PRE-COST | `stackPass_spec` `k ≤ 50 n + 4` (amortized: potential = stack height, 18 per pop through `EvalG.loop_measure_pot`); `bpEmit_spec` `k ≤ 14 n + 3` (potential = cells still to emit); `cartesianBP_*` `k ≤ 79 n + 19`. | Consumer projections. | Scratch step counts on `runArray` grew linearly (1154 at 16 keys to 38791 at 512 keys, row S3-2). | OPEN: no whole-builder work theorem. |
| S3 / INV-VALUE-DEPENDENCY | The only data-dependent control is the pop guard, computed from the leaf's result register; the stage theorems quantify over all key lists. | `spec_cartesianBP_*`. | S3-14. | OPEN. |
| S3 / INV-ALL-SIZE | All S3 theorems quantify over every `xs`, including `[]` (no stack step runs; the BP segment is empty). | Consumer `#guard` at `[]` and `[7]`. | n/a | OPEN at builder level. |
| S3 / INV-VALIDATION-REACH | New builder modules are reached by the builder firewall (13 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-009. | n/a | OPEN. |

## S4 checkpoint evidence rows (S4_CHECKPOINT, 2026-09-13)

Appended after the S3 appendix; nothing above is changed. Modules:
`Builder/{Registers,Interior}.lean` (re-hashed), `Spec/BlockStats.lean`,
`Proof/{BlockStats,SummaryTables}.lean`, `Proof/Emit.lean` (strengthened
`emitTable_spec` entry premise); consumer `scripts/preprocessing_stage_check.lean`;
commands in BUILDER_STAGE_LOG.md rows S4-1..S4-15. **All 31 IDs remain OPEN.**

| Evidence for | S4 checkpoint checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after the checkpoint |
| --- | --- | --- | --- | --- |
| S4 / REQ-PRE-EXACT | `blockStats_spec`: for every shape, block size `bs` and block count `bc` with `bc * bs ≤ 2n`, from the BP cells at `B` and four array bases ordered below `B`, `blockStatsBlock` stores `bpExcessAt shape (b * bs)` at `A0 + b` for `b ≤ bc` and `bpBlockMinExcess`, `bpBlockMaxExcess`, `bpBlockArgMinPrefixPos shape bs b` at `A1 + b`, `A2 + b`, `A3 + b` for `b < bc`, with memory outside `[A0, A3 + bc)` unchanged. `summaryTablesBlock` then appends `(tableBits (bpSuperblockBaselineEntries shape bs bps ssc) sw ++ tableBits (bpBlockRelativeMinExcessEntries shape bs bps bc) rw ++ tableBits (bpBlockRelativeMaxExcessEntries shape bs bps bc) rw ++ tableBits (bpBlockArgMinLocalOffsetEntries shape bs bc) rw).map bitToNat` (`summaryTables_spec`, premises `0 < bps`, `ssc = bc / bps + 1` and capacity). | `spec_blockStats`, `spec_summaryTables`, `spec_sampleLoop`, `spec_blockBody`, the three entry projections, `spec_tableBits_def`; chain: folds over samples (`natListMinFrom_append_singleton`, `natListMax_append_singleton`, `bpBlockArgMinPrefixPosFrom_eq_argAcc`) and `excess_step`, then `emitTable_spec`. | Fixtures before the proofs (S4-2, eleven inputs) and consumer `#guard` for 17 inputs including `n` in {0, 1, 2, 3} (`blockCount = 0`), threshold sizes `2^k ± 1` and `crossBlockInput` (S4-11); scratch mutation of the argmin comparison rejected (S4-14). | OPEN: the canonical-layout instantiation, the sparse tables, the level tables in store order and `closeSegment_eq` remain. |
| S4 / REQ-PRE-COST | `sampleLoop_spec` `j ≤ (bs + 1) * 28 + 3`; `blockBody_spec` `j ≤ (bs + 1) * 28 + 16`; `blockStats_spec` `j ≤ bc * ((bs + 1) * 28 + 20) + 7`; `summaryTables_spec` `j ≤ ssc * (7 sw + 10) + bc * (21 rw + 41) + 13`. | Consumer projections. | n/a | OPEN: linearity at the canonical layout (`bc * bs ≤ 2n`, `bc ≤ n`) and `close_cost` are not yet stated. |
| S4 / INV-VALUE-DEPENDENCY | The only data-dependent control in the checkpoint is the argmin improvement test and the last-sample guard; loop counts are layout registers. | `spec_sampleLoop`. | S4-14. | OPEN. |
| S4 / INV-ALL-SIZE | The checkpoint theorems quantify over every shape and every layout meeting size-only premises; `bc * bs ≤ 2n` holds for `blockSize = 2 base`, `blockCount = n / base` at every `n` (not yet stated as a theorem). | n/a | Consumer `#guard` at `n` in {0, 1, 2, 3}. | OPEN: the premise discharge belongs to the close-segment composition. |
| S4 / INV-VALIDATION-REACH | Changed builder modules are re-hashed and reached by the builder firewall (13 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-010. | n/a | OPEN. |

## S4 completion evidence rows (S4_COMPLETE, 2026-09-13)

Appended after the S4 checkpoint appendix; nothing above is changed. Modules:
`Builder/{Registers,Interior}.lean` (re-hashed), `Spec/SparseMemo.lean`,
`Proof/{SparseMemo,SparseTables,InteriorClose}.lean`; consumer
`scripts/preprocessing_stage_check.lean`; commands in BUILDER_STAGE_LOG.md rows
S4-16..S4-34. **All 31 IDs remain OPEN.**

| Evidence for | S4 completion checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S4 |
| --- | --- | --- | --- | --- |
| S4 / REQ-PRE-EXACT | `closeSegment_spec`: for every `W ≥ 32`, shape and running state holding the size-only geometry (`GeoBase n ∧ GeoUpTo n 39`, `n = shape.size`), the BP cells at `B` and the statistics and memo array bases in the stated order below `B`, with `s.extent + 16 * (400000 * (n + 1)) < 2 ^ W`, `interiorCloseBlock` reaches a state `s'` and a work state `t` with `t.extent = s.extent`, memory outside `[A0, Gb + GLC * mc)` unchanged, and `Emits t s' ((canonicalRelativeRmmInteriorDirectory shape).payload.map bitToNat)`. | `spec_closeSegment`, `spec_interiorPayload_eq_segments`; chain: `interiorCloseLayout_spec` (eight tables) ← `blockStats_spec`, `localMemo_spec`, `globalMemo_spec`, `summaryTables_spec`, `localSparseTable_spec`, `globalSparseTable_spec`, `levelTable_spec`; keys by `argPos_excess_eq_min`, doubling by `bpRangeArgMinBlock_pow_succ(_mul)` (S1). | Fixtures before the proofs of this part (S4-18) and 24 consumer `#guard` inputs against all eight segments, including `n ∈ {0, 1, 2, 3}` (no complete block or macro), threshold sizes up to 129 and `crossBlockInput`; scratch mutation S4-32 rejected. | OPEN: S6 must place the arrays in the assumed order and the close segment in the buffer; the capacity premise is discharged at `wordWidth n` in S8. |
| S4 / REQ-PRE-COST | `closeSegment_spec` `k ≤ 1600 * (400000 * (n + 1))`, from the component bounds and the S1 envelopes (segment lengths and entry counts `≤ 400000 * (n + 1)`, `levelCount * blockCount ≤ 3n`). | `spec_closeSegment`. | n/a | OPEN: no whole-builder work theorem; the constant is crude (ruling Q7). |
| S4 / INV-ALL-SIZE | The canonical theorem has no readiness or compatibility premise; its only size premise is the capacity bound. | `spec_closeSegment`. | Consumer `#guard` at `n ∈ {0, 1, 2, 3}`. | OPEN at builder level. |
| S4 / INV-VALUE-DEPENDENCY | Data-dependent control in the close segment: the argmin improvement tests, the block selection by stored minima and the entry guards (layout-only). | `spec_memoCell`, `spec_localEntry`, `spec_globalEntry`. | S4-32. | OPEN. |
| S4 / INV-VALIDATION-REACH | Changed builder modules are re-hashed and reached by the builder firewall (13 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-011. | n/a | OPEN. |
| S4 / process | One command exceeded five minutes without `Global\RMQHeavyVerification` (S4-20, 409.31 s). | BUILDER_STAGE_LOG.md S4-20; WDD-20260913-PRE1-011. | n/a | Recorded deviation; mitigation in place. |

## S5 evidence rows (S5_COMPLETE, 2026-09-13)

Appended after the S4 completion appendix; nothing above is changed. Modules:
`Builder/Access.lean` (new, registered and hashed), `Spec/Access.lean`,
`Proof/{PosPass,AccessFlags,AccessEntries,AccessRelative,AccessTables,AccessHalf}.lean`;
consumer `scripts/preprocessing_stage_check.lean`; commands in
BUILDER_STAGE_LOG.md rows S5-1..S5-19. **All 31 IDs remain OPEN.**

| Evidence for | S5 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S5 |
| --- | --- | --- | --- | --- |
| S5 / REQ-PRE-EXACT | `accessHalf_spec`: for every `W ≥ 32`, shape and running state holding the size-only geometry (`GeoBase n ∧ GeoUpTo n 39`, `n = shape.size`) with `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, the BP cells at `B`, the six access array bases ordered `P0 + n + 1 ≤ R0`, `R0 + 2n / ws + 1 ≤ L0`, `L0 + sup ≤ C0`, `C0 + sup + 1 ≤ F0`, `F0 + loc ≤ G0`, `G0 + loc + 1 ≤ B`, and `s.extent + 16 * (400000 * (n + 1)) < 2 ^ W`, `accessHalfBlock` reaches `s'` and a work state `t` with `t.extent = s.extent`, memory outside `[P0, G0 + loc]` unchanged, and `Emits t s' ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map bitToNat)`; registers 177 and 178 hold `longCount shape` (`lc_eq_longCount`) and the sparse-exception count whose product with `localStride` is `packedReviewerSparseCount shape` (`sc_eq_sparseCount`). | `spec_accessHalf_spec`, `spec_accessPasses_spec`, `spec_accessSegments_eq`, `spec_liveAccessPayload_eq_segments`, `spec_lc_eq_longCount`, `spec_sc_eq_sparseCount`; chain: `posPass_spec` (by `select_at_close`) → `longFlags_spec`, `sparseFlags_spec` → `AccessReady` → `accessTable1_spec` .. `accessTable18_spec` (sixteen through `accessTable_generic` and the entry lemmas, two through `relLoop_spec` and `relativeOffsetsOrZero_eq_positions`). | Fixtures before the proofs (S5-2) and 20 consumer `#guard` inputs against all eighteen segments; crafted long-super threshold inputs (S5-4: span `superLongSpan`, long count 0; span `superLongSpan + 1`, long count 1) on sources 11-14; scratch mutation S5-17 rejected. No executable input sets a sparse-exception flag (S5-18: local stride 1 for `n < 2 ^ 96`). | OPEN: S6 must reserve the arrays in the assumed order and place the access segments after the BP code; the capacity premises are discharged at `wordWidth n` in S8. |
| S5 / REQ-PRE-COST | `accessHalf_spec` `k ≤ 200 * (400000 * (n + 1))`, from the pass bounds (`(2n + 1) * 20 + 7`, `sup * 39 + 6`, `loc * 64 + 6`), per-table bounds `(J + 14) * bits + 3` and the potential bounds of the relative loops (`slots * 29 + 3 + 34 * bits`), with the S1 envelopes. | `spec_accessHalf_spec`, `spec_relLoop_spec`, `spec_accessTable_generic`. | n/a | OPEN: no whole-builder work theorem; the constant is crude (ruling Q7). |
| S5 / REQ-PRE-INPUT | The access half reads only the BP cells and its own arrays; positions come from one left-to-right scan, never from a rank or sort primitive. | `spec_posPass_spec`, `posPassBlock_def`. | n/a | OPEN at builder level. |
| S5 / INV-ALL-SIZE | The theorem has no readiness or compatibility premise; its size premises are the two capacity bounds. | `spec_accessHalf_spec`. | Consumer `#guard` at `n ∈ {0, 1, 2, 3}`. | OPEN at builder level. |
| S5 / INV-VALUE-DEPENDENCY | Data-dependent control in the access half: the close test and word-boundary test of the scan, and the stored-flag tests of the two relative loops; all other entries are branch-free arithmetic. | `posStepBlock_def`, `longRelativeBodyBlock_def`, `sparseRelativeBodyBlock_def`. | S5-17. | OPEN. |
| S5 / INV-VALIDATION-REACH | The new builder module is registered and hashed by the builder firewall (14 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-012. | n/a | OPEN. |

## S6 evidence rows (S6_COMPLETE, 2026-09-13)

Appended after the S5 appendix; nothing above is changed. Modules:
`Builder/{Micro,Finish}.lean` (new, registered and hashed), `Spec/Micro.lean`,
`Proof/{Micro,Finish,Buffer}.lean`; consumer
`scripts/preprocessing_stage_check.lean`; commands in BUILDER_STAGE_LOG.md rows
S6-1..S6-21. **All 31 IDs remain OPEN.**

| Evidence for | S6 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S6 |
| --- | --- | --- | --- | --- |
| S6 / REQ-PRE-EXACT | `bufferStage_spec`: for every `W ≥ 32`, `xs`, input predicate reading memory below the extent, `KeySpec` leaf and running state with register 0 zero, the bank (`GeoBase n ∧ GeoUpTo n 39`, `n = xs.length`), `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, the access bases ordered as in `accessHalf_spec` and the interior bases as in `closeSegment_spec`, both ending at or below `s.extent`, and `s.extent + 32 * (400000 * (n + 1)) < 2 ^ W`: `stackArraysBlock; stackPassBlock leaf; bufferBlock` reaches `s'` with register 220 `= base = s.extent + 3 * (n + 1)`, `ArrayAt s' base T.length (T.getD · 0)` for `T = (densePad (wordWidth n) (packedReviewerPaddedBits (shape xs))).map bitToNat`, `s'.extent ≤ base + T.length + 1`, memory below `s.extent` unchanged outside the two layouts, register 177 `= longCount (shape xs)`, register 178 the sparse-exception flag count, registers outside 4-28 and 100-228 and the keys unchanged. Microtables: `fringeTable_spec`, `selectTable_spec`, `microtables_spec` emit `(tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat`. Header and paddings: `headerPatch_spec` stores `lc / 2 ^ i % 2` at `base + i` for `i < oldW`; `pad_spec` appends `denseBitsOf oldW W L - L - [L < D] + 1` zero cells. | `spec_bufferStage_spec`, `spec_bufferHead_spec`, `spec_bufferAccessClose_spec`, `spec_bufferTail_spec`, `spec_bufferCells_getD`, `spec_bufferCells_length`, `spec_microtables_spec`, `spec_headerPatch_spec`, `spec_pad_spec`; chain: `stackArrays_spec`, `stackPass_spec` → `headerReserve_spec` → `bpEmit_spec` → `accessHalf_spec` → `closeSegment_spec` → `microtables_spec` (entries by `selectPos_step`/`selectPos_final` and `fringeBest_step`/`excessOffset_succ`) → `headerPatch_spec` → `pad_spec`, joined by `EmitsFrom.trans` and compared with the reference through `canonicalReviewerPayload_eq_plan`, `liveAccessPayload_eq_segments`, `interiorPayload_eq_segments` and `packedReviewerPaddedBits_length`. | Fixtures before the proofs (S6-5; microtables re-run in S6-17) and 25 consumer `#guard` fixtures (5 microtable sizes with `c = 1, 2`; 20 whole-buffer inputs); long count 1 at `n = 13395` (S6-12); the `L = D` edge at `n = 1116` (S6-14); scratch mutation S6-15 rejected with its control passing; the S5 mutation re-checked (S6-16). | OPEN: the plan's `outBase - bufBase = denseCount * W` is false for this text when `L = D` (DD-20260913-PRE1-012); S7 must reserve the arrays in the stated layout, repack and emit; capacity premises at `wordWidth n` in S8. |
| S6 / REQ-PRE-COST | `bufferStage_spec` `k ≤ 2000 * (400000 * (n + 1))`, summed from `79n + 21 + 5 oldW` (head), `1800 * (400000 * (n + 1))` (access and close), `100 * (400000 * (n + 1))` (tail: microtables `rows * (25c + 49 + 7 width) + rows' * (14c + 16 + 7 width') + 6` with `fringeRows_mul_scan_le` and `selectRows_mul_scan_le`, header patch `8 oldW + 4`, paddings `5 (D - L) + 18`). | `spec_bufferStage_spec`, `spec_bufferTail_spec`, `spec_microtables_spec`, `spec_pad_spec`. | n/a | OPEN: no whole-builder work theorem; the constant is crude (ruling Q7). |
| S6 / INV-PROGRAM-ACCOUNTING | The buffer is measured, not supplied: the pad block obtains `L` from a reserved probe address and computes `oldW`-cell and `W`-cell rounding from bank registers 75 and 76; microtable rows are computed per slot from the slot number. | `padBlock_def`, `fringeEntryBlock_def`, `selectEntryBlock_def`, `spec_denseBitsOf_def`. | S6-15. | OPEN: no program constant yet. |
| S6 / INV-ALL-SIZE | No readiness or compatibility premise; the size premises are the two capacity bounds and the array layouts. | `spec_bufferStage_spec`. | Consumer `#guard` at `n ∈ {0, 1, 2, 3}`; microtables at `c = 1, 2` (consumer) and `c = 3` (S6-17). | OPEN at builder level. |
| S6 / INV-VALUE-DEPENDENCY | Microtable rows and paddings are branch-free arithmetic on comparison results; the only loops are counted by slot counts, pattern width, `oldW` and the measured padding count. | `fringeStepBlock_def`, `selectStepBlock_def`, `zerosBlock_def`. | n/a | OPEN. |
| S6 / INV-VALIDATION-REACH | The two new builder modules are registered and hashed by the builder firewall (16 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-013. | n/a | OPEN. |
| S6 / process | S5-17 declared its mutated block in a namespace its theorem did not open; S6-16 re-ran it with names resolved and a passing control. The untracked `Proof/Buffer.lean` carried two temporary placeholders during one build (S6-7 run 1); no commit contains them. | BUILDER_STAGE_LOG.md S6-7, S6-16; WDD-20260913-PRE1-013. | S6-16 rejected, control passed. | Recorded. |

## Condition C2 evidence rows (C2_HEADERFIRST_CONSUMER, 2026-09-13)

Appended after the S6 appendix; nothing above is changed. Changed surfaces:
`builder_cases.json` (B14), `scripts/preprocessing_builder_replay.ps1` (IDs and
registry pin), BUILDER_REPLAY_DESIGN.md (B14 row); commands in
BUILDER_STAGE_LOG.md rows C2-1..C2-5. **All 31 IDs remain OPEN.**

| Evidence for | C2 checked proposition | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after C2 |
| --- | --- | --- | --- | --- |
| C2 / INV-CERTIFICATE-ANTI-BYPASS | Weakening `HeaderUse.headerFirst` to `True` while keeping a constructible certificate breaks exactly the consumer projection `hu_headerFirst` (`scripts/preprocessing_builder_check.lean:20`). | `B14_HEADERFIRST_CONSUMER`: firewall 0, producer 0, consumer 1 with failing line set exactly {20}. | Focused replay C2-3; restoration EXACT. | OPEN: seven of seven HeaderUse fields now reach a consumer line (B05-B11, B14); foundation projections still unreached (C3, before the S8 freeze). |
| C2 / REPLAY-EXACT-REGISTRY | The registry has exactly 14 IDs in pinned order with the pinned normalized SHA-256 `ac8d76e7...2182`; registry, selector and matcher self-tests pass. | `$script:ExpectedIds`, `$script:ExpectedRegistrySha256`. | C2-2, C2-4, C2-5. | OPEN: no full 14-case run recorded yet. |
| C2 / INV-MUTATION-REPRODUCIBILITY | B14's mutation is data (exact `before`/`after`), applied once, restored byte-identically with firewall, producer and consumer re-run. | `case-B14_HEADERFIRST_CONSUMER.json`. | C2-3. | OPEN. |

## Condition C3 evidence rows (C3_MECHANISM, 2026-09-13)

Appended after the C2 appendix; nothing above is changed. Changed surfaces:
`scripts/preprocessing_builder_replay.ps1`, `builder_cases.json` (B15),
`scripts/preprocessing_builder_firewall.ps1`, both typed consumers,
BUILDER_REPLAY_DESIGN.md; commands in BUILDER_STAGE_LOG.md rows C3-1..C3-9.
**All 31 IDs remain OPEN.**

| Evidence for | C3 checked proposition | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after C3 |
| --- | --- | --- | --- | --- |
| C3 / INV-CERTIFICATE-ANTI-BYPASS | A semantic weakening of a hashed closure foundation (`runArray_abstract` without its final-state conjunct) now reaches and breaks exactly its consumer projection (`preprocessing_builder_check.lean:335`). | `B15_ARRAYRUN_FINAL_WEAKEN` through the manifest re-hash. | C3-6. | OPEN: the other foundation declarations are due before the S8 freeze; V3-7 case (i) with the S7 constants. |
| C3 / INV-MUTATION-REPRODUCIBILITY | A re-hash case changes exactly one manifest digest for its duration; source and manifest bytes are restored in one `finally` and checked before the restored stages. | `case-B15_ARRAYRUN_FINAL_WEAKEN.json` (`manifestBeforeSha256 = manifestAfterSha256`). | C3-6; registry self-tests reject a bad value, an unhashed path and a firewall-stage expectation (C3-5). | OPEN: no full 15-case run yet (C3-9). |
| C3 / REPLAY-SUBPROCESS-DEADLINE | The builder firewall's nested contract guard runs as an owned bounded child with its own deadline; a timeout is inconclusive and fails. | `-ContractGuardDeadlineSeconds`. | C3-4: a 1 s deadline produced the inconclusive failure. | OPEN: POSIX branch unexecuted. |
| C3 / CHK-PRE-CONTROLS | Both typed consumers print their marker only when every declaration elaborated without `sorry` (and, for the builder consumer, the runtime guards hold), without adding a diagnostic on failure. | `consumerWitness`, `consumerGuards`, the final command of each consumer. | C3-1, C3-2 (probes), C3-7 and C3-8 (rejected cases print no marker, accept controls print it). | OPEN: the stage consumer still prints unconditionally; its exit code is the verdict. |

## Stage S7 checkpoint evidence rows (S7_CHECKPOINT, 2026-09-13)

Appended after the C3 appendix; nothing above is changed. Changed surfaces:
`Spec/Metadata.lean`, `Builder/Output.lean`, `Proof/{MetaBounds,MetaSteps,MetaChain,Output,Tail}.lean`,
`Proof/Buffer.lean` (frame strengthened, `bufferStage_spec` type unchanged), the builder firewall
table and manifest, `scripts/preprocessing_stage_check.lean`; commands in BUILDER_STAGE_LOG.md rows
S7-1..S7-20. **All 31 IDs remain OPEN.**

| Evidence for | S7 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S7 checkpoint |
| --- | --- | --- | --- | --- |
| S7 / REQ-PRE-EXACT | `tailStage_spec`: for every `W ≥ 32`, `xs`, input predicate reading memory below the extent, `KeySpec` leaf and running state with all registers below `2 ^ W`, register 0 zero and the bank, under `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, `extent + 64 * (400000 * (n + 1)) < 2 ^ W` and `wordWidth n ≤ W`, the arrays, the buffer phase and the output phase reach a running state with `extent = outBase + (buildMemory xs).length` (`outBase` in register 3) and cell `outBase + i` holding `(buildMemory xs)[i]` for every `i`; `outputWords_eq_buildMemory` identifies the emitted list; `metaWords_eq` identifies the metadata words. | `spec_tailStage_spec`, `spec_outputWords_eq_buildMemory`, `spec_outputStage_spec`, `spec_metaWords_eq` (stage consumer). | Harness fixtures: key model on `[]`, `[7]`, `[4, -3, -3, 8]`, a 12-key input and word model at `wordWidth n` on the last two (S7-7), consumer `#guard` on `[]` and `[4, -3, -3, 8]` (S7-19). | OPEN: no program constant, run, `efficientBuild` or exactness theorem is landed (V3-6 fuel-body obstruction, REPORT.md). |
| S7 / REQ-PRE-COST | Tail stage `k ≤ 2100 * (400000 * (n + 1))`: arrays `≤ 5 * size + 2`, buffer `≤ 2000 * (400000 * (n + 1))`, bank `≤ 6 * 108`, words `= 348`, dense words `≤ N * (7W + 12) + 3` with `N * W` bounded by the buffer envelope. | `spec_tailStage_spec`, `spec_metaChain_spec`, `spec_metaEmit_spec`, `spec_repack_spec`. | n/a | OPEN: no whole-builder literal; the draft literal is crude, no tightness claimed. |
| S7 / INV-WIDTH-SCALING | Every metadata bank value is at most `3 * (400000 * (n + 1))` under the payload envelope; every register stays below `2 ^ W` along safe evaluation; the capacity premises hold at `W = wordWidth n` for every `n` (`bankcap_wordWidth`, `cap_wordWidth` in the scratch draft, S7-13). | `spec_metaVal_le`, `spec_SafeEval_regs_fit`. | S7-1 numeric check for `n` up to `2^64`. | OPEN: the two capacity lemmas are not landed. |
| S7 / INV-PROGRAM-ACCOUNTING | Metadata words are computed and stored from registers (174 stores: one `store` into the reserved first cell, 173 `emitBit`s over a fixed register list); dense words are read from buffer cells by `load`; no word is supplied. | `metaEmitBlock_def`, `repackBlock_def`, `outputBlock_def`. | n/a | OPEN. |
| S7 / INV-VALIDATION-REACH | `Builder/Output.lean` is registered and hashed (17 modules); proof modules and the stage consumer are not reached by the builder replay or a gate checker. | WDD-20260913-PRE1-017. | S7-18. | OPEN. |
| S7 / process | One scratch fixture ran 623 s without the heavy-verification mutex and was stopped (S7-6); later scratch runs were bounded by `timeout ≤ 295`. | WDD-20260913-PRE1-017. | n/a | recorded deviation. |

## Stage S7 completion evidence rows (S7_CONSTANTS, 2026-09-14)

Appended after the S7 checkpoint appendix; nothing above is changed. Changed surfaces:
`Builder/Program.lean` (constants), new `Proof/Constants.lean` and `Proof/Exact.lean`, the builder
firewall table and manifest, `scripts/preprocessing_builder_check.lean` (V3-1..V3-6 section),
`scripts/preprocessing_stage_check.lean`, `scripts/preprocessing_builder_replay.ps1` and
`builder_cases.json` (34 cases); commands in BUILDER_STAGE_LOG.md rows C7-1..C7-10. **All 31 IDs remain OPEN.**

| Evidence for | S7 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual after S7 completion |
| --- | --- | --- | --- | --- |
| S7 / REQ-PRE-EXACT | `efficientBuild_eq_buildMemory : ∀ xs : List Int, efficientBuild xs = buildMemory xs` and `efficientBuildWord_eq_buildMemory : ∀ xs : List Int, InputFits (wordWidth xs.length) xs → efficientBuildWord (wordWidth xs.length) xs = buildMemory xs`, with `efficientBuild`/`efficientBuildWord` exactly the V3-6 bodies over the actual `run` of `builderProgram`/`builderProgramWord` at fuel `builderBudget xs.length`; route: `builderRun_spec` (the compiled source reaches `halt 3` with `buildMemory xs` stored from `outBase` to the extent) and `run_of_halting`. | Stage consumer `spec_efficientBuild_eq_buildMemory`, `spec_efficientBuildWord_eq_buildMemory`, `spec_builderRun_spec`, `spec_builderSource_spec`; builder consumer body pins `efficientBuild_def`, `efficientBuildWord_def` (`rfl` at every `xs`, word pin at `wordWidth xs.length`). | `stageGuard36`: `builderProgram` and `builderProgramWord` themselves on the array-backed interpreter, `[]` and `[4, -3, -3, 8]`, emitted cells equal `buildMemory xs` (C7-5). | OPEN: both equality theorems landed; the capstone and its typed consumers are S8. |
| S7 / REQ-PRE-CONTRACT (V3-1..V3-6) | V3-1 `run_cmd` maps the nine names to `RMQ.Core.WordRAM.Construction.Builder.Program`; V3-2 `@` pins; V3-3 `rfl` shapes of both constants, `builderSource` and both leaves; V3-4 `builder_leaf_difference` with literal `P = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433]`, `K`, `Wd`; V3-5 `ProgramContract builderProgram (fun _ => builderProgram) 2107 8079` and `ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089`; V3-6a fuel body `builderBudget n = 1000000000 + 1000000000 * n` by `rfl` and `builderBudget_eq_mul_add : ∀ n, builderBudget n = 1000000000 * n + 1000000000` by `omega`. | `scripts/preprocessing_builder_check.lean` lines 351-427; `Proof/Constants.lean`; stage consumer `spec_builderBudget_eq_mul_add`. | Registry B16/B17 (V3-7 (i), re-hash), B18 (V3-1 relocation, re-hash plus companion), B19-B34 (V3-7 (ii)); focused B18 PASS with exact restoration (C7-9); B16 mutant rejected at exactly line 370 (C7-10; the runner's state check failed for an unrelated worktree edit); numeral surfaces measured (C7-6). | OPEN: the full 34-case replay on the committed tree is still due; `Cw`, `Dw` cases follow with S8. |
| S7 / REQ-PRE-COST | Fuel sufficiency for every `n`: `budget_ge : 4 + (25 * wordWidth n + 40 + 39 * (5 * wordWidth n + 20)) + 2100 * (400000 * (n + 1)) ≤ builderBudget n`, from the stage cost theorems (`builderRun_spec` bounds the transitions by the left side). | `spec_budget_ge`, `spec_builderRun_spec`. | n/a | OPEN: the capstone work field (`steps ≤ C * n + D` with halting) is S8; the literals are crude, no tightness claimed. |
| S7 / INV-WIDTH-SCALING | `bankcap_wordWidth : ∀ n, 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ wordWidth n` and `cap_wordWidth : ∀ n, n + 1 + 64 * (400000 * (n + 1)) < 2 ^ wordWidth n`; both equality theorems use `W = wordWidth xs.length`. | `spec_bankcap_wordWidth`, `spec_cap_wordWidth`. | n/a | OPEN: `Run.Safe (wordWidth n)` of the whole run is S8. |
| S7 / INV-CERTIFICATE-ANTI-BYPASS | The consumer's V3 section references the producer declarations at independently written types; a parameter on either constant, a relocated `efficientBuild` or any changed numeral breaks exactly one registered consumer line. | Registry B16-B34. | C7-6, C7-9, C7-10. | OPEN: remaining C3 foundation cases before the S8 freeze. |
| S7 / process | During C7-10 documentation files were edited in the worktree, so the replay's repository-state check failed after a correct rejection. | BUILDER_STAGE_LOG.md C7-10. | n/a | recorded deviation. |
| S7 / REPLAY-EXACT-REGISTRY | Full builder replay on `48702c2`: executed IDs equal the 34 registered IDs in order; contract replay 18 = 18 with the frozen registry hash. | `.lake/preprocessing-builder-replay/20260913-180035-...`, `.lake/preprocessing-contract-replay/20260913-182634-...`. | All 34 builder cases rejected or accepted at exactly their registered stage and surface, with exact restoration (C7-11). | OPEN: final-candidate replay and the aggregate gate are due. |
| S7 / process (claim scan) | `claim_drift_scan.ps1 -Strict` exit 0; `-SelfTest` exit 1 because its hit-count parser reads a quoted summary line from the Stage 0 audit report copy (C7-13, C7-14). | WDD-20260913-PRE1-021. | Anchored-parser probe copy passes. | recorded finding; fix outside this lane's scope. |

## Stage S8 capstone evidence rows (S8_CAPSTONE, 2026-09-14)

Appended after the S7 records rows; nothing above is changed. Changed surfaces: new
`Proof/{Flow,FlowFacts,Frames,Ownership,RunFacts,Query,Lift}.lean`, `Capstone.lean`,
`RMQ/Validation/PreprocessingContract.lean`; commands in BUILDER_STAGE_LOG.md rows S8-1..S8-10.
**All 31 IDs remain OPEN** (replay extension, validator executable, gate reach, final replays,
aggregate gate and blind audit are still due).

| Evidence for | S8 checked proposition (quantifiers as stated) | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual |
| --- | --- | --- | --- | --- |
| S8 / REQ-PRE-JOIN | `constructionAndQueryCapstone_holds : ConstructionAndQueryCapstone` (21 fields): both exactness theorems, both `ProgramContract` instances, the V3-4 leaf difference, the fuel body, `HeaderUse` at both constants, both input boundaries, the all-size zero family at `wordWidth n`, `BuilderRunFacts` of both constants (comparison model for every `xs`; word model under `InputFits (wordWidth n) xs`), the joint retained capacity with little-o residual, the accepted `FullyChargedPackedQueryCapstone`, `PackedQueryOn` on both emitted allocations, the 32-bit fit and lifted simulation of the query program, and the translated query on `efficientBuild xs` halting with the accepted answer within `queryBudget` steps. | `RMQ/Validation/PreprocessingContract.lean`: 120 exact-type projections, marker after a `sorry`-free witness (S8-8, S8-10). | Recorded limit (ruling Q3): no offset-relocated in-place query. | OPEN: replay cases on the capstone consumer, gate reach and audit are due. |
| S8 / REQ-PRE-COST | For every `xs`: the run of `builderProgram` at `builderBudget n` halts; `steps ≤ 1000000000 * n + 1000000000`; the ten categories partition the steps; `outBase - extent₀ ≤ 3200000 * n + 3200000`; every fuel prefix has extent `≤ extent₀ + (3200000 * n + 3200000) + (buildMemory xs).length`; the final extent is `outBase + (buildMemory xs).length`; registers `≥ 400` stay 0 at every fuel; code `8079` (`8089`) words; the same for `builderProgramWord` under `InputFits`. | `check_comparisonRun_work`, `_workspace`, `_prefixExtent`, `_peakExtent`, `_registerBank`, `_categoryPartition` and the word-model twins. | Literals crude; the fuel equals the work literal and halting is a separate field, so `steps ≤ fuel` alone is not the claim. | OPEN. |
| S8 / INV-STORE-IDENTITY, INV-TRACE-EXECUTION | The emitted cells are the actual run's final memory from its halt value (`outputCells`), and every output cell `outBase + i` was written `(outBase + i, (buildMemory xs)[i])` by a transition at some index `k` of the actual run with no later write to that address (`outputProvenance`); `replay` pins the final memory to the recorded write events. | `check_comparisonRun_outputCells`, `_outputProvenance`, `_replay`; builder consumer `calc_write_at`. | Positional provenance at the transition index of the same run. | OPEN. |
| S8 / INV-STORE-AGREEMENT, INV-READ-BACKING | Read-level and supplied-store agreement of the builder run (`readAgreement`, `suppliedAgreement`), and the accepted query's `readWidth`, `positionalReadBacking` and `suppliedMemoryAgreement` on `efficientBuild xs`. | `check_comparisonRun_readAgreement`, `_suppliedAgreement`, `check_queryOnEmitted_*`. | n/a | OPEN. |
| S8 / INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-WIDTH-SCALING | `Run.Safe (wordWidth n)` of the whole builder run (every transition `Prim.Safe` with a fitting post-state), the initial and final states fit `wordWidth n`, for both constants; the query side at the same `wordWidth xs.length` through `PackedQueryOn`. | `check_comparisonRun_runSafe`, `_initialFits`, `_finalFits` and twins. | n/a | OPEN. |
| S8 / REQ-PRE-INPUT, INV-ALL-SIZE | Comparison model: unconditional for every `xs : List Int`; word model: `InputFits (wordWidth n) xs`; zero input writes (`noInputWrites`: every write event addresses at least the initial extent, by the static pointer flow) and retention of the input below the extent and of the keys; `zeroFamily : ∀ n, InputFits (wordWidth n) (List.replicate n 0)`. | `check_comparisonRun_noInputWrites`, `_inputRetained`, `check_zeroFamily`. | Flow facts per phase (S8-2..S8-3); the flow of the whole source is defined. | OPEN. |
| S8 / REQ-PRE-MACHINE, INV-GLOBAL-PHYSICAL-MACHINE | `HeaderUse` at both constants (tail never writes register 1, per phase V3-9); every register operand below 400 (`arrayReflects`: the array-backed evaluator equals the run at every fuel); the accepted query translated to the construction instruction set runs step for step as the old run (`translatedQueryRun`). | `check_headerUse_*`, `check_comparisonRun_arrayReflects`, `check_translatedQueryRun`, `check_translatedQueryOnEmitted`. | n/a | OPEN: validator executable still due. |

## Replay extension evidence rows (REPLAY_EXTENSION, 2026-09-14)

Appended after the S8 rows; nothing above is changed. Changed surfaces:
`RMQ/Validation/Preprocessing.lean`, `lakefile.toml` (stanza), `Proof/Static.lean`,
`Capstone.lean` (two fields at the end), `Proof/RunFacts.lean` (one proof),
`RMQ/Validation/PreprocessingContract.lean` (two projections, axiom inventory),
`scripts/preprocessing_builder_check.lean` (safety definition pins),
`scripts/preprocessing_builder_replay.ps1`, `builder_cases.json` (52 cases);
commands in BUILDER_STAGE_LOG.md rows R-V1..R-V3 and R-1..R-6.
**All 31 IDs remain OPEN** (full replays on the committed tree, gate reach,
family and digestion entries, final checks, aggregate gate and blind audit are
still due).

| Evidence for | Checked proposition or executed check | Consumer / identity chain | Anti-vacuity attempt and outcome | Status and residual |
| --- | --- | --- | --- | --- |
| RE / CHK-PRE-CONTROLS, INV-VALIDATION-REACH | The compiled executable runs the actual `builderProgram` and `builderProgramWord` on eleven fixtures (empty, singleton, two, three with a tie, leftmost tie, increasing, decreasing and equal of length 24, cross-block, `n = 83`, `n = 129`) at fuel `builderBudget n`: halting, emitted cells equal to the reference `buildMemory xs`, the work and workspace literals, writes at or above the initial extent, and the accepted query on the emitted list against `scanWindow`. | `rmq_preprocessing_validate` (lakefile stanza); replay validator stage in full mode. | Negative controls N01-N04 (missing header, other-shape expected list, swapped cells, bit cells for dense words) fail with pinned messages (R-V3). | OPEN: the executable does not reach `n = 1116` (reference too slow); replay validator stage on the committed tree due. |
| RE / INV-CERTIFICATE-ANTI-BYPASS (condition C3) | Consumer-reaching weakening or sibling cases for `EvalG.compile_realizes'`, `SafeEval.compile_safe`, `run_write_at`, `run_load_at`, `writes_replay`, `run_agree_of_reads`/`run_agree_of_supplied`, `RunsTo.fuel_extension`, `Prim.SafeAt` (via `safety_safeAt_arms`; `Run.Safe` and `State.Fits` pinned by `Iff.rfl`), with `runArray_abstract` already B15. | Registry B35-B42; builder consumer lines 218, 228, 108, 123, 128, {154, 161}, 142, 450. | Each observed at exactly its line set with exact restoration (R-1, R-3); the `reserve`-arm drift was rejected at the producer and not registered. | OPEN: full 52-case replay due. |
| RE / REQ-PRE-COST, INV-ALL-SIZE (capstone consumer reach) | Weakened `BuilderRunFacts` fields (work `C`, workspace `Cw` and `Dw`, zero input writes, register bank) build and break exactly the two projections of the comparison and word runs; V3-7 (ii) `Cw` and `Dw` numerals in the capstone consumer break line 275. | Registry B45-B51 (`profile: capstone`); B52 accept control prints the capstone marker. | R-1. | OPEN: full replay due. |
| RE / REQ-PRE-COST (V2-7.6 quadratic control) | A stack step that first counts the current index down to zero is rejected by the stack-pass stage proofs. | Registry B43 (`profile: stackpass`), producer surface `Proof/StackPass.lean:287`. | R-1. | OPEN: full replay due. |
| RE / INV-ADDRESS-WIDTH, INV-WORD-WIDTH | `programStatic : ∀ n, ∀ i ∈ builderProgram, i.primitive.OperandsFit (wordWidth n) ∧ i.primitive.RegistersBelow 400 ∧ (∀ c t, i.primitive = .branchZero c t → t.val < builderProgram.length) ∧ (∀ t, i.primitive = .jump t → t.val < builderProgram.length) ∧ (∀ src, i.primitive ≠ .jumpRegister src)`, and `programStaticWord` for `builderProgramWord`: every instruction, executed or dormant. | `check_programStatic`, `check_programStaticWord` (capstone consumer). | n/a | OPEN. |
| RE / trust hygiene | `#print axioms` for the 259 S7 and S8 producer declarations (capstone consumer) and the 24 validator declarations: all within {propext, Classical.choice, Quot.sound}. | R-6. | n/a | OPEN: final trust scan due. |

## Replay extension records rows (REPLAY_EXTENSION_RECORDS, 2026-09-14)

Appended; nothing above is changed. Commands in BUILDER_STAGE_LOG.md rows R-7..R-10.

| Evidence for | Executed check | Identity | Outcome | Status and residual |
| --- | --- | --- | --- | --- |
| RER / REPLAY-EXACT-REGISTRY, INV-MUTATION-REPRODUCIBILITY | Full builder replay: executed IDs equal the 52 registered IDs in order; every case at exactly its registered stage and surface; restoration EXACT; contract replay 18 = 18. | HEAD `cb2ba2c`; builder registry `0bc1fba4...`; contract registry `aaec37a6...`. | PASS (R-7, R-8). | OPEN until the final review; aggregate gate and audit are coordinator steps. |
| RER / CHK-PRE-CONTROLS, INV-VALIDATION-REACH | The replay's validator stage built `rmq_preprocessing_validate` through Lake, ran it in full and ran N01-N04. | same run. | PASS (R-7). | OPEN until the final review. |
| RER / process | Builder gate deadline 10800 s = 2.36 x the measured 4573.59 s run. | `scripts/preprocessing_builder_gate.ps1`. | parser check on both hosts (R-9). | recorded. |

## Final candidate review (FINAL_CANDIDATE, 2026-09-14)

Appended; nothing above is changed. Author review of each frozen row against the
tree `babfbef` (Lean sources identical to `cb2ba2c`, on which R-7 and R-8 ran) and
the final checks R-11..R-14. "MET in author review" is not acceptance: the
coordinator's aggregate gate, a fresh blind exact-commit audit and coordinator
acceptance are still required.

| ID | Evidence on the candidate | Author status and residual |
| --- | --- | --- |
| REQ-PRE-CONTRACT | Contract phase: C1-C4, 15-case table, typed consumers, controls, aggregate gate and fresh blind audit (predecessor, `c1c970b`); continuation audit PRE-1-A1C conditions C1 (`361fe82`), C2 (`6df96d6`), C3 (`75a6301`, foundations `cb2ba2c`) landed. | MET in author review. |
| REQ-PRE-INPUT | `efficientBuild_eq_buildMemory : ∀ xs : List Int, efficientBuild xs = buildMemory xs` and `comparisonRun` (work, input boundary with `extent = 1` and the key oracle); `efficientBuildWord_eq_buildMemory` and `wordRun` under `InputFits (wordWidth xs.length) xs` with `wordInput` (`memory = encodeInput width xs`, `extent = n + 1`), header read (`HeaderUse` at both constants), `zeroFamily`; key reads and comparisons are counted transitions (`categoryPartition`). | MET in author review. |
| REQ-PRE-MACHINE | Closed constants with `ProgramContract ... (fun _ => builderProgram) 2107 8079` (uniform), frozen interpreter `run`, `categoryPartition`, `Run.steps` as work, firewall-isolated semantics (B01-B03, B44), conservative query translation `translatedQueryRun`. | MET in author review. |
| REQ-PRE-EXACT | Both exactness theorems over the actual runs (`outputCells`, `outputProvenance`); pipeline stages S3-S7; the equality includes the metadata words, paddings and dense repacking of `buildMemory xs`. | MET in author review. |
| REQ-PRE-COST | `C = D = 1000000000`, `Cw = Dw = 3200000`; `work`, `workspace` (below the output base), `prefixExtent` (every fuel), `peakExtent`, `inputRetained`, `registerBank` (400), code words 8079/8089 and `jointCapacity`; `runSafe`, `finalFits`, static facts, `noInputWrites`, `outputProvenance`. | MET in author review; literals crude, no tightness. |
| REQ-PRE-JOIN | `constructionAndQueryCapstone_holds` (23 fields): same `xs`, `efficientBuild xs`, `wordWidth xs.length`, builder runs, `PackedQueryOn (efficientBuild xs) xs` (leftmost half-open answers, invalid guard, `stepBound ≤ queryBudget`), `jointCapacity` with little-o residual, comparison and word corollaries as separate fields. | MET in author review under ruling Q3 (no relocated in-place query). |
| CHK-PRE-CONTROLS | Validator P01-P11 (empty, singleton, increasing, decreasing, equal, ties, cross-block, `n = 83`, `n = 129`) and N01-N04 (missing header, other-shape expected list, mismatched allocation, write-unit confusion); B43 quadratic mutation; B44 and contract C06/C07/C10/C15-C17 for semantic imports, oracle, baked program and code-payload bypass; stage-consumer threshold guards (S4 at `n` up to 24, 127, 129); all on the production constants or stage blocks, not a copied model. | MET in author review; residual: the `n = 1116` dense edge and the select-directory flag thresholds (R-14, from `n = 5489`) are not executable with the reference. |
| INV-STORE-IDENTITY | `queryOnEmitted` and `jointCapacity` are about `efficientBuild xs`, the cells the builder run leaves (`outputCells`). | MET in author review. |
| INV-VALUE-DEPENDENCY | Output cells are the run's final memory with positional write provenance; query answers come from the PQ1 run on those cells (`result`, `positionalReadBacking`). | MET in author review. |
| INV-SEMANTIC-NONVACUITY | `HeaderUse`, flow, ownership and provenance facts are derived from the run; weakening cases B04-B15, B35-B49 break consumers. | MET in author review. |
| INV-TRACE-EXECUTION | `replay`, `outputProvenance`, `categoryPartition` over `(run ...).transitions`. | MET in author review. |
| INV-STORE-AGREEMENT | `readAgreement`, `suppliedAgreement` (builder); `suppliedMemoryAgreement` (query). | MET in author review. |
| INV-READ-BACKING | `Run.Safe` load arm (in-extent present cell) for every builder transition; `positionalReadBacking` on the query side. | MET in author review. |
| INV-WORD-WIDTH | `runSafe`, `initialFits`, `finalFits` at `wordWidth n`; `memoryWordsFit` (query). | MET in author review. |
| INV-ADDRESS-WIDTH | Executed: `Run.Safe (wordWidth n)`; dormant code, register identifiers, operands, branch and jump targets: `programStatic`, `programStaticWord`. | MET in author review. |
| INV-INSTRUCTION-ATOMICITY | Frozen `Prim` of `Primitive.lean` (contract registry C01-C18 unchanged); no new constructor. | MET in author review. |
| INV-PROGRAM-ACCOUNTING | Programs are closed constants independent of `xs` (`ProgramContract` uniform); code words in `jointCapacity`. | MET in author review. |
| INV-ORACLE-INDEPENDENCE | Validator expected cells from `buildMemory xs`, answers from `scanWindow`. | MET in author review. |
| INV-VALIDATION-REACH | `rmq_preprocessing_validate` imports `Builder.Program` and `Construction.ArrayRun` and runs both constants (R-7, R-11g). | MET in author review. |
| INV-ALL-SIZE | Every theorem quantifies all `xs` (word model: `InputFits` only); no readiness premise; `zeroFamily`. | MET in author review. |
| INV-PROOF-SEPARATION | The builder programs carry no proof fields; certificates are `Prop` structures. | MET in author review. |
| INV-NO-SYNTHETIC | All facts are about `run builderProgram (builderBudget n) s0` itself. | MET in author review. |
| INV-CATEGORY-SEPARATION | Payload bits (`jointCapacity`), machine state and ticks (`Run`), proof fields and the validator's wall-clock timings are kept apart; no timing is claimed as model cost. | MET in author review. |
| INV-PUBLIC-COMPOSITION | One structure about the same construction, width and validity domain. | MET in author review. |
| INV-CERTIFICATE-ANTI-BYPASS | Every capstone field projected at full type (122 projections); registry cases B14-B15, B35-B51 show weakenings break exactly the projections. | MET in author review. |
| INV-MUTATION-REPRODUCIBILITY | Versioned builder (52) and contract (18) registries; full replays PASS with exact restoration (R-7, R-8). | MET in author review. |
| INV-GLOBAL-PHYSICAL-MACHINE | The builder runs on one store from the input state; every transition is safe and no access fails. The query side is the accepted PQ1 evidence on the emitted list; no single physical execution of builder and query is claimed (ruling Q3). | MET in author review under ruling Q3. |
| INV-WIDTH-SCALING | One `wordWidth n` for builder and query; `bankcap_wordWidth`, `cap_wordWidth`, `length_lt_wordWidth`. | MET in author review. |
| REPLAY-EXACT-REGISTRY | Executed = expected (52, 18), pinned registry hashes. | MET in author review. |
| REPLAY-SELECTOR-NONVACUITY | Selector boundary self-tests in both runners (full replays). | MET in author review. |
| REPLAY-SUBPROCESS-DEADLINE | Owned bounded children, deadline self-tests, restoration in `finally`; builder gate 10800 s = 2.36 x measured. | MET in author review; the POSIX branch is uncovered on this Windows host (recorded, not passed). |

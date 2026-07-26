# RMQ Endgame Roadmap: Final Architecture Adjudication

Prepared: 2026-07-25

Governance: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`

Governed base: `bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4`

Base tree: `e182bd19531060a422e881ce8889279a1f0494bf`

Runway: approximately four weeks to V1 verification and submission freeze

This document is the candidate replacement internal endgame roadmap. It becomes
canonical only after independent audit and owner ratification of this exact
delta. Once ratified, it supersedes the sequencing and architecture
recommendation in the rejected
`RMQ_ENDGAME_PLAN.md` candidate at
`0e71b828ae975ba42881edf4c023813e80f070a0`, while preserving that candidate,
the A09 report at `930a610623c76ee789346f3c6c8c7510cc0d4adb`, and the
subsequent Claude/Codex audit exchange as process evidence. It does not alter
an accepted theorem, record coordinator acceptance, authorize a merge or push,
or itself make a public claim.

## Executive decision

The primary endgame target is a **counted-header, packed-storage cell-probe
refinement** of the canonical succinct RMQ construction.

Status: **FEASIBILITY CANDIDATE**, not accepted and not
`READY_TO_EXECUTE`.

The intended public theorem is conventional enough that a reviewer can
pattern-match it against the standard succinct-data-structure model:

> For every input list of length `n`, preprocessing constructs one read-only
> array of exact-width `w(n)`-bit cells, where checked all-size lower and upper
> bounds yield the conventional logarithmic-width corollary. Its complete
> allocated capacity, including a constant serialized header and final-cell
> padding, is at most
> `2n + rho(n)` bits for a checked `rho = o(n)`. For every valid half-open query
> `[left, right)`, a closed uniform controller given only `n`, the endpoints,
> and words returned by probes into that same array returns the leftmost
> minimum index after at most `C` adaptive probes, for one exact constant `C`
> independent of `n`.

Computation between probes is free, as in the cell-probe model. Semantic shape,
the source list, proof fields, a sibling logical store, uncounted advice, and
unaccounted lookup tables are not controller inputs.

The old B2/B3/B4/A4 small-step selector campaign is **banked research, not a V1
gate** during this runway. Its evidence remains useful, but continuing it now
would spend the remaining time completing a bespoke execution architecture
before establishing the more familiar physical-storage theorem.

This is an explicit proposed owner amendment to the V1 coordination DAG, not a
claim that PRELOGIC or the old route predicates were false. The packed
cell-probe node is a new release route outside the old A4 selector. If the old
selector is ever resumed, its original dependency law still applies: B4 is an
`adapterOfBase` downstream of a B2 or B3 receipt, and A4 cannot run without
terminal B2 and B3 dispositions. The amendment becomes governing policy only
after this roadmap delta receives its own independent audit.

The fallback is the integrated M1 theorem surface plus the current U3 theorem
chain. This fallback must not be called a certified combined floor yet:

- M1 is accepted and integrated.
- U3 is kernel-checked and recorded as candidate complete, but its
  coordinator-owned fresh-blind exact-commit audit remains open.

If Stage F returns `CHECKED_OBSTRUCTION` or
`RUNWAY_PIVOT_UNRESOLVED`, the remaining runway certifies U3, freezes the
honest M1/U3 claim, completes the manuscript and artifact, and records either
the exact checked obstruction or the exact unresolved residual surface. It
does not resume a broad architecture search. `ARCHITECTURE_DECISION_REQUIRED`
instead stops both paths for the owner.

If the U3 audit finds a material defect, the fallback is unavailable until U3
is repaired and re-audited or the `210` conjunct is removed and the narrower
fallback is re-audited.

No final architecture claim reaches README, paper, artifact, or public
headlines until the selected exact commit has passed coordinator
reconstruction and the required fresh-blind audit.

## Success standard

The endgame succeeds when a skeptical reviewer can identify, without
reverse-engineering project history:

1. one `2n + o(n)` representation object;
2. the complete allocated capacity of that object, not only its logical payload
   erasure;
3. one query whose only dynamic data access is by probes into that object;
4. one exact constant probe cap derived from the executed physical trace;
5. one same-object correctness theorem for half-open RMQ with leftmost ties;
6. one explicit boundary between free controller computation and counted
   memory;
7. one public theorem and one checked expected-type consumer that compose all
   five facts over identical objects and guards;
8. a replayable mutation campaign showing that shape, sibling-store, failed-
   probe, disconnected-trace, and public-consumer bypasses are rejected;
9. a complete manuscript, claim map, novelty log, and reproducible artifact at
   the exact audited release commit.

Linear preprocessing time, construction workspace, conventional word-RAM
instruction time, and extracted C/Rust execution are desirable strengthenings,
not V1 gates. They must be stated as open unless separately proved.

## Evidence and status discipline

Use the repository evidence tiers from `AUDIT_PROTOCOL.md`:

1. kernel theorem;
2. theorem about the explicit model, store, or trace;
3. executable validation;
4. reproducible artifact or CI evidence;
5. process evidence.

The labels in this roadmap are exact:

- **ACCEPTED**: coordinator-reconstructed and any mandatory fresh audit passed.
- **CANDIDATE**: committed theorem or artifact work that has not closed the
  acceptance chain.
- **REJECTED**: not part of the governing frontier; useful failures remain
  immutable evidence.
- **DRAFT**: prompt or plan artifact, never proof evidence or launch authority.
- **UNRESOLVED**: neither a positive witness nor a quantifier-matched negative
  theorem exists.

Agent reports, audit prose, and the uncommitted B2SUFF investigation may guide
the next theorem target but cannot satisfy an acceptance row.

## Reconstructed frontier

| Surface | Exact identity | Status and meaning |
|---|---|---|
| Governance | `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` | Governs skills and workflow policy |
| Main | `bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4`, tree `e182bd19531060a422e881ce8889279a1f0494bf` | Clean governed base for this roadmap |
| U2 | `4f7ec8be47ecd65b2859a3784fadeab48a629e4e` | Accepted uniform directory route |
| U3 | candidate `880dfdfd7409d5dbdfd226921a701055f3ec0fd7`; migration `f6000c3ee1cc8d5b04201257b8226bb7952ef051`; integration `0b8490cb1dee4f02e7c72a5e097c1fa78361c588` | Kernel-checked `210` chain is integrated; roadmap node remains candidate/open pending fresh-blind acceptance |
| M1 | candidate `977a4df8b5d9e908fe66d012dd242006790ebaf3`, audit report commit `e7c936d8a070a1db26e87b60c656044ee8a37b56` | Accepted and integrated under supplied-store scope |
| E1 B1 shared image | candidate `1727de15f2030bfb9296a9b31508bc00581aa33a`; audit `728174e2c049a29acf19d34661dfec6ebcde49fb` | Accepted branch-local validation prerequisite, off-main at `bc5851ad...`; not a `2n + o(n)` allocated packed representation |
| PRELOGIC/PRECUR/PREHIST | `d3a23540b124e8c7b9a5306d5c616954372e56d2`, `517317117c07858ebd8be6f71bc8c73ef353c935`, `50c5f8ccf7be83a56b90a6c29142ac32860f0a27` | Accepted branch-local research reports, off-main at `bc5851ad...`; not route verdicts or integrated theorem surfaces |
| B2 R1 | `83d9b1223bb018e5889b693400d39e955a1438a7` | Rejected proxy obstruction |
| B2 R2 | `b2d8b1a756927cd2566b4373826e774846507b5f` | Rejected disconnected opcode-list and host-projection surface |
| B2 R3 | `250fba1685411089825cbb8245a4fc3180678e77` | Valid refutation of stale frozen G10; not a B1/Core impossibility proof |
| B2 R4 prompt | `docs/internal/e1_arch_prompts/E1_ARCH2_B2DESC_R4_PROMPT.md` | Draft/not launched; do not launch unchanged |
| B3 source port | `c19061629ce8cf1e78992a99346170edd84b4971` | Accepted branch-local source/interface prerequisite, off-main at `bc5851ad...`; not a route |
| B3 R2 | `5973d5d549fc37575820aa6fb4cc648a0a33452e` | Audited `INCOMPLETE`; arithmetic expressibility, no route |
| B3 R3 | `5a786227008d346c974023ce4e5c3fc6982f3157` | Audited `INCOMPLETE`; operational multiplication correspondence candidate, no route verdict |
| B4/A4 | no accepted route candidates | Unresolved and frozen for this runway |
| Historical machine companion | `648e51247f6c07663008ba2955a98e03b4a1ba4f` | Kernel-complete for its own old contract, unmerged and unaudited; not the primary architecture |
| Rejected endgame plan | `0e71b828ae975ba42881edf4c023813e80f070a0` | Rejected strategy target; preserve as evidence |
| A09 report | `930a610623c76ee789346f3c6c8c7510cc0d4adb` | Process evidence; useful findings, not architecture acceptance |
| B2SUFF investigation | no branch, commit, declaration inventory, or replay | Non-durable partial evidence only |

### Live theorem anchors and the exact missing composition

The replacement starts from checked mainline theorems rather than reconstructing
the RMQ theory:

- `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` and
  `RMQ.SuccinctClassic.listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`
  compose the logical `buildPayload.length <= 2n + overhead n`, little-o
  witness, exact list semantics, canonical trace, and current cost story.
- `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`
  checks the literal `210`; the same-execution theorem
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210`
  bounds the canonical trace.
- M1's
  `RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`,
  `listIntFinalFullModelCostLeOfFootprintGlobal`, and
  `listIntFinalFullModelSoundnessExactOfFootprintGlobal` establish the accepted
  supplied-store transfer boundary.
- `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack` exposes the accepted
  fixed-length information-theoretic lower-bound package.

The missing capstone is not another RMQ-answer theorem. `buildPayload.length`
does not bound the allocated cell array: the current reviewer theorem flattens
away final padding, empty sentinels, and unused allocation. Moreover,
`queryTraceResultWithStore` passes `cartesianShape xs`, and
`concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore` accepts
`shape` directly to compute translated addresses. The feasibility gate must
replace that free semantic input with counted data and prove complete
allocation, closed control, and attempted-probe totality over the same object.

## What the E1-ARCH research established

The E1 campaign was not wasted by the model pivot. It exposed precisely which
parts of a plausible machine theorem are easy to fake and which inputs a
physical query must actually possess.

### Accepted and reusable results

- B1 constructed one all-size validation-local image and identical route-input
  aliases. It clarified descriptor, padding, sentinel, dead-cell, width, and
  shared-package obligations. Its header is not the constant serialized header
  proposed here: its package carries **six computational fields and forty-seven
  proof-only fields** (`1727de15:docs/internal/DESIGN_DECISIONS.md:4872-4873`),
  plus one word-length cell per physical payload word, and its image theorem
  has only a loose linear-cell envelope. The corrected numbers strengthen the
  point rather than weaken it: forty-seven of those fields are proof-only and
  cannot be serialized into counted cells at all, so B1's package is further
  from a constant serialized header than a bare field count suggests. Stage F
  must prove the new header and allocation independently.
- PRELOGIC fixed the route predicate relationships and the old A4 selector
  structure.
- PRECUR inventoried current-route arithmetic, reads, literals, widths, and
  traces.
- PREHIST reconstructed the historical 5,646-instruction, twelve-constructor
  source program and its simulation obligations.
- The B3 source-port task produced an accepted 56-module validation-local
  interface and a replay whose two-commit parser was repaired.
- B3 R2 proved that the required multiplication and division recursions are
  expressible without inventing a new source primitive.
- B3 R3 connected the multiplication block to actual `targetIterate`
  microsteps in an arbitrary containing program. Its audit still classifies the
  full route `INCOMPLETE`.

### Rejected surfaces that now serve as regressions

- **Proxy obstruction:** absence of a direct opcode or registry entry does not
  negate an allowed construction.
- **Disconnected execution:** opcode tags, list lengths, or a theorem about an
  adjacent helper do not prove a program computes the helper.
- **Uncharged semantic projection:** `shape.size`, `Nat.log2 shape.size`,
  proof fields, or sibling packages cannot stand in for runtime data.
- **Weak expected-type consumers:** pinning names or lengths does not pin an
  object-composition theorem.
- **Frozen-contract drift:** R3 soundly refuted the old G10 clause, but current
  definitions use long and sparse `blocksPerSuper = 1`; old G06 used `N /
  blockSize` instead of accepted `N / base`; old G14 incorrectly made a
  universal length equality across the empty sentinel case.
- **Non-replayable mutation evidence:** an out-of-tree mutation campaign or a
  failing committed extractor is not acceptance evidence.
- **Deadline and parser hazards:** fixed two-second process races and joined
  `rev-list` hashes produced false failures before being repaired.

### Findings from the endgame audit chain

- A09 correctly found missing allocated-capacity accounting and missing
  valid-query probe-totality accounting.
- A09 correctly rejected the raw all-ones dead-cell blocker:
  ordinary width-`w` decoding yields `2^w - 1`.
- A09 incorrectly extended that criticism to DD-20260725-003, whose rationale
  explicitly concerned the forbidden historical shifted decoder; that
  conditional decoder would yield `2^w`.
- The later architecture review isolated the decisive gap: the canonical
  evaluator receives the full semantic `shape` for free. Free arithmetic is
  lawful in cell-probe; free data-dependent shape is not.
- The B2SUFF narrative checked representatives, not a durable universal
  certificate. `G24` by `rfl` only unfolds a size-derived expression and does
  not prove counted-header decoding, consumption, allocation, or shape
  elimination.
- The `210` arithmetic is kernel-checked and M1's scoped fresh audit positively
  reconstructed it. That is not the same as accepting the whole U3 release
  lineage.
- `nonSyntheticWeight` and `TraceResult.toCosted`, not
  `isWordPrimitive`, are the relevant cost semantics. The canonical route
  proves emitted events are reads; a hypothetical primitive event would still
  be charged by the current trace-length cost.

## Architecture option comparison

| Option | Reviewer precedent match | Remaining proof risk | Runway fit | Disposition |
|---|---|---|---|---|
| Constant counted header + packed physical cells + cell-probe query | High: one packed representation, `w`-bit cells, adaptive constant probes, free computation | Medium: complete geometry factorization, packing/allocation, same-object trace | Best plausible primary route | **Primary feasibility candidate** |
| Direct S1 lift or n-budget padding rewrite of canonical payload | Medium-high, but changes the highest-blast-radius object and public space chain | High | Poor unless the header route formally fails | Reserve as decision-flip alternative |
| Full B2/B3/B4 small-step machine and A4 selector | Strong execution story but bespoke granularity; substantial simulation and registry remainder | Very high | Does not fit the primary four-week path | Bank; post-V1 strengthening |
| Merge historical `648e512...` machine companion | Honest theorem at old logical-store granularity; collision-heavy and not same packed object | High integration/audit cost | Poor | Post-V1 evidence only |
| Current M1 + U3 theorem surface | Honest and largely landed, but not one allocated packed queried object | Low after U3 audit | Reliable fallback | **Fallback; U3 audit required** |

The primary option is chosen because it removes the largest reviewer
brainpower tax with the smallest new abstraction. It follows Fischer's
non-systematic `2n + o(n)` constant-query representation and the standard
cell-probe convention used in RMQ lower-bound work: memory is an array of
fixed-width cells, probes are charged, and computation between probes is free.
The target is deliberately not called word-RAM time.

Primary precedent:

- Johannes Fischer, *Optimal Succinctness for Range Minimum Queries*:
  <https://arxiv.org/abs/0812.2775>
- Mingmou Liu and Huacheng Yu, *Lower Bound for Succinct Range Minimum Query*:
  <https://www.cs.princeton.edu/~hy2/files/suc_rmq.pdf>
- Affeldt, Garrigue, Qi, and Tanaka, *Proving Tree Algorithms for Succinct Data
  Structures*: <https://doi.org/10.4230/LIPIcs.ITP.2019.5>

These sources justify the model vocabulary, not this project's theorem. The
Lean acceptance matrix below must establish every project-specific link.

## Frozen target model

The implementation round may choose Lean names, but it may not weaken these
objects.

### Representation

Before the per-input quantifier, freeze one literal header arity `K`, one exact
width function `w`, one overhead function `rho`, one literal probe cap `C`, one
aligned-cell semantics, and one controller/program definition. There is one
uniform family quantified over every `xs` and every `n = xs.length`; only the
constructed memory contents vary with `xs`. No per-instance program, schema,
or proof callback may vary with the input.

For each input:

- `w(n)` is one exact frozen function. The theorem proves explicit all-size
  inequalities such as `1 <= w(n)`, `n < 2^(w(n))`, and
  `w(n) <= K_w * (Nat.log2 (n + 1) + 1)` for one literal `K_w`; asymptotic
  `Theta(log n)` prose is only a corollary;
- `headerBits xs` serializes a fixed number `K` of width-bounded descriptor
  fields;
- `payloadBits xs` is definitionally the exact canonical `buildPayload xs`;
  choosing a representation-equivalent replacement requires a new owner
  amendment and audit rather than being an implementation freedom inside this
  gate;
- `serializedBits xs = headerBits xs ++ payloadBits xs`;
- `memory xs` is the fixed-width chunking of `serializedBits xs`, including
  only explicitly counted final padding and any explicitly justified sentinel
  cells.

Prefer no dead or failed-read cells in the primary model. If a sentinel or dead
cell is retained, its full allocated width and every reachable probe to it are
counted.

### Query

The packed query is a closed uniform controller with dynamic inputs exactly:

- `n`;
- `left` and `right`;
- the contents returned by previous probes into `memory xs`.

Fixed schema constants may be part of the program. Input-dependent lookup
tables, semantic shape, `xs`, proof objects, a sibling store, expected answers,
and source-program inspection are forbidden. An arbitrary total Lean function
is model-faithful only after this complete dependency closure is checked.

One probe reads one aligned `w(n)`-bit array cell at one integer index. An
unaligned logical span crossing two cells costs two probes; the same rule
applies to header fields. A slice operation may be free only after all cells
containing the slice have appeared as ordered probe replies.

### Required theorem shape

The final capstone must combine over the same `xs`, memory, query, trace, and
validity guard:

1. `rho` is little-o linear;
2. `memory xs` has cell width `w(n)`;
3. `memory xs`'s complete allocated capacity is at most `2*n + rho n`;
4. every trace event is an attempted probe of `memory xs`;
5. every attempted address is in range and returns the indexed cell;
6. trace order and multiplicity are preserved;
7. trace length is at most one derived numeral `C`, independent of `n`;
8. the query result is the reference half-open, leftmost-tie RMQ result;
9. the controller's data dependencies are exactly the allowed inputs.

The cap may equal `210` plus descriptor/packing overhead, or another constant.
It must be derived from the physical trace. Reusing `210` by prose is forbidden;
a logical word read that straddles physical cells may require two probes.

## Stage F: mandatory 5-7 day feasibility gate

No full implementation prompt is launchable before this gate has a frozen
matrix and passes prompt preflight. Run one proof worker, one read-only
precedent/audit lane, and no competing heavy B3 worker.

| ID | Feasibility requirement | Minimum evidence |
|---|---|---|
| `EG-CP-F01-HEADER-SCHEMA` | Freeze `K`, every field, encoding, word width, and small-size behavior | Checked definitions and all-size arity/width theorems |
| `EG-CP-F02-HEADER-CONSUMPTION` | Header values are obtained from counted cells and are actually used | Executed read trace plus value equality; no host mirror |
| `EG-CP-F03-GEOMETRY-CLOSURE` | Every data-dependent offset, length, branch, divisor, and table selector factors through `n`, endpoints, header words, and prior probes | Exhaustive typed inventory for every current logical-read source and universal consumers, not representative rows |
| `EG-CP-F04-PACKING` | Define pack/unpack, field spans, boundary crossing, and exact bit erasure | Round-trip and slice theorems |
| `EG-CP-F05-ALLOCATED-SPACE` | Define allocation as `memory.length * w(n)`; count header, every cell, final padding, sentinel/dead cells, and prove `2n + o(n)` | All-size capacity theorem plus little-o proof |
| `EG-CP-F06-CLOSED-CONTROLLER` | Remove semantic shape and every sibling/oracle input | Closed signature, expected-type dependency consumer, and cross-shape transcript determinism for equal allowed inputs/probe replies |
| `EG-CP-F07-PROBE-TOTALITY` | Every valid-query attempted probe is in range and successful | Theorem over all valid queries; attempted, not merely successful, reads |
| `EG-CP-F08-PHYSICAL-CODEC-AND-CAP` | Give a universal packed codec for all 23 logical segments / 22 physical source layouts, including aliases, empty/sentinel cases, and cell crossings; derive an `n`-independent physical cap | Same-trace theorem with order/multiplicity and at-most-two-cell lowering for each logical word |
| `EG-CP-F09-END-TO-END-SLICE` | Execute at least one complete nontrivial route slice against packed cells and connect its result to the existing semantics | Kernel theorem plus pinned executable fixture |
| `EG-CP-F10-ANTI-BYPASS` | Reject shape, source-list, proof-oracle, uncounted-table, disconnected-trace, forged-count, and sibling-store mutations | Committed replay with exact expected failures and unchanged accept control |
| `EG-CP-F11-BOUNDARIES` | Empty representation, singleton, threshold, valid, reversed, empty-range, and out-of-range query behavior are explicit | Checked theorem/fixture matrix |
| `EG-CP-F12-RESIDUAL-ESTIMATE` | Close the dependency inventory and estimate the exact remaining theorem surface | Coordinator-reviewed path/theorem inventory; no unknown dynamic input |
| `EG-CP-F03` ordering | **Front-load F03 within Stage F** (Day-0 amendment) | F03 is the row most likely to yield `CHECKED_OBSTRUCTION`: it is the only exhaustive-and-universal requirement, and the B2SUFF narrative that made it look nearly closed was representative rows without a durable artifact. Discovering an F03 failure on gate day 6 wastes the gate. Attempt F03's inventory to completion, or to a named non-derivable value, before broad F04/F08/F09 work. |
| `EG-CP-F13-NO-ASSUMED-CAPSTONE` | Every reachable controller state, next address, reply, and final result is produced by the packed execution under one explicit invariant; final correctness is not stored in a field, hypothesis, or precomputed answer | Base/step/final invariant, decisive-cell corruption rejection, and a proved-unread-cell expected-accept control |

### FEASIBILITY_PASS rule

Record `FEASIBILITY_PASS` and proceed to a separately frozen implementation
only if:

- F01-F08 are closed by kernel/model theorems, not prose;
- F09 demonstrates the intended composition on the real packed store;
- F10 has at least one discriminating counterfactual per reusable failure
  family;
- F11 exposes no small-size model split;
- F12 estimates at most ten further focused proof-days and names every remaining
  consumer;
- F13 rules out a controller that merely replays a shape-generated trace or
  carries the capstone as state.

This outcome may establish representation feasibility; F09's one route slice
is not the final route theorem. The gate may not record architecture
acceptance.

### CHECKED_OBSTRUCTION rule

Record `CHECKED_OBSTRUCTION` only if one of the following is established over
the frozen objects and quantifiers:

- the required header has input-dependent arity or non-`o(n)` allocated space;
- a route-controlling value cannot be reconstructed from allowed inputs;
- semantic shape or an equivalent sibling object remains a dynamic input;
- physical probe expansion is not bounded by a constant independent of `n`;
- the same-object result theorem is incompatible with the frozen public RMQ
  semantics.

A local tactic failure, timeout, one inconvenient encoding, or an expired
schedule is not a mathematical obstruction.

### RUNWAY_PIVOT_UNRESOLVED rule

Record `RUNWAY_PIVOT_UNRESOLVED` when no checked obstruction exists but F12 gives a
reviewed residual estimate beyond the remaining proof budget, or the gate
deadline arrives with a named open theorem surface. Preserve every closed row,
state `UNRESOLVED` mathematically, switch the V1 critical path to the audited
fallback, and leave the packed lane resumable after V1 without pretending that
an impossibility was proved.

### ARCHITECTURE_DECISION_REQUIRED rule

Stop for explicit owner judgment, without recording any of the three outcomes
above, if progress would require changing RMQ semantics, adding a new
primitive/cost model, allowing input-dependent advice, counting an unaligned
span as one probe, replacing `buildPayload` outside the frozen object, or
resolving a genuine Core/B1 semantic conflict. A broad rewrite that is merely
too large for the runway is `RUNWAY_PIVOT_UNRESOLVED`, not this status.

## Stage A: packed architecture acceptance

After `FEASIBILITY_PASS`, freeze a new implementation matrix. The following
rows are the minimum node-closure contract:

| ID | Acceptance requirement |
|---|---|
| `EG-CP-A01-ONE-OBJECT` | Space, query, trace, and result use the identical `header ++ buildPayload ++ padding` packed memory object |
| `EG-CP-A02-SPACE` | Complete allocated capacity is `2n + o(n)` |
| `EG-CP-A03-WIDTH` | One exact query-independent width function satisfies the frozen explicit all-size lower/upper bounds for cells, fields, and addresses |
| `EG-CP-A04-HEADER-SUFFICIENCY` | All controller geometry is decoded from counted header/probe data |
| `EG-CP-A05-PROBE-SEMANTICS` | Every attempted probe is one aligned fixed-width indexed read of the same memory; cell crossings cost multiple probes |
| `EG-CP-A06-PROBE-CAP` | Exact derived numeral `C`, preserving order and multiplicity |
| `EG-CP-A07-CORRECTNESS` | All valid half-open queries return the leftmost reference RMQ answer |
| `EG-CP-A08-INVALID-DOMAIN` | Invalid/reversed/empty/out-of-range behavior is stated without weakening A07 |
| `EG-CP-A09-UNIFORMITY` | Closed controller has no semantic shape, input list, proof oracle, uncounted advice, or hidden table |
| `EG-CP-A10-NO-ASSUMED-CAPSTONE` | Reachable-state invariant and corruption/nonvacuity theorems show that packed execution, not an assumed answer or shape-generated replay, produces the result |
| `EG-CP-A11-PUBLIC-CONSUMER` | Independent expected-type consumer pins the full combined proposition |
| `EG-CP-A12-REPLAY` | Exact registry, selectors, mutations, deadlines, restoration, and clean-state controls |
| `EG-CP-A13-CAPSTONE-AUDIT` | Fresh-blind exact-commit audit and coordinator reconstruction pass |

The worker may report only `CANDIDATE_COMPLETE`. Only the coordinator records
local acceptance after A13. Public synchronization and V1 remain separate
roadmap nodes.

Feasibility-to-production mapping is explicit:

- F01/F05 witness A02/A03;
- F02/F03/F06/F13 witness A04/A09/A10;
- F04/F08 witness A01/A05/A06;
- F07 witnesses A05;
- F09 is only a composition witness toward A07, never A07 itself;
- F10/F11 witness A08/A12;
- F12 controls scheduling and proves no mathematical row.

## Four-week execution schedule

Stage F is **5–7 focused engineer-days**, not merely elapsed calendar days.
The matrix records an owner, start timestamp, used focused days, and a hard
calendar cutoff before launch. The coordinator owns the gate until explicitly
delegated.

### Day 0: govern the roadmap

- Audit this exact roadmap delta as a roadmap/architecture artifact.
- Apply one continuation only for literal findings; use a fresh audit if a
  material model or gate change results.
- Prepare the feasibility prompt from the accepted roadmap, freeze F01-F13,
  complete reusable failure-mode feedback, and run
  `worker_prompt_preflight.ps1`.
- Do not reuse the B2 R4 draft unchanged.

### Week 1: decide feasibility and secure the fallback

Primary proof lane:

- run Stage F against a fresh governed branch;
- one heavy Lean process at a time;
- front-load F01-F07 before broad query composition.

Independent lanes:

- commission the missing U3 fresh-blind exact-commit acceptance audit, or
  freeze an explicit release-audit scope that genuinely reconstructs the whole
  current U3/`210` surface;
- inventory and land durable acceptance evidence needed at the release commit;
- start the manuscript skeleton and novelty-search log;
- correct current claim prose about allocation, preprocessing, model scope,
  and the `210` audit lineage on a separate docs branch.

Friday decision:
`FEASIBILITY_PASS`, `CHECKED_OBSTRUCTION`, or
`RUNWAY_PIVOT_UNRESOLVED` under the rules above, unless
`ARCHITECTURE_DECISION_REQUIRED` has stopped the gate for the owner. No
ambiguous partial pass, and no schedule failure labeled as impossibility.

### Week 2: close the selected theorem surface

If `FEASIBILITY_PASS`:

- construct the packed memory and header;
- prove full allocated space, width, header sufficiency, and physical probe
  semantics;
- port the canonical query by a checked refinement rather than a parallel
  answer oracle;
- derive the physical cap from the actual trace.

If `CHECKED_OBSTRUCTION` or `RUNWAY_PIVOT_UNRESOLVED`:

- stop new architecture implementation;
- preserve the exact obstruction or unresolved residual surface and every
  reusable packing lemma;
- certify U3 and freeze the honest M1/U3 fallback theorem and wording;
- redirect proof capacity to claim correspondence and artifact checks.

**If the U3 audit itself returns a material defect** (Day-0 amendment): the
fallback is unavailable as stated, and week 2 has no slack to repair and
re-audit a cost chain. The named sub-fallback is therefore **M1 alone with the
`210` conjunct removed**, re-audited on its own narrower surface, with the
cost claim restated as the checked per-execution bound rather than the
all-size literal. Decide this within one working day of the U3 verdict; do not
spend week 3 attempting a U3 repair that the runway cannot absorb.

Both paths:

- extend the executable harness to at least `2^15` inputs when practical;
- report payload overhead, model probes/cost, and wall-clock time in separate
  columns;
- keep the manuscript lane active.

### Week 3: capstone, claims, and manuscript

If `FEASIBILITY_PASS`:

- close A01-A12 and the public expected-type consumer;
- run focused validation and one final aggregate gate on the unchanged tree;
- prepare the fresh-blind audit packet without the worker's verdict.

Both paths:

- complete the manuscript draft;
- finish primary-source related work and the per-venue novelty log;
- verify the exact 18-surface registry, policy version/hash, and Lean
  comment/docstring inventory in the synchronization contract below;
- synchronize only the claims supported by the selected accepted theorem.

Do not restart B3, B4, A4, the historical companion merge, or a broad Core
refactor because the primary lane finishes early. Spare capacity goes to
falsification and artifact reproducibility.

### Week 4: V1 freeze

- pinned Linux CI with stored logs and timings;
- project hygiene, axiom, trust, import, claim-drift, and design-decision gates;
- advisory independent checker where supported;
- exact theorem map, claim correspondence, related work, novelty log, artifact
  instructions, license, and code map;
- DOI-ready and, if needed, anonymous artifact bundle;
- fresh-blind audit of the exact release candidate;
- only audit repairs and manuscript polish after the freeze begins.

No new architecture branch starts in week 4.

## Continuous manuscript and evidence lanes

The proof result is not the submission. From day 1:

- the coordinator owns the manuscript lane until it is explicitly delegated;
- create the canonical source at `paper/rmq.tex`, bibliography at
  `paper/references.bib`, and build instructions at `paper/README.md`;
- freeze the target venue and page/appendix constraints by the end of focused
  day 2;
- require a clean PDF build from the documented pinned toolchain, complete
  theorem-reference resolution, and no draft placeholders before V1;
- assemble that paper from the existing theorem maps and claim correspondence;
- state the selected model before presenting constants;
- keep `2n + o(n)` payload bits, complete allocated bits, probe count, project
  model cost, and Lean wall-clock time distinct;
- never say "word-RAM time" for a cell-probe theorem;
- never imply practical crossover or Fischer-Heun redundancy parity from a
  loose `o(n)` envelope;
- state construction time/workspace as open unless proved;
- measure actual overhead without substituting measurements for the space
  theorem;
- make every manuscript claim resolve to an exact theorem at the release
  commit.

Novelty wording remains provisional until the search log covers at least the
AFP, Rocq/Coq package corpus, Lean libraries, ITP/CPP/JAR/JFP proceedings, the
Affeldt succinct-data-structure lineage, and current verified low-level
algorithm work.

## Exact public-claim synchronization contract

At governed base `bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4`,
`docs/internal/CLAIM_DRIFT_POLICY.json` is version `23`, Git blob
`437e37e171d974c4821d6e38c0115025a2fe4e02`, 16,717 bytes.
The release synchronization task must record the then-current version and blob
identity again; if the policy changes, regenerate this inventory and audit the
change.

**Pin the Git blob, never a working-tree SHA-256** (corrected 2026-07-25).
The same file yields at least three different SHA-256 values depending on how
it is read: `155BEB68…` from a Windows CRLF checkout, and
`a5b3bb63…` from the LF blob bytes. An earlier revision of this roadmap pinned
the CRLF value, which is correct only on Windows — CI runs Ubuntu, so a Linux
auditor executing that contract would compute a different digest and wrongly
conclude the policy had been tampered with. The Git blob identity is
platform-independent, is what every other exact citation in this project uses
(`blob be80468e…`, `blob 086abee6…`), and is therefore the required form. This
is the same hazard that forced the `.gitattributes -text` rule for the archived
prompt artifacts; do not re-import it.

The current policy registers exactly these 18 Markdown fact surfaces:

1. `README.md`
2. `artifact/CLAIMS.md`
3. `artifact/README.md`
4. `docs/FAMILY_SUMMARY.md`
5. `docs/PAPER_CLAIM_CORRESPONDENCE.md`
6. `docs/PAPER_MAIN_THEOREM.md`
7. `docs/PAPER_MODEL_ADEQUACY.md`
8. `docs/PAPER_THEOREM_MAP.md`
9. `docs/WHAT_IS_PROVED.md`
10. `docs/PAPER_RELATED_WORK.md`
11. `docs/PUBLICATION_STRATEGY.md`
12. `docs/RELATED_WORK_AND_LIMITATIONS.md`
13. `docs/ROADMAP.md`
14. `docs/TRUST_AUDIT_PACKET.md`
15. `docs/WORD_RAM_REVIEW_PACKET.md`
16. `docs/digests/PROJECT_DIGESTION_CURRENT.md`
17. `docs/internal/CLAIM_DRIFT_POLICY.md`
18. `docs/internal/RMQ_FINAL_ROADMAP.md`

Run strict policy scanning over all 18 and produce a path-by-path receipt.
Separately inventory public Lean comments/docstrings under `RMQ/`, especially
the `RMQPaper` import closure and headline aliases, for the same cost, space,
allocation, model, preprocessing, provenance, and novelty claims. Repair only
drift established against the exact selected source theorem; do not propagate
wording merely because it appeared in A09, the rejected `0e71b82...` target,
or this roadmap.

## Decision-flip conditions

The primary model changes only on evidence:

1. **Packed cell-probe to fallback:** Stage F returns
   `CHECKED_OBSTRUCTION`, or it returns `RUNWAY_PIVOT_UNRESOLVED` because the
   reviewed residual estimate exceeds the runway.
2. **Packed header to n-budget padding:** a checked obstruction rules out a
   constant header, while fixed n-determined padding has a proved
   `2n + o(n)` allocation and a closed estimate that still fits the runway.
3. **Cell-probe to small-step machine:** only if a target venue or primary
   precedent analysis shows the cell-probe theorem is insufficient for the
   paper's intended claim and a governed B3/B2 route has a closed completion
   estimate within the remaining time. "Stronger is nicer" is not enough.
4. **Fallback to packed after `CHECKED_OBSTRUCTION`:** only if the exact
   obstruction is formally discharged on a new governed branch. After
   `RUNWAY_PIVOT_UNRESOLVED`, post-V1 resumption requires a new governed
   estimate and authority, but not a fictitious discharge of an impossibility
   theorem.
5. **Public claim expansion:** only after the combined theorem and fresh audit,
   never from representative tests or an adjacent helper theorem.
6. **Owner architecture stop:** `ARCHITECTURE_DECISION_REQUIRED` suspends both
   implementation and fallback selection until the owner decides the explicit
   model/semantic change; it never authorizes an implicit workaround.

## Work explicitly frozen during the runway

- old B2DESC R4 prompt launch;
- full B3 R4 continuation;
- B4 and A4;
- merge or forward-port of `648e512...`;
- public Core/B1 rewrite in service of a validation-local obstacle;
- new instruction primitives or a new bespoke cost model;
- A1 module refactor and broad renaming;
- C/Rust backend work;
- envelope-tightness redesign without a reachable lower-bound witness;
- branch cleanup or evidence deletion before the final audit.

This freeze is reversible after V1. It is not a claim that the research lacks
value.

## Required workflow and Git hygiene

1. Re-enter at current governance and run `project_skill_preflight.ps1`.
2. Use a fresh `codex/` branch and worktree for every write task.
3. Freeze stable requirement IDs and the exact uniform object/controller
   quantifiers before proof edits.
4. Treat rejected branches and audit reports as immutable evidence; do not make
   the rejected strategy lineage an ancestor of the replacement plan.
5. Classify every prompt `DRAFT_DO_NOT_SEND` or `READY_TO_SEND`; structural
   preflight and semantic review are both required.
6. Keep one heavy Lean process per build tree; never rerun an unchanged
   expensive stage after a wrapper timeout.
6a. **Budget CI wall-clock separately from focused engineer-days** (Day-0
   amendment). `main` is protected and requires both workflows green on the
   exact pushed SHA, at roughly 25 minutes per cycle. Stage F's 5-7 focused
   days therefore do not include integration latency, and a single stale line
   has already cost two full cycles in this campaign. Per `WDD-20260725-011`:
   watch every push to green rather than moving on; never let a shell pipeline
   mask a gate's exit code; and run the gates the changed paths imply -- any
   `docs/internal/` file implies the strict design check, any prose implies
   strict claim drift, and a prior green run does not cover a file that did not
   exist when it ran.
7. Require exact registry identity, selectors, measured deadlines,
   process-tree kill, restoration, and terminal clean state for mutation
   campaigns.
8. Run fresh-blind audits for the roadmap architecture, combined
   space/execution capstone, U3 acceptance if not subsumed by a rigorously
   scoped release audit, and exact release commit.
9. Obtain explicit user authority before merge to main, push, publication,
   branch deletion, worktree retirement, or roadmap closure.

## Release wording

If the packed route is accepted, the strongest presently justified headline
form is:

> We mechanize a `2n + o(n)`-bit RMQ representation with at most `C` adaptive
> exact-width `w(n)`-bit cell probes per valid query in an explicit packed
> storage cell-probe model, with checked all-size bounds implying conventional
> logarithmic word width.

The exact theorem must define `C`, `w`, the allocated representation, validity
guard, and leftmost half-open result.

If the fallback is selected, the headline must instead identify the project
charged-read/supplied-store model and its limitations. It must not say packed
cell-probe, serialized-payload querying, word-RAM time, linear preprocessing,
or fully allocated `2n + o(n)` storage.

## Final checklist

- [ ] Roadmap delta audited and accepted as coordination policy.
- [ ] Feasibility prompt frozen and preflighted from current governance.
- [ ] Stage F returns exactly `FEASIBILITY_PASS`, `CHECKED_OBSTRUCTION`, or
      `RUNWAY_PIVOT_UNRESOLVED`, or records
      `ARCHITECTURE_DECISION_REQUIRED` and stops for the owner.
- [ ] U3 acceptance status resolved; no "certified floor" overstatement.
- [ ] Selected theorem surface reaches candidate complete.
- [ ] Same-object, allocated-space, probe-totality, state-invariant, and
      anti-bypass rows close.
- [ ] Fresh-blind exact-commit capstone audit passes.
- [ ] Manuscript and novelty log complete.
- [ ] Exact 18-surface policy inventory and public Lean comment/docstring
      inventory synchronized to the accepted theorem only.
- [ ] Reproducible artifact and V1 audit pass.
- [ ] No old E1 route, rejected strategy branch, or process report is presented
      as accepted mathematical evidence.

## Explicit uncertainties

- The universal header-sufficiency theorem does not yet exist. Representative
  B2SUFF reasoning is encouraging but non-durable.
- The exact physical probe expansion and resulting numeral `C` are unknown.
- The current `buildPayload` overhead is proved little-o but its envelope is
  loose; measured practical overhead is not yet part of the artifact.
- The packed representation's preprocessing complexity is unproved.
- U3's roadmap acceptance audit remains open even though M1's scoped audit
  reconstructed the `210` derivation.
- The paper venue and length constraint are not yet frozen.

These uncertainties are the worklist. None may be converted into a positive
claim by prose.

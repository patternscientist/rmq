# PQ1-A1 fresh blind audit and repair continuation

Status: CANDIDATE_COMPLETE. Verdict: merge-ready with follow-up for repaired exact target `6562ff62d14b17e918e7149f896bd0657ffd5aa0`. The original target failed verification and is not certified. Coordinator acceptance remains required.

## Scope and identity

- Mode: fresh blind source delta audit at 4c89378 plus one same-session tooling correction continuation to 6562ff6; auditor PQ1-A1; read-only, coordinator synthesis.
- Target: `4c89378f0c70aee272a56a12b7e70fb61e687e61`.
- Governance and delta base: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
- Repository: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
- Canonical role skill: none, as explicitly authorized by the frozen prompt. Actual runtime RMQ catalog: `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`.
- Project preflight passed in explicit no-role mode. At initial preflight HEAD equaled the original target; the later exact repair continuation is identified below. Governance is an ancestor and committed-range whitespace checks passed.
- Frozen requirements SHA256: `A8BA77D105E70AEE14E890E6FA5318318B828A60B45A6D1F3D4833138237B29B`. Verified against the packet and the two relevant target matrix sections, excluding all worker evidence/verdict sections.
- All inspected candidate source came from `git show TARGET:path`; concurrent mutation-gate working bytes were not used as candidate evidence. No prior reports or verdicts were consulted. After source reconstruction, an overbroad filter of gate output incidentally surfaced historical matrix and prior-audit scanner echoes; those echoes were excluded from evidence and did not alter findings. The auditor made no tracked edits; the coordinator owns repairs and report persistence.
- Scope: new packed primitive semantics, allocation, compiler and source/safety closure; all capstone fields and public typed consumers; replay and runtime evaluators; affected public claims and tooling delta. Helper proofs were sampled along their load-bearing composition edges. This is not a new independent reproof or a whole-repository predecessor audit.

## Conclusion and findings

No Lean theorem defect was found. Execution exposed a P1 required-gate blocker caused by replay portability at the original target; its exact repair and evidence are recorded in the continuation below. The source construction and public proposition were reconstructed in the explicit scalar arithmetic word model. Both required host aggregates and persisted report-tree checks pass. No unresolved P0/P1/P2 finding remains at the repaired target; the remaining P3 is optional terminology cleanup. All 34 frozen requirements and invariants have the source and execution evidence identified below.

P3 — terminology only: `README.md:28`, `docs/FAMILY_SUMMARY.md:80,107,117`, and other current public prose call the program “straight-line.” The program contains conditional branch instructions: `Guard.lean:24-29`, `Structured.lean:57-61`, and `QuerySource.lean:33-59`. “One fixed loop-free program” or “one fixed program with statically unrolled repetitions” is more precise. The program-length upper bound is unaffected. This is documentation polish, not a missing theorem or an acceptance blocker.

## Reconstructed propositions and object chains

All paths below beginning with a module name are relative to `RMQ/Core/WordRAM/Packed/`. Tier 1 denotes a kernel theorem; tier 2 denotes that theorem's explicit model content; tier 3 is executable validation; tier 4 is reproducible gate evidence; tier 5 is process/documentation evidence. The theorem claims below reconstruct the original source; the continuation records exact repaired-target build, trust and execution evidence.

**E1 — construction and uniformity (tiers 1/2).** `Allocation.lean:154-158` defines `shapeMemory shape := repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)` and `buildMemory xs := shapeMemory (SuccinctClassic.cartesianShape xs)`. `metadata` is the 42 scalar fields, 23 four-word regular descriptors, and eight five-word interior descriptors (`Allocation.lean:95-128,142-152`), totaling 174 words. Long and sparse counts are serialized, not recomputed by an uncharged query scan. `QuerySource.lean:55-63` defines one closed `queryBody`, `queryProgram`, `queryBudget`, and `queryRun memory n left right := run memory queryProgram queryBudget (initialState n left right)`. `Guard.lean:18-22` initializes only endpoints and public size; `Primitive.lean:111,119-122,133-153` contains no list of input values, shape, proof data, or semantic callback. `Setup.lean:143-167` proves charged setup installs metadata in the actual register bank, with the exact ordered 174 receipts.

**E2 — result and canonical interface discharge (tiers 1/2).** The canonical root is `fullyChargedPackedQueryCapstone_holds : FullyChargedPackedQueryCapstone`, with no premise (`Capstone.lean:171-174`). In particular:

```lean
∀ (xs : List Int) left right,
  queryNat (buildMemory xs) xs.length left right =
    if ValidRange xs left right then some (scanWindow xs left (right - left)) else none
```

and, for every `ValidRange xs left right`,

```lean
(run (buildMemory xs) queryProgram queryBudget
  (initialState xs.length left right)).result =
  some (scanWindow xs left (right - left) + 1)
```

These are fields `natContract` and `specResult` (`Capstone.lean:46-54,111-113`; typed consumers `PackedQueryContract.lean:81-95,185-188`). `leftmost` separately entails `LeftmostArgMin`, whose full tie/range/value predicate is independently pinned (`PackedQueryContract.lean:395-400`). The chain is physical scalar loads and span decoding → `logicalReadBlock_correct` (`PhysicalRead.lean:166-233`) → select/rank/fringe/interior source refinements → `lcaCloseBlock_correct` and `queryRun_result` (`QueryCorrect.lean:23-67`) → `QueryReference`’s predecessor-to-list transport → `queryNat_exact`, `queryRun_scanWindow`. Semantic interfaces are proved at the canonical builder; they are not public caller-supplied premises.

The return register chain is also operational: left/right selects populate 2049/2050; subtraction prepares 1200/1201; LCA yields 1202; final close rank yields 360; `queryRankFinishBlock` writes packet register 3; the actual primitive halt reads that register (`QuerySource.lean:24-56`). Raw `.load` writes the actual lookup reply (`Primitive.lean:135-146`), so the semantic answer does not precede the reads.

**E3 — complete storage and width (tiers 1/2).** For the identical `buildMemory xs`, the public fields state:

```lean
(buildMemory xs).length * wordWidth xs.length ≤
  2 * xs.length + allocationRho xs.length
((buildMemory xs).length + (queryProgram.map Instruction.encoding).flatten.length +
  (queryRegisterCount + 3)) * wordWidth xs.length ≤
  2 * xs.length + queryCompleteRho xs.length
```

Both residuals satisfy `LittleOLinear` (`Capstone.lean:22-31`; `Allocation.lean:160-201`; `Accounting.lean:18-26,53-56`). Dense repacking preserves the predecessor allocation, including header and padding, charging the 174-word prefix plus at most one new padding word. The complete residual also charges literal instruction tags/opcodes/operands and the finite register bank, PC, and two status words. `queryRun_finite_registers` fixes every register beyond that bank to zero at every fuel (`Accounting.lean:41-49`). The result is asymptotic absorption, not a small finite-size overhead claim.

The same `wordWidth n = 32 + 8 * packedReviewerCellWidth n` satisfies `Nat.log2 (n+2)+1 ≤ wordWidth n ≤ 192*(Nat.log2 (n+2)+1)`; all stored cells and addresses through the first out-of-allocation address fit (`Allocation.lean:23-44`; `Width.lean:409-461`; `QueryObservations.lean:13-22`). It is query independent. The constant floor covers code addressing at n=0.

**E4 — charged finite execution and safe arithmetic (tiers 1/2).** `Primitive.lean:28-63,133-184` has nine instruction constructors; each advertised arithmetic instruction performs one scalar arithmetic operation, each load one indexed lookup, and each branch/control instruction its advertised control action. No rank, select, popcount, decoder, or RMQ macro constructor is present. Repeats are compiled into instruction copies (`Structured.lean:42-63`): eight for rank/select chunks, seven for interior entry chunks, 33 for fringes, and fixed metadata/window/descriptor enumeration. These bounded copies are ordinary charged transitions. The source chain includes every rare long/sparse route (`SelectSource.lean:163-225`) and local/cross-macro/global/trailing interior route (`InteriorSource.lean:144-242`, `InteriorCandidateProof.lean:1813-1916`).

`queryBudget = 837572`, `queryProgram.length = queryBudget`, and `querySource.maxEncodedField = 8270` are checked definitional equalities; `queryRegisterCount = 8271`, `queryScratchWords = 8274` (`QueryStatic.lean:64-74`). `Compiler.lean:418-443` proves result, final data, ordered reads, and sufficient fuel for the compiled block. `queryRun_halts` supplies the load-bearing halting fact; the bare `steps ≤ fuel` fact alone would not close constant query time. Categories partition the actual transitions, not a synthetic accounting trace (`QueryObservations.lean:64-69`; `Primitive.lean:186-197`). No attainment/tightness conclusion follows.

Static `Instruction.Fits` enumerates every encoded field, including register IDs, operation tags, jump targets, and immediates (`Primitive.lean:77-108`); `queryProgram_fits` applies to all instructions, dormant ones included (`QueryStatic.lean:98-111`). Runtime `Instruction.Safe` requires fit, no subtraction underflow, nonzero divisor, legal shift amount, and an in-range arithmetic result (`Primitive.lean:199-213`). `queryRun_execution_safe` has only endpoint representability premises and fixes the same allocation/program/fuel/state (`QuerySafety.lean:450-461`). It discharges canonical fringe/interior leaves internally; local bound assumptions are produced by preceding stages, not left live at the capstone. `queryRun_requiredSafety` explicitly unfolds the every-transition, every-prefix, and every-read propositions (`QuerySafety.lean:490-510`).

**E5 — positional backing and whole-run store agreement (tiers 1/2).** For each indexed transition `transitions[index]? = some t` and receipt `t.receipt = some receipt`, `Capstone.lean:89-103` proves:

```lean
t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
∃ dst addrReg, t.instruction = .load dst addrReg ∧
  receipt.address = t.before.regs addrReg ∧
  receipt.reply = (buildMemory xs)[receipt.address]?
```

The backing proof is `Calculus.lean:165-198`, specialized in `QueryObservations.lean:48-56`. This records occurrence position, folded pre-state, fetched instruction, and address operands; it is stronger than membership in a store or trace. The ordered physical read list equals the 174 metadata reads followed by `logicalTraceReads` of the same query reference trace. `ReadOnlyTrace` rules out silently discarding synthetic/word-primitive events in that projection (`ReadInterface.lean:54-63`). `readerReceipts` intentionally produces no physical access for absent/zero-length logical spans. Present spans use actual one- or two-load decoding; a failed first load prevents a second load, and a failed issued load remains logged (`SpanAssembly.lean:19-101`). Canonical runs have no failed loads (`QueryCertificate.lean:188-197`).

`suppliedMemoryAgreement` requires lookup equality for every receipt in the first actual run and concludes equality of the entire `Run` on the supplied memory (`Capstone.lean:106-110`; `Calculus.lean:237-262`). Equality therefore preserves result, transitions, order, multiplicity, cost, and failure replies, not just a success set. Adding a cell at a previously failed lookup would violate its premise.

**E6 — inputs and all sizes (tiers 1/2).** `ValidRange xs left right` is exactly `left < right ∧ right ≤ xs.length` (`PackedQueryContract.lean:392-400`). Valid pairs always pass `encodeInputs` and fit; representable invalid pairs halt with packet 0 and no reads. Exact invalid guard cost is four steps when `left ≥ right`, otherwise six (`QueryCertificate.lean:108-165`). `queryNat` performs a separate uncharged word-domain check before machine execution (`QuerySource.lean:65-72,116-127`). Its correctness covers all mathematical Nat endpoints; this does not assign an instruction cost to parsing arbitrary integers. Empty/singleton, ragged/crossing, absent/dead, and rare/global cases remain in the universal theorem domains. Concrete small runtime fixtures do not prove those universal cases.

**E7 — public anti-bypass contract (tiers 1/2 plus replay tiers 3/4).** `RMQPaper` imports the headline; `RMQ/Headlines/RMQ.lean:25-36` abbreviates the exact capstone proposition and proof. `PackedQueryContract.lean:17-199` independently types every one of its 33 fields at the same explicit arguments. `publicContract` and `publicProposition` pin the export. The 38 definitional pins at lines 210-419 spell out evaluator, operand, safety, result, trace, input, validity, and little-o meanings; they prevent a producer and consumer from weakening together merely by changing shared vocabulary. Oversized register/jump/immediate rejection and largest-immediate acceptance are explicit checks (`PackedQueryContract.lean:427-450`). The elaborated inventory rejects extra/defaulted/indented/escaped/unicode fields (`scripts/packed_query_inventory_check.lean:11-64`), not just source-regex mismatches.

**E8 — replay and runtime (source tier 2; continuation outcomes tiers 3/4).** `scripts/packed_query_replay.ps1:41-100` pins the exact 38-case mapping: C01–C33 field weakenings, P01 public proof alias collapse, A01 unchanged acceptance, D01 instruction-category collapse, R01 scan packet projection mutation, N01 wrong expected runtime answer. Lines 188-260 check the literal registry against the frozen plan, source fields/initializers, typed checks, pins, and actual inventory. Lines 298-368 reject resource/setup failures and require the error at the designated consumer or producer initializer. Lines 370-465 exercise omitted, duplicate, reordered, extra, wrong-surface, missing-field/pin/check, and diagnostic controls.

Selection checks `PSBoundParameters.ContainsKey('OnlyCase')`, uses case-sensitive exact ID matching, rejects explicit empty/whitespace/unknown IDs, and checks the real host boundary (`packed_query_replay.ps1:23,262-269,471-521,600-614`). The runtime channel similarly rejects empty/unknown/malformed/duplicate selectors and checks exactly one selected fixture (`PackedQueryRuntime.lean:203-235`; replay lines 759-778).

Lean stages use owned bounded child execution, per-stage/runtime/rebuild deadlines, an 8 MiB output limit, retained JSON/stdout/stderr, resource-failure rejection, and restoration in `finally` with exact byte comparisons, restored producer/client checks, and clean-tree checks (`packed_query_replay.ps1:620-700,781-873`). Windows release gating assigns the child to a kill-on-close job before releasing the workload, then waits for owned descendants to die (`owned_process_tree.ps1:273-306,371-477`). `Invoke-DeadlineTest` requires a live grandchild and checks its absence after deadline. The Git-blob provenance helper has its own finite deadline; it does not launch Lean.

Runtime fixtures execute the new `execute`/`runArray` layer, with theorem `runArray memory program.toArray fuel s = run memory program fuel s` (`ArrayRun.lean:14-53`). Two fixtures also execute the list-program evaluator. Expected answers are fixed literals cross-checked against independent `scanWindow`; route assertions come from the shape/reference trace, not from the actual machine (`PackedQueryRuntime.lean:55-90,100-140,143-192`). The 15 positive fixtures and one deliberately false answer are fully enumerated. This supplies regression evidence, not universal route attainment or cost tightness.

**E9 — public prose, paper identity, and tooling (tiers 4/5).** The required README, family summary, what-is-proved, claim correspondence, review packet, artifact claims, manuscript, and theorem ledger correctly identify the separate primitive capstone and its unit-cost multiplication/division/remainder/variable-shift assumptions. They retain the mathematical-input/parsing boundary, preprocessing exclusion, asymptotic code/scratch absorption, and distinct predecessor cost models. `docs/DIGESTION_LOG.md:1653-1725` contains conceptual change, plain-English meaning, live assumptions, reusable proof ideas, and a skeptical next question; no proof-digestion omission was found.

The paper pin is `3849ecbb53bbedfcd679352cc68d095fa5a304c2` (`paper/THEOREM_LEDGER.md:617`), an ancestor of the target. The committed diff from that pin to target is empty for `RMQ`, `RMQPaper.lean`, `RMQ.lean`, `lakefile.toml`, and `lean-toolchain`; explicit capstone/headline/client blob comparisons are identical. The paper's mathematical source is therefore the same source, while its process identity remains a separate pin. Its `ACCEPTED_BASE` label is explicitly limited to kernel/export status, not coordinator acceptance (`paper/THEOREM_LEDGER.md:604-616`).

Claim policy v28 adds paragraph-local attribution for the primitive capstone and blocks attaching that budget to predecessor trace/probe theorem names; these new rules have no path allowance, and accepted/rejected regression controls are pinned. The pre-existing broad internal-process exemptions are not mathematical evidence. Prompt-preflight no-role support is restricted to explicit READ_ONLY mode and rejects absent opt-in, contradictory role, or missing frozen literals (`scripts/worker_prompt_preflight.ps1:67-80,117-136`); regression cases cover these boundaries. No new Lean import/trust permission was introduced by these tooling changes.

## Frozen acceptance dispositions

“Source satisfied” below means literal source and intended object composition reconstructed and supported by the repaired-target build/trust and executable evidence; Lean source identity with the original target was checked. It is not coordinator acceptance.

| ID | Disposition and concrete evidence |
| --- | --- |
| REQ-PQ1-CONSTRUCTION | Source satisfied: E1, numeric builder and closed primitive run; E2 actual returned register chain. |
| REQ-PQ2-EXECUTION | Source satisfied: E2/E5, complete result and ordered-read refinement through both selects, LCA/fringes/interior and final rank; canonical interface discharge. |
| REQ-PQ3-SPACE | Source satisfied: E3, exact complete allocation/program/register expression and both checked residuals; identical E1 execution memory. |
| REQ-PQ4-WIDTH | Source satisfied: E3/E4, logarithmic width, dormant constructor-complete encoded fields and actual prefix/transition/read arithmetic safety. |
| REQ-PQ5-COST | Source satisfied: E4, fixed finite program, halting within its fuel, actual transition/category partition; scalar arithmetic model explicit. |
| REQ-PQ6-COVERAGE | Source satisfied: E2/E4/E5/E6, no readiness premise, source branches include rare/global paths, ordered repeats and empty/dead semantics preserved. |
| REQ-PQ7-INPUTS | Source satisfied: E2/E6, total Nat wrapper and leftmost half-open contract; all valid endpoints representable; charged invalid guard. |
| REQ-PQ8-UNIFORMITY | Source satisfied: E1/E4, closed code, metadata prefix charged, no n-specialized query constants. |
| REQ-PQ9-PUBLIC | Source satisfied with optional P3 terminology follow-up: E7/E9, identical alias/import, typed consumers and digestion, properly separated costs. |
| CHK-PQ10-VERIFICATION | Satisfied at repaired target 6562ff6: both required host aggregates, exact full PQ1 replay, supplemental probes, preflight, source identity and hygiene pass. Persisted report-tree strict claim-drift, applicable strict design and whitespace checks pass; `.lake/pq1-report-checks-final.json` binds these results to the report SHA256. Original-target failure and environment-limited attempts are retained below. |
| REPLAY-EXACT-REGISTRY | Satisfied at repair target: E7/E8 and both-host full replay, exact 38-case registry/selection, inventory and all diagnostic/expected-accept controls. |
| REPLAY-SELECTOR-NONVACUITY | Satisfied at repair target: E8 and both-host full replay; explicit empty/invalid selectors reject, omitted selection runs all cases, valid selection is exact, and stale runtime-channel removal is checked at the real host boundary. |
| REPLAY-SUBPROCESS-DEADLINE | Satisfied at repair target: E8 and both-host full replay; intentional deadline control kills its live descendant, actual stages finish without resource failure, restoration and clean-tree checks pass. |
| INV-STORE-IDENTITY | Source satisfied: E1/E3/E5 same `buildMemory xs` in counted expression, actual run, receipts and agreement. |
| INV-VALUE-DEPENDENCY | Source satisfied: E2 actual read-to-return chain, E5 physical value refinement; committed `SpanAssembly.lean:499-503` changes each crossing input reply and compares `.result`; supplemental whole-query data mutation changes the returned packet at physical data addresses 174 and 177 (continuation). |
| INV-SEMANTIC-NONVACUITY | Source satisfied: E2/E4/E5 derived operational reader/source/safety predicates, not True or membership-only labels. |
| INV-TRACE-EXECUTION | Source satisfied: E5 `Run.reads = transitions.filterMap receipt` and indexed actual prefix proof. |
| INV-STORE-AGREEMENT | Source satisfied: E5 actual consumed lookup agreement determines the entire same-program run, including none replies. |
| INV-READ-BACKING | Source satisfied: E5 indexed transition/instruction/operand/lookup conjunction. |
| INV-WORD-WIDTH | Source satisfied: E3/E4 stored cells, registers, status result and transitions fit one width. |
| INV-ADDRESS-WIDTH | Source satisfied: E3/E4 constructor-complete static encoding plus every actual load operand, sentinel/dead/failed address checks. |
| INV-INSTRUCTION-ATOMICITY | Source satisfied: E4 scalar execute cases; all iterative high-level work expands into charged code. |
| INV-PROGRAM-ACCOUNTING | Source satisfied: E1/E3 fixed program encoding and scratch counted; varying metadata serialized and loaded. |
| INV-ORACLE-INDEPENDENCE | Source satisfied: E8 independent literal answers/scanWindow and reference-route assertions. |
| INV-VALIDATION-REACH | Source satisfied: E8 actual numeric-memory primitive evaluator and checked array equivalence, plus two list-run controls. |
| INV-ALL-SIZE | Source satisfied: E2/E4/E6 universal canonical list theorem without readiness or geometry exclusions. |
| INV-PROOF-SEPARATION | Source satisfied: E1/E2 proof predicates and observations never enter primitive state or instruction data. |
| INV-NO-SYNTHETIC | Source satisfied: E4/E5 actual transition-derived reads/categories; read-only logical trace excludes synthetic projected events. |
| INV-CATEGORY-SEPARATION | Source satisfied: E3/E4/E6/E9 separate bits, proof observations, scalar steps, mathematical input checking, preprocessing and Lean runtime. |
| INV-PUBLIC-COMPOSITION | Source satisfied: E2/E3/E4/E5/E6/E7 all advertised fields use identical allocation, execution and validity domain; representability guards are explicit. |
| INV-CERTIFICATE-ANTI-BYPASS | Satisfied at repair target: E7 exact-type projections and E8 full replay on both hosts reject every field/public collapse at its expected surface. |
| INV-MUTATION-REPRODUCIBILITY | Satisfied at repair target: E8 committed cases replay on both hosts with expected surfaces, restored acceptance and clean-tree checks; supplemental sources and precise verdicts appear below. |
| INV-GLOBAL-PHYSICAL-MACHINE | Source satisfied: E1/E5 one complete pre-execution numeric store, charged metadata and physical span reads; no suffix-only embedding. |
| INV-WIDTH-SCALING | Source satisfied: E3/E4 one query-independent logarithmic width bounds stored, dynamic and dormant static quantities together. |

## Counterfactual dispositions

| Attempt | Original P versus proposed Q | Rejecting surface / expected observation |
| --- | --- | --- |
| Ignore a decisive raw reply | P: `.load dst address` writes `memory[s.regs address]?`’s successful value. Q: retain the receipt but always write zero. | `PackedQueryContract.pinExecute`; source value chain E2; committed span `.result` dependency theorem, not enclosing-record inequality. Supplemental data replacements change the returned packet (addresses 174 and 177); see continuation for the concrete witness. |
| Remove allocation | P: run canonical counted memory on valid range. Q: run empty memory with the same code and initial state. | Physical first load faults and logs `⟨0,none⟩`; supplemental runtime probe passes at the repair target. Q does not satisfy canonical result or agreement premises. |
| Add an unread cell | P: count `buildMemory xs`. Q: execute/count `buildMemory xs ++ [0]` but reuse P’s exact capacity proposition. | Supplementary `siblingCapacity` rejects with the intended type mismatch at 16:2; its canonical positive control compiles. The runtime may remain equal on unread extension; its capacity nevertheless increases. |
| Weaken field to True | P: each exact C01–C33 proposition. Q: replace that field and its initializer by True/True.intro. | Corresponding exact `checkCnn`; committed runner checks the precise declaration span and restored acceptance. |
| Sibling allocation | P: same-memory capacity/result/backing. Q: use a fact with another allocation as though it had P’s type. | E7 explicit object arguments; supplementary added-cell client rejects with the intended type mismatch and its canonical positive control compiles. No claim that an extension necessarily violates the loose numerical upper bound. |
| Forge trace/prefix | P: `actual.transitions[index]? = some t`. Q: `invented[index]? = some t`. | Supplemental `forgedPrefix` rejects the mismatched premise at the public positional theorem application (20:104); the actual-transition positive control compiles. Membership in another record cannot certify execution. |
| Oversized dormant operand | P: every encoding member < word capacity. Q: a register, jump target or immediate equals capacity. | `fitsRejectsOversizedRegister/JumpTarget/Immediate`; largest legal immediate accepts; C08 projection anti-bypass. |
| Hide variable primitive work | P: explicit Arithmetic.eval/execute constructors and transition categories. Q: insert rank/select/controller macro or change category meaning without updating client. | Constructor-exhaustive pins; D01 category-collapse expected rejection at `pinInstructionCategory`; no such macro is present in inspected semantics. |
| Wrong answer projection/oracle | P: valid run returns `scanWindow + 1`. Q: `scanWindow + 2` or deliberately wrong literal tie answer. | R01 rejects only at `specResult` initializer; N01 rejects at runtime result mismatch. |

## Rejected objections and limitations

- A fuel bound is not enough; here the same actual run additionally halts within that fuel. This rejects the “budget is only tautological truncation” objection without claiming tightness.
- A source-level reader correctness or safety premise is not a hidden public hypothesis when the canonical builder discharges it; E2/E4 inspect that discharge.
- Empty/absent logical spans making no physical load is the explicitly chosen operational reader semantics, not suppression of an attempted failure. Issued failed loads remain logged, and universal canonical halting proves no such failures occur on canonical queries.
- An unread counted cell need not affect a given query. Agreement is sufficient for run equality, not a claim that every read is decisive or every cell is queried.
- Runtime fixture coverage does not establish rare-case attainability, universal coverage, or maximum-cost attainment. Universal correctness/safety comes from the kernel theorem chain.
- Nat-valued semantics alone would not imply bounded-machine behavior; separate no-overflow/no-underflow/no-zero-divisor/legal-shift and encoded-field proofs supply that refinement for representable input states.
- Fixed code/scratch may dominate small inputs. The public theorem and paper explicitly limit their absorption to the lower-order asymptotic term.
- Existing predecessor theorem assumptions/trust remain dependencies. This delta audit does not re-audit all predecessor mathematics, and a green report is not a substitute for the kernel.

## Verification log

Executed by auditor: no-role project preflight PASS; target identity and governance ancestry PASS; frozen packet hash and two exact section text comparison PASS; paper-pin ancestry and full Lean/source configuration diff equality PASS; `git diff --check BASE..TARGET` PASS; committed-byte equivalent of required forbidden-token/Mathlib and native_decide/Lean.ofReduceBool scans over RMQ and lakefile.toml produced no hits. Shell git configuration warnings concerned inaccessible global ignore configuration and did not fail checks. No broad build was duplicated because the coordinator owns the required two-host aggregate runs.

Completed coordinator evidence is recorded in the continuation: both required host aggregates, both-host full PQ1 replay and supplemental probes. Final persisted report-tree strict production claim-drift, applicable strict design-decision, trust/hygiene and whitespace checks pass. The auditor independently verified both aggregate artifacts and both full PQ1 reports; final report verification is bound to the exact report bytes in the retained check artifact.

Roadmap alignment: the candidate removes the intended abstraction gap by charging scalar execution on the same complete succinct numeric allocation, rather than relabeling a predecessor cost certificate. Best next target after coordinator acceptance: the assigned downstream serialized-payload/preprocessing work; cost tightening may be useful separately, but this upper-bound milestone does not require attainment.

Proof digestion: conceptually, source block refinement now transports actual loaded values, reads and safe arithmetic into one fixed primitive program, while a counted metadata prefix makes its code uniform. Plain English: for every ordinary list and valid half-open range, the modeled machine obtains the leftmost answer from its stored words within one fixed instruction budget. Live assumptions are the declared scalar arithmetic word model, Lean/Std plus omega and ordinary standard axioms, unbounded preprocessing, and an uncharged outer Nat encoding test. A skeptical grad student should next ask which stronger or cheaper machine model can implement those operations and what useful finite-size space or cost bound follows, rather than reading asymptotic absorption as practical compactness.

Durable disposition: this report is persisted at `docs/internal/audit_reports/PQ1_FRESH_BLIND_4c89378.md`, with final report-tree verification complete. Coordinator acceptance remains required; no merge, push, integration or acceptance was performed by the auditor.

## Supplemental probe sources

The following audit-only probes are additional falsification evidence. They do not replace the committed 38-case campaign. Recreate the three source files below in `.lake/pq1-blind-4c89378`, then replay sequentially after the required build using installed Lean v4.22.0; no tracked source mutation is needed. Expected results: the runtime probe accepts and prints its final PASS token; `AuditSiblingReject.lean` rejects at `siblingCapacity` with a type mismatch; `AuditTraceReject.lean` rejects at the public theorem application in `forgedPrefix` with an application type mismatch. Resource/setup failures do not count as expected rejection.

```powershell
$env:LEAN_PATH = '.lake/build/lib/lean'
$auditLean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
& $auditLean --run .lake/pq1-blind-4c89378/AuditCounterfactuals.lean
& $auditLean .lake/pq1-blind-4c89378/AuditSiblingReject.lean
& $auditLean .lake/pq1-blind-4c89378/AuditTraceReject.lean
```

### AuditCounterfactuals.lean

```lean
import RMQ.Validation.PackedQueryContract
import RMQ.Core.WordRAM.Packed.ArrayRun

open RMQ.SuccinctFinal.PackedWordRAM

namespace PQ1BlindAudit

-- A real load writes its reply; replacing it by a decorative zero write is false.
example : (execute [9] (.load 1 0) ⟨fun _ => 0, 0, .running⟩).1.regs 1 = 9 := by decide
example : (run [9] [.load 1 0, .halt 1] 2 ⟨fun _ => 0, 0, .running⟩).result = some 9 := by decide
example : (run [] [.load 1 0, .halt 1] 2 ⟨fun _ => 0, 0, .running⟩).reads = [⟨0, none⟩] := by decide
example : (run [] [.load 1 0, .halt 1] 2 ⟨fun _ => 0, 0, .running⟩).final.status = .fault := by decide

def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def mainImpl : IO Unit := do
  let xs : List Int := [4, -3, -3, 8]
  let memory := buildMemory xs
  let program := queryProgram.toArray
  let runOn (m : Memory) := runArray m program queryBudget (initialState 4 0 4)
  let actual := runOn memory
  check (actual.result == some 2) "independent literal answer"
  let empty := runOn []
  check (empty.result == none && empty.final.status == .fault && empty.reads == [⟨0, none⟩])
    "removed allocation must fault at first charged load"
  let extended := runOn (memory ++ [0])
  check (extended.result == actual.result && extended.reads == actual.reads && extended.steps == actual.steps)
    "unread added cell should preserve execution"
  check ((memory ++ [0]).length * wordWidth 4 > memory.length * wordWidth 4)
    "added cell must increase counted data capacity"
  let dataAddresses := ((actual.reads.map (·.address)).filter (174 ≤ ·)).eraseDups
  let addresses := dataAddresses.take 6
  let mut decisive := false
  for address in addresses do
    for value in [0, Nat.xor ((memory[address]?).getD 0) 1] do
      let altered := runOn (memory.set address value)
      if altered.result != actual.result then
        decisive := true
        IO.println s!"PQ1-BLIND DATA-DEPENDENCY address={address} value={value} canonical={repr actual.result} altered={repr altered.result}"
  check decisive "no decisive data reply among first six physical data addresses"
  IO.println s!"PQ1-BLIND COUNTERFACTUAL PASS removed/added allocation, raw failed load, returned data dependency; canonical steps={actual.steps}"

end PQ1BlindAudit

def main : IO Unit := PQ1BlindAudit.mainImpl
```

### AuditSiblingReject.lean

```lean
import RMQPaper
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open RMQ.SuccinctFinal.PackedWordRAM
attribute [local irreducible] buildMemory wordWidth allocationRho

example (xs : List Int) :
    (buildMemory xs).length * wordWidth xs.length ≤
      2 * xs.length + allocationRho xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.dataCapacity xs

-- Expected rejection: a theorem about canonical storage cannot certify an added cell.
theorem siblingCapacity (xs : List Int) :
    (buildMemory xs ++ [0]).length * wordWidth xs.length ≤
      2 * xs.length + allocationRho xs.length :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.dataCapacity xs
```

### AuditTraceReject.lean

```lean
import RMQPaper
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
open RMQ.SuccinctFinal.PackedWordRAM
attribute [local irreducible] run buildMemory queryProgram queryBudget initialState

example (xs : List Int) (left right index : Nat)
    (t : Transition) (receipt : Receipt)
    (h : (run (buildMemory xs) queryProgram queryBudget
      (initialState xs.length left right)).transitions[index]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final :=
  (RMQ.Headlines.succinctRMQFullyChargedPackedQuery.positionalReadBacking xs left right index t receipt h hr).1

-- Expected rejection: arbitrary membership in another transition sequence is insufficient.
theorem forgedPrefix (xs : List Int) (left right index : Nat)
    (t : Transition) (receipt : Receipt) (invented : List Transition)
    (h : invented[index]? = some t) (hr : t.receipt = some receipt) :
    t.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final :=
  (RMQ.Headlines.succinctRMQFullyChargedPackedQuery.positionalReadBacking xs left right index t receipt h hr).1
```

## Repair continuation and execution evidence

The fresh blind source target was `4c89378f0c70aee272a56a12b7e70fb61e687e61`. The focused continuation target is `6562ff62d14b17e918e7149f896bd0657ffd5aa0`. Source citations in E1-E9 refer to the original target unless explicitly qualified; the repair changes no RMQ Lean file, public root, lakefile or toolchain. The original target is not certified by later results.

Under AUDIT_PROTOCOL.md, a failed required gate is P1; the earlier P2 portability label was corrected before completion. This severity does not imply a Lean proof or trust defect. The coordinator and auditor classify the single correction as nonmaterial to the audited mathematical/public/trust surface: it changes environment-entry removal and its host-boundary regression, with no Lean, proposition, primitive, consumer, registry or rejection-semantics change. The protocol permits one same-auditor correction pass; the exact delta and both-host execution are checked. This is not an independent fresh repaired-target audit, and the continuation alone is not a new independent acceptance gate. The fresh source audit plus this scoped continuation supplies the audit evidence; coordinator acceptance remains a separate decision.

P1, repaired: required aggregate failed because runtime selector removal was not portable across PowerShell hosts. The first aggregate at 4c89378 failed after all 38 mutation cases passed: runtime-full reported a malformed selector channel. Report run-218d6cf703a042c39fc2671c052029f5 has Completed=false, exact Registry=Selected, 38 expected verdict matches and 147 successful restoration build/consumer stages. Replay line 35 assigned null through .NET; a direct PowerShell 7.6.5 probe showed a present empty environment variable remained. Lean correctly distinguishes absence from malformed empty input.

The repair uses actual environment-entry removal. Every real bounded selector child starts with a stale channel and must prove the entry absent after startup, including rejected selections; a survivor forces exit 99. The validation plan and WDD-20260911-PQ1-014 record this boundary. The auditor independently checked the exact delta, source identity and range whitespace. Both host RuntimeOnly reports at 6562ff6 (run-1e0066819ed044cb924927b6bc5876d7 and run-78e2a5842c304b9dac70ecaa41f54f8b) have Completed=true: all 15 fixtures, S02/S05 List evaluator controls, empty/whitespace/unknown/malformed rejection and exact single-case selection pass. Full fixtures took 131.820 and 128.228 seconds respectively. This closes the reproduced symptom without weakening selector semantics.

Before the fresh audit was dispatched, an initial coordinator gate at 3c8097e exited after 64.391 seconds because its ignored launcher overwrote inherited Git safe-directory configuration. The launcher was corrected to append configuration entries while preserving the inherited ones, and the affected strict design regression passed. This pre-dispatch attempt (pq1-aggregate-pwsh7-3c8097e.json) is not counted as certification.

A subsequent 6562ff6 aggregate passed full PQ1 and all 41 M1 cases, then the inherited EG-CP cleanup self-test received Access denied inside the sandbox. It remains failed certification, archived as pq1-aggregate-pwsh-6562ff6-sandbox-failed.json. Both EG-CP cleanup self-tests passed under both hosts outside the sandbox, with exact owned-process captures in pq1-egcp-selftests-unsandboxed-6562ff6.json. No self-test was skipped or weakened. An additional one-second launcher failure caused by duplicate executable resolution occurred before gate execution and is separately archived; selecting one executable repaired the ignored launcher, with no repository change.

Supplemental probes (tiers 3/4) passed at 6562ff6: a successful load returned its supplied word; empty allocation faulted with the first failed load logged; an unread appended cell preserved result, reads and steps but increased capacity; replacing physical data address 174 or 177 with zero changed packet some 2 to some 3 for [4,-3,-3,8], whose canonical run took 10165 steps. This is a concrete returned-value witness, not a universal sensitivity claim. Revised exact-type probes compiled canonical positive controls and rejected only the intended substitutions: siblingCapacity at 16:2 (canonical memory versus appended memory) and forgedPrefix at 20:104 (actual indexed execution versus invented transition list). Initial default heartbeat/recursion failures were inconclusive and are not counted. Probe-local irreducibility avoids incidental unfolding; bounded recursion/heartbeat options preserve the exact public types. The appendix contains the executed revised source, including positive controls.

PowerShell 7 aggregate at 6562ff6 passed in 5654.834 seconds: no timeout or output overflow, GATE PASS, 18/18 advertised checkers invoked. Its full PQ1 report is run-874f9ebfe40043e5b45fd72b4663141d/report.json. All 38 cases, all 15 runtime fixtures and selectors, M1 41 cases, EG-CP 21 and 16 cases, eight standard-axiom inventories, claim and paper checks, and all 16 paper-topology cases passed. The auditor independently verified the aggregate and exact PQ1 artifact. Windows PowerShell 5.1 aggregate at 6562ff6 also passed in 7415.157 seconds, with no timeout or output overflow, GATE PASS and all 18 advertised checkers invoked. Its full PQ1 artifact is run-ab42523e17a64ec9ac6ba6d81d8e3a46/report.json. It independently passed the full 38-case replay, 15 runtime fixtures and selector controls, M1 41 cases, EG-CP 21 and 16 cases, all eight trust inventories, claim/paper checks and all 16 paper-topology cases (14 expected rejects and two acceptance controls). No aggregate is inferred from component-only evidence.

Raw artifacts above are under .lake; these paths identify retained local execution captures, not permanent external storage. The committed runners and reproduced supplemental source make the checks replayable. Both-host aggregate outcomes and final report-sensitive checks are recorded; coordinator acceptance is a separate decision.


## Final verification artifacts

All aggregate commands were full `scripts/gate.ps1` invocations, with no skip or focused-selection flags, using installed Lean 4.22.0 and one build-tree owner at a time. The final successful executions used the normal user environment so their owned-process cleanup checks could run.

| Evidence | Exact retained local artifact |
| --- | --- |
| PowerShell 7 full aggregate | `.lake/pq1-aggregate-pwsh-6562ff6.json` |
| Windows PowerShell 5.1 full aggregate | `.lake/pq1-aggregate-powershell-6562ff6.json` |
| PowerShell 7 full PQ1 replay | `.lake/pq1-replay/run-874f9ebfe40043e5b45fd72b4663141d/report.json` |
| Windows PowerShell 5.1 full PQ1 replay | `.lake/pq1-replay/run-ab42523e17a64ec9ac6ba6d81d8e3a46/report.json` |
| Supplemental runtime and initial type attempt | `.lake/pq1-blind-4c89378/PROBE_RESULTS_6562ff6.json` |
| Initial trace resource failure, not counted as rejection | `.lake/pq1-blind-4c89378/TRACE_PROBE_6562ff6.json` |
| Revised exact-type rejections and positive controls | `.lake/pq1-blind-4c89378/TYPE_PROBES_6562ff6.json` |
| Final report checks and exact report SHA256 | `.lake/pq1-report-checks-final.json` |

The coordinator checked that all 34 frozen IDs occur exactly once in the report matrix and that all three reproduced probe sources match the executed files. The no-role prompt-preflight repair is recorded in WDD-20260911-PQ1-013; the runtime selector repair is recorded in WDD-20260911-PQ1-014. This report applies the existing audit protocol and introduces no new mathematical design or workflow policy, so no additional design-ledger entry is needed.

Final report-only verification: PASS. The two full aggregates certify source commit `6562ff62d14b17e918e7149f896bd0657ffd5aa0`; an additional aggregate was skipped for the subsequent report-only commit. Its final bytes passed `scripts/claim_drift_scan.ps1 -Strict` in production mode, `scripts/design_decision_check.ps1 -Strict -Base 4c89378f0c70aee272a56a12b7e70fb61e687e61 -Head 6562ff62d14b17e918e7149f896bd0657ffd5aa0`, and the report delta check with `-Strict -Base 6562ff62d14b17e918e7149f896bd0657ffd5aa0`. Working, staged and committed-range whitespace checks passed; both required RMQ trust/hygiene scans had no matches. No new Lean build or mutation campaign was needed for the report-only delta.

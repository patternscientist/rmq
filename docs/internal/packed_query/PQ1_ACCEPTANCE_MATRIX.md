# PQ1 frozen proof acceptance matrix

Worker: PQ-1. Branch: `codex/fully-charged-packed-query-v1`.
Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`.
Base and governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
Runtime RMQ catalog: `rmq-audit-prompt`, `rmq-coordinator`, `rmq-proof-sprint`.
Both required role skills passed project preflight before substantive work.

This matrix instantiates `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
The requirements below are frozen before proof edits. Evidence is append-only
and indexed by ID; evidence/status changes do not alter requirement text.
The inherited invariant text follows verbatim in a separate frozen appendix.
No row is closed merely by naming a theorem or by passing an executable fixture.

## Exact assigned requirements

| ID | Exact frozen requirement |
| --- | --- |
| REQ-PQ1-CONSTRUCTION | Supply one concrete query-independent packed-memory builder for each ordinary xs : List Int and a concrete primitive execution entry point. The machine has no xs, CartesianShape, proof fields, semantic-store callback or precomputed answer; query-dependent data come only from representable endpoints, public size parameters and charged replies from that allocation. |
| REQ-PQ2-EXECUTION | Prove whole-run result and positional-read refinement, including both selects, same-block and different-block cases, crossing-cell decoding, endpoint fringes, every interior route and final rank. The returned index must be computed by the primitive run. Correctness/budget/read-backing facts may not be supplied as hypotheses that restate the desired result for the canonical builder. |
| REQ-PQ3-SPACE | Prove the complete allocated data capacity, including headers, all directory/table data, padding and any shape/size metadata consulted by the program, is at most 2*n+rho(n) with checked LittleOLinear rho. State program and scratch-register accounting explicitly; charge input-dependent code/metadata as data or derive it uniformly. If program/scratch space is excluded by the machine convention, additionally give the bound needed to absorb it in the lower-order term. All space and execution conjuncts must refer to the same allocation and model. |
| REQ-PQ4-WIDTH | Prove a single query-independent word width with logarithmic scaling bounds stored cells, every reachable register/immediate/arithmetic result, decoded tags, physical addresses, failed/dead addresses, register IDs, return PCs and all instruction operands/targets, including dormant instructions. Handle all sizes and small-size code-addressability; array bounds or unbounded Nat arithmetic alone are insufficient. |
| REQ-PQ5-COST | Prove a fixed input-independent upper budget for all executed primitive query instructions, including memory attempts, arithmetic, comparisons, branches, decoding, calls/returns, validation and halt. Derive it from this run, with an exact step/category partition. No whole rank/select/popcount/controller/RMQ macro instruction may hide variable work. Resolve the sparse-count prelude and every other growing loop. A logarithmic-time theorem or a finite measured bound is not completion of this requirement. |
| REQ-PQ6-COVERAGE | Remove readiness and compatibility premises from the canonical List Int theorem. Prove rare exception and cross-macro/global-interior paths as well as the small paths exercised by the experiment. Keep ordered repetitions, empty logical sentinels, attempted failed physical reads and leftmost ties faithful to the chosen operational semantics. |
| REQ-PQ7-INPUTS | Preserve the total half-open, leftmost List Int reference contract. Every valid mathematical endpoint pair must be representable and covered by the primitive correctness and cost theorem. All representable invalid/empty/reversed/out-of-range machine inputs must be rejected within the charged guard. Explicitly separate the total mathematical Nat API from parsing/encoding unbounded external integers: fixed-width machine registers cannot contain arbitrary Nat endpoints. If the API rejects endpoints outside the word domain before encoding, give its value-level proof and do not claim a machine-instruction bound for unbounded input parsing. Do not narrow the valid-query domain. |
| REQ-PQ8-UNIFORMITY | Supply one fixed finite program, or a formally justified uniform equivalent, independent of xs and endpoints. The experiment's n-specialized constants are not free metadata by fiat: derive size-only geometry under the stated model or serialize it into counted memory and charge reads. Preprocessing itself may remain unbounded, but its resulting metadata cannot evade space accounting. |
| REQ-PQ9-PUBLIC | Expose the completed theorem through one documented import/alias with the exact same identity, update affected theorem/claim/digestion surfaces and code comments, and explain the reusable proof ideas. Keep the existing charged-trace 210 and packed structural/probe bounds distinct from the new instruction budget. Never label a prior theorem as fully charged merely by prose. |
| CHK-PQ10-VERIFICATION | Run narrow Lean checks during development, required final builds/trust/hygiene/design/reproduction checks, committed-range whitespace checks, negative controls and a fresh blind exact-commit audit before marking the public milestone accepted. Every claimed mutation campaign must be committed and replayable. |
| REPLAY-EXACT-REGISTRY | Pin every replay case ID and expected disposition; missing/duplicate IDs or mappings must fail. |
| REPLAY-SELECTOR-NONVACUITY | A focused selector executes exactly its requested case and rejects unknown or explicitly empty selectors; include known-success and omitted/duplicate-case controls. |
| REPLAY-SUBPROCESS-DEADLINE | Bound child processes and preserve diagnostic logs; one heavy Lean/Lake process per build tree, no unchanged reruns after unexplained timeout. |

## Evidence plan and current gaps

All rows have roadmap scope, except replay/gate rows (verification). The
inherited rows have the same whole-query scope. Exact proposition text will be
added only after the concrete definitions elaborate; proposed statements are
recorded in `PQ1_MODEL_AND_PROOF_DAG.md` and are not evidence.

| IDs | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge to attempt | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- |
| REQ-PQ1-CONSTRUCTION; INV-STORE-IDENTITY; INV-PROOF-SEPARATION | A closed builder and evaluator with only numeric allocation, width, program and representable endpoints as execution inputs. | List Int -> Cartesian shape during construction -> counted numeric allocation -> primitive run -> capstone. | Change input shape at fixed size; code must stay identical. Inspect absence of semantic callback/answer in state. | RC6 source inventory only. | Open: concrete new allocation and run. |
| REQ-PQ2-EXECUTION; INV-VALUE-DEPENDENCY; INV-TRACE-EXECUTION; INV-READ-BACKING; INV-NO-SYNTHETIC | Equality of actual primitive return and ordered receipts to lowered canonical semantics, carrying read position, instruction, folded pre-state and operands. | Actual run -> packed physical decoder -> logical protocol -> whole-query semantics -> List Int specification. | Mutate returned result, actual load, crossing order, repeated occurrence; same predicate/domain must reject each. | Experiment receipts are finite predecessor evidence only. | Open: universal refinement. |
| REQ-PQ3-SPACE; INV-PUBLIC-COMPOSITION; INV-PROGRAM-ACCOUNTING; INV-CATEGORY-SEPARATION | For the executed allocation A(xs), A.length * w(n) <= 2*n+rho(n), LittleOLinear rho, plus an explicit code/scratch absorption bound. | The allocation argument of run is literally A(xs), also used in the space conjunct. | Add a header or padding cell without modifying space; substitute a sibling allocation in the conjunction. | RC6 payload-length and little-o lemmas available. | Open: repacking and all metadata. |
| REQ-PQ4-WIDTH; INV-WORD-WIDTH; INV-ADDRESS-WIDTH; INV-WIDTH-SCALING | One w(n), logarithmic scaling, all stored cells, reachable states, primitive results, dead addresses and every dormant instruction field < 2^w(n). | w(n) -> allocation packing and program -> reachable prefix states -> capstone. | Oversized dormant register/PC/immediate; n=0/1 code capacity; all-ones logical word tag. | Width obligations identified in experiment. | Open: common width and constructor-exhaustive proofs. |
| REQ-PQ5-COST; INV-INSTRUCTION-ATOMICITY | One fixed K bounds actual steps on all representable endpoints; actual run halts; category counts sum exactly to steps. | Finite primitive blocks -> bounded loops/branches -> complete actual run. | Replace an arithmetic primitive by a scan; grow any loop bound; remove halt/guard charge. | No universal instruction count established. | Open: primitive program and adequacy. |
| REQ-PQ6-COVERAGE; INV-ALL-SIZE; INV-SEMANTIC-NONVACUITY | The closed theorem has no readiness, count-zero, one-macro, or full-tail-word premise. | Canonical all-size allocation -> every protocol branch -> common run. | Nonzero long/sparse metadata, global interior, ragged tail, absence and repeated reads. | Small experiment did not execute exception/global cases. | Open: all branches in proof. |
| REQ-PQ7-INPUTS | All valid Nat endpoints fit w(n); representable invalid inputs reject in K steps; total Nat wrapper equals specification including out-of-word endpoints. | Endpoint representation -> same guarded run -> total API. | Empty, reversed, n+1, capacity-1 and capacity endpoints. | Domain distinction frozen. | Open: guard and API proofs. |
| REQ-PQ8-UNIFORMITY; INV-ORACLE-INDEPENDENCE | Program is a fixed closed finite value; metadata is counted and read with charged primitives. | Builder headers -> charged setup -> fixed program. | Same-n/different-shape and different-n program equality; omitted metadata cell. | n-specialized experiment is not this proof. | Open: uniform source/program. |
| INV-STORE-AGREEMENT; INV-GLOBAL-PHYSICAL-MACHINE | Agreement on ordered actual reads gives same result, cost and trace; every segment uses one address translation into A(xs). | Whole primitive run -> actual receipts on one store -> capstone. | Change an unread cell; corrupt a read cell; attempted missing physical cell must remain logged. | Existing E1/calculus facts concern another evaluator. | Open: new evaluator theorem. |
| REQ-PQ9-PUBLIC; INV-CERTIFICATE-ANTI-BYPASS | Independent expected type consumes each capstone conjunct and exact object; public alias is identical. | New capstone -> RMQ.Headlines.RMQ -> RMQPaper -> typed validation consumer. | Delete/weakify each public field or substitute a sibling theorem; consumer must fail. | No public claim changed. | Open until complete proof candidate. |
| CHK-PQ10-VERIFICATION; INV-VALIDATION-REACH; INV-MUTATION-REPRODUCIBILITY; REPLAY-EXACT-REGISTRY; REPLAY-SELECTOR-NONVACUITY; REPLAY-SUBPROCESS-DEADLINE | Exact committed registries, expected verdicts and failure surfaces, restoration hashes, bounded subprocesses; final gates and fresh exact-commit audit. | New evaluator and public proposition -> production verification -> independent audit. | Missing/duplicate case, unknown/empty selector, result mutation, descendant timeout, expected-accept control. | Preflight PASS; experiment manifest verified before copying. | Open: new implementation tests and final certification. |

## Verification coverage ledger

### Primitive execution fixtures and final-client replay preparation

The actual numeric run passed S01–S10 in the first full runtime attempt
(171.989 seconds), covering empty/singleton/ties/slice, reversed/out-of-range,
maximum representable endpoints, the outer capacity rejection, a24-element
query and a changed loaded size word that changed the returned result. S11's
singleton had no unread allocated cell, so the fixture checker rejected that
attempt. Replacing its input with24 increasing values and query[0,1) produced
a passing actual unread-cell replacement (123.506 seconds): result some0,
7641 instructions,228 receipts, and identical result/steps/categories/receipts
after changing the unread allocated cell. These finite executions do not
substitute for universal route or arithmetic safety proofs.

PackedQueryContract now contains30 independent expected-type public field
consumers, plus exact proof/proposition alias consumers. It awaits the
unconditional export before elaboration. The fixed replay registry is checked
against the frozen validation plan, complete source declarations and client
names. Registry/selector, outside-marker field, exact runtime-ID and
type-versus-resource-diagnostic controls pass. The Windows owned-descendant
deadline test passed with a real launched descendant absent after termination.
The complete mutation campaign, restored public builds, full final runtime,
production gate and fresh blind exact-commit audit remain open.

### Canonical query semantics and complete LCA safety composition

QueryCorrect discharges every canonical semantic interface. The exact
interiorRangeBlock_source proposition and its protected-register frame are
consumed by lcaCloseProgram_source, then by queryRun_valid_with_lca and the
ordinary-list bridge. The checked final result now states, for every xs,left,
right with no leaf-correctness or readiness premise,
`(queryRun (buildMemory xs) xs.length left right).result =
some(optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)`.
Its halted-status theorem names that identical run. queryNat_exact states the
total if-ValidRange scanWindow contract, including outer word-domain rejection;
queryNat_leftmost yields LeftmostArgMin for every returned index. These results
alone do not assert fitting arithmetic on unbounded mathematical endpoints.

QueryObservations checks the exact174 metadata receipts followed by the
physical expansion of the public trace on valid inputs, and[] on invalid
inputs. It independently proves ReadOnlyTrace, positional raw-read provenance
with transition index/pre-state/instruction/address/reply, whole-Run equality
under supplied-memory agreement, and the exact six-category partition. Its
queryRun_correct_cost_space combines the same actual result/halt, steps≤837572,
and complete data/program/scratch capacity≤2*n+queryCompleteRho n. The residual
is already LittleOLinear. wordWidth_log_lower adds
`log2(n+2)+1≤wordWidth n` to the existing logarithmic upper bound.

LCASafety now checks the entire source controller composition, including
same-block, cross-left, adjacent or active interior middle, candidate merges,
cross-right, initialization and final close packet. Its two remaining local
interfaces are precisely CanonicalFringeSafety (actual fringe Safe with
fitting metadata-matching registers and1104..1106≤E) and
CanonicalInteriorSafety (actual interior Safe with896/897≤E). All LCA caller
parameters are derived from close1200/1201≤2*n; no extra output-margin premise
is needed for `(position-1)+1`. The protected-register invariant composes
checked source safety and running status using the existing write frames.

Final root narrow checks were clean: QueryReference1.25s, QueryCorrect,
complete LCASafety3.30s, QueryObservations3.18s. IC completed all13 local rows
and its canonical479411 run and imported consumers; root independently
consumed its exact source/frame in QueryCorrect. RS completed all13 rows,
canonical wrappers with only Fits/MetadataMatches, E output bounds, actual
compiled runs and imported consumers. SS's complete artifacts and imported
consumers also pass, including actual packet≤2*n for every occurrence.

PQ1-FS and PQ1-IS are now preflighted active safety producers. PQ1-QS is a
preflighted draft waiting for SS's final report, and will consume the completed
LCA composition plus those two producers. Full query arithmetic safety,
public capstone/alias, independent exact-type consumers, replay, final gates
and blind exact-commit audit remain open. No whole-milestone row is closed by
these local candidates or the current source joins.

### Checked complete source joins and static program width

FringeProof.fringeBlock_source now states, for MetadataMatches and the checked
reader interface, that actual status is running, candidateOfRegs7000 is
fringeReference.value, actual receipts equal logicalTraceReads of its exact
trace, and that trace is read-only. Its source contains the charged rank seed,
four actual-length window reads and all33 guarded fringe copies. There is no
supplied seed/window/candidate hypothesis.

LCAProof.lcaCloseProgram_source composes every LCA branch and final close
packet. The remaining local interface is InteriorCandidateCorrect, whose
complete proposition pins status, actual candidate7000, ordered physical reads
and ReadOnlyTrace to packedInteriorRangeMinRead on the canonical global store.
QueryProof.queryRun_valid_with_lca consumes the resulting exact LCA interface
and proves the actual queryRun packet,174 metadata receipts followed by the
ordered whole-query physical expansion, and actual.steps<=queryBudget. This
is the complete compiled controller join; its remaining canonical LCA premise
must be discharged by the interior worker before execution acceptance.

QueryStatic checks queryBudget=837572, querySource.maxEncodedField=8270,
queryRegisterCount=8271 and queryScratchWords=8274. querySource_fieldsFit
and queryProgram_fits cover every encoded scalar field and resolved PC,
including dormant arms and the appended halt, for every n. The proof uses a
constructor-complete source maximum and compile_fits rather than expanding the
compiled instruction list. queryProgramWords_le bounds its literal encoding
length by5*queryBudget; Accounting continues to count its exact value.

The final narrow root passes were clean: full FringeProof, generic complete
LCAProof, QueryProof through charged guard/actual run, Accounting and
QueryStatic. Static inventory took7.76 seconds; previous full source joins
took2--7 seconds each after generic evaluation boundaries were introduced.
The source associations preserve instruction order and ABI. The remaining
canonical interior proof, all-controller reachable arithmetic, public
capstone/alias, replay and blind exact-commit audit still prevent whole-row
closure. These checked joins do not convert their live interfaces into
unconditional canonical evidence.

### Checked rank, window and interior-entry producers

LoadSafety's completed local matrix/report binds numeric-memory fit, actual
span geometry and static code-field bounds to every indexed primitive
transition and every fuel prefix of the same span run. It covers zero-length,
contained, crossing, failed-first and failed-second reads, and the actual
metadata setup. The canonical width and both fixed reader register banks are
instantiated. This is the generic loader-width producer; it does not establish
the full controller's reachable arithmetic bounds.

RankProof's full artifact now checks source equality and actual compiled
result/ordered receipts/frame/budget for word rank, whole rank and each
close/long/sparse wrapper, including missing seeds and empty/ragged words.
The source always performs its three seed reads before presence guards.
ReadOnlyTrace accompanies logicalTraceReads; no non-read event is discarded
by the physical expansion. The exact worker matrix/report records final
propositions and independent consumer checks when finalized.

WindowProof.loadWindowBlock_reference states that source status is running,
register1064 is bitsToNatLE of packedLocalBPWindowBitsRead's value, receipts
are logicalTraceReads of that exact reference trace, and ReadOnlyTrace holds.
loadWindowBlock_canonical_machine instantiates logicalReadBlock and
shapeMemory in the literal appended-halt run at4319 steps, preserving the
same value/trace/frame. InteriorReadProof.interiorReadBlock_reference states
running status, register708 equal to the encoded Option Nat returned by
packedInteriorReadNatOf on the canonical global store's segment20, exact
expanded flat-execution receipts and ReadOnlyTrace. Its only local size
premise is chunkCount<=7; canonical_interior_chunks_le_seven discharges it
for every canonical component width. interiorReadBlock_canonical_machine
then binds all of these conclusions to the actual8698-budget run and frame.
WindowProof and InteriorReadProof passed narrow checks without warnings.

These are checked inputs to the remaining select/interior-navigator/fringe
joins. Full valid-query semantics, complete reachable/controller width,
public identity, replay, final gates and fresh exact-commit audit remain open.
No whole-query acceptance row is closed by this producer evidence.

### Canonical-reader and fixed-controller construction evidence

The source reader is now checked against the same shapeMemory allocation:
`logicalReadBlock_correct shape : ReaderCorrect shape (shapeMemory shape)
logicalReadBlock`. Expanded, for every register bank matching the174 metadata
words and every requested segment/index in8192/8193, its source evaluation is
running, returns the canonical global-store reply encoded as0 or value+1 in8194,
returns its actual bit length in8195, produces exactly readerReceipts in order,
and preserves registers outside8194..8270. This derives canonical successful
span decoding and does not assume successful reads. `logicalReaderRun_correct`
places those conclusions on the actual compileAt0-plus-halt primitive run,
with result/length/receipt/frame equality and steps<=1069. The independent
logicalReaderRun_expectedType pins the actual program, memory, input bank,
result, ordered reads and budget. PhysicalRead's final narrow check passed
without warnings; the local generic loader-width proof is a separate producer.

Safety.lean proves source numeric safety implies actual indexed instruction
safety and every-prefix state fit for the same compiled execution, retaining
its value/read/budget equality. LogicalSpan.lean proves all canonical logical
values and lengths on shapeMemory, and Locate.lean proves the fixed metadata
dispatcher, its1035-instruction size and the charged1383-instruction
setup-plus-location consumer. Their exact local matrices/reports quote checked
propositions, canonical/empty/dead consumers and live boundaries. Root
independently reconstructed the LogicalSpan -> Locate -> PhysicalRead chain;
these are bounded producer audits, not closure of any whole-query row.

SelectSource, InteriorSource and FringeSource have passed narrow syntax checks.
They are fixed scalar source; their canonical control/value/word-safety joins
remain open. QuerySource assembles the intended concrete two-select/LCA/rank
body after charged setup, with the existing endpoint guard. Its new checks and
all whole-query adequacy/width/value proofs remain development work. The
rank/select workers consume the actual reader; no row above is closed merely
by defining the full program or its syntax-derived budget.

The subsequent QuerySource check passes with a generic compiler consumer:
queryRun_refines_source has the exact independently evaluated querySource
result and ordered reads on the actual queryRun at queryBudget. The existing
guard supplies queryRun_invalid, and queryNat_invalid covers the external Nat
wrapper. CandidateProof proves exact left-biased candidate merging.
Scratch.run_frame and compilation's WritesOnly preservation establish
queryRun_finite_registers for every fuel prefix, with every register outside
queryRegisterCount remaining zero. Accounting.query_complete_capacity charges
the literal flattened instruction encodings and queryRegisterCount+3 state
words together with buildMemory at wordWidth; queryCompleteRho_littleO proves
the residual. These modules passed narrow checks without warnings. Evaluating
the closed constants yielded queryBudget837572, registerCount8271 and
scratchWords8274; these readouts are not substitutes for numerical equality
proofs or the remaining canonical controller/width joins.

| Command | Role and covered rows | Unique failure detected | Tree/runtime/deadline policy | Outcome |
| --- | --- | --- | --- | --- |
| project_skill_preflight.ps1, exact RC6 ref, both required roles, actual three-skill catalog | Development setup | Missing/stale governance or runtime role | Clean exact base; seconds | PASS |
| Verify experiment manifest entry length and SHA256 | Development provenance | Changed compiler/fixtures/specification input | External source read-only; seconds | 45 entries PASS before import |
| Targeted lean/lake for changed primitive/allocation modules and direct consumers | Development; REQ-PQ1 through PQ8 | Kernel/proof failure and import drift | One heavy process; warm dependency cache read-only; owned new outputs | Pending |
| Startup smoke, one exact selector, constructor/guard/crossing controls | Development; validation/replay invariants | Wrong semantic layer or initialization regression | Bounded subprocess; before full replay | Pending |
| lake build; lake build RMQPaper; axiom checks | Final-required; CHK-PQ10 and PUBLIC | Full integration and trust dependencies | Aggregate gate may own equivalent builds; avoid duplicate final-tree work | Pending |
| rg hygiene including native_decide and Lean.ofReduceBool; git diff --check; git diff --check 4639223bc8130b0ef752270b5cbdd74325abcd60..HEAD | Development and final-required | Forbidden trust shortcuts and committed whitespace | Seconds; after every scoped commit | Pending |
| scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 | Final-required | Missing companion ledger and design scope | Seconds, final candidate including report | Pending |
| Relevant claim/correspondence/paper gates; scripts/gate.ps1 | Final-required after implementation and fixtures | Public correspondence and integrated acceptance | Prior RC6 aggregate about 82 minutes; use at least 150-minute ownership deadline, short polling; diagnose failing component first | Pending |
| Fresh blind exact-commit audit | Final-required, all rows | Independent frozen-contract reconstruction | Candidate SHA and frozen requirements; no worker verdict given as evidence | Pending |

## Construction evidence supplement (whole-query rows remain open)

The following checked producers refine the original evidence plan; none is a
substitute for the full requirement attached to its row.

- REQ-PQ1/3/4/8: Allocation.lean defines the same concrete buildMemory and proves
  `buildMemory_capacity_le xs` and `buildMemory_with_machine_capacity_le xs P R`.
  The residuals are proved LittleOLinear and wordWidth is at most
  `192*(log2(n+2)+1)`. Width.lean proves all174 metadata words and every actual
  allocation word fit, its length/first-missing address fit, and valid endpoints
  fit. The source DAG is List Int -> cartesianShape -> metadata plus denseWords
  of the full old allocation -> buildMemory; no execution correctness is yet
  attached to this builder. Checkpoints1ae0bb4,13d1885,9e2720b carry its producers.
- REQ-PQ2/5 and provenance/agreement invariants: Calculus.lean proves run_add,
  exact category partition, actual prefix-indexed transition/read provenance
  and full-run equality under agreement on the first actual read observations,
  including missing cells. These are generic evaluator facts; they do not
  provide whole-query liveness or a concrete query budget.
- REQ-PQ2/6: Span.lean's loadOldCellNat_repacked universally recovers every old
  cell's numeric option from the same repacking. Source Structured.Block syntax
  contains only scalar actions, fixed expansion, branches and exit. The newly
  checked compiler and SpanAssembly join source results/ordered short-circuit
  receipts to actual primitive execution. Canonical logical-read/controller
  composition remains open.
- REQ-PQ7: Guard.lean's valid_inputs_encode covers every valid mathematical
  interval. guardedProgram_invalid states that for every body and arbitrary
  memory, the actual run at body.size+10 returns some0, has no reads and stays
  within that budget on invalid intervals. This is the invalid branch of a
  future fixed query body, not the complete total Nat API theorem.
- Scalar and RegularLocate narrow checks pass. The regular descriptor source
  uses19 fixed instructions; presence and zero bit length remain distinct.
  Canonical descriptor selection and global physical logical-read refinement
  still require their own conclusions.

Narrow checks have used the private copied dependency cache and one Lean
process at a time. No aggregate gate is claimed at this construction stage.
Full verification and blind audit remain pending the actual capstone.

## Coordinator evidence reconstruction (2026-09-11)

Appended by the coordinator after the worker stopped, reconstructed from source
and checked types rather than worker narrative, and after an independent
ten-lens audit. Candidate Lean state: f2f2a0a (base 4639223). Row statuses
remain coordinator-owned; this section is evidence and records no acceptance.

Common object chain. Every capstone field names the same four objects: the
builder `buildMemory xs` (`shapeMemory (SuccinctClassic.cartesianShape xs)`,
which is `repackWords (metadata shape) (wordWidth shape.size)
(packedReviewerMemory shape)`), the closed program `queryProgram`
(`guardedProgram queryBody`), the input state `initialState xs.length left
right` (registers 0, 1 and 2 hold left, right and n; every other register is
0; pc 0; running) and the fuel `queryBudget`. `run` is the nine-constructor
evaluator of Primitive.lean. The public alias
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery : FullyChargedPackedQueryCapstone`
is `fullyChargedPackedQueryCapstone_holds`, imported by RMQPaper.
`RMQ/Validation/PackedQueryContract.lean`, imported by RMQ.lean so that the
default build elaborates it, restates all 33 fields at independently written
types (checkC01 to checkC33) and adds 38 definitional pins and width controls.
Axioms: propext, Classical.choice, Quot.sound.

| IDs | Checked propositions | Consumer | Anti-vacuity challenge and outcome | Status |
| --- | --- | --- | --- | --- |
| REQ-PQ1-CONSTRUCTION; INV-STORE-IDENTITY; INV-PROOF-SEPARATION | `buildMemory : List Int -> List Nat`; `run : Memory -> Program -> Nat -> State -> Run`; `State` holds only registers, pc and status. The space fields (C04, C05) and the execution fields (C18, C19, C23 to C33) quantify the identical `buildMemory xs`, `queryProgram`, `initialState xs.length left right` and `queryBudget`. | checkC04, C05, C18 to C33; pins for run, step, execute, initialState and inputRegisters | Same-size different-shape program equality holds definitionally because `queryProgram` is a closed constant. Every check spells `buildMemory xs`, so a sibling allocation fails to elaborate. Runtime S10 changes loaded metadata word 0 and the packet changes to rejection; S11 changes an unread cell and the whole run is unchanged; C30 covers every memory. | Evidence complete |
| REQ-PQ2-EXECUTION; INV-VALUE-DEPENDENCY; INV-TRACE-EXECUTION; INV-READ-BACKING; INV-NO-SYNTHETIC | C31 `specResult`: every valid range returns `some (scanWindow xs left (right - left) + 1)` on the run itself. C18 and C19: representable endpoints give `.halted (optionNatPacket (queryTraceResult xs left right).value)`. C16 `natContract`; C17 `leftmost`. C27 `positionalReadBacking`: transition index, pre-state equal to the final state of `run` at that index, running status, instruction fetched from `queryProgram` at the pc, the `execute` equation, a `load` whose address is the pre-state register and whose reply is `(buildMemory xs)[address]?`. C28 `orderedLogicalRefinement`: valid-range reads equal the 174 metadata receipts followed by `logicalTraceReads shape (buildMemory xs) trace`, which covers every rank, select, fringe, window, interior and LCA read of the RC6 logical trace, two loads for a crossing cell, with repetitions as list positions; invalid ranges have `[]`. C29 `ReadOnlyTrace`. Producers: QueryProof.queryRun_valid_with_lca over the rank, select, fringe, window, interior and LCA source proofs; QueryCertificate.queryRun_scanWindow. | checkC16 to C19, C27 to C29, C31; pins for Run.reads, Run.result and queryNat | R01 changes the specResult projection from plus one to plus two and the producer rejects at the specResult initializer (manual run; replay pending). Weakening C18 or C31 fails the consumer (replay C18, C31). N01, a wrong literal answer, is rejected by the runtime checker. `Run.reads` is `transitions.filterMap receipt` (pinned), so no synthetic event can enter it. S10 is the returned-value dependency witness. | Evidence complete; replay pending |
| REQ-PQ3-SPACE; INV-PUBLIC-COMPOSITION; INV-PROGRAM-ACCOUNTING; INV-CATEGORY-SEPARATION | C01 `LittleOLinear allocationRho`, where `allocationRho n = packedReviewerRho n + (metadataWordCount + 1) * wordWidth n` is a fixed function. C04 `(buildMemory xs).length * wordWidth xs.length <= 2 * xs.length + allocationRho xs.length`. C02 and C05 add the literal flattened instruction encoding and `queryRegisterCount + 3` words at the same width under the fixed `queryCompleteRho`. C11 to C14: encoding at most five words per instruction, 8271 registers, 8274 scratch words, every register at or above 8271 is zero at every fuel. Transitions and receipts are proof observations of `Run`, not machine registers; measured runtimes are not claims. | checkC01, C02, C04, C05, C11 to C14; pin for LittleOLinear | An added header or padding cell changes the literal `(buildMemory xs).length` in C04, so the obligation changes (structural; no committed mutation). The literal object spelling in checkC04 and C05 rejects a sibling allocation. Disclosed magnitude: the code and scratch term exceeds n for every n below about 2^28, so it is lower order only asymptotically. | Evidence complete |
| REQ-PQ4-WIDTH; INV-WORD-WIDTH; INV-ADDRESS-WIDTH; INV-WIDTH-SCALING | C03 `log2(n+2)+1 <= wordWidth n <= 192 * (log2(n+2)+1)`, with `wordWidth n = 32 + 8 * packedReviewerCellWidth n` depending on n only. C06 stored words fit; C07 every address up to and including the allocation length fits; C08 every encoded field (tags, registers, immediates, jump targets, dormant arms, the appended halt) of every instruction fits `wordWidth n` for every n. C23 final state; C24 every indexed transition is `Instruction.Safe` (result below 2^w, no underflow, nonzero divisor, shift below w) with a fitting after-state; C25 every fuel prefix; C26 receipt address and reply below 2^w; C32 `noFailedLoads`. No `jumpRegister` is emitted, so there are no return PCs; register identifiers are at most 8270. | checkC03, C06 to C08, C23 to C26, C32; pins for Instruction.Fits, Safe, encoding, operands and State.Fits; width controls | At wordWidth 0 an oversized register, jump target and immediate are rejected and the largest immediate is accepted. n = 0 and 1 fall under C08's quantifier (wordWidth 0 is 112). Dropping the shift clause of Instruction.Safe breaks the producer at Safety.lean:203. | Evidence complete |
| REQ-PQ5-COST; INV-INSTRUCTION-ATOMICITY | C19 `halt` with fuel `queryBudget` for every representable endpoint pair is the adequacy fact: the run halts within C09's 837572 steps, which C10 equates with the program length. C20 and C33: every representable invalid input returns packet 0 with no reads within six steps (exactly four or six by queryRun_invalid_steps). C21 `stepBound` and C22 `categoryPartition` hold for every fuel-bounded run and carry no cost content by themselves. `execute` (pinned) performs one scalar operation per constructor; the program is straight-line (forward jumps only), so no loop grows with n; the sparse-count prelude is replaced by sparse-count-dependent descriptor bases serialized in the counted metadata prefix. | checkC09, C10, C19 to C22, C33; pins for execute, Instruction.category and Run.categoryCount | D01 collapses the non-load categories to control; the producer and RMQPaper still build and the consumer rejects only at the category pin (manual run; replay pending). Replacing an arithmetic primitive by a scan changes `execute` and fails its pin. A hidden loop would need a backward jump the compiler does not emit. | Evidence complete; replay pending |
| REQ-PQ6-COVERAGE; INV-ALL-SIZE; INV-SEMANTIC-NONVACUITY | `fullyChargedPackedQueryCapstone_holds` has no hypothesis and quantifies every `xs : List Int`; the conditional helper's only premise is discharged by queryRun_execution_safe. Long and sparse wrappers, ragged tails and global and cross-macro interior routes are proved in the universal source theorems consumed by QueryProof. Absent, dead and empty logical reads make zero physical loads (DD-20260911-PQ1-017); a failed primitive load would fault and be logged, and C32 shows valid runs have none. Repetitions are list positions in C28; ties follow C17. | checkC17, C28, C32 | Runtime S03 tie; S13 cross-block interior (18 reference interior reads), S14 same block, S15 adjacent blocks, with routes asserted from the shape and the reference trace. Cross-macro and global interior (n from 1000 and 3456), nonzero long count (more than 13,000 elements) and nonzero sparse count (n at least 2^96) are beyond interpreter fixtures and rest on the universal theorems, as the contract permits. | Evidence complete |
| REQ-PQ7-INPUTS | C15: every valid pair encodes to `initialState` and both endpoints fit. C16: the total Nat contract, where out-of-word endpoints give `encodeInputs = none` and are never valid. C20 and C33: representable empty, reversed, beyond-n and capacity-minus-one inputs are rejected with packet 0, no reads and at most six steps. `encodeInputs` is an uncharged value-level check; no instruction bound is claimed for parsing unbounded integers. | checkC15, C16, C20, C33; pins for encodeInputs, queryNat and ValidRange | S05 reversed, S06 right = n + 1, S07 capacity minus one, S08 outer capacity (value level only), S12 empty interval. | Evidence complete |
| REQ-PQ8-UNIFORMITY; INV-ORACLE-INDEPENDENCE | `queryProgram : Program` has no parameter; C08 holds for every n; geometry comes from the 174 counted metadata words loaded by the first 174 charged receipts (C28). Runtime expected answers are literals rechecked against `scanWindow`; routes come from the shape and reference trace, never from the machine. | checkC08, C28 | Same-n different-shape and different-n program equality are definitional. An omitted metadata cell would change the 174 receipts fixed by C28. | Evidence complete |
| INV-STORE-AGREEMENT; INV-GLOBAL-PHYSICAL-MACHINE | C30: any memory agreeing with `buildMemory xs` at every actual read address yields the identical Run (result, steps, transitions, receipts). C26 to C28 place every read of every segment in the one pre-execution store; failed accesses are logged by `execute` and none occur (C32). | checkC26 to C28, C30, C32 | S11 unread-cell change leaves the run identical; S10 read-cell corruption changes the packet. | Evidence complete |
| REQ-PQ9-PUBLIC; INV-CERTIFICATE-ANTI-BYPASS | `publicProposition : SuccinctRMQFullyChargedPackedQuery = FullyChargedPackedQueryCapstone := rfl`. RMQPaper exports the alias. All 18 current-fact surfaces document it as a CANDIDATE with its caveats (DD-20260911-PQ1-019); the 210 and 427 bounds stay distinct, enforced by claim-drift policy v28 (WDD-20260911-PQ1-010); the reusable proof ideas are in DIGESTION_LOG, PROJECT_DIGESTION_CURRENT and FAMILY_SUMMARY. The replay registry covers C01 to C33, P01 (public alias), A01 (unchanged control), D01, R01 and N01. | PackedQueryContract (33 checks, 38 pins) | Field weakening, alias replacement, definition collapse and projection mutation each have a named rejecting surface in the committed registry. | Open: paper absorption and repin (a later commit, because a commit cannot pin itself) and the full replay on the committed candidate |
| CHK-PQ10-VERIFICATION; INV-VALIDATION-REACH; INV-MUTATION-REPRODUCIBILITY; REPLAY-EXACT-REGISTRY; REPLAY-SELECTOR-NONVACUITY; REPLAY-SUBPROCESS-DEADLINE | Coordinator cold rebuild and axiom inventory; builds, axiom checks, hygiene and whitespace on the final Lean tree; runtime 15 of 15 in 309 s through `runArray` (proved equal to `run`), with S02 and S05 also executed by `run`; Lean-free registry, selector-boundary, provenance and deadline self-tests under PowerShell 7.6.6 and Windows PowerShell 5.1; per-commit design certification of every PQ1 commit. | packed_query_replay.ps1; gate.ps1 | Missing, duplicate, reordered, bound-empty, whitespace and unknown selectors fail at the script boundary; a real descendant is absent after its deadline on both hosts; the provenance check rejects the known-bad blobs of 8910d53. | Open: full 38-case replay on the committed candidate, final strict design and claim checks, aggregate gate on both hosts, fresh blind exact-commit audit |

## Explicit deferrals

Native performance optimization and preprocessing complexity are separate
unless a proof dependency requires them. No frozen theorem requirement is
deferred. Publishing, pushing, merging the original checkout, and deleting
other worktrees are not authorized by this task.

## Frozen inherited invariants

The following source block is copied byte-for-byte from the canonical
completion gate at the exact governance ref, including its original line
breaks. It is part of this matrix's frozen requirement text.

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;
- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;
- `INV-SEMANTIC-NONVACUITY`: semantic coverage, liveness, ownership, and
  refinement predicates are derived from the operational construction they
  describe. A predicate defined to be `True`, an enumeration restated as
  membership, or a separately hand-written consumer label does not establish
  operational liveness by itself;
- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;
- `INV-STORE-AGREEMENT`: supplied-store agreement determines result, cost, and
  the relevant trace;
- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;
- `INV-WORD-WIDTH`: stored and returned words fit one declared modeled
  machine word;
- `INV-ADDRESS-WIDTH`: every executed address, dead/sentinel address, and
  encoded instruction operand fits the modeled machine word, not merely the
  host array bounds. Constructor-exhaustive evidence must include register
  identifiers, branch/jump targets, dormant code, and arithmetic operands;
- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;
- `INV-PROGRAM-ACCOUNTING`: input-dependent constants and metadata carried by
  executable code are counted machine data or are derived uniformly from
  counted/public inputs. Calling shape-specialized data "program code" does
  not remove it from the payload/state accounting obligation;
- `INV-ORACLE-INDEPENDENCE`: executable fixtures and edge-case expected values
  come from an independent specification or a theorem already connected to it,
  never from the implementation result being tested;
- `INV-VALIDATION-REACH`: executable validation imports and runs the new
  semantic layer. A validator for the predecessor implementation is regression
  evidence only and does not validate the new machine;
- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;
- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;
- `INV-NO-SYNTHETIC`: synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;
- `INV-CATEGORY-SEPARATION`: payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

The following IDs apply when the public claim has the corresponding shape:

- `INV-PUBLIC-COMPOSITION`: a theorem combining space, exactness, cost,
  provenance, or machine claims proves them about the same construction and
  execution and over the same validity domain. Conjoining true theorems about
  different payloads or guarded and unguarded executions is not closure.
- `INV-CERTIFICATE-ANTI-BYPASS`: every mandatory field advertised by a public
  certificate is projected by a checked typed consumer at the exact proposition
  and object arguments required by the acceptance contract. Deleting or
  weakening a field, or replacing it with a sibling fact, must break that
  consumer rather than leave only constructor initializers and prose unchanged.
- `INV-MUTATION-REPRODUCIBILITY`: when acceptance relies on an exhaustive,
  production, or public-dependency mutation campaign, the candidate contains a
  versioned runner or fixtures that replay every claimed case, check the exact
  expected failure/acceptance surface, restore tracked state, and leave the tree
  clean. Report prose, copied terminal output, and dangling Git objects are not
  replayable evidence. A public theorem additionally has a checked exact-type
  consumer that fails when the advertised dependency is removed; `#print
  axioms` over the theorem's current type is not such a consumer.
- `INV-GLOBAL-PHYSICAL-MACHINE`: a physical-machine claim supplies one
  pre-execution store/word array and a checked address translation for every
  executed segment, including failed/dead accesses. A theorem for one suffix or
  component is not a whole-machine embedding.
- `INV-WIDTH-SCALING`: one query-independent word-width declaration bounds all
  stored words, addresses, sentinels, operands, and primitive results, and its
  capacity/width is related to input size in the form required by the public
  word-RAM claim. A standalone asymptotic fact about an unconstrained width
  function is insufficient.


## Coordinator acceptance (2026-09-12)

Status: **ACCEPTED**. All 34 frozen requirement/invariant IDs are closed in
`PQ1_COORDINATOR_ACCEPTANCE.md`, with exact proposition/composition evidence
in the immutable `../audit_reports/PQ1_FRESH_BLIND_4c89378.md` report committed
at `d21b190139fa810291ae271974ec00cde58af965`. Both-host full gates certify
repaired source `6562ff62d14b17e918e7149f896bd0657ffd5aa0`. The original P1
selector failure was repaired; the later P3 wording correction changes no
theorem. Earlier Open/pending rows remain historical evidence, not live gaps.
This append-only disposition does not alter any frozen requirement text.

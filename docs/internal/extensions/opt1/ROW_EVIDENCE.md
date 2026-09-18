# OPT-1 row-specific proof evidence

Active append-only evidence ledger on source freeze ac5af8e416f906391dc117f083a883acc053a268.
Full semantic replay passed; final dependency/audit/certification outcomes remain
open until exact completed receipts are supplied.
The 35 original frozen rows remain byte-identical. Nothing here records
coordinator acceptance.

Completed semantic evidence: runtime-replay/evidence/full-runtime.json records
23 positives, four expected corruptions, 16 script boundaries, five direct Lean
selector controls and exact 646-source/artifact restoration at the proof freeze.
It closes the semantic execution observations below; actual certificate kernel
mutations and externally scheduled certification are still pending.

## Shared object and consumer identity

Let `S = .seq querySource (.exit 3)`, `F = queryRegisterCount = 8271`,
`P = compactAt S F 0 0`, `B = compactBound S = 151978`,
`M = buildMemory xs`, `I = initialState xs.length left right`, and
`W = wordWidth xs.length`. These abbreviate actual definitions, not new
objects. `compactQueryProgram = P`, `compactQueryRun M ... = run M P B I`,
and `compactQueryProgramWords = (P.map Instruction.encoding).flatten.length`.
The same record has 39 mandatory fields. For every field `f`, the checked
`CertificateConsumers.f_expectedType` projects `certificate.f`
at an independently written exact proposition, and `f_canonical` applies
that consumer to `compactPackedQueryCapstone_holds`. certificate-replay/FIELDS.json
v3 freezes those exact types; the replay never derives an expectation from a
mutant declaration.

The space field is literally
`((M.length + (P.map Instruction.encoding).flatten.length + (compactQueryRegisterCount + 3)) * W)
 <= 2 * xs.length + compactQueryCompleteRho xs.length`.
The residual is `allocationWithMachineRho compactQueryProgramWords
compactQueryScratchWords`; it has `LittleOLinear` without a size threshold.
All physical safety fields use the same representable-endpoint guards
`left < 2^W` and `right < 2^W`; list-facing exactness is unconditional and
returns none outside ValidRange. The validity domain never switches stores.

## Requirement rows

- REQ-OPT-BUDGET: for every memory/n/left/right, the original complete
  `queryRun` has steps at most 150739. Full `Run` equality connects the
  original adequate fuel to 150739, through an actual `RunsTo` witness and
  the structural branch recurrence. This is stronger than truncation at the
  displayed fuel. `originalExecutionBound` and `originalReducedFuel` pin both
  propositions. Both branches, early stops and malformed memory are in the
  universal domain; executable branch/fault controls provide concrete checks.
- REQ-OPT-COMPILE: compactAt emits ordinary constants, branches, decrement
  and jump around one body copy. Constructor induction proves literal length;
  universal simulation proves status/register agreement and exact ordered
  receipts, an actual transition segment and adequate execution. Positive
  loops rebase body agreement at each actual state and protect parent counters;
  zero loops emit no control code. Literal P has 212964 instructions, strictly
  below the unchanged original program. `emittedProgram`, `programLength`,
  `programReduction`, `completedExecution` and `adequateFuel` consume this route.
- REQ-OPT-RUN: arbitraryMemoryObservations equates result and the complete
  ordered attempted receipt list with queryRun for every memory, including
  failed loads. Canonical result/halt/invalidGuard and natContract/leftmost
  connect that same run to scanWindow/LeftmostArgMin. QuerySafety instantiates
  generic TraceSafe/global-fit transport on M/P/B/I/W, covering every indexed
  transition and every fuel prefix; programFieldsFit covers dormant fields.
- REQ-OPT-SPACE: completeCapacity counts literal flattened code, the bank
  8273 and three machine-state words. unusedRegisters states every r>=8273
  is zero after every fuel, including early prefixes. The two added loop
  registers are therefore counted, not hidden behind a proof field. Exact
  instruction/encoding recurrences and direct literal measurements coincide.
- REQ-OPT-CONSUMER: the single inhabitant supplies all 39 fields without a
  supplied correctness or safety hypothesis. The 78 fixed generic/canonical
  consumers pin every advertised field. Baseline Packed files and public
  aliases are unchanged; the extension is additive. The field campaign must
  demonstrate deletion/weakening rejection after the mutant producer compiles.
- CHK-OPT-CONTROLS: semantic C01-C13, Q01-Q10 and N01-N04 registry covers
  branches/sequences, zero/one/repeated/nested loops, early halt/fault,
  empty-body boundaries, initial stopped states, ties/invalid endpoints,
  same/adjacent/interior routes and malformed metadata. Actual final outcomes
  must be recorded from the completed production run, not startup alone.
- REPLAY-EXACT-REGISTRY: production runners pin semantic 23 positives plus
  four rejects, and certificate v3 80 cases (78 rejects/two accepts), exact
  order/names/counts, and executed-versus-selected equality. Preparation-only
  cases do not count as executed producer/consumer checks.
- REPLAY-SELECTOR-NONVACUITY: the script distinguishes omitted selection from
  explicitly empty/blank/malformed/unknown; valid selection must execute exactly
  one registered case. Direct Lean/environment channels require their own
  completed outcomes, not inference from script-only probes.
- REPLAY-SUBPROCESS-DEADLINE: owned_process_tree supervises each actual child
  and preserves exit/stdout/stderr plus timeout/cleanup state. Windows probes
  include a verified descendant and environment absence/presence restoration.
  POSIX remains uncovered on this host. All case mutations occur in isolated
  copies; finally restores exact bytes and baseline Git/import hashes.
- CHK-OPT-DEVELOPMENT: focused source/hash-pinned module and typed consumer
  checks cover every new proof layer. First failed attempts and later repairs
  remain recorded. The scheduling-overlap incident is disclosed separately;
  later checks used one owned Lean process at a time.
- CHK-OPT-FINAL: explicit new capstone/consumer imports and axiom inventory
  have completed. Exact original-base and returning-base whitespace checks
  pass at the source freeze. Full Lake/aggregate certification needs the
  coordinator-scheduled host slot; no local narrow check substitutes for it.
- CHK-OPT-TRUST: full RMQ/lakefile trust scans have no matches, including the
  separate native-reduction scan. The 93-root builtin axiom union has exact
  existence/visited coverage and two standard public prints, with only
  propext/Classical.choice/Quot.sound. It is a union, not 93 separate inventories.
- CHK-OPT-CONDITIONAL: strict claim drift and original-base strict design
  checks pass at source freeze. Public prose states code/encoding and certified
  upper bounds; it makes no attainment, optimality or native-speed claim.
  Final report additions still require their own report-sensitive checks.
- CHK-OPT-AUDIT: source review must identify its exact target and limitations.
  Worker review is not coordinator acceptance.

Completed semantic evidence: runtime-replay/evidence/full-runtime.json records
23 positives, four expected corruptions, 16 script boundaries, five direct Lean
selector controls and exact 646-source/artifact restoration at the proof freeze.
It closes the semantic execution observations below; actual certificate kernel
mutations and externally scheduled certification are still pending. Fresh independent final audit
  and scheduled certification remain external milestones until recorded.

## Inherited invariant rows

- INV-STORE-IDENTITY: completeCapacity, result, safety, receipts and agreement
  all literally use M and P above. The consumers fix those arguments, so a
  sibling allocation cannot discharge the advertised field without equality.
- INV-VALUE-DEPENDENCY: executable compactAt depends only on fixed source
  syntax and layout; initialState depends only on n/endpoints. Query execution
  receives array values only through M and Primitive.execute.load replies.
  run_eq_of_agree proves agreement on actual attempted reads determines the
  whole run, including result, not just its log. Source/refinement proofs do
  not occur in executable definitions. Malformed metadata control changes the
  returned result and compares old/compact executions on the changed memory.
- INV-SEMANTIC-NONVACUITY: simulation relates actual RunsTo transitions to
  independent Block.eval; its relation includes final status, all source
  registers and ordered receipts. It is not True or a list of consumer labels.
  Compiler mutations are tested through the same verifyCompiler predicate
  and literal C05 status/register/read/step expectation as the positive case.
- INV-TRACE-EXECUTION: compactQueryRun unfolds to Primitive.run; receipts are
  filtered from its real transitions. positionalReadBacking retains index,
  producing instruction, the folded prefix pre-state, execution equation,
  address register and reply from M. Repeated equal receipt values retain
  their positions and multiplicity.
- INV-STORE-AGREEMENT: suppliedMemoryAgreement quantifies over each receipt
  in the canonical compact run and equates full Runs on agreeing supplied M.
  The generic producer also works on arbitrary memory and includes failures.
- INV-READ-BACKING: at every indexed receipt-producing transition, the
  instruction is load, address equals its pre-state address register, and reply
  equals M[address]?. noFailedLoads supplies successful replies on valid ranges.
- INV-WORD-WIDTH: memoryWordsFit and finalStateFit use W; transitionSafety
  checks Instruction.Safe plus after.Fits for every real transition. readWidth
  constrains the address/reply value at that actual occurrence.
- INV-ADDRESS-WIDTH: allocationAddressesFit includes address=M.length (dead
  sentinel), programFieldsFit quantifies every instruction in P, and indexed
  transition/read safety covers actual address operands. Host bounds alone
  are not the conclusion; all bounds are against 2^W.
- INV-INSTRUCTION-ATOMICITY: Compact adds no Instruction/Action constructor
  and does not alter Primitive.execute. Each loop control is an existing
  ordinary primitive transition; the bound charges executed body/control steps.
- INV-PROGRAM-ACCOUNTING: completeCapacity includes literal numeric opcode
  and operand encoding, including count constants and targets. P is fixed
  independent of xs; scratch includes the fresh pair and state words. No
  input-specific metadata is moved from counted M into uncounted code.
- INV-ORACLE-INDEPENDENCE: fixture answers/receipts/steps are literal or derived
  from scanWindow and independent source evaluation, before comparing the
  actual run. Block-route checks use Cartesian shape/logical close positions;
  they do not infer the route from the compact result being tested.
- INV-VALIDATION-REACH: PackedOptimized imports the new capstone/emitter and
  runs actual compactQueryProgram/compactAt through proved ArrayRun; compiler
  fixtures additionally compare list-run observations. Baseline runtime alone
  would not establish this row.
- INV-ALL-SIZE: natContract quantifies every List Int and both Nat endpoints,
  with exactly ValidRange selecting scanWindow versus none. Canonical raw
  answer/trace theorems have no size/readiness activation premise; physical
  safety uses only the declared endpoint representability guards.
- INV-PROOF-SEPARATION: executable emission/run/query definitions use no
  certificate, proof field or extracted semantic answer. CompactPackedQueryCapstone
  is Prop and records facts about already defined executable objects.
- INV-NO-SYNTHETIC: every receipt comes from Primitive.execute on the same M,
  and positionalReadBacking identifies its actual producing load/pre-state.
  No post-hoc trace constructor or decorative reread is added by compilation.
- INV-CATEGORY-SEPARATION: emitted instruction count 212964, encoded numeric
  words 722339, modeled execution bound 151978, scratch 8276, and asymptotic
  bit capacity are distinct quantities. The original bound 150739 concerns
  the original complete run. Runtime measurements are validation timings.
- INV-PUBLIC-COMPOSITION: all 39 fields inhabit one record on the literal
  M/P/B/I/W chain. Representable invalid ranges halt at packet zero with no
  reads; validInputs proves valid endpoints fit, connecting unconditional
  natContract to guarded physical safety. No guarded/unguarded sibling run
  is silently substituted.
- INV-CERTIFICATE-ANTI-BYPASS: each mandatory field has generic and canonical
  exact-type consumers. The campaign deletes its field/initializer or weakens
  both to True/trivial, builds that altered producer, then requires the fixed
  consumer to fail at the advertised field/type. Actual 80-case evidence is
  mandatory; successful source preparation is not a dependency check.
- INV-MUTATION-REPRODUCIBILITY: committed versioned runners/FIELDS/registries
  generate every case, pin expectation and failure surface, preserve errors
  and restore isolated copies and tracked-source/import hashes. Controls must
  reject fixture loss and admit unchanged/nonsemantic producer cases.
- INV-GLOBAL-PHYSICAL-MACHINE: P executes one M containing baseline metadata
  and all packed payload segments. OrderedLogicalRefinement links every read
  to the existing whole-query logical trace plus fixed metadata prefix;
  physical backing and capacity concern that whole M, not a component slice.
- INV-WIDTH-SCALING: widthBounds states log2(n+2)+1 <= wordWidth n <=
  192*(log2(n+2)+1). The same query-independent width scales all counted data,
  code, scratch, stored words, sentinels, instruction fields and real safety
  conclusions. Complete residual remains little-o of n under that width.

## Final local execution evidence, bbbe652

The earlier pending field-campaign references above are now discharged by the
complete actual 80-case producer/consumer run at
bbbe652fa41fa40bf2530b5e2f09c4c225c0e896. Every one of the 39 FIELDS.json
propositions has both D and W cases: its altered Certificate and Capstone
compile, then the unchanged generic expected-type consumer fails at that
exact field and required proposition. All 39 canonical consumers remain
present in those fixed bytes. The unchanged and comment-only controls compile
all three modules. No expectation is derived from a mutant type.

REQ-OPT-CONSUMER, REPLAY-EXACT-REGISTRY, INV-CERTIFICATE-ANTI-BYPASS and
INV-MUTATION-REPRODUCIBILITY now have actual full-case evidence rather than
preparation-only results. The other construction/semantic/invariant rows use
their already checked propositions and common M/P/B/I/W composition above,
plus the completed 27-case semantic registry. Mandatory capstone fields named
in those rows are all covered by the 39 deletion/weakening pairs, including
completion/fuel, literal code/space, read backing, agreement and global safety.

The raw campaign records 243 stages: 160 successful producer compilations,
80 fixed-consumer checks and three probes. Its two accepts and 78 rejects match
the exact registry in order. All stderr streams are empty; only the intended
field diagnostics occur in rejected consumers. Isolated originals, private
producer artifacts and the 259 immutable dependencies are hash-checked.
certificate-independent-check.py/json independently reconstructs these facts
from the actual stage files and restored bytes. Replay reports retain focused
controls, first setup failure and both earlier mixed-diagnostic witnesses.

CHK-OPT-DEVELOPMENT, CHK-OPT-TRUST and the local components of CHK-OPT-FINAL
retain their explicit build/consumer/93-root axiom evidence. No Lean, validator,
field, runtime or axiom source changed after its checked proof freeze; only the
certificate runner changed and its complete actual campaign exercised that
repair. Final-report claim/design/hygiene/range receipts apply to the final
documentation changes. The mandatory externally scheduled aggregate and
exact-candidate acceptance phase remains open under CHK-OPT-FINAL/AUDIT.
SCHEDULED_FINAL_REQUEST.md names that boundary; no row records ACCEPTED.

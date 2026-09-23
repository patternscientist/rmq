# OPT-1 frozen acceptance matrix

Handle: OPT-1. Requested title: `(OPT-1) Tighten and compact packed compilation`.
Base and workflow governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/opt-1-packed-compiler`.
Worktree: `C:/Users/poin/.codex/worktrees/1580/RMQ`.
Template: `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
Frozen before proof edits, 2026-09-12. Requirement text and IDs are immutable;
evidence is appended in row-keyed sections or linked phase artifacts.
Only the coordinator can amend requirements or record acceptance.

The join is a smaller certified query program and tighter instruction theorem
over the unchanged succinct allocation. The required declarations are
`RMQ.SuccinctFinal.PackedWordRAM.Optimization.branchSensitiveQueryBound` and
`compactPackedQueryCapstone_holds` in
`RMQ/Core/WordRAM/Optimization/Capstone.lean`.
The first bound is a checkpoint, not closure of this two-part target.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-OPT-BUDGET` | Prove branch-sensitive execution bounds from actual compiler/run semantics, then instantiate the actual query source. The measured candidate recurrence is skip=0, action/exit=1, seq=sum, ifZero=max(1+zero,2+nonzero), repeat=count*body; querySource plus halt evaluated to 150739. Re-derive it and prove that bound or a corrected, strictly smaller-than-837572 universal bound if a precise counterexample shows the candidate recurrence wrong. Prove the bound on the existing complete queryRun with its original adequate fuel, and prove that running the original queryProgram with the new smaller fuel halts with the same answer and ordered receipts. Merely bounding the steps of run at the smaller fuel by that fuel is tautological and does not discharge this row. No literal constant without the execution bridge. | Local and join | For every memory and initial state at PC zero, the original compiled block has an actual RunsTo segment of length at most the recurrence. Derive equality of complete runs at adequate old and new fuel; instantiate querySource. | Structured.Block.eval -> existing compileAt -> RunsTo -> original queryRun -> branchSensitiveQueryBound -> compact capstone | Both branch directions, early halt/fault, empty bodies, original fuel and smaller fuel equality; pending. | None yet. | Open |
| `REQ-OPT-COMPILE` | Implement actual compact code emission using charged counted loops and/or reusable subroutines. Prove simulation, termination/fuel, jump/return behavior, register frames and actual code-size accounting. The preliminary six-instruction loop estimate was 213038 instructions and depth one; it was not an emitted program. Achieve a strict emitted-code reduction against current queryProgram and report the independently checked concrete size. | Local and join | Actual emitted Program; source evaluation equivalence up to declared fresh registers; adequate fuel; exact emitted length strictly less than queryProgram.length. | Compact emitter -> actual Primitive.run -> source evaluator -> query refinement -> capstone | Nested loops, zero/one/repeated iterations, fresh-counter collision, boundary jumps and early exits; pending. | None yet. | Open |
| `REQ-OPT-RUN` | Prove whole-query exact answers, representable-invalid behavior and safety of every primitive/prefix/register/address/encoded operand on the same buildMemory allocation. Preserve the ordered attempted data-read/reply behavior, or explicitly prove the exact accepted observation relation if an optimization removes redundant reads; do not silently weaken it. Current target preserves the ordered trace, so a change requires a reviewed contract amendment. | Local and join | Every xs and representable endpoints: compact run halts at reference packet, exact ordered receipt equality to queryRun; every prefix and transition safe in wordWidth xs.length; every encoded field fits. | Same buildMemory xs, initialState, wordWidth and compactProgram in all conjuncts; existing query correctness/safety transported by proved simulation. | Invalid queries, missing load and malformed metadata; compare ordered attempts including multiplicity; pending. | None yet. | Open |
| `REQ-OPT-SPACE` | Account for compact code encoding and added loop/subroutine registers/stack in complete 2n+o(n) space with the existing word-width convention or a proved conservative common refinement. Input-dependent constants cannot migrate into uncounted code. | Local and join | Complete capacity for buildMemory plus actual flattened instruction encoding plus all machine scratch, with LittleOLinear residual and logarithmic width. | buildMemory_capacity_le + emitted encoding length + finite fresh-register interval -> compact complete capacity -> capstone | Delete counter/stack charge or substitute sibling allocation; pending. | None yet. | Open |
| `REQ-OPT-CONSUMER` | One inhabited capstone must connect actual compact emitted code, its exact execution/cost bound, same allocation, width/safety and complete space. Keep original public aliases and constants available; additive definitions allow all other workers to proceed on baseline. | Join | Inhabited CompactPackedQueryCapstone with checked independently pinned type consumers for every mandatory field and same objects/guards. | compactPackedQueryCapstone_holds -> exact field consumers; original public identities unchanged. | Field deletion, proposition weakening, object substitution; pending. | None yet. | Open |
| `CHK-OPT-CONTROLS` | Persist branch directions, nested sequencing, zero/one/repeated loops, early exits/halt, targets at code boundaries, fresh-counter collisions, invalid queries, full different-block paths and malformed metadata. Test compile correctness over semantic examples plus universal proofs; corrupt jumps/counters/budgets and ensure exact-type consumers or the production replay reject them. | Verification | Committed registry and runner execute each pinned case against independent expectations, including exact failure surfaces and restoration. | PackedOptimized validator imports Optimization capstone and actual emitter; production replay mutates exact predicates and consumers. | Required positive and negative controls listed in requirement, not yet run. | None yet. | Open |
| `REPLAY-EXACT-REGISTRY` | any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure. | Verification | Registry identity/count equality and expected/executed equality in full and focused mode. | Production optimized replay. | Delete one registered case; pending. | None yet. | Open |
| `REPLAY-SELECTOR-NONVACUITY` | omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing. | Verification | Omitted selects full suite; a valid selector selects exactly one; explicitly empty, whitespace, malformed or unknown selectors fail before semantic execution. | Actual script parameter boundary, not helper only. | Each selector class; pending. | None yet. | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed. | Verification | Owned process tree termination and restored exact hashes, preserving subprocess exit and stderr under bounded deadlines. | scripts/owned_process_tree.ps1 -> optimized replay. | Timeout descendant, nonzero exit, unavailable host branch; pending. | None yet. | Open |

## Phase ordering and scope

Verify baseline and freeze requirements; produce contract/feasibility evidence;
review evidence-dependent route choices; implement and verify; obtain an
independent exact-commit audit; repair and re-audit; coordinator accepts and
prepares integration/public wording. Mandatory contract audit precedes PRE
builder implementation. This lane owns no PRE builder. The explicit mandatory
contract/route review and resource waits may return an INCOMPLETE phase report.

Write scope is the assigned Optimization modules, PackedOptimized validator,
packed_optimized scripts, this folder, append-only OPT-1 entries in the two
decision ledgers/FAMILY_SUMMARY/DIGESTION_LOG, and one uniquely named validation
target in lakefile.toml. Shared Packed source, root aliases, gate, skills and
unrelated roadmap files are read-only. Local commits authorized; push, merge,
branch deletion and cleanup are excluded.

All assigned invariants below apply to the composed capstone. Pure cost helper
lemmas need no separate store representation, but do not discharge that
capstone's store or execution obligations by themselves.

## Verification coverage frozen before implementation

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `CHK-OPT-DEVELOPMENT` | build only the owned changed modules and direct typed consumers with bounded, one-job Lean/Lake execution; use narrow executable cases as new operations appear. | Development | Narrow module and direct consumer exit zero, logs/time/deadline/exact source hashes. | Changed Optimization files and actual validator. | No predecessor-only validation; pending. | None yet. | Open |
| `CHK-OPT-FINAL` | lake build; explicit build/import of every new capstone and typed consumer (default RMQ may not import new modules); new lane's full validation registry and relevant axiom inventory; trust hygiene; git diff --check; after committing, git diff --check 0e6a00f654abc64f8b68988fa9675b9a839dca2f..HEAD; scripts/design_decision_check.ps1 -Strict -Base 0e6a00f654abc64f8b68988fa9675b9a839dca2f. | Final | Frozen content and coordinator-scheduled host aggregate slot, all commands exit zero with durable exact evidence. | Full candidate and baseline compatibility; explicit new capstone imports required. | Partial timeout is not pass; pending. | None yet. | Open |
| `CHK-OPT-TRUST` | rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib" RMQ lakefile.toml; and rg -n "native_decide\|Lean\.ofReduceBool" RMQ for any new trust/validation surface. Explain actual matches and never hide them. | Final | Full scan with all matches explained, plus explicit #print axioms for exact new declarations. | Kernel trust of capstone and typed consumers. | No unexamined trust matches; pending. | None yet. | Open |
| `CHK-OPT-CONDITIONAL` | scripts/claim_drift_scan.ps1 -Strict if public prose changes (the narrow family/digestion entry qualifies); targeted existing compatibility checks if their imported executable behavior changes. Add explicit #print axioms for the new exact declarations. | Conditional | Strict prose scan and appropriate compatibility checks; declaration axiom inventory. | Additive public family/digestion entry and exact declarations. | New prose cannot promote a cost estimate to execution proof; pending. | None yet. | Open |
| `CHK-OPT-AUDIT` | Full aggregate certification belongs to the coordinator-scheduled final audit phase. Request it on frozen content and do not run several redundant full gates; candidate completion records this pending external acceptance stage accurately. PRE contract freeze additionally requires the plan's contract gate before its blind audit. | External phase | Independent exact-commit audit and scheduled certification evidence; PRE contract gate applies only before PRE builder implementation, which is outside this lane. | Coordinator acceptance follows worker proof evidence. | Worker self-acceptance prohibited. | None yet. | Open |

Final paper rewrite, publication-strategy update and combined campaign
integration are explicitly deferred to independent acceptance. No obligation
required to make an assigned theorem true is deferred. Phase reports record
exact unmet rows; a helper or passing build alone cannot complete OPT-1.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-INSTRUCTION-ATOMICITY` | each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-PROGRAM-ACCOUNTING` | input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-ORACLE-INDEPENDENCE` | executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-VALIDATION-REACH` | executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim; | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. Conjoining true theorems about different payloads or guarded and unguarded executions is not closure. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-CERTIFICATE-ANTI-BYPASS` | every mandatory field advertised by a public certificate is projected by a checked typed consumer at the exact proposition and object arguments required by the acceptance contract. Deleting or weakening a field, or replacing it with a sibling fact, must break that consumer rather than leave only constructor initializers and prose unchanged. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-MUTATION-REPRODUCIBILITY` | when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean. Report prose, copied terminal output, and dangling Git objects are not replayable evidence. A public theorem additionally has a checked exact-type consumer that fails when the advertised dependency is removed; `#print axioms` over the theorem's current type is not such a consumer. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | Composed capstone | Exact checked proposition preserving every clause at all xs and assigned endpoint guards. | Actual compact Program, Primitive.run, buildMemory, wordWidth and complete accounting in capstone; row-keyed evidence will expand producer chain. | Matching-predicate mutation or boundary witness, pending. | None yet. | Open |


## E1: checked generic producers; concrete/query composition pending

REQ-OPT-BUDGET has the checked producer
`compiled_run_bound_and_fuel_eq (memory) (block) (s) (hpc : s.pc=0) (a b)
(ha : branchBound block <= a) (hb : branchBound block <= b)` concluding
`(run memory (block.compileAt 0) a s).steps <= branchBound block` AND equality
of the two full runs at a and b. The producer uses an actual RunsTo witness
from `compile_realizes_branchBound`, whose type fixes HostedAt, the same
source evaluation, exact transition-filtered receipts, the structural bound
and running continuation PC `base+block.size`. No memory, success or valid
range premise is supplied. Exact checked types, source hashes, direct expected-
type consumers, branch/loop/early-stop controls, commands and axiom inventories
are quoted in bound-development/REPORT.md. The concrete query instantiation
in Capstone.lean remains unverified, so this row is not closed.

REQ-OPT-COMPILE and the inherited value/trace/frame/safety rows have a checked
independent source-relation leaf: with BlockRegistersBelow bound block and
same status/registers below bound, source_eval_congr gives same final status,
registers below bound and the exact ordered source receipt list. The frame
covers all r>=bound; source_safe_transport additionally requires global fit
of the alternate data. Exact types/controls are in relations-development/
REPORT.md. The independent contract audit's counterexamples require rebasing
new protected counter pairs and maintaining global machine fit separately;
these corrections are adopted without changing frozen rows.

All compact implementation evidence remains draft at this phase: actual
emitter, generic simulation/safety/static accounting, query objects/glue and
runtime controls require kernel/executable checks after the sole cold query
build releases its slot. No compact proof name, fixture draft, static count
or code-size proposition is entered as checked evidence. The capstone named
compactPackedQueryCapstone_holds has not yet been constructed. Same-store,
width, all-size, public-composition, exact-consumer and mutation rows all remain
open at the composed target.

The exact 35 frozen table rows were compared as strict UTF-8 bytes against
1f3a4199eaa95324cd1daaadbab89340ca8392c4; there are no missing, duplicate or
changed rows (frozen-row-check.json). This append is evidence only. The
checkpoint claim scan completed with 1573 review/allowed hits and zero strict
failures; full candidate certification and independent exact-commit audit
remain pending.

## E2: continuation checks the concrete original-query bridge

The resumed owned build returned its actual exit: all 250 prerequisites passed,
then the concrete bound module failed on recursion-depth/reflexivity obligations.
After only those repairs, a one-module check passed with exact source preserved
as query-development/BranchCapstoneChecked.lean and matching recorded SHA-256
in query-development/capstone-branch-pass.json. The actual
proposition is `forall memory n left right, (queryRun memory n left right).steps
<= 150739` on the original queryBudget. A second theorem equates the entire
`run memory queryProgram 150739 (initialState n left right)` with that original
queryRun. No memory validity, canonical-store, success or endpoint premise is
added. Canonical smaller-fuel halting/result and ordered receipt equality follow
on the same buildMemory. Exact expected-type consumers were in the checked
module. REQ-OPT-BUDGET now has its concrete execution bridge; final candidate
imports/axiom inventory and the compact target remain pending. Later capstone
composition edits require rechecking the current module and do not change what
this preserved source snapshot establishes. All frozen table rows are untouched.

## E3: checked compact construction and whole-query certificate

The checked generic compact producer now constructs actual RunsTo transitions
for every BlockRegistersBelow fresh block at a hosted compactAt program and
starting PC=base. Final status and all registers below the active fresh counter
agree with the source evaluation, and transition-filtered receipts equal the
source receipt list in order and multiplicity. Transition length is at most
compactBound block. The standalone adequate-fuel theorem reaches terminal fetch;
the appended-halt theorem has nonrunning final status. Nested loop counters are
rebased/protected rather than required to equal source scratch. Exact semantic
and safety types, controls, live guards and commands are in compact-proof-
development/REPORT.md. Global entry/final fit and every TraceSafe/prefix obligation
are separate premises/conclusions, not inferred from finite register agreement.

CompactStatic proves literal encoding recurrence and constructor-complete
encoded field fit with repeat-count/PC/register bounds. Its arbitrary-fuel
frame preserves every register outside the emitted bank. Query's kernel numeric
facts and independent literal measurements agree: code 212964, encoding 722339,
compact bound 151978, depth 1, count 33, bank 8273 and scratch 8276. This is actual
code strictly shorter than queryProgram 837572; the former213038 estimate is
not evidence. Exact propositions/consumers and measurement commands are in
compact-static-development/REPORT.md.

The current root composition files all passed on source hashes pinned by
composition-checked-manifest.json. `compactPackedQueryCapstone_holds` is an
inhabitant without a supplied correctness/safety premise. Its39 exact fields
are independently spelled out in certificate-replay/FIELDS.json v3 and all 78
generic/canonical consumers kernel-check. Every field fixes the same actual
compact program, run, buildMemory, initialState and wordWidth. In addition to
arbitrary-memory result/ordered-read equality, completedExecution forbids a
running final status and adequateFuel equates full Run objects at every larger
adequate fuel. Canonical result/nat/leftmost/invalid behavior, supplied-memory
agreement, physical positional backing and global transition/prefix safety
are consumed by that same inhabitant. The complete-space field counts literal
722339 encoded words and 8276 scratch words with the same allocation and the
same LittleOLinear residual. No input-dependent code constant is uncounted.

This supplies the theorem/object chain for REQ-OPT-COMPILE/RUN/SPACE/CONSUMER and
the 21 inherited invariants. Full semantic controls and public dependency
mutations are still required before those rows can support candidate completion.
The v3 campaign fixes 78 source-deletion/weakening rejects and two accept controls;
preparation-only restoration is explicitly NOT_RUN for kernel producer/consumer
results. It does not replace the separate 23-positive/four-negative actual runtime
registry. Startup C01 and known C05 pass, with unchanged source/artifact hashes;
the full registries are next on frozen content.

The full exact 93-root axiom union passed in 8.710s through the same builtin
collector with shared visited state, root-existence/visited guards and two
explicit standard public prints. Only propext, Classical.choice and Quot.sound
occur. The first 93-separate-print timeout remains incomplete in its receipt;
no per-root distributions are claimed by the union result. Independent
exact-commit audit, clean final restoration and scheduled aggregate certification
remain pending. These are evidence appends; all 35 frozen table rows are intact.

## E4: frozen-source semantic campaign and row-specific proof inventory

The complete runtime campaign at ac5af8e416f906391dc117f083a883acc053a268 passed
all 23 positive cases, four expected corruption rejections, 16 script boundary
checks and five direct Lean selector controls. It ended with exact source and
import-artifact SHA equality, no tracked mutations and wrapper exit zero. The
same/adjacent/interior route checks use independent logical geometry and the
malformed-metadata control changes the actual returned answer. Full receipts
are preserved in runtime-replay; startup alone is not the evidence for this run.

ROW_EVIDENCE.md expands all 35 IDs individually, including exact common object
arguments and each inherited invariant's producer/consumer chain. The original
frozen rows remain untouched. The independent certificate-checker boundary
review found an extra-diagnostic acceptance gap before the actual kernel field
campaign; its repair and production-verdict controls precede that campaign.
No preparation-only case is promoted to a producer/consumer result. Fresh
source review, complete field replay and scheduled final certification remain
separate evidence obligations.

## E5: complete field-dependency campaign at bbbe652

On clean bbbe652fa41fa40bf2530b5e2f09c4c225c0e896, the complete versioned
certificate campaign returned wrapper exit zero with executed=expected=80.
There were two successful accept controls and 78 intended rejections, one
deletion and one weakening for each of the 39 frozen fields. All 160 producer
compilations succeeded before the fixed consumer ran. Every rejection was at
the selected generic expected-type consumer; every stderr stream was empty.
All isolated sources were restored and all original/import/status/private
dependency snapshots matched. No source-setup failure counts as a rejection.

Root's independent certificate-independent-check.py/json reconstructs all
240 compilation stages in exact case order, checks commands and private
libraries, hashes all producer artifacts/restored sources and verifies actual
diagnostic paths, lines and field names. The complete raw stage/case records
are retained in the certificate-replay evidence. Focused unchanged/deleted/
weakened width-bound controls precede this full result; they are not its proxy.

This supplies the previously pending field-campaign evidence for
REQ-OPT-CONSUMER, REPLAY-EXACT-REGISTRY, INV-CERTIFICATE-ANTI-BYPASS and
INV-MUTATION-REPRODUCIBILITY, and the mandatory-field dependency part of every
same-object invariant. REQ-OPT-BUDGET/COMPILE/RUN/SPACE and the remaining
invariants retain the exact checked proposition/object chains in ROW_EVIDENCE.md
and the completed semantic registry at ac5af8e. REPLAY-SELECTOR-NONVACUITY and
REPLAY-SUBPROCESS-DEADLINE retain their actual boundary/owned-process evidence;
unavailable POSIX behavior remains uncovered rather than passed.

The ac5 source audit, bbbe checker-remediation review and completed-case receipt
review are separately scoped evidence, not coordinator acceptance. Final
report-sensitive checks and exact ranges are recorded in final-report receipts.
CHK-OPT-FINAL and CHK-OPT-AUDIT retain their explicitly coordinator-scheduled
aggregate/acceptance phase. SCHEDULED_FINAL_REQUEST.md is the durable request.
All 35 original frozen rows remain verbatim; no acceptance status is rewritten.

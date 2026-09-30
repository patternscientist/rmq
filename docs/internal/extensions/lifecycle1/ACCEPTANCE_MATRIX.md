# LIFE-1 frozen acceptance matrix

This is the initial contract baseline, not proof evidence or candidate completion.
All 43 full eight-column rows are immutable. Append dated evidence, exact theorem
propositions, P/Q comparisons, outcomes and current dispositions only below the
append-only marker. The frozen Open statuses describe the initial state; later
append-only evidence must state the current disposition without rewriting them.
No row closes by a theorem name, a build, a process receipt or this integrity check.

- Worker: LIFE-1.
- Worktree: C:/Users/poin/.codex/worktrees/8941/RMQ.
- Exact base: bf31f983205175481fcb659caa4dfb70ef43e361.
- Branch: codex/life-1-continuous-packed-lifecycle.
- Workflow governance: 7b227c49ef2ec044b702126cc41c9add847eed01.
- Template: docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md.
- Source prompt and exact byte hash: CONTRACT_REQUIREMENTS.json.
- Required target: RMQ.SuccinctFinal.PackedLifecycle.continuousConstructionQuery_holds.
- Required independent consumer: RMQ/Validation/LifecycleContract.lean.
- Required executable consumer: RMQ/Validation/PackedLifecycle.lean.
- Verification roles and boundaries: VERIFICATION_PLAN.md.
- Retained mathematical/executable model closure is local; native allocator
  ownership, production native adapter, publication synchronization, aggregate
  certification, fresh-blind audit and coordinator acceptance remain separate
  campaign phases. No assigned local proof/check is deferred by this statement.
- Numeric machine invariants use the explicit word model. Arbitrary-Int keys
  use their separately accounted comparison-oracle/resource model.
- The global physical-machine row uses the prompt's evolving-arena interpretation:
  actual stores/reservations/releases change backing; requests enter through the
  charged boundary, and the compact-query read/reply list is only the query suffix.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `L1-01` | Implement one conservative lifecycle machine extending the existing construction primitives with scalar release operations and an explicit charged external request-admission/control-entry boundary. Old instructions retain their exact semantics and ordered run simulation. Release of numeric memory revokes one tail cell and lowers extent by one; any comparison-key retirement changes at most one key cell or one key register per charged primitive. Boundary transitions perform only their declared scalar state changes, appear in the trace and per-query bound, and retain no unbounded future-request tape. State explicitly and check zero/invalid release behavior and separate cost categories. | Local machine | Conservative old-step embedding and ordered runs; each successful numeric/key retirement changes one cell or one register, with explicit zero/invalid outcomes; each boundary transition has declared scalar effects and a charged category. | Existing construction step -> lifecycle step -> whole run -> capstone and reusable-entry consumer. | Planned; not yet attempted: Compare old and embedded steps at every constructor; challenge zero release, failed release, multi-cell retirement, free admission and hidden future requests. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-02` | Produce fixed input-independent word-input and comparison-input programs, sharing the existing builder template and accepted compact query implementation through proved adapters. Runtime values, descriptors and endpoints must reside in accounted inputs/state or be computed by charged instructions. Do not specialize code to xs, its shape, n or a query. | Local programs | One closed word program and one closed comparison program independent of xs, n and endpoints; adapters identify the actual old builder/query instructions and accounted runtime data. | Fixed code -> builder adapter -> query adapter -> executed code used by capstone. | Planned; not yet attempted: Hold code constant across empty, tied and distinct inputs and different endpoints; inspect every data-dependent literal and dormant field. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-03` | Execute the existing builder BODY at its real nonzero program offset and continue running into finalization. Derive actual entry and exit PCs, relocation, code-field fit, complete intermediate-state identity and ordered trace concatenation; do not resume a halted standalone builder by a meta-level reset. | Local builder embedding | Relocated BODY starts at its actual nonzero entry, follows old semantics on the complete state, exits into finalization without halt/reset, and concatenates ordered receipts with exact PCs. | Builder BODY -> relocated lifecycle prefix -> produced finalizer entry -> continuous run. | Planned; not yet attempted: Mutate entry/branch relocation or substitute a merely equal memory state with unequal registers, PC, status or key banks. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-04` | Transfer output base B by a charged instruction from the builder-produced output register with positional provenance to its reservation, then load n and M from the actual produced metadata at B and B+7. Derive the output extent/length and address facts, rather than assuming a stored B field that canonical metadata does not contain. Read or transfer the represented request through charged instructions before its cells can be overwritten or released. Prove dependence of the relevant register/value/route on its actual producing transition; an unrelated source cell with the same value must not satisfy output provenance. | Local producing provenance | The output-register transfer occurrence follows the producing reservation; metadata reads at actual B and B+7 derive n/M/extent; the charged request transfer precedes overwrite/release and determines the advertised projection. | Reservation/output occurrence -> transfer/load occurrences -> finalizer registers and route -> capstone. | Planned; not yet attempted: Use a wrong source containing the same value, absent metadata, or overwritten request; compare exact producing pre-state, instruction and position. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-05` | Execute scalar forward overlapping copy from the actual produced [B,B+M) into [0,M), then exactly B single-cell numeric releases. Prove the resulting whole memory function equals canonical buildMemory lookup, extent equals M, and every address at or above M is absent. Preserve ordered producing load/store/release occurrences, values and multiplicity on the actual whole run. | Local scalar compaction | From the actual produced allocation, forward scalar copy then exactly B releases yields memory = canonical buildMemory lookup, extent = M, and absent tail, retaining ordered load/store/release occurrences and multiplicities. | Produced [B,B+M) -> actual copy/release run -> READY store -> query backing/space consumer. | Planned; not yet attempted: Challenge backward overlap, absent source, skipped store, omitted release and stale suffix on matching produced objects. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-06` | Operationally retire all retained construction input and temporary resources before the succinct READY boundary. In the word-input route the input words lie in the same owned numeric arena; in the arbitrary-Int comparison route account for separate input-key cells and key registers and retire them by charged scalar execution. READY requires zero owned extents for these key banks, reflected by empty executable containers; pointwise zero/none lookups alone do not establish retirement. The production retained owner has no hidden input, old arena suffix or observation history. Native backing capacity and external aliases remain separately assigned native obligations, not conclusions of extensional Lean equality. | Local ownership retirement | The operational word/comparison routes retire numeric input/scratch and separately counted key cells/registers; READY has zero key extents and empty containers and its owner contains no inputs, suffix or observations. | Input owner -> charged retirement execution -> abstract READY -> executable retained-owner projection. | Planned; not yet attempted: Distinguish empty banks from zero-valued retained banks; retain one key, old suffix, input alias field or history in the production owner. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-07` | Derive charged query initialization and the actual jump to the compact query prefix from the produced finalizer state. Establish the exact query ABI and finite register support, with n derived from the produced metadata. A 400-register initial clearing profile may be used only after proving its incoming frame through every handoff; no admitted finalizer/query state or answer premise may remain in the completed public theorem. | Local first entry | From the derived finalizer exit, charged clearing/initialization and jump establish exact compact ABI, produced n, and zero numeric tail outside a finite bank; no finalizer/answer premise survives capstone construction. | Finalizer exit -> proven incoming support -> scalar initialization -> actual query-prefix entry. | Planned; not yet attempted: Skip one dirty register or n load, jump to a wrong PC, or rely on infinitely many unexecuted clears. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-08` | Prove one continuous construction-finalization-first-query execution whose query suffix uses exactly the resulting counted canonical memory. Preserve the complete accepted compact-query transition simulation, ordered attempted read/reply list including failures and repetitions, positional producing states and instruction identity, and the exact half-open leftmost answer or represented-invalid rejection packet. | Local continuous execution | Construction, finalization and first query form one completed run; its query suffix on the counted canonical store preserves every compact transition and ordered attempted read/reply, including failures/repeats, and returns the exact valid/invalid packet. | Initial state -> builder -> finalizer -> query simulation -> same-store capstone result/receipt. | Planned; not yet attempted: Reorder repeated reads, omit failed reads, manufacture a replay, substitute sibling store or mismatch invalid guards. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-09` | Provide a reusable query-entry protocol on the same READY allocation, including after a previous query has dirtied the query register bank. Model the external request boundary explicitly and charge its machine-state changes, finite-bank clearing and control entry. Prove the result, unchanged retained allocation, restored reusable interface and a uniform per-query bound. Do not infer repeated-query readiness from the builder-only 400-register frame or silently reset a halted state for free. | Local reusable entry | For every reachable READY/query-exit interface and represented request, charged boundary/clearing/control entry returns the exact packet, preserves allocation, restores reusable interface and has one uniform constant query cost. | Prior query exit -> named external entry transitions -> next compact suffix -> reusable READY on same allocation. | Planned; not yet attempted: Run a second query with a dirty full query bank; reject a free halted-state PC/status reset or allocation replacement. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-10` | Prove all-size word-input lifecycle correctness under the existing InputFits predicate at one query-independent width, and a separately labeled all-List-Int comparison-input lifecycle theorem. Representable valid, empty, reversed and out-of-range endpoint pairs share a coherent domain. Keep out-of-word Nat admission and pre-supplied input materialization boundaries explicit; do not claim bounded arbitrary-Int input bits. | Local all-size domains | For every List Int word input satisfying existing InputFits at the declared query-independent width, and separately every comparison input, derive all lifecycle facts for representable valid/empty/reversed/out-of-range pairs. | InputFits or explicit comparison resources -> initial materialized state -> all-size lifecycle capstone. | Planned; not yet attempted: Check n = 0/1/2 and thresholds; invalid represented pairs share the same guards; out-of-word Nat admission and arbitrary-Int bits remain explicit boundaries. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-11` | Prove a uniform logarithmic word profile bounding all numeric input words, intermediate words, returned words, actual/dead/sentinel addresses, PCs and dormant encoded operands throughout the same lifecycle. Discharge bounds for the actual programs and consumers; the experiment W=32+K satisfiability witness cannot substitute for width scaling. | Local width profile | One logarithmic query-independent width bounds numeric inputs, every intermediate/returned word, executed/dead/sentinel addresses, PCs and every dormant constructor operand of the actual fixed programs. | wordWidth n -> constructor-exhaustive code fit and transition preservation -> every segment of same run. | Planned; not yet attempted: Overflow a dormant register/target/immediate, dead address or intermediate result; reject a per-instance W=32+K substitute. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-12` | Derive linear construction-plus-finalization work and a uniform constant query budget from actual transitions and successful completion. Fix constants and cost functions outside per-instance certificates, count setup/branches/copy/releases/retirement/entry and separate comparison-oracle costs. Merely bounding steps by an arbitrary fuel parameter is insufficient without a proved completed run within it. | Local work bounds | Fixed constants outside certificates bound a successfully completed construction/finalization by a linear n function and each reusable query by one constant, including setup, branches, copy, releases, retirement and entry; oracle categories stay separate. | Actual transition-category receipts -> proved completion budgets -> public uniform work bounds. | Planned; not yet attempted: Choose insufficient fuel, omit an entry/release category or hide oracle work; compare completed traces, not arbitrary supplied fuel. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-13` | Prove peak owned numeric allocation is O(n) words from the actual run, including supplied input, request cells and overlap; give a separate explicit bound for comparison-key input resources. Prove complete retained READY data/code/register/control/descriptor capacity is at most 2*n+rho(n) for one fixed checked LittleOLinear rho. All components must be the ones used by the lifecycle and reusable queries; temporary and retained bounds must not be conflated. | Local resource bounds | Every state on the actual run has linear peak numeric allocation including input/request/overlap and explicit key bounds; complete retained READY capacity for the executed store, code, registers, control and descriptors is <= 2*n+rho(n) for one checked LittleOLinear rho. | Whole-run extents -> peak bounds; produced READY owner + fixed code/state -> same-store retained bound -> capstone. | Planned; not yet attempted: Count only final payload, omit code/request/register/key resources, conflate peak with retained, or count a sibling allocation. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-14` | Preserve supplied-store determinism and value dependency through the combined interpreter. State the read/transition agreement relation with complete guards and quantifiers. Derive reads from execution, not a second replay; constrain answer or route projections where claimed rather than only inequality of an enclosing logged record. | Local supplied-store semantics | Under the fully quantified execution-derived read/transition agreement relation, same inputs/code determine result, categories and ordered observations; the claimed answer/route dependency constrains its actual projection. | Supplied store -> combined interpreter execution -> actual attempted reads -> projection-specific agreement/dependency consumer. | Planned; not yet attempted: Change an unread/read source under exact guards; a difference only in logged metadata cannot witness answer/route dependence. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-15` | Connect a finite-container executable lifecycle runner to the abstract execution, including stores, reservations, scalar releases, key-bank extents and charged request entry; prove final values, actual ordered observations and cost-category refinement. Separate the production retained owner from optional validation observations and prove its executable projection excludes histories and retired logical resources. Validation must execute this new layer on representative input/query shapes, not call a predecessor validator or rebuild canonical output as its implementation. Logical container size is not a native backing-capacity bound. | Local executable refinement | Finite-container execution simulates every abstract store/reserve/release/key/boundary primitive and full runs, preserving values, ordered observations and cost categories; retained owner projects away histories and retired resources. | Finite input owner -> new executable lifecycle evaluator -> abstract run -> executable READY/query owner -> new validator. | Planned; not yet attempted: Mutate the new evaluator, preserve a key extent/history, or rebuild canonical output; independent expectations must detect each relevant fault. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-16` | Expose a small coherent theorem interface at RMQ.Core.WordRAM.Lifecycle.Capstone with continuousConstructionQuery_holds and a separately checked exact-type consumer. The final theorem derives every advertised execution, correctness, resource and cost fact; no structure field accepts the final advertised answer/equality as a premise. Signature choices and uniform family constants are reviewed early but remain implementation obligations, not a weaker alternate endpoint. | Local public interface | RMQ.SuccinctFinal.PackedLifecycle.continuousConstructionQuery_holds derives all advertised facts from initial-domain assumptions and fixed family constants; an independent exact-type consumer projects the same objects without final-result premise fields. | Lifecycle construction proofs -> Capstone theorem -> RMQ.Validation.LifecycleContract exact expected type -> additive headline. | Planned; not yet attempted: Delete/weaken a mandatory field, substitute sibling facts or accept the answer as an input; the independent consumer must fail. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-17` | Commit replayable projection-specific negative controls covering wrong output source, skipped initialization, stale retained tail, absent source word, omitted release, backward overlapping copy, key retention, wrong program entry, field overflow, and a second-query dirty-bank failure. For controls inherited from experiments, use the same positive relation or a proved bridge. New proposed controls are evidence-producing tests, not pre-certified failures; do not require an unreal counterexample to pass a gate. | Local operational controls | Replay the ten named controls with exact challenged projection, P/Q guards, objects and quantifiers; use identical positive relations or checked bridges and record actual expected verdicts. | Production operational predicate -> negative fixture (or checked bridge) -> committed dedicated checker -> evidence rows. | Planned; not yet attempted: Wrong output source; skipped initialization; stale tail; absent source; omitted release; backward copy; key retention; wrong entry; field overflow; second-query dirty bank. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-18` | Pin the public contract with an independent expected-type consumer and a meaningful dependency-mutation suite that rejects weakened or bypassed load-bearing conclusions. Any runner must have a frozen exact case registry, focused selector boundaries, exact failure classification, positive controls, owned subprocess deadlines/cleanup and restoration checks; mixed expected and unrelated diagnostics must reject. | Local dependency controls | Independent expected-type consumer rejects load-bearing weakening/bypass through a versioned exact-case runner with selector-boundary, expected-accept, exact diagnostic, deadline/cleanup and restoration controls. | Public proposition -> independent expected type -> dependency mutations -> exact failing surface -> restored final source. | Planned; not yet attempted: Mutate conclusion/field/type; reject missing/duplicate/unknown/explicit-empty selection, mixed diagnostics, timeout, leaked descendant or unrestored source. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-19` | Keep the implementation maintainable: reuse existing builder/layout/query and generic execution lemmas, give one owner to machine/READY interfaces, separate reusable scalar lemmas from RMQ specialization, and document a short worked lifecycle and proof-dependency route. Avoid broad machine unification, cloned successor APIs, giant closed-program reductions and a certificate enlarged solely to mirror this checklist. | Local architecture | Reviewed modules reuse existing builder/layout/query and execution facts, have one machine/READY owner, separate generic scalar lemmas, and document a worked example with dependency route. | Existing source spine -> owned scalar facts -> RMQ-specialized lifecycle -> public capstone and proof guide. | Planned; not yet attempted: Inspect cloned APIs, hidden code duplication, giant closed witness reduction and fields that exist solely to restate checklist obligations. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `L1-20` | Produce a clean committed candidate with complete frozen requirement evidence, exact type/axiom inventories, targeted executable/negative checks, default build, per-commit and range design certification, and accurate candidate documentation. This closes the mathematical/executable model implementation rung only; native allocator ownership, publication-wide synchronization, complete aggregate certification and fresh-blind acceptance remain separate mandatory campaign phases. | Local candidate certification | Clean exact-base candidate carries every frozen row disposition, exact types/axioms, required successful checks on final content, per-commit/range design evidence and precise candidate/campaign limits. | Final source + consumers + checks -> append-only evidence and complete REPORT -> coordinator review, not self-acceptance. | Planned; not yet attempted: Challenge stale receipts, post-check edits, missing required check, uncommitted source, or native/publication/aggregate/audit closure inferred from this local report. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient; | Inherited invariant | Equality/refinement identifies the store supplied to actual lifecycle/query runs with the exact payload and retained owner whose capacity is counted. | Builder output -> compacted READY store -> executable/query store -> public space object. | Planned; not yet attempted: Substitute same-sized or semantically equivalent sibling payload without a proved identity at the consumer. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient; | Inherited invariant | Actual charged read values determine the returned answer or decisive route through the evaluator and refinements under the full public domain. | Producing load -> state/register/route -> returned packet -> public exactness. | Planned; not yet attempted: Change only a logged record while preserving answer/route; such inequality cannot close this row. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself; | Inherited invariant | Coverage, liveness, ownership and refinement follow reachable transitions and concrete evaluator behavior, with definitions expanded and exact guards. | Operational construction -> semantic predicates -> exact public projections. | Planned; not yet attempted: Replace predicates by True, enumeration membership or hand-written labels; named operational witnesses must fail. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe; | Inherited invariant | Ordered traces/footprints are projections of the same folded machine execution, retaining required positions and multiplicities. | Transition observations -> ordered run receipt -> public trace. | Planned; not yet attempted: Manufacture a second replay or drop/reorder repeated occurrences. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace; | Inherited invariant | The complete supplied-store agreement hypothesis entails equal result, charged categories and relevant trace for the same initial interface/program. | Execution-derived attempted reads/guards -> agreement induction -> result/cost/trace projections. | Planned; not yet attempted: Weaken a failed-read guard or compare only successful stores while changing a relevant reply. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store; | Inherited invariant | Every successful read occurrence identifies its producing pre-state, instruction/address and word in the counted store as it evolves. | Evolving initial arena -> stores/reservations/releases -> producing state -> read occurrence -> counted backing. | Planned; not yet attempted: Use immutable initial contents after a store or justify repeated equal reads only by List.Mem. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word; | Inherited numeric invariant | All stored/intermediate/returned numeric words in the same lifecycle fit its one declared modeled width; arbitrary-Int keys use the separate oracle model. | Initial InputFits -> transition preservation -> numeric final/query values. | Planned; not yet attempted: Introduce an oversized primitive result or treat arbitrary-Int comparison keys as finite-word input bits. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | Inherited numeric invariant | Constructor-exhaustive operand bounds plus run preservation cover every numeric address, register identifier, PC/target, immediate and dead/sentinel access at the same width. | Actual fixed programs + evolving states -> full machine address/operand capacity. | Planned; not yet attempted: Mutate a dormant opcode field or failed/dead address while keeping host array access bounded. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-INSTRUCTION-ATOMICITY` | each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive; | Inherited machine invariant | Each evaluator branch performs the advertised scalar primitive, or work is expanded into charged transitions/accepted bounded primitives. | Constructor evaluator bodies -> primitive category receipts -> lifecycle work theorem. | Planned; not yet attempted: Hide recursive copy/release, a variable scan or multiple arithmetic categories inside one charged constructor. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-PROGRAM-ACCOUNTING` | input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation; | Inherited machine invariant | Fixed program independence and accounted state/inputs cover every input-dependent runtime value and descriptor; charged instructions derive any computed constant. | Fixed code -> accounted runtime inputs/state -> retained data/code/state capacity. | Planned; not yet attempted: Specialize code by xs, n, shape or endpoints and remove those literals from the bit count. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-ORACLE-INDEPENDENCE` | executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested; | Inherited validation invariant | Expected executable packets are derived independently from List Int half-open leftmost reference semantics or an already connected theorem. | Independent spec/fixtures -> expected packets -> new evaluator comparisons. | Planned; not yet attempted: Set expected answers to the implementation result or use an unconnected predecessor as oracle. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-VALIDATION-REACH` | executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine; | Inherited validation invariant | The validator imports and executes the new finite-container lifecycle evaluator and production mutations alter the checked result. | RMQ.Validation.PackedLifecycle -> new executable lifecycle -> abstract refinement/capstone. | Planned; not yet attempted: Run only a predecessor validator or canonical buildMemory implementation and show the reach check rejects it. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Inherited semantic invariant | The exact public domain covers all assigned input sizes and represented endpoint cases without readiness or compatibility escape routes. | All-size builder/finalizer/query proofs -> one coherent valid/invalid public capstone. | Planned; not yet attempted: Inspect empty/tiny/threshold inputs and represented invalid requests for hidden unproved dispatch. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information; | Inherited model invariant | Proof-erased invariants establish operational facts but no executable answer, route or uncharged metadata is obtained from proof-only fields. | Counted initial data -> charged evaluator -> answer/route; proof witnesses certify this chain only. | Planned; not yet attempted: Place a semantic answer or uncharged routing choice in a certificate field consumed by execution. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim; | Inherited trace invariant | Every claimed occurrence comes from actual execution and contributes according to the declared interpreter categories. | Real instruction occurrence -> observation/category -> concatenated lifecycle receipt. | Planned; not yet attempted: Add decorative rereads or a post-hoc generated log to support a dependency claim. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct. | Inherited reporting invariant | Theorems and reports distinguish retained bits, proof witnesses, charged ticks, numeric/key state, executable containers and native measurements. | Formal cost/space statements -> executable refinement -> accurately scoped report. | Planned; not yet attempted: Infer native heap capacity or elapsed performance from extensional memory/container size. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. Conjoining true theorems about different payloads or guarded and unguarded executions is not closure. | Inherited public invariant | Every advertised conjunct uses identical construction/run/store/width/request objects and coherent validity guards, with explicit equalities/refinements for adapter changes. | One initial allocation -> one continuous run -> same READY reused -> capstone projections. | Planned; not yet attempted: Conjoin guarded exactness with unguarded execution, or space for a sibling store. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-CERTIFICATE-ANTI-BYPASS` | every mandatory field advertised by a public certificate is projected by a checked typed consumer at the exact proposition and object arguments required by the acceptance contract. Deleting or weakening a field, or replacing it with a sibling fact, must break that consumer rather than leave only constructor initializers and prose unchanged. | Inherited public invariant | Independent exact expected-type consumer projects every mandatory proposition at the required object arguments and fails after deletion/weakening/sibling replacement. | Public capstone fields -> typed consumer projections -> replayed dependency controls. | Planned; not yet attempted: Adjust constructor initializers after weakening and show no unchanged consumer can silently accept. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-MUTATION-REPRODUCIBILITY` | when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean. Report prose, copied terminal output, and dangling Git objects are not replayable evidence. A public theorem additionally has a checked exact-type consumer that fails when the advertised dependency is removed; `#print axioms` over the theorem's current type is not such a consumer. | Inherited evidence invariant | Committed fixtures/runner encode each claimed mutation, exact expected failure surface, positive controls and restoration/clean-tree evidence; public dependency types are independently pinned. | Versioned mutation source -> production consumer/check -> exact verdict -> restored source identity. | Planned; not yet attempted: Omit a claimed case, mix expected and unrelated errors, adapt the consumer to weakened type, or retain only report transcripts. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding. | Inherited evolving-arena invariant | One initial owned numeric arena and checked region/address scheme evolve through actual reserve/store/release transitions; every segment includes code, numeric registers/control/request/memory and positional backing; comparison banks stay separate. | Initial whole-machine embedding -> construction -> handoff/finalizer -> reusable query boundaries and suffixes. | Planned; not yet attempted: Embed only query suffix, treat initial contents as immutable after writes, omit failed addresses or store all future requests. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | Inherited whole-machine invariant | One query-independent width with logarithmic relation to n bounds all actual code/state/store/intermediate fields throughout the same global evolving machine. | Declared width family -> actual code fit + run invariant -> public capacity/width claim. | Planned; not yet attempted: Prove an unrelated asymptotic width fact or use a per-instance oversized satisfiability witness. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `CHK-FINAL` | Run the final-required checks on the final submitted content, with exact identities, complete outcomes and declared platform limits. | Local final verification | All final-required checks in VERIFICATION_PLAN.md finish on source/consumer/report identities submitted; outcomes include durations, exits, deadlines and declared platform limits. | Final source -> targeted controls/build/axioms -> report/claim/design checks -> exact final receipts. | Planned; not yet attempted: Treat a missing/timed-out check as pass or reuse a pre-edit receipt for changed consumed content. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |
| `CHK-SCOPE` | Keep the assigned write scope, clean committed tree, exact base, full frozen row integrity and truthful local-versus-campaign status. | Local identity/scope | Exact base/branch/worktree and allowed changed paths; immutable strict UTF-8 complete frozen rows; clean committed tree and truthful local/campaign disposition. | START identity -> frozen contract -> scoped Git diff -> commit/range checks -> final report. | Planned; not yet attempted: Change a late requirement clause, duplicate/miss ID, edit another worktree, stage unrelated output or claim coordinator acceptance. | None at contract freeze. Append exact checked propositions and result receipts below. | Open; complete local requirement remains to be established. |

<!-- APPEND-ONLY-EVIDENCE -->


## Final candidate-local reconciliation

The following 43 dispositions append evidence only. The complete inherited
43-row/eight-column prefix remains byte-for-byte unchanged, including its
historical Open statuses. These are worker candidate-local closure dispositions,
not coordinator ACCEPTED status. [ACCEPTANCE_EVIDENCE.md](ACCEPTANCE_EVIDENCE.md)
quotes the same formal object chains and preserves development receipts as history.

Final evidence families are B (default5.732s and named57.584s builds), T (exact
inventory135.302s, standard axioms only, both hygiene scans zero), N (corrected
16-case native replay81.505s with9 clean owned receipts), and D (actual
26-case dependency summary passed=true,23 rejects/3 accepts, original/private
restoration and shadow removal true). N and D are fully recorded in
[NATIVE_VERIFICATION.md](NATIVE_VERIFICATION.md) and
[DEPENDENCY_VERIFICATION.md](DEPENDENCY_VERIFICATION.md). D is
.lake/lifecycle-dependency/20260921T021035666-83fc2827/summary.json,
SHA-25617d5798eb4a91699c2b938fa9f82e393652c43de9a28654976649c8c5ae29ed7.

S is the mandatory static/source/delivery gate in
[SOURCE_MANIFEST.json](SOURCE_MANIFEST.json), [FINAL_RECEIPTS.json](FINAL_RECEIPTS.json)
and [REPORT.md](REPORT.md). Root owns final claim/design/commit/path/clean-tree
checks. Their actual postcommit outcomes belong to external
.lake/lifecycle-final/delivery.json and the submission message, avoiding a
self-hash claim. No unperformed closing-commit or postcommit check is asserted
by this appendix. Submission is gated on S for every disposition, including
L1-20, CHK-FINAL and CHK-SCOPE. Implementation source identity is
299ec6527ca2fbcf73cfc34e9de75f4a1f34140c; the evidence-only closing identity
is supplied separately through the external delivery receipt and submission message.

### L1-01 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E01: old execution is lifted with complete state/ordered trace. `requestProtocol.steps = 4` and its categories are exactly two admissions followed by two control entries. Successful release changes one tail cell/register and lowers one extent; zero extent faults. These operations are the constructors used by `actual` and `queryRun`.

Final observed evidence and challenge: B/T recheck the scalar constructors and exact boundary trace; N checks reserve/release size changes and two admission/two control-entry categories. D03_SAFETY, D05_EXECUTABLE and D06_REUSABLE reject weakened consumers; zero-release and halted-entry guards remain explicit.

### L1-02 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E02: `Layout.program : InputModel -> List Instruction`, with no input/shape/size/request argument; hosts identify builder/descriptor/finalizer/retirement/service in that same list. `program.length = jumpBase model+1`; `encodedProgram.length <= 1116895`.

Final observed evidence and challenge: B/T check the same fixed Layout.program and encoded fields. D01_CONSTRUCTION, D07_UNIFORM and D15_CODE_FETCH_DROP reject lost program/width/fetch conclusions; C10 pins code and bank constants. N runs both model programs unchanged across all 16 cases.

### L1-03 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E03/E06/E07: `producer = {abstract with pc := base+source.size}` and live `RunsTo p initial producedState producedTrace`; `Continuous.exact_run` appends the actual finalization/service traces without a reset. Entry is 221239; BODY exit is 223345.

Final observed evidence and challenge: B/T pin the nonzero BODY entry and exact continuous trace. D01_CONSTRUCTION and P01_OUTPUT reject missing construction/producer receipts; N starts initialOwner at the builder entry and reaches finalization without a reset.

### L1-04 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E03/E04/E14: actual `reserve 3` pre-extent equals `B`, register 3 is framed through the exit, and `move 0 3` returns that extent. Actual descriptor reads load `n`, `M`, left and right at local 1/4/8/10; E14 pins global indices `body.length+{1,4,8,10}` and actual prefix states.

Final observed evidence and challenge: P01_OUTPUT, P02_METADATA and P05_PUBLIC_TRUE reject loss of the actual reservation/descriptor chain. OUTPUT-SOURCE accepts OutputReceipt for move 0 3, rejects move 0 4, and checks differing loaded destination values; B/T bind the global occurrence client.

### L1-05 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E05/E06: `final.memory = fun a => cells[a]?`, `final.extent=M`, running exit at base+14; exact work `7*M+4*B+5`. Copy load/store indices are 4+7*i/5+7*i and releases 5+7*M+4*k, with actual producing state and value chain. E14 lifts them after builder+descriptor.

Final observed evidence and challenge: P03_COPY, P04_RELEASES and P05_PUBLIC_TRUE reject missing indexed copy/release conclusions. Same-predicate ABSENT-SOURCE, STALE-TAIL, OMITTED-RELEASE and BACKWARD-COPY controls pass. N checks actual finalizer base/length, allocation balance and exact release count.

### L1-06 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E06/E12: comparison retirement gives `keyExtent=0` and `keyRegExtent=0` after `4*n+5` actual steps; word retirement is zero steps on empty banks. `Ownership.Ready.empty_keys` concludes actual `keys=#[]` and `keyRegs=#[]`. `Owner` contains only arrays/control.

Final observed evidence and challenge: D02_RETAINED, D05_EXECUTABLE and D17_READY_BANK reject lost canonical/finite-bank facts. KEY-RETENTION rejects default-valued but owned banks; N requires literal empty arrays and exactly n key-cell/two key-register releases in comparison mode.

### L1-07 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E04/E06/E07: produced metadata gives register 302=n and charged request loads give 300/301. The real jump reaches service entry; four preparation instructions and 8270 clears plus jump establish exact compact initial registers/PC, with incoming tail already proved.

Final observed evidence and challenge: D01_CONSTRUCTION and D06_REUSABLE preserve the consumed setup chain. N:L11-W-DIRTY/L12-C-DIRTY execute the actual second setup: positive complete bank accepts, the single skipped register-400 clear rejects through query_entry_implies_clean.

### L1-08 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E07/E10/E13: `actual = <service.final, fullTrace ++ service.transitions>` and actual transitions factor into that same construction, actual setup, then complete lifted `compactQueryRun cells n left right` transitions. Public valid/invalid projections give the half-open leftmost packet/zero.

Final observed evidence and challenge: D01_CONSTRUCTION, D02_RETAINED, D10_PUBLIC_TRUE, D11_WORD_TRUE and D12_COMPARISON_TRUE reject bypasses of the same actual run and packet. N independently checks all valid/invalid/tie results; B/T bind the full lifted query suffix.

### L1-09 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E08/E12/E13: for any Ready halted owner and represented next request, `queryOwner.memory = es.memory`, Ready is restored, packet is exact, and `queryRun.steps <= 160257`. The actual query trace includes four boundary events and the full clear even with a dirty bank below 8273.

Final observed evidence and challenge: D06_REUSABLE and D17_READY_BANK reject lost repeated-query/owner obligations. N checks actual queryOwner, the four boundary events, unchanged exact memory, restored empty key banks and query budget; both real dirty-entry controls pass.

### L1-10 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E03/E13: `wordInputContinuousConstructionQuery` assumes only existing InputFits plus represented endpoints; `comparisonInputContinuousConstructionQuery` quantifies all `List Int` with no magnitude guard. ValidRange selects semantic answer versus rejection, not a separate execution domain.

Final observed evidence and challenge: D11_WORD_TRUE and D12_COMPARISON_TRUE reject weakened model-specific public claims. N covers empty/singleton/repeated/tied/invalid and n=24/83 shapes; L14/L16 explicitly witness comparison keys outside the signed word-input domain.

### L1-11 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E02/E09/E10/E13: every actual prefix Fits W, physical extent/addresses/replies fit 2^W, every encoded field is below 2^W, and `log2(n+2)+1 <= W <= 192*(log2(n+2)+1)`. All are on the actual fixed program and same run.

Final observed evidence and challenge: D03_SAFETY, D04_PHYSICAL, D07_UNIFORM, D15_CODE_FETCH_DROP and D16_PREFIX_RESOURCES reject lost bounds/fetch/prefix facts. FIELD-OVERFLOW rejects dormant immediate/register/target 256 at width8. B/T check the canonical same-W declarations.

### L1-12 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E06/E07/E08: completed `fullTrace.length <= 1100000000*(n+1)` and actual total steps <= that bound+160253; repeated query <=160257. Exact equations count descriptor, copy, releases, key retirement, setup, jump and boundary events before stopped-fuel extension.

Final observed evidence and challenge: D01_CONSTRUCTION and D06_REUSABLE reject weakened completed-run budgets; C10 fixes construction/setup/query constants. N checks actual category totals, one halt, reserve/release balance and each subsequent query's 160257 bound.

### L1-13 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E09/E10/E12/E13: each actual prefix has arena extent <=5000000*(n+1), comparison keyExtent <=n and keyRegExtent <=2, while word extents are both zero. Executed owner capacity times W <=`2*n+retainedRho n`; `LittleOLinear retainedRho` uses the same code/register/control constants.

Final observed evidence and challenge: D02_RETAINED, D05_EXECUTABLE, D14_RETAINED_COST, D16_PREFIX_RESOURCES and D17_READY_BANK reject omitted storage/resource conclusions. N records physical array lengths and peak arena sizes. Numeric retained capacity remains separate from comparison resources and native allocation.

### L1-14 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E11/E13: initial `State.Agree` plus `DynamicReadsAgree p fuel s t` at paired actual producing steps derives `Run.Agree`, equal result/register/status, steps, categories and ordered numeric/key reads/writes. Distinct successful replies at matched load occurrences force distinct destination registers.

Final observed evidence and challenge: D18_STORE_TRUE rejects replacing public determinism by True; C13/C14 independently pin the conclusion and numeric read guard. B/T check paired actual-prefix ReadAgree and loaded-register sensitivity; ABSENT-SOURCE exercises missing initialization rather than assuming a successful read.

### L1-15 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E12/E13: for every fuel, actual finite `runOwner.toState`/`runArray.toRun` equals the defined abstract run, with all destinations derived from input guards. The retained owner has empty key arrays; `queryArray` preserves actual boundary/service observations and categories.

Final observed evidence and challenge: D05_EXECUTABLE and D17_READY_BANK reject loss of finite-owner refinement/bank facts. N executes initialOwner/runOwner/queryOwner, checks counted_owner's complete result and actual categories, and detects a real program-clear mutation; no predecessor validator or buildMemory implementation is used.

### L1-16 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E13: `continuousConstructionQuery_holds model xs left right domain hl hr : ContinuousConstructionQuery model xs left right`, with seven same-object fields and no expected answer/equality premise. Independent C01-C07 clients spell out canonical/ready/profile and field propositions.

Final observed evidence and challenge: D01_CONSTRUCTION through D07_UNIFORM, D10_PUBLIC_TRUE and P05_PUBLIC_TRUE reject weakened public groups/theorems; D19_ACCEPT_COMMENT, D20_ACCEPT_IDENTITY and P06_ACCEPT_IDENTITY accept unchanged propositions. B/T check independent clients against the same public objects.

### L1-17 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: P/Q use the same production predicates: OutputReceipt, Initialized, Entry/FinalOutput, positional CopyReceipt, key extents and universal field Fits. Dirty-control source compares the actual second service's exact compact ABI after replacing one witnessed dirty register's clear.

Final observed evidence and challenge: B compiles all nine scalar P/Q controls and their checked bridges. N observes both actual dirty second-query cases with register400. CONTROL_PREDICATES.md identifies every accepted/challenged object and guard; no control is credited to an arbitrary compiler/runtime failure.

### L1-18 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Independent clients project every public field at expanded expected propositions; the direct provenance client expands Occurrence and receipt predicates. Required weakening/bypass mutations must fail these fixed clients, with positive controls and exact diagnostic/selector/restoration/cleanup checks.

Final observed evidence and challenge: D completed all 26 exact cases:23 expected rejections and3 expected accepts. Final self-test, focused selection, exact JSON diagnostic rejection, owned timeout/descendant cleanup and original/private restoration all passed; N's five selector negatives and nine owned process receipts also passed.

### L1-19 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E01-E14 and the worked guide give one state/owner interface and the explicit `input -> BuildStage -> fullTrace -> actual -> owner -> next query` dependency chain. Scalar generic lemmas are reused; original builder and compact query remain the executable sources.

Final observed evidence and challenge: B/T and E01-E14 bind the reused scalar/old-builder/query chain; LIFECYCLE_PROOF_GUIDE.md supplies the worked source/descriptor/copy/release route. NATIVE_VERIFICATION.md and DEPENDENCY_VERIFICATION.md preserve exact replay history. S governs final claim/design/path reconciliation.

### L1-20 — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Required conclusion is a clean committed candidate whose exact final content passes all local required checks; no theorem or partial receipt alone establishes it.

Final observed evidence and challenge: B/T/N/D have final passing source-bound receipts. S supplies final report, source/receipt manifests, strict claim/design/whitespace/integrity checks and exact committed clean-delivery identity. Postcommit checks are not asserted here; delivery is gated on root's external delivery.json.

### INV-STORE-IDENTITY — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `finalizer_memory cells` -> canonical same `cells` in exact compact suffix -> executed owner projection -> capacity counts actual `owner.memory.size` and encoded actual program.

Final observed evidence and challenge: D01_CONSTRUCTION, D02_RETAINED, D05_EXECUTABLE and P03_COPY reject missing same-store chains. N compares complete actual owners and exact retained memory arrays; B/T retain canonical equality only as a derived conclusion.

### INV-VALUE-DEPENDENCY — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Reservation pre-extent -> actual register 3 -> actual transfer/read destinations; copy receipt links loaded register to the immediate store; paired different successful replies imply different destination values.

Final observed evidence and challenge: P01_OUTPUT and P03_COPY reject lost producing-value receipts; D18_STORE_TRUE pins the operational agreement client. OUTPUT-SOURCE and loaded-register sensitivity use destination values, not enclosing log inequality. B/T check the complete global indices.

### INV-SEMANTIC-NONVACUITY — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `build_stage` derives producer/trace; actual scalar finalization and retirement derive canonical memory/zero extents; actual owner projection derives literal empty arrays. No Ready or answer is assumed at the public input.

Final observed evidence and challenge: D01_CONSTRUCTION, D02_RETAINED, D05_EXECUTABLE, D10_PUBLIC_TRUE and P05_PUBLIC_TRUE reject witness/contract bypasses. N builds from supplied input and observes real finalizer/release/key retirement before querying; Ready/answer is not supplied as a public premise.

### INV-TRACE-EXECUTION — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `RunsTo = run p ts.length s = <t,ts>`; `Continuous.exact_run`, actual boundary/service append, and `runArray.toRun` identify all observations with the execution.

Final observed evidence and challenge: D01_CONSTRUCTION, D05_EXECUTABLE, D06_REUSABLE and P01_OUTPUT through P04_RELEASES reject missing execution/occurrence facts. B/T identify exact RunsTo/runArray traces; N's counted_owner uses actual stepArray transitions.

### INV-STORE-AGREEMENT — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `s.Agree t` plus actual-prefix guarded reply agreement implies positional `Run.Agree`, not just final packet equality; unread cells are not falsely equated.

Final observed evidence and challenge: D18_STORE_TRUE rejects a weakened public agreement conclusion; C13/C14 pin paired guarded reads and the numeric extent condition. B/T check all live quantifiers. This does not assert equality of unread source cells.

### INV-READ-BACKING — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Every exposed read retains nth occurrence, actual before-state and step; successful logical reply equals canonical/current arena lookup and the checked physical lookup at that prefix.

Final observed evidence and challenge: D04_PHYSICAL, D15_CODE_FETCH_DROP, P02_METADATA and P03_COPY reject lost physical/indexed producing reads. B/T retain actual prefix states and exact occurrence equations; ABSENT-SOURCE rejects a missing reply at the real load.

### INV-WORD-WIDTH — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Actual prefix Fits W and physical lookup/reply bounds constrain every stored/result/control numeric word at the same W. Comparison Int values stay outside this numeric claim.

Final observed evidence and challenge: D03_SAFETY, D04_PHYSICAL and D07_UNIFORM reject weakened same-W bounds. FIELD-OVERFLOW checks every encoding constructor, including dormant fields. N validates represented numeric inputs/endpoints while comparison keys remain a separate channel.

### INV-ADDRESS-WIDTH — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Every actual logical/checked physical address fits 2^W; generic failed-read behavior retains guard/none; all encoding words, including dormant fields, fit the same width.

Final observed evidence and challenge: D04_PHYSICAL, D15_CODE_FETCH_DROP and D16_PREFIX_RESOURCES reject lost physical/fetch/prefix facts. B/T check guarded failed-read semantics without asserting a physical fetch outside extent; the field-width negative uses the same production Fits predicate.

### INV-INSTRUCTION-ATOMICITY — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `execute` arms are scalar old operations or one tail revoke; copy, clearing and retirement loops expand into counted transitions. Boundary admits only two scalar endpoint words plus control updates.

Final observed evidence and challenge: B/T expose scalar reserve, store, copy, clear and one-tail-cell releases. N checks actual per-transition sizes and charged boundary categories; P03_COPY/P04_RELEASES and the operational controls reject omitted scalar work. Reservation leaves an absent cell until an actual store.

### INV-PROGRAM-ACCOUNTING — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `program model` is input-independent; flattened actual encoding is counted, runtime n/M/request descriptors are charged state values, and fields fetched from code match that encoding.

Final observed evidence and challenge: D07_UNIFORM and D15_CODE_FETCH_DROP reject lost encoding/fetch facts; C10 pins actual code, bank, control and setup constants. B/T count the same fixed program and derive descriptor values through real loads; N does not specialize that program per fixture.

### INV-ORACLE-INDEPENDENCE — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Successful packet is proved equal to independent `scanWindow+1` with `LeftmostArgMin`; validator `reference` scans the supplied values using strict improvement and does not invoke packed query output.

Final observed evidence and challenge: D02_RETAINED, D11_WORD_TRUE and D12_COMPARISON_TRUE reject weakened semantic packet conclusions. N's strict-improvement scan is independent of packed query output and passes all16 cases, including invalid ranges and leftmost ties.

### INV-VALIDATION-REACH — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Validator imports new Executable/Controls and runs `initialOwner`, scalar `runOwner`/step counters and queryOwner; counter fold final owner is proved equal to runOwner.

Final observed evidence and challenge: N runs the new initialOwner/runOwner/queryOwner with real finalization/retirement, and its actual program-clear mutation rejects the entry projection. D05_EXECUTABLE/D17_READY_BANK reject lost public finite refinement. Predecessor validator results are not used.

### INV-ALL-SIZE — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Public theorem quantifies every input under the declared word/comparison domain and all represented endpoints; valid/invalid packet claims are projections of that same run, with no size/readiness dispatch.

Final observed evidence and challenge: B/T check universal declared-domain quantifiers; D11_WORD_TRUE and D12_COMPARISON_TRUE reject model-specific public bypasses. N's16 representative shapes supplement those proofs; finite fixtures are not substituted for the all-size theorem.

### INV-PROOF-SEPARATION — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Runtime State/Owner/Instruction carry arrays, words and scalar control; BuildStage/capstone are derived Prop witnesses, never evaluator arguments containing answers.

Final observed evidence and challenge: T reports only subsets of propext/Classical.choice/Quot.sound and no axioms for constant pins; both trust-hygiene scans have zero matches. B checks executable source; D10_PUBLIC_TRUE/P05_PUBLIC_TRUE reject public certificate bypasses.

### INV-NO-SYNTHETIC — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Actual builder/fragment/service traces compose by RunsTo and exact run equations; executable observations refine that same run. No trace is manufactured from a precomputed semantic answer.

Final observed evidence and challenge: D01_CONSTRUCTION, D05_EXECUTABLE and P01_OUTPUT through P04_RELEASES reject missing real execution/occurrence conclusions. N observes actual stepArray and uses the proved final-owner projection; no invented trace, decorative reread or semantic-answer replay is counted.

### INV-CATEGORY-SEPARATION — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Release, key-read/oracle comparison, admission/control categories remain distinct; costs are actual transition counts, retained numeric capacity is separate from peak and Int resources, and neither is a native-runtime measurement.

Final observed evidence and challenge: B/T check distinct scalar categories, exact fragment costs and array category refinement. N checks the exhaustive15-category mapping, sums, actual numeric/key retirement and two admission/two control events; model transitions and native elapsed seconds remain distinct.

### INV-PUBLIC-COMPOSITION — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: E13's seven fields share `continuousRun`, actual owner, actual program, retainedRho and W; construction witness and exact compact suffix are retained, and repeated-query guards stay represented/halted/Ready.

Final observed evidence and challenge: D01_CONSTRUCTION through D07_UNIFORM, D10_PUBLIC_TRUE, D13_ALIAS_PHYSICAL and P05_PUBLIC_TRUE reject loss/substitution of joined public objects. B/T independently type the same continuousRun, program, owner, width and remainder.

### INV-CERTIFICATE-ANTI-BYPASS — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: C01-C07 project each mandatory field at independent expected types; provenance client independently expands actual occurrences and scalar receipts. Weakening mandatory propositions must fail those fixed clients.

Final observed evidence and challenge: D's23 negative cases reject weakened/deleted/sibling/alias/public/provenance clauses at fixed independent declarations; D19/D20/P06 accept irrelevant/identity changes. Every mutated producer compiled before its client verdict was classified.

### INV-MUTATION-REPRODUCIBILITY — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Scalar positive/negative fixtures are immutable executable/proved objects with equal predicates, not transcript-only mutations. Public dependency cases require a frozen versioned registry, isolated replay, exact failure surface and hash restoration.

Final observed evidence and challenge: D's exact26-case registry, final classifier self-test, source/private-artifact restoration and shadow cleanup pass. N pins16 cases, strict selectors, full output surfaces and unchanged source/binary hashes. Scalar controls and the in-memory clear challenge are committed replayable definitions, not report-only experiments.

### INV-GLOBAL-PHYSICAL-MACHINE — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Same code/register/control offsets and current arena view cover every actual segment; image at index k uses actual before/after, physical read projection preserves order, scalar update image lemmas and array refinement share those objects.

Final observed evidence and challenge: D04_PHYSICAL, D08_DELETE_PHYSICAL, D09_SIBLING_PHYSICAL, D13_ALIAS_PHYSICAL and D15_CODE_FETCH_DROP reject weakening or replacing the whole-run image/fetch facts. B/T cover code/register/control/current arena on actual prefixes; native backing-capacity/alias claims remain outside this model.

### INV-WIDTH-SCALING — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: `log2(n+2)+1 <= wordWidth n <=192*(log2(n+2)+1)` is joined to actual program fields, state Fits, peak/physical extents and read values; no unrelated chosen width witness.

Final observed evidence and challenge: D07_UNIFORM rejects removal of the same logarithmic width result; D03_SAFETY/D04_PHYSICAL preserve its state/address consumers. C10 and B/T pin the actual program/bank/control constants; no unrelated width witness is introduced.

### CHK-FINAL — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: All final-required checks must run on submitted content with exact source/receipt identities, full outcomes and platform limitations; development labels do not imply this conclusion.

Final observed evidence and challenge: B/T/N/D completed on their recorded source identities. S binds submitted Git/workspace bytes, final report/static checks, commit/range checks and external delivery.json. Candidate-local closure is delivery-gated; no unperformed postcommit check is marked observed.

### CHK-SCOPE — Candidate-local closed; S delivery gate applies

Quoted conclusion and object chain: Exact base/governance and 43 immutable row bytes preserved; permitted paths only and clean committed state, with local formal/executable scope distinguished from native/aggregate/blind-audit acceptance.

Final observed evidence and challenge: S preserves exact base/governance, allowed paths, all43 immutable rows and clean committed delivery. The frozen byte checker is rerun after this append; LF-preserving checkout and raw Git/workspace equality are explicit. Root's postcommit identity/clean-tree receipt remains required.


The all-input claims come from the quoted kernel propositions, not finite tests.
Logical container extents are not native backing-capacity or external-alias
claims. Comparison Int resources remain separate from numeric retained words.
No aggregate gate, fresh blind audit or coordinator acceptance is credited here.

# LIFE-1-R1 frozen acceptance matrix

Exact inherited rows copied from Git base 12bd7f0fc2c87f2c9bdef3825bd92477e48e3433. Historical Open cells are immutable.
This matrix uses docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md; evidence is appended below the marker.

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
| `L1R1-SELECTOR` | The actual production lifecycle validator preserves omitted selector versus explicit environment selector semantics under both current bundled pwsh 7.6.5/.NET 10.0.11 and documented Windows PowerShell 5.1/.NET Framework. Registry/startup, argument-selected and full invocations that mean omission must launch the child with no LIFE1_VALIDATE_SELECTOR key, including when the caller has an inherited selector value; an intentional environment selection must reach the same child as the exact id: value. Restore the caller's prior process-environment state on success and failure, without persistent environment changes. Distinguish absent, representable present-empty, explicit id: empty, whitespace, valid, unknown, malformed, duplicate-argument and duplicate-channel inputs at the real command/child boundary. Preserve exact Lean selector rejection, no-semantic-case startup, ordered 16-case registry, independent semantic assertions and strict stdout/stderr/exit checks. Do not implement omission by an empty string or by passing null through the inherited helper's string cast. Commit a frozen exact control registry and actual child-process controls against the production adapter, including inherited ambient environments and failure restoration; component calls alone do not close process reach. Reproduce the immutable old wrapper's current-runtime failure with its same pinned executable, retain the legitimate old Windows PowerShell positive, then pass complete production full16 validation under both runtimes on repaired source. Missing runtime, timeout, wrong selector cardinality or extra/unexpected diagnostics is uncovered/failure, never success. | Local verification repair | Actual bounded production child controls and complete changed-script replays under the declared runtime profiles. | Production validator adapter or dependency finally -> unchanged child/verdict -> pinned receipts -> coordinator review. | Challenge omission/inherited environments or changed owned captured pins against the same production path; preserve exact failure surfaces. | Pending source-bound replay; no closure asserted at freeze. | Open; repair and final verification required. |
| `L1R1-CLEANUP` | The actual lifecycle dependency replay finally checks original-byte integrity and attempts removal of its disposable shadow in independent guarded operations, so a failed original-integrity check cannot skip safe cleanup. Keep the original stage failure, integrity failure and cleanup failure distinguishable; any failure remains nonzero with no terminal PASS, restored=false when integrity failed, and truthful shadowRemoved status. Do not restore, overwrite or erase changed original/tracked files automatically. Preserve the exact safe resolved-descendant and shadow-basename checks, process ownership/deadlines, mutex release, ordered 26-case registry, producer-before-client acceptance, unchanged expected types and strict mixed-diagnostic rejection. Commit source-bound controls reaching the production finalizer under real bounded child execution for intact success, intact prior failure, prior failure plus changed captured fixture pin, apparent success plus changed pin, partial captured baselines and safe cleanup rejection/failure. Mutate only owned scratch pins and shadows; invalid cleanup paths must remain untouched, and all fixture restoration must occur in their own finally. The exact old integrity-failure component must keep failing and exhibit its old retained shadow; the repaired finalizer must retain failure while removing the valid owned shadow. A count/summary-only imitation or an unrelated in-memory replacement predicate is insufficient. Replay all 26 production dependency cases through the changed script on frozen repaired content, including all positive and expected-reject clients, with final source identity and cleanup receipts. | Local verification repair | Actual bounded production child controls and complete changed-script replays under the declared runtime profiles. | Production validator adapter or dependency finally -> unchanged child/verdict -> pinned receipts -> coordinator review. | Challenge omission/inherited environments or changed owned captured pins against the same production path; preserve exact failure surfaces. | Pending source-bound replay; no closure asserted at freeze. | Open; repair and final verification required. |

<!-- APPEND-ONLY-EVIDENCE -->

# LIFE-1-R1 row dispositions

Status: BLOCKED. Formal evidence reusable; final delivery blocked. These 45 dispositions do not record coordinator acceptance or campaign closure.

Every inherited proposition/object-chain cell below is quoted exactly from the original historical ACCEPTANCE_EVIDENCE.md cell, including its cell padding. Historical candidate-closure labels are not copied as current dispositions.

Live guards: actual is Continuous.continuousRun model xs left right; initial is the supplied state at Layout.builderBase; cells=buildMemory xs; M=cells.length; B=producer.regs3; n=xs.length; W=wordWidth n. Public guards remain InputDomain model xs and endpoints below 2^W. Word input uses InputFits; comparison input retains separately counted arbitrary-Int resources.

Historical source: `docs/internal/extensions/lifecycle1/ACCEPTANCE_EVIDENCE.md` (SHA256 `f996eb73d4acc9020b093e568521d7413b232aba9d0d642376b564439cb22fab`). Current reuse checks cover 1162 exact initial Lean/consumer/toolchain byte identities. No new Lean proof, theorem type, assumption, native capacity claim, or arbitrary-Int bit bound follows from this repair.

The S delivery gate applies to every row: final source/receipt/report identities, original contract integrity, strict claim/design checks, scoped committed delivery, and required runtime controls remain mandatory. Original protected contract working files retain inherited CRLF bytes and fail the original raw hash gate. Windows PowerShell cannot execute the protected Hash-Bytes implementation's modern .NET APIs; its required source-derived cleanup controls remain blocked pending coordinator direction.

Available process evidence uses the protected helper's returned nonempty lines. It is not complete raw stream identity; overflow or exceptional cleanup can prevent output recovery. No missing evidence is promoted to a pass.

## Fresh verification families

B: recorded default build passed in 1.637s and named lifecycle/consumer build passed in 1.661s; their complete source-pin sets match current bytes. Receipts: `.lake/repair-r1/checks/final-default-build-pinned/result.json` (SHA256 `db4dc37d39b9d095f3044454a0633dc25ea1bfe2f35c2c092dbe1770bec0f46a`); `.lake/repair-r1/checks/final-named-build-pinned/result.json` (SHA256 `e04c96ec1183dd0500ff5369987d1959c90336248a6c604348f42ae9ebbb1160`). These are bounded build results with recorded cache reuse, not newly supplied mathematical assumptions.

N: both declared runtimes completed the actual production full16 wrapper, with ordered nine-process receipts and matching current source pins. pwsh: `.lake/repair-r1/checks/final-validator-pwsh-full/result.json` (SHA256 `65df72c58dcfbd3578bca936d81b66baf93e8f3a50ab0a5eee7bf1367845bbce`), full16 119.739s; startup `.lake/repair-r1/checks/final-validator-pwsh-startup/result.json` (SHA256 `786e73f5ba1a708e930309886cc7639fdf860c62f9d03fd7be9dfc093d1afd43`); winps: `.lake/repair-r1/checks/final-validator-winps-full/result.json` (SHA256 `319851b371b6e86ec3f1944bf561d7f550275b945690845dba11e28df639f96f`), full16 109.269s; startup `.lake/repair-r1/checks/final-validator-winps-startup/result.json` (SHA256 `2750c55245773d884dd01a652e259c1e7bcff10fc45964ccbfda82140eba01e0`).

D prerequisites: startup and a real focused case passed: `.lake/repair-r1/checks/final-dependency-startup/result.json` (SHA256 `c3a5c635d339a2796838e6e2f81b3131f2cdd270405e61a6e0baa1298e32da62`); `.lake/repair-r1/checks/final-dependency-focused/result.json` (SHA256 `dbaf7fce36a775aff5e76eebcd742f73391ef68f2bc5cae4b2eb0d08d853bfb0`). D local verification component RECORDED: exact ordered 26, 23 reject/3 accept, bounded producer/client receipts and nonempty restored baseline match; `.lake/repair-r1/dependency-full/20260921T053148629-87cd7da0/summary.json` (SHA256 `ec6b84c7ba1268cd3b69d7c6d66e9c3303f33bba6a844715e23bcde73b24782c`); `.lake/repair-r1/checks/final-dependency-full/result.json` (SHA256 `71416e8e3f47b446c5b0e7a8cb68786bba54958788c21fb9da0cc8f735910cd0`). Production diagnostic classification remains the source-bound runner's verdict, not a new classifier in this generator.

C: BLOCKED_REQUIRED_WINDOWS_DEPENDENCY_AND_FINALIZER_CONTROLS. Actual current-runtime67 controls passed; Windows selected all66 but passed only the exact first32 (S01..S23 and W01..W09), then D01 failed on the exact protected HashData API error in its positive boundary. Both 12-control registry campaigns passed. The complete Windows66 requirement remains live; observed evidence does not set controlsComplete. Receipts: `.lake/repair-r1/f2-controls-pwsh/summary.json` (SHA256 `9ec17492c6c0650e9ce1c6589d2247fa41c279d66c44042754e65040dfb214ec`); `.lake/repair-r1/f2-controls-winps/summary.json` (SHA256 `913f67491686037c77708b2022761af65b5ae3e91f1aa54469002e11d2f21a43`); `.lake/repair-r1/f2-registry-pwsh/summary.json` (SHA256 `1b4f7006532a404801554db8d62e14db669bc3eee201a3f9d1c86e07514301c7`); `.lake/repair-r1/f2-registry-winps/summary.json` (SHA256 `b4596bd104aa916c2410968ef5b8c1920cd03843028df32f677255f570385d63`); `.lake/repair-r1/f2-controls-winps/D01_OMITTED/process.json` (SHA256 `84d4312000219073f0885bc05124b8e26cea183039ae9f60b2a4982077f86445`); `.lake/repair-r1/f2-controls-winps/D01_OMITTED/fixture/positive.json` (SHA256 `5d65e1a95530fded469202ffac9837b752dd5c8052f17f5f98c803510f2a1d37`).

Historical harness failures: the earlier Windows driver evaluated its default RegistryPath before PSScriptRoot was established, and a separate W01 receipt-array wrapping error caused a count failure after production startup passed. Control source freeze 7c406b15bdc12333d323c92641ab6c6dad6af7a2 moves registry-default initialization into the driver body and reads JSON receipt arrays directly. The fresh Windows32 prefix includes W01 success on the corrected source; these historical harness failures are not current failure claims. The exact registry-byte checks and the separate protected HashData blocker remain in force. Separate Windows T01 observed PASS with the real bounded sleeper/descendant receipt: `.lake/repair-r1/checks/f2-winps-timeout/result.json` (SHA256 `a47ba38e25e48a68c26b38d204da88ad7154444e30bb1740176fe2c444e1f2ad`); `.lake/repair-r1/f2-winps-timeout/T01_DESCENDANT_TIMEOUT/fixture/result.json` (SHA256 `923e3cd53785a5ddd85a3d41863d0e68b86221a827787df33b36c0bcea120d75`). Separate Windows F01 intact P observed BLOCKED at protected Hash-Bytes with its exact source pin and HashData error: `.lake/repair-r1/checks/f2-winps-finalizer/result.json` (SHA256 `ff3e3457834fc0b3306fb2c8f0d8c9c2565b80a089c681f91cbe844290c0d871`); `.lake/repair-r1/f2-winps-finalizer/F01_INTACT_SUCCESS/fixtures/F01_INTACT_SUCCESS-8360764675824a05b19b3152dbfa9cac/result.json` (SHA256 `0f039003b2acc51fca54e9def9647b284fd7afa77e267a3067170b40d9134818`). Its capture failed before retaining any pins; restored=true covers an empty baseline only. This is not an accepted negative control.

### Evidence for L1-01

Historical proposition/object-chain cell, quoted without rewriting:

> “ E01: old execution is lifted with complete state/ordered trace. `requestProtocol.steps = 4` and its categories are exactly two admissions followed by two control entries. Successful release changes one tail cell/register and lowers one extent; zero extent faults. These operations are the constructors used by `actual` and `queryRun`. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-02

Historical proposition/object-chain cell, quoted without rewriting:

> “ E02: `Layout.program : InputModel -> List Instruction`, with no input/shape/size/request argument; hosts identify builder/descriptor/finalizer/retirement/service in that same list. `program.length = jumpBase model+1`; `encodedProgram.length <= 1116895`. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-03

Historical proposition/object-chain cell, quoted without rewriting:

> “ E03/E06/E07: `producer = {abstract with pc := base+source.size}` and live `RunsTo p initial producedState producedTrace`; `Continuous.exact_run` appends the actual finalization/service traces without a reset. Entry is 221239; BODY exit is 223345. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-04

Historical proposition/object-chain cell, quoted without rewriting:

> “ E03/E04/E14: actual `reserve 3` pre-extent equals `B`, register 3 is framed through the exit, and `move 0 3` returns that extent. Actual descriptor reads load `n`, `M`, left and right at local 1/4/8/10; E14 pins global indices `body.length+{1,4,8,10}` and actual prefix states. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-05

Historical proposition/object-chain cell, quoted without rewriting:

> “ E05/E06: `final.memory = fun a => cells[a]?`, `final.extent=M`, running exit at base+14; exact work `7*M+4*B+5`. Copy load/store indices are 4+7*i/5+7*i and releases 5+7*M+4*k, with actual producing state and value chain. E14 lifts them after builder+descriptor. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-06

Historical proposition/object-chain cell, quoted without rewriting:

> “ E06/E12: comparison retirement gives `keyExtent=0` and `keyRegExtent=0` after `4*n+5` actual steps; word retirement is zero steps on empty banks. `Ownership.Ready.empty_keys` concludes actual `keys=#[]` and `keyRegs=#[]`. `Owner` contains only arrays/control. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-07

Historical proposition/object-chain cell, quoted without rewriting:

> “ E04/E06/E07: produced metadata gives register 302=n and charged request loads give 300/301. The real jump reaches service entry; four preparation instructions and 8270 clears plus jump establish exact compact initial registers/PC, with incoming tail already proved. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-08

Historical proposition/object-chain cell, quoted without rewriting:

> “ E07/E10/E13: `actual = <service.final, fullTrace ++ service.transitions>` and actual transitions factor into that same construction, actual setup, then complete lifted `compactQueryRun cells n left right` transitions. Public valid/invalid projections give the half-open leftmost packet/zero. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-09

Historical proposition/object-chain cell, quoted without rewriting:

> “ E08/E12/E13: for any Ready halted owner and represented next request, `queryOwner.memory = es.memory`, Ready is restored, packet is exact, and `queryRun.steps <= 160257`. The actual query trace includes four boundary events and the full clear even with a dirty bank below 8273. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-10

Historical proposition/object-chain cell, quoted without rewriting:

> “ E03/E13: `wordInputContinuousConstructionQuery` assumes only existing InputFits plus represented endpoints; `comparisonInputContinuousConstructionQuery` quantifies all `List Int` with no magnitude guard. ValidRange selects semantic answer versus rejection, not a separate execution domain. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-11

Historical proposition/object-chain cell, quoted without rewriting:

> “ E02/E09/E10/E13: every actual prefix Fits W, physical extent/addresses/replies fit 2^W, every encoded field is below 2^W, and `log2(n+2)+1 <= W <= 192*(log2(n+2)+1)`. All are on the actual fixed program and same run. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-12

Historical proposition/object-chain cell, quoted without rewriting:

> “ E06/E07/E08: completed `fullTrace.length <= 1100000000*(n+1)` and actual total steps <= that bound+160253; repeated query <=160257. Exact equations count descriptor, copy, releases, key retirement, setup, jump and boundary events before stopped-fuel extension. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-13

Historical proposition/object-chain cell, quoted without rewriting:

> “ E09/E10/E12/E13: each actual prefix has arena extent <=5000000*(n+1), comparison keyExtent <=n and keyRegExtent <=2, while word extents are both zero. Executed owner capacity times W <=`2*n+retainedRho n`; `LittleOLinear retainedRho` uses the same code/register/control constants. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-14

Historical proposition/object-chain cell, quoted without rewriting:

> “ E11/E13: initial `State.Agree` plus `DynamicReadsAgree p fuel s t` at paired actual producing steps derives `Run.Agree`, equal result/register/status, steps, categories and ordered numeric/key reads/writes. Distinct successful replies at matched load occurrences force distinct destination registers. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-15

Historical proposition/object-chain cell, quoted without rewriting:

> “ E12/E13: for every fuel, actual finite `runOwner.toState`/`runArray.toRun` equals the defined abstract run, with all destinations derived from input guards. The retained owner has empty key arrays; `queryArray` preserves actual boundary/service observations and categories. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-16

Historical proposition/object-chain cell, quoted without rewriting:

> “ E13: `continuousConstructionQuery_holds model xs left right domain hl hr : ContinuousConstructionQuery model xs left right`, with seven same-object fields and no expected answer/equality premise. Independent C01-C07 clients spell out canonical/ready/profile and field propositions. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-17

Historical proposition/object-chain cell, quoted without rewriting:

> “ P/Q use the same production predicates: OutputReceipt, Initialized, Entry/FinalOutput, positional CopyReceipt, key extents and universal field Fits. Dirty-control source compares the actual second service's exact compact ABI after replacing one witnessed dirty register's clear. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-18

Historical proposition/object-chain cell, quoted without rewriting:

> “ Independent clients project every public field at expanded expected propositions; the direct provenance client expands Occurrence and receipt predicates. Required weakening/bypass mutations must fail these fixed clients, with positive controls and exact diagnostic/selector/restoration/cleanup checks. ”

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-19

Historical proposition/object-chain cell, quoted without rewriting:

> “ E01-E14 and the worked guide give one state/owner interface and the explicit `input -> BuildStage -> fullTrace -> actual -> owner -> next query` dependency chain. Scalar generic lemmas are reused; original builder and compact query remain the executable sources. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1-20

Historical proposition/object-chain cell, quoted without rewriting:

> “ Required conclusion is a clean committed candidate whose exact final content passes all local required checks; no theorem or partial receipt alone establishes it. ”

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-STORE-IDENTITY

Historical proposition/object-chain cell, quoted without rewriting:

> “ `finalizer_memory cells` -> canonical same `cells` in exact compact suffix -> executed owner projection -> capacity counts actual `owner.memory.size` and encoded actual program. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-VALUE-DEPENDENCY

Historical proposition/object-chain cell, quoted without rewriting:

> “ Reservation pre-extent -> actual register 3 -> actual transfer/read destinations; copy receipt links loaded register to the immediate store; paired different successful replies imply different destination values. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-SEMANTIC-NONVACUITY

Historical proposition/object-chain cell, quoted without rewriting:

> “ `build_stage` derives producer/trace; actual scalar finalization and retirement derive canonical memory/zero extents; actual owner projection derives literal empty arrays. No Ready or answer is assumed at the public input. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-TRACE-EXECUTION

Historical proposition/object-chain cell, quoted without rewriting:

> “ `RunsTo = run p ts.length s = <t,ts>`; `Continuous.exact_run`, actual boundary/service append, and `runArray.toRun` identify all observations with the execution. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-STORE-AGREEMENT

Historical proposition/object-chain cell, quoted without rewriting:

> “ `s.Agree t` plus actual-prefix guarded reply agreement implies positional `Run.Agree`, not just final packet equality; unread cells are not falsely equated. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-READ-BACKING

Historical proposition/object-chain cell, quoted without rewriting:

> “ Every exposed read retains nth occurrence, actual before-state and step; successful logical reply equals canonical/current arena lookup and the checked physical lookup at that prefix. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-WORD-WIDTH

Historical proposition/object-chain cell, quoted without rewriting:

> “ Actual prefix Fits W and physical lookup/reply bounds constrain every stored/result/control numeric word at the same W. Comparison Int values stay outside this numeric claim. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-ADDRESS-WIDTH

Historical proposition/object-chain cell, quoted without rewriting:

> “ Every actual logical/checked physical address fits 2^W; generic failed-read behavior retains guard/none; all encoding words, including dormant fields, fit the same width. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-INSTRUCTION-ATOMICITY

Historical proposition/object-chain cell, quoted without rewriting:

> “ `execute` arms are scalar old operations or one tail revoke; copy, clearing and retirement loops expand into counted transitions. Boundary admits only two scalar endpoint words plus control updates. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-PROGRAM-ACCOUNTING

Historical proposition/object-chain cell, quoted without rewriting:

> “ `program model` is input-independent; flattened actual encoding is counted, runtime n/M/request descriptors are charged state values, and fields fetched from code match that encoding. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-ORACLE-INDEPENDENCE

Historical proposition/object-chain cell, quoted without rewriting:

> “ Successful packet is proved equal to independent `scanWindow+1` with `LeftmostArgMin`; validator `reference` scans the supplied values using strict improvement and does not invoke packed query output. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-VALIDATION-REACH

Historical proposition/object-chain cell, quoted without rewriting:

> “ Validator imports new Executable/Controls and runs `initialOwner`, scalar `runOwner`/step counters and queryOwner; counter fold final owner is proved equal to runOwner. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-ALL-SIZE

Historical proposition/object-chain cell, quoted without rewriting:

> “ Public theorem quantifies every input under the declared word/comparison domain and all represented endpoints; valid/invalid packet claims are projections of that same run, with no size/readiness dispatch. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-PROOF-SEPARATION

Historical proposition/object-chain cell, quoted without rewriting:

> “ Runtime State/Owner/Instruction carry arrays, words and scalar control; BuildStage/capstone are derived Prop witnesses, never evaluator arguments containing answers. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-NO-SYNTHETIC

Historical proposition/object-chain cell, quoted without rewriting:

> “ Actual builder/fragment/service traces compose by RunsTo and exact run equations; executable observations refine that same run. No trace is manufactured from a precomputed semantic answer. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-CATEGORY-SEPARATION

Historical proposition/object-chain cell, quoted without rewriting:

> “ Release, key-read/oracle comparison, admission/control categories remain distinct; costs are actual transition counts, retained numeric capacity is separate from peak and Int resources, and neither is a native-runtime measurement. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-PUBLIC-COMPOSITION

Historical proposition/object-chain cell, quoted without rewriting:

> “ E13's seven fields share `continuousRun`, actual owner, actual program, retainedRho and W; construction witness and exact compact suffix are retained, and repeated-query guards stay represented/halted/Ready. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-CERTIFICATE-ANTI-BYPASS

Historical proposition/object-chain cell, quoted without rewriting:

> “ C01-C07 project each mandatory field at independent expected types; provenance client independently expands actual occurrences and scalar receipts. Weakening mandatory propositions must fail those fixed clients. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-MUTATION-REPRODUCIBILITY

Historical proposition/object-chain cell, quoted without rewriting:

> “ Scalar positive/negative fixtures are immutable executable/proved objects with equal predicates, not transcript-only mutations. Public dependency cases require a frozen versioned registry, isolated replay, exact failure surface and hash restoration. ”

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-GLOBAL-PHYSICAL-MACHINE

Historical proposition/object-chain cell, quoted without rewriting:

> “ Same code/register/control offsets and current arena view cover every actual segment; image at index k uses actual before/after, physical read projection preserves order, scalar update image lemmas and array refinement share those objects. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for INV-WIDTH-SCALING

Historical proposition/object-chain cell, quoted without rewriting:

> “ `log2(n+2)+1 <= wordWidth n <=192*(log2(n+2)+1)` is joined to actual program fields, state Fits, peak/physical extents and read values; no unrelated chosen width witness. ”

Disposition: UNCHANGED_FORMAL_EVIDENCE_REUSED; formal evidence reusable; final delivery blocked.

The quoted historical formal chain is reused only under its unchanged source and stated guards; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for CHK-FINAL

Historical proposition/object-chain cell, quoted without rewriting:

> “ All final-required checks must run on submitted content with exact source/receipt identities, full outcomes and platform limitations; development labels do not imply this conclusion. ”

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for CHK-SCOPE

Historical proposition/object-chain cell, quoted without rewriting:

> “ Exact base/governance and 43 immutable row bytes preserved; permitted paths only and clean committed state, with local formal/executable scope distinguished from native/aggregate/blind-audit acceptance. ”

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1R1-SELECTOR

New repair row; no historical formal proposition is asserted. The frozen requirement remains in CONTRACT.json and the 45-row matrix.

Disposition: OBSERVED_SELECTOR_COMPONENTS; final delivery blocked.

Both production full16 wrappers and the Windows32 selector/wrapper components are observed; the full C requirement and global S remain blocked.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

### Evidence for L1R1-CLEANUP

New repair row; no historical formal proposition is asserted. The frozen requirement remains in CONTRACT.json and the 45-row matrix.

Disposition: BLOCKED_LOCAL_VERIFICATION; formal evidence reusable where applicable; final delivery blocked.

Direct blockers: Windows PowerShell protected Hash-Bytes API availability and original protected working-file serialization; S applies.

Fresh references: B and N above; D prerequisites passed; D full26 component recorded. C partial observations recorded; required Windows dependency/finalizer controls blocked.

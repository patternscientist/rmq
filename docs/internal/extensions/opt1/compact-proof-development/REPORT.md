Status: INCOMPLETE
Phase: COMPACT-SEMANTICS-AND-SAFETY / CHECKED-LEAF HANDOFF. The coordinator assigned this bounded producer leaf and explicitly scheduled the final safety/axioms checks followed by slot return for whole-query composition. The assigned generic semantic and safety declarations now kernel-check. This report does not declare the full two-part OPT-1 candidate complete, accepted, or narrowed.

Handle/title: OPT-1 / (OPT-1) Tighten and compact packed compilation.
Worker: bound_proof. Branch/worktree: codex/opt-1-packed-compiler; C:/Users/poin/.codex/worktrees/1580/RMQ.
Exact governing base: 0e6a00f654abc64f8b68988fa9675b9a839dca2f.
Resume and final-leaf evidence HEAD: 8e355fda7788077f548865c1d6acf2ae5e88da55. Files below are the retained working-tree revisions; this worker made no commit.
Frozen contract: docs/internal/extensions/opt1/ACCEPTANCE_MATRIX.md, with original stable requirements and inherited invariants unchanged by this worker. The canonical proof skill, AGENTS, completion gate and CONTRACT_AUDIT.md were personally read. Exact preflight passed with required rmq-proof-sprint and actual runtime catalog rmq-coordinator/rmq-proof-sprint/rmq-audit-prompt.

Owned implementation and identity

- CompactProof.lean: 30,606 bytes, SHA-256 FC28F5FA141C1F66EA69C0B0C77BA988E7887F4AF273CD283C2B823F06748A1B.
- CompactSafety.lean: 34,119 bytes, SHA-256 75A541A25894F1807F118EC846E49E45DD47D02D98DB691F2A8CAB0C61320A29.
- Compact.lean was added to this worker's ownership for possible routine repairs, but passed unchanged: 3,133 bytes, SHA-256 A616631ACD50296408D5CD5D9BB6122C6F84C517C452C9FFE2DEE4177F63C434.
- Evidence lives only in docs/internal/extensions/opt1/compact-proof-development/. No shared source, capstone, query, static, public prose, decision ledger or replay edits were made by this worker in this resumed leaf. Peer edits were retained.

REQ-OPT-COMPILE: checked exact semantic producer

All declarations below are in namespace RMQ.SuccinctFinal.PackedWordRAM.Optimization, with Structured opened. CompactProof imports Compact only. Its relation is exactly:

```lean
def CompactRealizes (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    DataAgreesBelow observed (Data.ofState final) expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish)

theorem compact_realizes (memory : Memory) (program : Program) (block : Block)
    (fresh depth base : Nat) (s : State) (hpc : s.pc = base)
    (bounded : BlockRegistersBelow fresh block)
    (host : HostedAt program base (compactAt block fresh depth base)) :
    CompactRealizes memory program (compactCounter fresh depth) s
      (block.eval memory (Data.ofState s)) (base + compactSize block) (compactBound block)
```

The witness is an actual RunsTo segment of the unchanged primitive machine. DataAgreesBelow fixes final status and every register below the observed bound. The exact ordered attempted receipt list includes failed loads and multiplicity. No memory shape, successful load, running-state or query-validity assumption appears. Scratch is present in actual transition states and excluded only from source register observations.

compact_loop_realizes starts at base+2 with current counter=remaining and unit register=1. It accepts a body realization at base+3 and depth+1 for every actual body-entry state, and exact branch/decrement/jump fetch equalities. It proves the source iterate for remaining iterations, with running finish base+5+compactSize body and charged bound 1+remaining*(compactBound body+3). The two actual initializers compose with it, giving the positive-loop bound 3+count*(bodyBound+3). The compiled body is reused, while branch, subtraction and backward jump remain separate primitive transitions.

The standalone termination theorem is exactly:

```lean
theorem compact_compile_run (memory : Memory) (block : Block) (fresh depth : Nat)
    (s : State) (hpc : s.pc = 0) (bounded : BlockRegistersBelow fresh block)
    (fuel : Nat) (enough : compactBound block ≤ fuel) :
    DataAgreesBelow (compactCounter fresh depth)
      (Data.ofState (run memory (compactAt block fresh depth 0) fuel s).final)
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (compactAt block fresh depth 0) fuel s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (compactAt block fresh depth 0) fuel s).steps ≤ compactBound block ∧
    step memory (compactAt block fresh depth 0)
      (run memory (compactAt block fresh depth 0) fuel s).final = none
```

Normal code exhaustion yields the actual terminal step=None; an earlier halt or fault also does. compact_run_extend_stopped extends the actual segment to arbitrary adequate fuel, so the cost theorem is not merely run.steps≤its supplied fuel.

The actual appended-halt theorem is:

```lean
theorem compact_compile_with_halt (memory : Memory) (block : Block) (fresh output : Nat)
    (s : State) (hpc : s.pc = 0) (bounded : BlockRegistersBelow fresh block)
    (hout : output < fresh) :
    let source := block.eval memory (Data.ofState s)
    let program := compactAt block fresh 0 0 ++ [Instruction.halt output]
    let actual := run memory program (compactBound block + 1) s
    actual.result = (match source.final.status with
      | .running => some (source.final.regs output)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ compactBound block + 1 ∧
    actual.final.status ≠ .running
```

Named downstream chain: compactAt -> compact_realizes -> compact_compile_run / compact_compile_with_halt -> root QueryProof.compactQueryRun_original_observations and canonical refinement clauses -> compactPackedQueryCapstone_holds. Static worker's actual emitted length/frame facts compose at the query and certificate level. This leaf does not itself establish the concrete query's smaller code length or complete space accounting.

REQ-OPT-RUN: checked actual global and prefix safety

CompactSafety imports CompactProof. Its relation is exactly:

```lean
def CompactSafeRealizes (width : Nat) (memory : Memory) (program : Program) (observed : Nat)
    (s : State) (expected : Evaluation) (finish budget : Nat) : Prop :=
  ∃ final transitions,
    RunsTo memory program s final transitions ∧
    DataAgreesBelow observed (Data.ofState final) expected.final ∧
    transitions.filterMap (·.receipt) = expected.reads ∧
    transitions.length ≤ budget ∧
    (final.status = .running → final.pc = finish) ∧
    final.Fits width ∧ TraceSafe width transitions

theorem compact_safe_realizes (width : Nat) (memory : Memory) (program : Program)
    (block : Block) (fresh depth base : Nat) (s : State) (hpc : s.pc = base)
    (bounded : BlockRegistersBelow fresh block)
    (host : HostedAt program base (compactAt block fresh depth base))
    (fields : ∀ instruction ∈ compactAt block fresh depth base, instruction.Fits width)
    (bound : base + compactSize block < 2 ^ width)
    (fit : s.Fits width) (safe : block.Safe memory width (Data.ofState s)) :
    CompactSafeRealizes width memory program (compactCounter fresh depth) s
      (block.eval memory (Data.ofState s)) (base + compactSize block) (compactBound block)
```

The exhaustive actual emitted-field premise includes the count literal, counter identifiers, instruction tags and branch/jump targets. CompactStatic.compactAt_fits supplies it from constructor-exhaustive source fields and finite count/bank/PC guards. Global fit is a separate live hypothesis and invariant; it is never inferred from finite register agreement.

The run theorem used downstream has exactly the following conclusion and hypotheses:

```lean
theorem compact_compile_safe_run (width : Nat) (memory : Memory) (block : Block)
    (fresh depth : Nat) (s : State) (hpc : s.pc = 0)
    (bounded : BlockRegistersBelow fresh block)
    (fields : ∀ instruction ∈ compactAt block fresh depth 0, instruction.Fits width)
    (bound : compactSize block < 2 ^ width) (fit : s.Fits width)
    (safe : block.Safe memory width (Data.ofState s))
    (fuel : Nat) (enough : compactBound block ≤ fuel) :
    DataAgreesBelow (compactCounter fresh depth)
      (Data.ofState (run memory (compactAt block fresh depth 0) fuel s).final)
      (block.eval memory (Data.ofState s)).final ∧
    (run memory (compactAt block fresh depth 0) fuel s).reads =
      (block.eval memory (Data.ofState s)).reads ∧
    (run memory (compactAt block fresh depth 0) fuel s).steps ≤ compactBound block ∧
    (run memory (compactAt block fresh depth 0) fuel s).final.Fits width ∧
    TraceSafe width (run memory (compactAt block fresh depth 0) fuel s).transitions ∧
    (∀ index, index ≤ fuel →
      (run memory (compactAt block fresh depth 0) index s).final.Fits width)
```

The source agreement, ordered receipts, cost, final fit, transition safety and every-prefix fit all refer to the same actual run. Prefix index zero is included. TraceSafe expands to Instruction.Safe width t.before t.instruction and t.after.Fits width for each actual transition t. The final prefix clause applies the existing run_prefix_fits to that actual trace. Root QuerySafety specializes these hypotheses with buildMemory xs, the existing query-independent wordWidth xs.length and representable endpoints, then uses run_read_fits at each actual positional read occurrence. Those concrete query/space fields still require the root's composition check.

REQ-OPT-CONSUMER / CHK-OPT-CONTROLS: checked local consumers

- CompactConsumers.compact_realizes_expectedType explicitly projects actual RunsTo, final status, every observed register, exact ordered receipts, actual bound and running continuation PC.
- CompactConsumers.compact_halt_expectedType pins the actual emitted program, source-result case split, exact reads, steps and non-running conclusion.
- CompactSafetyConsumers.compact_safe_expectedType spells out actual final status/register agreement, ordered reads, cost, global final fit, every transition's safe instruction and fitting post-state, and every adequate-run prefix including zero.
- nested_loop_execution kernel-reduces an actual nested load program: repeat 3(load) inside repeat 2, followed by exit, emitted length 12, charged budget 40, result 7, six ordered successful receipts and exactly 40 steps.
- nested_loop_fault checks the first nested load fault at actual step 7, with exactly one failed receipt. No later loop controls execute.
- zero_and_stopped_loops checks empty emission for zero repeat and preservation of initially halted/faulted states.
- counter_collision_rejected proves the complete source register guard rejects a source write at the fresh counter boundary.
- finite_agreement_does_not_give_fit gives source agreement below register 2 while actual register 2 contains 16, proving that agreement does not imply global State.Fits 4.

These checked controls are local semantic/consumer evidence. They are not a substitute for the frozen whole-lane production mutation registry, exact selector behavior, subprocess fault campaign or final public-dependency replay. Those are peer/root-owned and remain outside this leaf report's verdict.

Proof construction and independent review

The nested body evaluates from the actual entry data after counter setup and branch. Its stronger next-depth agreement protects the caller's counter and unit register. source_eval_frame recovers their unchanged source values. The real decrement only changes the excluded current counter; source_eval_congr relates the rebased tail to the original iteration, including all reads. Early halt/fault retains the actual prefix without adding control transitions. The safe induction independently carries global entry/body/decrement/jump fit, proves local subtraction safety using counter=remaining+1 and unit=1, and transports tail source safety with source_safe_transport and actual nextFit.

source_relations independently inspected the two loop inductions and small controls without editing or running Lean. Its actionable initial Block.safe_repeat implicit-argument defect and unnecessary Option.none simp arguments were repaired before kernel checks. It found no semantic counterexample in rebasing, protected parent counters, tail safety or early-stop trace handling. Final elaboration repairs normalized only PC arithmetic and three-instruction prefix lengths; one tiny control replaced an unnecessary split with omega after simp. No public signature, premise, source evaluator or emitted route was weakened to pass.

While awaiting the shared slot, this worker also performed root-requested read-only reviews of QueryProof/QuerySafety and Certificate/Capstone/Consumers. No concrete object/guard/field defect was found. certificate-source-review.json pins hashes and a 37-field textual comparison against the frozen FIELDS.json registry, with no missing/duplicate/mismatched expected type. CERTIFICATE_SOURCE_REVIEW.md distinguishes that source review from root kernel/replay verification and final independent exact-commit audit.

Command, ownership and trust evidence

Personal resume preflight and command readiness are recorded in RESUME.json and RESUMED_DEVELOPMENT.md. Each check uses exact installed Lean 4.22.0 directly, -j1, task-local .lake/build/lib/lean and scripts/owned_process_tree.ps1 with a 180-second deadline and 2 MiB output limit. The elan shim's unwanted download was not used; no toolchain or shared build cache was changed. The direct development runner is not the production acceptance replay.

The successful narrow commands were:

```powershell
& docs/internal/extensions/opt1/compact-proof-development/check.ps1 -Modules Compact
& docs/internal/extensions/opt1/compact-proof-development/check.ps1 -Modules CompactProof
& docs/internal/extensions/opt1/compact-proof-development/check.ps1 -Modules CompactSafety
& docs/internal/extensions/opt1/compact-proof-development/check.ps1 -Modules Axioms
```

Exact result records:

- 20260912-084823-803-Compact.json: PASS, 12.803 seconds.
- 20260912-084901-469-CompactProof.json: diagnostic FAIL, 13.141 seconds, three PC normalization errors.
- 20260912-085040-423-CompactProof.json: diagnostic FAIL, 23.580 seconds, remaining prefix-length normalization.
- 20260912-085200-649-CompactProof.json: final PASS, 12.800 seconds, no output.
- 20260912-085248-004-CompactSafety.json: diagnostic FAIL, 26.348 seconds, only the final finite-agreement control's unnecessary split.
- 20260912-090310-823-CompactSafety.json: final PASS, 8.119 seconds, no output.
- 20260912-090340-416-Axioms.json: PASS, 4.289 seconds, full axiom output retained.

All owned commands exited normally; none timed out or exceeded the output limit. The leaf released the sole slot after the first safety diagnostic to permit CompactStatic/Query verification, waited without Lean, received explicit slot return, then released to root immediately after final safety/axioms success. No heavy commands overlapped.

Axioms.lean inventories the seven generic semantic/safe producers, all three direct expected-type consumers and all five controls. Only propext, Classical.choice and Quot.sound occur; the operational controls use fewer of these. No sorryAx or added axiom appears. final-leaf-checks.json records source lengths/hashes, a combined trust/Mathlib/native-decision lexical scan with no matches (rg exit 1), and git diff --check exit 0. Git's ordinary LF/CRLF advisories are preserved in that JSON. The broad final build, full-tree scans, committed-range check, design-policy check and public claim drift scan are coordinator-scheduled whole-candidate obligations, not rerun by this narrow leaf.

Remaining full-target obligations and reentry

There is no unmet generic proof or safety elaboration obligation in these owned files. The whole OPT-1 matrix remains coordinated at the root: concrete query instantiation and inhabited certificate checks, literal-code/finite-scratch space composition, production runtime and public-field mutation campaigns with restoration, mandatory final checks, exact candidate commit and independent audit/acceptance. The static peer has reported its concrete Query/typed-consumer pass, but its numeric results are evidence owned by that peer and the root join. No requirement was removed or postponed merely because this leaf is green.

The next executable consumer is root QueryProof/QuerySafety -> Certificate -> Capstone -> Consumers, using the passing local artifacts. If root changes a generic producer, rerun only that producer and its direct consumers under explicit serialized slot ownership, and retain new source hashes. Root may incorporate this proof digestion into the task-scoped decision/digestion ledgers. No new route decision was made here beyond the already-reviewed fresh-counter route; the explicit arithmetic fixes are proof elaboration details. Actual-state rebasing and independent global fit deserve the design rationale already tracked in the contract audit.

Proof digestion

The checked proof means that counted loops really execute the same source computation and the same ordered attempted reads, while charging their initializer, test, subtraction and backward jump instructions. Scratch registers stay visible in actual machine states and have their own complete safety proof. Semantic simulation needs only hosting, starting PC and the complete source-register bound; word safety additionally needs actual initial fit, source operation safety, fitting emitted fields and a fitting end PC. A skeptical graduate student should next inspect how the whole query discharges those live hypotheses for the exact buildMemory allocation, and whether literal encoding plus the complete finite scratch bank is counted in the same-width space theorem. Those questions feed the named root capstone, not an alternative endpoint.

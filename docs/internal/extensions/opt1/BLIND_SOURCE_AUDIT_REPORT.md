The exact-target source review found no load-bearing defect. Executable, axiom-inventory, mutation-campaign, and aggregate certification remain unexecuted in this lane; this report does not record coordinator acceptance.

Scope: **FRESH BLIND DELTA**, target `ac5af8e416f906391dc117f083a883acc053a268`, original base/governance `0e6a00f654abc64f8b68988fa9675b9a839dca2f`, returning-phase base `8e355fda7788077f548865c1d6acf2ae5e88da55`. I read the frozen matrix from `1f3a4199eaa95324cd1daaadbab89340ca8392c4`, source, executable controls, and literal certificate fields. I did not read prior audits, worker reports, appended matrix verdicts, or campaign transcripts. No files were edited.

Preflight passed with explicit no-role authorization. Expected, checked-out, working, and runtime RMQ skills were exactly `rmq-audit-prompt`, `rmq-coordinator`, and `rmq-proof-sprint`. No role skill was applied.

**Findings**

- **P0/P1:** None established by source reconstruction.
- **P2:** No source-blocking issue established. Remaining executable and certification evidence is unavailable to this lane, rather than failed.
- **P3, documentation polish:** Missing spaces in `docs/DIGESTION_LOG.md:1773` (`sharper150739`) and `:1786` (`fields and78`). These do not change the mathematical claims.
- The new digestion entry contains the conceptual change, plain-English interpretation, live model assumptions, and skeptical next checks at `docs/DIGESTION_LOG.md:1769–1789`. I found no missing digestion category in that entry. The worker completion report itself was intentionally withheld.

For compact references below, `O/` means `RMQ/Core/WordRAM/Optimization/`, and `P/` means `RMQ/Core/WordRAM/Packed/`, under `C:/Users/poin/.codex/worktrees/1580/RMQ`. All references concern the exact target.

Let:

- `D xs := buildMemory xs`;
- `w xs := wordWidth xs.length`;
- `s xs l r := initialState xs.length l r`;
- `C m n l r := run m compactQueryProgram compactQueryBudget (initialState n l r)`;
- `B m n l r := queryRun m n l r`, using the unchanged original program and original fuel;
- `R xs l r := l < 2 ^ w xs ∧ r < 2 ^ w xs`;
- `V xs l r := ValidRange xs l r`.

“Source-supported” below means that I reconstructed the declaration, proof path, guards, and objects. It does not mean I independently ran Lean in this lane.

**Independent reconstruction of all 35 frozen IDs**

1. **`REQ-OPT-BUDGET`**

   > Prove branch-sensitive execution bounds from actual compiler/run semantics, then instantiate the actual query source. The measured candidate recurrence is skip=0, action/exit=1, seq=sum, ifZero=max(1+zero,2+nonzero), repeat=count*body; querySource plus halt evaluated to 150739. Re-derive it and prove that bound or a corrected, strictly smaller-than-837572 universal bound if a precise counterexample shows the candidate recurrence wrong. Prove the bound on the existing complete queryRun with its original adequate fuel, and prove that running the original queryProgram with the new smaller fuel halts with the same answer and ordered receipts. Merely bounding the steps of run at the smaller fuel by that fuel is tautological and does not discharge this row. No literal constant without the execution bridge.

   **Source-supported.** `O/BranchBound.lean:17` defines the specified recurrence. `compile_realizes_branchBound`, at `:100`, proves a hosted `Realizes` segment bounded by that recurrence for every memory and initial state at its base PC. `compiled_run_bound_and_fuel_eq`, at `:230`, proves
   `run a.steps ≤ branchBound block ∧ run a = run b`
   whenever both fuels dominate the recurrence and PC is zero.

   `O/Capstone.lean:37–60` instantiates this on `.seq querySource (.exit 3)`: `B.steps ≤ 150739`, and `run memory queryProgram 150739 initial = B`, universally in memory, size, and endpoints. Canonical halting, packet, and receipt equality follow at `:64`.

   **Challenge:** Accepted proposition P is the bound on the original complete run plus full old/new-fuel equality. Rejected Q is merely `run newFuel.steps ≤ newFuel`. Q does not imply P. `original_run_bound_expectedType` and `reduced_fuel_expectedType`, `O/Capstone.lean:78–85`, pin the required executions and fuels. The one-short truncation control at `O/BranchBound.lean:297` is relevant adversarial evidence, pending independent execution/checking here.

2. **`REQ-OPT-COMPILE`**

   > Implement actual compact code emission using charged counted loops and/or reusable subroutines. Prove simulation, termination/fuel, jump/return behavior, register frames and actual code-size accounting. The preliminary six-instruction loop estimate was 213038 instructions and depth one; it was not an emitted program. Achieve a strict emitted-code reduction against current queryProgram and report the independently checked concrete size.

   **Source-supported.** `compactAt`, `O/Compact.lean:41–58`, emits ordinary instructions. Positive repeats emit two constants, a branch, one body, subtraction, and backward jump; zero repeats emit no code. `compactAt_length` at `:62` relates the actual list to `compactSize`.

   `O/CompactProof.lean:121` proves the remaining-counter induction; `:229` proves hosted compiler simulation; `:409` derives adequate-fuel execution from the witnessed segment and terminal fetch. The emitted query has **212964 instructions**, proved at `O/Query.lean:99–104`, strictly below the original program length at `:119–121`. Independent execution of the size calculation was not performed here.

   **Challenge:** P is a positive loop with fresh counter pairs at successive depths and protected source registers. Q reuses the parent pair for a nested body or initializes the count to zero. For nested `repeat 2 (repeat 3 load)`, Q can lose the required six reads. `compact_realizes_expectedType`, `O/CompactProof.lean:473`, pins actual source-register/status/read behavior; `C06-NESTED-LOOP`, `N02-COUNTER`, and `N04-FRESH-COLLISION` target these failures.

3. **`REQ-OPT-RUN`**

   > Prove whole-query exact answers, representable-invalid behavior and safety of every primitive/prefix/register/address/encoded operand on the same buildMemory allocation. Preserve the ordered attempted data-read/reply behavior, or explicitly prove the exact accepted observation relation if an optimization removes redundant reads; do not silently weaken it. Current target preserves the ordered trace, so a change requires a reviewed contract amendment.

   **Source-supported.** `O/QueryProof.lean:33` proves `C.result = B.result ∧ C.reads = B.reads` for arbitrary memories. The equality is of ordered receipt lists, preserving attempts, failures, and multiplicity. Canonical packet correctness is at `:64`; invalid raw queries return `some 0` with `[]` reads at `:75`.

   `O/QuerySafety.lean:24` proves `RankExecutionSafety (D xs) (w xs) compactQueryProgram compactQueryBudget (s xs l r)` under `R`. This includes all static fields, final fit, transition safety, prefix fit, and read width/backing. `O/Certificate.lean:61–106` fixes those objects explicitly.

   **Challenge:** P is ordered-list equality plus the exact result and safety predicates. Q retains only receipt membership or distinct addresses. Repeated-load fixture C05 distinguishes them. Weakening `arbitraryMemoryObservations`, `transitionSafety`, or `prefixSafety` must fail the corresponding fixed consumer at `O/Consumers.lean:150`, `:302`, or `:318`. Canonical safety is not claimed for arbitrary malformed memory.

4. **`REQ-OPT-SPACE`**

   > Account for compact code encoding and added loop/subroutine registers/stack in complete 2n+o(n) space with the existing word-width convention or a proved conservative common refinement. Input-dependent constants cannot migrate into uncounted code.

   **Source-supported.** `O/Query.lean:16–24` defines one closed program, actual flattened encoding length, finite register count, and scratch count. The values are **722339 encoded words**, **8273 registers**, and **8276 scratch words** at `:91–117`. Thus both added counter registers are charged.

   The public capacity proposition is
   `((D xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length + (compactQueryRegisterCount + 3)) * w xs ≤ 2 * xs.length + compactQueryCompleteRho xs.length`
   at `O/Certificate.lean:24–27`; its residual is `LittleOLinear` at `:19`. The chain is actual encoding theorem → finite-bank theorem → `P/Allocation.lean:187–197` → `O/Query.lean:152–160`.

   **Challenge:** P charges the literal encoding and complete finite bank; Q omits counters or substitutes a smaller sibling store. A smaller capacity inequality does not imply P. `completeCapacity_expectedType`, `O/Consumers.lean:50`, independently repeats P; `unusedRegisters_expectedType`, `:178`, pins the operational bank bound.

5. **`REQ-OPT-CONSUMER`**

   > One inhabited capstone must connect actual compact emitted code, its exact execution/cost bound, same allocation, width/safety and complete space. Keep original public aliases and constants available; additive definitions allow all other workers to proceed on baseline.

   **Source-supported; campaign evidence pending.** `CompactPackedQueryCapstone`, `O/Certificate.lean:16–126`, contains 39 fields. `compactPackedQueryCapstone_holds`, `O/Capstone.lean:92–143`, supplies them from the actual construction. I independently compared the literal FIELDS contract against all **39 generic and 39 canonical consumers**: no type/body discrepancies were found.

   The original `RMQ.lean`, `P/` sources, and `lean-toolchain` have no delta against the original base. The Lake change only adds the uniquely named validator target.

   **Challenge:** P is the complete fixed proposition for each projected field. Q deletes a field, weakens it to `True`, or supplies another field. Fixed generic consumers directly project `certificate.field`; canonical consumers apply those generic consumers to the inhabitant. The replay’s producer-before-consumer order is at `scripts/packed_optimized_certificate_replay.ps1:258–270`. Actual mutation rejection is unexecuted here.

6. **`CHK-OPT-CONTROLS`**

   > Persist branch directions, nested sequencing, zero/one/repeated loops, early exits/halt, targets at code boundaries, fresh-counter collisions, invalid queries, full different-block paths and malformed metadata. Test compile correctness over semantic examples plus universal proofs; corrupt jumps/counters/budgets and ensure exact-type consumers or the production replay reject them.

   **Controls present; execution pending.** `RMQ/Validation/PackedOptimized.lean:40–84` supplies 13 compiler and 10 query positive fixtures; `:94–128` supplies four negative controls. The fixtures cover both branches, zero/one/repeated/nested loops, early halt, missing load, empty body/branches, initially stopped states, invalid endpoints, maximum representable endpoints, distinct route cases, and malformed metadata.

   P compares actual status, exact receipt list, exact step count, protected registers, and the independent source evaluator. Q corrupts jump/counter/fuel/fresh origin. `verifyCompiler`, `:99–112`, is the shared rejection surface. Different-block route checks at `:146–158` additionally pin a genuine interior read.

7. **`REPLAY-EXACT-REGISTRY`**

   > any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

   **Source-supported runner; execution pending.** Runtime replay pins 27 cases at `scripts/packed_optimized_runtime.ps1:33–84`; the Lean validator pins its 23 positive and four negative IDs at `RMQ/Validation/PackedOptimized.lean:86–95,214–236`. Certificate replay pins **80 cases: 78 rejects and two accepts**, at `scripts/packed_optimized_certificate_replay.ps1:26–47,91–126`.

   P requires exact order/count/identity and final executed/expected equality. Q removes, duplicates, or reorders a registered case. Runtime `Assert-OPT1Exact` and certificate `Assert-CExact` must reject Q; final checks are runtime `:387` and certificate `:391`. This is source evidence, not an observed full run.

8. **`REPLAY-SELECTOR-NONVACUITY`**

   > omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

   **Source-supported runner; boundary executions pending.** Runtime selection is fixed at `scripts/packed_optimized_runtime.ps1:88–93`; certificate selection at `scripts/packed_optimized_certificate_replay.ps1:128–134`. Binding detection distinguishes omitted from explicitly empty. Omitted selects the full suite; a valid ID selects one; empty, whitespace, malformed, and unknown IDs fail.

   P is a nonempty exact selection. Q is an explicitly empty selector silently treated as omitted or successful zero-case selection. Production boundary tests at runtime `:189–238` and certificate `:325–363` invoke the script parameter boundary and reject semantic execution on bad selectors. The Lean environment channel is checked separately at validator `:200–212`.

9. **`REPLAY-SUBPROCESS-DEADLINE`**

   > run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.

   **Source-supported runner; host behavior pending.** Both runners call `Invoke-RMQOwnedBoundedProcess`: runtime `:100–110`, certificate `:139–152`. Certificate mutants exist only in isolated copies, restored byte-for-byte in `finally`, `:273–285`; original source/import hashes and tracked-source status are compared at `:398–414`.

   P requires ordinary expected exit, preserved stderr, bounded ownership, and restoration. Q counts timeout/setup failure as semantic rejection or accepts an uncreated child-process condition. Runtime deadline controls at `:241–272` preserve exit 7/stderr and explicitly mark an unstarted descendant `UNCOVERED`. Certificate rejection filtering at `:160–184` excludes resource/setup failures. No host deadline experiment was run here.

10. **`CHK-OPT-DEVELOPMENT`**

    > build only the owned changed modules and direct typed consumers with bounded, one-job Lean/Lake execution; use narrow executable cases as new operations appear.

    **Unexecuted in this audit.** `scripts/packed_optimized_build.ps1:24–79` runs a sequential module plan with `-j1`, per-module/total deadlines, source hashes, and bounded-process records. It has explicit reuse records and invalidates consumers after rebuilt direct imports.

    P is exact-source narrow producer/consumer evidence; Q is predecessor-only validation or a stale imported artifact. Runtime import-closure checks at `scripts/packed_optimized_runtime.ps1:275–314` reject missing/older artifacts. Timestamp and snapshot checks alone are not an independent fresh compilation receipt; coordinator verification must supply that evidence.

11. **`CHK-OPT-FINAL`**

    > lake build; explicit build/import of every new capstone and typed consumer (default RMQ may not import new modules); new lane's full validation registry and relevant axiom inventory; trust hygiene; git diff --check; after committing, git diff --check 0e6a00f654abc64f8b68988fa9675b9a839dca2f..HEAD; scripts/design_decision_check.ps1 -Strict -Base 0e6a00f654abc64f8b68988fa9675b9a839dca2f.

    **Partially checked, otherwise unexecuted.** I ran trust scans and scoped base-to-target `git diff --check`; both were clean. I did not run `lake build`, explicit Lean imports, executable registry, axiom inventory, the unrestricted base-to-target whitespace check, or strict design-decision check.

    P requires the entire named exact-target certification set. Q is a green default library build that never imports `O/Capstone.lean` or `O/Consumers.lean`. The explicit import in `O/Consumers.lean:1` and validator imports show what the scheduled check must reach, but source presence does not close this verification row.

12. **`CHK-OPT-TRUST`**

    > rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib" RMQ lakefile.toml; and rg -n "native_decide\|Lean\.ofReduceBool" RMQ for any new trust/validation surface. Explain actual matches and never hide them.

    **Hygiene scans checked; axiom execution pending.** Both prescribed searches had no matches. New optimization imports remain inside the existing RMQ/Lean/Std footprint. The checker script imports Lean’s builtin collector only in the checker, `scripts/packed_optimized_axiom_union.lean:1–3`.

    P is the exact new roots’ actual dependency inventory, with no unexplained trust additions. Q is merely successful source grep or a printed dependency list for the wrong roots. The checker freezes 93 distinct roots, checks existence/visitation, and retains explicit standard `#print axioms` for both named public targets at `:113–128`. I reviewed that source but did not run it.

13. **`CHK-OPT-CONDITIONAL`**

    > scripts/claim_drift_scan.ps1 -Strict if public prose changes (the narrow family/digestion entry qualifies); targeted existing compatibility checks if their imported executable behavior changes. Add explicit #print axioms for the new exact declarations.

    **Required conditional checks pending.** Public family/digestion prose changed. I inspected only the new factual claims at `docs/FAMILY_SUMMARY.md:3454–3468` and `docs/DIGESTION_LOG.md:1769–1789`. The numerical and model-scope statements agree with the source reconstruction.

    P includes the strict prose scan and exact declaration inventory; Q substitutes a prose assertion of certification. No strict claim-drift execution occurred in this lane. Existing executable baseline source was unchanged.

14. **`CHK-OPT-AUDIT`**

    > Full aggregate certification belongs to the coordinator-scheduled final audit phase. Request it on frozen content and do not run several redundant full gates; candidate completion records this pending external acceptance stage accurately. PRE contract freeze additionally requires the plan's contract gate before its blind audit.

    **External phase remains open.** This report supplies independent exact-source reconstruction only. The other lanes’ receipts and coordinator’s scheduling/acceptance decision were not assumed.

    P is independent reconstruction plus scheduled exact-target certification. Q is worker self-acceptance or interpreting this source-only report as aggregate certification. No PRE builder is present in this lane, so the PRE-specific clause does not add a builder obligation here.

15. **`INV-STORE-IDENTITY`**

    > the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient;

    **Source-supported.** `O/Certificate.lean:22–30,61–106` uses `buildMemory xs` both in data/complete capacity and execution/safety/backing. `O/Query.lean:157` obtains capacity from the same allocation via `P/Allocation.lean:157–197`.

    P is capacity and execution over `D xs`; Q replaces only the capacity store with a sibling. The smaller sibling inequality does not imply the fixed `completeCapacity_expectedType`, `O/Consumers.lean:50`. No equality to a different allocation is silently assumed.

16. **`INV-VALUE-DEPENDENCY`**

    > returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads. When the requirement concerns the returned answer or route, evidence must constrain that value, state, or route; inequality of an enclosing trace record can be satisfied by its log alone and is insufficient;

    **Source-supported operational chain; universal per-read sensitivity is not claimed.** `P/Primitive.lean:136–153` writes loaded values into registers and halts from a register. `P/Setup.lean:15–23` loads metadata into its actual bank. The physical reader transfers `spanBlock`’s loaded result into packet register 8194 at `P/PhysicalRead.lean:19–36`; rank seed/combination operations use those packet registers at `P/RankSource.lean:74–109`; final rank writes register 3 at `P/QuerySource.lean:27–38`.

    `O/QueryProof.lean:13–38` carries this operational source result into actual compact execution for arbitrary memory. `specResult`, `O/Certificate.lean:121`, constrains the returned packet itself.

    P preserves those value/state dependencies. Q retains receipts while overwriting the answer with a fixed zero. Q fails `specResult_expectedType` for `[7]`, range `[0,1)`, and the validator checks the answer itself at `:178–191`. The malformed-metadata control also requires a changed result, not merely a changed enclosing run record. It remains incorrect to infer that every read must individually change the final answer.

17. **`INV-SEMANTIC-NONVACUITY`**

    > semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself;

    **Source-supported.** `CompactRealizes`, `O/CompactProof.lean:15–22`, contains actual `RunsTo`, source-register/status agreement, exact receipts, and length. `RunsTo` expands to equality with `run`, `P/Calculus.lean:40–42`. Safety adds actual global fit and transition safety at `O/CompactSafety.lean:14–22`.

    P is this execution-derived relation. Q replaces it with `True` or a label-only predicate. Expanded generic consumers at `O/CompactProof.lean:473` and `O/CompactSafety.lean:527–544` pin the actual projections, so Q cannot furnish the required conclusion.

18. **`INV-TRACE-EXECUTION`**

    > traces and footprints are derived from the execution they describe;

    **Source-supported.** `P/Primitive.lean:163–187` generates transitions from `step` and defines reads by `transitions.filterMap`. The compact simulation’s receipt equality is over that list, `O/CompactProof.lean:18–20`; the certificate’s positional theorem pins transition occurrence and execution at `O/Certificate.lean:99–106`.

    P uses actual transition-indexed reads. Q appends synthetic receipts after the run. `positionalReadBacking_expectedType`, `O/Consumers.lean:352`, and the exact ordered observation consumer must reject the substituted proposition.

19. **`INV-STORE-AGREEMENT`**

    > supplied-store agreement determines result, cost, and the relevant trace;

    **Source-supported.** `O/QueryProof.lean:83–88` proves full `C supplied = C memory` from agreement at every address in the actual run’s receipt list. It uses `P/Calculus.lean:240–244`, whose conclusion is full run equality, hence includes result, steps, and transition/read traces.

    P includes agreement on attempted reads, including `none` replies. Q checks only successful reads. On a failed load, supplying a newly present word can change execution, so Q does not imply P. `suppliedMemoryAgreement_expectedType`, `O/Consumers.lean:404`, pins the complete premise and full-run equality.

20. **`INV-READ-BACKING`**

    > every successful read is backed positionally by the counted store;

    **Source-supported, stronger attempted-read statement present.** `O/Certificate.lean:99–106` states that an indexed transition’s receipt comes from an actual fetched `.load`, its address is the pre-state address register, and its reply is `(D xs)[address]?`. This is instantiated from `run_read_at`, `P/Calculus.lean:186–198`.

    P is occurrence-indexed backing in `D xs`. Q supplies only “the returned word occurs somewhere in memory.” Q loses position and does not imply the fixed consumer at `O/Consumers.lean:352–372`.

21. **`INV-WORD-WIDTH`**

    > stored and returned words fit one declared modeled machine word;

    **Source-supported.** Stored words fit by `P/Width.lean:421–424`. Under `R`, final state and halted payload fit `w xs` by `O/QuerySafety.lean:24`; `State.Fits`, `P/Primitive.lean:199–201`, quantifies every register and halted value.

    P uses `w xs` for data, final registers, and return value. Q preserves only low-register agreement while allowing an oversized fresh register. `finite_agreement_does_not_give_fit`, `O/CompactSafety.lean:547–555`, explicitly demonstrates Q with width 4 and register value 16. `finalStateFit_expectedType`, `O/Consumers.lean:290`, requires P.

22. **`INV-ADDRESS-WIDTH`**

    > every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands;

    **Source-supported within the declared model/domain.** `Instruction.encoding/Fits`, `P/Primitive.lean:78–108`, includes tags and every numeric operand. `compactAt_fits`, `O/CompactStatic.lean:198–258`, separately checks original source fields, repeat literals, wrapper tags, fresh-register capacity, and end PC, over every emitted instruction. Query instantiation is `O/Query.lean:123–138`.

    Under `R`, every executed read address fits by `O/Certificate.lean:92–98`; all allocated addresses and the first failed address fit by `P/Width.lean:451–454`.

    P includes dormant code, count literals, identifiers, and sentinel boundary. Q checks only fetched successful loads or reuses the baseline inventory that erases repeat counts. `O/CompactStatic.lean:301–329` contains explicit oversized count/counter/target/tag counterexamples. `programFieldsFit_expectedType` and `readWidth_expectedType` pin the public statements.

23. **`INV-INSTRUCTION-ATOMICITY`**

    > each modeled small step performs the familiar primitive operation it advertises. A constructor whose evaluator body hides recursion, a variable-length scan, repeated rank/select work, decoding, or several arithmetic categories is a macro-step unless that work is expanded into charged transitions or bounded by an explicitly accepted primitive;

    **Source-supported under unchanged primitive-cost assumptions.** Compact emission uses the unchanged `Instruction` type and `execute`, `P/Primitive.lean:53–62,133–153`. The loop controls are separate constant, branch, subtraction, and jump transitions, `O/Compact.lean:53–58`.

    P retains one advertised primitive per step; Q introduces an optimizer/loop opcode that executes a recursive body internally for one tick. No such constructor or evaluator change exists. The actual emitted-program identity and compiler simulation consumers fix the present instruction list. Multiplication, division, shifts, bit operations, and indexed access retain their baseline modeled unit-cost interpretation; this is not a Lean-runtime statement.

24. **`INV-PROGRAM-ACCOUNTING`**

    > input-dependent constants and metadata carried by executable code are counted machine data or are derived uniformly from counted/public inputs. Calling shape-specialized data "program code" does not remove it from the payload/state accounting obligation;

    **Source-supported.** `compactQueryProgram` is a closed definition with no `xs`, memory, or endpoint parameter, `O/Query.lean:16–18`. The original source is likewise fixed and loads its varying metadata at runtime, `P/QuerySource.lean:55–63` and `P/Setup.lean:15–23`. All literal instruction words, including repeat counts, are counted.

    P is fixed code plus counted metadata. Q specializes an uncounted code constant to the input’s answer or geometry. Q changes the fixed `emittedProgram` identity or complete encoding object; `O/Consumers.lean:124–130` and `:50–62` pin those objects.

25. **`INV-ORACLE-INDEPENDENCE`**

    > executable fixtures and edge-case expected values come from an independent specification or a theorem already connected to it, never from the implementation result being tested;

    **Source-supported fixtures; execution pending.** Compiler expectations are literal status/receipts/steps in `RMQ/Validation/PackedOptimized.lean:40–62`, cross-checked against source evaluation at `:99–106`. Query literals are checked against `scanWindow`, `:170–174`. Route assertions use Cartesian close positions and the logical reference trace, `:134–158`.

    P compares actual results to independent literals/specification. Q defines expected values from `actual.result` or takes the predecessor as its only oracle. The current checks would lose their pinned literal/specification obligations under Q; the certificate independently connects compact results to `scanWindow`.

26. **`INV-VALIDATION-REACH`**

    > executable validation imports and runs the new semantic layer. A validator for the predecessor implementation is regression evidence only and does not validate the new machine;

    **Source-supported reach; execution pending.** Validator imports the optimization capstone at line 1, builds `compactQueryProgram.toArray` at `:224`, and executes it with `compactQueryBudget` at `:176`. Compiler controls call `compactAt`, `:115–116`. The original program is a comparison object, not the tested machine.

    P executes compact emitted code. Q runs only `queryProgram`. `runQuery`’s compact result and ordered observation checks, plus the explicit optimization imports, identify the actual required layer.

27. **`INV-ALL-SIZE`**

    > exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch;

    **Source-supported.** `compactQueryNat_exact`, `O/QueryProof.lean:101–105`, is universal in `xs,l,r`, returning the scan specification when `V`, otherwise `none`. `compactQueryNat_eq_original`, `:92–99`, uses the same representable-input boundary and actual compact answer. Physical safety is separately guarded by `R`; valid ranges are proved representable.

    P covers every list and endpoint combination through the stated wrapper/physical domains. Q inserts a hidden readiness premise or unproved fallback implementation. `natContract_expectedType`, `O/Consumers.lean:200`, has no readiness premise, and `validInputs_expectedType`, `:188`, pins valid-input representation.

28. **`INV-PROOF-SEPARATION`**

    > proof-only fields never carry answers or uncharged routing information;

    **Source-supported.** The capstone is a `Prop` at `O/Certificate.lean:16`. Execution is fixed independently at `O/Query.lean:26–34`. Initial registers contain only size/endpoints and zeros, `P/Guard.lean:18–22`; proof certificates are not executable parameters.

    P uses proofs to establish properties of independently defined execution. Q supplies a proof-side answer/register function to the actual machine. The present function signatures and the primitive data-flow chain exclude that parameter path. Proof observations in transitions are not counted as machine registers, consistently with `P/Primitive.lean:155–161`.

29. **`INV-NO-SYNTHETIC`**

    > synthetic events, decorative rereads, and post-hoc replay do not support the execution claim;

    **Source-supported.** Read observations are extracted from actual transitions, and compact execution’s ordered attempted reads equal the original source/run at `O/QueryProof.lean:13–38`. Added loop-control instructions have no receipts; the only data-read steps remain ordinary `.load`.

    P relates real primitive execution to source value and trace. Q generates receipts separately after computing a semantic answer. `CompactRealizes`’s `RunsTo` and result agreement, together with the positional public consumer, reject the substituted observation relation. The fixed output-register data flow is additional evidence; trace equality alone would not establish this invariant.

30. **`INV-CATEGORY-SEPARATION`**

    > payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct.

    **Source-supported.** Capacity is word counts times `wordWidth`; steps are transition-list length; categories partition actual instruction categories; finite registers are separately charged. See `O/Certificate.lean:24–27,49–52,73–79` and `P/Primitive.lean:173–201`.

    P makes modeled capacity/operation claims. Q interprets 151978 as elapsed-runtime improvement or 212964 as payload bits. The new prose explicitly disclaims attained cost and native-runtime improvement at `docs/FAMILY_SUMMARY.md:3467–3468` and `docs/DIGESTION_LOG.md:1773–1775`.

31. **`INV-PUBLIC-COMPOSITION`**

    > a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. Conjoining true theorems about different payloads or guarded and unguarded executions is not closure.

    **Source-supported.** The compact certificate uses `D xs`, `compactQueryProgram`, `compactQueryBudget`, `s xs l r`, and `w xs` consistently. Physical result/halt/safety fields share `R`; valid reference/leftmost statements use their explicit `V`/answer domains. Arbitrary-memory completion and observation facts are separate, stronger operational statements.

    P fixes those objects and domains. Q combines canonical safety with execution over another memory, or replaces representable invalid behavior with only valid-query behavior. Fixed result/halt/invalid/safety consumers at `O/Consumers.lean:222–340` spell out the original objects and guards. No unguarded arbitrary-memory safety statement was inferred from the stronger observation theorem.

32. **`INV-CERTIFICATE-ANTI-BYPASS`**

    > every mandatory field advertised by a public certificate is projected by a checked typed consumer at the exact proposition and object arguments required by the acceptance contract. Deleting or weakening a field, or replacing it with a sibling fact, must break that consumer rather than leave only constructor initializers and prose unchanged.

    **Exact source coverage checked; compiled rejection pending.** Every one of the 39 fields has a generic direct projection and canonical consumer in `O/Consumers.lean`. My read-only comparison found **39/39/39** producer/generic/canonical coverage against literal `certificate-replay/FIELDS.json`, with no expected-type discrepancies.

    P is the independently repeated expected proposition and direct projection. Q is a deleted field with its initializer also removed, or a `True` field with `True.intro` initializer. Certificate replay compiles both mutant producers first, then unchanged Consumers, and checks only the selected field’s invalid-field/type-mismatch region at `scripts/packed_optimized_certificate_replay.ps1:160–184,258–270`. This avoids mistaking a broken constructor initializer for consumer sensitivity.

33. **`INV-MUTATION-REPRODUCIBILITY`**

    > when acceptance relies on an exhaustive, production, or public-dependency mutation campaign, the candidate contains a versioned runner or fixtures that replay every claimed case, check the exact expected failure/acceptance surface, restore tracked state, and leave the tree clean. Report prose, copied terminal output, and dangling Git objects are not replayable evidence. A public theorem additionally has a checked exact-type consumer that fails when the advertised dependency is removed; `#print axioms` over the theorem's current type is not such a consumer.

    **Replayable source present; campaign results pending.** Runtime and certificate runners contain exact versioned registries, controls, expected surfaces, selection checks, bounded launches, and restoration records. Certificate fields are protected by a literal SHA256 and expected-type comparison, `scripts/packed_optimized_certificate_replay.ps1:27,91–126`.

    P is executable replay with unchanged consumers and verified expected verdicts/restoration. Q is a transcript, stale artifact, timeout, wrong-field error, or only `#print axioms`. The runner distinguishes these cases and compiles mutant producers before rejecting Consumers. No campaign verdict was taken from withheld prose or fabricated here.

34. **`INV-GLOBAL-PHYSICAL-MACHINE`**

    > a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding.

    **Source-supported for the stated packed primitive machine.** `D xs` is fixed before whole-query execution. The physical reader translates logical spans into the same repacked allocation, including the counted 174-word metadata offset, `P/PhysicalRead.lean:19–36,143–161,166–192`. Whole-query ordered refinement, transition provenance, address fit, and safety are composed into `O/Certificate.lean:83–120`.

    P uses the one supplied data memory throughout the full compact query. Q changes memory between components or proves only the final rank suffix. The whole-run fields and indexed backing consumer reject that object substitution.

    **Scope limit:** This is the existing explicit primitive-machine model with a separate `Program`. Literal code serialization is counted. The source does not newly prove execution by fetching/decoding instructions from one concatenated serialized code-plus-data array, and I have not attributed that stronger claim to OPT-1.

35. **`INV-WIDTH-SCALING`**

    > one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient.

    **Source-supported.** The unchanged declaration is `wordWidth n := 32 + 8 * packedReviewerCellWidth n`, `P/Allocation.lean:23`. The certificate proves
    `log2(n+2)+1 ≤ wordWidth n ≤ 192*(log2(n+2)+1)`,
    at `O/Certificate.lean:20–21`, together with same-width data/address/code/transition/return fit and complete capacity.

    P is that common width and all its operational bounds. Q supplies only a Little-O width fact while omitting the link to actual operands or memory. `widthBounds_expectedType`, `O/Consumers.lean:30`, plus exact safety/capacity consumers fix those links. Endpoint dependence does not enter the width definition.

**Evidence strength and important limits**

The main source chain is:

`querySource.eval`
→ hosted original/compact compiler `RunsTo`
→ adequate complete primitive execution
→ exact arbitrary-memory result and ordered-receipt correspondence
→ canonical query correctness and same-width execution safety
→ literal emitted encoding plus finite bank accounting
→ the 39-field capstone
→ 78 fixed typed consumers.

The branch-sensitive original bound is **150739**; compact loop control yields a different upper bound, **151978**. The compact code reduction is from the original **837572 instructions** to **212964**, with **722339 encoded words**. These are upper-bound and literal-size statements. No attainment, optimality, impossible-smaller-budget, or measured native-speed conclusion follows.

The source explicitly handles zero repeats, initially stopped states, early halt/fault, terminal code exhaustion, and appended halt. Its global safety proof carries full `State.Fits` separately from low-register agreement. This separation is load-bearing and correctly retained.

The inspected Lean declarations are intended tier-1/kernel facts about a tier-2 explicit machine/store model. This lane reconstructed their sources but did not independently elaborate them. Runtime cases would provide tier 3; exact build/campaign receipts provide tier 4. Documentation and this report remain tier 5.

**Rejected objections**

- “The smaller-fuel bound is only the generic fuel bound.” Rejected: `compiled_run_bound_and_fuel_eq` constructs and extends an actual bounded terminal segment; the public theorem bounds the original complete `queryRun`.
- “213038 was only an emitter estimate.” True about the preliminary number, but stale for the target: the actual emitted-length theorem gives 212964.
- “Low-register equivalence is being treated as whole-state fit.” Rejected: the safe relation, follow rule, source-safety transport, and loop proof carry full fit separately.
- “Failed reads or repeated attempts were dropped.” Rejected at the proposition level: equality is of ordered `List Receipt`, including `none`.
- “Compact cost equal to its fuel proves adequacy.” Insufficient in isolation, but the target also supplies universal stopped execution and full equality at every adequate larger fuel, with fixed consumers.
- “A green producer construction alone establishes certificate anti-bypass.” Rejected: the runner preserves consumer bytes and compiles mutant producers before requiring the exact consumer rejection.
- “Every changed read must change the answer.” Not the assigned claim and generally false. The relevant source evidence constrains real value/state flow; the malformed metadata fixture explicitly tests answer change.
- “The matrix still says Open, therefore the proof failed.” Rejected: I did not use frozen status cells as substantive evidence.

**Checks performed and skipped**

Performed:

- Read `AGENTS.md` and `docs/internal/AUDIT_PROTOCOL.md`.
- Ran exact-governance explicit-no-role skill preflight: PASS.
- Extracted all 35 requirements from the initial frozen commit.
- Inspected exact-target source with `git show`, focused symbol searches, and both base deltas.
- Compared the 39 literal field propositions against the producer and all 78 fixed consumers: no discrepancies.
- Ran the prescribed trust-hygiene and `native_decide`/`Lean.ofReduceBool` searches: no matches.
- Ran scoped `git diff --check` over `RMQ`, `scripts`, and `lakefile.toml`, original base to exact target: PASS.
- Confirmed no baseline Packed-source, root-alias, or toolchain changes in the delta.

Skipped by the lane contract:

- Every Lean/Lake process, executable replay, subprocess mutant, axiom-inventory execution, aggregate gate, and tracked report write.
- Exact clean/status certification, owned by the independent execution lane/coordinator.
- Strict claim-drift and strict design-decision execution.
- Prior audit narratives, worker verdicts, and appended matrix evidence.

Initial ad hoc text-comparison attempts had auditor-command escaping errors; after correcting the local read-only comparison, it reported 39 generic and 39 canonical consumers with no discrepancies. Those failed parser attempts are not repository findings.

**Roadmap alignment and next steps**

The source addresses both halves of OPT-1: it tightens the complete original execution theorem and replaces unrolled repeats with actual smaller emitted code, while retaining the original succinct allocation and explicit word model. It preserves additive baseline interfaces and does not hide iteration inside a new primitive.

The next required work is evidence collection on this frozen target: finish the independently scheduled full runtime and certificate campaigns, obtain the exact root/consumer axiom inventory and explicit imports, run the contracted aggregate/prose/design checks once on the final tree, then have the coordinator reconcile all 35 rows. A fresh failure should be diagnosed at its smallest precise surface; this source review supplies no reason for a broad proof rewrite.

Durable report path: **none yet**. This is a chat-only report; persistence remains with the root’s authorized report-writing scope.

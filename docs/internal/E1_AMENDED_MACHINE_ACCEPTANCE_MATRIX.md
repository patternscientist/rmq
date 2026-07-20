# E1 Amended Familiar-Machine Acceptance Matrix (frozen before implementation)

Worker: E1-R4 (branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`,
full SHA `d90b062687fd8e32f5c6f0120bf21f4e56666f4b`, the coordinator-accepted
B4 candidate). Contract source: the E1-R4 delegation prompt (amended E1
target per DD-20260717-C05-001 and `OPTION_B_CHARGED_FRINGE_DESIGN.md`),
`docs/PAPER_MODEL_ADEQUACY.md` charge-policy section, and
`.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`. Requirement
wording below is verbatim from the delegation prompt. Frozen at this commit;
after this commit only evidence, status, and coordinator-approved amendments
may change.

Accepted-route objects the rows refer to (verified in this worktree at
`d90b062`):

- accepted whole-query trace:
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`
  (`RMQ/Core/SuccinctFinalRAM.lean:4337`), readWord-only vocabulary
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
  (`:9479`), cost bound
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
  (`:9216`) with derived literal
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 210`
  (`:8702`); public `SuccinctClassic.queryCost_eq : queryCost = 210`
  [AMENDED 2026-07-19, see AMENDMENT A1 below; both read 207 when this matrix
  was frozen at `d90b062`, and neither has said 207 since `f6000c3`]
  (`RMQ/Core/SuccinctRMQClassic.lean:111`), invalid guard
  `SuccinctClassic.queryCosted_invalid` (`:236`).
- word model: `machineWordBits` (`RMQ/Core/SuccinctRank.lean:38`); reviewer
  width `concreteBPNativeSuccinctRMQReviewerWordBits`.
- chunk caps: 33-per-fringe-window cap identity in
  `ChargedFringeChunks.lean` (`Nat.min (relHi/c + 1) 33` identity on the
  reachable domain, consumed at
  `ChargedFringeChunks.lean:1624-1687`); 8-per-word cap
  `machineWordBits_le_8_mul_bpFringeChunkBits`
  (`ChargedWordChunks.lean:39`) with all-size regime identities in
  `ChargedTableRegime.lean`.
- refuted old target: `E1R3FamiliarMachineTarget` /
  `e1R3FamiliarMachineTarget_obstruction` (commit `7fe5b8b`, branch
  `codex/e1-fully-charged-small-step-machine-r3`; NOT in this tree).
- validator patterns: `RMQ/Validation/SuccinctClassic.lean`,
  `RMQ/Validation/SuccinctClassicCostHarness.lean`; lakefile executables
  `rmq_succinct_classic_validate`, `rmq_succinct_classic_cost_harness`.
- documentary uncharged-omission list to discharge:
  `docs/PAPER_MODEL_ADEQUACY.md` "Events And The Declared Charge Policy"
  (uncharged bullet: dispatch, register moves, decode, bounded
  arithmetic/comparison, option tests, branching, merges, trace assembly,
  validity guard).

EVIDENCE NOTE (added after the freeze; frozen requirement text above is
UNCHANGED, and this note corrects no requirement, only a line anchor).
The accepted whole-query trace anchor above cites
`RMQ/Core/SuccinctFinalRAM.lean:4337`. At HEAD `e90c5d6` that line falls
inside a DOC COMMENT which closes at `:4339`, and the comment documents a
DIFFERENT definition, `concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted`
(`:4340`). The intended object,
`def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`, is at
`:4426`. The FILE PATH in the anchor is correct at this HEAD. Verified
independently at source by M3d-14 and again by M3d-15. Anchor repair inside
frozen text is a coordinator decision and has NOT been made here.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-E1-01 | "Familiar small-step machine: a standard word-RAM instruction semantics — memory read (segment, index -> register), register move/write, integer arithmetic (add/sub, and mul/div-by-constant only if the route needs them — inventory first and record the ISA decision), comparison, conditional branch, halt — over `concreteBPNativeSuccinctRMQReviewerWordBits`-width operands [AMENDED 2026-07-19, see AMENDMENT A2 below; was `machineWordBits`]. Every executed instruction charges exactly one step. No instruction may hide recursion, variable-length scans, table decoding beyond one bounded arithmetic expression, or multi-read composites." | Local | A Lean `inductive` instruction type whose constructors are exactly the familiar repertoire; a step function executing ONE instruction per step with cost 1 charged per executed instruction (checked cost lemma: total steps = executed instruction count); structural audit theorem or definitional shape making per-instruction work non-recursive (the step function is a single non-recursive `match`; only the outer run loop recurses, on a fuel/halt counter); ISA inventory recorded as a DD entry (which arithmetic ops the route needs and why). | The E1 amended target Prop (REQ-E1-07) existentially consumes this machine; chain: instruction type -> step function -> run -> program (REQ-E1-03). | Adversarial: a constructor like `readFringeFold` that folds 33 reads in one step must be impossible to add without failing the certificate — the per-instruction read-event count lemma (each step emits <= 1 memory-read event) and the cost=instruction-count lemma reject multi-read composites; a hidden `List.rec` in the step function rejected by the step function being a single `match` with no recursive call. | SATISFIED. `Instr` (`E1Machine.lean:76`) is an inductive with exactly TWELVE constructors and no others -- `readMem`, `const`, `move`, `add`, `sub`, `mulConst`, `divConst`, `natLt`, `natLe`, `natEq`, `brNZ`, `halt` -- which is the familiar repertoire the row names, with `mulConst`/`divConst` carrying CONSTANT immediates only (ISA inventory recorded DD-20260718-005, `DESIGN_DECISIONS.md:3121`). `execInstr` (`:160`) is a SINGLE non-recursive `match` on the constructor: no arm calls `execInstr`, and only the outer `run` loop recurses, on a fuel counter. `run_steps_eq_catLog_length` (`:340`) is the cost lemma the row asks for -- total steps = executed-instruction count -- and `catCount_partition` (`:296`) partitions that total across the six frozen categories as an EQUALITY. THE ANTI-VACUITY CHALLENGE IS DISCHARGED STRUCTURALLY, AND MORE STRONGLY THAN IT ASKED, WHICH IS RECORDED HERE SO AN AUDITOR DOES NOT SEARCH FOR A MISSING LEMMA. The row demands a "per-instruction read-event count lemma (each step emits <= 1 memory-read event)". NO SUCH NAMED PROPOSITION EXISTS IN THE TREE, and it cannot be stated as a non-trivial claim, because `execInstr` returns `State x Category x Option TraceEvent` (`:160-161`): the event channel is an `Option`, so a step emitting TWO events is UNTYPEABLE rather than merely unproved. The adversarial `readFringeFold` constructor folding 33 reads into one step could not be given a semantics in this signature at all. The bound the row wanted proved is enforced by the type, which is the stronger discharge; and the hidden-`List.rec` half of the challenge is rejected by `execInstr` being a single `match` with no recursive call. | SATISFIED. No residual gap. The absence of the named per-instruction read-count lemma is the discharge and not a hole -- see the evidence cell. |
| REQ-E1-02 | "Constructor-exhaustive address/operand width accounting: every encoded field of every instruction fits the modeled word width, and oversizing any field must break the certificate (a predicate returning True on unhandled constructors fails the row)." | Local | A width-accounting predicate defined by exhaustive `match` on the instruction constructors (no wildcard/default arm returning `True` for operand-carrying constructors), and a checked theorem: every instruction of the concrete program satisfies it at the modeled width for every size; plus an explicit rejection witness: some concrete oversized instruction fails the predicate (kernel-checked `¬ fits`). | Feeds REQ-E1-07 (target Prop conjunct) and INV-ADDRESS-WIDTH. | Replace one constructor arm with `True` — the rejection witness for that constructor's oversized instance must fail, demonstrating the arm is load-bearing; the predicate must range over the operands actually encoded, not a projection that drops fields. | SATISFIED. `wholeQueryProgram_fits_reviewerWordBits` (`E1WholeQueryPathWidth.lean:547`) certifies that every encoded field of every instruction of the program that ACTUALLY EXECUTES fits the modeled width, with NO hypothesis -- no size threshold, no premise about interior, select or composition. It is now proved as the instantiation of a PARAMETRIC theorem, `wholeQueryProgram_fits_of_wordAddressesStructure` (`:512`), at the amended width, and so doubles as the witness that that theorem's model assumption `WordAddressesStructure` (`E1ReviewerWidth.lean:177`) is satisfiable; the assumption is proved non-vacuous by `not_wordAddressesStructure_of_width_le_18` (`E1ReviewerWidth.lean:213`). The parametric form is the SAME mathematics in model vocabulary, not a stronger theorem -- see AMENDMENT A2, which records the extensional equivalence explicitly so that no reader infers new generality. The predicate is `Instr.FieldsFit` (`E1Machine.lean:535`), a `Prop` defined by exhaustive `match` with one arm per constructor, no wildcard and no default-`True` arm; `ProgramFits` (`:552`) lifts it over the program. THE REJECTION WITNESSES ARE ELEVEN, ONE PER OPERAND-CARRYING CONSTRUCTOR, AND EACH IS AIMED AT A DIFFERENT FIELD POSITION (`E1Machine.lean:561-607`): `readMem` segment, `const` value, `move` dst, `add` src1, `sub` src2, `mulConst` k, `divConst` k, `natLt` dst, `natLe` src1, `natEq` src2, `brNZ` target. Because the targeted position differs witness by witness, replacing any single arm with `True` breaks THAT arm's own witness -- which is precisely the row's challenge, discharged constructor by constructor rather than in aggregate. `fieldsFit_rejects_zero_divisor` (`:589`) additionally rejects a zero divisor, so `divConst`'s positivity conjunct is load-bearing rather than assumed away. The twelfth constructor `halt` carries no field and needs no witness. The negative direction is RETAINED, and is the reason AMENDMENT A2 exists: `wholeQueryProgram_not_fits_machineWordBits` (`E1WholeQueryWidth.lean:84`) proves the same executed program does NOT fit the size-indexed width, at small shapes only, because the program is constant-size. See AMENDMENT A2 for why the amended width buys uniformity across all shapes rather than headroom -- both widths are proved logarithmic in the input size by the repository itself. | SATISFIED at the amended width of AMENDMENT A2. No residual gap. |
| REQ-E1-03 | "result agreement — the machine's output equals `(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right).value` (and through it the public `List Int` query) for every valid query" | Local+roadmap | Checked theorem: for every shape/left/right admitted by the accepted route's validity domain, running the concrete program on the machine yields output = `(...GlobalWordTraceResult shape left right).value`; composed corollary through the existing exactness chain to the public `List Int` query answer. Universal quantification, no sampling, no readiness guards. | The amended target Prop; chain: machine run -> program semantics -> accepted trace `.value` -> `SuccinctClassic.queryCosted` -> public `List Int` query. | Q-mutations rejected: agreement only on sampled inputs (statement is universally quantified); agreement of a projection that ignores the packet's index component (statement equates the full value). Value must be computed from machine registers fed by the machine's own reads (INV-VALUE-DEPENDENCY), not copied from the spec trace. | Theorem clauses FULLY MET, universally, to the accepted object and through to the public surface. The target''s valid-path conjunct (`E1AmendedTarget.lean:381-395`) quantifies over ALL `xs : List Int` and ALL `left right : Nat` admitted by `ValidRange` -- no sampling, no readiness guard, no threshold dispatch -- and concludes `decodePacket (final.regs regOut) = (SuccinctClassic.queryCosted xs left right).value`, the FULL packet value rather than a projection that drops the index component, at the canonical store `concreteBPNativeSuccinctRMQGlobalReadStore`. It is discharged by `amendedFamiliarMachineTarget_holds` (`:620`). The composed corollary through to the public `List Int` query answer is `programSkeleton_valid_matches_public` (`E1WholeQueryPublic.lean:140`). RESIDUAL GAP -- INV-VALUE-DEPENDENCY AT WHOLE-QUERY SCOPE. The invariant demands that corrupting a read value on a witness input CHANGE THE MACHINE OUTPUT. The validator''s phase 3l/4k (`E1MachineValidate.lean:2194`) is the tree''s only executed store-perturbation witness, and it is ARM-SCOPED, not whole-query: it perturbs `E1FringeArmProgram.armWitnessStore` and observes the fringe-arm registers `E1FringeArmBlock.fRV`/`fRP`, NOT `regOut` of `wholeQueryProgram` at the canonical store. So value dependency is demonstrated OF AN ARM, not of the query answer. This is a harness gap at whole-query scope, not a defect in the theorem clauses above, and it is the one thing standing between this row and the status its clauses would otherwise carry. | PARTIAL. Theorem clauses met universally and carried through to the public surface; INV-VALUE-DEPENDENCY is not witnessed at whole-query scope, phase 3l being arm-scoped. |
| REQ-E1-04 | "receipt projection — the ordered sequence of memory-read events the machine performs is POSITIONALLY EQUAL to the accepted trace `(...).trace` (same segments, indices, values)" | Local+roadmap | Checked theorem: the machine execution's ordered read-event projection (list of (segment, index, word?) in execution order) = `(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right).trace` mapped through the readWord shape, as a POSITIONAL list equality (not multiset/membership), for every valid query. | The amended target Prop; chain: machine read log -> projection -> accepted trace; consumes `_readWord_only` to state the projection totally. | Positional equality rejects: permuted logs, deduplicated repeated reads (the B4 repeated-read receipts require multiplicity), appended decorative reads. Evidence must be `List` equality, not `∀ e, e ∈ log ↔ e ∈ trace`. | SATISFIED, AND BY A MECHANISM STRONGER THAN THE LEMMA THE ROW ASKED FOR. Positional receipt equality is not a separate theorem that a later edit could quietly weaken to membership: it is THE RECEIPT ARGUMENT OF `RunsTo` ITSELF (`E1MachineCalculus.lean:96`), the exact-fuel big-step relation in which every E1 simulation in this tree is stated. `RunsTo store program s s'' reads cats` carries `reads` as a `List TraceEvent` positionally, and there is no formulation of a run in this calculus that records reads as a set or a multiset -- so the row''s demand for `List` equality rather than `forall e, e IN log <-> e IN trace` cannot be satisfied accidentally, and cannot be relaxed without rewriting the calculus. The whole-query instance is the target''s own conjunct (`E1AmendedTarget.lean:384-392`): the `RunsTo` application whose receipt argument is literally `(SuccinctClassic.queryTraceResult xs left right).trace` (`:390`), for every `xs`/`left`/`right` satisfying `ValidRange`, discharged by `amendedFamiliarMachineTarget_holds` (`:620`). Permuted logs, deduplicated repeated reads and appended decorative reads are each rejected by positional `List` equality; the B4 repeated-read receipts, which require multiplicity, survive because order and multiplicity are preserved by construction rather than by a side lemma. | SATISFIED. No residual gap. |
| REQ-E1-05 | "invalid guard — empty/reversed/out-of-bounds inputs produce the guarded none-packet with empty read projection and zero cost, matching `SuccinctClassic.queryCosted_invalid` semantics" | Local | Checked theorem(s): for invalid ranges (left >= right or right > n), the machine run halts with the none/guarded output, its read projection = `[]`, and its charged step total for the memory-read category = 0 with the overall guarded cost matching the accepted invalid semantics; exercised on empty, reversed, and out-of-bounds fixtures in Lean examples and in the validator. | Public guard parity with `SuccinctClassic.queryCosted_invalid`; chain: machine guard branch -> none packet -> public invalid semantics. | The guard must be computed by machine comparisons on the query operands (charged steps), not a meta-level `if` outside the machine; an unguarded machine wrapped in a Lean-level guard fails the row. | SATISFIED. `amendedTarget_invalidGuard` (`E1AmendedTarget.lean:529`) discharges the target''s INVALID conjunct for ALL `store` and all `xs` -- the guard''s behaviour does not depend on the store, which is exactly right for a guard that must reject BEFORE reading -- and its conclusion is the row''s three-part demand at once (`:375-379`): the guarded none-packet output, `([] : List TraceEvent) = (SuccinctClassic.queryTraceResult xs left right).trace` for the empty read projection, and `catCount (guardRejectCats left right) Category.memoryRead = (SuccinctClassic.queryCosted xs left right).cost` for the charge. Public parity is `programSkeleton_invalid_matches_public_guard` (`E1QueryBridge.lean:55`), matching `SuccinctClassic.queryCosted_invalid` semantics. THE GUARD IS CHARGED MACHINE WORK, NOT A LEAN-LEVEL `if`, WHICH IS THE ROW''S NAMED FAILURE MODE. `guardBlock` (`E1QueryProgram.lean:110`) is EIGHT executed machine instructions -- `const`, `const`, `natLt`, `natLe`, `natEq`, `brNZ`, `natEq`, `brNZ` (`guardBlock_length = 8`, `:120`) -- so `left < right` and `right <= n` are decided by machine comparisons on the input registers and rejection is charged in the frozen categories; an unguarded machine wrapped in a Lean-level guard is excluded by construction. EXERCISED, not only proved: the validator runs empty, reversed and out-of-bounds fixtures, and its guard phase is gated on `gAccepted > 0` (`E1MachineValidate.lean:3475`), so a reject-everything machine -- which would satisfy every other check in that phase -- scores zero and FAILS rather than passing vacuously. | SATISFIED. No residual gap. |
| REQ-E1-06 | "Fully charged cost correspondence: total machine steps = sum of explicit category counts (controller/dispatch, decode/arithmetic, comparison/branch, memory reads, register writes — choose and freeze the categories); memory-read count = accepted trace length (<= 210 by the existing bound) [AMENDED 2026-07-19, see AMENDMENT A1 below; was 207]; a DERIVED literal all-size total step bound (never asserted; expect low thousands — whatever derives, derives)." | Local | Frozen category choice recorded (DD); checked theorems: (a) total steps = sum over the frozen categories of per-category counts (an accounting identity over the machine log); (b) the memory-read category count = accepted trace length for every valid query (hence <= 207 via the existing bound); (c) an all-size literal `totalSteps <= <literal>` derived by `rfl`/omega from the per-phase algebra, no size hypothesis. The literal is whatever the derivation produces; it is never asserted against an independent numeral first. | The amended target Prop conjuncts; chain: step log -> category partition -> read category = trace length -> 207 bound; total <= derived literal. | Mutating a phase constant must break the `_eq` derivation (pattern: B2's REQ-B2-15 challenge); a category partition that double-counts or omits steps is rejected by the accounting identity being an equality, not <=; the read-category theorem must equate to the ACCEPTED trace length, not to an independent count. | SATISFIED, on all three conjuncts, AND THE RESIDUAL GAP THIS ROW''S OWN STATUS CELL RECORDED IS STRUCK -- see the status cell. (a) THE ACCOUNTING IDENTITY: `catCount_partition` (`E1Machine.lean:296`) sums the six frozen categories to `log.length` as an EQUALITY, not a `<=`, so a partition that double-counts or omits a step is rejected by the statement''s shape; `run_steps_eq_catLog_length` (`:340`) ties that length to executed steps. (b) THE READ CATEGORY IS EQUATED TO THE ROUTE'S OWN TRACE, not to an independent count: it is the same `RunsTo` receipt argument REQ-E1-04 records, with the memoryRead charge equated to `(SuccinctClassic.queryCosted xs left right).cost` in the target''s valid-path conjunct (`E1AmendedTarget.lean:397-400`). (c) THE DERIVED ALL-SIZE LITERAL EXISTS: `wholeQueryCats_machineS_length_le` (`E1WholeQueryCostLiteral.lean:538`) proves the whole-query category log has length `<= 11886`, taking only `shape`, `left` and `right` and carrying NO SIZE HYPOTHESIS. The literal was summed by `omega` from the per-phase algebra (`11886 = 9 + 729 + 2 + 729 + 10179 + 2 + 234 + 2`, `:485`), never asserted against an independent numeral first; `wholeQueryStepBound_isTheProvedBound` (`E1MachineValidate.lean:2591`) pins the validator''s printed bound to that theorem, so the harness cannot drift from the proof. ANTI-VACUITY BY EXECUTION AGAINST THIS ROW''S OWN CHALLENGE: MUTANT L (`E1MachineValidate.lean:2381-2440`) moves ONE charge from `registerWrite` to `arithmetic`, preserving value, position, full receipt, preservation, exit pc, modeled steps, catLog LENGTH and memoryRead charge -- `mutantL_isCategoryOnly` checks that case for case -- and is caught ONLY by the positional category log (`mutantL_catLogMismatches > 0`), the single discriminator with any power over it. | SATISFIED. THE RESIDUAL GAP PREVIOUSLY RECORDED IN THIS CELL IS STRUCK, BECAUSE ITS MECHANISM NO LONGER EXISTS. That gap held that the interior leg computes `Nat.log2 count` / `bpSparseLogSpan count` in a loop with no literal all-size iteration cap, contradicting conjunct (c). B7 replaced that mechanism with a count-indexed charged table whose cell packs level and span, read once and unpacked by constant-divisor `div`/`mod` (`bpSparseLevelCell_div`/`_mod`, `SparseLevelTable.lean:78`/`:90`); no executed definition mentions `Nat.log2`. The decisive evidence is not the narrative but the SHAPE OF THE THEOREM: `wholeQueryCats_machineS_length_le` carries NO size hypothesis, WHICH COULD NOT BE TRUE IF THE UNCAPPED LOOP WERE STILL LIVE. The M3d-11 status correction below anticipated this and offered it for adjudication; it is now adjudicated and applied. FLAGGED, NOT EDITED -- a residual staleness in this row''s FROZEN `Evidence needed` cell, which still reads "hence <= 207". AMENDMENT A1 amended only the three occurrences it enumerates and did not reach this fourth one; the live bound is `210`. Editing frozen requirement text is outside this lane''s authority, so it is flagged here for a coordinator rather than corrected. |
| REQ-E1-07 | "state the amended target Prop (`E1AmendedFamiliarMachineTarget` or similar), prove it via your construction, and add a short design-decision + doc note relating it to the refuted `E1R3FamiliarMachineTarget`: the old target's per-position clause is now satisfied VACUOUSLY-FREE (the route has no per-position scan; the chunk loop is charged per iteration with a literal iteration cap) — make the relationship precise, do not hand-wave." | Local+roadmap | An explicit Prop bundling: existence of a machine + program with one-step-per-instruction charging, width accounting, result agreement, positional receipt projection, invalid guard, category accounting, and the derived literal bound; a checked theorem proving it by exhibiting the construction; a DD entry + doc note stating precisely which clause of the refuted R3 target failed (the unbounded event-silent scan made the per-position charge bound unsatisfiable) and why the amended route eliminates the clause's domain (no per-position scan exists; every loop is a chunk fold with literal cap 33/8, each iteration charged as one read + bounded register steps). | Roadmap join: E1 rung closure feeding A07 blind audit; supersession note consumed by `docs/PAPER_MODEL_ADEQUACY.md` and DESIGN_DECISIONS. | The Prop must quantify like the public claims (all shapes/sizes, all valid queries), not a singleton demo; the supersession note must cite the exact obstruction identifier and commit, and must NOT claim the old target is proved — it is superseded; conflating refutation-of-old with proof-of-new fails the row. | SATISFIED. `amendedFamiliarMachineTarget_holds` (`E1AmendedTarget.lean:620`) is the checked theorem discharging the amended target Prop by EXHIBITING the construction, and the Prop bundles all seven items the row demands -- machine and program, one-step-per-instruction charging, width accounting, result agreement, positional receipt projection, invalid guard, category accounting, and the derived literal -- instantiated at `wholeQueryMachineS 11886` (`:624`) from `wholeQueryCats_machineS_length_le` (`:626`). The width conjunct (3) is at `:432-436`, added only once `wholeQueryProgram_fits_reviewerWordBits` supplied the positive direction unconditionally (DD-20260719-304, cited at `:430`); before that the sole width fact about the executed program was a REFUTATION, and the conjunct was honestly OMITTED rather than weakened to something provable. THE QUANTIFICATION IS THE PUBLIC ONE, NOT A SINGLETON DEMO, and the spelling is load-bearing: the machine and program binders sit OUTSIDE the `xs` quantification as functions (`:60-64`), asserting ONE uniform construction that every input is run against; moving the existential inside would assert only that each input has SOME program, which would have been easier to prove and would not have been the claim. "ONE-STEP-PER-INSTRUCTION CHARGING" APPEARS AS NO SYNTACTIC CONJUNCT, AND THAT IS CORRECT RATHER THAN MISSING -- recorded so an auditor does not read its absence as an omission: it is DEFINITIONAL in `RunsTo` (`E1MachineCalculus.lean:96`), whose category list emits exactly one entry per executed instruction, so every conjunct stated in terms of `RunsTo` already carries it. The supersession note is at `E1AmendedTarget.lean:66-162` with DD-20260719-245 (`DESIGN_DECISIONS.md:8298`); it cites the exact obstruction identifier and commit -- `e1R3FamiliarMachineTarget_obstruction`, commit `7fe5b8b`, `RMQ/Core/SuccinctFinalSmallStep.lean:37016`/`:37046` -- and states that the old target is SUPERSEDED, not proved. | SATISFIED. No residual gap. The note's "every loop is a chunk fold under a literal cap" wording is TRUE only post-B7, and it ships with the B7 dependency explicit and the two distinct `33`/`8` literals disambiguated at `E1AmendedTarget.lean:155-162` -- see also the M3d-11 and M3d-12 notes below. |
| REQ-E1-08 | "Production validator (INV-VALIDATION-REACH): an executable (lakefile target) that RUNS the machine on deterministic fixtures — empty, singleton, size-two, same-block, threshold-boundary, cross-interior, invalid, plus generated cases — comparing against an independent half-open leftmost `List Int` reference implementation (write the expected values independently, not from the machine); checks result/read-projection/step-count correspondence and no-synthetic receipts; and includes at least one deliberate machine mutation that the validator verifiably rejects. Report modeled steps separately from wall-clock." | Local | A new `lean_exe` lakefile target; validator source following `Validation/` patterns; fixture list covering the named cases + generated cases; an independent reference RMQ (naive half-open leftmost scan over `List Int`, written directly against the semantics, not calling the machine or the succinct route); checks: machine result = reference result, machine read projection = accepted trace, machine step totals = category sums, machine literal bound honored, mutation rejected (exit-code-visible failure on the mutated machine, un-mutated run green); output separates modeled step counts from wall-clock ms. | INV-VALIDATION-REACH; chain: compiled validator -> machine `run` -> comparisons -> process exit code. | The mutation must be in the MACHINE (program or step semantics variant), not in the fixtures; the reference implementation must not import the machine or succinct modules' answers (independence audit: it may share only `List Int` and basic prelude); a validator that derives expected values by calling the machine passes trivially and fails the row. | Extensive, and largely EXECUTED rather than only proved. The `lean_exe` target is `rmq_e1_machine_validate` (`lakefile.toml:41`, root `RMQ.Validation.E1MachineValidate`). PHASE 5 IS NO LONGER A HOLE: it runs 24 whole-query cases (`wholeQueryCases`, `E1MachineValidate.lean:2664-2688`) covering every fixture class the row names -- empty, singleton, size-two, same-block, threshold-boundary, cross-adjacent, cross-interior, select-miss, invalid, plus generated (`gen-6-1`, `gen-9-2`) -- with the classes COMPUTED from the route''s own closes rather than declared, and `wholeQueryClassesAllPopulated` failing the run if any named class has no members. Expected values come from `refRMQ` (`:78`), a naive half-open leftmost scan written from the SPECIFICATION, with expectations computed before any machine run. `wholeQueryComparisonAvailable` (`:2821`) is now DERIVED from the corpus -- `wholeQueryCases.length > 0` together with the report count matching -- replacing a hand-written status string that had gone stale repeatedly; and phase 5 GATES THE EXIT CODE, through `okWholeQuery` (`:3507`) into `okNewDiscriminators` (`:3521`) into `ok` (`:3524`) and the process return at `:3529`. Eleven-plus machine mutants are executed and COMPLEMENTARY, each rejected by a discriminator the others lack: D value-only, E receipt-only, G preservation-only, K exit-invisible, L category-only, M whole-query value-only. **CORRECTION 2026-07-20: M''s "whole-query value-only" label is WRONG and is retained here only so the correction is legible.** M (`natLt` -> `natLe` throughout the whole-query program) was labelled value-only on the assumption that the value comparison is what catches it. MEASURED at REQ-E1-08''s new positional receipt diff: the VALUE comparison catches M on **12 of 24** cases, while the POSITIONAL RECEIPT catches it on **20 of 20** comparable cases -- eight cases the value cannot see at all, because relaxing `<` to `<=` re-routes control through read-bearing code even where the returned answer coincides. So the receipt does not merely complement the value on M, it **strictly outranks** it, and the discriminator taxonomy understated the receipt''s power rather than overstating it. Modeled steps are reported separately from wall-clock throughout, with the wall-clock line explicitly labelled "NOT evidence". TWO GAPS, BOTH NAMED PRECISELY RATHER THAN ARGUED AWAY. (a) NO WHOLE-QUERY RECEIPT DIFF: `WQReport` (`:2691-2704`) carries `reads : Nat`, a COUNT, so at whole-query scope the receipt is counted and never compared event-by-event against the route''s `.trace` -- unlike phase 3d, which diffs positionally at composite scope. This is a HARNESS gap, not a proof gap: the positional theorem exists (REQ-E1-04); it is simply not the thing phase 5 checks. (b) THE INDEPENDENCE CLAUSE FAILS ITS LITERAL WORDING: the row requires the reference implementation to "not import the machine or succinct modules'' answers", sharing "only `List Int` and basic prelude". `refRMQ` is FUNCTIONALLY independent -- it calls neither the machine nor the succinct route, and its expectations are computed from itself alone -- but it is DEFINED IN `E1MachineValidate.lean`, the same module that imports the machine. On the literal reading the clause fails; on the substantive reading it passes. Recorded as a gap. | PARTIAL. Validator built, executed, and gating the exit code across 24 whole-query cases with complementary mutants; two gaps remain -- no whole-query positional receipt diff (a harness gap, not a proof gap, since the theorem exists), and the reference implementation shares a module with the machine imports so the independence clause fails its literal wording. |
| REQ-E1-09 | "This discharges, at machine level, the 'documentary uncharged omissions' list in PAPER_MODEL_ADEQUACY.md — after this rung that list should be empty or reduced to an explicitly-argued residue; update the doc section accordingly." Plus the bookkeeping: "fix the four stale 'fresh segment 21' public surfaces (`README.md:94`, `docs/WHAT_IS_PROVED.md:14` and `:95`, `artifact/CLAIMS.md:68`, `docs/PAPER_MAIN_THEOREM.md:60` — the checked counterfactual is segment 23 since B3); fix the 33-cap file attribution in `PAPER_MODEL_ADEQUACY.md`; clean the unused-simp-arg warnings at `SuccinctFinalRAM.lean:5694-5824` if cheap (warnings only — skip if it risks churn)." | Public surface | Doc edits: PAPER_MODEL_ADEQUACY charge-policy section updated to state that the E1 machine now charges each enumerated uncharged item, with any residue explicitly argued; stale segment-21 doc lines corrected to segment 23 (checked object: `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.segment = 23`, `SuccinctFinalRAM.lean:6788`); 33-cap attribution corrected (33-cap identity lives in `ChargedFringeChunks.lean`; `ChargedWordChunks.lean`/`ChargedTableRegime.lean` carry the 8-per-word cap and regime identities); simp-arg warnings cleaned or explicitly skipped with reason. `claim_drift_scan.ps1` + `paper_topology_lint.ps1` exit 0. | Public doc surface; chain: machine theorems -> adequacy doc claims. | Doc text must not overclaim: the machine is a refinement target, not a wall-clock claim (framing preserved); the uncharged-list update must cite the actual checked machine theorems, not aspirational ones. | BOOKKEEPING ITEMS DONE; THE PRIMARY DELIVERABLE IS NOT STARTED. The stale segment-21 public surfaces are corrected to segment 23, and the 33-cap file attribution is correct -- the 33-per-fringe-window cap identity is attributed to `ChargedFringeChunks.lean`, with `ChargedWordChunks.lean`/`ChargedTableRegime.lean` carrying the 8-per-word cap and the regime identities, as this matrix''s own accepted-route block records. THE UNCHARGED-OMISSIONS LIST IS UNCHANGED. `docs/PAPER_MODEL_ADEQUACY.md:142-145` still lists "instruction dispatch, register moves, fixed-width decode of a fetched word into register values (mixed-radix unpack of a table entry), bounded arithmetic/comparison on register values, option tests, branching, candidate merges, trace assembly, and the validity guard" as Uncharged -- which is the exact list this rung was raised to discharge, and every item of which the E1 machine now charges as an executed instruction in a frozen category. WORSE, THE DOC ASSERTS IN THE FUTURE TENSE WHAT THE TREE HAS ALREADY DONE. `:263-268` reads that the E1 machine "will define the richer instruction semantics that individually charges every controller, decode, arithmetic, comparison, branch, and register step, and prove a separate literal total; until then these omissions are documentary and enumerated here". `:386-387` reads "E1 must define its richer instruction semantics and prove a simulation separately." Both are public-facing, and both now contradict the tree''s headline result (`amendedFamiliarMachineTarget_holds`, with the derived literal `11886`) -- a public document contradicting a checked theorem in its own repository is a worse state than an un-updated one. TEN STALE `207` NUMERALS REMAIN, in exactly the two files AMENDMENT A1''s scope note flagged as owed to this row: `README.md:70`, `:76`, `:140`, `:334`, and `docs/FAMILY_SUMMARY.md:9`, `:43`, `:48`, `:133`, `:446`, `:1041`. `FAMILY_SUMMARY.md:9` is DOUBLY stale -- `2 * select35 + (2 * rank11 + 2 * endpointFringe37 + interior30) + rank11 = 207` carries both the pre-B7 `interior30`, now `33`, and the retired `207`, now `210`. None of these is caught by a gate: `CLAIM_DRIFT_POLICY.json` carries no `207`/`210` term, and `paper_topology_lint.ps1` anchors on identifiers rather than prose numerals. | NOT SATISFIED. Segment-23 and 33-cap items are done; the primary deliverable -- the PAPER_MODEL_ADEQUACY uncharged-list update -- is not started, that document still asserts in the future tense that E1 "will"/"must" define the machine, and ten stale `207` numerals remain across `README.md` and `docs/FAMILY_SUMMARY.md`. |
| REQ-E1-10 | Process: "freeze a NEW acceptance matrix ... FIRST in its own commit"; "Maintain `docs/internal/E1_WORKLOG.md` per milestone; DD entries for ISA/encoding/program-representation choices; never yield with uncommitted work unless a committed recovery patch is refreshed first (`git diff > docs/internal/E1_WIP.patch`, commit it, delete when superseded)." | Process | Git history: this matrix commit precedes all E1 implementation commits; worklog updated at each milestone commit; DD entries exist for ISA choice, instruction encoding, and program representation; recovery-patch discipline followed on any yield with uncommitted work. | Coordinator audit of branch history. | `git log` order check at final report. | SATISFIED. MATRIX-FIRST ORDER VERIFIED BY GIT RATHER THAN BY NARRATIVE: `git merge-base --is-ancestor 702cfbe 11b8cf9` returns true, so the commit freezing this matrix is an ancestor of the E1 implementation commit, which is the ordering the row demands. DD entries exist for each decision the row enumerates: `DESIGN_DECISIONS.md:3121` (DD-20260718-005, the amended-machine ISA and instruction-encoding decision -- which arithmetic operations the route needs and why, with `mulConst`/`divConst` restricted to constant immediates) and `:3178` (DD-20260718-006, the query register map, output packet convention and guard/exit program skeleton, completing the program-representation decision DD-20260718-005 explicitly deferred). `docs/internal/E1_WORKLOG.md` is maintained per milestone. RECOVERY-PATCH DISCIPLINE: no `docs/internal/E1_WIP.patch` is present, and THAT IS THE CORRECT END STATE RATHER THAN A MISSING ARTIFACT -- the row requires the patch to be refreshed and committed on a yield with uncommitted work and DELETED when superseded, so its absence at a clean tree is compliance. Recorded explicitly because an auditor could otherwise read the absence the wrong way. | SATISFIED. No residual gap. |
| REQ-E1-11 | "RULES (standing): no sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib; library green at every commit; no weakened closed B2/B3/B4 rows; no renamed/deleted frozen public identities; no asserted constants; no dead sources; no sibling public query; the machine is a refinement target, not a wall-clock claim — keep that framing in all docs." | Inherited hygiene + process | Per-commit `lake build RMQ` (or full-root equivalent) green, recorded in the worklog ledger; hygiene `rg` shows no NEW hits in touched files; no closed B2/B3/B4 matrix row weakened (their theorem statements untouched or only strengthened); frozen public identities preserved; all literals derived; the machine consumes the accepted route rather than defining a sibling public query surface. | All touched modules; coordinator audit. | Deliberate check: the E1 machine module must not export a second `query`-shaped public surface competing with `SuccinctClassic.query`; docs framing check for wall-clock claims. | HYGIENE CLEAN. CHK-E1-02''s pattern over `RMQ`, `RMQExamples` and `lakefile.toml` returns NINE hits and ZERO declarations: every hit is the word `partial`, `axiom` or `opaque` occurring in PROSE inside a comment or docstring -- `ReviewerPhysical.lean:2269` ("partial sums"), `E1InteriorChunkFold.lean:181` ("partial-chunk indicator"), `E1WholeQueryPublic.lean:25` ("not an axiom"), and six "opaque to `omega`" notes at `E1CrossBlockArm.lean:475`, `E1FringeArmProgram.lean:211`, `E1InteriorCombine.lean:373` and `:648`, `E1WholeQueryLcaLeg.lean:31`, `E1WholeQueryPathWidth.lean:362`. No `sorry`, `admit`, `unsafe`, `implemented_by` or `extern`, and no `import Mathlib`. (The narrower REQ-E1-11 pattern, which omits `opaque` and `noncomputable`, returns three of those nine.) `native_decide` and `Lean.ofReduceBool`: ZERO hits tree-wide. NO SIBLING PUBLIC QUERY SURFACE: `RMQ/Core/WordRAM/` defines no `query`-shaped public definition competing with `SuccinctClassic.query`; the machine CONSUMES the accepted route (`programSkeleton_valid_matches_public`, `E1WholeQueryPublic.lean:140`). Literals are derived rather than asserted: `11886` is summed by `omega` from the per-phase algebra, and `210` comes from the route''s own cost chain. THE CROSS-MATRIX AUDIT HAS NOW BEEN PERFORMED (2026-07-20, read-only lane at `847a08b`), AND THE NON-WEAKENING CLAUSE HOLDS ON PER-ROW EVIDENCE RATHER THAN ASSERTION. SCOPE CORRECTION FIRST: there are no standalone B3 or B4 matrix FILES -- they are continuation sections of `B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` (B2-01 rows `:49-72`, B2-02 `:126-132`, B3 `:212-240`, B4 `:371-392`), 82 rows, every one `Closed`. RESULT: 82 rows enumerated individually by frozen ID, **0 weakened, 0 falsified, 11 stale-wording, 71 unaffected.** Constant identities were verified BEFORE adjudication and both conflation hazards were real: the moved interior charged cap is `InteriorDirectory.lean:1934` (`30 -> 33`), while the FRINGE `33` at `ChargedFringeChunks.lean:1647`/`:1665` did NOT move -- five closed rows (REQ-B2-03, REQ-B2-10, INV-ALL-SIZE, REQ-B3-02, INV-B3-ALL-SIZE) are written to the at-risk "33" shorthand and were explicitly cleared as referring to the fringe cap. Rows stated against frozen HISTORICAL constants (`207` at `SuccinctFinalRAM.lean:8962`, `142`, `76`) are not weakened by a live constant moving -- that is precisely why those were pinned to literals -- so the `30` appearing in REQ-B2-15 and REQ-B3-09 remains CORRECT rather than broken. TWO CANDIDATE P0s WERE CHASED AND BOTH CLEARED: (i) `...announced_slack_of_size_ge_four_of_bounded` was DELETED, not weakened (its `route <= 30` conjunct is now false, `InteriorDirectory.lean:5541-5555`), and a scan of all 82 rows finds ZERO depending on it; (ii) `..._cost_le_thirty_of_size_ge_four_of_bounded` (`:5529`) and its WithStore twin (`:5637`) keep "thirty" in the NAME but are stated against the cap FIELD, not a literal, so they still hold at 33 -- stale names only. TWO FINDINGS BEYOND THE ROW''S OWN CHARTER: (1) **the residual-gap text above was INCOMPLETE -- B7 moved THREE constants, not two.** Commit `c45e62c` also moved `canonicalRelativeRmmInteriorQueryCost` `240 -> 264` (`InteriorDirectory.lean:1915`), carrying `canonicalTransitionalQueryCost` `328 -> 352` (`SuccinctRMQClassic.lean:147-148`). Four in-scope rows are stated against `328` (REQ-B2-15, REQ-B3-04, REQ-B3-09, REQ-B4-07); all are STALE, none asserts "the transitional constant equals 328" as its own proposition, so none is weakened. Unlike `207`, **no frozen historical `328` was minted** and `328` appears nowhere in the Lean sources. (2) A FALSE PROPOSITION WAS FOUND ON PUBLIC HEADLINE SURFACE and has been REPAIRED: `RMQCompatibility.lean:85` docstringed `succinctRMQCompatibility328QueryCostEq` as "computes to `328`" while the underlying `...CanonicalTransitionalQueryCost_eq` proves `= 352` (`SuccinctFinalRAM.lean:9729-9734`). The frozen public NAME was preserved and only the docstring corrected, now recording why name and value differ. The migrated claim-drift pattern would not have caught it, which is consistent with the standing finding that no gate scans `RMQ/`. | SATISFIED. Hygiene, `native_decide`, sibling-surface and derived-literal clauses were already clean; the cross-matrix "no closed B2/B3/B4 row weakened" audit has now been run per-row over all 82 closed rows and found none weakened or falsified. Residual is documentation only: 11 stale-wording rows, and the row''s own residual text understated B7 by one constant. |

## Inherited invariants (applicable subset, per COMPLETION_GATE.md)

| ID | Application to this rung | Status |
| --- | --- | --- |
| INV-VALUE-DEPENDENCY | The machine's output register value must be computed from its own charged memory reads through the step semantics; corruption of a read value on a witness input must change the machine output (conclusion about the returned value, not the log). | Open |
| INV-TRACE-EXECUTION | The machine's read log and step log are derived from the run function on the concrete program, not assembled post hoc. | Open |
| INV-NO-SYNTHETIC | No cost-only/synthetic steps: every charged step is an executed instruction of the run; the receipt projection contains exactly the reads the run performed (no decorative or replayed reads). | Open |
| INV-ADDRESS-WIDTH | Every executed address/operand (including guard comparisons and dead branches) fits the modeled word width via REQ-E1-02's exhaustive predicate. | Open |
| INV-ALL-SIZE | All theorems quantified over all shapes/sizes and valid queries; no readiness/threshold dispatch in the machine or program generator. | Open |
| INV-CATEGORY-SEPARATION | Machine state/steps, accepted-route model ticks, Lean runtime, and wall-clock remain distinct; validator reports modeled steps separately from wall-clock. | Open |
| INV-VALIDATION-REACH | See REQ-E1-08. | Open |

## Verification battery (CHK rows)

| ID | Command | Status |
| --- | --- | --- |
| CHK-E1-01 | `lake build RMQ RMQPaper RMQExamples` + validator executable run (final battery; targeted `lake env lean` while iterating; mutex `Global\RMQHeavyVerification` for >5 min). | Open |
| CHK-E1-02 | Hygiene `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples lakefile.toml` — no NEW hits; `rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples`. | Open |
| CHK-E1-03 | Cost harness executable run. | Open |
| CHK-E1-04 | `git diff --check` and `git diff --check d90b062..HEAD`. | Open |
| CHK-E1-05 | `design_decision_check.ps1 -Strict -Base d90b062687fd8e32f5c6f0120bf21f4e56666f4b`. | Open |
| CHK-E1-06 | `claim_drift_scan.ps1`; `paper_topology_lint.ps1`. (gate.ps1 explicitly NOT run per delegation.) | Open |

## READ THIS BEFORE THE DATED EVIDENCE NOTES BELOW (added 2026-07-19, E1-LaneP)

The dated per-milestone notes that follow (M3d-11 through M3d-17) are the
historical record of what each lane reported at the time, and they are
retained **unedited**. Several of them close an item with the disclaimer
"Does NOT discharge the row (whole-query scope)", and the M3d-12 and M3d-13
headers state that closure was "impossible by construction" because "every
row is whole-query scoped".

**THAT FRAMING WAS FALSE, AND IT IS WITHDRAWN.** Rows are not whole-query
scoped. This matrix's own `Scope` column reads `Local`, `Local+roadmap`,
`Public surface` or `Process`, and it classifies **where the work lands**,
not how large the claim is. The disclaimer was inherited from lane to lane
without re-examination, and its effect was that an auditor reading the
matrix would conclude nothing had closed, in a tree where seven rows are
satisfied.

Every occurrence has been deleted from the live `Evidence obtained` and
`Status / residual gap` cells in the table above, which are the cells that
carry current status. The occurrences remaining below are inside dated,
attributed worker reports; they are left in place because rewriting another
lane's record is not this lane's to do, and because the headers above them
already mark them as point-in-time notes. **Read them as history, not as
current status.** Current status is the table. See DD-20260719-320.

## M3d-11 evidence note (worker E1-R4t) — no row closed, no row weakened

Added at commit `3811920`. All eleven rows REQ-E1-01..11 remain **Open**.
This note records component-level evidence and one status correction; it
amends no requirement wording.

Component-level evidence added, all in
`RMQ/Core/WordRAM/E1InteriorReadBlock.lean`:

- **REQ-E1-01** — `interiorReadNat:107`, seven instructions, every one an
  atomic constructor, exactly ONE `readMem`, no multi-read composite. The
  route's `i < entries.length` guard is decided BY THE MACHINE (`natLt` at
  `Q+1` on the machine's own index register, branched at `Q+4`), not by a
  Lean-level `if` around the block, so the dead-address path is a charged
  path. ISA decision recorded DD-20260719-002. Does NOT discharge the row
  (whole-query scope).
- **REQ-E1-02** — `interiorReadNat_fits:175`, constructor-exhaustive over all
  seven instructions, no wildcard arm; no divisor, hence no positivity side
  condition. Does NOT discharge the row.
- **REQ-E1-04** — `interiorReadNat_route_atom:443`: the route's own adapter
  (`FixedWidthNatTable.machineReadComputationAt`,
  `MachineChunkedTableProgram.lean:343`), at one chunk, emits a ONE-EVENT
  trace at exactly the address the block reads, and the block's receipt is
  syntactically that trace — a POSITIONAL `List` equality for one interior
  read. Does NOT discharge the row.
- **REQ-E1-06** — `interiorReadNatCats:133` is a FUNCTION of the route-side
  validity condition (six steps live, seven dead), never a numeral;
  `interiorReadNatCats_memoryRead_count:151` fixes exactly one charged read
  on either path, matching `machineReadCostedWithStore_cost`. No literal
  total derived. Does NOT discharge the row.

### STATUS CORRECTION to REQ-E1-06's recorded residual gap

The residual gap recorded in the REQ-E1-06 row reads, in part: the interior
computes `Nat.log2 count` and `bpSparseLogSpan count` for a runtime-derived
`count`, and "the loop has NO literal all-size iteration cap". **That gap is
superseded in its cause and its mechanism no longer exists.** B7 (`d5a9355`,
merged at `f9b1ecc`) replaced the runtime computation with a count-indexed
charged table whose cell packs level and span, read once per two-span call
and unpacked by constant-divisor `div`/`mod` (`bpSparseLevelCell_div` /
`_mod`, `SparseLevelTable.lean:78`, `:90`). No executed definition mentions
`Nat.log2`.

What replaces it is NOT a restatement of the same obstruction. The remaining
uncapped structure is the table adapter's chunk fold, and that fold has a
LITERAL cap of `8`
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`,
`InteriorDirectory.lean:4511`), so REQ-E1-06 conjunct (c) — an all-size
literal total with no size hypothesis — survives intact. See
DD-20260719-003 and `E1_WORKLOG.md` M3d-11 section 2.

**This correction is offered for coordinator adjudication, not applied to the
frozen row text.** The row's own wording names a mechanism that is gone;
carrying it forward unamended would misdescribe the current machine, which is
the same failure mode the REQ-E1-07 supersession-note correction was recorded
to prevent.

### Consequence for REQ-E1-07's supersession note

The delegation's caution stands and is now discharged in one direction. The
sentence "every loop is a chunk fold under a literal cap" was FALSE while the
interior recursion existed. After B7 it is TRUE — but it must be shipped with
the B7 dependency explicit, and with the cap named as TWO literals, not one:
`33`/`8` for the fringe window and the interior chunk fold respectively. A
draft that names only `33`/`8` from the pre-B7 fringe text is still wrong,
because the `8` there is the per-word cap
(`machineWordBits_le_8_mul_bpFringeChunkBits`, `ChargedWordChunks.lean:39`),
a different `8` from the interior adapter's chunk cap. Two distinct literals
that happen to share a value.

## Evidence added by E1-R4u (M3d-12), no row closed, no row weakened

All eleven rows remain OPEN. Closure was impossible by construction: every
row is whole-query scoped and the whole-query composition is downstream of
the interior simulation, of which this session landed the second of six
pieces (M3d-11 landed the atom; this landed the eight-capped chunk fold).

Module: `RMQ/Core/WordRAM/E1InteriorChunkFold.lean`.

- REQ-E1-01. A second interior block whose guard is decided by a MACHINE
  comparison (`natLt` at `Q+1` on the machine's own index register,
  branched at `Q+9`) rather than a Lean-level `if`, and whose iteration
  count is COMPUTED by the machine via the truncated-subtraction cap chain
  `chunkCount - (chunkCount - 8)` rather than asserted
  (`interiorChunkInit:268`, `cap_chain_eq_min:1461`, DD-20260719-005).
- REQ-E1-02. `interiorChunkFold_fits:619`, constructor-exhaustive, no
  wildcard arm, per segment at `:507`, `:552`, `:578`, `:602`. Unlike the
  atom this block carries a divisor, so it has a positivity arm, discharged
  from `0 < wordScale`.
- REQ-E1-04. `chunkEventsAt_eq_route:1745`: positional receipt equality
  with the route's own address list, covering BOTH arms of the validity
  split at once because the dead path is a one-chunk instance of the same
  fold (`chunkAddrs_eq_consecutive:159`, DD-20260719-006). The whole-block
  form is `interiorChunkFold_runsTo:1785`.
- REQ-E1-05. `chunkFoldWitness_paths_distinguishable:1955`: four EXECUTED
  paths -- fully present multi-chunk, partially missing, wholly missing,
  dead -- onto pairwise distinguishable halts, by `decide`, depending on no
  axioms. All four halt (`:1937`).
- REQ-E1-06. `interiorChunkFoldCats_memoryRead_count:457` DERIVES the
  block's memory traffic from the category algebra as exactly the iteration
  count (init charges none, the reversal loop is read-free, the epilogue
  charges none), and `interiorChunkFoldCats_memoryRead_le_eight:480` caps
  it at the literal `8` WITH NO SIZE HYPOTHESIS.

### Sharpening of the REQ-E1-07 caution recorded above

The caution that the two `8`s are distinct literals that happen to share a
value is CONFIRMED and can now be stated with both sides concrete. The
fringe's `8` is the per-word chunk cap
(`machineWordBits_le_8_mul_bpFringeChunkBits`, `ChargedWordChunks.lean:39`).
The interior's `8` is the table adapter's per-read chunk cap, and it is now
proved on the machine side as `interiorChunkCount_le_eight:189`, derived
from `width <= 7 * wordSize` as `7` full chunks plus the partial-chunk
indicator.

Recorded because it is the kind of thing a reviewer would otherwise have to
re-derive: `interiorChunkCount_le_eight` carries NO `0 < wordSize`
hypothesis, deliberately. At `wordSize = 0` the route's own definition gives
`width / 0 = 0` and `width % 0 = width`, so the count is at most the
indicator `1`. Stating the bound without a positivity side condition keeps
the interior cap UNCONDITIONAL, which is what an all-size claim needs; a
version carrying `0 < wordSize` would silently owe that hypothesis to every
consumer.

### What REQ-E1-06 still lacks, stated precisely

The cap is now proved OF ONE BLOCK, not of the interior leg. The row needs
the composition: the five-branch interior dispatch and `hInterior`, which
are M3d-13 items 2-5. Separately, the block's VALUE correspondence to the
route's `fixedWidthNatTableMachineDecode` is not yet proved -- only its
RECEIPT is. See `E1_WORKLOG.md` M3d-12 section 7 item 1 for the exact
statement owed and the missing `bitsToNatLE_append` lemma.

## Evidence added by E1-R4v (M3d-13), no row closed, no row weakened

All eleven rows REQ-E1-01..11 remain OPEN. Closure was impossible by
construction, for the reason M3d-11 and M3d-12 both recorded: every row is
whole-query scoped and the whole-query composition is downstream of the
interior simulation, of which this session landed the third piece and
unblocked the fourth.

Module: `RMQ/Core/WordRAM/E1InteriorChunkValue.lean`, plus a strengthening
of two theorems in `RMQ/Core/WordRAM/E1InteriorChunkFold.lean`.

- **REQ-E1-03** (result agreement) — FIRST VALUE-SIDE INTERIOR EVIDENCE.
  Every earlier interior entry in this matrix was about receipts, widths
  or categories; the fold's VALUE was stated only in machine vocabulary.
  `chunkFoldValue_eq_route_decode:310` equates the machine's
  option-shifted cell with `fixedWidthNatTableMachineDecode`
  (`MachineChunkedTable.lean:215`), THE ROUTE'S OWN DECODE, on the words
  read at the route's own addresses, covering both the `some` and `none`
  verdicts. `interiorChunkFold_cOut_eq_routeDecode:491` restates it with
  a left-hand side that is verbatim the `cOut` clause of
  `interiorChunkFold_runsTo`, so a consumer may rewrite and be left with
  a statement purely about the route. This required
  `bitsToNatLE_append:84`, which the repository did not have. Does NOT
  discharge the row (whole-query scope).
- **REQ-E1-01** — `interiorChunkFold_runsTo`
  (`E1InteriorChunkFold.lean:1794`) now states what the block LEAVES
  ALONE (`:1821`), not only what it computes, chaining the four segments'
  own preservation clauses after supplying the missing fourth at
  `interiorChunkEpilogue_runsTo:1682`. STRENGTHENING ONLY: a conjunct was
  added to two conclusions, nothing weakened, nothing renamed, no
  hypothesis added. This is what makes the block instantiable more than
  once in one program, which the summary group requires. Does NOT
  discharge the row.
- **REQ-E1-05** — `witnessRouteDecode_cell2:560` checks the `none` arm on
  the ROUTE side by execution: the wholly missing cell decodes to `none`,
  matching the machine's `cOut = 0`. A value-only check has no power over
  that arm. Does NOT discharge the row.
- **Anti-vacuity for the new premise.** `interiorChunkFold_cOut_eq_routeDecode`
  carries a per-chunk width premise. `witnessWidth_cell0:579` discharges
  it on the existing witness store and `witnessCOut_cell0_via_bridge:612`
  DERIVES `2` through the bridge — the same `2`
  `chunkFoldWitness_path_bothPresent` (`E1InteriorChunkFold.lean:1918`)
  obtained by RUNNING the machine — so the premise set is demonstrably
  satisfiable and the theorem is not vacuously true.

### Reference correction offered for adjudication, NOT applied to frozen text

This matrix's accepted-route block (line 17) cites the accepted whole-query
trace as `RMQ/Core/SuccinctFinalRAM.lean:4337`. At this HEAD `:4337` is a
comment line; `def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`
is at `:4426`. The identifier is unchanged and correct — only the line
number has drifted. Recorded here rather than edited, because the block is
frozen. See `E1_WORKLOG.md` M3d-13 section 8.

### REQ-E1-09 / M7 doc row: the corrected citation was checked and REFUSED again

M3d-12 refused a coordinator-supplied `Nat.log2` scope precision because
it did not survive checking. A corrected version was supplied to M3d-13.
It was checked and it also does not hold: its load-bearing half — that the
four surviving runtime `bpSparseLogSpan` sites
(`InteriorRAM.lean:574, 622, 820, 868`) are reachable from the
size-premised `...OfSizeGe` family — is FALSE.
`WholeQueryInstr.evalGlobalWordTraceOfSizeGe`
(`SuccinctFinalRAM.lean:3718`) takes `(_hsize : 2 ^ 128 <= shape.size)`
UNUSED and its `.lcaClose` arm (`:3732`) dispatches to the same
`...AllSizeStructural` interior leg the accepted route uses.

The underlying claim — "no uncharged size-dependent computation on the
ACCEPTED ROUTE" — is TRUE and supportable, but the correct contrast is
`...AllSizeStructural` (`ConcreteDirectoryRAM.lean:1188`, accepted) versus
`...AtSegmentsAllSizeStructuralLegacy` (`:1196`, theorem-only consumers),
the same Legacy/non-Legacy distinction the coordinator already established
for `boundedSummaryRangeScanTraceResultAtSegments`. The doc row should be
written only after a coordinator settles that wording; it is in any case
downstream of the unbuilt interior items. Full evidence in
`E1_WORKLOG.md` M3d-13 section 8.

## Evidence added by E1-R4y (M3d-16), no row closed, no row weakened

All eleven rows REQ-E1-01..11 remain OPEN. Closure was impossible by
construction, for the reason M3d-11 through M3d-15 all recorded: every row
is whole-query scoped and the whole-query composition is downstream of the
interior simulation, of which this session discharged the last outstanding
premise but composed no further block.

Module: `RMQ/Core/WordRAM/E1InteriorChunkExact.lean`.

- **REQ-E1-03** (result agreement) — the value bridge's `hexact` premise,
  which M3d-15 reclassified from vacuous to LIVE, now has a SUBSTANTIVE
  discharge landed as executable Lean.
  `machineWords_length_eq_of_succ_lt_chunkCount` proves the machine word
  at flat index `i * count + j` has length exactly `wordSize` whenever the
  table holds cell `i` and another chunk sits above `j`, via
  `FixedWidthNatTable.machineWords_cell_slice`
  (`MachineChunkedTable.lean:121`) and
  `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`).
  `hexact_of_segment_agrees` restates it in the bridge's own shape over a
  `ReadStore` segment. Does NOT discharge the row (whole-query scope).
- **Anti-vacuity, on this module's OWN statement.**
  `exactFixture_final_length_lt` shows the FINAL chunk at the reachable
  `shape.size = 1` row has length `1` against `wordSize = 2`, so the
  `j + 1 < n` guard is LOAD-BEARING: dropping it makes the statement
  FALSE, not weaker. `exactFixture_nonfinal_lengths` exhibits the two
  non-final chunks at exactly `2`. All four fixture theorems depend on NO
  axioms (kernel computation).
- **Satisfiability of the one carried premise.** `hexact_of_segment_agrees`
  carries `hagree`, the segment-to-table mapping, as a deliberate
  parameter. `segmentStore` / `segmentStore_agrees` exhibit a store
  meeting it. NOTE THE LIMIT OF THAT EVIDENCE, stated so no consumer
  over-reads it: it shows the premise is SATISFIABLE, not that it HOLDS at
  `canonicalRelativeRmmInteriorComponentStore`. Deriving it there is the
  composition step and is NOT done.
- **REQ-E1-11** — `cell_exists_of_lt` is DERIVED from the table's
  `read_exact` field rather than assumed, so the corollary carries no
  unchecked existential premise.

### Correction to a supplied claim, checked at source

The M3d-16 delegation stated that `chunkPayloadWords_get?_eq_take_drop`
(`WordStore.lean:274`) "does not exist" and directed that it be proved.
IT EXISTS, at exactly that file and line, with exactly the per-index
presentation needed, and four modules already cite it. The new module's
proof CALLS it and compiles. DD-20260719-010's original direction was
correct as written; the non-existence gloss added downstream of it was
wrong. Recorded per the standing instruction to report rather than write
an unsupported sentence. Full evidence in `E1_WORKLOG.md` M3d-16 section 1
and DD-20260719-011.

## Evidence added by E1-R4z (M3d-17), no row closed, no row weakened

All eleven rows REQ-E1-01..11 remain OPEN. No frozen requirement text was
edited. Every row is whole-query scoped and the whole-query composition is
downstream of the interior simulation, of which this session landed the
premise discharge and not a block.

- **REQ-E1-03** (result agreement) - the interior value bridge's `hexact`
  premise is now DISCHARGED AT
  `canonicalRelativeRmmInteriorComponentStore`, not merely witnessed
  satisfiable away from it. `E1InteriorChunkStore.hexact_baseline`,
  `hexact_minRel`, `hexact_maxRel` and `hexact_argOffset` instantiate
  `hexact_of_segment_agrees` at that store with the agreement parameter
  SUPPLIED, from `hagree_baseline` .. `hagree_argOffset`; the other four
  component tables have their agreement clauses landed (`hagree_local`,
  `hagree_global`, `hagree_localLevel`, `hagree_globalLevel`) awaiting the
  blocks that read them. The base offsets are the ROUTE's own
  (`canonicalRelativeRmmInteriorComponentOffsets`,
  `InteriorDirectory.lean:1614`, consumed at `:2282`, `:2317`, `:2335`),
  so this is agreement with the route's addressing.

  THE EVIDENCE IS PARTLY A SUBTRACTION, as it was in M3d-14 and M3d-15, and
  the subtraction is recorded rather than netted out. What M3d-16 recorded
  for this row rested on an `hagree` premise that is FALSE at this store for
  seven of its eight tables - the store is the CONCATENATION of the eight
  tables' word lists, so past the end of any one of them it still answers
  `some` while the table's own list answers `none`. The premise is re-cut
  BOUNDED (strengthening only: premise weakened, conclusion untouched,
  nothing renamed) and the bound is supplied internally by
  `machineWords_index_lt`. The row is not better off than it looked; it is
  now as well off as it looks.

- **REQ-E1-05** (anti-vacuity) - `unbounded_agreement_refuted` proves the
  discarded premise CONTRADICTORY at every shape whose `minRel` table is
  non-empty, so the bound in the re-cut premise is demonstrated load-bearing
  rather than asserted to be. Recorded because it bounds future anti-vacuity
  work: the numeric fixture was written first and does NOT compile - the
  interior store's sizes run through `Nat.log2`, defined by well-founded
  recursion, which the compiler evaluates (`#eval` gives `(2, 31)` at the
  one-node shape) but THE KERNEL CANNOT REDUCE, so `rfl` and `decide` both
  fail and `native_decide` is forbidden. The general theorem is strictly
  stronger than the fixture would have been.

  NOTE THE LIMIT OF THIS EVIDENCE, stated so no consumer overreads it. All
  twelve clauses carry `HoldsInteriorStore` - that the machine's flat store
  at `segment` holds the interior directory - as a SETUP hypothesis.
  `interiorReadStore_holds` shows it satisfiable. By this session's own
  finding that is NOT a discharge: it is a store built FOR the hypothesis,
  the same shape of witness as the `segmentStore_agrees` that hid the defect
  this session found. Discharging it at the store the interior program
  actually runs against is owed by whoever writes the summary group, and the
  established E1 pattern for it is instantiation, not parameterisation.

Full evidence in `E1_WORKLOG.md` M3d-17 and `DESIGN_DECISIONS.md`
DD-20260719-012.

---

## AMENDMENT A1 (2026-07-19) — `207` -> `210`, coordinator-approved

**Authority.** The matrix header permits "evidence, status, and
coordinator-approved amendments" to change after the freeze. This amendment was
escalated to the project owner rather than decided by the coordinator, because
altering frozen requirement text is outside the coordinator's standing
authority. The owner selected amendment over an appended note.

**What changed.** Three occurrences of the numeral `207`:

1. REQ-E1-06's frozen requirement cell, "memory-read count = accepted trace
   length (`<= 207` by the existing bound)" -> `<= 210`.
2. The accepted-route object block's citation
   `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 207`
   -> `= 210`.
3. The same block's `SuccinctClassic.queryCost_eq : queryCost = 207` -> `= 210`.

No other cell, row, status or evidence entry was touched. No row was weakened in
substance: REQ-E1-06's operative clause is the EQUALITY "memory-read count =
accepted trace length"; the parenthetical is a bound on that length, and it is
the bound's *identity* that moved, not the requirement's shape.

**Why it was necessary rather than cosmetic.** When this matrix was frozen at
`d90b062` both cited theorems did read `207`. Commit `f6000c3` ("B7 commit A:
widen the interior charged cap 30 -> 33 and migrate 207 -> 210") retired that
constant: at HEAD, `207` is a FROZEN HISTORICAL constant naming a route that is
no longer accepted
(`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq`), and the
live all-size bound is `210`. The algebra is
`2*select35 + (2*rank11 + 2*endpointFringe37 + interior33) + rank11 = 210`, with
`closeLCA = 129`.

So the cell as frozen demanded a bound that is **unprovable for the accepted
route, not merely unproved** — B7's own docstring records the interior component
as TIGHT AND ATTAINED at `33` with the headroom CONSUMED. Leaving the text
unamended would have left REQ-E1-06 unsatisfiable by construction while
appearing merely open.

**Scope note — what this amendment does NOT do.** It does not touch the frozen
historical constants themselves (`207`, `142`, `76`, `328`), which remain pinned
to literals in `SuccinctFinalRAM.lean` precisely so that no later recharge can
rewrite history. It does not alter any Closed row in the B2/B3/B4, B6 or B7
matrices. And it does not address the stale `207` numerals still present in
`README.md` and `docs/FAMILY_SUMMARY.md`, which are paper-facing prose, are
caught by no gate (`CLAIM_DRIFT_POLICY.json` carries no `207`/`210` term, and
`paper_topology_lint.ps1` anchors on identifiers rather than prose numerals),
and are recorded here as owed to REQ-E1-09's documentation pass.

---

## AMENDMENT A2 (2026-07-19) — REQ-E1-01's operand width, coordinator-approved

**Authority.** The matrix header permits "evidence, status, and
coordinator-approved amendments" to change after the freeze. Escalated to the
project owner rather than decided by the coordinator, because altering frozen
requirement text is outside coordinator authority. The owner approved amendment
over adjudication, and directed that the amendment be paired with the
logarithmic bound recorded below.

**What changed.** One occurrence, in REQ-E1-01's frozen requirement cell:
"over `machineWordBits`-width operands" -> "over
`concreteBPNativeSuccinctRMQReviewerWordBits`-width operands". Nothing else in
the row, and no other row, was touched.

**Why it was necessary rather than cosmetic.** The tree contains a **checked
theorem that the executed program does not fit the size-indexed width**:

- `wholeQueryProgram_not_fits_machineWordBits` (`E1WholeQueryWidth.lean:84`)
  proves `¬ ProgramFits (SuccinctRank.machineWordBits shape.size)
  (wholeQueryProgram shape n)` for every shape of size `<= 2821`.

This is structural, not a defect. `machineWordBits n = Nat.log2 n + 1`, so at
`n = 4` the modeled envelope is `2^3 = 8`, while the construction allocates
register indices to `152` and branch targets to `5644`. Leaving the cell
unamended would have left REQ-E1-01 **unsatisfiable by construction while
appearing merely open** — the same failure AMENDMENT A1 was raised to fix for
REQ-E1-06's retired `207`.

**The positive certificate is proved for a FAMILY of widths, and the amended
width is the member exhibited.** (Restated 2026-07-20; the earlier wording of
this paragraph advertised "no parametric `w`" as a virtue, which read as a
deficiency once the row named a specific width.)

- `wholeQueryProgram_fits_of_wordAddressesStructure`
  (`E1WholeQueryPathWidth.lean:512`) fits a **parametric** `w` under a single
  named word-RAM model assumption: `WordAddressesStructure w shape.size`
  (`E1ReviewerWidth.lean:177`), that one machine word addresses the structure.
- `wholeQueryProgram_fits_reviewerWordBits` (`:547`) is that theorem
  instantiated at the amended width, and is the witness that the assumption is
  **satisfiable**. Its statement is UNCHANGED by the parametrisation, and it is
  still hypothesis-free: no size threshold, no premise about interior, select or
  composition.
- `wholeQueryProgram_fits_of_reviewerWordBits_le` (`:557`) carries it to any
  wider word via `ProgramFits.mono` (`E1Machine.lean:581`), so a reader may
  instantiate at THEIR word size rather than ours.
- `wholeQueryProgram_fits_logarithmicWidth` (`:581`) states in ONE proposition
  that the assumption holds at a width `<= 20 * (Nat.log2 (n + 2) + 1)`.

**The family is not vacuous, and that is proved rather than argued.**
`not_wordAddressesStructure_of_width_le_18` (`E1ReviewerWidth.lean:213`) shows
the assumption FAILS for every `w <= 18` at every size. So the premise excludes
a real range of widths instead of holding of any `w` — which is what an auditor
should check before accepting any hypothesis-carrying theorem as content.

**WHAT THIS RESTATEMENT IS NOT, recorded so that no reader infers more than was
proved.** It is the same mathematics in reviewer-facing vocabulary, **not a
stronger theorem.** The admissible family is exactly
`{w : shapeWidth shape <= w}`, so the parametric theorem is **extensionally
equivalent** to the concrete theorem plus `ProgramFits.mono`. The reason:
`shapeWidth = Nat.log2 capacity + 1` while the minimal `w` with
`capacity <= 2 ^ w` is `ceil (log2 capacity)`, and these coincide unless the
capacity is a power of two — which `capacity n = 400000 * (n + 1)
= 2^7 * 5^5 * (n + 1)` never is, since `5^5` is odd and greater than one. **That
equivalence argument is analytical and is NOT machine-checked**; it is recorded
as reasoning. The parametrisation was undertaken because the problem was
presentational, and an equivalent restatement in model vocabulary is precisely
the remedy for a presentational problem. It buys legibility, not generality, and
this amendment claims only the former.

**Verification status of the theorems cited in this amendment.** All were
checked at commit `27f1284` before merge: whole-tree `lake build RMQ` PASSED at
that exact commit — with freshness established independently of the build cache,
since the axiom check resolved `not_wordAddressesStructure_of_width_le_18`, a
declaration that does not exist at the preceding commit — all eleven
declarations axiom-clean (subsets of `[propext, Classical.choice, Quot.sound]`,
zero `sorryAx`), and the validator built and ran to `RESULT: PASS`.

**THE AMENDMENT BUYS UNIFORMITY, NOT HEADROOM. Both widths are logarithmic in
the input size, and the repo already proves it.**

- `concreteBPNativeSuccinctRMQReviewerWordBits_le_log`
  (`ReviewerPhysical.lean:1502`): the reviewer width is
  `<= 20 * (Nat.log2 (n + 2) + 1)`. **Explicitly logarithmic, all sizes.**
- It is already a **public headline**, aliased as
  `succinctRMQReviewerWordBitsLogarithmic` (`RMQ/Headlines/RMQ.lean:304`),
  already consumed by the adequacy certificate
  (`SuccinctFinalModelAdequacy.lean:388`), and already covered by the repo's own
  axiom check (`scripts/wordram_axiom_check.lean:236`).
- The underlying capacity is concretely linear:
  `concreteBPNativeSuccinctRMQReviewerCapacity_linear` (`:1496`),
  `= 400000 * (n + 1)`.

So the machine is certified at a word width the repository **independently
proves is `Theta(log n)`**, with the constant factor proved rather than
assumed. That is the transdichotomous word-RAM model as ordinarily stated, not
a departure from it.

**Why the size-indexed width fails, stated precisely so it is not mistaken for
a scaling problem.** The refutation window is `size <= 2821`. The failure is at
SMALL shapes only, because the program is **constant-size** — `5646`
instructions, whose largest encoded field is the branch target `5644`,
independent of `n`. Asymptotically `machineWordBits` would suffice. But
REQ-E1-01 demands the property "for every size", and this campaign forbids
size-thresholded claims on the public route, so a uniform statement requires
the reviewer width. **The amendment purchases uniformity across all shapes, not
a wider machine.**

**Scope note — what this amendment does NOT do.** It does not weaken the row:
the requirement is still that every encoded field of every instruction of the
concrete program fits the modeled word, and that is now proved rather than
open. It does not touch `machineWordBits` itself, which remains the input-array
pointer width and is a different quantity. It does not disturb the rejection
witnesses: `wholeQueryProgram_not_fits_machineWordBits` is retained precisely
because it records why this amendment was needed — and it now does double duty,
as the anti-vacuity witness for the width family alongside
`not_wordAddressesStructure_of_width_le_18` — and
`programSkeleton_not_fits_machineWordBits` (`E1ReviewerWidth.lean:477`) is a
distinct fact about a distinct program. And it does not resolve REQ-E1-02's
phrase "the modeled word width", which the matrix's own accepted-route block
already defines as naming both widths; that row is adjudicated, not amended.

## Evidence added by E1-Req08, no row closed, no row weakened

Lane scope: REQ-E1-08's two recorded gaps. **No frozen requirement text is
edited, no `Status` cell is set to ACCEPTED, and no row is closed here** --
acceptance is the coordinator's to record, not this lane's.

### Anchor correction, stated rather than edited into the frozen cell

The `Evidence obtained` cell above cites the reference implementation as
`refRMQ` (`:78`), a line reference into
`RMQ/Validation/E1MachineValidate.lean`. **That anchor is now stale**, and it
is stale by this lane's own doing: `refRMQ` has moved to
`RMQ/Validation/E1RefRMQ.lean`. Its NAME is unchanged --
`RMQ.Validation.E1MachineValidate.refRMQ`, namespace deliberately retained
across the move -- so every by-name citation in this matrix still resolves.
Only the file-and-line pair moved. Recorded here rather than rewritten into
the cell, per the standing rule that these cells are not this lane's to edit.

### Gap (b) -- the independence clause -- is addressed

`refRMQ` now lives in `RMQ/Validation/E1RefRMQ.lean`, a module with **no
`import` lines at all**, so its entire ambient context is Lean's `Init`:
the "basic prelude" the anti-vacuity column allows, and nothing else. The
independence the clause asks for is now enforced by the module system on
every build rather than by reviewer attention -- a machine or route constant
used from that module does not elaborate.

Two specification clauses are proved there as well:
`refRMQ_eq_none_of_hi_le_lo` and `refRMQ_eq_none_of_length_lt`. Both report
"does not depend on any axioms". See DD-20260720-010, which also records a
near-miss: under `split` the second proof's hypothesis is consumed by the
split rather than by the simp, the linter then flags it unused, and the
theorem reads as vacuous. It is not -- deleting the hypothesis breaks the
proof -- and the proof was rewritten explicitly so the next reader need not
re-derive that.

### Gap (a) -- the whole-query positional receipt diff -- is addressed

`WQReport` carried `reads : Nat`, a COUNT. It now also carries
`routeTraceLen`, `receiptMatchesRoute` and `receiptEmpty`, and
`runWholeQuery` compares the machine's `readLog` against the route's
`wholeQueryRouteTrace` with `==` on `List TraceEvent`. `TraceEvent` derives
`DecidableEq`, so that comparison is decided **constructor by constructor and
field by field, in order** -- segment, index AND word. It is not a length,
not a count, and not a multiset.

Comparing against `wholeQueryRouteTrace` is comparing against the accepted
trace this row names:
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_decompose`
(`E1RouteDecomposition.lean`) proves, with no branch hypothesis, that the
route object's `.trace` IS `wholeQueryRouteTrace`.

Executed, un-mutated:

```
wholeQueryRouteTraceEvents=1415        (route side)
wholeQueryModeledReads=1415            (machine side)
wholeQueryReceiptMismatches=0          (event for event)
wholeQueryReceiptComparisons=20
wholeQueryComparableCases=20           (equality is the anti-vacuity check)
wholeQueryInvalidReceiptViolations=0   (a rejected query reads NOTHING)
RESULT: PASS                           (exit 0)
```

`.invalid` cases are excluded from the diff for the reason `modelSteps`
already excludes them -- the guard exits before the route's stage record
applies -- and are NOT waived: `wqInvalidReceiptViolations` checks the
stronger property that the machine read nothing at all, and gates the exit
code. The comparison count is required to EQUAL the comparable-case count
rather than merely exceed zero, so a case dropping out of the diff fails the
run.

The clause is exit-code-visible: `okWholeQuery` now also requires
`wqReceiptBad == 0`, `wqReceiptCmp == wqComparable`, `wqReceiptCmp > 0` and
`wqInvalidReceipt == 0`.

### The diff is load-bearing, and it OUTRANKS the value comparison on mutant M

A check that nothing can fail is the vacuity this matrix exists to police, so
the receipt diff was run against the existing machine mutant rather than
asserted to be live. Mutant M (`natLt` -> `natLe` throughout the whole-query
program) was recorded here as "whole-query value-only".

```
mutantM_answerMismatches=12    (of 24 cases; the value comparison)
mutantM_casesUnaffected=12     (windows with no tie answer identically)
mutantM_receiptMismatches=20   (of 20 comparable cases; the receipt)
```

**The receipt rejects mutant M on every comparable case, including the eight
the value comparison cannot see**, because relaxing `<` to `<=` re-routes
control through read-bearing code even on windows whose final answer
coincides. Mutant M's "value-only" label in the `Evidence obtained` cell
above is therefore now understated -- stated here rather than edited into the
cell. See DD-20260720-011, which also records why this does not contradict
the §6 models where receipts are weaker than the value.

### What this lane did NOT do

- No `Status` cell changed; **REQ-E1-08 remains as the table records it**.
  Whether the two gaps being addressed closes the row is the coordinator's
  call, not this lane's.
- No frozen requirement text edited.
- No public identity renamed or deleted -- `refRMQ` kept its namespace
  precisely so the move would not become a rename.
- `class_select-miss=0` is UNCHANGED and remains a real corpus hole: no
  fixture in `wholeQueryCases` reaches a select-miss branch, so that class is
  named but unpopulated. `wqClassesAllPopulated` does not require it, and
  this lane did not add one.

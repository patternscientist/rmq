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
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 207`
  (`:8702`); public `SuccinctClassic.queryCost_eq : queryCost = 207`
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

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-E1-01 | "Familiar small-step machine: a standard word-RAM instruction semantics — memory read (segment, index -> register), register move/write, integer arithmetic (add/sub, and mul/div-by-constant only if the route needs them — inventory first and record the ISA decision), comparison, conditional branch, halt — over `machineWordBits`-width operands. Every executed instruction charges exactly one step. No instruction may hide recursion, variable-length scans, table decoding beyond one bounded arithmetic expression, or multi-read composites." | Local | A Lean `inductive` instruction type whose constructors are exactly the familiar repertoire; a step function executing ONE instruction per step with cost 1 charged per executed instruction (checked cost lemma: total steps = executed instruction count); structural audit theorem or definitional shape making per-instruction work non-recursive (the step function is a single non-recursive `match`; only the outer run loop recurses, on a fuel/halt counter); ISA inventory recorded as a DD entry (which arithmetic ops the route needs and why). | The E1 amended target Prop (REQ-E1-07) existentially consumes this machine; chain: instruction type -> step function -> run -> program (REQ-E1-03). | Adversarial: a constructor like `readFringeFold` that folds 33 reads in one step must be impossible to add without failing the certificate — the per-instruction read-event count lemma (each step emits <= 1 memory-read event) and the cost=instruction-count lemma reject multi-read composites; a hidden `List.rec` in the step function rejected by the step function being a single `match` with no recursive call. | Partial (component). Fringe fold block `RMQ/Core/WordRAM/E1FringeFoldBlock.lean`: 66-instruction body, every instruction one atomic constructor, no multi-read composite (the pass emits exactly ONE `readMem`, `fringePrefix_runsTo:465`). ISA decision recorded DD-20260718-009. Extended by the ARM block `RMQ/Core/WordRAM/E1FringeArmBlock.lean` (DD-20260718-010): the window read is FOUR separate `readMem` instructions, not a composite (`fringeWindowRead:90`, `fringeArmPrologueCats_memoryRead_count:166` = 4); whole arm `fringeArm_runsTo:904` is 95 instructions plus the fold. Extended by the SAME-BLOCK arm `RMQ/Core/WordRAM/E1SameBlockArm.lean` (DD-20260718-011): `sameBlockArm_runsTo:373` is 97 instructions, every one an atomic constructor; the `bpCandidateClose?` epilogue is TWO instructions with no option dispatch and no read, because `bpFringeCandGlobal` is total into `some`. The ADDRESS PREAMBLE `windowAddr:127` is four instructions using `divConst`/`mulConst` with PER-SHAPE CONSTANT immediates only — verified at source, not assumed (see worklog M3d-3 section 1), so the route needs no variable-divisor instruction and none was invented. Extended by the RANGE PREAMBLE and the RANK SEED (M3d-4): `windowRange` (`E1SameBlockArm.lean:447`) is eight instructions using `add`/`sub` only — no divisor at all — and `rankSeedFinish` (`E1SameBlockLeg.lean:102`) is three instructions whose only multiplier is the CONSTANT `2`, so the seed needs no variable-multiplier instruction either. The composed leg `sameBlockLeg_runsTo_canonical` (`E1SameBlockLeg.lean:333`) is 173 instructions, every one an atomic constructor. ANTI-VACUITY DISCHARGED FOR THIS COMPOSITION: `sameBlockLegProgram_hosts` (`:477`) exhibits one concrete program satisfying all thirteen `HostedAt` hypotheses plus the back-edge fetch simultaneously, so the composed simulation is not a theorem with unsatisfiable premises; every offset is forced by the preceding segments' lengths, so a one-off layout error fails to typecheck. M3d-6 STRENGTHENS THAT WITNESS OFF BASE ZERO: at base `0` the leg's four absolute internal addresses (`rankCloseBlock` base `5`, `fringeMerge 97`, the `brNZ fCnt 97` back edge, `fringeCandGlobal 164`) are correct BY ACCIDENT, so a base-0-only witness cannot detect a rebasing defect. `sameBlockLegProgramAt` (`E1SameBlockLeg.lean:595`) rebases all four; `sameBlockLegProgramAt_hosts` (`:634`) derives the twelve hosting facts at `B + k`; `sameBlockLegProgramAt_zero` (`:621`) proves it specialises to the landed base-0 layout, so nothing regresses. The dispatch composition `sameBlockDispatchProgram_runsTo` (`E1CloseCompose.lean:95`) runs dispatch-then-leg as ONE program, and `sameBlockDispatchProgram_runsTo_witnessCross` (`:158`) pins the leg's host base to a CONCRETE `6` (internal targets `103`/`170`, exit `179`). M3d-7 ADDS THE THREE-WAY CANDIDATE MERGE, the last cross-block component that was neither assembly nor interior-blocked: `candMerge3` (`E1CandMerge3.lean:198`) is 16 instructions, every one an atomic constructor, read-free (`candMerge3_readFree:206`), and `candMerge3_runsTo` (`:718`) simulates all SIX control paths -- the block does NOT generalise from `sameBlockClose`, because `middle?` is genuinely optional. ANTI-VACUITY BY EXECUTION, NOT HOSTING: `candMerge3Witness_path1..6` (`:817`-`:841`) RUN the block on six concrete register files and reach six distinguishable halts, separated by modeled steps (`10,11,13,14,12,13`) AND close payload (`99,200,201,302,103,304`); `candMerge3Witness_paths_distinguishable` (`:843`) states the pairwise distinctness as a `Nodup` that fails if any two arms collapse. All eight depend on NO axioms (kernel computation). M3d-9 COMPOSES THE CROSS-BLOCK ARM AS ONE PROGRAM: `crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean`) runs all 370 instructions, every one an atomic constructor, with the INTERIOR AS A HYPOTHESIS (`hInterior`) rather than a pin — its trace, categories and value are parameters, so worker B7's interior change instantiates the theorem differently and does not restate it. One structural finding forced a layout change, recorded not worked around: `fOne` (register 40) sits INSIDE the fold bank 40..62, so the arms may clobber the merge's required unit constant and the fold takes `fOne = 1` as a hypothesis without restating it as a conclusion; the new one-instruction `crossPinOne` re-pins it (369 -> 370 instructions). Does NOT discharge the row (whole-query scope). | Open |
| REQ-E1-02 | "Constructor-exhaustive address/operand width accounting: every encoded field of every instruction fits the modeled word width, and oversizing any field must break the certificate (a predicate returning True on unhandled constructors fails the row)." | Local | A width-accounting predicate defined by exhaustive `match` on the instruction constructors (no wildcard/default arm returning `True` for operand-carrying constructors), and a checked theorem: every instruction of the concrete program satisfies it at the modeled width for every size; plus an explicit rejection witness: some concrete oversized instruction fails the predicate (kernel-checked `¬ fits`). | Feeds REQ-E1-07 (target Prop conjunct) and INV-ADDRESS-WIDTH. | Replace one constructor arm with `True` — the rejection witness for that constructor's oversized instance must fail, demonstrating the arm is load-bearing; the predicate must range over the operands actually encoded, not a projection that drops fields. | Partial (component). `fringeLoopBody_fits` (`:376`) is a constructor-exhaustive width certificate over all 66 instructions, no wildcard arm. The four-word window is deliberately NOT held in one register: `windowRegsValue` four-register Horner form with `c <= L` unconditional at every size (`bpFringeChunkBits_le_machineWordBits`). Arm prologue adds `fringeArmPrologue_fits` (`E1FringeArmBlock.lean:210`), constructor-exhaustive over all 21 prologue instructions, no wildcard arm; the predicate is `Instr.FieldsFit` (`E1Machine.lean:503`), a Prop with an arm per constructor. Same-block arm adds `sameBlockClose_fits` (`E1SameBlockArm.lean:249`) and `windowAddr_fits` (`:143`), both constructor-exhaustive with no wildcard arm; `windowAddr_fits` additionally discharges `divConst`'s `0 < k` positivity arm from the route facts `canonicalBPRelativeSummaryBlockSizeRaw shape >= 2` and `machineWordBits_pos`, so the width certificate is load-bearing against a zero divisor rather than assuming one away. M3d-4 adds three more constructor-exhaustive certificates with no wildcard arm: `windowRange_fits` (`E1SameBlockArm.lean:468`) over all eight range-preamble instructions, `rankSeedPos_fits` (`E1SameBlockLeg.lean:68`) and `rankSeedFinish_fits` (`:114`) over the four seed instructions. Every one discharges its own constructor's field conjunction from `Instr.FieldsFit`; none carries a divisor, so none needs the positivity arm. M3d-5 adds `closeDispatch_fits` (`E1CloseDispatch.lean:106`), constructor-exhaustive over the four dispatch instructions, discharging `divConst`'s positivity arm from `canonicalBPRelativeSummaryBlockSizeRaw_pos`. M3d-6 adds `fringeCandGlobal_fits` (`E1FringeArmBlock.lean:738`) over the seven global-rebase epilogue instructions, which was the ONE same-block leg segment with no width certificate (`rankCloseBlock_fits` `E1RankBlock.lean:1003` and `fringeLoopBody_fits` `E1FringeFoldBlock.lean:376` already covered the rest). M3d-7 CLOSES THE WHOLE-PROGRAM GAP: `sameBlockLegProgramAt_fits` (`E1ProgramWidth.lean:57`) certifies all 173 leg instructions and `sameBlockDispatchProgram_fits` (`:141`) the dispatch composite, carrying the cross arm as a hypothesis so the certificate is stated BEFORE the cross-block arm exists and will force it to be certified when it does. Two facts the M3d-6 'assembly only' estimate missed, both checked not assumed: `rankCloseBlock` is instantiated at `L := shape.bpCode.length`, NOT the `machineWordBits` the fold body uses, so the leg certificate needs its own width hypothesis; and the fold back edge's `fCnt` is an abbrev opaque to `omega`. The merge adds `candMerge3_fits` (`E1CandMerge3.lean:324`), constructor-exhaustive, no wildcard arm, no divisor hence no positivity side condition. M3d-9 adds `crossPinOne_fits` (`E1CrossBlockArm.lean`) and updates `crossBlockArmProgramAt_fits` for the 370-instruction layout; it still carries the interior's instructions as a HYPOTHESIS, so it remains stated before the interior exists and will force the interior to be certified when it lands. Does NOT discharge the row. | Open |
| REQ-E1-03 | "result agreement — the machine's output equals `(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right).value` (and through it the public `List Int` query) for every valid query" | Local+roadmap | Checked theorem: for every shape/left/right admitted by the accepted route's validity domain, running the concrete program on the machine yields output = `(...GlobalWordTraceResult shape left right).value`; composed corollary through the existing exactness chain to the public `List Int` query answer. Universal quantification, no sampling, no readiness guards. | The amended target Prop; chain: machine run -> program semantics -> accepted trace `.value` -> `SuccinctClassic.queryCosted` -> public `List Int` query. | Q-mutations rejected: agreement only on sampled inputs (statement is universally quantified); agreement of a projection that ignores the packet's index component (statement equates the full value). Value must be computed from machine registers fed by the machine's own reads (INV-VALUE-DEPENDENCY), not copied from the spec trace. | — | Open |
| REQ-E1-04 | "receipt projection — the ordered sequence of memory-read events the machine performs is POSITIONALLY EQUAL to the accepted trace `(...).trace` (same segments, indices, values)" | Local+roadmap | Checked theorem: the machine execution's ordered read-event projection (list of (segment, index, word?) in execution order) = `(concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right).trace` mapped through the readWord shape, as a POSITIONAL list equality (not multiset/membership), for every valid query. | The amended target Prop; chain: machine read log -> projection -> accepted trace; consumes `_readWord_only` to state the projection totally. | Positional equality rejects: permuted logs, deduplicated repeated reads (the B4 repeated-read receipts require multiplicity), appended decorative reads. Evidence must be `List` equality, not `∀ e, e ∈ log ↔ e ∈ trace`. | Partial (component). `fringeFoldLoop_runsTo_accepted` (`:1301`): machine read log = `(bpFringeChunkFoldTraceResultAtSegmentWithStore ...).trace` as a POSITIONAL `List` equality, via `iterLog_congr` + `iterLog_singleton_desc`. Extended to a WHOLE FRINGE ARM: `windowReadEvents_eq_route` / `_windowBits` (`E1FringeArmBlock.lean:393`/`:405`) are positional `List` equalities to `localBPBlockWordsTraceResultWithStore` / `localBPWindowBitsTraceResultWithStore`, and `fringeLeg_trace_eq_leftArm`/`_rightArm` (`:618`/`:647`) give the named accepted arm objects` full receipts (the `bpFringeCandGlobal` epilogue emits none). Extended to the SAME-BLOCK object: `sameBlockSeeded_trace_eq` (`E1SameBlockArm.lean:308`) is a POSITIONAL `List` equality to `bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore` (`ChargedSameBlockTrace.lean:55`), and `sameBlockArm_runsTo:373` carries it as the whole arm's receipt; the close epilogue emits no event, matching the route's `TraceResult.map`. Extended to the DECODED object at the CANONICAL STORE (M3d-4): `rankSeedLeg_runsTo_canonical` (`E1SameBlockLeg.lean:204`) is a POSITIONAL `List` equality to `localBPSeedFromRankCloseTraceResult`'s trace, and `sameBlockLeg_runsTo_canonical` (`:333`) is a POSITIONAL `List` equality to `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` (`ChargedSameBlockTrace.lean:340`). Because `rankCloseBlock_runsTo_canonical` is fixed at `concreteBPNativeSuccinctRMQGlobalReadStore shape`, the composition forces the store-parametric arm onto that SAME store: one machine run, one store, one log — the store-swap glue form the whole-query composition needs. M3d-6 carries the SAME positional receipt through the branch dispatch: `sameBlockDispatchProgram_runsTo` (`E1CloseCompose.lean:95`) reproduces the route's same-block trace from the composite program, and because the dispatch emits no read event the composite's log equals the leg's exactly. EXECUTED, not only proved: validator phase 3d diffs the composite's `readLog` event-by-event against the route's independently computed `.trace` (40 cases, 27 same-block, 0 mismatches), and phase 4c's mutant B — one operand, the fold back edge moved from the rebased `103` to the base-0 `97` — REACHES THE CORRECT EXIT PC 179 yet is rejected by the receipt diff alone. M3d-9 carries a POSITIONAL receipt through the whole CROSS-BLOCK arm: `crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean`) reproduces `crossBlockArmSpec`'s trace — the two seed legs, the two arms and the interior in the route's own emission order, the preambles/stashes/repoint/pin/merge being read-free — as a `List` equality, with the interior's trace a PARAMETER. Does NOT discharge the row (whole-query scope). | Open |
| REQ-E1-05 | "invalid guard — empty/reversed/out-of-bounds inputs produce the guarded none-packet with empty read projection and zero cost, matching `SuccinctClassic.queryCosted_invalid` semantics" | Local | Checked theorem(s): for invalid ranges (left >= right or right > n), the machine run halts with the none/guarded output, its read projection = `[]`, and its charged step total for the memory-read category = 0 with the overall guarded cost matching the accepted invalid semantics; exercised on empty, reversed, and out-of-bounds fixtures in Lean examples and in the validator. | Public guard parity with `SuccinctClassic.queryCosted_invalid`; chain: machine guard branch -> none packet -> public invalid semantics. | The guard must be computed by machine comparisons on the query operands (charged steps), not a meta-level `if` outside the machine; an unguarded machine wrapped in a Lean-level guard fails the row. | — | Open |
| REQ-E1-06 | "Fully charged cost correspondence: total machine steps = sum of explicit category counts (controller/dispatch, decode/arithmetic, comparison/branch, memory reads, register writes — choose and freeze the categories); memory-read count = accepted trace length (<= 207 by the existing bound); a DERIVED literal all-size total step bound (never asserted; expect low thousands — whatever derives, derives)." | Local | Frozen category choice recorded (DD); checked theorems: (a) total steps = sum over the frozen categories of per-category counts (an accounting identity over the machine log); (b) the memory-read category count = accepted trace length for every valid query (hence <= 207 via the existing bound); (c) an all-size literal `totalSteps <= <literal>` derived by `rfl`/omega from the per-phase algebra, no size hypothesis. The literal is whatever the derivation produces; it is never asserted against an independent numeral first. | The amended target Prop conjuncts; chain: step log -> category partition -> read category = trace length -> 207 bound; total <= derived literal. | Mutating a phase constant must break the `_eq` derivation (pattern: B2's REQ-B2-15 challenge); a category partition that double-counts or omits steps is rejected by the accounting identity being an equality, not <=; the read-category theorem must equate to the ACCEPTED trace length, not to an independent count. | Partial (component). Per-pass category log is a FUNCTION of the route-side branch conditions (`fringeMergeArmCats:281`, `fringeMergeCatsAt:300`, `fringePassCats:309`), never a numeral; whole-fold log `fringeFoldCats:952` is their execution-ordered concatenation (`ascLog`/`iterLog_desc`). Arm level: `fringeCandGlobalArmCats` (`E1FringeArmBlock.lean:731`) is indexed by the ROUTE-side occupancy of the accepted fold object`s best candidate (`bestOfRegs_isSome:881`), and the iteration count is DERIVED as `Nat.min (relHi/c+1) 33` by the truncated-subtraction cap chain (`cap_chain_eq_min:239`), never asserted. M3d-7: the merge's category log is likewise a FUNCTION of the route-side branch conditions -- `candMerge3Cats` (`E1CandMerge3.lean:247`) dispatches on middle occupancy and the two `bpCandidateBetter` comparisons, never a numeral -- and the six resulting step totals are EXHIBITED by execution (`candMerge3Witness_path1..6`), not asserted. M3d-9: `crossBlockArmCats` (`E1CrossBlockArm.lean`) is likewise a FUNCTION of route-side data throughout — the two seed legs' and two arms' route-indexed logs, and the merge's log on the route's OWN three candidates (the arms' values, not numerals) — with the interior's log carried as a PARAMETER. No literal total derived yet. Does NOT discharge the row. | Open. RESIDUAL GAP RAISED THIS ROUND, needs coordinator adjudication before this row can close as frozen: the INTERIOR leg computes `Nat.log2 count` and `bpSparseLogSpan count = 2 ^ Nat.log2 count` for a RUNTIME-derived `count` (`InteriorDirectory.lean:2112-2142`, `SparseArgMin.lean:598-599`), and `level` feeds the accepted read address (`LocalGlobalSparse.lean:200-202`), so it cannot be routed around. The existing ISA CAN compute it (halving/doubling by the constant `2`), so this is not an expressiveness obstruction — but the loop has NO literal all-size iteration cap, contradicting conjunct (c) "an all-size literal `totalSteps <= <literal>` ... no size hypothesis". Options and a recommendation are in `E1_WORKLOG.md` M3d-3 section 2. This is a structural finding with exact file:line, NOT a checked non-existence theorem. |
| REQ-E1-07 | "state the amended target Prop (`E1AmendedFamiliarMachineTarget` or similar), prove it via your construction, and add a short design-decision + doc note relating it to the refuted `E1R3FamiliarMachineTarget`: the old target's per-position clause is now satisfied VACUOUSLY-FREE (the route has no per-position scan; the chunk loop is charged per iteration with a literal iteration cap) — make the relationship precise, do not hand-wave." | Local+roadmap | An explicit Prop bundling: existence of a machine + program with one-step-per-instruction charging, width accounting, result agreement, positional receipt projection, invalid guard, category accounting, and the derived literal bound; a checked theorem proving it by exhibiting the construction; a DD entry + doc note stating precisely which clause of the refuted R3 target failed (the unbounded event-silent scan made the per-position charge bound unsatisfiable) and why the amended route eliminates the clause's domain (no per-position scan exists; every loop is a chunk fold with literal cap 33/8, each iteration charged as one read + bounded register steps). | Roadmap join: E1 rung closure feeding A07 blind audit; supersession note consumed by `docs/PAPER_MODEL_ADEQUACY.md` and DESIGN_DECISIONS. | The Prop must quantify like the public claims (all shapes/sizes, all valid queries), not a singleton demo; the supersession note must cite the exact obstruction identifier and commit, and must NOT claim the old target is proved — it is superseded; conflating refutation-of-old with proof-of-new fails the row. | Not started. CORRECTION RECORDED FOR THE SUPERSESSION NOTE: the planned wording "every loop is a chunk fold under a literal cap" is FALSE as written. The per-position clause of the refuted R3 target is indeed void (no branch of the accepted route performs a per-position scan), but the interior leg's `Nat.log2`/`bpSparseLogSpan` computation is a loop that is neither a chunk fold nor literally capped — see the REQ-E1-06 residual gap. The note must state this rather than assert the stronger claim. | Open |
| REQ-E1-08 | "Production validator (INV-VALIDATION-REACH): an executable (lakefile target) that RUNS the machine on deterministic fixtures — empty, singleton, size-two, same-block, threshold-boundary, cross-interior, invalid, plus generated cases — comparing against an independent half-open leftmost `List Int` reference implementation (write the expected values independently, not from the machine); checks result/read-projection/step-count correspondence and no-synthetic receipts; and includes at least one deliberate machine mutation that the validator verifiably rejects. Report modeled steps separately from wall-clock." | Local | A new `lean_exe` lakefile target; validator source following `Validation/` patterns; fixture list covering the named cases + generated cases; an independent reference RMQ (naive half-open leftmost scan over `List Int`, written directly against the semantics, not calling the machine or the succinct route); checks: machine result = reference result, machine read projection = accepted trace, machine step totals = category sums, machine literal bound honored, mutation rejected (exit-code-visible failure on the mutated machine, un-mutated run green); output separates modeled step counts from wall-clock ms. | INV-VALIDATION-REACH; chain: compiled validator -> machine `run` -> comparisons -> process exit code. | The mutation must be in the MACHINE (program or step semantics variant), not in the fixtures; the reference implementation must not import the machine or succinct modules' answers (independence audit: it may share only `List Int` and basic prelude); a validator that derives expected values by calling the machine passes trivially and fails the row. | Partial (component). `rmq_e1_machine_validate` RUNS the machine (before it, `E1Machine.run` had no caller in the tree). M3d-7 adds phase 3e: 36 merge fixtures compared against `refMerge3` (`RMQ/Validation/E1MachineValidate.lean:801`), an INDEPENDENT reference written from the specification that deliberately does not share the route's structure -- the route is a left-associated pairwise fold of option-lifted merges, `refMerge3` flattens then folds once -- so agreement checks the association and the tie-break rather than restating them; expectations computed BEFORE any machine run; value grids overlap so ties occur in both directions. `mergePathCoverage` (`:926`) = 6 confirms all six control paths are exercised. Phase 4d RAISES the mutation bar rather than reusing it, and the reason is recorded honestly: the merge is read-free, so receipt diffing -- which catches every earlier mutant, including 4c's mutant B -- is UNAVAILABLE here. Mutant D (`mutatedMergePosition:888`) changes ONE source operand, preserves length, opcode categories and control flow exactly, and `mergeMutantDIsValueOnly` (`:948`) CHECKS case-for-case that its exit pc, modeled steps and receipt all match the honest sweep; only the independent-reference value rejects it (8 mismatches). Figures modeled and wall-clock separated: `mergeModeledSteps=431`, `mergeModeledReads=0`, `mergeWallClockMs=1`. THE WHOLE-QUERY HOLE IS UNTOUCHED and still reports `OPEN (interior leg blocked; NOT a pass)`. M3d-9 ADDS A THIRD DISCRIMINATOR, phase 3h/4g, because neither existing one has any power over a mutation that computes the right answer, does the right reads, in the right number of steps, and merely scribbles on a register it does not own — precisely the defect class this session's headline theorem (`fringeArm_runsTo`'s preservation clause) excludes. Phase 3h checks the clause by execution: 66 registers, 36 fixtures, `presFailures=0`, `presClobberedRegs=[]`. THE SENTINEL SEEDING IS LOAD-BEARING and stated as such: from a zero-seeded register file the phase is VACUOUS, since a block that zeroes a register it does not own still "preserves" it; `presSentinel r = r*7+3` is injective and nowhere zero. Each fixture is also re-run zero-seeded and compared (`presSeedDisagreements=0`), which doubles as evidence the arm reads no register it does not initialise. MUTANT G renames the epilogue's private scratch register from `fT` (60) to 70 consistently: identical value, position, step count, control path and (empty) epilogue receipt, with `mutantG_isPreservationOnly=true` checking that case for case, and `mutantG_clobberedRegs=[70]` — which in the cross layout is `fClose`, the query operand both right-hand preambles read. Complementarity is now EXECUTED in three directions: D value-only, E receipt-only, G preservation-only. Does NOT discharge the row (whole-query scope). | Open |
| REQ-E1-09 | "This discharges, at machine level, the 'documentary uncharged omissions' list in PAPER_MODEL_ADEQUACY.md — after this rung that list should be empty or reduced to an explicitly-argued residue; update the doc section accordingly." Plus the bookkeeping: "fix the four stale 'fresh segment 21' public surfaces (`README.md:94`, `docs/WHAT_IS_PROVED.md:14` and `:95`, `artifact/CLAIMS.md:68`, `docs/PAPER_MAIN_THEOREM.md:60` — the checked counterfactual is segment 23 since B3); fix the 33-cap file attribution in `PAPER_MODEL_ADEQUACY.md`; clean the unused-simp-arg warnings at `SuccinctFinalRAM.lean:5694-5824` if cheap (warnings only — skip if it risks churn)." | Public surface | Doc edits: PAPER_MODEL_ADEQUACY charge-policy section updated to state that the E1 machine now charges each enumerated uncharged item, with any residue explicitly argued; stale segment-21 doc lines corrected to segment 23 (checked object: `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.segment = 23`, `SuccinctFinalRAM.lean:6788`); 33-cap attribution corrected (33-cap identity lives in `ChargedFringeChunks.lean`; `ChargedWordChunks.lean`/`ChargedTableRegime.lean` carry the 8-per-word cap and regime identities); simp-arg warnings cleaned or explicitly skipped with reason. `claim_drift_scan.ps1` + `paper_topology_lint.ps1` exit 0. | Public doc surface; chain: machine theorems -> adequacy doc claims. | Doc text must not overclaim: the machine is a refinement target, not a wall-clock claim (framing preserved); the uncharged-list update must cite the actual checked machine theorems, not aspirational ones. | — | Open |
| REQ-E1-10 | Process: "freeze a NEW acceptance matrix ... FIRST in its own commit"; "Maintain `docs/internal/E1_WORKLOG.md` per milestone; DD entries for ISA/encoding/program-representation choices; never yield with uncommitted work unless a committed recovery patch is refreshed first (`git diff > docs/internal/E1_WIP.patch`, commit it, delete when superseded)." | Process | Git history: this matrix commit precedes all E1 implementation commits; worklog updated at each milestone commit; DD entries exist for ISA choice, instruction encoding, and program representation; recovery-patch discipline followed on any yield with uncommitted work. | Coordinator audit of branch history. | `git log` order check at final report. | — | Open (matrix frozen this commit) |
| REQ-E1-11 | "RULES (standing): no sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib; library green at every commit; no weakened closed B2/B3/B4 rows; no renamed/deleted frozen public identities; no asserted constants; no dead sources; no sibling public query; the machine is a refinement target, not a wall-clock claim — keep that framing in all docs." | Inherited hygiene + process | Per-commit `lake build RMQ` (or full-root equivalent) green, recorded in the worklog ledger; hygiene `rg` shows no NEW hits in touched files; no closed B2/B3/B4 matrix row weakened (their theorem statements untouched or only strengthened); frozen public identities preserved; all literals derived; the machine consumes the accepted route rather than defining a sibling public query surface. | All touched modules; coordinator audit. | Deliberate check: the E1 machine module must not export a second `query`-shaped public surface competing with `SuccinctClassic.query`; docs framing check for wall-clock claims. | — | Open |

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

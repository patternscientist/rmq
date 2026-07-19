# E1-R4 Worklog (amended familiar-machine rung)

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062` (B4 candidate,
coordinator-reconstructed). Contract: E1-R4 delegation prompt; frozen matrix
`docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`.

## M0 (this commit): matrix freeze

- Read the mandated contract sources: `OPTION_B_CHARGED_FRINGE_DESIGN.md`,
  `PAPER_MODEL_ADEQUACY.md` (charge policy), the closed
  `B2_CHARGED_FRINGE_ACCEPTANCE_MATRIX.md` rows, `SKILL.md` +
  `COMPLETION_GATE.md`, DD-20260717-C05-001.
- Verified anchors at `d90b062`: `queryCost_eq : queryCost = 207`
  (`SuccinctRMQClassic.lean:111`), `..GlobalWordTraceResult_readWord_only`
  (`SuccinctFinalRAM.lean:9479`), fresh counterfactual segment = 23
  (`SuccinctFinalRAM.lean:6788`), 33-cap in `ChargedFringeChunks.lean`,
  8-cap in `ChargedWordChunks.lean:39` + `ChargedTableRegime.lean`.
- Froze the acceptance matrix (REQ-E1-01..11 + inherited INV subset + CHK
  battery) in this commit, before any implementation.
- Process note: the host process restarted during the initial session before
  any commit; the coordinator directed matrix-freeze-first on resume and
  early/frequent commits. No work was lost (nothing had been committed; the
  in-context read state was reconstructed from the same tree).

## M1: bookkeeping repairs (C05 round-4 audit queue)

- Fixed the stale "fresh segment 21" counterfactual mentions on the public
  surfaces (the checked object is
  `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.segment = 23`,
  `SuccinctFinalRAM.lean:6788`, since B3 added live segment 22): README.md
  (2 lines), docs/WHAT_IS_PROVED.md (3 lines), artifact/CLAIMS.md (1 line),
  docs/PAPER_MAIN_THEOREM.md (1 line), docs/PAPER_MODEL_ADEQUACY.md (1 line,
  same staleness class, found during the fix sweep).
- Fixed the 33-cap file attribution in PAPER_MODEL_ADEQUACY.md: the 33-cap
  identity is checked in `ChargedFringeChunks.lean`; `ChargedWordChunks.lean`
  / `ChargedTableRegime.lean` carry the 8-per-word cap and regime identities.
- SKIPPED (sanctioned by delegation "skip if it risks churn"): the
  unused-simp-arg warnings at `SuccinctFinalRAM.lean:5694-5824`. Reason:
  warnings only; editing the 9k-line kernel-heavy module forces a
  world-rebuild verification mid-rung for zero semantic gain, exactly the
  churn risk the delegation names. No Lean source touched in M1.
- Verification: doc-only commit (library unaffected); `claim_drift_scan.ps1`
  + `paper_topology_lint.ps1` run at this commit (results in ledger).

## M2: machine core (`RMQ/Core/WordRAM/E1Machine.lean`)

- New module `RMQ.WordRAM.E1Machine`: 12-constructor atomic ISA (readMem,
  const, move, add, sub, mulConst, divConst, natLt, natLe, natEq, brNZ,
  halt), six frozen charge categories, single non-recursive `execInstr`
  match, fueled `run` (only recursion, on the fuel counter), option-shift
  read decode `decodeRead` (none -> 0, some w -> bitsToNatLE w + 1).
- Checked core lemmas: `run_steps_eq_catLog_length` (one step per
  executed instruction), `catCount_partition` + `run_steps_eq_category_sum`
  (six categories partition the total), `execInstr_readCount_eq_
  memoryRead_indicator` + `run_readLog_length_eq_memoryRead_count` (reads
  charged one-for-one, only readMem emits), `run_readLog_readWord_shape`
  / `_matchesReadStore` / `_no_syntheticCostOnlyPrimitive` (receipts are
  genuine store reads), `run_add` (fuel composition backbone),
  `run_steps_le_fuel`, `run_stuck`, `step_some` inversion.
- Width accounting (REQ-E1-02 machinery): constructor-exhaustive
  `Instr.FieldsFit` (no wildcard arm), `ProgramFits`, 12 kernel-checked
  oversizing/zero-divisor rejection witnesses `fieldsFit_rejects_*`.
- DD-20260718-005 records the ISA inventory decision (no general
  mul/div/mod: all route multipliers/divisors are per-shape program
  constants; mod = sub/div/mul-const composition), the decode choice, the
  frozen categories, and the rejected alternatives.
- Wired into the root: `import RMQ.Core.WordRAM.E1Machine` in `RMQ.lean`.
- Verification at this commit: standalone `lake env lean` on the new
  module exit 0; `lake build RMQ` (ledger below); hygiene rg on touched
  files clean.
- REQ-E1-01/02 status: machinery delivered; rows CLOSE only when the
  concrete program consumes them (M3+), per the matrix consumer chains.

## M3a: program-composition calculus (`RMQ/Core/WordRAM/E1MachineCalculus.lean`)

- `HostedAt program base code` (absolute-base block hosting) with
  `hostedAt_self`, `.head`, `.tail`, `.append_left`, `.append_right`.
- `RunsTo store program s s' reads cats` exact-fuel big-step relation
  (fuel = cats.length, consumed exactly): `RunsTo.refl`, `RunsTo.trans`
  (via `run_add`), generic `RunsTo.step`, one mechanical rule per
  instruction constructor (readMem/const/move/add/sub/mulConst/divConst/
  natLt/natLe/natEq/brNZ/halt), and fuel insensitivity after halt
  (`RunsTo.run_fuel_ge` / `.run_of_le_fuel`) so the machine outcome is
  well defined for any sufficient fuel budget.
- Machine-generic; nothing route-specific. Verification: standalone
  `lake env lean` exit 0; `lake build RMQ` green; hygiene clean.

## M3b-1: query skeleton + charged invalid guard (REQ-E1-05 machine half)

- New module `RMQ/Core/WordRAM/E1QueryProgram.lean`
  (`RMQ.WordRAM.E1Query`): frozen register map (inputs 0/1, packet 2,
  pinned zero 3, size constant 4, guard scratch 5-7, components from 8),
  option-shift output packet `decodePacket` (mirrors `decodeRead`),
  `guardBlock`/`invalidExitBlock`/`programSkeleton n validPath` (guard at
  base 0, valid path at 8, invalid exit at `8 + validPath.length`,
  reachable only via the guard branches), hosting lemmas, constructor-
  exhaustive width lemmas (`guardBlock_fits`, `invalidExitBlock_fits`,
  `programSkeleton_fits`), and the charged rejection theorems
  `guard_reject_of_not_lt` (exact 8-step log `guardRejectRangeCats`),
  `guard_reject_of_out_of_bounds` (exact 10-step log
  `guardRejectBoundsCats`), `guard_reject_of_invalid`,
  `programSkeleton_reject_of_invalid` - all with EMPTY receipt log and
  zero memoryRead category, guard computed by machine natLt/natLe/natEq/
  brNZ on the input registers (anti-vacuity: no meta-level guard).
  Kernel-checked fixtures: empty `[0,0)` on n=0, reversed `[3,2)` and
  out-of-bounds `[0,9)` on n=5 (regOut=0, readLog=[], steps=8/10, exact
  category logs by `rfl`).
- New module `RMQ/Core/WordRAM/E1QueryBridge.lean`: REQ-E1-05 public
  parity `programSkeleton_invalid_matches_public_guard` - decoded packet
  = `(SuccinctClassic.queryCosted xs left right).value`, machine receipt
  log = accepted invalid trace (both `[]`, positional), memoryRead count
  = accepted invalid cost (0) - plus empty/reversed/out-of-bounds
  specializations against `queryCosted_invalid`.
- DD-20260718-006 records the register map, packet encoding, skeleton
  layout, and rejected alternatives (completes the program-representation
  decision deferred by DD-20260718-005).
- Both modules wired into `RMQ.lean`. Guard lemmas are `HostedAt`-generic
  so valid-path landing will not touch them.
- REQ-E1-05 status: machine + public-parity theorems landed; the row
  CLOSES after the validator exercises the invalid fixtures (M6).
- Verification at this commit: `lake env lean` exit 0 on both new
  modules; `lake build RMQ` green (ledger below); hygiene rg clean on
  touched files.

## M3b-2: whole-query positional trace decomposition (route inventory)

- New module `RMQ/Core/WordRAM/E1RouteDecomposition.lean` (namespace
  `RMQ.SuccinctFinal`): checked positional decomposition of
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` into its
  component traces, one theorem per control branch of the closed
  five-instruction program:
  - `..._decompose_of_selects_lca_some`: trace = select(left) ++
    select(right-1) ++ allSizeStructural LCA ++ rankCloseAtSegment
    (answerClose+1); value = some (rankValue - 1);
  - `..._decompose_of_lca_none`: three-leg trace, value = none;
  - `..._decompose_of_left_select_none` / `..._decompose_of_right_select_none`:
    two-leg trace, value = none.
- These are the interfaces the machine simulation targets component by
  component (REQ-E1-03/04): result agreement and positional receipt
  equality reduce to per-component machine lemmas composed with
  `RunsTo.trans`, glued by these route-side equalities.
- Verification at this commit: `lake env lean` exit 0 (no warnings);
  `lake build RMQ` green.

## M3b-3: chunk-loop composition backbone

- `RunsTo.iterate` + `iterLog` appended to
  `RMQ/Core/WordRAM/E1MachineCalculus.lean`: generic counted-loop
  composition (invariant indexed by remaining iterations, one `RunsTo`
  segment per iteration with iteration-indexed receipt/category
  functions), so exact positional receipts survive brNZ-back-edge loop
  composition.  This is the backbone for the 33-cap fringe window folds
  and 8-cap word-chunk folds.
- Verification at this commit: `lake env lean` exit 0 on the module;
  `lake build RMQ` green.

## M3c-1a: rank fold bridge lemmas (`RMQ/Core/WordRAM/E1RankBridge.lean`)

- New module `E1RankBridge.lean` (wired into `RMQ.lean`): the div-mod-by-
  constant bridge layer the rank-close machine block consumes.
  - Little-endian decode bridges: `bitsToNatLE_drop` (`/ 2^k`),
    `bitsToNatLE_take_add_drop` + `bitsToNatLE_take` (`% 2^k`),
    `bpFringeWindowChunkValue_eq_div_mod` (the fold's window chunk value
    IS the machine's `W / 2^(j*c) % 2^c` register expression),
    `div_pow_chunk_succ` (remaining-word register update `R / 2^c`).
  - Truncated-subtraction machine forms: `nat_min_eq_sub_sub`,
    `nat_mod_eq_sub_div_mul`, `bpWordChunkSliceLen_eq_sub`,
    `bpWordChunkCount_eq_sub`, `bpWordRankEffLimit_eq_of_le`,
    `bpChunkRankOfEntry_false_eq` (in-chunk rank decode as literal
    div/mul/sub chain).
  - Option-shift decode bridges: `decodeRead_pred_eq_map_getD`
    (machine register minus one = fold's `getD 0` decode),
    `decodeRead_eq_zero_iff`, `decodeRead_some_eq`.
  - Positional fold shape: `bpWordRankChunkSlotAt`/`bpWordRankChunkEventAt`
    (per-chunk slot/event), `bpChunkedWordRankTraceFromWithStore_trace_map`
    (fold trace = ascending `List.range`-indexed read list),
    `bpWordRankAccAt` + `bpChunkedWordRankTraceFromWithStore_value_accAt`
    (fold value = literal iterated accumulator - the machine loop
    invariant's register content).
  - `iterLog` combinators: `iterLog_congr`, `iterLog_singleton_desc`
    (descending-counter receipts = ascending `List.range` order),
    `iterLog_const_length`, `catCount_iterLog_const`, `catCount_append`.
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean on the new file.

## M3c-1b: straight-line executor + rank-close block simulation

- New module `RMQ/Core/WordRAM/E1StraightLine.lean` (machine-generic,
  wired into `RMQ.lean`): `Instr.isStraight`, per-instruction effect
  functions `straightStepRegs`/`straightStepEvent`, segment folds
  `straightRegs`/`straightReads`, and `RunsTo.straight` - one lemma runs
  ANY hosted branch-free code segment with computed registers, receipts,
  and one category tick per instruction (`code.map Instr.category`).
  Plus `Instr.writesTo` + `straightRegs_preserves` (registers outside a
  segment's write set are untouched) and `RunsTo.brNZ_taken`/`_not_taken`.
  This kills the hand-written state-tower style for long blocks: register
  values are computed by `simp` symbolic evaluation at query sites.
- New module `RMQ/Core/WordRAM/E1RankBlock.lean` (wired into `RMQ.lean`):
  the rank-close component block and its hit-path simulation.
  - Frozen register bank (8..27, doc-commented), segments `rankSeg1`
    (constants, min-clamp, word/super index + offset arithmetic, THREE
    seed reads, first zero test), `rankSeg2`/`rankSeg3` (zero tests),
    `rankSegInit` (option shift, cursor/acc zero, 8-capped count by
    subtraction chain), `rankLoopBody` (24 instrs: slice length by
    truncated sub, window chunk value by div/mod-2^c, slot affine form,
    chunk-table read, `bpChunkRankOfEntry` decode chain, accumulate),
    `rankSegFin`, `rankMissSeg`; `rankCloseBlock B G c L WS BPS`
    (60 instructions, branch targets absolute from `B`).
  - Frozen category logs `rankHitHeadCats` (30) / `rankLoopPassCats` (25)
    / `rankHitTailCats` (4); `rankCloseHitCats count` with DERIVED length
    `34 + 25 * count` (`rankCloseHitCats_length`).
  - `rankCloseBlock_hosting` (hosting peel), straightness certificates,
    `rankCloseBlock_prologue_runsTo` (entry -> loop entry: exactly the
    three seed-read receipts, `rankHitHeadCats`, decoded registers),
    `rankCloseBlock_loop_runsTo` (`RunsTo.iterate` with invariant carrying
    remaining word `W / 2^(j*c)`, cursor `j*c`, accumulator
    `bpWordRankAccAt`, counter; receipts = ascending fold reads),
    and the component theorem `rankCloseBlock_runsTo_hit`:
    for ANY hosting program, store presenting the three seed reads, and
    `wordOffset <= word.length`, the block runs with exact fuel to
    `B + 60` with receipts POSITIONALLY EQUAL to
    `(d.bpChunkedRankTraceResultWithStore store G (G+1) (G+2) (G+4) c
    false pos).trace`, the component's `.value` in `rVal`, frozen cats
    `rankCloseHitCats (bpWordChunkCount c (d.wordOffset pos))`, and all
    registers outside the component bank preserved.
- Verification at these commits: standalone `lake env lean` exit 0 (no
  warnings after unused-simp-arg cleanup); `lake build RMQ` green;
  hygiene rg clean on the new files.

## M3c-1c: rank-close block at the accepted component (canonical instantiation)

- New module `RMQ/Core/WordRAM/E1RankCanonical.lean` (wired into
  `RMQ.lean`): `rankCloseBlock_runsTo_atSegment` - for EVERY shape,
  EVERY base, and EVERY position (no sampling, no readiness guards), the
  hosted rank-close block runs against
  `concreteBPNativeChunkedRankCloseSeedReadStore shape rankSegmentBase`
  from block entry to `B + 60` with receipts POSITIONALLY EQUAL to
  `(concreteBPNativeRankCloseWordTraceResultAtSegment shape
  rankSegmentBase (regs0 rPos)).trace`, the component's `.value` in
  `rVal`, the frozen `rankCloseHitCats` category log, and all registers
  outside the component bank preserved.
- Hypothesis discharge is entirely route-side: presence of the three
  seed reads from `super_present`/`block_present`/`word_present` plus
  `FixedWidthNatTable.read_exact` (entries-present -> word-present), and
  the offset bound `wordOffset pos <= word.length` from the sentinel-
  chunked store's index characterization
  (`builtRankData_wordOffset_le`, via
  `chunkPayloadWords_get?_eq_take_drop` for full chunks and the
  `length_eq_div_add_indicator` boundary argument for the sentinel row -
  the sentinel is reachable only at an exact top boundary where the
  offset is zero).
- The rank-close leg of the M3c inventory is now fully simulated
  machine-side.  Remaining for glue: swap the seed store for the
  canonical global store at base 17
  (`concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq` +
  the block theorem's store genericity re-instantiated at
  `concreteBPNativeSuccinctRMQGlobalReadStore` with the
  `_rankCloseSuper/Block/Word/fringeChunkTable` agreement lemmas).
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean.

## M3c-2a: rank-close canonical-store glue, width certificate, macro lift

- Lifted the symbolic-evaluation macros into `E1StraightLine.lean` as
  `straight_eval [...]` / `straight_writes [...]` (the simp-arg splicing
  that the M3c-1b gotcha reported as failing works when the extra
  arguments are parsed as `Lean.Parser.Tactic.simpLemma,*` and spliced
  with `$args,*`; the earlier failure was a different formulation).
  `E1RankBlock.lean`'s `local` macros are now thin wrappers naming the
  block's segments/registers; all inherited proofs unchanged.
- `rankCloseBlock_fits` (`E1RankBlock.lean`): constructor-exhaustive
  REQ-E1-02 certificate for the 60-instruction block ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â register bank,
  segments `G..G+4`, immediates, mul/div constants
  (`WS`/`BPS`/`2^c`/`c+1`/`2*c+2`/`2`, variable divisors positive ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â `c`
  needs the route's `bpFringeChunkBits_pos`), branch targets
  `< 2^w` given `28 <= 2^w`, `G+4 < 2^w`, `L < 2^w`, `0 < c`,
  `0 < WS < 2^w`, `0 < BPS < 2^w`, `2^c < 2^w`, `2*c+2 < 2^w`,
  `B+60 < 2^w`.  (Flattening gotcha: `List.mem_append` leaves the
  disjunction grouped per segment; add `or_assoc` to the simp set before
  the 60-way `rcases`.)
- `rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean`): the M3c
  store-swap glue ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â for every shape/base/position the hosted block runs
  against `concreteBPNativeSuccinctRMQGlobalReadStore shape` (base
  `concreteBPNativeRankCloseTraceSegmentBase` = 17) with receipts
  POSITIONALLY EQUAL to
  `(concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
  pos).trace`, value in `rVal`, frozen `rankCloseHitCats`, outside
  registers preserved.  Machine store and component store are the SAME
  argument.  Presence via the `_rankCloseSuper/Block/Word` agreement
  lemmas (`superSampleWords false` reduces definitionally to the
  false-table words), offset bound via `builtRankData_wordOffset_le`,
  chunk segment aligned by `17 + 4 = 21 = fringeChunkTraceSegment` (rfl).
- Verification at this commit: standalone `lake env lean` exit 0 on the
  three touched modules (no warnings); `lake build RMQ` green; hygiene
  rg clean on touched files.

## M3c-2b: early-exit loop backbone (`RunsTo.iterateUntil`)

- Appended to `E1MachineCalculus.lean`: `iterUntilLog` (execution-ordered
  early-exit log: per-counter exit decision function `exits`, continuing
  log, exit log, exhaustion log) with `_zero/_succ/_succ_of_exits/
  _succ_of_continues`, and `RunsTo.iterateUntil` (invariant `P k s`, exit
  predicate `Q`, per-step alternative continue/exit decided by
  `exits k` - a FUNCTION of the remaining counter, so receipts/cats stay
  fixed functions of the initial counter - plus the counter-0 exhaustion
  segment).  Machine-generic.
- NOTE: the select-fold simulation below ended up using direct induction
  on the fold's own recursion instead (receipts/cats are naturally
  fold-shaped, so no descending->ascending log flip is needed);
  `iterateUntil` remains available for loops whose spec is not already a
  recursion (e.g. LCA-leg folds if their evaluator shape differs).

## M3c-3a: in-word select fold block (`E1SelectBlock.lean`)

- Select-close inventory (the M3b-2 gap): the accepted component is
  `concreteBPNativeChunkedSelectCloseGlobalWordTraceResult =
  (sparseExceptionSelectData shape.bpCode false)
  .bpChunkedSelectTraceResultWithStore
  concreteBPNativeSelectCloseTraceSegmentLayout 21 22 globalStore c idx`
  (`ChargedRankSelectWiring.lean:645`, evaluator
  `ChargedRankSelectLeafTrace.lean:1157`).  Control branches: (i) idx out
  of occurrence range -> pure none; (ii) super entry-table read (4 accepted
  relabeled `readWord`s via `readTraceResultRelabeledWithStore`), none ->
  none; (iii) marked super -> LONG leg: chunked rank fold (target TRUE,
  seeds at `layout.longFlagRankBase..+2`, chunks at 21) then one relative
  read; (iv) local entry-table read (4 reads), none -> none; marked local
  -> SPARSE leg: `sparseDirectory.bpChunkedReadTraceResultWithStore`
  (true-rank fold + relative read); else DENSE leg
  (`bpChunkedDenseTwoWordSelectTraceResultWithStore`,
  `ChargedRankSelectLeafTrace.lean:575`): word read, TWO true/target rank
  folds (at `firstOffset` and full length), then the early-exit select
  fold on the first word, or a second word read + select fold.  The
  in-word select fold `bpChunkedWordSelectTraceFromWithStore`
  (`ChargedRankSelectTrace.lean:322`) is the early-exit core; slot forms:
  routing read at `bpFringeChunkSlot c v t t`, select read at
  `bpChunkSelectSlot c v k = v*(c+1)+k`; the dense select fold runs at
  the data's target = FALSE; the long/sparse rank folds run at target =
  TRUE (their value decode differs from `rankCloseBlock`'s false chain by
  dropping the final `t -` subtraction; receipts are target-independent).
- New module `RMQ/Core/WordRAM/E1SelectBlock.lean` (wired into
  `RMQ.lean`): the 36-instruction `selectFoldBlock LB R S c` (loop head
  22 instrs; exit brNZ at LB+22 -> exit tail LB+30..35; continue tail +
  back edge LB+23..26; exhaustion tail LB+27..29), frozen bank `9..27`
  aligned with the rank bank where roles coincide, frozen per-pass
  category logs (`selContPassCats` 27 / `selExitPassCats` 29 /
  `selExhaustCats` 3), route-side decoded-rank function `selChunkRankAt`,
  DERIVED whole-run category log `selectFoldCats` mirroring the fold's
  exit recursion with checked bound `selectFoldCats_length_le`
  (`<= 27*count + 3`), width certificate `selectFoldBlock_fits`
  (constructor-exhaustive, no variable divisors beyond the outright-
  positive `2^c`/`c+1`/`2*c+2`/`2`), hosting peel, and the simulation
  theorem `selectFoldBlock_runsTo`: for ANY hosting program, store, word,
  `count >= 1`, cursor/occurrence state in the bank, the block runs with
  exact fuel from `LB` to `LB+36` with receipts POSITIONALLY EQUAL to
  `(bpChunkedWordSelectTraceFromWithStore store R S c false word j count
  k).trace`, `decodePacket (regsF sVal) = (...).value`, cats
  `selectFoldCats`, and all registers outside the fold bank preserved.
  Early exit decided by machine `natLt`/`brNZ` on the machine-decoded
  chunk rank (no meta-level guard).  Proof: direct induction on `count`
  mirroring the fold (exit pass / continue-exhaust / continue-IH), each
  pass via `RunsTo.straight` + the shared `straight_eval` macro.
- Technique notes: preservation-helper hypotheses must be stated on
  register NUMERALS (`r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  22`), not the abbrevs (`r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  sA`) - omega does
  not unfold abbrevs in hypotheses; `rw` auto-closes refl goals (no
  trailing `rfl` after preservation chains); the packet-value goal needs
  an explicit `X + j*c + 1 = j*c + X + 1` commutation before
  `decodePacket_succ`.
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean.

## M3c-4a: TRUE-target rank block (`E1RankTrueBlock.lean`)

- New module `RMQ/Core/WordRAM/E1RankTrueBlock.lean` (wired into
  `RMQ.lean`): mechanical clone of `E1RankBlock` for the TRUE-target
  seeded component `d.bpChunkedRankTraceResultWithStore store G (G+1)
  (G+2) (G+4) c TRUE pos` (select-close long/sparse legs).  Deltas
  exactly as planned: shared segments re-used (NOT cloned) from
  `E1RankBlock` (`rankSeg1/2/3`, `rankSegInit`, `rankSegFin`,
  `rankMissSeg`, head/tail cats, register bank); new 23-instr
  `rankTrueLoopBody` (false body minus `.sub rA rT rA`; decode ends at
  `/2` per `bpChunkRankOfEntry_true_eq`); 59-instr `rankTrueCloseBlock`
  (loop B+30..52, back edge B+53, epilogue B+54..56, exit jump B+57 ->
  B+59, miss B+58); 24-long `rankTrueLoopPassCats`; derived
  `rankTrueCloseHitCats_length : 34 + 24 * count`.  Theorems:
  `rankTrueCloseBlock_hosting`, `rankTrueCloseBlock_prologue_runsTo`,
  `rankTrueLoopFold_runsTo` (stated at a GENERIC loop base `LB` so the
  select legs can host the fold anywhere; ends `LB+24`),
  `rankTrueCloseBlock_runsTo_hit` (receipts positionally equal to the
  component trace, value in `rVal`, frozen cats, outside-bank
  preservation), width certificate `rankTrueCloseBlock_fits`
  (constructor-exhaustive, 59 arms, branch targets `B+30/B+58/B+59`).
- Technique delta discovered: with a generic loop base the invariant's
  pc equation `hpc : pc = LB` has a BARE-VARIABLE RHS, and `subst hpc`
  eliminates `LB` (not `pc`), breaking later explicit `LB` references ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â
  use `subst pc` to force the direction.  (The false block never hit
  this because its RHS `B + 30` is not a variable.)
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green (only the pre-existing
  `SuccinctFinalRAM`/reachability simp-arg warnings listed in
  REQ-E1-09).

## M3c-4b: atomic in-word rank fold block (`E1RankAtBlock.lean`)

- New module `RMQ/Core/WordRAM/E1RankAtBlock.lean` (wired into
  `RMQ.lean`): the seed-free FALSE-target fold sub-block the dense
  two-word select leg consumes twice
  (`bpChunkedWordRankTraceResultAtSegmentWithStore store (G+4) c false w
  limit`).  Pieces: `rankFalseLoopFold_runsTo` (the shared
  `rankLoopBody` loop re-proved at a GENERIC loop base `LB`, end
  `LB+25`, preservation widened to the exact write-set complement
  `r <= 8 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 10 <= r <= 16 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 24 <= r <= 26 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 <= r` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the dense leg
  must keep `rWrd`/samples across a fold); 32-instr
  `rankAtSegmentBlock A G c` (7-instr register-input init `A..A+6`,
  loop `A+7..A+30`, back edge `A+31`); frozen `rankAtSegmentCats`
  (derived `7 + 25 * count`); `rankAtSegmentBlock_runsTo` (inputs: rOne/
  rC/rEight pinned, `rE = bpWordRankEffLimit w limit`,
  `rR = bitsToNatLE w`; receipts positionally equal to the atomic fold
  trace, value in `rVal`); width certificate `rankAtSegmentBlock_fits`
  (32 arms, branch target `A+7`).
- Technique: init-only preservation hypotheses must ALSO be stated on
  register numerals (`r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  22 ÃƒÂ¢Ã‹â€ Ã‚Â§ ...`), instantiated with `(by decide)` at
  abbrev call sites ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â same omega-opacity gotcha as loop preservation.
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green.

## M3c-5a: select-close read sub-blocks (`E1SelectBridge.lean`)

- New module `RMQ/Core/WordRAM/E1SelectBridge.lean` (wired into
  `RMQ.lean`): RESUME steps 2 and 3 - the entry-table 4-read sub-block
  and the relative-offset read sub-block, plus the route-side reductions
  they consume.
  - Route-side reductions (ALL `rfl` - the inventory's near-rfl
    prediction was exact): `ofProgramWithStore_natTable_trace/_value`
    (one relabeled fixed-width-table read = one `readWord` event at the
    mapped segment, value = `bitsToNatLE` decode of the supplied store's
    word), `entryRead_trace_eq`/`entryRead_value_eq` (the accepted
    4-read evaluator's trace = `entryFieldEvents` at the layout's four
    segments; value = `entryOfFields` over the four decodes),
    `relativeRead_trace_eq`/`relativeRead_value_eq`.
  - Decode connectors: `entryOfFields_decode_some/_decode_none` (entry
    presence in terms of the machine's shifted `decodeRead` registers),
    `missSum_eq_zero_iff`, `relativeSplitSelectEntryIsMarked_iff`
    (marked test = nonzero test on the `rankBefore` field).
  - Frozen EXTENSION BANK `28..39` (DD-20260718-007): `xIdx/xQ` 28/29,
    super fields `xSF1..xSF4` 30..33, local fields `xLF1..xLF4` 34..37,
    `xBPos/xBOcc` 38/39; shifted `decodeRead` field encode.
  - `entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4` (12 instrs: 4 readMems at
    slot index `rP` + miss-indicator sum via `rT/rA/rB`), frozen
    `entryReadCats`; `entryReadBlock_runsTo` - exact fuel to `A + 12`,
    receipts POSITIONALLY EQUAL to `entryFieldEvents`, the four shifted
    field decodes in the PARAMETRIC destination registers (side
    conditions `28 <= F`, pairwise distinct - one theorem serves the
    super and local instantiations), miss indicator in `rA`, write-set
    complement preserved; width certificate `entryReadBlock_fits`.
  - `relativeReadBlock A S` (4 instrs: read at `rSlot`, presence brNZ,
    packet add from `xBPos`), `relativeReadCats present`;
    `relativeReadBlock_runsTo` - exact fuel to `A + 4`, receipts = the
    accepted relative-offset read trace, the accepted value under
    `decodePacket` in `rT`, only `rT` written; width certificate
    `relativeReadBlock_fits`.
- Technique notes (parametric-destination variant of the numerals
  gotcha): disequalities for `RegFile.write` if-conditions must be
  provided in the CONDITION'S orientation (`(10 : Nat) ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  F1` for address
  preservation, `F1 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  F2` for later-write skips over the queried
  register) - derive them once by omega from the bank bounds and splice
  into the per-fact simp lists; the unused-simp-arg linter identifies
  the ones each fact does not need.  `HostedAt.tail.tail.head` type-
  checks directly at `A + 2` (literal successor additions are
  definitionally associated).
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean on the new file.

## M3c-5b: dense two-word leg, head block (`E1DenseSelectBlock.lean`)

- New module `RMQ/Core/WordRAM/E1DenseSelectBlock.lean` (wired into
  `RMQ.lean`): stage 1 of RESUME step 4 - the dense-leg HEAD
  `denseHeadBlock B M W G c WS N2` (84 instrs), everything up to and
  including the first-count compare.
  - Segments: `denseSegA` (word index `xBPos / WS` -> rP, word start ->
    rWI, local occurrence `xQ - xBOcc` -> rSI, packed word read at
    segment `W` -> rWrd), presence brNZ pair (miss exit to absolute
    target `M` - the leg's miss tail, stage 2), `denseSegB` (WORD-LENGTH
    MIN CHAIN `min WS (N2 - firstWordStart)` -> rBlk from the per-shape
    constants WS/N2, first effective limit -> rE, word decode -> rR),
    hosted `rankAtSegmentBlock (B+15) G c` (fold 1, limit firstOffset),
    `denseSegC` (save before -> rSup, second limit, decode reload),
    hosted `rankAtSegmentBlock (B+50) G c` (fold 2, limit word length),
    `denseSegD` (firstCount -> rVal, compare -> rA).
  - `denseHeadBlock_runsTo_present`: exact fuel to `B + 84`, receipts
    POSITIONALLY EQUAL to the word-read event :: fold1.trace ++
    fold2.trace (the accepted component calls verbatim), all branch
    inputs decoded in registers (rP/rWI/rSI/rBlk/rWrd/rSup/rVal/rA),
    frozen `denseHeadPresentCats n1 n2` (derived length
    `33 + 25*(n1+n2)`), pinned constants (24..26) and extension bank
    (28 <= r) preserved.  Route-side hypothesis `hlen : w1.length =
    Nat.min WS (N2 - xBPos / WS * WS)` - the dense store's word-length
    characterization, discharged at canonical instantiation (expect via
    `chunkPayloadWords_get?_eq_take_drop`-style take/drop lengths).
  - `denseHeadBlock_runsTo_miss`: absent word exits to `M` with exactly
    the read receipt, `denseHeadMissCats` (6), prologue write set only.
  - Width certificate `denseHeadBlock_fits` (delegates the fold arms to
    `rankAtSegmentBlock_fits`; needs `0 < WS`, `WS/N2/W < 2^w`,
    `40 <= 2^w`, `B + 84 < 2^w`, `M < 2^w`).
- Technique notes: the parametric-destination/effLimit goals mix abbrev
  and numeral spellings after simp - close min-chain goals by rewriting
  the ROUTE side (`simp only [bpWordRankEffLimit, nat_min_eq_sub_sub]`
  then `rw` the pre-derived `hlenChain`), never by omega (division
  products `xBPos / WS * WS` are nonlinear atoms to omega).  Concrete-
  register preservation instantiations must be `(by decide)`, variable-
  register ones `(by omega)` (M3c-4b gotcha, still biting).
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean on the new file.

## M3c-5c: dense two-word leg, tails + whole-leg theorem (STAGE 2 DONE)

- Appended to `E1DenseSelectBlock.lean` (now imports `E1SelectBlock`):
  the instruction-exact stage-2 layout below, implemented verbatim.
  - Segments: `denseTail2Pre W` (2: probe add + word read),
    `denseTail2Setup WS N2 c` (14: second word start, min-chain length
    into `rE` directly, `rSI := rSI - rVal`, decode, cursor, count
    chain), `denseTail1Setup c` (9: `rE := rBlk`, `rSI := rSup + rSI`,
    decode, cursor, count chain); `denseSelectLegBlock L W G S c WS N2`
    (193 instrs, layout exactly as planned: head at `L` with miss
    target `L+192`, compare brNZ `L+84`, second tail `L+85..142` with
    fold at `L+103`, first tail `L+143..191` with fold at `L+152`,
    miss tail `L+192`, END `L+193`).
  - Cats: `denseTail1SetupCats`/`denseTail2SetupCats` (+ rfl `_eq`
    lemmas vs `.map Instr.category`), `packetShiftCats : Option Nat ->
    List Category` (3 executed steps both ways), derived `denseLegCats`
    matching on `store.readWord?` at both word indices, the route-side
    rank `.value` compare, and the select-fold packet (selectFoldCats
    precedent - a function, never asserted).
  - `denseFoldShift_runsTo`: SHARED tail suffix lemma - hosted
    `selectFoldBlock` at `FB` plus the 3-executed-step packet shift at
    `FB+36..39` (both tails have identical relative layout), ending at
    absolute `E`; receipts = the accepted
    `bpChunkedWordSelectTraceResultAtSegmentsWithStore` trace; value
    under `decodePacket` = fold value shifted by `regs1 rWI`
    (word start); count positivity free from `bpWordChunkCount_eq_sub`.
  - `denseSelectLegBlock_runsTo`: the whole-leg theorem vs
    `GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore W
    (G+4) S c false bitWords store (regs0 xBPos) (regs0 xBOcc)
    (regs0 xQ)` - all four control branches (miss1 / first /
    second-miss / second) in one statement, receipts POSITIONALLY
    EQUAL per branch, value under `decodePacket` in `rVal`, cats
    `denseLegCats`, pinned constants + extension bank preserved.
    Route hypotheses `hlen1`/`hlen2` (word-length min chains) as
    per-word implications, discharged at canonical instantiation.
  - Width certificate `denseSelectLegBlock_fits` (delegates head +
    both folds; `first`-combinator over the 40 flattened arms).
- Gotchas discovered: the dense evaluator lives in namespace
  `RMQ.GenericSelect`, NOT `SuccinctClose` (an unresolved name in a
  theorem statement silently auto-binds as an implicit sort variable -
  watch for "Function expected at" + `?m` errors); `cases hv : X.value`
  substitutes into the goal, so no `rw [hv]` afterwards; the hosting
  peel through a 193-instruction block needs
  `set_option maxRecDepth 8192 in` (placed BEFORE the doc comment);
  `rw [write_same, ...]`-chains ending in an assoc-only mismatch need
  a trailing `omega`.
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green (only the pre-existing sanctioned
  `SuccinctFinalRAM.lean:5694+` simp-arg warnings); hygiene rg clean.

## M3c-6a: select-close long and sparse legs (`E1SelectLegBlocks.lean`)

- New module `RMQ/Core/WordRAM/E1SelectLegBlocks.lean` (wired into
  `RMQ.lean`): the two exception legs of the select dispatch, each
  "seeded TRUE rank block + entry-field arithmetic + relative read +
  packet move".
  - `longLegBlock LB GL CH RL SS WS c L WSc BPS` (73 instrs: rank
    `LB..58`, `longLegSetup` `59..67` re-pins rOne and computes compact
    slot `exceptionRank*SS + (q - super.baseOccurrence)` -> `rSlot`,
    base `super.baseWordIndex*WS + super.firstOffset` -> `xBPos`,
    `relativeReadBlock (LB+68) RL`, `move rVal rT` at 72).
  - `sparseLegBlock LB GS CH RS LS WS c L WSc BPS` (77 instrs: same
    with the two-entry sums `relativeSplitSelectLocalBaseOccurrence` /
    `relativeSplitSelectLocalBasePosition` and stride `LS`).
  - `longLegBlock_runsTo` / `sparseLegBlock_runsTo`: receipts
    POSITIONALLY EQUAL to the route-side `TraceResult.bind` of
    `d.bpChunkedRankTraceResultWithStore ... true (regs0 rPos)` into
    `bpRelativeOffsetReadTraceResultWithStore` (exactly the dispatch's
    long-leg expression / the body of
    `SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`);
    packet under `decodePacket` in `rVal`; cats
    `longLegCats`/`sparseLegCats` (rank hit cats + setup + present/
    absent relative read + move); preservation
    `(r <= 8 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 <= r) ÃƒÂ¢Ã‹â€ Ã‚Â§ r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  38` (the legs own `xBPos`).  Entry
    fields arrive as shifted-encode hypotheses
    (`regs0 xSF1 = super.baseOccurrence + 1` etc.); seed presence +
    offset bound are route-side hypotheses for canonical discharge.
  - Width certificates `longLegBlock_fits`/`sparseLegBlock_fits`
    (delegate the rank block; `first`-combinator arms).
- Gotcha: `relativeReadBlock_runsTo`'s value clause uses WordRAM's
  `bitsToNatLE`, the route uses `SuccinctSpace.bitsToNatLE` - convert
  with `funext SuccinctSpace.WordRAMBridge.bitsToNatLE_eq` and
  `rw [ÃƒÂ¢Ã¢â‚¬Â Ã‚Â hfn]` (simp cannot rewrite the unapplied function under
  `Option.map`).
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean.

## M3c-6b: dense-leg preservation strengthened to the pinned bank

- Inherited uncommitted work from the R4g session (cut off mid-commit by
  a usage limit), verified and landed here unchanged.
- `E1DenseSelectBlock.lean`: the register-preservation clauses of
  `denseHeadBlock_runsTo_present` and `denseSelectLegBlock_runsTo` are
  strengthened from `(ÃƒÂ¢Ã‹â€ Ã¢â€šÂ¬ r, (24 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ r ÃƒÂ¢Ã‹â€ Ã‚Â§ r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 26) ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ r ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ regsF r =
  regs0 r)` to `(ÃƒÂ¢Ã‹â€ Ã¢â€šÂ¬ r, r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 8 ÃƒÂ¢Ã‹â€ Ã‚Â¨ (24 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ r ÃƒÂ¢Ã‹â€ Ã‚Â§ r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 26) ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ r ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ regsF r =
  regs0 r)`, with the internal `h6bank` hypothesis widened to match.
- WHY (needed downstream, not cosmetic): the top-level select dispatch
  calls the dense leg with the pinned constants (`rOne`, `rZero`, the
  per-shape constant registers) live in `0..8`; without this clause the
  dispatch would have to re-pin them after every leg call.  The proof
  cost was nil - `h6pres`/`h5pres` already covered `r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 8`, so only the
  hypothesis and conclusion widened.
- Verification at this commit: `lake env lean
  RMQ\Core\WordRAM\E1DenseSelectBlock.lean` exit 0 (24.3s, zero errors,
  coordinator-run under the heavy mutex); `lake build RMQ` exit 0
  (29.5s, 232/232), only the pre-existing sanctioned unused-simp-arg
  warnings in `SuccinctFinalRAM.lean:5694+`,
  `ReviewerReachabilitySparse.lean:574`, `BPNavigationRAM.lean:2111`.

## M3c-6c: select-close dispatch skeleton (`E1SelectDispatch.lean`)

- New module `RMQ/Core/WordRAM/E1SelectDispatch.lean` (wired into
  `RMQ.lean`): the top-level select dispatch block, its derived category
  log, and the hosting peel.  Simulation theorem lands in M3c-6d.
- `selectCloseBlock A S1..S4 M1..M4 GL RL GS RS G W ST c OC SS LSPS LS
  DLS WS N2 LLen LWS LBPS SLen SWS SBPS` (405 instructions).  Exact
  layout: prologue `A+0..A+5` (pin `rOne`/`rC`/`rEight` for the dense
  leg, occurrence count into `rA`, `xQ := xIdx`, `natLt`), range branch
  `A+6..A+7`, super slot `A+8..A+9`, super entry 4-read `A+10..A+21`,
  super-miss branch `A+22`, marked test `A+23..A+24`, local slot
  `A+25..A+30`, local entry 4-read `A+31..A+42`, local-miss branch
  `A+43`, marked test `A+44..A+45`, dense base `A+46..A+54`, DENSE leg
  `A+55..A+247`, jump `A+248..A+249`, LONG leg `A+250..A+322`, jump
  `A+323..A+324`, SPARSE leg `A+325..A+401`, jump `A+402..A+403`, none
  tail `A+404`, END `A+405`.
- `selectCloseCats data layout G ST store c idx`: derived log matching
  `bpChunkedSelectTraceResultWithStore` branch for branch over the
  route's OWN decoded entries (`superEntry`/`localEntry` abbreviations),
  with the three legs' existing derived logs spliced in.  Nothing
  asserted.
- GOTCHAS (new):
  - The SPARSE compact slot uses `data.sparseDirectory.localStride`, NOT
    `data.localStride` (the latter only drives
    `relativeSplitSelectLocalSlotInSuper`).  The block takes both, as
    `DLS` and `LS`; conflating them silently type-checks and would give
    a wrong slot.
  - `queryOccurrence data idx = idx` definitionally
    (`Source.lean:1851`), so `xQ` is a plain register copy of `xIdx`.
  - Unconditional jumps after the LONG/SPARSE legs cannot use `rOne`:
    those legs preserve only `r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 8 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ r`, and `rOne = 24` is
    outside it.  Use the 2-instruction `const rB 1; brNZ rB END` idiom
    (the DENSE leg does preserve `24..26`, but the same idiom is used
    for uniformity).
  - The hosting peel is kept PROPOSITIONAL via a `hostRebase` helper
    plus a `host_len` macro (`simp only [<length lemmas>] <;> omega`):
    letting `append_right`'s `A + 6 + 2 + 12 + ...` bases meet `A + 248`
    by defeq would push a 248-deep `Nat.succ` tower through the kernel,
    against the standing kernel-safety pattern.  `selectCloseBlock_length`
    is likewise `by simp [selectCloseBlock]`, not `rfl`.
- Verification at this commit: standalone `lake env lean` exit 0 (4.3s,
  no warnings); `lake build RMQ` exit 0 (6.9s, 233/233), only the
  pre-existing sanctioned unused-simp-arg warnings.

## M3c-6d: dispatch straight-line sims, prefix, and the two none branches

- Appended to `E1SelectDispatch.lean`:
  - `dispatchPrologue_runsTo`, `dispatchSuperSlot_runsTo`,
    `dispatchLocalSlot_runsTo`, `dispatchDenseBase_runsTo` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the four
    straight-line segments (all first-try green).
  - `dispatchNoneTail_runsTo`, `dispatchJump_runsTo` (the two tail
    idioms), `selectCloseBlockAt` (the block instantiated at the accepted
    layout/data ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â a large readability win for every later statement).
  - `selectCloseBlock_prefix_runsTo`: the shared in-range prefix
    (prologue, taken range branch, super slot, super entry 4-read) to
    `A + 22`, receipts POSITIONALLY EQUAL to the accepted super
    entry-table read events, four shifted field decodes in the super
    bank, miss indicator in `rA`, pinned constants live, `r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 7 ÃƒÂ¢Ã‹â€ Ã‚Â¨ r = 28`
    preserved.
  - `entryFields_of_some`: inversion of the accepted 4-read decode ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â a
    present entry pins each shifted field register to `field + 1`
    (exactly the leg blocks' hypothesis shape, and a zero miss indicator
    for free).  Works for both the super and local tables.
  - `selectCloseBlock_runsTo_outOfRange` and
    `selectCloseBlock_runsTo_superMiss`: the two `none`-answering
    branches, full receipts/value/cats/preservation against
    `bpChunkedSelectTraceResultWithStore`.
- Gotchas (new):
  - `omega` cannot see through the register ABBREVS: `28 ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ xSF1` and
    `r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  xSF1` both fail.  Use `by decide` for CLOSED side conditions,
    and put explicit `have nSF1 : xSF1 = 30 := rfl` facts in context when
    the register is universally quantified (omega then treats the abbrev
    as an atom with a known value).
  - `RunsTo.brNZ_taken`'s condition hypothesis is stated on
    `s.regs cond`, so a tactic block there operates on the unreduced
    projection and `rw` fails.  Prove `regsX rOne ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â  0` as a standalone
    `have` and pass it ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â `exact` closes the projection by defeq.
  - `simp only [ÃƒÂ¢Ã¢â‚¬Â Ã‚Â superEntry]` is rejected (`ÃƒÂ¢Ã¢â‚¬Â Ã‚Â` on a definition to be
    unfolded).  Get the raw form with a `have hmissRaw : <raw> = none :=
    hmiss` type ascription instead and `rw` with that.
  - `cases h1 : store.readWord? ...` already substitutes into the goal,
    so passing `h1` to a follow-up `simp` is an unused-arg warning.
- Verification at this commit: standalone `lake env lean` exit 0 (8.2s,
  no warnings); `lake build RMQ` exit 0.
- REMAINING for the dispatch: the long, sparse, and dense branch
  theorems, then the combining `selectCloseBlock_runsTo`.

## M3c-6f: TOP-LEVEL SELECT DISPATCH COMPLETE (all six branches)

- `E1SelectDispatch.lean` now carries the whole dispatch:
  - `selectCloseBlock_runsTo_outOfRange`, `_superMiss`, `_long`,
    `_localMiss`, `_sparse`, `_dense` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the six control branches, each
    with receipts POSITIONALLY EQUAL to
    `(data.bpChunkedSelectTraceResultWithStore layout (G+4) ST store c
    idx).trace`, the evaluator's optional answer under `decodePacket` in
    `rVal`, the derived `selectCloseCats`, and `r ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ 7 ÃƒÂ¢Ã‹â€ Ã‚Â¨ r = 28`
    preserved.
  - `selectCloseBlock_localPrefix_runsTo` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the shared continuation past
    an unmarked super entry (consumed by the last three branches).
  - `selectCloseBlock_runsTo` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the combining theorem, case-splitting on
    range / super presence / super marked / local presence / local
    marked, with the three route-side hypotheses (`hLongSeed`,
    `hSparseSeed`, `hDenseLen`) each conditioned on exactly the branch
    that consumes it.
- KEY TECHNIQUE (this unblocked five failing proofs at once): do NOT
  reduce the route side with staged `simp only [...]; rw [...]` chains.
  After `rw` puts `some super` into the scrutinee, a following
  `simp only [hunmarked, ...]` does NOT fire, because the `match` has not
  iota-reduced and the marked-test `if` is not yet in the goal (the
  telltale symptom is an "unused simp argument" warning on the very
  hypothesis you are trying to use).  Instead give ONE `simp` the whole
  fact set ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â evaluator def, `queryOccurrence`, `hrange`, the raw `.value`
  equations, the marked/unmarked booleans, `entryRead_trace_eq`, and (for
  the sparse leg) `SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`
  ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â and let it unfold, iota-reduce, and rewrite in one pass.  For the
  value goals, prove a `have hval : (route).value = (leg expr).value` by
  the same one-shot `simp` and then `exact` the leg's decode clause.
- Other gotchas: `by_contra` is Mathlib-only and unavailable here (use
  `simpa [relativeSplitSelectEntryIsMarked]` to invert an unmarked
  entry); `by_cases` IS available (core).  `rw` does not close
  `n + 1 - 1 = n` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â add `omega`.
- Verification at this commit: standalone `lake env lean` exit 0 (11.1s,
  no warnings); `lake build RMQ` exit 0 (14.6s, 233/233).
- NEXT: the canonical-store select form mirroring
  `rankCloseBlock_runsTo_canonical` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â instantiate `selectCloseBlock_runsTo`
  at `concreteBPNativeSuccinctRMQGlobalReadStore` and discharge
  `hLongSeed`/`hSparseSeed`/`hDenseLen` from the canonical layout facts
  (agreement lemmas listed at `ChargedRankSelectWiring.lean:656`).

## M3c-6g: CANONICAL SELECT FORM COMPLETE (`E1SelectCanonical.lean`)

The inventory in the RESUME POINT section below is now DISCHARGED ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â every
one of its predictions held, including the two it flagged as unverified.
Landed in commits `d9ecd68` (prep) and this one.

- PREP (`d9ecd68`), two structural cleanups the inventory called for:
  - NEW `RMQ/Core/SuccinctFinal/RAM/RankSamplePresence.lean`: the
    three-seed presence statement `twoLevelRankData_sample_words_present`
    and its helper `fixedWidthNatTable_word_present_of_entry_present`,
    de-privatized and SINGLE-SOURCED.  The two byte-identical `private`
    copies in `ReviewerReachabilityLong.lean` (which named its copy
    `..._present_long`) and `ReviewerReachabilitySparse.lean` are DELETED
    and both files now import the shared module.  This is the
    coordinator-endorsed option (de-privatize one, delete the other); a
    shared module was preferred over de-privatizing in one sibling
    because Long and Sparse are independent witness files and neither
    should have to import the other.  Import is
    `RMQ.Core.GenericSelect.RAM`, NOT `RMQ.Core.SuccinctRank`:
    `superSampleWords`/`blockSampleWords` are defined at
    `GenericSelect/RAM.lean:165,176`, not in `SuccinctRank.lean`.
  - `E1RankCanonical.lean`: `builtRankData_wordOffset_le` GENERALIZED to
    `twoLevelRankData_wordOffset_le`, stated for any
    `TwoLevelPayloadLiveStoredWordRankData` given `hwords` (its payload
    store is the sentinel-padded chunking of its own bits).  The old
    shape-specialized name is retained as a one-line instance, so no
    consumer moved.  The inventory's plan (textual substitution of the
    body with the payload renamed) worked verbatim.
- NEW `RMQ/Core/WordRAM/E1SelectCanonical.lean` (added to `RMQ.lean`):
  - `canonical_longSeed`, `canonical_sparseSeed` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the three seed reads of
    the long-flag rank object and of the sparse-directory rank object are
    PRESENT at the canonical global store, with the in-word offset bound.
    Both are UNCONDITIONAL in the entry (presence does not depend on entry
    contents), so the dispatch's `ÃƒÂ¢Ã‹â€ Ã¢â€šÂ¬ super, ... ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ ... ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢` hypotheses are
    discharged by `fun _ _ _ => ...` with no case split.
  - `canonical_denseLen` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the dense-leg exact `Nat.min` word length, one
    lemma serving BOTH the `i` and `i + 1` obligations.
  - `selectCloseBlock_runsTo_canonical` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the canonical-store dispatch.
- CONFIRMED (the inventory's two flagged unknowns, both now checked):
  - The `hwords` premise IS `rfl` for both select rank objects
    (`longFlagRankData_bitWords_words`, `sparseRankData_bitWords_words`),
    exactly as the constructor chain predicted.
  - `17 + 4 = 21` closes the chunk-segment identification by `rfl`, the
    same trick as `E1RankCanonical.lean:386`.
- CONFIRMED WRONG-GUESS CORRECTION HELD: `hDenseLen` really is the
  three-step `ofChunks` route (`_selectBitWords` ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢
  `selectAlignedBitWords_ofChunks.get_eq_take_drop` ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ `simp
  [List.length_take, List.length_drop]`), NOT a
  `builtRankData_wordOffset_le` mirror.  Sentinel-free, no case split.
- NEW GOTCHAS (add to the standing list):
  - `sparseExceptionSelectData` needs its two rank-overhead indices given
    EXPLICITLY in a helper's type ascription (`_` will not synthesize
    them); they are
    `sparseExceptionEffectiveFlagRank{Super,Block}Overhead bits target`.
  - The sparse local slot's entry argument has type
    `SparseDenseSelectDenseLocalEntry`, NOT `RelativeSplitSelectEntry` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â
    the two are easy to confuse since both flow through
    `relativeSplitSelectEntryIsMarked`.
  - `xIdx` is AMBIGUOUS under the dispatch's `open` set; qualify it as
    `E1SelectBridge.xIdx` in any new file that opens `E1SelectDispatch`.
  - Declare the data abbreviation as `private abbrev`, not `private def`,
    so the `rfl` identifications stay reducible.
- Verification at this commit: standalone `lake env lean
  RMQ/Core/WordRAM/E1SelectCanonical.lean` exit 0, NO warnings; `lake
  build RMQ` exit 0.
- NEXT: the close/LCA structural leg (the last risk center) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
  (`SuccinctFinalRAM.lean:2330`).

## RESUME POINT (M3c-6g: canonical select form) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â DISCHARGED, see M3c-6g above

Everything below was inventoried at HEAD by a read-only survey of an
earlier session.  It is retained as the audit record of what was predicted
versus what held; the implementation is described in the M3c-6g section
immediately above.

TARGET: a new file `RMQ/Core/WordRAM/E1SelectCanonical.lean` (does not
exist yet; no `selectCloseBlock_runsTo` reference exists outside
`E1SelectDispatch.lean`).  Import pair, mirroring `E1RankCanonical.lean:1-2`:
`RMQ.Core.WordRAM.E1SelectDispatch` + `RMQ.Core.SuccinctFinalRAM` (the
latter transitively supplies every agreement lemma below).

TEMPLATE to mirror: `rankCloseBlock_runsTo_canonical`
(`E1RankCanonical.lean:263`), NOT `_atSegment` (`:133`).

CANONICAL INSTANTIATION ARGUMENTS:
- `data := GenericSelect.sparseExceptionSelectData shape.bpCode false`
  (`GenericSelect/Source.lean:2371`).
- `layout := concreteBPNativeSelectCloseTraceSegmentLayout`
  (`SuccinctFinal/RAM/Segments.lean:24`).  Field values: superTable
  1/2/3/4, localTable 5/6/7/8, longFlagRankBase 9 (seeds 9/10/11),
  longRelativeBase 12, sparseDirectory.rankBase 13 (seeds 13/14/15),
  sparseDirectory.relativeBase 16, bitWordBase 0, deadSegment 29.
- `store := concreteBPNativeSuccinctRMQGlobalReadStore shape`
  (`Segments.lean:174`).
- `G := concreteBPNativeRankCloseTraceSegmentBase = 17` (`Segments.lean:48`)
  so that `G + 4 = 21 = concreteBPNativeFringeChunkTraceSegment`
  (`Segments.lean:79`) BY `rfl` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the same `17 + 4 = 21` trick the rank
  template uses at `E1RankCanonical.lean:386`.
- `ST := concreteBPNativeSelectChunkTraceSegment = 22` (`Segments.lean:82`).
- `c := SuccinctClose.bpFringeChunkBits shape.bpCode.length`.
- Target trace object: `concreteBPNativeChunkedSelectCloseGlobalWordTraceResult`
  (`ChargedRankSelectWiring.lean:645`); public alias
  `concreteBPNativeSelectCloseGlobalWordTraceResult`
  (`SuccinctFinalRAM.lean:1342`) is DEFINITIONALLY the same.

DISCHARGING `hDenseLen` (EASIEST ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â do this one first):
The select dense store is SENTINEL-FREE: `data.bitWords` is built by
`BoundedPayloadWordStore.ofChunks` (`GenericSelect/Source.lean:2408-2410`),
NOT `ofChunksWithSentinel`.  So every present word is a genuine chunk and
the exact `Nat.min` length is unconditional.  Route:
1. rewrite `store.readWord? layout.bitWordBase i` into
   `(...).bitWords.store.words[i]?` with
   `concreteBPNativeSuccinctRMQGlobalReadStore_selectBitWords`
   (`ChargedRankSelectWiring.lean:281`);
2. apply `SelectAlignedBitWords.get_eq_take_drop` from
   `selectAlignedBitWords_ofChunks` (`GenericSelect/DenseWord.lean:26`;
   structure at `:13`) to get `word = (bits.drop (i*wordSize)).take wordSize`;
3. `simp [List.length_take, List.length_drop]` gives exactly
   `Nat.min wordSize (bits.length - i * wordSize)` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the `hDenseLen`
   shape, for both `i` and `i + 1`, no case split.
The worklog's earlier guess that this would mirror
`builtRankData_wordOffset_le` was WRONG; that name belongs to the
sentinel-padded RANK store.

DISCHARGING `hLongSeed` / `hSparseSeed` (the only real work):
Two sub-obligations, seed PRESENCE and the OFFSET BOUND.

(a) PRESENCE.  Per-address agreement lemmas all exist, in exactly the
    `readWord? seg addr = <sampleWords>[addr]?` form needed, all in
    `ChargedRankSelectWiring.lean`:
      `_selectLongFlagSuper` :292, `_selectLongFlagBlock` :305,
      `_selectLongFlagWord` :318, `_selectLongRelative` :331,
      `_selectSparseRankSuper` :345, `_selectSparseRankBlock` :359,
      `_selectSparseRankWord` :374, `_selectSparseRelative` :388,
      `_selectBitWords` :281, `_routeSelectChunkTable` :402,
      `_fringeChunkTable` (`Segments.lean:247`)
    (all prefixed `concreteBPNativeSuccinctRMQGlobalReadStore_`).
    The three-seed existence statement itself is ALREADY PROVED but is
    `private`, in two byte-identical copies:
      `twoLevelRankData_sample_words_present_long`
        (`SuccinctFinal/RAM/ReviewerReachabilityLong.lean:534`)
      `twoLevelRankData_sample_words_present`
        (`SuccinctFinal/RAM/ReviewerReachabilitySparse.lean:672`)
    stated for a generic `TwoLevelPayloadLiveStoredWordRankData` at any
    `pos ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ bits.length`, in the `superSampleWords`/`blockSampleWords`
    vocabulary ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â i.e. it composes with the agreement lemmas above by
    plain rewrite, with NO `read_exact` codec detour (unlike the rank
    template, which hand-rolls that upgrade three times at
    `E1RankCanonical.lean:289-357`).  DECISION NEEDED: de-privatize one
    copy and delete the other (preferred ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â it removes a duplication),
    or write a third copy in the new file.  Their shared helper
    `fixedWidthNatTable_word_present_of_entry_present` is likewise
    duplicated (`ReviewerReachabilityLong.lean:293`,
    `ReviewerReachabilitySparse.lean:336`).

(b) OFFSET BOUND.  NO reusable lemma exists (searched
    `wordOffset.*[<=ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤].*length` repo-wide: only hypothesis binders in the
    E1 block files).  `builtRankData_wordOffset_le`
    (`E1RankCanonical.lean:42`) is shape-specialized but its proof
    transfers verbatim with the payload renamed, because ALL THREE rank
    objects share one constructor,
    `SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock`
    (`SuccinctRank.lean:1331`), which always threads
    `canonicalRankWordBridgeOfChunksWithSentinel` (`:1097`) whose
    `bitWords := ofChunksWithSentinel` (`:1101-1103`):
      `builtRelativeSplitBPCloseRankData shape` (`SuccinctFinal.lean:832`)
      `GenericSelect.longFlagRankData bits target` (`Source.lean:411`)
      `sparseExceptionEffectiveFlagRankData bits target`
        (`FlagRank.lean:283`; wired as `sparseDirectory.rankData` at
        `Directory.lean:225`).
    PLAN: generalize once as
      `theorem twoLevelRankData_wordOffset_le {bits so bo qc}
        (d : ...RankData bits so bo qc)
        (hwords : d.bitWords.store.words =
          (SuccinctSpace.chunkPayloadWords d.wordSize bits ++
            List.replicate (bits.length + 1) []).toArray)
        (pos : Nat) {w} (hw : d.bitWords.store.words[d.wordIndex pos]? =
          some w) : d.wordOffset pos ÃƒÂ¢Ã¢â‚¬Â°Ã‚Â¤ w.length`
    with the body of `builtRankData_wordOffset_le` (`E1RankCanonical.lean:49-122`)
    textually substituted (`builtRelativeSplitBPCloseRankData shape` ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ `d`,
    `shape.bpCode` ÃƒÂ¢Ã¢â‚¬Â Ã¢â‚¬â„¢ `bits`), then instantiate three times.  All the
    generic steps it uses are structure-level and transfer: `queryPos pos
    = Nat.min pos bits.length` (so `Nat.min_le_right` gives the clamp for
    free), `wordIndex pos = queryPos pos / wordSize := rfl`, `wordOffset
    pos = queryPos pos - wordIndex pos * wordSize := rfl`.  Supporting
    lemmas it cites: `SuccinctSpace.chunkPayloadWords_get?_eq_take_drop`
    (`SuccinctSpace/WordStore.lean:274`),
    `chunkPayloadWords_length_eq_div_add_indicator` (`:390`),
    `nat_min_eq_sub_sub` (`E1RankBridge.lean:46`).
    CAVEAT to check at first build: `hwords` should be `rfl` for both
    select rank objects (the constructor chain is definitional, as it is
    for the rank object at `E1RankCanonical.lean:29`), but that single
    `rfl` is the one step the survey could not verify without building.
    If it is not `rfl`, unfold the constructor chain named above.

NOT NEEDED: the eight entry-table segments (1-4, 5-8) have only
`pullback`-level agreement lemmas
(`ChargedRankSelectWiring.lean:417,437,457,477,497,517,537,557`), NOT
per-address `readWord?` ones.  This is NOT a gap for the canonical form:
`superEntry`/`localEntry` enter `selectCloseBlock_runsTo` only as
hypotheses that the canonical theorem RECEIVES (or case-splits on), never
as something it must prove.

CONTEXT for the eventual `_refines` join:
`concreteBPNativeChunkedSelectCloseGlobalWordTraceResult_refines`
(`ChargedRankSelectWiring.lean:656`) consumes those nineteen agreement
lemmas in a fixed order (8 pullback, then :292, :305, :318, :331, :345,
:359, :374, :388, :281, `Segments.lean:247`, :402); companions
`_matchesReadStore` (:692), `_no_syntheticCostOnlyPrimitive` (:708),
`_events_readWord` (:730).

AFTER M3c-6g, the remaining dependency order is unchanged: close/LCA
structural leg (`concreteBPNativeLCACloseGlobalWordTraceResultAllSize
Structural`, `SuccinctFinalRAM.lean:2330`) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â the last risk center ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â
then whole-query glue via `E1RouteDecomposition`, then M4 category
algebra + derived literal, M5 target Prop + supersession note, M6
validator `lean_exe`, M7 adequacy doc + matrix closure + final battery.

## STAGE-2 LAYOUT (dense leg tails - implemented in M3c-5c above;
## kept for reference)

`selectFoldBlock_runsTo` interface RE-VERIFIED this session
(`E1SelectBlock.lean:367`): inputs sOne=1, sC=c, sLen(13)=word.length,
sR(17)=bitsToNatLE word / 2^(j*c), sJC(27)=j*c, sOcc(12)=k, sK(18)=count,
`0 < count`; ends LB+36, packet in sVal(9), preserves r<=8 ÃƒÂ¢Ã‹â€ Ã‚Â¨
rÃƒÂ¢Ã‹â€ Ã‹â€ {10,11,13,14,15,16,24,25,26} ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28<=r.  The dense select call is at
j=0, count = bpWordChunkCount c word.length (ALWAYS >= 1 - positivity is
free via `bpWordChunkCount_eq_sub` + omega; discharge the `/2^(0*c)`
hypothesis by simp [Nat.zero_mul, pow_zero, Nat.div_one]).  Head-output/
fold-input register alignment is exact: sOcc=rSI, sLen=rE, packet
register sVal=rVal.

Whole-leg block `denseSelectLegBlock L W G S c WS N2` at base `L`
(193 instrs, END = L+193, MISS = L+192, first tail T1 = L+143):

- L+0..L+83: `denseHeadBlock L (L+192) W G c WS N2` (M := miss tail).
- L+84: `brNZ rA (L+143)` (compare taken -> first tail).
- SECOND TAIL L+85..: add rP rP rOne; readMem rWrd W rP; brNZ rWrd
  (L+89); brNZ rOne (L+192); mulConst rWI rP WS; const rA WS; const rB
  N2; sub rB rB rWI; sub rT rA rB; sub rE rA rT (len2 -> sLen directly);
  sub rSI rSI rVal (sOcc := locc - firstCount); sub rR rWrd rOne;
  const rJC 0; sub rA rE rOne; divConst rA rA c; add rK rA rOne; sub rB
  rK rEight; sub rK rK rB; then `selectFoldBlock (L+103) R S c`
  (L+103..L+138); packet shift L+139: brNZ rVal (L+141); brNZ rOne
  (L+142); add rVal rWI rVal; L+142: brNZ rOne (L+193) (jump to END).
- FIRST TAIL L+143..: move rE rBlk; add rSI rSup rSI (sOcc := before +
  locc); sub rR rWrd rOne; const rJC 0; count chain (5 instrs, from rE);
  `selectFoldBlock (L+152) R S c` (L+152..L+187); packet shift L+188:
  brNZ rVal (L+190); brNZ rOne (L+191); add rVal rWI rVal; L+191: brNZ
  rOne (L+193) (jump over miss tail).
- MISS TAIL L+192: const rVal 0; fall through to END = L+193.

Packet-shift correctness: fold none -> sVal 0 -> shift skipped -> packet
none ÃƒÂ¢Ã…â€œÃ¢â‚¬Å“; fold some off -> sVal = off+1 -> add gives rWI + off + 1 =
packet (wordStart + off) ÃƒÂ¢Ã…â€œÃ¢â‚¬Å“ (commute by omega).  Second-tail length needs
the SECOND route hypothesis `hlen2 : w2.length = Nat.min WS (N2 -
(bPos / WS + 1) * WS)`.  Whole-leg theorem target:
`bpChunkedDenseTwoWordSelectTraceResultWithStore W (G+4) S c false
bitWords store bPos bOcc q` with bPos/bOcc/q := regs0 xBPos/xBOcc/xQ;
four control branches (miss1/first/second-miss/second); cats
`denseLegCats` defined by matching on `store.readWord?` and the two
route-side rank `.value`s (selectFoldCats precedent); value under
`decodePacket` in rVal; extension bank untouched by the leg (second
tail rewrites only rP/rWI in the component bank).

## RESUME POINT (next session: select-close read sub-blocks onward)

NEW in the M3c-4 session (commits `eb3f102`, `aff4393`, `d49672d`):
RESUME step 1 is DONE ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â `E1RankTrueBlock.lean` (TRUE-target seeded
block, chunk segment `S` decoupled from the seed base, generic-base
loop `rankTrueLoopFold_runsTo`) and `E1RankAtBlock.lean` (atomic
register-input FALSE fold `rankAtSegmentBlock` + generic-base
`rankFalseLoopFold_runsTo` with write-set-complement preservation).
See the M3c-4a/-4b/-4c sections above for exact theorem names/offsets.

CONCRETE LAYOUT INVENTORY (verified this session,
`SuccinctFinal/RAM/Segments.lean:24`,
`concreteBPNativeSelectCloseTraceSegmentLayout`): superTable fields at
segments 1/2/3/4 (baseOccurrence/baseWordIndex/rankBefore/firstOffset),
localTable at 5/6/7/8, longFlagRankBase 9 (seeds 9/10/11),
longRelativeBase 12, sparseDirectory.rankBase 13 (seeds 13/14/15),
sparseDirectory.relativeBase 16, bitWordBase 0, dead segment
`concreteBPNativeDeadTraceSegment`; fringe chunk table 21, select chunk
table 22; rank-close base 17 (its chunk 21 = 17 + 4 is the only
`seeds+4` coincidence ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â hence M3c-4c).  ATOMIC-BLOCK NOTE: the dense
leg instantiates `rankAtSegmentBlock A G c` at `G := 17` so its
hardwired `G + 4 = 21` hits the chunk table.

TOP-LEVEL DISPATCH SHAPE (verified, `bpChunkedSelectTraceResultWithStore`,
`ChargedRankSelectLeafTrace.lean:1157`): `q := data.queryOccurrence idx`;
guard `idx < occurrenceCount bits target` (per-shape constant register);
super 4-read at `layout.superTable` slot `selectSuperSlot q superStride`;
none -> none; `relativeSplitSelectEntryIsMarked super` -> LONG leg
(seeded TRUE rank block at 9..11/21 on slot `selectSuperSlot q
superStride`, then relative read at segment 12, base
`relativeSplitSelectEntryBasePosition wordSize super`, slot
`relativeSplitSelectLongCompactSlot exceptionRank (q -
super.baseOccurrence) superStride`); else local 4-read at
`layout.localTable` slot `relativeSplitSelectLocalSlot ...`; none ->
none; marked local -> SPARSE leg (`bpChunkedReadTraceResultWithStore` =
seeded TRUE rank block at 13..15/21 on `localSlot`, then relative read
at 16); else DENSE leg (word read at 0, two atomic FALSE folds at 21,
compare, `selectFoldBlock` at 21/22 per M3c-3a).

REGISTER-ALLOCATION CONSTRAINT (checked): `E1QueryProgram` reserves
0..7; component bank 8..27 is fully owned by the rank/select folds;
hosted-fold preservation covers `r <= 8 ÃƒÂ¢Ã‹â€ Ã‚Â¨ 28 <= r` (seeded) and the
write-set complement (atomic).  The select dispatch must therefore keep
`idx`/`q`/the 4 super fields/the 4 local fields/base-position/
base-occurrence in registers `>= 28` (they survive every hosted fold);
plan a frozen extension bank 28..39 and record it as a DD entry when
the dispatch block is written.

ENTRY-TABLE 4-READ REDUCTION PATH (inventoried): the accepted 4-read
evaluator `readTraceResultRelabeledWithStore`
(`GenericSelect/RAMStoreParam.lean:258`) is four
`TraceResult.ofProgramWithStore (singletonSegmentMap fieldSeg dead)
store (table.readProgram i)` binds ending in `entryOfFields`
(none-propagating 4-way match, `GenericSelect/DenseEntryTable.lean:109`).
`ofProgramWithStore` (`RAMStoreParam.lean:29`) = relabel of
`(readProgram i).evalR (store.pullback segmentMap)`; `readProgram i` is
`mapOptWordNat/mapOptWordOptionNat (store.readProgram i)` over
`Program.readWord 0 i` (`SuccinctSpace/WordStoreRAM.lean:26`,
`TablesRAM.lean:53/145`), so each bind's trace should reduce (near-rfl)
to `[readWord fieldSeg i (store.readWord? fieldSeg i)]` and its value
to the decoded option ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â derive small bridge lemmas
`ofProgramWithStore_readProgram_trace/_value` first (in a new
`E1SelectBridge.lean`), then the machine sub-block is 4 readMems +
4 zero tests with the fields parked in the `>= 28` bank.

NEXT (dependency order):

1. DONE (M3c-4a/-4b/-4c): TRUE-target seeded rank block
   (`E1RankTrueBlock.lean`) + atomic register-input FALSE fold block
   (`E1RankAtBlock.lean`).
2. DONE (M3c-5a, `E1SelectBridge.lean`): entry-table 4-read sub-block
   (`entryReadBlock_runsTo`, parametric destinations for the super/local
   banks) + route-side `rfl` reductions + decode connectors + extension
   bank 28..39 (DD-20260718-007).  Original plan follows.
   Entry-table read sub-block: the accepted 4-read evaluator
   `readTraceResultRelabeledWithStore` (`GenericSelect/RAMStoreParam.lean:
   258/530`, relabeled segments per
   `concreteBPNativeSelectCloseTraceSegmentLayout`) - inventory its
   trace/value shape first (4 sequential `readWord`s, entry assembled
   from 4 decoded fields, none-propagation per field); machine: 4
   readMems + 4 zero tests, entry fields kept in separate registers
   (marked test `relativeSplitSelectEntryIsMarked` +
   base-position/occurrence arithmetic `RelativeSplit.lean:13-61` are
   plain register arithmetic).
3. DONE (M3c-5a, `E1SelectBridge.lean`): relative-offset read
   (`relativeReadBlock_runsTo`, 4 instrs with a presence brNZ - the
   "3-instr straight" prediction missed the none-packet skip branch).
4. Dense two-word leg: STAGE 1 DONE (M3c-5b, `E1DenseSelectBlock.lean`
   `denseHeadBlock_runsTo_present/_miss` - word read, both atomic false
   folds, compare, receipts = component prefix).  STAGE 2 REMAINING: the
   two select tails + whole-leg theorem - (a) first-word tail: sOcc :=
   rSup + rSI (before + localOccurrence), sR := rWrd - 1, sLen := rBlk,
   sJC := 0, sK := chunk count of rBlk by the 8-cap chain, host
   `selectFoldBlock` (needs `1 <= count`, discharge from `0 < w.length`
   route-side), then packet shift: brNZ sVal -> add sVal rWI (+wordStart,
   preserves the 0 = none packet); (b) second-word tail: second read at
   rP + 1 (readMem + presence brNZ -> miss), same length chain at index
   rP+1, sOcc := rSI - rVal (locc - firstCount), select fold, packet
   shift by (rP+1)*WS via mulConst; (c) miss tail at `M`: const rVal 0 +
   jump to leg end; (d) whole-leg theorem vs
   `bpChunkedDenseTwoWordSelectTraceResultWithStore W (G+4) S c false
   bitWords store bPos bOcc q` - four control branches (miss1 / first /
   second-miss / second), receipts positionally equal per branch, value
   under `decodePacket` in sVal(9) = rVal.  Original inventory: compose
   word read (segment `layout.bitWordBase`), two atomic false-rank
   folds, compare, then `selectFoldBlock` on first word (occurrence
   `beforeFirst + localOccurrence`) or second word read +
   `selectFoldBlock` (occurrence `localOccurrence - firstCount`);
   word-length register discharge mirrors `builtRankData_wordOffset_le`
   (word rows have length `wordSize` except the boundary row - find the
   dense store's length characterization when instantiating).
5. Top-level select-close block: occurrence-range guard (`idx <
   occurrenceCount`, a per-shape constant register), super read ->
   marked dispatch -> long/local -> sparse/dense, mirroring
   `bpChunkedSelectTraceResultWithStore` branch for branch; receipts
   positionally equal to
   `(concreteBPNativeChunkedSelectCloseGlobalWordTraceResult shape
   idx).trace`; then canonical instantiation like
   `rankCloseBlock_runsTo_canonical` (agreement lemmas are all in
   `ChargedRankSelectWiring.lean` / `Segments.lean`, listed at the
   `_refines` call at `ChargedRankSelectWiring.lean:656`).
6. Then the close/LCA structural leg (M3b-2 route decomposition names
   the target `concreteBPNativeLCACloseGlobalWordTraceResultAllSize
   Structural`, `SuccinctFinalRAM.lean:2330`), then whole-query glue
   (`e1ValidPath`), then M4-M7 per the original plan below.

TECHNIQUE (additions to the M3c notes, all battle-tested this session):
state preservation-helper hypotheses on register NUMERALS, not abbrevs
(omega cannot unfold abbrevs in hypotheses); no trailing `rfl` after
`rw`-chains that close the goal; `or_assoc` in the simp set before
wide `rcases` over block membership; `straight_eval [segments,
registers]` / `straight_writes [registers]` are the shared macros in
`E1StraightLine.lean` (simp-arg splicing via
`Lean.Parser.Tactic.simpLemma,*` works; the M3c-1b gotcha applied to a
different formulation); early-exit loops: prove by direct induction on
the spec fold's recursion (receipts/cats stay fold-shaped) rather than
forcing `iterUntilLog` - `RunsTo.iterateUntil` remains for evaluators
that are not already structural recursions.

## ORIGINAL M3c PLAN (superseded where marked; kept for the glue/M4-M7 tail)

DONE so far (M3b commits `e93e2ae`, `933955e`, `bd84fc6`; M3c commits
`c1e7d0a`, `ff03a37`, `b761581`, `0ddf257`):
- Register map / packet / skeleton frozen (DD-20260718-006), charged
  invalid guard + REQ-E1-05 public parity landed
  (`E1QueryProgram.lean`, `E1QueryBridge.lean`).
- Whole-query positional decomposition landed
  (`E1RouteDecomposition.lean`).
- Loop backbone `RunsTo.iterate`/`iterLog` landed (M3b-3).
- M3c-1 RANK-CLOSE IS DONE machine-side: bridge lemmas
  (`E1RankBridge.lean`), straight-line symbolic executor
  (`E1StraightLine.lean`: `RunsTo.straight`, `straightRegs_preserves`,
  `RunsTo.brNZ_taken/_not_taken`), the 60-instruction block + hit-path
  simulation (`E1RankBlock.lean`: `rankCloseBlock_runsTo_hit`), and the
  canonical instantiation (`E1RankCanonical.lean`:
  `rankCloseBlock_runsTo_atSegment` - receipts positionally equal to
  `concreteBPNativeRankCloseWordTraceResultAtSegment` at the seed store,
  value in `rVal`, frozen cats, for all shapes/positions).

PROOF TECHNIQUE (read this before writing the next block; it is the
whole cost model of the grind): do NOT hand-write RunsTo state towers.
Segment the block into straight-line pieces + branches; run each piece
with `RunsTo.straight`; name the register file after each piece by
`obtain ÃƒÂ¢Ã…Â¸Ã‚Â¨regsN, hregsNÃƒÂ¢Ã…Â¸Ã‚Â© : ÃƒÂ¢Ã‹â€ Ã†â€™ x, straightRegs store seg regsM = x :=
ÃƒÂ¢Ã…Â¸Ã‚Â¨_, rflÃƒÂ¢Ã…Â¸Ã‚Â©`; prove per-register value facts by `rw [<- hregsN]` then the
`regs_eval` macro (local in `E1RankBlock.lean`: simp with segment defs,
`straightRegs_cons`, `straightStepRegs/Event`, `RegFile.write`, and the
register-numeral abbrevs) followed by a second `simp [bridge equations]`
via `<;>`; preservation by `straightRegs_preserves` + `writes_eval`.
Loops: `RunsTo.iterate` with the invariant carrying exact register
contents as functions of iterations-done, receipts as a fixed function
of the remaining counter, then `iterLog_singleton_desc`/`iterLog_congr`
to flip descending receipts into the ascending `List.range` order.
Bridge direction discipline: normalize BOTH sides to machine constant
forms (`nat_min_eq_sub_sub`, `nat_mod_eq_sub_div_mul`,
`bpWordChunkSliceLen_eq_sub`, `bpFringeWindowChunkValue_eq_div_mod`,
`decodeRead_pred_eq_map_getD`, `bpChunkRankOfEntry_false_eq`).  Gotchas:
omega does NOT see through `Nat.min`, register abbrevs, or variable-
divisor `/` (generalize the division first); `simp` argument splicing in
macros fails on the heterogeneous simpArg list (use an argument-less
macro + follow-up simp); pass `(store := store)` to the brNZ helpers.
The `regs_eval`/`writes_eval` macros are `local` to `E1RankBlock.lean` -
either re-declare them in the next block module or lift them into
`E1StraightLine.lean` first (recommended).

M3c remaining plan (REQ-E1-03/04):
1. Glue-side store swap for rank-close (small): re-instantiate
   `rankCloseBlock_runsTo_hit` at
   `concreteBPNativeSuccinctRMQGlobalReadStore shape` with base 17
   (presence via `concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper/
   Block/Word/fringeChunkTable`, `SuccinctFinalRAM.lean:1561-1581`
   region, + the same `builtRankData_wordOffset_le`), then rewrite the
   receipts through
   `concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`.
   NOTE: the machine store and the component store must be the SAME
   argument for receipts to match; at base 17 both equal the global
   store on the touched segments.
2. (b) select-close
   (`concreteBPNativeChunkedSelectCloseGlobalWordTraceResult`, public
   face `concreteBPNativeSelectCloseGlobalWordTraceResult`,
   `SuccinctFinalRAM.lean:1342`): inventory its trace evaluator first
   (it is NOT yet inventoried in this log; expect sample legs + the
   two-segment select fold `bpChunkedWordSelectTraceFromWithStore`,
   `ChargedRankSelectTrace.lean:322`).  The select fold has a
   DATA-DEPENDENT EARLY EXIT (found-chunk branch fires one select-table
   read and stops).  `RunsTo.iterate` does not express early exit; add a
   dedicated backbone first (suggest `RunsTo.iterateUntil` in
   `E1MachineCalculus.lean`: invariant P k s plus per-step alternative
   "exit to Q with exit receipts/cats" - receipts/cats stay fixed
   functions of the counter because the exit iteration is determined by
   store+inputs).  Machine loop shape: routing read + `natLt` on the
   remainder + forward `brNZ` to the select-read tail, else subtract and
   back edge.
3. (c) the all-size structural close/LCA leg
   (`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`,
   `SuccinctFinalRAM.lean:2330`) - same-block vs cross-block split,
   chunked fringe folds (33-cap), interior reads, merges - the risk
   center.  Same technique; expand the trace per control branch.
3. Glue: `e1ValidPath shape` = select block; select block; option tests
   on packets (natEq vs `regZero`, brNZ) mirroring the decomposition
   branches; lca block; rank block; packet write (`regOut :=
   rankValue - 1 + 1` encoded per `decodePacket`); halt.  Compose with
   `RunsTo.trans`/`HostedAt` hosting facts from
   `programSkeleton_hosts_validPath`; result agreement + positional
   receipt equality vs the M3b-2 decomposition theorems; then the
   public `List Int` corollary via `SuccinctClassic.queryTraceResult`
   (valid branch) and `Cartesian.shape_size`.
4. Then M4 category algebra + derived literal (guard cats are already
   literal; loop caps 33/8 give the bound), M5 target Prop +
   supersession DD/doc note, M6 validator lean_exe (fixtures incl. the
   three invalid ones already checked as `rfl` examples; machine
   mutation rejection), M7 adequacy-doc discharge + final battery +
   matrix closure.

Open rows: REQ-E1-01..11 all open (machinery for 01/02/05/06 landed;
05 closes with the validator fixtures, 01/02/06 close when the concrete
program consumes them; 03/04 rank-close leg simulated, select-close and
close/LCA legs plus glue outstanding).  No closed row weakened; no
frozen identity touched.  Branch state: M0 `702cfbe`, M1 `18f35d7`,
M2 `11b8cf9`, M3a `d721ca9`, M3b-1 `e93e2ae`, M3b-2 `933955e`, M3b-3
`bd84fc6`, M3c-1a `c1e7d0a`, M3c-1b `ff03a37` + `b761581`, M3c-1c
`0ddf257` (+ this worklog commit); working tree clean at each yield.
Width/fits certificate for `rankCloseBlock` (REQ-E1-02 consumption) is
NOT yet written - add `rankCloseBlock_fits` alongside the glue (needs
`0 < c` from `bpFringeChunkBits_pos`, `0 < wordSize`/`blocksPerSuper`
from the data, and `2^c`, `2*c+2`, `L`, branch targets `< 2^w`).

Planned milestones: M1 bookkeeping repairs (stale segment-21 doc lines ->
23; 33-cap attribution; simp-arg warnings if cheap). M2 machine core (ISA +
step semantics + width predicate + DD entries). M3 program + simulation
(result agreement, receipt projection, invalid guard). M4 cost categories +
derived literal. M5 amended target Prop + supersession note. M6 validator +
doc discharge. M7 final battery + matrix closure.

## M3d BLOCKER: RESOLVED BY B6 (see the M3d-1 section at the end of this log)

The blocker recorded below was real at the time and was answered by option
(a): the B6 rung (`6775e22`..`bacd41b`) landed a charged same-block window
leg on the accepted route.  Re-verified at source this session
(`ChargedFringeWiring.lean:50-64`): the dispatcher's same-block arm is now
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment` charged at
`fringeSegment`, so BOTH arms are charged and no branch of the route
performs a per-position scan.  The `_sameBlockSegment` parameter remains
present but inert.  B6's arithmetic finding also held: the close/LCA
principled cap is a MAX over the two branches, not a sum, so
`queryCost = 207` did NOT move.  The section below is retained as the audit
record of the finding; do not act on its "coordinator decision needed".

## M3d BLOCKER (historical): the same-block LCA branch is still event-silent

Found while inventorying the close/LCA structural leg (mission milestone 2,
the flagged "last risk center").  This blocks milestones 2-7.  It does NOT
affect anything landed through M3c-6g.

### The finding

The whole-query route's `.lcaClose` instruction dispatches to
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
(`SuccinctFinalRAM.lean:2330`, reached from
`WholeQueryInstr.evalGlobalWordTrace` at `SuccinctFinalRAM.lean:3185-3191`).
That object splits on `blockOfClose blockSize leftClose = blockOfClose
blockSize rightClose` (`ChargedFringeWiring.lean:49-63`):

- CROSS-BLOCK branch: `bpChunkedCrossBlockCloseTraceResultWithRankSeed
  AllSizeStructuralAtSegments` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â properly CHARGED.  This is the B2
  charged-fringe work: every endpoint-fringe min-excess/argmin is paid for
  by chunk-table reads at the fringe segment, under literal caps.
- SAME-BLOCK branch: `localBPSameBlockCloseDecodedTraceResultWithRankSeed`
  (`ConcreteDirectoryRAM.lean:1559`) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â still EVENT-SILENT.

The same-block branch is a rank seed plus
`localBPSameBlockCloseSeededTraceResult` (`ConcreteDirectoryRAM.lean:334`),
which is exactly ONE `TraceResult.map` over
`localBPWindowBitsTraceResult` ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â and
`localBPWindowBitsTraceResult_cost` (`ConcreteDirectoryRAM.lean:225`) checks
that this contributes exactly `4` read events, independent of the query
width.  The model's charge for the whole branch is likewise the constant
`rankCost + 4` (`localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le`,
`LocalBPDecoder.lean:1179-1185`).

Inside that single `map`, the value is computed by
`localBPSeededPrefixRangeMinExcess` / `localBPSeededPrefixRangeArgMinPrefixPos`
(`LocalBPDecoder.lean:929-941`), which recurse through
`localBPSeededPrefixRangeArgMinPrefixPosFrom` (`:797-805`) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â a PER-POSITION
scan, one `localBPSeededBetterPrefixPos` comparison (`:739`) per position,
for `count = rightClose - leftClose + 1` positions.

### Why this blocks E1

Same-block means `leftClose / blockSize = rightClose / blockSize`, so
`count <= blockSize = 2 * (Nat.log2 shape.size + 1)`
(`RelativeSummary.lean:1236-1242`).  That is UNBOUNDED in the size ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â 258 at
`size = 2^128`, 2002 at `2^1000`.  So on this branch the machine must
perform Theta(log n) comparisons while the accepted receipt contains a
CONSTANT 4 window reads.  Under the frozen matrix that is jointly
unsatisfiable:

- REQ-E1-01 forbids an instruction that hides a variable-length scan, so
  each of the `count` comparisons costs at least one charged step;
- REQ-E1-06(c) demands a DERIVED all-size LITERAL total step bound with no
  size hypothesis ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â impossible against a Theta(log n) step count;
- and the obvious repair (fold the window chunk-wise against the fringe
  chunk table, as the cross-block branch does) adds read events, which
  REQ-E1-04 forbids: the read projection must be POSITIONALLY EQUAL to the
  accepted trace, which has exactly those 4 window reads.

The machine does not need more READS here ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â four words already carry the
whole window ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â it needs more STEPS than any literal allows.

### Why this is a scope decision, not a repair I may make

DD-20260717-C05-001 already decided this class of thing: it replaces "the
event-silent fringe min-excess extraction" with charged chunk-table lookups,
and it explicitly REJECTS "keeping the extraction event-silent while
re-labeling the machine 'fully charged': re-hides the scan E1 exists to
expose; forbidden."  Option B (B2) applied that conversion to the
CROSS-BLOCK fringe only.  The same-block window decode was never converted,
and searches find NO charged/chunked same-block variant anywhere in the tree
(`SameBlockClose` definitions are all event-silent; no
`localBPWindowBits`-chunked path exists).

Converting it is B2-class route work, and it necessarily perturbs the
ACCEPTED route: a charged same-block window leg adds chunk-table reads to
the accepted trace, which moves the accepted literal and therefore the
FROZEN public identity `SuccinctClassic.queryCost_eq : queryCost = 207`
(`SuccinctRMQClassic.lean:111`).  Standing rules for this rung forbid me
from touching frozen public identities or weakening closed B2/B3/B4 rows,
so I am not able to make that call unilaterally.

### IMPORTANT: the repair needs no new mathematics

A second, independent survey of the leg turned up the decisive fact.  The
value-equality the conversion needs is ALREADY PROVED AND CLOSED in-tree:

```
theorem bpFringeChunkFoldCosted_global_eq_localBPSeeded
    {window : List Bool} {seed base start count : Nat} (c : Nat)
    (hc : 0 < c) (hlen : window.length <= 32 * c)
    (hvalid : BPFringeWindowValid window seed)
    (hcount : 0 < count) (hstart : base <= start)
    (hcov : start + count <= base + window.length + 1) :
    bpFringeCandGlobal base seed start
        (bpFringeChunkFoldCosted (bpFringeChunkTable c) c window seed
          (start - base) (start + count - 1 - base)
          (Nat.min ((start + count - 1 - base) / c + 1) 33)).value.2 =
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            start count)
```
(`ChargedFringeChunks.lean:1694`)

That is EXACTLY the substitution the same-block branch needs: the 33-capped
chunk fold computes precisely the pair
`(localBPSeededPrefixRangeMinExcess, localBPSeededPrefixRangeArgMinPrefixPos)`
that `localBPSameBlockCloseSeededTraceResult` currently computes silently.
Its `hlen` side condition is discharged all-size by
`four_machineWordBits_le_32_mul_bpFringeChunkBits`
(`ChargedFringeChunks.lean:49`), the accepted four-word window fitting in 32
chunks at every size.

So option (a) below is a SUBSTITUTION exercise of the same shape B2 already
performed on the cross-block branch, not new mathematics.  Its cost is
bounded and predictable: the same-block branch gains at most 33 chunk reads
at segment 21, so the accepted literal moves from `207` to at most `240`.
That is the whole of the disruption, and it is why this is a scope call
rather than a research question.

### Status of the claim

This is documented and evidence-backed but NOT kernel-checked as an
obstruction: the step-count half rests on the informal (though routine)
observation that the listed ISA cannot produce a window argmin in O(1)
steps.  Deriving that as a checked lower bound is the same shape of argument
as the R3 obstruction and would be its own task.  I am therefore NOT
claiming OBSTRUCTED.

### Coordinator decision needed

Either (a) authorize a B2-style charged same-block window leg on the
accepted route, accepting that the accepted literal and `queryCost = 207`
move (and say whether that is this rung's work or a separate one); or
(b) direct that E1 proceed cross-block-only with the same-block branch
carried as an explicitly-argued residue (this weakens REQ-E1-03/04/06 to a
branch-restricted claim and needs a matrix amendment); or (c) treat E1 as
obstructed pending a formalized lower bound and commission that instead.

### Resume point if the answer is (a) or (b)

Milestone 1 is landed (`f2e3860`).  The cross-block branch is properly
charged and its machine block can be built without any of the above being
settled; the survey of its fold structure, caps, and segment agreement
lemmas was in progress when this blocker surfaced.  The same-block branch is
the ONLY event-silent leg found on the LCA route.

## RESUME INVENTORY: close/LCA leg (verified this session, read-only survey)

Recorded so the next session does not re-derive it.  Nothing here is
implemented.  The same-block blocker above gates USE of this, but the
cross-block half is properly charged and can be built once scope is settled.

LEG ORDER in the whole query (`E1RouteDecomposition.lean`): `select(left)`
-> `select(right-1)` -> `LCA` -> `rank(answer+1)`.  The LCA leg is THIRD of
four.  Both `_decompose_of_selects_lca_some` (`:41`) and
`_decompose_of_lca_none` (`:85`) need it, so the block must be proved for
BOTH the `some` and `none` value cases.  In the two select-miss cases
(`:121`, `:148`) the close/LCA instruction writes `none` WITHOUT running its
leaf, so the machine block must be jumped over entirely, contributing zero
receipts.

DISPATCHER (`ChargedFringeWiring.lean:49`), split on
`blockOfClose blockSize leftClose = blockOfClose blockSize rightClose`
where `blockOfClose blockSize x = x / blockSize` (`BlockLocal.lean:864`) and
`blockSize = canonicalBPRelativeSummaryBlockSizeRaw shape`
(`RelativeSummary.lean:1240`).  On the machine: `leftClose / blockSize ==
rightClose / blockSize`.

CROSS-BLOCK branch
(`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments`,
`ChargedFringeTrace.lean:922`).  Trace is EXACTLY, in this order:
  1. rank-seed@left   `localBPSeedFromRankCloseTraceResult` (segs 17/18/19 +
     <=8 chunk reads at 21)
  2a. 4 window reads at seg 0   2b. LEFT FRINGE FOLD, <=33 reads at seg 21
  3. INTERIOR, guarded by `leftBlock + 1 < rightBlock`; the `else` arm is
     `TraceResult.pure none` and is RECEIPT-EMPTY (but still costs
     comparison + branch category ticks ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â account for them)
  4. rank-seed@right   5a. 4 window reads at seg 0   5b. RIGHT FRINGE FOLD
  then a pure merge, no reads: `bpCandidateClose? (bpCandidateMerge3? ...)`
  (`Candidate.lean:24,28`).

FOLDS AND CAPS ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â two independent caps, so ONE cross-block query runs FOUR
counted loops (two rank-seed folds <=8, two fringe folds <=33):
- fringe fold `bpFringeChunkFoldComputationFrom` (`ChargedFringeTrace.lean:32`),
  iteration count LITERALLY `Nat.min (relHi / c + 1) 33`
  (`ChargedFringeTrace.lean:509` left, `:529` right); one read per
  iteration (`bpFringeChunkFoldCostedFrom_cost`,
  `ChargedFringeChunks.lean:1531`).  NO early exit -> use `RunsTo.iterate`,
  NOT `iterateUntil`.
- word-rank fold cap `bpWordChunkCount c e = Nat.min ((e-1)/c + 1) 8`
  (`ChargedWordChunks.lean:150`) ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â already simulated by
  `rankAtSegmentBlock_runsTo` (`E1RankAtBlock.lean:359`), whose `G + 4`
  lands on segment 21 at `G := 17`.
- address function `bpFringeChunkSlot c v a b = (v*(c+1) + a)*(c+1) + b`
  (`ChargedFringeChunks.lean:360`); offsets `bpFringeChunkStartOff` (`:900`),
  `bpFringeChunkEndOff` (`:904`); `c = bpFringeChunkBits m = Nat.log2 m / 8 + 1`
  (`:42`).

RECEIPT ORDER ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â there is NO route-side flip lemma.  The fold's footprint is
ASCENDING in `j` (`bpFringeChunkFoldComputationFrom_run_footprint`,
`ChargedFringeTrace.lean:141`) while `iterLog` descends.  Reconcile with
`iterLog_congr` (`E1RankBridge.lean:345`) + `iterLog_singleton_desc`
(`E1RankBridge.lean:362`), following the WORKED two-step pattern at
`E1RankTrueBlock.lean:630-641`.

SEGMENTS AND AGREEMENT LEMMAS ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â every segment this leg touches ALREADY has a
per-address lemma, so no pullback plumbing is needed:
  seg 0  window/bp code  `..._bpCode` (`Segments.lean:281`)
  seg 17/18/19 rank seed `..._rankCloseSuper/Block/Word`
                         (`ChargedRankSelectWiring.lean:154/165/176`)
  seg 20 interior        `..._canonicalComponent` (`Segments.lean:258`)
  seg 21 fringe + rank chunk table
                         `..._fringeChunkTable` (`Segments.lean:247`)
Segment 28 (`concreteBPNativeFiniteSmallSameBlockCloseTraceSegment`) is
passed but bound to `_sameBlockSegment` and is INERT ÃƒÂ¢Ã¢â€šÂ¬Ã¢â‚¬Â no machine code
should reference it.  Seg 21 is shared by the fringe fold (direct) and the
rank-seed fold (as `17 + 4`); `rfl` closes the gap
(`SuccinctFinalRAM.lean:1578`).

INTERIOR leg is NOT a loop: `canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2185`) is a five-way `if` dispatch into fixed-shape
sparse-table span reads.  Cost cap `canonicalRelativeRmmInteriorQueryCost =
240` (`InteriorDirectory.lean:1777`).

MACHINE-SIDE REUSE: `HostedAt` (`E1MachineCalculus.lean:32`), `RunsTo.trans`
(`:103`), `iterLog` (`:284`), `RunsTo.iterate` (`:302`), `iterUntilLog`
(`:338`), `RunsTo.iterateUntil` (`:378`); rank blocks
`rankAtSegmentBlock_runsTo` (`E1RankAtBlock.lean:359`, 32 instrs) and
`rankTrueCloseBlock_runsTo_hit` (`E1RankTrueBlock.lean:663`).

## M3d-1a: charged fringe fold BRIDGE LAYER (LANDED, commits `1e26b07`, `e28135b`)

New module `RMQ/Core/WordRAM/E1FringeBridge.lean`, wired into `RMQ.lean`
after `E1SelectCanonical`.  This is the arithmetic layer the fringe fold
block consumes.  BOTH arms of the post-B6 dispatcher run the same fold, so
this layer serves same-block and cross-block alike.

### Route re-verification at source (post-B6; supersedes the pre-B6 inventory)

- Dispatcher `lcaCloseTraceResultWithRankSeedAllSizeStructural`
  (`ChargedFringeWiring.lean:50`), split at `:58-59` on
  `blockOfClose blockSize leftClose = blockOfClose blockSize rightClose`.
- SAME-BLOCK arm (`:60-61`):
  `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment shape
  rankCloseTrace fringeSegment blockSize leftClose rightClose`
  (`ChargedSameBlockTrace.lean:326`).  It is
  `TraceResult.bind (localBPSeedFromRankCloseTraceResult ...) fun seed =>
  bpChunkedSameBlockCloseSeededTraceResultAtSegment ...`
  (`ChargedSameBlockTrace.lean:35`), which is in turn
  `bind (localBPWindowBitsTraceResult ...) fun window =>
  map (fun st => bpCandidateClose? (bpFringeCandGlobal base seed start st.2))
  (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
  fringeSegment c window seed relLo relHi (Nat.min (relHi / c + 1) 33))`.
  Instantiation: `base := localBPWindowBase shape blockSize leftClose`,
  `start := leftClose + 1`, `count := rightClose - leftClose + 1`,
  `relLo := start - base`, `relHi := start + count - 1 - base`.
- CROSS-BLOCK arm (`:63-64`) unchanged from the pre-B6 inventory above.
- NET EFFECT FOR E1: the same-block arm is now structurally IDENTICAL to a
  cross-block endpoint-fringe leg (rank seed, four window reads at segment
  0, one 33-capped fringe fold at segment 21, pure merge).  One machine
  fold block therefore serves every fringe fold on the route.

### The structural problem this layer solves (and why it is not the rank fold)

The fringe fold's `window` is the FOUR payload words of `localBPWindowBits`
(`LocalBPDecoder.lean:220-225`, `= (shape.bpCode.drop base).take
(4 * wordSize)`), not a single machine word.  So `bitsToNatLE window` is up
to `4 * machineWordBits` bits wide and the machine MAY NOT HOLD IT in a
register (REQ-E1-02 / INV-ADDRESS-WIDTH).  The rank fold's single "remaining
word" register trick (`E1RankBridge.lean:172` `div_pow_chunk_succ`) does not
transfer.

RESOLUTION (implemented and checked in this module): a fixed-stride
four-register representation

    windowRegsValue L R0 R1 R2 R3 = R0 + 2^L * (R1 + 2^L * (R2 + 2^L * R3))

with `L := machineWordBits shape.bpCode.length` and each `Ri` the decode of
one payload word.  Against it the fold's per-chunk advance `/ 2^c` is a
four-register shift using ONLY the per-shape CONSTANTS `2^c` and `2^(L-c)`:

    R0' = R0/2^c + (R1 % 2^c) * 2^(L-c)
    R1' = R1/2^c + (R2 % 2^c) * 2^(L-c)
    R2' = R2/2^c + (R3 % 2^c) * 2^(L-c)
    R3' = R3/2^c

and the chunk value is `R0 % 2^c`.  No variable-width shift is needed, so
the ISA constant-only `mulConst`/`divConst` suffice and no ISA amendment is
required (DD-20260718-005 stands unchanged).

### Delivered and checked in `E1FringeBridge.lean`

- `bitsToNatLE_append` - decode of a concatenation.
- `bpFringeChunkBits_le_machineWordBits` - the `c <= L` side condition,
  UNCONDITIONAL at every size (`log2 m / 8 + 1 <= log2 m + 1`, omega).  The
  block discharges its shift hypothesis with this once, all-size.
- `windowRegsValue`, `windowRegsValue_eq_bitsToNatLE` (exact for a four-word
  window whose first three words are full-width).
- `add_pow_div_pow`, `add_pow_mod_pow`, `horner_shift`.
- `windowRegsValue_shift` (the four-register advance), `windowRegsValue_mod`,
  `bpFringeWindowChunkValue_eq_windowRegs`.
- `max_sub_eq_sub`, `bpFringeChunkStartOff_eq_sub`,
  `bpFringeChunkEndOff_eq_sub` - machine truncated-subtraction forms of the
  chunk offsets (`bpFringeChunkStartOff` `ChargedFringeChunks.lean:900`,
  `bpFringeChunkEndOff` `:904`).
- `bpFringeChunkStepDecoded_eq_machine` - the decoded step
  (`ChargedFringeChunks.lean:1493`) in constant div/mul/sub vocabulary.

Verification: `lake env lean` on the module exit 0 with ZERO warnings;
`lake build RMQ` exit 0 (239/239); hygiene rg clean; `git diff --check`
clean.

NOTE ON `windowRegsValue_eq_bitsToNatLE` hypotheses: it needs the first
THREE window words full-width (`w0.length = w1.length = w2.length = L`).
This is a route-side fact of the `chunkPayloadWords` shape (all words full
except the last present one) and is discharged at canonical instantiation,
exactly as the dense select leg discharges `hlen`
(`E1SelectCanonical.lean` `canonical_denseLen`, via
`selectAlignedBitWords ... get_eq_take_drop`).  For the BP code window the
analogous characterization is
`SuccinctSpace.chunkPayloadWords_get?_eq_take_drop`
(`SuccinctSpace/WordStore.lean:274`) plus
`chunkPayloadWords_length_eq_div_add_indicator` (`:390`) - the same pair
`builtRankData_wordOffset_le` uses (`E1RankCanonical.lean:49-122`).


## M3d-1b COMPLETE: the charged fringe fold BLOCK (worker E1-R4k)

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, HEAD at yield
`56b03dd`. `lake build RMQ` exit 0 at HEAD. The fold block planned in the
RESUME POINT below is now IMPLEMENTED and compiled; the plan's four-way
merge analysis was correct and is discharged.

### PROCESS DEFECT FOUND AND CORRECTED (read this first)

Two intermediate commits of this session (`06673fd`, `9320bbf`) claimed
working lemmas that were in fact INERT COMMENT TEXT. Cause: new sections
were spliced into the file at a marker that was a SUBSTRING of a `/-!`
doc-comment line, so the insertion landed mid-comment and produced a
nested unterminated comment which swallowed the whole inserted region.
Per-file `lake env lean` reported clean because commented-out code
produces no errors.

Repaired in `22a8b90`, which also fixes every error that then surfaced.
BINDING ON SUCCESSORS: `lake build RMQ` (exit 0) is the verification
standard, not per-file `lake env lean`. A per-file check cannot
distinguish "proved" from "commented out", and cannot see stale
dependency oleans either (this session's per-file checks were also
resolving against a stale `E1FringeBridge` olean until the first real
`lake build`).

### WHAT LANDED

`RMQ/Core/WordRAM/E1FringeBridge.lean` (extended, commit `b23a20f`) -
positional shape of the accepted fold, mirroring the rank bridge:

- `bpFringeChunkSlotAt` (`:260`), `bpFringeChunkEventAt` (`:266`)
- `bpFringeChunkFoldComputationFrom_run_reads` (`:275`) - the fold's
  operational read log is the literal ascending-chunk list
- `bpFringeChunkFoldTraceResultAtSegmentWithStore_trace_map` (`:315`)
- `bpFringeStateAt` (`:349`) - the literal iterated fold state
- `bpFringeChunkFoldComputationFrom_run_value_stateAt` (`:361`)
- `bpFringeChunkFoldTraceResultAtSegmentWithStore_value_stateAt` (`:399`)

`RMQ/Core/WordRAM/E1FringeFoldBlock.lean` (NEW, ~1340 lines) - layout,
certificates, and the full simulation:

- register bank `40..62` (`:62-106`), recorded as DD-20260718-009
- `bestOfRegs` (`:114`) + `bestOfRegs_merge_some` (`:125`) - the
  option-shift convention and the shifted comparison bridge
- segments: `fringePrefix` (`:146`, 32 instrs), `fringeMerge` (`:199`,
  13), `fringeShift` (`:223`, 19), `fringeAdvance` (`:248`, 2),
  `fringeLoopBody` (`:255`, 66 total)
- cats: `fringePrefixCats` (`:269`), `fringeTailCats` (`:273`),
  `fringeMergeArmCats` (`:281`), `fringeMergeCatsAt` (`:300`),
  `fringePassCats` (`:309`), `fringeFoldCats` (`:952`)
- `fringeLoopBody_hosting` (`:319`), straightness certificates
  (`:336/:344/:351/:359`), width certificate `fringeLoopBody_fits` (`:376`)
- `fringePrefix_runsTo` (`:465`) - straight prefix, ONE charged read
- `fringeTail_runsTo` (`:564`) - four-register constant-stride shift
- `fringeMerge_runsTo` (`:661`) - THE FOUR-WAY MERGE
- `ascLog` (`:915`) + `iterLog_desc` (`:922`) - descending-counter to
  ascending-order log combinator, the general-list analogue of
  `iterLog_singleton_desc`
- `fringeFoldLoop_runsTo` (`:993`) - the whole fold
- `fringeFoldLoop_runsTo_accepted` (`:1301`) - the same against the
  ACCEPTED object `bpFringeChunkFoldTraceResultAtSegmentWithStore`

The plan's instruction counts were checked and one was wrong: the window
shift is 19 instructions, not the plan's "(17)" - three 6-instruction
Horner levels plus the final `divConst`. Body total is 66, not ~63.

### CORRECTIONS TO THE PLAN WORTH CARRYING FORWARD

1. `bitsToNatLE` is AMBIGUOUS in a `WordRAM` module: bare use resolves to
   `RMQ.WordRAM.bitsToNatLE`, but every route-side lemma is stated with
   `SuccinctSpace.bitsToNatLE`. Qualify it explicitly, as the rank block
   modules do.
2. The chunk value must be stated in the machine's SUB-DIV-MUL normal
   form (`W0 - W0 / 2^c * 2^c`), not `W0 % 2^c`: the `fringe_eval` simp
   set rewrites `%` away via `nat_mod_eq_sub_div_mul`, so a `%`-form
   hypothesis will not match.
3. Write-set predicates must be stated on LITERAL bank slots
   (`r â‰  53 âˆ§ ...`), not on the register abbrevs (`r â‰  fV âˆ§ ...`): omega
   does not see through the abbrevs in HYPOTHESES, so the preservation
   side conditions fail. Concrete-register side conditions then discharge
   by `decide`, and generic-`r` ones by the three coercion lemmas
   `fringePrefixUntouched_of_fold` / `fringeTailUntouched_of_fold` /
   `fringeMergeNe_of_fold` (`:965/:969/:973`).
4. `fringeMergeCatsAt` must NEVER be handed to `simp`: it unfolds to
   `fringeMergeArmCats (decide (startOff < endOff)) ...` and simp will
   try to evaluate the `decide`, blowing the whnf heartbeat limit. Align
   the merge segment's cats by rewriting with the prefix's `hPbest`/
   `hPCV` facts instead (pattern at `:1092`).
5. The shift exponent step `j * c + c = (j + 1) * c` is `Nat.succ_mul`,
   not omega (nonlinear in two variables).

### RESUME POINT (M3d-2: window reads, then the two dispatcher arms)

NOTHING below is implemented.

1. WINDOW-READ SUB-BLOCK. Four straight reads at segment 0 producing the
   four window registers `fW0..fW3` in the `windowRegsValue` form the
   fold consumes. Route object `localBPWindowBitsTraceResult`
   (`ConcreteDirectoryRAM.lean:208`). The caller must discharge
   `windowRegsValue_eq_bitsToNatLE` (`E1FringeBridge.lean:99`), whose
   hypotheses are that the first three window words have length exactly
   `L` - a route-side fact about `chunkPayloadWords`, to be discharged at
   canonical instantiation (same discipline the dense select leg uses for
   `hlen`).
2. THE 33-CAP INIT. The fold's iteration count is literally
   `Nat.min (relHi / c + 1) 33` (`ChargedSameBlockTrace.lean:52` for the
   same-block arm; `ChargedFringeTrace.lean:509/:529` for the two
   cross-block arms). Derive the count register by the truncated-
   subtraction cap chain `rankAtInit` uses for its 8-cap
   (`E1RankAtBlock.lean:56-62`). `fringeFoldLoop_runsTo` already takes
   `hcount : 0 < count`, which the cap identity supplies.
3. SAME-BLOCK ARM (B6's object): rank seed
   (`rankCloseBlock_runsTo_canonical`, `E1RankCanonical.lean:263`,
   already exists); window reads; the fold; then the PURE merge
   `bpCandidateClose? (bpFringeCandGlobal ...)` - no reads. Target
   `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment`
   (`ChargedSameBlockTrace.lean:326`) - the POST-B6 object.
4. CROSS-BLOCK ARM: two fringe folds plus the INTERIOR leg. The interior
   leg is NOT a loop:
   `canonicalRelativeRmmInteriorRangeMinComputation`
   (`InteriorDirectory.lean:2185`), a five-way `if` into fixed-shape
   sparse span reads; its `else` arm is receipt-EMPTY but still costs
   comparison/branch ticks.
5. CANONICAL-STORE FORM mirroring `rankCloseBlock_runsTo_canonical` /
   `selectCloseBlock_runsTo_canonical`. Segment agreement lemmas: seg 0
   `..._bpCode` (`Segments.lean:281`), seg 17/18/19
   `..._rankCloseSuper/Block/Word`
   (`ChargedRankSelectWiring.lean:154/165/176`), seg 20
   `..._canonicalComponent` (`Segments.lean:258`), seg 21
   `..._fringeChunkTable` (`Segments.lean:247`). Segment 28 is INERT
   after B6 - no machine code should reference it.
6. WHOLE-QUERY GLUE via `E1RouteDecomposition`. NAME THE ACCEPTED OBJECT
   EXPLICITLY: `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
   (`SuccinctFinalRAM.lean:2330`, consumed at `:3279`/`:3733`), NOT the
   legacy near-homonym `concreteBPNativeLCACloseGlobalWordTraceResult`
   (`:2271`). They differ by one suffix and sit 59 lines apart.
7. Then M4 (derived literal step total), M5 (amended target Prop +
   obstruction supersession), M6 (validator `lean_exe`), M7 (docs +
   matrix closure + final battery, including the coordinator-queued
   PAPER_MODEL_ADEQUACY and B6-matrix edits recorded in the COORDINATOR
   DIRECTIVES section below).

### MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN. This session closed none and weakened
none. Partial evidence accumulated for REQ-E1-01/02/04/06 is recorded in
the matrix evidence column; it is component-level (the fringe fold block)
and does NOT discharge any row, all of which are whole-query scoped.
## RESUME POINT (M3d-1b: the fringe fold BLOCK) - SUPERSEDED, IMPLEMENTED in M3d-1b above

Everything below is a PLAN, verified against source this session but NOT
written as Lean.  It is recorded in the style that the M3c-5c "STAGE-2
LAYOUT" section used, which the next session then implemented verbatim.

TARGET: a new file `RMQ/Core/WordRAM/E1FringeFoldBlock.lean`, importing
`RMQ.Core.WordRAM.E1FringeBridge` and `RMQ.Core.WordRAM.E1RankAtBlock`
(for `rankAtSegmentBlock` and the shared bank/macros).

TEMPLATE to mirror: `rankFalseLoopFold_runsTo` + `rankAtSegmentBlock_runsTo`
(`E1RankAtBlock.lean:151` and `:359`).  Read that pass-lemma proof first;
the register-invariant / `straightRegs_preserves` / `writes_eval` skeleton
transfers line for line.

### THE ONE STRUCTURAL DIFFERENCE FROM EVERY EXISTING FOLD BLOCK

The fringe loop body is NOT branch-free.  `bpFringeMergeCand`
(`ChargedFringeChunks.lean:892`) is a three-way match, and the candidate is
gated by `bpFringeChunkStartOff < bpFringeChunkEndOff`.  A branch-free
encoding would need `take * X` with `take` a RUNTIME 0/1 value, and the ISA
has `mulConst` only (constant multiplier) - deliberately, per
DD-20260718-005.  So the body must branch.

CONSEQUENCE FOR THE PROOF: `RunsTo.straight` (`E1StraightLine.lean`) runs
only branch-free segments, so the per-pass lemma is NOT one
`RunsTo.straight` call as in `rankFalseLoopFold_runsTo`.  It is a straight
prefix, then a FOUR-WAY case analysis, then a shared straight suffix,
composed with `RunsTo.brNZ_taken` / `RunsTo.brNZ_not_taken` / `RunsTo.trans`.
The four cases are exactly the arms of the route-side expression:
  (i)   `not (startOff < endOff)`          -> candidate `none`, best unchanged
  (ii)  `startOff < endOff`, best `none`   -> best := candidate
  (iii) `startOff < endOff`, best `some`, `cand.1 < best.1`      -> best := cand
  (iv)  `startOff < endOff`, best `some`, `not (cand.1 < best.1)` -> unchanged
Budget the pass lemma at roughly four times the `rankFalseLoopFold_runsTo`
body-invariant block; that is the single largest remaining proof on the
rung and it is the reason this session stopped here rather than starting it.

### PLANNED REGISTER BANK (fresh; 0..7 skeleton, 8..27 component, 28..39 select)

Allocate the fringe bank at 40..62 and record it as a DD entry when the
block is written (precedent: DD-20260718-007 for the select extension bank):
  40 `fOne` (pinned 1), 41 `fC` (pinned c),
  42..45 `fW0..fW3` (the four window registers),
  46 `fAcc` (fold `st.1`), 47 `fBV` (best value, option-shifted: 0 = none),
  48 `fBP` (best position), 49 `fJC` (`j * c`),
  50 `fLo` (relLo), 51 `fHi` (relHi), 52 `fCnt` (remaining count),
  53 `fV` (chunk value), 54 `fA` (startOff), 55 `fB` (endOff),
  56 `fSlot`, 57 `fE` (decoded entry), 58 `fCV`, 59 `fCP` (candidate),
  60..62 `fT`/`fU`/`fX` (scratch - allocate rather than share; the
  preservation side conditions are cheaper that way).
CHECK BEFORE COMMITTING: the LCA leg runs THIRD (after both select legs,
`E1RouteDecomposition.lean`), so the select extension bank 28..39 is dead by
then; a fresh bank is still preferred so the glue never has to reason about
liveness across legs.

### PLANNED LOOP BODY (per pass, at loop base `LB`)

Immediates available as per-shape constants (no register needed): `c`,
`c+1`, `2*c+2`, `(c+1)*(2*c+2)`, `2^c`, `2^(L-c)`.

  1. chunk value          `divConst fT fW0 2^c; mulConst fT fT 2^c;
                           sub fV fW0 fT`                        (3)
  2. start offset         `sub fT fLo fJC; const fA c; sub fU fA fT;
                           sub fA fA fU`                         (4)
                          [justified by `bpFringeChunkStartOff_eq_sub`;
                           `max relLo (j*c) - j*c = relLo - j*c` is
                           `max_sub_eq_sub`, so NO max instruction]
  3. end offset           `add fT fHi fOne; const fU c; add fU fJC fU;
                           sub fX fT fU; sub fB fT fX; sub fB fB fJC` (6)
                          [`bpFringeChunkEndOff_eq_sub`]
  4. slot                 `mulConst fSlot fV (c+1); add fSlot fSlot fA;
                           mulConst fSlot fSlot (c+1);
                           add fSlot fSlot fB`                   (4)
                          [`bpFringeChunkSlot c v a b = (v*(c+1)+a)*(c+1)+b`,
                           `ChargedFringeChunks.lean:360`]
  5. read + decode        `readMem fE S fSlot; sub fE fE fOne`   (2)
                          [`decodeRead - 1 = (map bitsToNatLE).getD 0`,
                           `E1RankBridge.lean:182`]
  6. candidate value      `divConst fT fE (c+1); divConst fU fT (2*c+2);
                           mulConst fU fU (2*c+2); sub fT fT fU;
                           add fCV fAcc fT; sub fCV fCV fC`      (6)
  7. candidate position   `divConst fT fE (c+1); mulConst fT fT (c+1);
                           sub fT fE fT; add fCP fJC fT`         (4)
     [6 and 7 MUST precede 8: the candidate reads the OLD accumulator
      `st.1`, per `bpFringeChunkStepDecoded`]
  8. accumulator advance  `divConst fT fE ((c+1)*(2*c+2));
                           add fAcc fAcc fT; sub fAcc fAcc fC`   (3)
  9. merge (BRANCHING, ~10 instrs, four arms as listed above):
       `natLt fT fA fB; brNZ fT MERGE; brNZ fOne SHIFT`
       `MERGE: brNZ fBV CMP; add fBV fCV fOne; move fBP fCP;
               brNZ fOne SHIFT`
       `CMP: add fT fCV fOne; natLt fU fT fBV; brNZ fU TAKE;
             brNZ fOne SHIFT`
       `TAKE: add fBV fCV fOne; move fBP fCP`   (falls through)
     [option-shift convention: `fBV = value + 1`, `0 = none`, matching
      `decodePacket` (`E1QueryProgram.lean`).  The `cand.1 < best.1` test is
      therefore `fCV + 1 < fBV`.]
 10. window shift (17)    three copies of
                           `divConst fT fWi 2^c; divConst fU fW(i+1) 2^c;
                            mulConst fX fU 2^c; sub fX fW(i+1) fX;
                            mulConst fX fX 2^(L-c); add fWi fT fX`
                          then `divConst fW3 fW3 2^c`.
                          IN-ORDER (i = 0,1,2) is correct and needs no
                          temporaries: `Wi'` depends only on `Wi` and
                          `W(i+1)`, and `Wi` is dead once written.
                          [justified by `windowRegsValue_shift`]
 11. counter + back edge  `add fJC fJC fC; sub fCnt fCnt fOne;
                           brNZ fCnt LB`                         (3)

Total ~63 instructions, four branch points.  Per-pass category log is
therefore NOT a single constant list: it depends on which merge arm runs.
Follow the `selectFoldCats` / `denseLegCats` precedent
(`E1SelectBlock.lean`, `E1DenseSelectBlock.lean`) - define the per-pass cats
as a FUNCTION of the route-side branch condition, never assert a numeral.

### RECEIPT ORDER (unchanged from the pre-B6 inventory, re-verified)

One read per iteration, ascending in `j`
(`bpFringeChunkFoldComputationFrom_run_footprint`,
`ChargedFringeTrace.lean:141`), while `iterLog` descends.  Reconcile with
`iterLog_congr` (`E1RankBridge.lean:345`) + `iterLog_singleton_desc`
(`:362`), following the worked two-step pattern at
`E1RankTrueBlock.lean:630-641`.  NO early exit in this fold, so use
`RunsTo.iterate` (`E1MachineCalculus.lean:302`), NOT `iterateUntil`.

Iteration count is LITERALLY `Nat.min (relHi / c + 1) 33`
(`ChargedSameBlockTrace.lean:52` for the same-block arm;
`ChargedFringeTrace.lean:509/:529` for the two cross-block arms) - derive
the count register by the same truncated-subtraction cap chain
`rankAtInit` uses for its 8-cap (`E1RankAtBlock.lean:56-62`).

### AFTER THE FOLD BLOCK, the remaining dependency order is unchanged

1. window-read sub-block (four reads at segment 0, straight-line; the
   route object is `localBPWindowBitsTraceResult`,
   `ConcreteDirectoryRAM.lean:208`) + the rank-seed reuse
   (`rankCloseBlock_runsTo_canonical` already exists).
2. same-block arm assembly (rank seed; window reads; fold; pure merge
   `bpCandidateClose? (bpFringeCandGlobal ...)`, no reads).
3. cross-block arm (two fringe folds + the INTERIOR leg - NOT a loop:
   `canonicalRelativeRmmInteriorRangeMinComputation`,
   `InteriorDirectory.lean:2185`, a five-way `if` into fixed-shape sparse
   span reads; note its `else` arm is receipt-EMPTY but still costs
   comparison/branch ticks).
4. canonical-store form mirroring `rankCloseBlock_runsTo_canonical`
   (`E1RankCanonical.lean:263`) / `selectCloseBlock_runsTo_canonical`
   (`E1SelectCanonical.lean`).  Segment agreement lemmas: seg 0
   `..._bpCode` (`Segments.lean:281`), seg 17/18/19
   `..._rankCloseSuper/Block/Word`
   (`ChargedRankSelectWiring.lean:154/165/176`), seg 20
   `..._canonicalComponent` (`Segments.lean:258`), seg 21
   `..._fringeChunkTable` (`Segments.lean:247`).  Segment 28 is INERT after
   B6 (bound to the unused `_sameBlockSegment`) - no machine code should
   reference it.
5. whole-query glue via `E1RouteDecomposition`, then M4-M7 per the mission.

### STATE AT YIELD

Branch `claude/b1-b2-charged-fringe-tables`, HEAD `e28135b`, working tree
CLEAN, `lake build RMQ` exit 0 at every commit of this session.  No closed
B2/B3/B4/B6 row weakened; no frozen public identity touched; no route-side
file modified this session (the two commits are additive: one new module
plus its `RMQ.lean` import line).  Matrix rows REQ-E1-01..11 all remain
Open; this session closed none and weakened none.

## COORDINATOR DIRECTIVES received this session (verified at source, binding on the resume)

Delivered mid-session by the coordinator after the parallel B6 reconstruction
of this branch's base `bacd41b` and a charge-policy audit.  Every claim below
was re-verified at source before being recorded here.

### D1. B6 reconstruction of `bacd41b`: PROCEED, no blocking defect

Three conditions attach.

(a) TARGET THE POST-B6 TRACE.  B6 changed the same-block branch's trace
    CONTENT (it now emits per-chunk `readWord fringeSegment` events).  Any
    receipt work drafted against the pre-swap trace is invalid.  The M3d-1a
    section above was written after this swap and targets the post-B6 object
    (`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment`,
    `ChargedSameBlockTrace.lean:326`); the pre-B6 inventory earlier in this
    log is superseded for the same-block arm.

(b) LIVE NAMING FOOTGUN - VERIFIED AT SOURCE.  Two definitions differ by ONE
    SUFFIX and sit 59 lines apart:
      `concreteBPNativeLCACloseGlobalWordTraceResult`
        (`SuccinctFinalRAM.lean:2271`) - LEGACY, NOT on the accepted route
      `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
        (`SuccinctFinalRAM.lean:2330`) - ACCEPTED
    The accepted whole-query route uses the `...AllSizeStructural` one, at
    `SuccinctFinalRAM.lean:3279` and `:3733` (both verified: the
    `WordRAM.TraceResult.map (fun answer? => state.setOpt dst answer?)`
    arms).  Name it EXPLICITLY in every positional-equality statement and
    double-check each one; a silent bind to the legacy name would produce a
    theorem that looks right and proves nothing about the accepted route.

(c) `queryCost = 207` is CONFIRMED UNCHANGED by the reconstruction
    (`SuccinctRMQClassic.lean:111`, re-checked present at this HEAD).  The
    REQ-E1-06 literal-bound clause may rely on it.

### D2. Select-close occurrence guard: adjudicated a REPRESENTATION ARTIFACT

The audit flagged the select-close leaf's guard
`if idx < occurrenceCount bits target` (`ChargedRankSelectLeafTrace.lean:1167`)
as an undisclosed Theta(n) event-silent computation, since
`occurrenceCount bits target = rankPrefix target bits bits.length` is a full
list traversal.  The coordinator ADJUDICATED it a representation artifact,
not algorithmic work, because the collapsing bridge is already checked
in-tree.  Both lemmas re-verified at source this session:

  `GenericSelect.falseSelectOccurrenceCount_eq`
    (`RMQ/Core/GenericSelect/BPCompat.lean:20-22`, proof is `rfl`):
    `falseSelectOccurrenceCount shape = occurrenceCount shape.bpCode false`
  `falseSelectOccurrenceCount_eq_size`
    (`RMQ/Core/SuccinctSelect/CloseSelect/BuiltRouting/SlotBasics.lean:35-38`,
     via `SuccinctSpace.bpCode_rankFalse_full`):
    `falseSelectOccurrenceCount shape = shape.size`

Composing: `occurrenceCount shape.bpCode false = shape.size`.  So the guard
is `idx < shape.size` - a comparison against an INPUT quantity the machine
already holds in a register.

BINDING ON THE MACHINE: implement this guard as a REGISTER COMPARISON
against the size input, justified by those two lemmas.  NOT as a loop of any
kind.  Say so explicitly in the REQ-E1-01 / REQ-E1-06 evidence rows.
(`E1SelectDispatch.lean`'s prologue already computes the occurrence count
into `rA` as a per-shape constant register and does `natLt` on it - so the
existing dispatch is already compliant; what is owed is the CITATION of the
two lemmas in the evidence row, not a code change.  VERIFY that when closing
the row.)

SAME CATEGORY (same treatment, same paragraph in the doc):
  `queryOccurrence data idx = Nat.min idx bits.length`,
  `queryPos`, `machineWordBits` - Lean-level list/recursion artifacts whose
  values are O(1)-available.

### D3. M7 doc work: tighten PAPER_MODEL_ADEQUACY.md from absolute to enumerated

`docs/PAPER_MODEL_ADEQUACY.md` currently asserts "There is no event-silent
computation left on the accepted route" and "what remains uncharged is
exactly the register list above".  BOTH ARE TOO ABSOLUTE.  Required
rewording, to be folded into M7:

- No event-silent computation whose cost GROWS WITH INPUT SIZE (the
  enumerated form), rather than the unqualified "none left".
- Add an explicit "representation artifacts" paragraph naming the D2
  instances WITH their bridge lemmas, and stating the distinguishing
  principle: a scan that computes the ANSWER must be charged; a Lean-level
  traversal whose value is checked-equal to an input parameter or to a
  charged read is a representation artifact.
- Add the same-block enumerated exception the audit asked for.

## M3d-2 COMPLETE: the whole charged fringe ARM (worker E1-R4l)

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, session base
`fb1d292`. `lake build RMQ` exit 0 at EVERY commit of this session.

Items 1 and 2 of the previous RESUME POINT (window reads, 33-cap init)
are IMPLEMENTED, and the session went further: the whole fringe arm now
runs end to end against the named accepted objects, on both the receipt
and the value side. Items 3-7 of that resume point remain open.

### WHAT LANDED

One NEW module, `RMQ/Core/WordRAM/E1FringeArmBlock.lean` (~1000 lines),
namespace `RMQ.WordRAM.E1FringeArmBlock`, plus its `RMQ.lean` import line.
No route-side file was modified; the change is purely additive.

Commits, in order:

- `2a9e210` M3d-2a: window-read sub-block and derived 33-cap init
- `91ddc5d` M3d-2b: receipt/value/Horner bridges, prologue composition
- `eb31429` M3d-2c: fringe leg composition, receipt bridges to both arms
- `0a6f956` M3d-2d: the `bpFringeCandGlobal` epilogue (first form)
- `6de78f2` M3d-2e: whole arm; epilogue rewritten to pin its own constant
- `eb262f9` M3d-2f: value bridges to the named accepted arm objects

Key objects (file:line exact in `E1FringeArmBlock.lean` at `eb262f9`):

- `fBase 63`, `fBB 64`, `fSeed 65`, `fStart 66`, `fRV 67`, `fRP 68` â€”
  bank extension, recorded as DD-20260718-010.
- `readBits` (`:51`), `windowBitsOfStore` (`:55`) â€” the store-side window.
- `fringeWindowRead` (`:90`, 11 instructions, FOUR reads),
  `fringeArmInit` (`:119`, 10 instructions), `fringeArmPrologue` (`:135`,
  21 instructions).
- `fringeCandGlobal` (`:715`, 7 instructions, exit `E+7`).
- `cap_chain_eq_min` (`:239`), `cap_count_pos` (`:245`) â€” the DERIVED
  33-cap; `cap_count_pos` is exactly the fold block's `hcount`.
- `fringeArmPrologue_fits` (`:210`) â€” constructor-exhaustive width
  certificate, no wildcard arm.
- `fringeWindowRead_runsTo` (`:270`), `fringeArmInit_runsTo` (`:326`),
  `fringeArmPrologue_runsTo` (`:473`).
- `windowReadEvents_eq_route` (`:393`) /
  `windowReadEvents_eq_route_windowBits` (`:405`) â€” POSITIONAL receipt
  bridges to `localBPBlockWordsTraceResultWithStore`
  (`ConcreteDirectoryRAMStoreParam.lean:4071`) and
  `localBPWindowBitsTraceResultWithStore` (`:4152`).
- `route_windowBits_eq_windowBitsOfStore` (`:422`) â€” the route object's
  window bits ARE the concatenation of the four words the machine's own
  charged reads return (value dependency, not a spec copy).
- `windowRegsValue_of_readBits` (`:443`) â€” the Horner bridge supplying
  the fold block's `hW`.
- `fringeLeg_runsTo` (`:550`) â€” prologue + fold, `A -> A+88`.
- `fringeLeg_trace_eq_leftArm` (`:618`) / `_rightArm` (`:647`).
- `fringeCandGlobal_runsTo` (`:747`) â€” the two-arm rebase.
- `fringeArm_runsTo` (`:904`) â€” THE WHOLE ARM, `A -> A+95`.
- `leftArm_value_eq` (`:987`) / `rightArm_value_eq` (`:1018`) â€” value
  bridges to the NAMED accepted objects
  `bpChunkedLeft/RightFringeCandidateSeededTraceResultAtSegmentWithStore`
  (`ChargedFringeTrace.lean:708`/`:731`).

Arm layout at base `A` (95 instructions): prologue `A..A+20`, fold loop
base `A+21` (exit `A+88`), epilogue `A+88..A+94`, exit `A+95`.

### GOTCHAS RECORDED THIS SESSION (carry forward)

1. `omega` DOES handle `min`/`max`, but only after `show ... = min x k`
   â€” a goal written with `Nat.min` does not match, and `rw [Nat.min_def]`
   fails for the same reason. Worse, `omega` then still fails on
   `min (relHi / c + 1) 33` because division by a VARIABLE divisor is an
   opaque atom whose non-negativity omega loses; `generalize relHi / c = q`
   first. Both fixes are in `cap_chain_eq_min` / `cap_count_pos`.
2. `hf k _ _ (by omega) rfl (by omega)` fetch-fact helpers fail at `k = 0`
   because the target index `m` is still a metavariable when `omega` runs.
   Give `m` explicitly at the zero case (pattern at `:756`).
3. Side conditions of the shape `(regs.write fT 1) fBV = 0` do NOT close
   by `rw [hbvT]` even with `hbvT` in hand: the register abbrevs are
   reducible and the goal is already in numerals, so the rewrite is not
   syntactically applicable. Use `simpa [RegFile.write, fT, fBV] using hbv`.
4. `FringeFoldUntouched`-shaped side conditions on CONCRETE bank slots
   close by `decide`, not by `simp [FringeFoldUntouched]`.
5. The width predicate is `Instr.FieldsFit w` (`E1Machine.lean:503`), a
   `Prop`, NOT a `Bool`-valued `Instr.fits`. `divConst` additionally
   requires `0 < k`, so a width certificate over a segment containing
   `divConst _ _ c` needs `0 < c` as a hypothesis.
6. Splicing into a Lean file at a `/-!` marker remains hazardous (the
   defect the previous session recorded). This session appended only
   immediately BEFORE the `end <namespace>` lines and verified every
   claimed theorem with `#print axioms`, which is the cheap independent
   check that a name is a real constant rather than comment text.

### VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at all six commits. `#print axioms` run on every
theorem this session claims: `fringeWindowRead_runsTo`,
`fringeArmInit_runsTo`, `fringeArmPrologue_fits`,
`fringeArmPrologue_straight`, `cap_chain_eq_min`, `cap_count_pos`,
`readBits_decode`, `flatten_readStorePayloadWordValue`,
`fringeArmPrologueCats_memoryRead_count`, `windowReadEvents_eq_route`,
`windowReadEvents_eq_route_windowBits`,
`route_windowBits_eq_windowBitsOfStore`, `windowRegsValue_of_readBits`,
`localBPWindowBase_eq`, `fringeArmPrologue_runsTo`, `fringeLeg_runsTo`,
`fringeLeg_trace_eq_leftArm`, `fringeLeg_trace_eq_rightArm`,
`fringeCandGlobal_runsTo`, `bestOfRegs_isSome`, `fringeArm_runsTo`,
`leftArm_value_eq`, `rightArm_value_eq` â€” every one reports only
`propext` / `Classical.choice` / `Quot.sound`, never `sorryAx`. Hygiene
`rg` clean on the new module; `git diff --check` clean;
`design_decision_check.ps1 -Strict -Base d90b062` exit 0 (40 changed
files).


### FINDING FOR THE COORDINATOR: `scripts/axiom_check.lean` is BROKEN at base

Not fixed here, and deliberately so: `scripts/axiom_check.lean` is in the
file set assigned to the concurrent `claude/a07-blocker-repairs` worker,
so this session reports rather than edits. BOTH defects are PRE-EXISTING
at the coordinator-accepted base `d90b062`; neither was introduced by
this branch.

1. UNBUILDABLE IMPORT. Line 4 is `import RMQ.Core.GenericSelectBPCompat`.
   That module exists as a source file
   (`RMQ/Core/GenericSelectBPCompat.lean`) but is NOT in `RMQ.lean`'s
   import closure, so `lake build RMQ` never produces its olean and the
   script fails to LOAD: "object file ... RMQ.Core.GenericSelectBPCompat
   .olean ... does not exist". A separate
   `lake build RMQ.Core.GenericSelectBPCompat` (exit 0) makes it loadable.

2. STALE CONSTANT. Once loadable, line 975 is `#print axioms
   RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace
   Result_nonSyntheticWeight_sum_le_76` â€” an UNKNOWN CONSTANT. The tree
   carries `..._nonSyntheticWeight_sum_le_207`; the `_76` name is a
   leftover from before the bound became 207. So the script exits 1 and
   that assertion has been checking nothing.

Net effect: `lake env lean scripts/axiom_check.lean` exits 1 at this base,
so the delegation's "MUST exit 0" battery item cannot be satisfied by any
worker until this script is repaired. Substantively the run is clean â€”
with the dependency built, the 2430 lines of output contain ZERO
`sorryAx` â€” but the script itself does not certify that, because it
aborts. This is the same class as the trust-base defect the external
blind audit found. `scripts/wordram_axiom_check.lean` and
`scripts/headline_axiom_check.lean` both exit 0 at this HEAD.

### MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN. This session closed none and weakened
none. Evidence accumulated for REQ-E1-01/02/04/06 is recorded in the
matrix evidence column; it is component-level (now a whole fringe arm
rather than only the fold) and does NOT discharge any row, all of which
are WHOLE-QUERY scoped.

### RESUME POINT (M3d-3: the same-block arm, then the cross-block arm)

NOTHING below is implemented.

1. ADDRESS PREAMBLE. `fringeArm_runsTo` takes `fBase`, `fBB`, `fLo`,
   `fHi`, `fAcc`, `fSeed`, `fStart` as register HYPOTHESES. A whole arm
   still needs the straight-line code that computes them from the query
   operands: `bpWindowFirstWord` (`E1FringeArmBlock.lean:373`) is
   `blockStartOf blockSize (blockOfClose blockSize close) / L`, and
   `localBPWindowBase` is that times `L` (`localBPWindowBase_eq:380`).
   `blockOfClose` and `blockStartOf` are constant div/mul by `blockSize`,
   so this is a short straight segment â€” but CHECK whether `blockSize` is
   a per-shape constant on the accepted route before encoding it as an
   immediate; if it is not, the ISA has no variable-divisor instruction
   and the preamble needs rethinking. THIS IS THE FIRST THING TO VERIFY.
2. SAME-BLOCK ARM (B6's object). Rank seed
   (`rankCloseBlock_runsTo_canonical`, `E1RankCanonical.lean:263`,
   already exists); window reads and fold now exist as `fringeLeg_runsTo`;
   then the PURE merge `bpCandidateClose? (bpFringeCandGlobal ...)` â€” no
   reads. Target
   `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegment`
   (`ChargedSameBlockTrace.lean:326`), the POST-B6 object - but PREFER its store-parameterized twin `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore` (`:340`), the form every block in this rung targets. Its 33-cap
   init is at `ChargedSameBlockTrace.lean:52` â€” CONFIRM it is the same
   `Nat.min (relHi / c + 1) 33` shape `cap_chain_eq_min` already covers.
3. CROSS-BLOCK ARM. Two fringe arms (both now available as
   `fringeArm_runsTo`, instantiated left and right via
   `leftArm_value_eq` / `rightArm_value_eq`) plus the INTERIOR leg. The
   interior leg is NOT a loop:
   `canonicalRelativeRmmInteriorRangeMinComputation`
   (`SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory.lean:2185`), a five-way `if` into fixed-shape
   sparse span reads; its `else` arm is receipt-EMPTY but still costs
   comparison/branch ticks, so it needs a route-indexed category log in
   the `fringeCandGlobalArmCats` style.
4. CANONICAL-STORE FORM mirroring `rankCloseBlock_runsTo_canonical` /
   `selectCloseBlock_runsTo_canonical`. This is where the THREE window
   full-width hypotheses of `windowRegsValue_of_readBits` get discharged,
   via `SuccinctSpace.chunkPayloadWords_get?_eq_take_drop`
   (`SuccinctSpace/WordStore.lean:274`) plus
   `chunkPayloadWords_length_eq_div_add_indicator` (`:390`) â€” the same
   pair `builtRankData_wordOffset_le` uses
   (`E1RankCanonical.lean:49-122`). Segment agreement lemmas: seg 0
   `..._bpCode` (`Segments.lean:281`), seg 17/18/19
   `..._rankCloseSuper/Block/Word`
   (`ChargedRankSelectWiring.lean:154/165/176`), seg 20
   `..._canonicalComponent` (`Segments.lean:258`), seg 21
   `..._fringeChunkTable` (`Segments.lean:247`). Segment 28 is INERT
   after B6 â€” no machine code should reference it.
5. WHOLE-QUERY GLUE via `E1RouteDecomposition`. NAME THE ACCEPTED OBJECT
   EXPLICITLY:
   `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
   (`SuccinctFinalRAM.lean:2330`, consumed at `:3279`/`:3733`), NOT the
   legacy near-homonym `concreteBPNativeLCACloseGlobalWordTraceResult`
   (`:2271`).
6. Then M4 (derived literal step total â€” note the arm is now a known
   95 instructions plus `67 * count` for the fold, which with the
   derived cap `count <= 33` gives a literal per-arm bound; derive it,
   do not assert it), M5 (amended target Prop + obstruction
   supersession), M6 (validator `lean_exe`), M7 (docs + matrix closure +
   final battery, including the coordinator-queued PAPER_MODEL_ADEQUACY
   and B6-matrix edits in the COORDINATOR DIRECTIVES section above).

## M3d-3 (worker E1-R4m): address preamble gate, same-block arm, and a NEW ISA-level finding on the INTERIOR leg

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, session base
`74ada9e`. `lake build RMQ` exit 0 at EVERY commit. Commits:

- `b3eba0d` M3d-3a: the whole same-block close arm
- `e4aa8d0` M3d-3b: the address preamble (risk gate discharged)

### 1. THE ADDRESS-PREAMBLE RISK GATE: PASSES (verified at source)

The resume inventory's first task was to establish whether `blockSize` is
a per-shape constant on the accepted route, since the ISA has `divConst`
only. IT IS. Verified at source, not assumed:

- `blockOfClose blockSize close = close / blockSize` and
  `blockStartOf blockSize block = block * blockSize`
  (`BlockLocal.lean:863`/`:866`) take `blockSize` as a PARAMETER, so the
  classification lives entirely at the call sites.
- Every accepted-route call site binds
  `canonicalBPRelativeSummaryBlockSizeRaw shape`
  (`ChargedFringeWiring.lean:36` and `:57`,
  `ChargedFringeTrace.lean:928` and `:1151`,
  `SuccinctFinalRAM.lean:2356-2360`).
  `canonicalBPRelativeSummaryBlockSizeRaw shape = 2 * (Nat.log2 shape.size + 1)`
  (`RelativeSummary.lean:1240`) - a function of `shape` ALONE, never of
  `close`/`left`/`right` or of any value read from memory, and always
  `>= 2`.
- The other route divisors are likewise shape-determined:
  `wordSize = machineWordBits shape.bpCode.length` (`SuccinctRank.lean:38`,
  positive by `machineWordBits_pos:41`); the chunk width
  `c = bpFringeChunkBits shape.bpCode.length` and its mixed radices
  `c + 1`, `(c+1)*(2*c+2)` (`ChargedFringeChunks.lean:42`, `:1493-1502`);
  `layout.macroSize = (Nat.log2 shape.size + 1)^2`
  (`RelativeSummary.lean:1276-1292`, positive by `Valid.macroSize_pos:1361`).
  In the chunk-entry decode the memory-read value is the NUMERATOR, never
  the divisor.

GOTCHA WORTH CARRYING: the zero-able twin
`canonicalBPRelativeSummaryBlockSize` (`RelativeSummary.lean:1469`, which
is `if active then raw else 0`) is used ONLY by the legacy dispatcher
`ConcreteDirectory.lean:122-136` behind the near-homonym
`concreteBPNativeLCACloseGlobalWordTraceResult`
(`SuccinctFinalRAM.lean:2271`) - the object the delegation correctly told
us NOT to bind. Machine code must generate its immediates from `...Raw`;
generating them from the guarded name would produce `k = 0` on inactive
shapes and fail the `0 < k` arm of `Instr.FieldsFit` for a leg that in
fact never executes. (Even the legacy route short-circuits the zero case
before any division, so no route divides by zero.)

Discharged constructively in `e4aa8d0`: `windowAddr` is FOUR instructions
(`divConst`/`mulConst` with per-shape constant immediates only), with
`windowAddr_fits` carrying the positivity side conditions and
`windowAddr_runsTo_route` proving the outputs ARE the route's
`bpWindowFirstWord` and `localBPWindowBase`. NO new instruction was
invented and none is needed for the preamble.

### 2. NEW FINDING, NOT THE DIVISOR ONE: the INTERIOR leg needs a RUNTIME `Nat.log2`

This is a DIFFERENT ISA gap in the same class, found while running the
gate, and it is a COORDINATOR DECISION ITEM. It does not affect the
fringe or same-block arms; it blocks resume item 3 (the interior leg) and
therefore items 5-7.

Verified at source. `canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2185-2209`) is the five-way `if` the prior
inventory describes, and its arms call:

- `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`
  (`InteriorDirectory.lean:2112-2126`), which computes
  `let level := Nat.log2 count` and `let span := bpSparseLogSpan count`;
- `canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation`
  (`InteriorDirectory.lean:2128-2142`), same shape on `macroSpanCount`.

`bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount`
(`SparseArgMin.lean:598-599`). The argument `count` / `macroSpanCount` is
RUNTIME-derived (the interior block span of the query, i.e. a function of
`left`/`right`), NOT shape-determined. `level` then feeds the address
`bpGlobalSparseCellSlot macroCount macroStart level = level * macroCount + macroStart`
(`LocalGlobalSparse.lean:200-202`), so the machine MUST compute it to
reproduce the accepted read addresses; there is no way to route around it.

WHY THIS IS NOT AN EXPRESSIVENESS OBSTRUCTION: the existing ISA CAN
compute both, without any new instruction - `level` by repeated
`divConst _ _ 2` halving, `span` by repeated `mulConst _ _ 2` doubling.
Both the divisor and the multiplier are the literal constant `2`. So the
machine exists.

WHY IT IS NEVERTHELESS A BLOCKER FOR THE FROZEN TARGET: the loop runs
`Nat.log2 count` times, and `count` is bounded only by shape-growing
quantities (`layout.macroSize` in the local arm, `macroSampleCount` in the
global arm). There is therefore NO literal all-size cap on the iteration
count. That contradicts REQ-E1-06(c) as frozen - "an all-size literal
`totalSteps <= <literal>` derived by `rfl`/omega ..., no size hypothesis" -
and hence REQ-E1-07, whose Prop bundles that literal bound.

Structurally this is the SAME SHAPE as the refuted
`E1R3FamiliarMachineTarget` obstruction (event-silent work with no literal
cap), but MUCH weaker: it is log-many steps, not per-position linear-many,
and every iteration IS charged. IMPORTANT CONSEQUENCE FOR M5: the
delegation's planned supersession wording - "after B6 no branch of the
accepted route performs a per-position scan; every loop is a chunk fold
under a literal cap" - is TRUE for the first clause but FALSE as written
for the second. The interior leg's log2/span computation is a loop that is
NOT a chunk fold and NOT under a literal cap. The M5 note must be
rewritten to say so, or it would be an overclaim.

OPTIONS FOR THE COORDINATOR (not chosen here; the delegation forbids
inventing a workaround instruction):

(a) Amend REQ-E1-06(c) to a literal-plus-word-width bound,
    `totalSteps <= A + B * machineWordBits shape.bpCode.length` with `A`
    and `B` derived literals. This is the standard word-RAM statement and
    is honest; it costs an amendment to a frozen row.
(b) Add an `msb`/`log2` instruction to the ISA. It is a conventional
    word-RAM primitive, and it would restore a bare literal total. Costs
    an ISA amendment and a REQ-E1-01 re-justification.
(c) Precompute a log2 table in the store and read it. REJECTED on
    inspection: it adds a memory-read event absent from the accepted
    trace, so it breaks REQ-E1-04 positional receipt equality and would
    require reopening the accepted route (frozen B-rows).

Recommendation if asked: (a) or (b). (a) changes only the E1 statement;
(b) preserves the literal but widens the ISA.

HONESTY NOTE: this is a STRUCTURAL finding established by reading the
route definitions, with exact file:line above. It is NOT a checked Lean
non-existence theorem - proving "no literal bound exists" would require a
machine-step lower bound, which was not attempted. It should be treated
as a well-evidenced blocker to be adjudicated, not as a proved obstruction.

### 3. WHAT LANDED (unblocked work)

New module `RMQ/Core/WordRAM/E1SameBlockArm.lean` (~330 lines), namespace
`RMQ.WordRAM.E1SameBlockArm`, plus its `RMQ.lean` import line. No
route-side file modified; purely additive.

The B6 same-block object is structurally the fringe arm already simulated,
instantiated at the same-block range and post-composed with the PURE
`bpCandidateClose?`. Because `bpFringeCandGlobal` is total into `some`
(`ChargedFringeChunks.lean:1617` - both arms yield `some`),
`bpCandidateClose?` is the single expression `position - 1`, so the
epilogue is TWO instructions with no option dispatch and NO read event,
matching the route, whose `TraceResult.map` contributes no trace.

Key objects (file:line exact at `e4aa8d0`):

- `fRes 69` (close result, `:46`), `fClose 70` (preamble input, `:123`) -
  bank extension.
- `windowAddr` (`:127`, 4 instructions), `windowAddrCats` (`:137`),
  `windowAddr_fits` (`:143`), `windowAddr_straight` (`:159`),
  `windowAddr_runsTo` (`:174`), `windowAddr_runsTo_route` (`:211`).
- `sameBlockClose` (`:238`, 2 instructions), `sameBlockCloseCats` (`:246`),
  `sameBlockClose_fits` (`:249`), `sameBlockClose_runsTo` (`:265`).
- `sameBlockSeeded_trace_eq` (`:308`) - POSITIONAL `List` equality of the
  accepted object's `.trace`.
- `sameBlockSeeded_value_eq` (`:329`).
- `sameBlockArmCats` (`:348`).
- `sameBlockArm_runsTo` (`:373`) - THE WHOLE SAME-BLOCK ARM, `A -> A+97`.

(Line numbers above re-verified against the source at final HEAD, after
the iteration-time numbers had drifted.)

Same-block arm layout at base `A` (97 instructions): prologue `A..A+20`,
fold loop base `A+21` (exit `A+88`), global-rebase epilogue `A+88..A+94`,
close epilogue `A+95..A+96`, exit `A+97`. The preamble's 4 instructions sit
before `A` and are not yet spliced into that layout.

### 4. GOTCHAS RECORDED THIS SESSION (carry forward)

1. `set ... with ...` is a MATHLIB tactic and is NOT available here. Use
   `RunsTo.straight` plus the module-local `straight_eval`/`straight_writes`
   macros (`E1StraightLine.lean:210`/`:217`) for straight segments; that is
   the house idiom and it is much shorter than hand-chaining step rules.
2. Preservation side conditions must be stated with NUMERAL register
   predicates (the house pattern, e.g. `WindowAddrUntouched r` defined as
   `r != 63` and `r != 64`), not with the `fBase`/`fBB` abbrevs. With the
   abbrevs, `omega` treats the register names as opaque atoms and fails.
   This is why every existing module writes its `...Untouched` predicate
   in numerals.
3. Per-constructor step rules (`RunsTo.const`, `RunsTo.sub`, ...) need the
   state given EXPLICITLY via the named argument `s`; otherwise the fetch
   hypothesis is elaborated before `s` is known and you get a
   `?m[State.pc ?m]?` mismatch.
4. The same-block route objects use `have`-bindings in their bodies, so
   `unfold` leaves `let_fun` in the way and `rw` cannot see through it.
   Use `simp only` with the definition plus
   `TraceResult.bind`/`map`/`pure` FIRST to zeta-reduce, THEN `rw` the
   bridges. (The `ChargedFringeTrace` arm objects have no `have`s, which
   is why plain `unfold` worked there.)
5. Finish a trace bridge with `simp only [List.append_nil]`, NOT bare
   `simp`: plain `simp` normalizes `a + 1 + (b - a + 1) - 1` into
   `a + 1 + (b - a)` on one side only, after which the two sides no longer
   match the `abbrev`-level `relHi`.

### 5. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at both commits. `#print axioms` run on all
eleven theorems this session claims: `sameBlockClose_length`,
`sameBlockClose_fits`, `sameBlockClose_runsTo`, `sameBlockSeeded_trace_eq`,
`sameBlockSeeded_value_eq`, `sameBlockArm_runsTo`, `windowAddr_length`,
`windowAddr_fits`, `windowAddr_straight`, `windowAddr_runsTo`,
`windowAddr_runsTo_route` - every one reports only `propext` /
`Classical.choice` / `Quot.sound`, never `sorryAx`. Hygiene `rg` clean on
the new module; `git diff --check` clean.

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN. This session closed none and weakened
none. Evidence accumulated is component-level and does NOT discharge any
row; all rows are WHOLE-QUERY scoped.

### 7. RESUME POINT (M3d-4)

NOTHING below is implemented.

1. COORDINATOR DECISION REQUIRED on the interior-leg `Nat.log2` finding in
   section 2 above before items 3-7 of the previous resume point can be
   completed as frozen. Items 2 and 3 below are unaffected and can proceed
   in parallel with that decision.
2. SPLICE THE PREAMBLE into the same-block arm: `windowAddr_runsTo_route`
   delivers `fBase`/`fBB`, but `fringeArm_runsTo` also needs `fLo`, `fHi`,
   `fAcc`, `fSeed`, `fStart`. `fStart = leftClose + 1` and
   `fLo = leftClose + 1 - fBB`,
   `fHi = leftClose + 1 + (rightClose - leftClose + 1) - 1 - fBB`
   are add/sub only; `fAcc` and `fSeed` are the rank seed (item 3).
3. RANK SEED. `localBPSeedFromRankCloseTraceResult`
   (`ConcreteDirectoryRAM.lean:1530`) is
   `map (localBPSeedFromRankFalse base) (rankCloseTrace base)`, so the
   seed leg is `rankCloseBlock_runsTo_canonical`
   (`E1RankCanonical.lean:263`) at address `base`, then the pure
   `localBPSeedFromRankFalse`. Composing it in front of
   `sameBlockArm_runsTo` reaches the delegation's named target
   `bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore`
   (`ChargedSameBlockTrace.lean:340`).
4. CANONICAL-STORE FORM, then whole-query glue, M4-M7 - unchanged from the
   previous resume point, except that M5's supersession wording MUST be
   corrected per section 2.

## M3d-4 (worker E1-R4n): range preamble, rank seed, and the same-block LEG

Session scope was deliberately narrowed by the coordinator: the interior
leg is BLOCKED pending a user decision on the `Nat.log2` finding recorded
in M3d-3 section 2, and this session was instructed not to touch it, not
to invent an msb/log2 instruction, and not to amend any frozen row.
Nothing below touches the interior leg.

### 1. WHAT LANDED

Commit `d72d3ea` (appended to `E1SameBlockArm.lean`) - the RANGE PREAMBLE:

- `windowRange` (`:447`, 8 instructions), `windowRange_length` (`:457`),
  `windowRangeCats` (`:461`), `windowRange_fits` (`:468`),
  `windowRange_straight` (`:493`), `windowRange_runsTo` (`:512`),
  `windowRange_runsTo_route` (`:553`).

This closes resume-point item 2. `fStart`, `fLo` and `fHi` are add/sub
only; no divisor is involved, so the divisor risk gate did not have to be
re-opened. New bank slot `fRight = 71` (`:442`) carries the right close
position.

ORDERING NOTE WORTH CARRYING: the instruction order mirrors the route's
`sbRelHi` expression LEFT TO RIGHT on purpose. `sbRelHi` is
`leftClose + 1 + (rightClose - leftClose + 1) - 1 - base`, and in `Nat`
the machine must subtract `1` and THEN `base`. Folding them into a single
subtraction of `1 + base` is NOT the same function at the clamping
boundary, and the bridge would fail there.

Commit `d231043` (new module `RMQ/Core/WordRAM/E1SameBlockLeg.lean`,
imported from `RMQ.lean:33`) - the RANK SEED and the whole LEG:

- `rankSeedPos` (`:60`, 1 instruction), `rankSeedPos_length` (`:62`),
  `rankSeedPosCats` (`:65`), `rankSeedPos_fits` (`:68`),
  `rankSeedPos_runsTo` (`:77`).
- `rankSeedFinish` (`:102`, 3 instructions), `rankSeedFinish_length`
  (`:107`), `rankSeedFinishCats` (`:110`), `rankSeedFinish_fits` (`:114`),
  `rankSeedFinish_straight` (`:131`), `rankSeedFinish_runsTo` (`:149`).
- `rankSeedLegCats` (`:187`), `rankSeedLeg_runsTo_canonical` (`:204`) -
  `P -> P + 64`, receipt POSITIONALLY equal to
  `localBPSeedFromRankCloseTraceResult`'s trace at the canonical
  rank-close trace.
- `canonicalSeed` (`:292`), `sameBlockLegCats` (`:302`),
  `sameBlockLeg_runsTo_canonical` (`:333`) - `A -> A + 173`.

This closes resume-point item 3 and reaches the delegation's named target
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore`
(`ChargedSameBlockTrace.lean:340`, NOT `:326`) instantiated at
`rankCloseTrace := concreteBPNativeChunkedRankCloseGlobalWordTraceResult
shape`.

Commit `312581f` (same module) - the ANTI-VACUITY HOSTING WITNESS:

- `hostedAt_step` (`:437`, private peeling helper),
  `sameBlockLegProgram` (`:447`), `sameBlockLegProgram_length` (`:466`,
  = 173), `sameBlockLegProgram_hosts` (`:477`),
  `sameBlockLegProgram_runsTo_canonical` (`:537`).

### 2. WHY THE HOSTING WITNESS WAS WORTH DOING

`sameBlockLeg_runsTo_canonical` takes THIRTEEN `HostedAt` hypotheses plus
a back-edge fetch, all constraining ONE program at offsets that are only
correct if every segment length in the layout table is right. A composed
simulation theorem whose hypotheses cannot all hold at once proves
nothing, and nothing in the previous rungs had discharged that risk for a
multi-segment composition.

`sameBlockLegProgram_hosts` discharges all thirteen at once against a
concrete program. Every offset is forced by the preceding segments'
lengths through `HostedAt.append_left`/`append_right`, so a one-off error
anywhere in the 173-instruction layout fails to typecheck rather than
producing a true-but-empty theorem.

`sameBlockLegProgram_runsTo_canonical` is then the leg with hosting fully
discharged. The hypotheses that remain are genuine route-side facts, not
plumbing: `sbChunkBits shape <= machineWordBits`, and the three window
words being full width in the canonical store.

### 3. THE CANONICAL-STORE FORM IS REAL, AND WHY

`rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean:263`) is fixed at
`concreteBPNativeSuccinctRMQGlobalReadStore shape`, while
`sameBlockArm_runsTo` is store-parametric. Composing them FORCES the arm's
store to be that same canonical store. So the seed leg and the fringe arm
are not merely both true of their own stores; they are true of a SINGLE
machine run against a SINGLE store, and the receipt is that run's own log.
That is the property the whole-query composition will need.

### 4. WHAT THE CROSS-BLOCK / INTERIOR COMPOSITION STILL NEEDS

Stated precisely, as the delegation requires. The same-block leg above is
complete; NONE of the following is implemented, and the first item is
blocked on a decision that is not this worker's to make.

1. BLOCKED (not touched this session). The interior leg's runtime
   `Nat.log2` / `bpSparseLogSpan` computation - see M3d-3 section 2 for
   the exact file:line and the options. Until the coordinator/user
   adjudicates, no interior-leg block can be built without either an
   uncapped loop (contradicting the frozen literal-step-bound row) or a
   new instruction (forbidden this session).
2. The CROSS-BLOCK dispatcher. The same-block arm is one branch of the
   close/LCA dispatch. The other branch needs the left-fringe and
   right-fringe arms (both already simulated: `fringeLeg_trace_eq_leftArm`
   / `_rightArm`, `E1FringeArmBlock.lean:618`/`:647`) composed with the
   interior leg (item 1) and the select-close leg
   (`E1SelectCanonical.lean`), then merged. The merge itself is register
   arithmetic and a comparison; the blocker is item 1's leg, not the
   merge.
3. The BRANCH between same-block and cross-block. The route-side test is
   whether the two close positions land in the same summary block. On the
   machine this is `divConst` on each endpoint plus a `natEq` plus a
   `brNZ` - all existing instructions, all constant-divisor - so this is
   NOT a risk item, but it is not written.
4. The WHOLE-QUERY glue, the derived all-size literal, and the amended
   target Prop remain out of scope per the delegation, all three
   downstream of item 1.

### 5. GOTCHAS RECORDED THIS SESSION (carry forward)

1. `lake env lean <file>` does NOT write an olean. A `#print axioms`
   script that imports the module will report `unknown constant` for
   everything you just added until you run `lake build RMQ` first. This
   looks exactly like the "the name is only a comment" failure the
   axiom-check discipline is designed to catch, and it is not. Build,
   THEN axiom-check.
2. Preservation side conditions of the shape
   `r <= 8 or 28 <= r` discharged against a register ABBREV (`fBB`,
   `fBase`, ...) need `by decide`, never `by omega` - omega treats the
   abbrev as an opaque atom and reports a counterexample in which the
   register number is unconstrained. This is the M3c-6d gotcha recurring
   at composition sites; expect it wherever a component block's
   preservation clause meets an arm-bank register.
3. `hostedAt_step`-style peeling helpers must be given the resulting base
   EXPLICITLY (`hostedAt_step (n := 97) h ...`). With `n` left as a
   metavariable the offset side goal becomes `97 = ?n` and `simp` cannot
   close it.
4. Finishing a hosted single-instruction fetch with `simpa` can
   over-normalize `program[i]? = some instr` into a `getElem` form and
   leave `this : True`. Use a defeq `exact h.append_left 0 (by decide)`.
5. Multi-argument `runsTo` composition lemmas take their register
   hypotheses in a FIXED order (`hClose`, `hRight`, `hBB` for
   `windowRange_runsTo_route`). Supplying them in the wrong order fails
   with a confusing "did not find instance of the pattern `regs2 fBB`"
   rewrite error inside a `by` block, not with an arity error.

### 6. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at all three commits (`d72d3ea`, `d231043`,
`312581f`). No new warnings in either touched module; the only warnings in
the build are the pre-existing sanctioned unused-simp-arg ones in
`SuccinctFinalRAM.lean`, `ReviewerReachability*.lean` and
`BPNavigationRAM.lean`.

`#print axioms` run on all seventeen theorems this session claims:
`windowRange_length`, `windowRange_fits`, `windowRange_straight`,
`windowRange_runsTo`, `windowRange_runsTo_route`, `rankSeedPos_length`,
`rankSeedPos_fits`, `rankSeedPos_runsTo`, `rankSeedFinish_length`,
`rankSeedFinish_fits`, `rankSeedFinish_straight`, `rankSeedFinish_runsTo`,
`rankSeedLeg_runsTo_canonical`, `sameBlockLeg_runsTo_canonical`,
`sameBlockLegProgram_length`, `sameBlockLegProgram_hosts`,
`sameBlockLegProgram_runsTo_canonical` - every one reports only
`propext` / `Classical.choice` / `Quot.sound`, never `sorryAx`.

### 7. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN. This session closed none and weakened
none. Matrix closure was impossible this session by construction: every
row is whole-query scoped and the whole-query composition is downstream of
the blocked interior leg.

### 8. RESUME POINT (M3d-5)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Items 2 and 3 below are unaffected.
2. THE SAME-BLOCK/CROSS-BLOCK BRANCH (section 4 item 3 above). Not a risk
   item: `divConst` on each endpoint, `natEq`, `brNZ`. Writing it does not
   require the interior leg, and it is the natural next unblocked step.
3. M6 PRODUCTION VALIDATOR scaffolding independent of the blocked leg:
   the independent `List Int` reference implementation (expectations
   written from the spec, NOT from the machine), the fixture list, the
   modeled-steps-vs-wall-clock harness, and the deliberate-mutation
   rejection check. NOT STARTED this session - see section 9.
4. Everything else is unchanged from the M3d-4 resume point and remains
   downstream of item 1.

### 9. WHAT THIS SESSION DID NOT DO, AND WHY

The delegation listed the M6 validator scaffolding as a "if you still have
budget" item. It was NOT started. The three landed commits plus the
anti-vacuity witness consumed the session's budget, and a partially built
validator that does not compile would be worse than none - it would have
to be reverted or repaired by the next worker before any root build could
go green. Recording it here as genuinely not-started is the honest
report; it remains resume item 3 above.

## M3d-5 (worker E1-R4o): branch dispatch, and the M6 machine validator

Scope was narrowed by the coordinator exactly as in M3d-4: the interior
leg remains BLOCKED pending the user decision on `bpSparseLogSpan` /
`Nat.log2` (M3d-3 section 2).  Nothing below touches the interior leg, no
msb/log2 instruction was invented, and no frozen row was amended.

### 1. WHAT LANDED

Commit `9b3ecd0` (new module `RMQ/Core/WordRAM/E1CloseDispatch.lean`,
imported from `RMQ.lean:34`) - the SAME-BLOCK/CROSS-BLOCK DISPATCH.
This closes M3d-4 resume item 2.

- Bank slots `dLB = 72` (`:64`), `dRB = 73` (`:67`), `dSame = 74` (`:70`).
  The fringe/same-block bank ended at `fRight = 71`; the dispatch takes
  the next three and READS `fClose`/`fRight` without writing them, since
  both arms consume the endpoints afterwards.
- `closeDispatchPrefix` (`:77`, 3 instructions), `closeDispatch` (`:85`,
  4 instructions), `closeDispatchPrefix_length` (`:88`),
  `closeDispatch_length` (`:91`), `closeDispatchCats` (`:96`),
  `closeDispatchCats_no_read` (`:100`), `closeDispatch_fits` (`:106`),
  `closeDispatchPrefix_straight` (`:125`),
  `CloseDispatchUntouched` (`:138`), `closeDispatchPrefix_runsTo` (`:144`).
- `closeDispatch_runsTo_same` (`:187`) and `closeDispatch_runsTo_cross`
  (`:224`) - the two branch directions.
- Anti-vacuity: `closeDispatchProgram` (`:277`),
  `closeDispatchProgram_length` (`:281`), `closeDispatchProgram_hosts`
  (`:291`), `witnessCrossArm` (`:320`), `witnessSameArm` (`:323`),
  `witnessProgram` (`:326`), `witnessProgram_length` (`:329`),
  `witnessProgram_runs_same` (`:337`), `witnessProgram_runs_cross`
  (`:377`).

Commits `46297fd`, `ff7da19`, `ccc740d` (new module
`RMQ/Validation/E1MachineValidate.lean`, new `lean_exe`
`rmq_e1_machine_validate` in `lakefile.toml`) - the M6 VALIDATOR.  This
closes M3d-4 resume item 3, which the predecessor deliberately did not
start.

### 2. WHY THE DISPATCH IS UNBLOCKED, STATED PRECISELY

This deserves recording because the dispatch and the blocked interior leg
both involve `Nat.log2`, and the difference is the whole reason one is
writable and the other is not.

The route condition (`ChargedFringeWiring.lean:496`, and identically at
`:39` costed / `:57` structural) is
`blockOfClose blockSize leftClose = blockOfClose blockSize rightClose`
with `blockSize = canonicalBPRelativeSummaryBlockSizeRaw shape`
(`RelativeSummary.lean:1240`) `= 2 * (Nat.log2 shape.size + 1)`
(`:1237`).

That `Nat.log2` is applied to `shape.size`.  It is fully determined before
the machine starts, so `blockSize` is an ENCODABLE IMMEDIATE and
`divConst` applies with no new instruction.  Positivity, which the
`divConst` width arm additionally requires, is
`canonicalBPRelativeSummaryBlockSizeRaw_pos` (`RelativeSummary.lean:2488`)
and is carried as the `hpos` hypothesis of `closeDispatch_fits`.

The interior leg `bpSparseLogSpan blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598`) applies `Nat.log2` to
a RUNTIME-DERIVED `blockCount` and feeds the result to an accepted read
address.  No immediate encodes it.  That distinction, not the presence of
a logarithm, is what blocks the interior leg.

### 3. THE DISPATCH ANTI-VACUITY IS EXECUTION, NOT JUST HOSTING

`closeDispatch_runsTo_same`/`_cross` are hypothetical in `program` AND
take a bare `Nat` branch `target`.  Hosting alone is therefore not enough:
a theorem about a target that falls off the end of the program would be
equally true and equally worthless.

`closeDispatchProgram` (`:277`) places the same-block target at
`4 + crossArm.length`, i.e. COMPUTED from the layout rather than asserted,
and `closeDispatchProgram_hosts` (`:291`) discharges all three `HostedAt`
obligations against that one program.  `witnessProgram_runs_same` (`:337`)
and `witnessProgram_runs_cross` (`:377`) then RUN the machine on the same
concrete program in both directions, each landing on a distinguishable
`halt`.  A wrong branch target or a wrong fall-through offset makes them
unprovable rather than vacuous.

### 4. THE M6 VALIDATOR, AND WHAT IT ACTUALLY ESTABLISHES

`lake exe rmq_e1_machine_validate`, exit 0.  It is a NEW executable; the
existing `rmq_succinct_classic_validate` was not modified (it belongs to
the concurrent repair worker).

FINDING WORTH CARRYING: before this harness, `E1Machine.run`
(`E1Machine.lean:226`) had NO caller anywhere in the repository.  Every
machine fact was a `RunsTo` proposition discharged in the kernel and no
modeled instruction had ever been executed.  This is the first execution
of the machine, so anything it finds is ground that proofs never covered.

- INDEPENDENT REFERENCE: `refRMQ` (`:66`) is half-open leftmost RMQ over
  `List Int` written from the specification.  It does not call the route,
  the machine, `Cartesian`, `SuccinctClassic`, or `RMQ.scanWindow`.
  `expectationTable` (`:136`) is computed from it and is materialised in
  phase 1, BEFORE any machine run.  `expectationSelfConsistent` (`:152`)
  brute-force checks the reference own answers (in-window, minimal,
  leftmost): 0 failures over 576 expectations.
- FIXTURES: 31 (`allFixtures:105`) - empty, singleton, size-two in both
  orders, all-equal, ties, ascending, descending, negatives, wide, plus 21
  deterministic generated - crossed with every window including the
  invalid ones (`windowsFor:113`: empty, reversed, past-the-end) = 576
  expectations, 258 `none` / 318 `some`.
- DISPATCH vs ROUTE: 405 cases (`:231`), machine executed against the
  route condition (`routeOutcome:222`), 0 mismatches, 2430 modeled steps,
  0 modeled reads.
- SAME-BLOCK LEG: `runSameBlockLeg` (`:373`) executes
  `sameBlockLegProgram` against
  `concreteBPNativeSuccinctRMQGlobalReadStore` and diffs its `readLog`
  against the route own `.trace`.  90 cases: 0 exit failures (proved exit
  pc 173), 0 receipt mismatches, 30343 modeled steps, 1080 modeled read
  events.  This is an EXECUTABLE confirmation of the
  `sameBlockLegProgram_runsTo_canonical` receipt clause - the two sides
  are `E1Machine.run` folding `execInstr` on one hand and
  `ChargedSameBlockTrace` on the other, neither derived from the other.
- SELECT LEG: `runSelectLeg` (`:484`) does the same for the
  405-instruction select dispatch at base 0.  32 cases: 0 exit failures
  (proved exit pc 405), 0 receipt mismatches, 8273 modeled steps, 475
  modeled read events.
- MUTATIONS, BOTH REJECTED.  `mutatedDispatchProgram` (`:287`) turns the
  dispatch `natEq` into `natLt`: 266 machine/route disagreements.
  `mutatedLeg` (`:413`) turns the same-block fold back edge
  `brNZ fCnt 97` into `brNZ fCnt 98` - a mutation of a REAL machine
  component that preserves program length AND still reaches exit pc 173,
  so `legMutantExitFailures` is 0.  An exit-pc-only check would MISS it
  entirely.  The receipt comparison catches it: 81 mismatches, 30060
  modeled steps against the honest 30343.  The report prints the 0
  deliberately, because it is the argument for diffing receipts rather
  than control flow.
- MODELED vs WALL-CLOCK: reported in separate labelled columns, never
  combined, with wall-clock explicitly called non-evidence.  Measured at
  HEAD: dispatch 2ms, same-block leg 2127ms, select leg 754ms, leg
  mutation 2082ms.
- THE HOLE: `wholeQueryComparisonAvailable` (`:549`) is `false` and
  `wholeQueryMismatches` (`:556`) returns `none`, reported as
  `wholeQueryComparison=OPEN (interior leg blocked; NOT a pass)`.  It
  compiles, is clearly marked, and is deliberately NOT a passing check.

### 5. GOTCHAS RECORDED THIS SESSION (carry forward)

1. LEAN LIFTS CLOSED SWEEPS OUT OF `main`, AND IT SILENTLY FALSIFIES
   TIMING.  A harness expression like `legModeledSteps mutatedLeg` has no
   free variables, so Lean evaluates it as a top-level constant BEFORE
   `main` runs.  Bracketing it with `IO.monoMsNow` then measures nothing
   and prints a confident `0 ms` for phases that really take seconds.
   Forcing inside the bracket does NOT help - the value already exists -
   and `if n == n then` is optimised away entirely.  The fix that works is
   threading a runtime-derived `salt` into the sweep (added to the already
   generous fuel, always `0`, so no result changes), which makes the term
   non-closed.  Modeled step counts were never affected; only wall-clock
   was.  This harness reported `0 ms` for every phase across two attempted
   fixes before the cause was found.
2. `IO.monoMsNow` returns `Nat`, not a fixed-width integer: `.toNat` on it
   is `unknown constant Nat.toNat`.
3. The M3d-4 gotcha 4 recurs verbatim for any hosted single-instruction
   fetch: `have := hHost i (by decide); simpa using this` over-normalises
   `program[i]? = some instr` into a `getElem` form and fails with a type
   mismatch against `witnessSameArm[0]?`.  `exact hHost i (by decide)`
   closes it by defeq.  This cost four of the five errors in the dispatch
   module first compile.
4. `one_ne_zero` is Mathlib-only and unavailable here; use `decide`.
5. `E1SelectCanonical.selData` is `private`, so a validator cannot reach
   it.  Its body is
   `GenericSelect.sparseExceptionSelectData shape.bpCode false`
   (`E1SelectCanonical.lean:41`) and must be repeated, not imported.
   Likewise the `E1CloseDispatch` import closure does NOT include the
   select modules; a harness touching both needs an explicit
   `import RMQ.Core.WordRAM.E1SelectCanonical`.
6. `State`/`RunResult` have no `Repr` (`RegFile := Nat -> Nat` is a
   function), so an executable harness must project `.steps`, `.pc`,
   `.halted`, `.readLog` and read registers individually.

### 6. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at all four commits (`9b3ecd0`, `46297fd`,
`ff7da19`, `ccc740d`).  `lake build RMQ RMQPaper RMQExamples` exit 0 at
HEAD.  No new warnings in either new module; the only warnings are the
pre-existing sanctioned unused-simp-arg ones.

`#print axioms` run AFTER a root build on all thirteen theorems this
session claims: `closeDispatch_length`, `closeDispatchPrefix_length`,
`closeDispatchCats_no_read`, `closeDispatch_fits`,
`closeDispatchPrefix_straight`, `closeDispatchPrefix_runsTo`,
`closeDispatch_runsTo_same`, `closeDispatch_runsTo_cross`,
`closeDispatchProgram_length`, `closeDispatchProgram_hosts`,
`witnessProgram_length`, `witnessProgram_runs_same`,
`witnessProgram_runs_cross` - every one reports only `propext` /
`Quot.sound` (two report no axioms at all), never `sorryAx`.

`lake exe rmq_e1_machine_validate` exit 0.  Hygiene `rg` clean on both new
files; no `native_decide` anywhere.  `git diff --check` clean both in the
working tree and over `d90b062..HEAD`.
`design_decision_check.ps1 -Strict -Base d90b062` exit 0 (45 changed
files).  `claim_drift_scan.ps1` exit 0.  `paper_topology_lint.ps1` exit 0;
neither lint reports anything in the two files this session added.

### 7. TWO PRE-EXISTING BASE DEFECTS, REPORTED NOT FIXED

Both files belong to the concurrent `claude/a07-blocker-repairs` worker.

1. `lake exe rmq_succinct_classic_validate` FAILS at this base, as the
   delegation anticipated: `singletonRepeatedEqualReadPositionsOK ... did
   not evaluate to true` in `RMQ/Validation/SuccinctClassic.lean`.  Not
   this session file and not fixed here.
2. NEW FINDING: `scripts/wordram_axiom_check.lean` now EXITS 1, and it is
   the same stale-constant defect the M3d-3 session found in
   `scripts/axiom_check.lean`.  Line 197 prints axioms for
   `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_76`,
   an UNKNOWN CONSTANT; the tree carries only `..._sum_le_207`
   (`SuccinctFinalRAM.lean:9411`/`:9843`,
   `SuccinctFinalModelAdequacy.lean:67`/`:302`/`:303`,
   `Headlines/RMQ.lean:499`).
   `git diff d90b062..HEAD -- scripts/wordram_axiom_check.lean` is EMPTY,
   so this branch did not introduce it.  NOTE that the M3d-3 log records
   this script as exiting 0; that statement is now false, whether through
   drift since or through an inaccurate reading then.  Substantively the
   run is clean - 311 axiom lines, ZERO `sorryAx` - but the script aborts
   and therefore certifies nothing past line 197.
   `scripts/headline_axiom_check.lean` exits 0.

### 8. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Matrix closure was impossible by construction: every row is
whole-query scoped and the whole-query composition is downstream of the
blocked interior leg.  Evidence accumulated is component-level and does
NOT discharge any row.

### 9. RESUME POINT (M3d-6)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Items 2-4 are unaffected.
2. COMPOSE THE DISPATCH WITH THE SAME-BLOCK LEG.  `closeDispatch`
   (`E1CloseDispatch.lean:85`) and `sameBlockLegProgram`
   (`E1SameBlockLeg.lean:447`) cannot yet be placed in ONE program,
   because `sameBlockLegProgram` hardcodes its internal branch targets
   `97` and `164` as ABSOLUTE addresses, correct only at base 0.  Hosting
   it behind a 4-instruction dispatch needs a base-parametric
   `sameBlockLegProgramAt B` with targets `B + 97` / `B + 164`, which does
   not exist.  This is a real, bounded piece of work and is the natural
   next step; it is NOT blocked by the interior leg.
3. THE CROSS-BLOCK ARM remains as described in M3d-4 section 4 item 2:
   two fringe arms plus the interior leg (blocked) plus the select-close
   leg, then the merge.
4. WHOLE-QUERY GLUE, the derived all-size literal, and the amended target
   Prop remain out of scope, all downstream of item 1.  When item 1
   unblocks, the validator hole at
   `RMQ/Validation/E1MachineValidate.lean:549`/`:556` is where the
   end-to-end machine-vs-`refRMQ` comparison attaches.

## M3d-6 (worker E1-R4p): base-parametric leg, the dispatch composition, and composite validation

Branch `claude/b1-b2-charged-fringe-tables`, base `c52e91b`, commits
`cb0b908` and `72e7020`.

### 1. THE REBASING WORK (resume item 2) - LANDED

The predecessor's diagnosis was correct but understated the good news.
`sameBlockLegProgram` (`E1SameBlockLeg.lean:447`) is indeed a hosting
witness only at base `0`, and it hardcodes FOUR internal addresses, not
the two the resume point named:

* the `rankCloseBlock` segment base `5` (its own first argument),
* `fringeMerge 97`,
* the `brNZ fCnt 97` fold back edge,
* `fringeCandGlobal 164`.

What the resume point did NOT record, and what makes this rung much
cheaper than budgeted: `sameBlockLeg_runsTo_canonical`
(`E1SameBlockLeg.lean:333`) was ALREADY base-parametric.  Its binder is
`{A ...}`, every hosting hypothesis sits at `A + k`, and its targets are
written `A + 97` / `A + 164` (`:352`, `:356`, `:357`).  The simulation
theorem needed NO change.  Only the concrete witness program was stuck at
base `0`.

Landed in `E1SameBlockLeg.lean` (M3d-6 section, after
`sameBlockLegProgram_runsTo_canonical`):

* `sameBlockLegProgramAt shape fringeSegment blockSize B` - the same
  173-instruction layout with all four internal addresses `B`-relative.
* `sameBlockLegProgramAt_length` = 173.
* `sameBlockLegProgramAt_zero` - specialises to the landed base-`0`
  layout, so nothing already proved regresses.  (The delegation asked to
  keep the existing base-0 form working OR to prove the new one
  specialises to it; this is the second, and it is the stronger.)
* `sameBlockLegProgramAt_hosts` - all twelve hosting facts at `B + k` from
  the single assumption `HostedAt program B (sameBlockLegProgramAt ... B)`.
* `sameBlockLegProgramAt_runsTo_canonical` - the leg at an arbitrary base.

New module `RMQ/Core/WordRAM/E1CloseCompose.lean` (imported at
`RMQ.lean:35`):

* `sameBlockDispatchProgram shape fringeSegment blockSize crossArm` -
  dispatch at `0`, `crossArm` at `4`, the leg rebased to
  `4 + crossArm.length`.  The argument to `sameBlockLegProgramAt` and the
  branch target `closeDispatchProgram` computes are the SAME expression,
  so an off-by-one fails to typecheck.
* `sameBlockDispatchProgram_runsTo` - the composite on the route's own
  same-block condition, `0 -> 4 + crossArm.length + 173`, reproducing the
  route trace and value.
* `sameBlockDispatchProgram_runsTo_witnessCross` - instantiated at the
  dispatch module's witness cross arm, so the leg's host base is the
  CONCRETE `6` (internal targets `103` and `170`) and the exit is `179`.
  This is the anti-vacuity witness for the rung: at base `0` the old
  layout typechecks by accident because `0 + 97 = 97`.
* `witnessCross_legBase_eq_six` - `4 + witnessCrossArm.length = 6`, by
  `decide`, so the layout arithmetic is checked rather than described.

`crossArm` is left a PARAMETER; nothing in the composition depends on its
contents, only its length, so the finished cross arm drops into the same
layout without disturbing the same-block result.

### 2. THE CROSS-BLOCK ARM (resume item 3): structural map, verified at source

The delegation asked to assemble it as far as it goes without the interior
leg, and to state precisely what the interior composition will need.  The
assembly did NOT proceed, for a reason worth recording rather than
glossing: the route's cross-block object needs a component that does not
exist and is NOT the interior leg.  The map below was read at source this
session, not carried forward.

The else-branch of `ChargedFringeWiring.lean:496` is
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeTrace.lean:1144`;
note the `RelativeRmmMacro/` path component, which an earlier survey
omitted).  It sequences FIVE sub-computations, not the four the M3d-4
resume point assumed, and the two rank seeds are NOT adjacent - the right
seed sits between the interior leg and the right arm (`:1154-1181`):

1. `localBPSeedFromRankCloseTraceResult ... leftClose`   (LEFT SEED)
2. `bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore`  (LEFT ARM)
3. `if leftBlock + 1 < rightBlock then concreteBPRelativeRmmInteriorRangeMin... else TraceResult.pure none`  (INTERIOR - BLOCKED)
4. `localBPSeedFromRankCloseTraceResult ... rightClose`  (RIGHT SEED)
5. `TraceResult.map (fun right? => bpCandidateClose? (bpCandidateMerge3? left? middle? right?)) (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore ...)`  (RIGHT ARM, merge fused on)

Machine-side coverage, checked this session:

* Arms (2, 5): EXIST and are arm-agnostic.  `fringeArm_runsTo`
  (`E1FringeArmBlock.lean:904`) is stated over abstract
  `base/bb/relLo/relHi/seed/start`; `leftArm_value_eq` (`:987`) and
  `rightArm_value_eq` (`:1018`) are the two instantiations.  Results land
  in `fRV`/`fRP`.
* Seeds (1, 4): EXIST (`rankSeedLeg_runsTo_canonical`) but are wired only
  at the same-block leg's instantiation; they need re-hosting at the
  cross-block layout.  Assembly, not new construction.
* Interior (3): BLOCKED, unchanged - see section 3.
* MERGE (5): DOES NOT EXIST.  `rg` over `RMQ/Core/WordRAM/` for
  `bpCandidateMerge`, `bpCandidateBetter`, `candMerge`, `merge3` returns
  NOTHING.  This is a NEW finding: previous resume points listed the
  cross-block arm as "two fringe arms plus the interior leg plus the
  select-close leg, then the merge", which reads as though the merge were
  a known small step.  It is unbuilt, and it is why the cross-block arm
  cannot be assembled even partially into a running program.

`E1SameBlockArm.sameBlockClose` (`:238`, two instructions) does NOT
generalise to it.  That epilogue handles `bpCandidateClose?` on a SINGLE
arm and needs no option dispatch, because `bpFringeCandGlobal` is total
into `some` (`ChargedFringeChunks.lean:1617`).  In the cross-block object
`middle?` is genuinely optional - the `leftBlock + 1 < rightBlock` guard
produces `TraceResult.pure none` - so `bpCandidateMerge3?` needs a real
three-way option-aware minimum.

### 3. WHAT THE MERGE AND THE INTERIOR COMPOSITION WILL NEED (precise)

THE MERGE (unblocked, read-free, buildable today).  `bpCandidateBetter`
(`RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/Candidate.lean:15`)
is `if right.1 < left.1 then right else left` - STRICT `<`, so ties keep
the left candidate and the leftmost tie-break is inherited for free.
`bpCandidateMerge?` (`:18`) is the option-lifted version and
`bpCandidateMerge3?` (`:24`) is `merge? (merge? left middle) right`.
Since both arms are total into `some`, only `middle?` needs an occupancy
test, and the whole step is:

    acc := left
    if middle present and middle.val < acc.val then acc := middle
    if right.val < acc.val then acc := right
    result := acc.pos - 1              -- bpCandidateClose?

A 16-instruction, read-free, already-base-parametric block suffices
(`natLe` + `brNZ` + `move`; no new ISA constructor, no divisor).  The
house convention for the optional candidate is the `+1` BIAS already used
by `fringeMerge` (`E1FringeFoldBlock.lean:204`, `.add fBV fCV fOne`):
`0` encodes `none`, `v+1` encodes `some v`.  DESIGNED BUT NOT BUILT this
session - the six control paths are a real proof obligation, and the
remaining budget went to validating what had already landed rather than
starting a block that could not be finished and verified.

THE INTERFACE OBLIGATION ON THE INTERIOR LEG, when it unblocks: it must
deliver `middle?` in that biased form - occupancy in one register as
`0`/`v+1`, position in another - so the merge needs no option dispatch
beyond a single `brNZ`.  Any other encoding forces a redesign of the
merge block.  This is the one cross-component contract the interior work
should be told about BEFORE it is built.

THE INTERIOR ITSELF is unchanged and still blocked.
`bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598`) is applied to
`rightBlock - leftBlock - 1` (`ChargedFringeTrace.lean:1166`) - derived at
RUNTIME from the query operands - and both `Nat.log2 count` and the span
reach accepted read addresses.  Contrast the dispatch's own `Nat.log2`,
applied to `shape.size`, fixed before the machine starts, never reaching a
read address; that is exactly why the dispatch was buildable and the
interior is not.

### 4. VALIDATOR (delegation item 3)

`RMQ/Validation/E1MachineValidate.lean` gains phase 3d (composite
execution) and phase 4c (rebasing mutations).  The whole-query hole
(`wholeQueryComparisonAvailable` / `wholeQueryMismatches`) is UNTOUCHED
and still reports `OPEN (interior leg blocked; NOT a pass)`.

Phase 3d is strictly stronger than phase 3b: 3b runs the leg at base `0`,
where every absolute internal target is correct by accident.  Same-block
cases must reach `179` with a receipt equal event-for-event to the route's
independently computed trace; because the dispatch performs no read, this
also checks the dispatch is read-free IN SITU rather than by inspecting
its opcodes.  Cross-block cases must halt in the witness cross arm having
read nothing - which does NOT validate the route's cross-block VALUE, and
the harness comments say so.

MUTANT B IS THE ONE TO BEAT NEXT.  It moves a SINGLE operand - the fold
back edge from its rebased `103` to the base-`0` `97` - and it REACHES
THE CORRECT EXIT PC 179 (exitFailures = 0) while its receipt diverges
(6 mismatches).  Program length, instruction count and opcodes are all
unchanged.  Only receipt diffing catches it.

### 5. GOTCHAS RECORDED THIS SESSION (carry forward)

1. `lake build RMQ` DOES NOT BUILD THE VALIDATOR.  It reported
   `Build completed successfully` while
   `RMQ/Validation/E1MachineValidate.lean` was failing to compile; that
   module belongs to the `lean_exe` target, not the `RMQ` lib.  Build
   `rmq_e1_machine_validate` (or run it) before believing the validator is
   green.  This is a hole in the "root build is the binding standard"
   habit and it silently hid three compile errors.
2. `by decide` closes `0 < [instr].length` at base `0` but NOT under a
   free base variable: the goal `0 < [Instr.brNZ fCnt (B + 97)].length`
   contains a free variable and `decide` refuses it outright ("expected
   type must not contain free variables").  Use `by simp`.  This is the
   base-parametric analogue of the M3d-4 gotcha 2 and will recur for every
   rebased witness.
3. AN EXECUTABLE HARNESS MUST COMPUTE ITS REPORT LIST ONCE.  Deriving each
   statistic from its own sweep re-runs the machine per statistic; eight
   statistics over 40 leg-scale cases did not finish in ten minutes.  Fold
   the counts over a single `List ComposeReport`.
4. A MIS-REBASED PROGRAM DOES NOT FAIL FAST - IT LOOPS UNTIL FUEL IS
   EXHAUSTED.  A mutant whose back edge targets a wrong address can burn
   the full fuel budget on every case, making the mutant sweep hundreds of
   times more expensive than the honest one.  Give mutant sweeps a reduced
   budget and case subset, and make the harness CHECK that the budget
   exceeds the largest honest run (`composeMutantFuelIsSlack`) and that the
   subset still reaches the mutated arm (`composeMutantCoversSameBlock`),
   rather than asserting either.  Fuel exhaustion is rejection a fortiori,
   so this weakens nothing.
5. A LONG `&&` VERDICT CHAIN BLOWS THE ELABORATOR.  A single `&&` chain
   over ~20 Bool clauses fails with `failed to synthesize BEq Nat,
   maximum recursion depth`.  Group into named `let` clauses; the grown
   `do` block additionally needed `set_option maxRecDepth 8000 in` on
   `mainImpl` (an elaborator budget only - not a proof option, and it
   weakens no check).
6. `Nat` `>` in string interpolation is a `Prop`: `s!"{n > 0}"` fails with
   `failed to synthesize ToString Prop`.  Use `n != 0`.

### 6. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at both commits (`cb0b908`, `72e7020`).
`lake build rmq_e1_machine_validate` exit 0 at HEAD - recorded separately
BECAUSE of gotcha 1.

`#print axioms` run AFTER a root build on all nine theorems this session
claims: `sameBlockLegProgramAt_length`, `sameBlockLegProgramAt_zero`,
`sameBlockLegProgramAt_hosts`, `sameBlockLegProgramAt_runsTo_canonical`,
`sameBlockDispatchProgram_length`, `sameBlockDispatchProgram_runsTo`,
`sameBlockDispatchProgram_runsTo_witnessCross`,
`witnessCross_legBase_eq_six`, `fringeCandGlobal_fits` - every one reports
only `propext` / `Classical.choice` / `Quot.sound` (two report fewer),
never `sorryAx`.

`lake exe rmq_e1_machine_validate` exit 0, `RESULT: PASS (with the
whole-query comparison still OPEN)`.  Composite figures, modeled and
wall-clock kept apart: `composeCases=40` (`composeSameCases=27`,
`composeCrossCases=13`), `composeLegExitFailures=0`,
`composeReceiptMismatches=0`, `composeCrossArmFailures=0`,
`composeCrossReads=0`, `composeModeledSteps=9222`,
`composeMaxModeledSteps=585`, `composeModeledReads=322`;
`composeWallClockMs=194` (this binary on this host; NOT evidence).
Mutations: `composeMutationsAreReal=true`, `composeMutantFuel=6000` vs
honest max `585` with `slack=true`, `composeMutantCoversSameBlock=true`,
`mutantA_unrebased_exitFailures=6` / `receiptMismatches=6`,
`mutantB_backEdge_exitFailures=0` / `receiptMismatches=6`.

### 7. WIDTH CERTIFICATES: the gap was ONE segment, not six

Checked rather than assumed.  `rankCloseBlock_fits`
(`E1RankBlock.lean:1003`) and `fringeLoopBody_fits`
(`E1FringeFoldBlock.lean:376`, covering `fringePrefix ++ fringeMerge ++
fringeShift ++ fringeAdvance`) already existed, as did
`fringeArmPrologue_fits`, `windowAddr_fits`, `windowRange_fits`,
`sameBlockClose_fits`, `rankSeedPos_fits`, `rankSeedFinish_fits`.  The
only same-block leg segment with NO width certificate was the
global-rebase epilogue; `fringeCandGlobal_fits`
(`E1FringeArmBlock.lean:738`) closes it, constructor-exhaustive with no
wildcard arm.

STILL OUTSTANDING: no whole-program width certificate for
`sameBlockLegProgramAt` or `sameBlockDispatchProgram`.  All segment-level
pieces now exist, so this is assembly - collecting the segments'
hypotheses into one signature and dispatching `List.mem_append` (with
`or_assoc` in the simp set, per the M3d-3 flattening gotcha).

### 8. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Matrix closure was impossible by construction: every row is
whole-query scoped and the whole-query composition is downstream of the
blocked interior leg.  Evidence accumulated is component-level and does
NOT discharge any row.

Component-level evidence added: REQ-E1-01 (the composed simulation now has
an anti-vacuity witness at a NONZERO host base, not only at `0`);
REQ-E1-02 (`fringeCandGlobal_fits`); REQ-E1-04 (the composite's receipt is
positionally equal to the route's, executed); REQ-E1-08 (composite
execution phase plus two rebasing mutations, one of which reaches the
correct exit pc and is caught only by the receipt diff).

### 9. RESUME POINT (M3d-7)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Items 2-4 are unaffected.
2. BUILD THE THREE-WAY CANDIDATE MERGE.  Unblocked, read-free, and now the
   binding obstacle to the cross-block arm - ahead of the interior leg in
   the sense that the arm cannot be assembled even partially without it.
   Design, register convention and the exact route semantics are in
   section 3 above.  Six control paths; budget accordingly.
3. WHOLE-PROGRAM WIDTH CERTIFICATES for `sameBlockLegProgramAt` and
   `sameBlockDispatchProgram`.  All segment lemmas now exist (section 7);
   this is assembly only.
4. THE CROSS-BLOCK ASSEMBLY still needs, in order: the merge (item 2), the
   two seeds re-hosted at the cross-block layout, the two arms hosted
   (both already arm-agnostic), and then the interior leg (blocked).
5. WHOLE-QUERY GLUE, the derived all-size literal, and the amended target
   Prop remain out of scope, all downstream of item 1.  The validator hole
   is at `RMQ/Validation/E1MachineValidate.lean`
   (`wholeQueryComparisonAvailable` / `wholeQueryMismatches`, phase 5) and
   is where the end-to-end machine-vs-`refRMQ` comparison attaches.

## M3d-7 (worker E1-R4q): the three-way candidate merge, whole-program width, and the interior interface contract

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`0e5360d` to `<HEAD>`.  Three milestones landed green and committed.

### 1. THE THREE-WAY CANDIDATE MERGE (resume item 2) - LANDED

`RMQ/Core/WordRAM/E1CandMerge3.lean`, new module.  This was the binding
obstacle to the cross-block arm: before it, `rg` over `RMQ/Core/WordRAM/`
for `bpCandidateMerge` / `candMerge` / `merge3` returned nothing.

16 instructions, read-free, base-parametric, in three segments:
`candMerge3Mid` (`:157`, 9 instructions, exit `E+9` on all three arms),
`candMerge3Right` (`:175`, 5, exit `E+14` on both arms),
`candMerge3Close` (`:190`, 2), composed at `candMerge3` (`:198`).

The M3d-6 design survived contact with the proof; two things are worth
recording because they are not obvious from the design note.

WHY THE `+1` BIAS PAYS FOR ITSELF TWICE.  The house bias (`0` = `none`,
`v + 1` = `some v`, decoded by `bestOfRegs`) was adopted for option
encoding.  It also makes both comparisons DIRECT: for two occupied
candidates the biased test `v₁ + 1 < v₂ + 1` is literally the route's
`v₁ < v₂`, so no unbiasing arithmetic is needed before either `natLt`.
That is why the block is 16 instructions and not ~24.  The accumulator
invariant carrying this is `regs' mAV = (candAfterMid ...).1 + 1`
(`candMerge3Mid_runsTo:365`), which is what lets the RIGHT phase compare
without decoding.

THE SIX PATHS FACTOR 3 x 2, AND SHOULD BE PROVED THAT WAY.  All three
middle arms converge on `E+9` and both right arms on `E+14`, so the block
splits into two lemmas (`candMerge3Mid_runsTo:365`,
`candMerge3RightClose_runsTo:549`) whose case analyses are 3 and 2 rather
than one analysis of 6.  `candMerge3_runsTo` (`:718`) composes them.  A
single six-way proof would have been roughly twice the size for the same
content.

Also delivered: `candMerge3_fits` (`:324`), constructor-exhaustive with no
wildcard arm and no divisor (hence no positivity side condition);
`candMerge3_readFree` (`:206`); `candMerge3_hosting` (`:337`);
`candMerge3Cats` (`:247`), a function of the route-side branch conditions,
never a numeral.

`bpFringeCandGlobal_isSome` (`:84`) fills a real gap found this session:
the tree relies on `bpFringeCandGlobal` being total into `some` at several
sites and in three prose comments, but had NO lemma for it -- every use
discharged it inline.  It is one line (`cases candidate? <;> rfl`).

### 2. ANTI-VACUITY BY EXECUTION, NOT ONLY HOSTING

`candMerge3_runsTo`'s six-way case split would still typecheck if two arms
had collapsed.  `candMerge3Witness_path1..6` (`:817`-`:841`) RUN the block
on six concrete register files and observe six distinguishable halts.

The paths are separated by BOTH observables the machine offers: modeled
steps (`10, 11, 13, 14, 12, 13`, which alone separate five of six) and the
close payload in `fRes` (`99, 200, 201, 302, 103, 304`, pairwise distinct,
separating the two 13-step paths).
`candMerge3Witness_paths_distinguishable` (`:843`) states the pairwise
distinctness as a `Nodup` that fails if any two paths collapse;
`candMerge3Witness_readLogs_empty` (`:855`) is the executed form of
`candMerge3_readFree`.  All eight depend on NO axioms -- they are kernel
computations, not `simp` arguments.

### 3. WHOLE-PROGRAM WIDTH CERTIFICATES (resume item 3) - LANDED

`RMQ/Core/WordRAM/E1ProgramWidth.lean`, new module.
`sameBlockLegProgramAt_fits` (`:57`) covers all 173 instructions;
`sameBlockDispatchProgram_fits` (`:141`) covers the dispatch composite,
carrying the cross arm as a hypothesis so the certificate can be stated
BEFORE the cross-block arm exists and will force it to be certified when
it does.

M3d-6 called this "assembly only".  It very nearly was, but two things it
would not have predicted:

* `rankCloseBlock` is instantiated at `L := shape.bpCode.length`, NOT the
  `machineWordBits ...` the fold body uses, so the leg-level certificate
  needs its OWN `shape.bpCode.length < 2 ^ w` hypothesis.  Passing the
  fold's `L` silently unifies the implicits to a wrong segment
  (`B + 111`) and fails with a membership mismatch, not a width error.
* the fold back edge's condition register `fCnt` is an `abbrev`, opaque
  to `omega` (the recurring M3d-4 gotcha), needing `show (52 : Nat) < 2 ^ w`.

### 4. VALIDATOR (delegation item 4): PHASES 3e AND 4d

`RMQ/Validation/E1MachineValidate.lean`.  The whole-query hole
(`wholeQueryComparisonAvailable` / `wholeQueryMismatches`, phase 5) is
UNTOUCHED and still reports `OPEN (interior leg blocked; NOT a pass)`.

Phase 3e runs the merge on 36 fixtures against `refMerge3` (`:801`), an
independent reference written from the specification.  It deliberately
does NOT share the route's structure: the route is a LEFT-ASSOCIATED
pairwise fold of option-lifted merges, while `refMerge3` flattens the
options first and folds once.  Agreement is therefore a check on the
association and the tie-break, not a restatement.  The value grids in
`mergeCases` (`:817`) overlap so TIES occur in both directions -- a
fixture set without ties could not distinguish `natLt` from `natLe`.

`mergePathCoverage` (`:926`) checks all six control paths are reached; it
is load-bearing, not decorative (see mutant D).

THE MUTATION BAR WAS RAISED, NOT REUSED, AND THE REASON MATTERS.  Every
earlier mutation in this harness is ultimately caught by RECEIPT diffing;
phase 4c's mutant B is the sharpest, changing one operand and reaching the
correct exit pc while its read log diverges.  THAT TEST IS UNAVAILABLE
HERE: the merge block is read-free, so the honest run and every mutant
produce the same empty receipt.

* mutant C (`mutatedMergeCompare:871`) swaps the two operands of the right
  comparison.  One operand, same length, same opcode-category sequence.
  `exitFailures=0`, `mismatches=24`.
* mutant D (`mutatedMergePosition:888`) makes the middle candidate's
  POSITION move read the left candidate's position.  One operand, same
  length, same opcode categories, and control flow COMPLETELY UNTOUCHED
  -- so it agrees with the honest run on exit pc, halted flag, modeled
  step count AND receipt.  `exitFailures=0`, `mismatches=8`.
  `mergeMutantDIsValueOnly` (`:948`) CHECKS case-for-case that the first
  three agree, so "only the value rejects it" is evidence rather than
  commentary.  Mutant D is only visible on cases where the middle
  candidate wins, which is why `mergePathCoverage` is load-bearing.

Mutant D is strictly harder than mutant B: B was caught by the receipt,
D cannot be.

### 5. THE CROSS-BLOCK ASSEMBLY (delegation item 3): WHY IT STOPPED HERE

The merge is built, so the M3d-6 obstacle is cleared.  The assembly
nevertheless did NOT proceed, for a reason checked at source this session
rather than assumed:

THERE IS NO ARM PROGRAM LAYOUT.  `sameBlockLegProgramAt`
(`E1SameBlockLeg.lean:595`) exists because someone built the leg's
instruction-list form.  The fringe ARM has no counterpart: `fringeArm_runsTo`
(`E1FringeArmBlock.lean:904`) is stated entirely against HOSTING
HYPOTHESES, and `rg` for `fringeArmProgram` returns nothing.  Assembling
the cross-block arm therefore needs, FIRST, an arm layout in the
`sameBlockLegProgramAt` idiom, and only then a five-segment cross-block
layout with a hole where the interior goes.  That is new construction,
not assembly, and it is bigger than the merge was.

This is a correction to the M3d-6 resume point, which listed item 4 as
"the two seeds re-hosted, the two arms hosted" -- reading as though
hosting the arms were a step of the same size as re-hosting the seeds.
The seeds do have a layout form; the arms do not.

### 6. THE INTERIOR INTERFACE OBLIGATION (stated precisely, as delegated)

The merge now EXISTS, so the contract the interior leg must satisfy is no
longer a design intention -- it is a signature.  When the interior
unblocks (worker B7, `claude/b7-charged-sparse-level`; the route literal
moves 207 -> 210), it must deliver `middle?` as:

* `E1CandMerge3.mMV` (register `77`) holding the BIASED occupancy-and-value
  word: `0` when `middle? = none`, `v + 1` when `middle? = some (v, _)`;
* `E1CandMerge3.mMP` (register `78`) holding the POSITION `p` when
  `middle? = some (_, p)`; UNCONSTRAINED when `middle? = none` (the block
  never reads `mMP` on the absent path -- `candMerge3Mid:157`, `E+2`
  branches away before any use).

Any other encoding forces a redesign of the merge block.  In particular:

* an UNBIASED value plus a separate occupancy flag would need an extra
  register and an extra test, changing the instruction count and every
  category log;
* a sentinel encoding (`middle?` absent as a large value) would BREAK THE
  TIE-BREAK: `bpCandidateBetter` uses strict `<` (`Candidate.lean:15`) so
  ties keep the LEFT candidate, and a sentinel that happens to tie with a
  real candidate would silently take the wrong branch.

The left and right candidates are already occupied by construction, which
is now a lemma rather than a per-site inline argument
(`bpFringeCandGlobal_isSome`, `E1CandMerge3.lean:84`).  The merge's
hypotheses `regs mLV = lv + 1` and `regs mRV = rv + 1`
(`candMerge3_runsTo:718`) are exactly that fact, so the arms need no
change.

THE INTERIOR ITSELF is unchanged and still blocked, for the reason M3d-3
section 2 records: `bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598`) applied to
`rightBlock - leftBlock - 1` (`ChargedFringeTrace.lean:1166`), derived at
RUNTIME and reaching an accepted read address, with no literal all-size
iteration cap.

### 7. GOTCHAS RECORDED THIS SESSION (carry forward)

1. `set ... with ...` is Mathlib and unavailable (M3d-4 gotcha 1 recurs).
   The core-Lean replacement that behaves identically is
   `obtain ⟨X, hX⟩ : ∃ z : RegFile, z = <expr> := ⟨_, rfl⟩`.  NOTE THE
   BINDER NAME: writing `∃ q : RegFile, q = q.write ...` shadows the outer
   `q` and fails with a confusing `Exists.intro ?m rfl` type mismatch, not
   a shadowing warning.
2. `obtain ⟨..⟩ := hr` CONSUMES `hr`.  If a later step needs the
   undestructured hypothesis (e.g. to feed a preservation lemma expecting
   the packed form), use `obtain ⟨..⟩ := id hr`.
3. A CONDITIONAL REGISTER VALUE does not close by `simp [hX, RegFile.write]
   <;> omega`: the goal becomes `(if a < b then 1 else 0) = 1` and `omega`
   cannot see through the `if`.  Use
   `rw [hX, RegFile.write_same]; exact if_pos (by omega)` (or `if_neg`).
4. `(fun _ => 0 : RegFile).write ...` DOES NOT ELABORATE.  Lean types the
   lambda as `Nat → Nat` before the ascription bites and reports
   `The environment does not contain Function.write`.  Write
   `RegFile.write (fun _ => 0) ...` in prefix form.
5. `decide` REFUSES FREE VARIABLES, so a per-instruction property of a
   base-parametric block (`.brNZ mMV (E + 4)`) cannot be closed by
   `decide` even when the property is independent of `E`.  Use
   `simp [Instr.category]`.  This is M3d-6 gotcha 2 in a new costume.
6. BULK-INJECTING REGISTER ABBREVS INTO EVERY `simp` LIST IS A BAD TRADE.
   It fixes the opaque-atom problem (M3d-2 gotcha 3) but produced 282
   unused-simp-arg warnings.  The `linter.unusedSimpArgs` output names the
   exact line and argument, so a short script can remove them iteratively;
   one pass sufficed.  Better to add the two or three abbrevs a site
   actually needs.
7. `lake build RMQ` STILL DOES NOT BUILD THE VALIDATOR (M3d-6 gotcha 1).
   Confirmed again this session.  `lake build rmq_e1_machine_validate` and
   `lake exe rmq_e1_machine_validate` are separate, and both were run.

### 8. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at every commit.  `lake build
rmq_e1_machine_validate` exit 0 and `lake exe rmq_e1_machine_validate`
exit 0 at HEAD, recorded separately BECAUSE of gotcha 7.

`#print axioms` run AFTER a root build on all nineteen theorems this
session claims.  Never `sorryAx`.  The six execution witnesses, the
`Nodup` distinguishability theorem, the empty-receipt theorem,
`bpFringeCandGlobal_isSome` and `bpCandidateMerge3?_some_left_right`
report NO axioms at all (kernel computation); the remainder report only
`propext` / `Classical.choice` / `Quot.sound`.

Validator figures, modeled and wall-clock kept apart: `mergeCases=36`,
`mergePathCoverage=6`, `mergeExitFailures=0`, `mergeMismatches=0`,
`mergeModeledSteps=431`, `mergeModeledReads=0`; `mergeWallClockMs=1`
(this binary on this host; NOT evidence).  Mutations:
`mergeMutationsAreReal=true`, `mutantC_compareSwap_exitFailures=0` /
`mismatches=24`, `mutantD_position_exitFailures=0` / `mismatches=8`,
`mutantD_isValueOnly=true`.  All pre-existing phases unchanged and still
passing.  `RESULT: PASS (with the whole-query comparison still OPEN)`.

### 9. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Matrix closure was impossible by construction: every row is
whole-query scoped and the whole-query composition is downstream of the
blocked interior leg.  Evidence accumulated is component-level and does
NOT discharge any row.

Component-level evidence added: REQ-E1-01 (the merge block, six paths
executed onto distinguishable halts); REQ-E1-02 (the FIRST whole-program
width certificates, plus the merge's own); REQ-E1-04 (nothing -- the merge
is read-free, and the honest statement is that it has no receipt to
compare); REQ-E1-06 (the merge's category log is a function of the
route-side branch conditions); REQ-E1-08 (an independent reference for the
merge, and a mutation that NO receipt diff could catch).

### 10. RESUME POINT (M3d-8)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Items 2-4 are unaffected.
2. BUILD THE FRINGE ARM'S PROGRAM LAYOUT, in the `sameBlockLegProgramAt`
   idiom (`E1SameBlockLeg.lean:595`) -- an instruction-list form plus a
   `..._hosts` decomposition and a `..._fits` certificate.  This is the
   newly-identified prerequisite for the cross-block arm (section 5); the
   arm's simulation `fringeArm_runsTo` (`E1FringeArmBlock.lean:904`)
   already exists and is arm-agnostic, so this is layout work, not new
   simulation work.
3. THEN the cross-block layout: left seed, left arm, INTERIOR HOLE, right
   seed, right arm, merge -- five sub-computations with non-adjacent seeds
   (`ChargedFringeTrace.lean:1144-1181`).  State it with the interior as a
   PARAMETER, as `sameBlockDispatchProgram_fits`
   (`E1ProgramWidth.lean:141`) already does for the cross arm, so the
   layout can be proved before the interior exists.
4. The merge is READY and needs nothing further: its contract on the
   interior is section 6 above, and it is base-parametric, so it drops
   into any layout at any offset.
5. WHOLE-QUERY GLUE, the derived all-size literal, and the amended target
   Prop remain out of scope, all downstream of item 1.  The validator hole
   is at `RMQ/Validation/E1MachineValidate.lean` phase 5
   (`wholeQueryComparisonAvailable` / `wholeQueryMismatches`) and is where
   the end-to-end machine-vs-`refRMQ` comparison attaches.

## M3d-8 (worker E1-R4r): the fringe ARM's program form, the cross-block layout, and both discriminators executed

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`810c68f` to `<HEAD>`.  Three milestones landed green and committed
(`156eed2`, `55694f5`, `f9553c8`).

### 1. THE FRINGE ARM'S PROGRAM FORM (resume item 2) - LANDED

`RMQ/Core/WordRAM/E1FringeArmProgram.lean`, new module.  This was the
prerequisite M3d-7 section 5 identified: `fringeArm_runsTo`
(`E1FringeArmBlock.lean:940`) is stated against SEVEN hosting hypotheses
and `rg fringeArmProgram` returned nothing, so no caller could discharge
them from one assumption.

`fringeArmProgramAt S c L A` (`:79`) is 95 instructions in six segments,
BASE-PARAMETRIC FROM THE START.  Its three internal addresses (the fold
merge target `A + 21`, the back edge `A + 21`, the epilogue base
`A + 88`) are all `A`-relative, so - unlike `sameBlockLegProgram`, which
was built pinned at `0` and cost M3d-6 a rebuild plus a `_zero`
specialisation lemma - there is NO base-`0` version to specialise from and
no rebuild scheduled.  The delegation named this explicitly and it was the
right call: the cross-block layout below hosts TWO arms at different
bases, which a pinned form could not have served at all.

Delivered: `_length` (`:87`), `_fold_eq` (`:95` - the arm's three fold
segments ARE `fringeLoopBody`'s three groups, which is what lets the width
certificate delegate 66 of the 95 instructions), `_hosts` (`:110`),
`_runsTo` (`:140`), `_fits` (`:188`, constructor-exhaustive, no wildcard
arm).

### 2. THE EXECUTION WITNESS, AND WHY BASE `2`

The delegation asked for a witness that EXECUTES rather than merely hosts.
`armWitnessProgram` (`:232`) pads with two instructions so the arm is
hosted at `2`, NOT `0`.  That is not decoration: at base `0` the internal
addresses coincide with their own offsets (`0 + 21 = 21`) and a
base-pinned layout typechecks by accident.
`fringeArmWitness_internalAddresses` (`:255`) observes `brNZ fCnt 23` at
index 87 and `brNZ fBV 95` at index 89 in the emitted list; at base `0`
these would read `21` and `93`.

`armWitness_path1..7` (`:288`-`:340`) RUN the arm on seven fixtures, all
halting at `97`.  `armWitness_paths_distinguishable` (`:346`) states
pairwise distinctness of `(steps, value, position, reads)` as a `Nodup`
that fails if any two paths collapse.  The seven cover BOTH epilogue arms
(occupied window rebase, paths 1-5; seed fallback, paths 6-7) and one, two
and three fold passes - so the epilogue branch and the fold back edge are
both witnessed live, not argued.

`fringeArmWitness_readsAreCharged` (`:366`) records `[5, 7, 8, 6]` charged
reads.  This matters for the validator: the arm is READ-BEARING, which is
exactly the property the merge block lacks.

All eight execution theorems depend on NO axioms (kernel computation).

TECHNIQUE: the multi-pass fixtures (143-271 modeled steps) need
`set_option maxRecDepth 40000`; the default budget reduces the 88-step
fixtures but not the longer ones, and the failure is a bare "maximum
recursion depth" with no indication that only SOME of the block's `rfl`s
are affected.

### 3. THE CROSS-BLOCK LAYOUT (resume item 3) - LANDED, interior parameterized

`RMQ/Core/WordRAM/E1CrossBlockArm.lean`, new module.

THE INTERFACE FIRST.  `crossBlockArmSpec` (`:132`) is the cross-block
object with the interior's whole `TraceResult` as an ARGUMENT.
`crossBlockArmSpec_eq` (`:170`) exhibits the accepted route object
(`ChargedFringeTrace.lean:1144`) as that spec applied to the interior's
current contents.  This is the ONLY place the interior appears
concretely: when B7 lands (interior trace gains reads, route literal
`207 -> 210`) this theorem's `interior` argument changes and nothing else
stated over `crossBlockArmSpec` does.
`crossBlockArmSpec_trace_of_interior_pure` (`:207`) makes "the interior is
a hole" checked rather than pictured.

FINDING, VERIFIED AT SOURCE - A CORRECTION TO THE M3d-7 RESUME POINT.
`E1SameBlockArm.windowRange` (`:447`) is NOT reusable by either cross arm.
Its high endpoint is driven by `rightClose - leftClose + 1`, the
SAME-BLOCK span between the two query endpoints.  Read off
`fringeLeg_trace_eq_leftArm` (`E1FringeArmBlock.lean:618`) and `_rightArm`
(`:647`), the left cross arm instead runs from `leftClose + 1` to the END
OF THE LEFT BLOCK, and the right cross arm STARTS at
`blockStartOf blockSize rightBlock` rather than at `leftClose + 1`.
Neither is `windowRange`'s arithmetic.  The M3d-7 resume point listed the
cross-block step as layout-then-assembly; two new preamble blocks were
required first.

NEW SEGMENTS, each with length, category log, straightness and a
constructor-exhaustive width certificate: `crossLeftRange` (`:225`, 10
instructions), `crossRightRange` (`:290`, 10), `crossStashLeft` (`:349`,
3) and `crossStashRight` (`:357`), `crossRepoint` (`:410`, 1).  Both range
preambles compute their ranges from `fClose` by `divConst`/`mulConst` on
the per-shape program constant `blockSize` (`blockOfClose bs c = c / bs`,
`blockStartOf bs b = b * bs`, `BlockLocal.lean:864,868`) - no route value
is copied in.  The stashes apply the house `+1` BIAS, which is not
bookkeeping: `candMerge3_runsTo` requires `regs mLV = lv + 1`, and that
hypothesis IS the route fact `bpFringeCandGlobal_isSome`.

THE LAYOUT.  `crossBlockArmProgramAt shape S blockSize A interior`
(`:452`) is `369 + interior.length` instructions, five sub-computations
with the two seeds NON-ADJACENT and the interior as a HOLE, in the route's
own emission order (only the two seed legs, the two arms and the interior
emit receipts; the preambles, stashes, repoint and merge are read-free).
`_hosts` (`:507`) derives all SEVENTEEN segment hosting facts from one
assumption, with every post-hole address forced by `interior.length`.
`_fits` (`:590`) is constructor-exhaustive over the whole arm and carries
the interior's instructions as a HYPOTHESIS - the
`sameBlockDispatchProgram_fits` idiom - so it is stated before the
interior exists and will force the interior to be certified when it lands.

Both arms are hosted at their own bases (`A + 78`, `A + 255 + n`) and each
receives its OWN base as the `fringeArmProgramAt` argument.  This is the
concrete payoff of milestone 1: a base-pinned arm form could not have
served both.

### 4. VALIDATOR (delegation item 3): PHASES 3f/4e AND 3g/4f

`RMQ/Validation/E1MachineValidate.lean`.  The whole-query hole (phase 5)
is UNTOUCHED and still reports `OPEN (interior leg blocked; NOT a pass)`.

DISCRIMINATOR CHOICE PER BLOCK, which is the point of these two phases:

* PHASE 3f/4e, the FRINGE ARM - RECEIPT.  The arm is read-bearing, so the
  receipt has power.  `refArmReads`/`refArmWindowAddrs` are computed from
  the specification BEFORE the program is built.  MUTANT E
  (`mutatedArmSegment`) charges the fold's chunk-table read to the next
  segment: same length, same opcode categories, and because the witness
  store answers every segment identically, exit pc, halted flag, step
  count, VALUE and POSITION are all unchanged.
  `armMutantEIsReceiptOnly` checks that case for case.
* PHASE 3g/4f, the CROSS-BLOCK RANGE PREAMBLES - VALUE.  Both are
  read-free, so no receipt exists to diff - the merge's situation.
  `refCrossLeftRange`/`refCrossRightRange` are written from the route's
  `blockStartOf`/`blockOfClose`, structurally different from the machine's
  fused `(leftBlock + 1) * blockSize`.  MUTANT F drops the `+ 1` that
  turns the block INDEX into the block's exclusive end.

MUTANT E IS THE EXACT MIRROR OF M3d-7's MUTANT D.  D was invisible to the
receipt and caught only by the value; E is invisible to the value and
caught only by the receipt.  M3d-7 ARGUED that the two discriminators are
complementary; this session EXECUTES the argument in both directions, so
complementarity is now evidence rather than commentary.

Anti-vacuity added: `armEpilogueCoverage` (must be 2), `armPassCoverage`
(must be > 1), `armModeledReads > 0`, `rangeModeledReads == 0`.
`eventAddr` returns `Option` so a non-`readWord` event SHRINKS the
projected list and is caught by the length check, rather than being passed
off as a read by a sentinel.

### 5. GOTCHAS RECORDED THIS SESSION (carry forward)

1. LONG `rfl` EXECUTION WITNESSES NEED `maxRecDepth` AND FAIL SELECTIVELY.
   88-step runs reduce under the default budget; 143-271-step runs do not.
   The error names only "maximum recursion depth", giving no hint that the
   short fixtures in the same block are fine.  `set_option maxRecDepth
   40000` at the section head.
2. `simp` DOES NOT CLOSE `A + k + m = A + (k+m)` WHEN THE OFFSET CARRIES A
   VARIABLE LENGTH.  In `crossBlockArmProgramAt_hosts` the goals
   `A + 176 + interior.length + 1 = A + 177 + interior.length` need
   `simp; omega`, while the interior-free ones close on `simp` alone.
   Reaching for `omega` uniformly instead produces unused-simp warnings.
3. `or_assoc` WAS NOT NEEDED in the 17-way `List.mem_append` flattening,
   contrary to the M3d-3 gotcha.  A fully right-nested `++` chain already
   produces a right-nested disjunction; the M3d-3 case had `++` groups.
   The linter names it as unused, so follow the linter, not the gotcha.
4. THE `Instr.FieldsFit` ABBREV-OPACITY GOTCHA STILL BITES ON ONE-LINE
   BLOCKS.  `crossRepoint_fits` has a single `move` and the obvious
   anonymous-constructor proof fails - `fClose`/`fRight` are abbrevs.
   Needs `simp only [Instr.FieldsFit, fClose, fRight]` first.  (M3d-4
   gotcha, recurring for the fifth session.)
5. AN UNBALANCED PAREN IN A DEEPLY NESTED `++` LAYOUT REPORTS AS
   "unexpected token" AT THE NEXT DECLARATION, not at the def.  The
   17-segment layout is one paren per segment; count them before trusting
   the error location.
6. THE VALIDATOR'S `mainImpl` DO-BLOCK NOW NEEDS `set_option maxRecDepth
   8192` at the namespace head.  Adding four phases pushed the whole
   do-block past the default budget, and the reported error line was in
   the MERGE phase (untouched this session), not in the new code.
7. `lake build RMQ` STILL DOES NOT BUILD THE VALIDATOR.  Confirmed again
   (M3d-6 gotcha 1, M3d-7 gotcha 7).

### 6. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at every commit.  At HEAD:

* `lake build RMQ RMQPaper RMQExamples` -> `Build completed successfully.`
* `lake build rmq_e1_machine_validate` -> `Build completed successfully.`
* `lake exe rmq_e1_machine_validate` -> exit 0,
  `RESULT: PASS (with the whole-query comparison still OPEN)`
* `lake env lean scripts/headline_axiom_check.lean` -> exit 0
* `git diff --check` and `git diff --check d90b062..HEAD` -> both exit 0
* `design_decision_check.ps1 -Strict -Base d90b062` ->
  `DESIGN-CHECK: checked 50 changed files`, exit 0
* `claim_drift_scan.ps1` ->
  `CLAIM-DRIFT: scan complete (739 hits, 0 strict failures)`, exit 0
* `paper_topology_lint.ps1` ->
  `PAPER-TOPOLOGY PASS (83 broad documentary identifiers; 49 paper
  identifiers resolved)`, exit 0
* hygiene `rg` over the three touched Lean files and `RMQ.lean`: no
  matches.  No `native_decide` anywhere under `RMQ/`.

`#print axioms` run AFTER a root build on all twenty-six theorems this
session claims.  Never `sorryAx`.  The eight arm execution witnesses,
`fringeArmProgramAt_fold_eq`, `crossLeftRange_cats`, `crossRightRange_cats`
and both `_straight` lemmas report no axioms or only `propext`; the
remainder report only `propext` / `Classical.choice` / `Quot.sound`.

Validator figures, modeled and wall-clock kept apart: `armCases=36`,
`armExitFailures=0`, `armReceiptFailures=0`, `armEpilogueCoverage=2`,
`armPassCoverage=4`, `armModeledSteps=6276`, `armModeledReads=234`;
`mutantE_segment_exitFailures=0`, `mutantE_segment_receiptFailures=36`,
`mutantE_isReceiptOnly=true`.  `rangeCases=54` per preamble,
`crossLeftRangeMismatches=0`, `crossRightRangeMismatches=0`,
`rangeModeledReads=0`; `mutantF_blockEnd_exitFailures=0`,
`mutantF_blockEnd_mismatches=33`.  Wall clock on this host, NOT evidence:
`armWallClockMs=10`, `armMutationWallClockMs=27`, `rangeWallClockMs=1`,
`rangeMutationWallClockMs=0`.  All pre-existing phases unchanged and still
passing.

NOTE ON `mutantF_blockEnd_mismatches=33` OF 54.  The mutation replaces
`leftBlock + 1` by `leftBlock + leftBlock`, which COINCIDES with the
honest value whenever `leftBlock = 1`.  21 of the 54 fixtures have
`leftBlock = 1`, so 33 rejections is the correct count, not a partial
failure.  A fixture set confined to the first block would have rejected
nothing.

### 7. PRE-EXISTING RED ITEMS, RECORDED NOT FIXED

Both owned by `claude/a07-blocker-repairs`; neither touched.

1. `lake exe rmq_succinct_classic_validate` exits 1.  THE BRIEF DESCRIBES
   THIS AS "a stale fixture"; what is actually observed is a COMPILE-TIME
   failure, so the executable never runs:
   `RMQ/Validation/SuccinctClassic.lean:253:0: expression
   singletonRepeatedEqualReadPositionsOK did not evaluate to 'true'`.
   Last touched by `f1c8af3` (B3 M5), an ancestor of this branch's base,
   so it is not this rung's.  Reported as a refinement, not a new defect.
2. `lake env lean scripts/wordram_axiom_check.lean` exits 1:
   `scripts/wordram_axiom_check.lean:197:14: error: unknown constant
   'RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_76'`
   - exactly as briefed.
3. `scripts/axiom_check.lean` and `gate.ps1` NOT RUN, per the delegation.

### 8. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Closure was impossible by construction: every row is whole-query
scoped and the whole-query composition is downstream of the blocked
interior leg.  Evidence added is component-level and discharges no row.

Component-level evidence added: REQ-E1-01 (the arm's program form executed
at a nonzero base on seven distinguishable paths); REQ-E1-02 (whole-arm
and whole-cross-block-arm width certificates, the latter carrying the
interior as a hypothesis); REQ-E1-04 (the arm's receipt checked against an
independent read reference, and a mutation NO value check could catch);
REQ-E1-06 (the new segments' category logs are functions or `.map
Instr.category`, never numerals); REQ-E1-08 (independent references for
the arm's reads and for both cross-block ranges, plus the first
receipt-only mutation in this harness).

### 9. RESUME POINT (M3d-9)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Items 2-5 are unaffected.
2. THE ONE GENUINELY NEW CERTIFICATE THE COMPOSITION NEEDS:
   `fringeArm_runsTo` (`E1FringeArmBlock.lean:940`) states NO register
   preservation clause at all, and `fringeArmProgramAt_runsTo`
   (`E1FringeArmProgram.lean:140`) inherits that gap.  The cross-block
   composition requires the LEFT stash's `mLV` (75) and `mLP` (76) to
   survive the interior, the right seed leg, the right range preamble and
   the RIGHT ARM.  Both registers sit above every existing block's write
   set, so this is a STRENGTHENING of an existing theorem (add a
   preservation clause on the write-set complement, discharged from the
   fold's and epilogue's existing preservation lemmas), not new
   simulation.  DO THIS FIRST: everything in item 4 depends on it.
3. `crossLeftRange_runsTo` / `crossRightRange_runsTo` and
   `crossStashLeft_runsTo` / `crossStashRight_runsTo` - four straight-line
   blocks, `RunsTo.straight` plus a `straight_eval`-style macro.  The
   route-side obligations are
   `(leftClose / bs + 1) * bs - leftClose =
   blockStartOf bs (blockOfClose bs leftClose) + bs - leftClose`
   (by unfolding plus `Nat.succ_mul`) and its right-hand analogue.  Both
   are already VALIDATED by execution against an independent reference
   (phase 3g), so the arithmetic is known right before the proof starts.
4. THEN `crossBlockArmProgramAt_runsTo`, stated over `crossBlockArmSpec`
   with the interior's `RunsTo` as a HYPOTHESIS (abstract entry/exit,
   trace, cats, and the two-register post-condition `mMV` biased / `mMP`
   positional per M3d-7 section 6).  Composition, but threading
   preservation across ~370 instructions.
5. WHOLE-QUERY GLUE, the derived all-size literal, and the amended target
   Prop remain out of scope, all downstream of item 1.  The validator hole
   is at `RMQ/Validation/E1MachineValidate.lean` phase 5
   (`wholeQueryComparisonAvailable` / `wholeQueryMismatches`).

## M3d-9 (worker E1-R4s): the arm's preservation clause, the composed cross-block arm, and a THIRD discriminator

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`49d4810` to `<HEAD>`.  Four milestones landed green and committed
(`a072028`, `5059459`, `91dad6c`, `00a3bfb`).

The M3d-8 resume point's items 2, 3 and 4 are all DONE.  Item 1 (the
interior `Nat.log2` decision) remains blocked and untouched.

### 1. THE PRESERVATION CLAUSE (resume item 2) - LANDED

`fringeArm_runsTo` now carries
`(forall r, FringeArmUntouched r -> regsF r = regs r)`.

`FringeArmUntouched r := r < 40 \/ (63 <= r /\ r <> 67 /\ r <> 68)`
is the EXACT union of the two constituent write sets --
`FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`, bank 40..62) and
`FringeCandGlobalUntouched` (`E1FringeArmBlock.lean:775`, 60/67/68) -- not
a conservative under-approximation invented to make the composition go
through.  Two pullback lemmas `fringeFoldUntouched_of_arm` /
`fringeCandGlobalUntouched_of_arm` do the work; the proof cost was three
lines, exactly as the resume point predicted.

Carried through `fringeArmProgramAt_runsTo`
(`E1FringeArmProgram.lean:139`).  `sameBlockArm_runsTo` discards it -- its
own conclusion does not restate it -- so no consumer statement moved.

### 2. TWO MORE GAPS OF THE SAME SHAPE, FOUND BY NEEDING THEM

Neither was in the resume inventory; both were found by attempting the
composition, and both are recorded at their definitions.

* `rankSeedLeg_runsTo_canonical` stated only FOUR specific preservation
  clauses (`fBase`/`fBB`/`fClose`/`fRight`) -- precisely the registers the
  SAME-BLOCK leg happened to need.  The cross-block composition must carry
  the left stash's `mLV`/`mLP` and the interior's `mMV`/`mMP` across the
  RIGHT seed leg, none of which is in that list.  Added
  `RankSeedLegUntouched r := (r <= 7 \/ 28 <= r) /\ r <> 46 /\ r <> 61 /\
  r <> 65` as a general clause; the four specific ones are retained so no
  consumer moved.
* `fOne` (40) IS INSIDE THE FOLD BANK.  `candMerge3_runsTo` requires
  `regs fOne = 1`, and nothing between the cross arm's entry and the merge
  guarantees it: `fOne` fails `FringeArmUntouched`, and the fold takes
  `fOne = 1` as a HYPOTHESIS without restating it as a conclusion.  New
  one-instruction segment `crossPinOne` re-pins it before the merge.  This
  is the THIRD instance of the same trade in this development
  (`fringeCandGlobal` pins its own `fT`; both stashes pin their own `mT`),
  and it was made the same way: one register write is cheaper than
  strengthening a 66-instruction loop's invariant.  Kept as its own
  segment rather than appended to `crossStashRight`, so the two stashes
  stay symmetric.  LAYOUT CONSEQUENCE: 369 -> 370 instructions, merge base
  `A+353+n` -> `A+354+n`; `_length`, `_hosts` and `_fits` all updated.

### 3. THE FIVE SEGMENT SIMULATIONS (resume item 3) - LANDED

All read-free, all by `RunsTo.straight`, all first-try green:
`crossLeftRange_runsTo`, `crossRightRange_runsTo`, `crossStashLeft_runsTo`,
`crossStashRight_runsTo`, `crossRepoint_runsTo`, plus `crossPinOne_runsTo`.

The two range preambles state their outputs in the ROUTE's own spelling
(`blockStartOf`/`blockOfClose`), so the composition feeds them straight
into `fringeArmProgramAt_runsTo` with no bridging step.  The machine's
fused `divConst`/`mulConst` form is connected to it by two new lemmas,
`cross_blockEnd_eq` and `cross_blockStart_eq` -- `Nat.succ_mul` is the
whole content, but the spellings are structurally different and nothing
else connects them.  The resume point predicted this obligation exactly,
and phase 3g had already validated the arithmetic by execution, so the
proofs started from a known-right target.

### 4. THE COMPOSED CROSS-BLOCK ARM (resume item 4) - LANDED

`crossBlockArmProgramAt_runsTo`: the whole 370-instruction cross arm at
the canonical store, receipts POSITIONALLY EQUAL to `crossBlockArmSpec`'s
trace at the supplied interior, `fRes` carrying its `.value`, and the
derived `crossBlockArmCats` whose every component -- including the merge
arm, selected by the arms' OWN values -- is a function of route-side data.

THE INTERIOR IS A HYPOTHESIS, NOT A PIN.  `hInterior` supplies the
interior's own `RunsTo` at its own base `A + 176`, for any entry register
file carrying the two query operands; its trace, categories and value are
PARAMETERS.  B7's change instantiates this theorem differently and does not
restate it.  The interior's four preservation obligations are exactly what
the composition consumes downstream and nothing more: `fClose`/`fRight`
(the repoint and the right preambles recompute everything else) and
`mLV`/`mLP`, which must survive 194 instructions to reach the merge.

RECORDED HONESTLY RATHER THAN PINNED (the delegation's instruction): if the
interior needs pinned machine inputs beyond the two query operands,
`hInterior`'s antecedent gains those conjuncts and the proof gains the
matching obligation to establish them at `A + 176`.  That is a hypothesis
change, not a restatement, and the four preservation clauses are
unaffected.  Nothing in this session was pinned to current interior
behaviour.

### 5. GOTCHAS RECORDED THIS SESSION (carry forward)

1. `set` IS MATHLIB-ONLY and fails as "unknown tactic" -- with the error
   reported on the `set` line but the whole remaining proof then reported
   as "unsolved goals", which makes it look like a proof failure rather
   than a missing tactic.  Write the terms out.
2. PC ARITHMETIC DOES NOT ASSOCIATE DEFINITIONALLY ONCE A VARIABLE LENGTH
   IS IN IT.  `A + 176 + n + 1` and `A + 177 + n` are equal but not defeq,
   so `RunsTo.trans` fails to chain.  The all-literal same-block leg never
   hit this and fixes its pc ONCE at the end; the cross-block composition
   must renormalise EVERY post-hole segment's exit.  New private helper
   `runsTo_pc_congr`.  The same bites hosting facts:
   `rankSeedLeg_runsTo_canonical` wants its rank block at `P + 1`, which is
   not defeq to the layout's `A + 182 + n`, so `q11`/`q12` must be restated
   by `rw` before use.
3. A MULTI-LINE `by` BLOCK INSIDE PARENTHESES must put `by` on its own
   line if the tactics span lines; `(by rw [...]` with the continuation
   less-indented parses the continuation OUTSIDE the block and reports
   "unexpected identifier" at a column in the middle of the term.
4. THE WORD "opaque" IN A COMMENT IS A HYGIENE HIT.  CHK-E1-02's `rg`
   matches the bare word anywhere, including prose.  Two pre-existing hits
   sit in comments (`E1FringeArmProgram.lean:213`,
   `E1CrossBlockArm.lean:475`); a third was introduced this session and
   reworded to "not transparent to `omega`" before commit.
5. THE `simpa ... using htrans` AT THE END OF A LONG COMPOSITION needs the
   statement's own ABBREVS in its simp set, not just the definitions.  The
   goal side arrives with `sbBase`/`sbChunkBits`/`crossLeftRelHi` unfolded
   and further normalised (`x + 1 + X - 1` collapsed), while `htrans`
   keeps them folded; the mismatch reads as a wall of near-identical terms.
6. `lake build RMQ` STILL DOES NOT BUILD THE VALIDATOR.  Confirmed again
   (M3d-6 gotcha 1, M3d-7 gotcha 7, M3d-8 gotcha 7).

### 6. VALIDATOR (delegation item 4): PHASE 3h/4g, A THIRD DISCRIMINATOR

`RMQ/Validation/E1MachineValidate.lean`.  Phase 5 UNTOUCHED and still
reporting `OPEN (interior leg blocked; NOT a pass)`.

DISCRIMINATOR CHOICE, AND WHY IT IS A DESIGN DECISION HERE.  M3d-7 argued
that value and receipt are complementary; M3d-8 executed both directions.
Neither has ANY power over a mutation that computes the right answer, does
the right reads, in the right number of steps, and merely scribbles on a
register it does not own.  That is precisely the defect class this
session's headline theorem excludes, so reusing either existing
discriminator would have left the new clause unexercised.

* PHASE 3h, the FRINGE ARM - PRESERVATION.  Every register satisfying
  `FringeArmUntouched` must leave the arm holding what it went in with.
  `presCases=36`, `presCheckedRegs=66`, `presFailures=0`,
  `presClobberedRegs=[]`.
  THE SENTINEL SEEDING IS LOAD-BEARING: from `fun _ => 0` this phase is
  VACUOUS, because a block that zeroes a register it does not own still
  "preserves" it.  `presSentinel r = r * 7 + 3` is injective and nowhere
  zero, so a clobber is detectable whatever it writes and a copied
  register is distinguishable from an untouched one.  The phase also
  re-runs each fixture zero-seeded and compares
  (`presSeedDisagreements=0`), which doubles as evidence that the arm
  reads no register it does not initialise.
* PHASE 4g, MUTANT G - renames the epilogue's private scratch register
  from `fT` (60) to 70, consistently across all three of its occurrences
  (`const fT 1`, `brNZ fT (E+7)`, `sub fRV fBV fT`).  Identical `fRV`,
  `fRP`, step count, control path and (empty) epilogue receipt.
  `mutantG_isPreservationOnly=true` CHECKS case for case that its exit pc,
  modeled steps, value and position all match the honest sweep, so both
  earlier discriminators are blind to it.
  `mutantG_scratch_preservationFailures=36`, and
  `mutantG_clobberedRegs=[70]` -- exactly the predicted register, which in
  the cross-block layout is `fClose`, the query operand the repoint and
  both right-hand preambles read.  A clobber there computes the right
  answer on the left and the wrong window on the right.

COMPLEMENTARITY IS NOW EXECUTED IN THREE DIRECTIONS, not two: D
value-only, E receipt-only, G preservation-only.

Phase 3g's note that the range preambles had no `_runsTo` theorems is now
stale and was corrected in place: they have them (section 3), so its
independent reference is a genuine cross-check rather than sole evidence.

### 7. VERIFICATION LEDGER (root builds, not per-file checks)

`lake build RMQ` exit 0 at every commit.  Decisive lines in the final
report.

`#print axioms` run AFTER a root build on all fourteen theorems this
session claims.  Never `sorryAx`.  `crossPinOne_runsTo`,
`cross_blockEnd_eq` and `cross_blockStart_eq` report only `propext`; the
four straight-line cross segments report `propext` / `Quot.sound`; the
remainder report only `propext` / `Classical.choice` / `Quot.sound`.

Validator figures, modeled and wall-clock kept apart.  NEW this session:
`presCases=36`, `presCheckedRegs=66`, `presExitFailures=0`,
`presFailures=0`, `presClobberedRegs=[]`, `presSeedDisagreements=0`,
`presSentinelNonZero=true`; `presMutationIsReal=true`,
`mutantG_scratch_exitFailures=0`,
`mutantG_scratch_preservationFailures=36`,
`mutantG_clobberedRegs=[70]`, `mutantG_isPreservationOnly=true`.
Wall clock on this host, NOT evidence: `presWallClockMs=35`,
`presMutationWallClockMs=88`.
All pre-existing phases unchanged and still passing (`armCases=36`,
`armModeledSteps=6276`, `armModeledReads=234`, `armEpilogueCoverage=2`,
`armPassCoverage=4`; `mergeCases=36`, `mergePathCoverage=6`,
`mergeModeledSteps=431`, `mergeModeledReads=0`; `rangeCases=54`,
`crossLeftRangeMismatches=0`, `crossRightRangeMismatches=0`).
`RESULT: PASS (with the whole-query comparison still OPEN)`.

### 8. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Closure was impossible by construction: every row is whole-query
scoped and the whole-query composition is downstream of the blocked
interior leg.  Evidence added is component-level and discharges no row.

Component-level evidence added: REQ-E1-01 (the cross-block arm composed as
ONE program over an abstract interior, 370 atomic-constructor
instructions); REQ-E1-02 (the layout's width certificate updated for the
new segment, still carrying the interior as a hypothesis); REQ-E1-04 (the
composed arm's receipt POSITIONALLY equal to `crossBlockArmSpec`'s trace);
REQ-E1-06 (`crossBlockArmCats` is a function of route-side data
throughout, with the interior's log a parameter); REQ-E1-08 (a THIRD
discriminator with a mutation neither earlier one can catch).

INV-NO-SYNTHETIC and INV-TRACE-EXECUTION gain the preservation evidence:
the arm's register footprint is now checked by execution, not only proved.

### 9. RESUME POINT (M3d-10)

NOTHING below is implemented.

1. STILL BLOCKED: the interior-leg `Nat.log2` decision (M3d-3 section 2).
   Everything remaining on the cross-block path is now downstream of it --
   which is a change from M3d-8, where items 2-4 were independent.
2. DISCHARGE `hInterior` in `crossBlockArmProgramAt_runsTo`
   (`E1CrossBlockArm.lean:1143`).  This is THE remaining cross-block
   obligation and it is the only one; the statement, the layout
   (`crossBlockArmProgramAt_hosts:829`), the width certificate
   (`crossBlockArmProgramAt_fits:913`), the category log
   (`crossBlockArmCats:1088`) and every surrounding segment are done and
   green.  The segments, all verified at these lines this session:
   `crossLeftRange_runsTo:514`, `crossRightRange_runsTo:561`,
   `crossStashLeft_runsTo:618`, `crossStashRight_runsTo:651`,
   `crossPinOne_runsTo:687`, `crossRepoint_runsTo:712`; the two arithmetic
   bridges `cross_blockEnd_eq:493` / `cross_blockStart_eq:500`; the pc
   helper `runsTo_pc_congr:119`; the new segment `crossPinOne:436`.
   Upstream, `FringeArmUntouched` (`E1FringeArmBlock.lean:951`) with
   `fringeFoldUntouched_of_arm:955` / `fringeCandGlobalUntouched_of_arm:961`
   and the strengthened `fringeArm_runsTo:975`; `RankSeedLegUntouched`
   (`E1SameBlockLeg.lean:209`) and `rankSeedLeg_runsTo_canonical:221`.
   Validator phase 3h/4g: `presSentinel`
   (`RMQ/Validation/E1MachineValidate.lean:1359`),
   `armUntouchedRegs:1375`, `runPres:1400`, `mutatedArmScratch:1476`,
   `presMutantGIsPreservationOnly:1492`.
3. ANTI-VACUITY BY EXECUTION for the composed cross arm.  The seventeen
   hosting facts are derived from one assumption
   (`crossBlockArmProgramAt_hosts`), but no concrete program has been RUN
   through the whole cross arm the way `armWitness_path1..7`
   (`E1FringeArmProgram.lean:294`) runs the single arm.  Needs a concrete
   interior to fill the hole, so it is downstream of item 1.  When it is
   done, host it OFF BASE ZERO for the M3d-8 reason.
4. If the interior needs pinned inputs beyond `fClose`/`fRight`, extend
   `hInterior`'s antecedent and establish them at `A + 176` (section 4).
5. WHOLE-QUERY GLUE, the derived all-size literal, and the amended target
   Prop remain out of scope, all downstream of item 1.  The validator hole
   is at `RMQ/Validation/E1MachineValidate.lean` phase 5
   (`wholeQueryComparisonAvailable` / `wholeQueryMismatches`).

## M3d-11 (worker E1-R4t): the interior's atomic table read, and the two-regime finding that resizes the remaining interior work

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`f9b1ecc` (the B7 merge) to `<HEAD>`.  One milestone landed green and
committed (`3811920`).

The M3d-10 resume point's item 1 -- "STILL BLOCKED: the interior-leg
`Nat.log2` decision" -- IS DISCHARGED, by B7 rather than by this session.
`Nat.log2` is gone from every executed definition; it survives only in
table-CONSTRUCTION generators (`bpSparseLevelCell`,
`SparseLevelTable.lean:55`), in the spec-side `PayloadLive*` refinement
ladder (`LocalGlobalSparse.lean:30-31`, `:603-604`), and in space-budget
proofs.  The interior's level and span now arrive from ONE charged
count-indexed table read whose cell packs both, unpacked by constant-divisor
`div`/`mod` (`bpSparseLevelCell_div` / `_mod`, `SparseLevelTable.lean:78`,
`:90`).  Item 2, discharging `hInterior`, is now genuinely unblocked and is
what the remaining interior work consists of.

### 1. THE ATOM (landed)

New module `RMQ/Core/WordRAM/E1InteriorReadBlock.lean`, imported from
`RMQ.lean:40`.

Every memory read the interior performs is one instance of
`FixedWidthNatTable.machineReadComputationAt`
(`MachineChunkedTableProgram.lean:343`).  The maximising cross-macro branch
makes THIRTY-THREE of them.  A defect in the atom multiplies by thirty-three,
so it is landed and certified alone before any composite.

* `interiorReadNat:107` -- seven instructions, ONE branch, exactly ONE
  `readMem`.  `interiorReadAddr:125` is the route's own case split.
* `interiorReadNat_runsTo:214` -- exact simulation: positional singleton
  receipt, category log indexed by the route-side validity condition,
  decoded cell in the option-shift convention, preservation off the
  three-register write set `InteriorReadNatUntouched:159`.
* `interiorReadNat_route_atom:443` -- THE BRIDGE.  The route's adapter, at
  one chunk, issues that same address, emits that same one-event trace, and
  decodes to that same value.  Supported by `chunkCount_eq_one:400`,
  `footprintAt_eq_singleton:415`, `collectPayloadWords_singleton:425`.
* `interiorReadNat_fits:175` -- constructor-exhaustive width certificate, no
  wildcard arm, no divisor hence no positivity arm.
* `interiorReadNatCats_memoryRead_count:151` -- exactly one charged read on
  EITHER path.  Depends on no axioms.

THE VALIDITY TEST IS MACHINE-PERFORMED, not a Lean-level `if` around the
block: `natLt` at `Q+1` on the machine's own index register, branched at
`Q+4`.  The dead path costs one more controller step but not one more read,
matching `machineReadCostedWithStore_cost` (`MachineChunkedTable.lean:240`).
Recorded as DD-20260719-002, together with the fresh register bank `85 .. 88`
chosen above the merge slots `75 .. 84` so no interior scratch can collide
with the `mLV`/`mLP`/`mMV`/`mMP` that `hInterior` must preserve.

### 2. THE FINDING THAT RESIZES THE REMAINING WORK

THE INTERIOR'S ATOMIC READ IS NOT SINGLE-CHUNK IN GENERAL, and the route's
own cost lemmas already distinguish two regimes.  This was found by asking
what `interiorReadNat`'s one `readMem` is entitled to assume, not by reading
the cost prose, which states only the macro-crossing rate.

* MACRO-CROSSING: `width <= machineWordBits` gives chunk count `1`
  (`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`,
  `InteriorDirectory.lean:4060`).  This is the `11`-per-two-span rate and the
  attained `33`.
* WITHIN-MACRO: only `width <= 7 * machineWordBits` is available, so the rate
  is `canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`
  (`InteriorDirectory.lean:4511`), consumed by
  `..._cost_le_twenty_six_of_size_ge_four` (`:5196`), whose arithmetic is
  explicitly `26 = 8 + 9 + 9`.  AT SMALL SHAPES ONE LOGICAL INTERIOR READ CAN
  EMIT UP TO EIGHT PHYSICAL READ EVENTS.

Consequence, stated plainly: `interiorReadNat` is CORRECT BUT INSUFFICIENT
ALONE.  It carries `0 < width` and `width <= wordSize` as EXPLICIT
hypotheses on its bridge rather than discharging them from the current
tables, so every consumer inherits the obligation instead of the shape being
silently assumed.  The interior simulation needs a SECOND block: an
eight-capped chunk fold for the within-macro regime.

THIS IS NOT A RETURN TO THE PRE-B7 OBSTRUCTION.  `8` is a LITERAL cap, and
the fold is the same truncated-subtraction cap chain `x - (x - 8)` that
`fringeArmInit` (`E1FringeArmBlock.lean:118`) already uses for the fringe's
`33`.  REQ-E1-06 conjunct (c) -- an all-size literal total with no size
hypothesis -- survives intact.  Recorded as DD-20260719-003.

`0 < width` is the half the route's cost bound does not need and is stated
anyway: at `width = 0` the route reads NOTHING while the block still reads
once, and an `<= 1` cost bound hides exactly that off-by-one.

### 3. THE ROUTE-SIDE MAP THE NEXT SESSION SHOULD NOT RE-DERIVE

Interior object: `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`)
instantiates the interior as
`concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore`
(`ConcreteDirectoryRAMStoreParam.lean:3639`), guarded by
`leftBlock + 1 < rightBlock` (else `TraceResult.pure none`, zero events).
That def is a `flatStoreExecutionTraceResultAtSegment` of
`canonicalRelativeRmmInteriorRangeMinComputation` (`InteriorDirectory.lean:2444`)
on the SINGLE segment `segments.canonicalComponent`, the literal `20`
(`Segments.lean:60`).  `FlatStoreComputation.bind` appends read logs
left-to-right, and the trace map preserves log order, so TRACE ORDER =
TEXTUAL BIND ORDER.

Five branches, writing `L`/`G` for the local/global level read, `o`/`b` for
the local-offset / global-block read, and `S` for the four-read summary group
(`baseline, minRel, maxRel, argOffset`, in that order,
`InteriorDirectory.lean:2277`):

| Branch | Guard | Read sequence | reads |
| --- | --- | --- | --- |
| B0 empty | `count = 0` | (none) | 0 |
| B1 within-macro | `count <= macroSize - localStart` | `L, o,S, o,S` | 11 |
| B2 adjacent-macro | `middleMacroCount = 0` | `L,o,S,o,S, L,o,S,o,S` | 22 |
| B3 left+middle | `rightCount = 0` | `L,o,S,o,S, G,b,S,b,S` | 22 |
| B4 cross-macro | otherwise | `L,o,S,o,S, G,b,S,b,S, L,o,S,o,S` | 33 |

A `none` level read short-circuits its two-span call to `pure none` and its
two span reads are NOT emitted; likewise a `none` offset/block read skips the
following summary group.  The level read is indexed by THE COUNT ITSELF --
no slot arithmetic -- while `o`/`b` carry `bpLocalSparseCellSlot` /
`bpGlobalSparseCellSlot` arithmetic.

### 4. THE READ-ORDER INVARIANT, INHERITED FROM B7 AND WORTH RESTATING

B7's whnf timeout (`B7_WORKLOG.md:1954-2005`) was a membership cascade
encoding a STALE READ ORDER: a witness claimed the sparse-OFFSET read was
leftmost via `List.mem_append_left`, which the swap made false, and
elaboration went hunting through concrete slot arithmetic until the heartbeat
budget blew.  Raising `maxHeartbeats` would have produced a theorem
describing the wrong machine.

THE INVARIANT TO ENCODE: the LEVEL read is the unconditional head of every
two-span call's append chain -- the outer `bind` performs it before matching
on the read value.  Any positional or membership lemma that assumes otherwise
presents as a HEARTBEAT TIMEOUT, not as a clean type error.  Diagnose a whnf
timeout in this area as a read-order defect first.

### 5. VERIFICATION LEDGER

`lake build RMQ` exit 0.  Decisive lines:
`[249/251] Built RMQ.Core.WordRAM.E1InteriorReadBlock`,
`[250/251] Built RMQ`, `Build completed successfully.`

`#print axioms` AFTER the root build, importing
`RMQ.Core.WordRAM.E1InteriorReadBlock` DIRECTLY (`import RMQ` does not reach
it):

    interiorReadNat_runsTo                depends on axioms: [propext, Quot.sound]
    interiorReadNat_fits                  depends on axioms: [propext, Quot.sound]
    interiorReadNat_route_atom            depends on axioms: [propext, Quot.sound]
    chunkCount_eq_one                     depends on axioms: [propext, Quot.sound]
    footprintAt_eq_singleton              depends on axioms: [propext, Quot.sound]
    collectPayloadWords_singleton         depends on axioms: [propext]
    interiorReadNatCats_memoryRead_count  does not depend on any axioms

Never `sorryAx`.  The validator was NOT extended this session and phase 5
still reports `OPEN (interior leg blocked; NOT a pass)`; that report is now
STALE IN ITS REASON -- the interior is no longer blocked, it is unbuilt --
and the next session should reword it as it closes it.

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Closure was impossible by construction: every row is whole-query
scoped and the whole-query composition is downstream of the interior
simulation, of which this session landed the atom.

Component-level evidence added: REQ-E1-01 (one more atomic-constructor block,
with the guard decided by a machine comparison rather than a meta-level
`if`); REQ-E1-02 (`interiorReadNat_fits`, constructor-exhaustive, no wildcard
arm); REQ-E1-04 (`interiorReadNat_route_atom`, positional singleton receipt
equal to the route adapter's trace); REQ-E1-06 (`interiorReadNatCats` is a
function of the route-side validity condition, never a numeral, and the
two-regime finding fixes the remaining cap as the LITERAL `8`).

REQ-E1-06's standing residual gap -- "the interior loop has no literal
all-size iteration cap" -- is now SUPERSEDED IN ITS CAUSE.  B7 removed the
`Nat.log2` loop; what remains is the chunk fold, which does have a literal
cap (`8`).  The gap should be restated by the coordinator rather than
carried forward in its old wording, which named a mechanism that no longer
exists.

### 7. RESUME POINT (M3d-12)

NOTHING below is implemented.

1. THE EIGHT-CAPPED CHUNK FOLD.  `interiorReadNat` covers the single-chunk
   regime only (section 2).  Build its within-macro twin as a capped fold
   over `fixedWidthNatTableMachineFootprint`, cap `8`, using the
   `x - (x - 8)` chain from `fringeArmInit` (`E1FringeArmBlock.lean:118`) and
   the fold-loop pattern of `fringeFoldLoop_runsTo_accepted`
   (`E1FringeFoldBlock.lean:1301`), whose receipt is already a POSITIONAL
   `List` equality via `iterLog_congr` + `iterLog_singleton_desc`.  Decide
   deliberately whether the interior uses ONE block carrying the cap (simpler
   layout, eight-step cost everywhere) or TWO with a per-shape generator
   choice (tighter, but the generator then branches on a shape predicate --
   check that against INV-ALL-SIZE before committing to it).
2. THE SUMMARY GROUP `S`: four atomic reads at
   `baseline (block / blocksPerSuper)`, `minRel block`, `maxRel block`,
   `argOffset block`, in that order, then the four-way `match` into
   `Option (Nat x Nat x Nat x Nat)` and `bpRelativeSummaryMinCandidate`
   (`InteriorDirectory.lean:2277`, `:2300`).  Between reads the caller must
   stage `iVal` into a holding register and reset `iIdx`; `iIdx` is
   read-only within the atom, so only the caller writes it.
3. THE SPAN BLOCKS: `o`/`b` read plus option dispatch into the summary group
   (`:2311`, `:2329`).  The `none` arm emits NOTHING -- the block must branch
   PAST the summary group, not run it and discard.
4. THE TWO-SPAN BLOCKS: level read, then constant-divisor `div`/`mod` by
   `bpSparseLevelDomain`, then two span blocks and `bpCandidateMerge?`
   (`:2351`, `:2376`).  The level read is the UNCONDITIONAL HEAD (section 4).
5. THE FIVE-BRANCH DISPATCH (`:2444`) and then `hInterior` in
   `crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean:1143`), whose four
   preservation obligations (`fClose`, `fRight`, `mLV`, `mLP`) are all
   outside the interior bank `85 .. 88` by construction.
6. Only then: the whole-query glue, the derived literal, the amended target
   Prop, the validator's phase 5, and the doc rows.  All remain out of scope
   and all are downstream of item 5.

OPEN THREAD INHERITED FROM B7, NOT RESOLVED HERE (STRETCH-01,
`B7_WORKLOG.md:1063-1068`): whether
`concreteBPFiniteSmallInteriorRangeMinTable` /
`...AllSizeStructuralLegacy` (`ConcreteDirectoryRAM.lean:1100-1209`), which
dispatches to `boundedSummaryRangeScanTraceResultAtSegments` -- a name
suggesting a LINEAR SCAN -- is dead from the whole-query root.  Tracing this
session found the live route reaching only the `canonicalComponent` flat
execution, with the `...Legacy` def at
`ConcreteDirectoryRAMStoreParam.lean:3624` unreferenced by that chain, which
is CONSISTENT WITH IT BEING DEAD BUT IS NOT A PROOF OF ABSENCE.  If it is
live, the interior has a sixth branch and it is a scan; that would bear
directly on REQ-E1-07's supersession note.  Worth a definitive answer before
the target Prop is stated.

## M3d-12 (worker E1-R4u): the interior's eight-capped chunk fold, built and executed

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`7bdef2c` (M3d-11's yield) to `<HEAD>`.  Five commits, all green.

The M3d-11 resume point's item 1 -- THE EIGHT-CAPPED CHUNK FOLD -- IS
BUILT.  Items 2-6 (the summary group, the span blocks, the two-span
blocks, the five-branch dispatch, `hInterior`) are NOT, and remain the
frontier in that order.

The suspected sixth interior branch is settled and needs no further work:
the coordinator established that
`boundedSummaryRangeScanTraceResultAtSegments`'s only two non-theorem
references (`ConcreteDirectoryRAM.lean:1205`, `:1232`) are inside the
`...AllSizeStructuralLegacy` def (`:1196`) and a `..._total_legacy`
theorem (`:1219`), while the accepted route consumes the NON-legacy
`...AllSizeStructural` (`:1188`), whose body ends before `:1196`.  THE
INTERIOR HAS FIVE BRANCHES AND NO SCAN.

### 1. WHAT LANDED

New module `RMQ/Core/WordRAM/E1InteriorChunkFold.lean` (1973 lines),
imported from `RMQ.lean:41`.  Register bank `89 .. 99`
(DD-20260719-007), disjoint from the merge slots the cross-block
composition requires the interior to preserve, and from the atom's
`85 .. 88` -- the fold READS `iIdx` (`85`) and writes nothing below `89`.

Thirty-seven instructions in four segments, exactly ONE `readMem`:

* `interiorChunkInit:268` (17), `interiorChunkReadBody:292` (9),
  `interiorChunkCombine:316` (8), `interiorChunkEpilogue:336` (3),
  assembled by `interiorChunkFold:346`.
* `interiorChunkFold_runsTo:1785` -- THE HEADLINE.  From the block entry
  with the logical index in `iIdx`, the hosted block runs to `Q + 37`
  emitting EXACTLY the route's trace for that chunked read --
  positionally, address for address, word for word, on BOTH arms of the
  validity split -- charging the fold's category log and leaving the
  decoded cell in `cOut` in the option-shift convention.
* `interiorChunkReadLoop_runsTo:1013` and
  `interiorChunkCombineLoop_runsTo:1309`, composed from
  `interiorChunkReadBody_step:770` and `interiorChunkCombine_step:1192`
  through `RunsTo.iterate`.
* `interiorChunkInit_runsTo:1483`, `interiorChunkEpilogue_runsTo:1672`.
* `chunkEventsAt_eq_route:1745` (positional receipt identity), consuming
  `chunkAddrs_eq_consecutive:159`.
* `interiorChunkFoldCats_memoryRead_count:457` -- the block's memory
  traffic DERIVED from the category algebra as exactly the iteration
  count -- and `interiorChunkFoldCats_memoryRead_le_eight:480`.
* `interiorChunkCount_le_eight:189`, `interiorChunkCount_pos:204`.
* `interiorChunkFold_fits:619`, constructor-exhaustive, per segment at
  `:507`, `:552`, `:578`, `:602`.  This block DOES carry a divisor, so
  unlike the atom it has a positivity arm.

### 2. THE THREE DESIGN DECISIONS, AND WHY THEY WERE FORCED

DD-20260719-004 (two loops, one reads).  The route's value is
`bitsToNatLE` of the chunk CONCATENATION, i.e. LITTLE-endian in the chunk
index.  The machine has `mulConst`/`divConst` -- scale a register by a
program CONSTANT -- and NO register-by-register multiply (`Instr`,
`E1Machine.lean:76`), so the little-endian term
`2 ^ (j * wordSize) * chunk j` cannot be formed: it needs the running
power TIMES the fresh chunk, and both are runtime registers.  What
`mulConst` supports is the Horner step
`acc := acc * 2 ^ wordSize + chunk j`, which accumulates BIG-endian.  So
the fold reads ascending into a big-endian accumulator and a SECOND,
READ-FREE loop reverses the base-`2 ^ wordSize` digits.

Reading descending would have collapsed this to one loop and was
REJECTED: the route's `readMany` issues ascending addresses and the
receipt obligation is POSITIONAL list equality.  Trading a read-free
arithmetic loop for a wrong trace order is the same class of defect as
B7's stale read order.

DD-20260719-005 (the cap is machine-enforced).  Unlike the fringe's `33`,
whose uncapped count derives from a query-dependent register, the
interior's chunk count depends only on the shape, so it reaches the
machine as a program CONSTANT.  The tempting simplification -- let the
loop count BE that constant and prove `chunkCount <= 8` about it -- would
make the literal cap a property of a theorem about the GENERATOR, not of
the machine.  Instead `interiorChunkInit` computes
`chunkCount - (chunkCount - 8)` at runtime (`cap_chain_eq_min:1461` is the
arithmetic content), so a shape presenting a larger count runs a SHORT
fold, never an unbounded one; `interiorChunkCount_le_eight` then shows no
reachable shape does, making the cap exact rather than lossy.

Recorded deliberately: `interiorChunkCount_le_eight` carries NO
`0 < wordSize` hypothesis because it does not need one.  At `wordSize = 0`
the route's own definition gives `width / 0 = 0` and `width % 0 = width`,
so the count is at most the indicator `1`.  The cap stays UNCONDITIONAL,
which is what the all-size claim needs.

DD-20260719-006 (the dead path is a one-chunk fold).
`machineReadComputationAt` (`MachineChunkedTableProgram.lean:343`) applies
the SAME decode to both arms of its validity split; only
`machineReadCostedWithStore` short-circuits to `none`.  The interior
consumes the COMPUTATION form, so the machine realises the dead path by
overriding `cAddr`/`cCnt` before the loop, and the receipt obligation
becomes UNIFORM in the validity condition.

### 3. THE TWO HYPOTHESES THAT ARE NOT DECORATION

`interiorChunkFold_runsTo` carries `0 < chunkCount` and `chunkCount <= 8`.

`0 < chunkCount` is the half the route's `<= 8` cost bound does NOT
supply.  The back edge makes both loops do-while, so at zero chunks the
machine reads once while the route reads nothing.  This is the same
off-by-one M3d-11 recorded for the single-chunk atom, surfacing again
rather than being silently assumed.

`chunkCount <= 8` is the within-macro cap, discharged for every reachable
shape by `interiorChunkCount_le_eight` from
`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`
(`InteriorDirectory.lean:4511`).

### 4. THE PATHS EXECUTE, ONTO DISTINGUISHABLE HALTS

`chunkFoldWitness:1886` runs the fold at base `0` on a concrete store
(`witnessStore:1875`): one segment, table base `10`, dead address `99`,
three entries, TWO chunks per entry, word scale `2`.

    path                  steps  cOut  readLog
    both chunks present   53     2     [10 some, 11 some]   :1909
    second chunk missing  52     0     [12 some, 13 none]   :1918
    both chunks missing   52     0     [14 none, 15 none]   :1924
    dead path             38     2     [99 some]            :1932

All four halt (`chunkFoldWitness_all_halt:1937`) and are pairwise
distinguishable (`chunkFoldWitness_paths_distinguishable:1955`, by
`decide`).  Path 1 returning `cOut = 2` is the EXECUTED check that the
big-endian read loop and the read-free reversal loop compose back to the
route's little-endian value: `bitsToNatLE ([true] ++ [false]) = 1`.

WORTH CARRYING TO M6.  Paths 2 and 3 agree on BOTH the modeled step count
(`52`) and the returned cell (`0`), and are separated ONLY by the read
log.  On this block a value check has no power over a receipt-only
difference and step counting has none either; a mutation redirecting a
chunk read to a different address of the same multiplicity passes both and
is caught only by event-by-event receipt diffing.  That is a concrete
instance of the discriminator-power question M6 must answer.

### 5. VERIFICATION LEDGER

`lake build RMQ` exit 0:
`[250/252] Built RMQ.Core.WordRAM.E1InteriorChunkFold`,
`[251/252] Built RMQ`, `Build completed successfully.`
`lake build rmq_e1_machine_validate` exit 0; `lake exe` exit 0,
`RESULT: PASS (with the whole-query comparison still OPEN)`.

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkFold` DIRECTLY:

    interiorChunkFold_runsTo             [propext, Classical.choice, Quot.sound]
    interiorChunkReadLoop_runsTo         [propext, Classical.choice, Quot.sound]
    interiorChunkCombineLoop_runsTo      [propext, Classical.choice, Quot.sound]
    interiorChunkInit_runsTo             [propext, Quot.sound]
    interiorChunkEpilogue_runsTo         [propext, Quot.sound]
    interiorChunkReadBody_step           [propext, Quot.sound]
    interiorChunkCombine_step            [propext, Quot.sound]
    interiorChunkFold_fits               [propext, Quot.sound]
    interiorChunkFoldCats_memoryRead_count     [propext, Quot.sound]
    interiorChunkFoldCats_memoryRead_le_eight  [propext, Quot.sound]
    interiorChunkCount_le_eight          [propext, Classical.choice, Quot.sound]
    chunkEventsAt_eq_route               [propext, Quot.sound]
    chunkFoldWitness_paths_distinguishable     does not depend on any axioms
    chunkFoldWitness_path_bothPresent          does not depend on any axioms
    chunkFoldWitness_readCounts                does not depend on any axioms

Never `sorryAx`.

The validator's phase 5 REASON was STALE and is corrected
(`E1MachineValidate.lean:982` docstring and the report line): it named the
`bpSparseLogSpan`/`Nat.log2` obstruction, which B7 discharged.  The phase
stays OPEN -- it is not a pass -- but now reads "interior leg UNBUILT, not
blocked".

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Closure was impossible by construction: every row is whole-query
scoped and the whole-query composition is downstream of the interior
simulation, of which this session landed the second of six pieces.

Component-level evidence added: REQ-E1-01 (a second interior block whose
guard is decided by a machine comparison, and whose iteration cap is
computed by the machine rather than asserted); REQ-E1-02
(`interiorChunkFold_fits`, constructor-exhaustive, with the divisor
positivity arm the atom did not have); REQ-E1-04
(`chunkEventsAt_eq_route`, positional receipt equality with the route's
address list on both arms of the validity split); REQ-E1-05
(`chunkFoldWitness_paths_distinguishable`, four EXECUTED paths onto
distinguishable halts); REQ-E1-06
(`interiorChunkFoldCats_memoryRead_count` derives the block's memory
traffic from the category algebra, and
`interiorChunkFoldCats_memoryRead_le_eight` caps it at the literal `8`
with no size hypothesis).

REQ-E1-06's standing residual gap, restated: the interior loop now HAS a
literal all-size iteration cap, machine-enforced.  What is still missing
for the row is not the cap but the composition -- the cap is proved of one
block, not yet of the interior leg.

### 7. RESUME POINT (M3d-13)

NOTHING below is implemented.  Items 2-5 are M3d-11's items 2-5 unchanged;
the fold they were waiting on now exists.

1. THE VALUE BRIDGE, NEWLY OPENED BY THIS SESSION AND THE ONE PIECE OF THE
   FOLD NOT YET DONE.  `interiorChunkFold_runsTo` gives the RECEIPT
   against the route positionally, and gives the VALUE only in the
   machine's own terms: `cOut` is
   `if chunkBad ... = 0 then (chunkRevAt wordScale (chunkAcc ...) iters).2 + 1 else 0`.
   What is NOT yet proved is that this equals the route's
   `fixedWidthNatTableMachineDecode`, i.e. that
   `(chunkRevAt scale (chunkAcc store segment scale start n) n).2
   = bitsToNatLE (w_0 ++ ... ++ w_(n-1))` when every `w_j` has exactly
   `wordSize` bits and `scale = 2 ^ wordSize`.  The mathematical content
   is a `bitsToNatLE_append` lemma plus the big-endian/little-endian round
   trip; the round trip is EXECUTED and passes on the witness (`:1909`,
   `cOut = 2`), so this is a proof obligation, not a suspected defect.
   The repo has NO `bitsToNatLE_append` -- a grep of
   `RMQ/Core/SuccinctSpace/*.lean` found only `TablesRAM.lean:18`
   (`bitsToNatLE_eq`) and `WordStore.lean:53`
   (`bitsToNatLE_natToBitsLE_of_lt`) -- so it must be proved, and the
   per-chunk width fact (`each stored chunk is exactly wordSize bits`)
   must be sourced from the `BoundedPayloadWordStore` side.
2. THE SUMMARY GROUP `S`: four atomic reads at
   `baseline (block / blocksPerSuper)`, `minRel block`, `maxRel block`,
   `argOffset block`, in that order, then the four-way `match` into
   `Option (Nat x Nat x Nat x Nat)` and `bpRelativeSummaryMinCandidate`
   (`InteriorDirectory.lean:2277`, `:2300`).  Between reads the caller
   must stage the output into a holding register and reset `iIdx`; `iIdx`
   is read-only within both the atom and this fold, so only the caller
   writes it.
3. THE SPAN BLOCKS: `o`/`b` read plus option dispatch into the summary
   group (`:2311`, `:2329`).  The `none` arm emits NOTHING -- the block
   must branch PAST the summary group, not run it and discard.
4. THE TWO-SPAN BLOCKS: level read, then constant-divisor `div`/`mod` by
   `bpSparseLevelDomain`, then two span blocks and `bpCandidateMerge?`
   (`:2351`, `:2376`).  THE LEVEL READ IS THE UNCONDITIONAL HEAD of every
   two-span append chain (M3d-11 section 4); a positional or membership
   lemma assuming otherwise presents as a HEARTBEAT TIMEOUT, not a type
   error, and raising `maxHeartbeats` would produce a theorem about the
   wrong machine.
5. THE FIVE-BRANCH DISPATCH (`:2444`) and then `hInterior` in
   `crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean:1143`), whose
   four preservation obligations (`fClose`, `fRight`, `mLV`, `mLP`) are
   all outside both interior banks by construction.
6. Only then: the whole-query glue via `E1RouteDecomposition`, the derived
   all-size literal, the amended target Prop with its
   obstruction-supersession note, the validator's phase 5, and the doc
   rows.  All remain out of scope and all are downstream of item 5.

WHICH BLOCK TO CALL FROM ITEMS 2-4, AND WHY THE CHOICE IS STILL OPEN.
Both interior read blocks now exist and they are NOT interchangeable.
`E1InteriorReadBlock.interiorReadNat` is 7 instructions and assumes
`width <= wordSize`; `E1InteriorChunkFold.interiorChunkFold` is 37 and
assumes only `0 < chunkCount` and `chunkCount <= 8`.  M3d-11 section 7
item 1 asked for a deliberate choice between ONE block carrying the cap
everywhere (simpler layout, eight-step cost everywhere) and TWO with a
per-shape generator choice (tighter).  THAT CHOICE IS STILL OPEN and
should be made BEFORE item 2 is written, because it fixes the program
layout the whole interior inherits and the layout is what the single
consolidated program-layout DD is supposed to record.  Check a per-shape
generator branch against INV-ALL-SIZE before committing to it: a generator
that branches on a shape predicate is exactly what that invariant exists
to police.

### 8. THE `Nat.log2` SCOPE PRECISION -- CHECKED, AND THE INHERITED CITATION DOES NOT HOLD

M3d-12 was directed to extend `docs/PAPER_MODEL_ADEQUACY.md` with a scope
precision supplied as coordinator-verified: that uncharged runtime
`Nat.log2` still exists in trace-producing code reachable from the
`OfSizeGe` sibling family at `SuccinctFinalRAM.lean:4486` (guarded by
`2 ^ 128 <= shape.size`) and in the `...WithStoreLegacy` mirror, that those
appear ONLY at `RMQ/Headlines/RMQCompatibility.lean:133,137`, and nowhere
in `RMQPaper.lean`, `Headlines/RMQ.lean`, `WHAT_IS_PROVED.md`, or
`artifact/CLAIMS.md`.

THE DOC WAS NOT EXTENDED, because the citation does not survive checking
and `PAPER_MODEL_ADEQUACY.md` is public-facing. What was actually found, at
this HEAD:

* `SuccinctFinalRAM.lean:4486` IS
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe` and
  IS guarded by `2 ^ 128 <= shape.size`. That half is right.
* THAT DEF CONTAINS NO `Nat.log2`. `grep -n "Nat.log2"
  RMQ/Core/SuccinctFinalRAM.lean` returns exactly two hits: `:4561` and
  `:5970`. `:5970` is a comment. `:4561` is
  `concreteBPNativeTraceEventBitWidth`, a DECLARED REVIEWER WIDTH computed
  from a finished trace, whose own docstring says "This is a trace-local
  bound, not an asymptotic machine-word theorem". It is a width
  declaration consumed by width certificates, not a runtime computation
  inside an executed definition -- which is the opposite of the thing the
  precision was meant to flag.
* `RMQ/Headlines/RMQCompatibility.lean` contains NO `Nat.log2` at all
  (`grep -rn "Nat.log2" RMQ/Headlines/` is empty). What `:133` and `:137`
  actually reference is the `OfSizeGe` family --
  `..._execution_story` and `..._bounded_execution_story` -- so the
  FAMILY-reachability half of the claim is right and the
  `Nat.log2`-location half is a conflation of the two.
* `docs/WHAT_IS_PROVED.md` DOES contain `Nat.log2`, at `:542`, so "nowhere
  in `WHAT_IS_PROVED.md`" is false as stated. The occurrence is the ambient
  rank/select word size `Nat.log2 bits.length + 1` in a space-budget
  passage, not an executed-route computation.
* Repository-wide, `grep -rn "Nat.log2" RMQ/ --include=*.lean` returns 883
  hits, overwhelmingly in space-budget and spec-side code.

WHAT SURVIVES, AND SHOULD STILL BE SAID. The UNDERLYING point stands and is
worth writing into `PAPER_MODEL_ADEQUACY.md`: "no uncharged size-dependent
computation on the ACCEPTED ROUTE" is true and provable, while "nowhere in
the repository" is false, and a reviewer who greps `Nat.log2` finds
hundreds of hits in minutes. What must NOT be shipped is the specific
citation above, because a reviewer who follows it to
`SuccinctFinalRAM.lean:4486` or to `RMQCompatibility.lean:133` finds no
`Nat.log2` there and concludes the adequacy doc is careless.

RECOMMENDED NEXT STEP, for the coordinator rather than for a worker: decide
whether the intended referent was (a) the reviewer-width declaration at
`:4561`, (b) a genuine runtime `Nat.log2` somewhere in the `OfSizeGe` or
`...WithStoreLegacy` chain that this session did not locate, or (c) the
`bpSparseLogSpan` site B7 discharged, mis-remembered. The doc row should be
written only after that is settled, and item 8 is in any case downstream of
M3d-13 items 2-5, none of which are built.

## M3d-13 (worker E1-R4v): the chunk fold's value bridge, and the preservation clause item 2 turned out to need

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`63591cc` (M3d-12's yield) to `255ef61`.  Two commits, both green.

M3d-12's resume item 1 -- THE VALUE BRIDGE -- IS BUILT.  Items 2-6 are
NOT.  Item 2 was started, and starting it surfaced a blocker that had to
be fixed first; that fix is the second commit and is section 3.

The coordinator's ruling on the open block decision is recorded and
followed: compose the interior on the 37-instruction FOLD
(`E1InteriorChunkFold.lean`), uniformly across all five branches, NOT on
the 7-instruction atom.  M3d-12 section 7's "THAT CHOICE IS STILL OPEN"
is therefore CLOSED; nothing below relitigates it.

### 1. WHAT LANDED (commit `f6573ca`)

New module `RMQ/Core/WordRAM/E1InteriorChunkValue.lean` (627 lines),
imported from `RMQ.lean:42`.  No new registers, no new instructions: this
is arithmetic content only, relating numbers the fold already computes to
numbers the route already computes.

* `chunkFoldValue_eq_route_decode:310` -- THE HEADLINE.  The machine's
  option-shifted cell equals
  `RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode`
  (`MachineChunkedTable.lean:215`), THE ROUTE'S OWN DECODE, applied to the
  words read at the route's own addresses.  Both sides are computed from
  `store.readWord?` at the SAME addresses, so this is a statement about
  the arithmetic; the addressing is `chunkEventsAt_eq_route`.
* `interiorChunkFold_cOut_eq_routeDecode:491` -- the same fact in the
  shape a consumer needs: its left-hand side is verbatim the `cOut`
  clause of `interiorChunkFold_runsTo`, at the fold's own machine-computed
  `chunkStart`/`chunkIters`.  A consumer of the simulation theorem may
  rewrite with this and be left with a statement purely about the route.
* `bitsToNatLE_append:84` -- THE LEMMA THE REPOSITORY DID NOT HAVE.
  M3d-12 recorded that a search of `RMQ/Core/SuccinctSpace/` found only
  `TablesRAM.lean:18` and `WordStore.lean:53`.  That was re-checked and is
  correct.  See DD-20260719-008 for why it is proved in the new module
  rather than added to `WordStore.lean`.
* `bitsToNatLE_lt_two_pow:106`, `chunkDigit_lt:437` -- what makes each
  chunk a legitimate base-`2 ^ wordSize` digit, hence the reversal exact
  rather than lossy.  A missing chunk qualifies for free: the option shift
  sends it to the truncated `0 - 1 = 0`.
* `chunkRevGen:199`, `chunkRevGen_succ_front:222`,
  `chunkRevGen_chunkAcc:239`, `chunkRevAt_eq_gen:207` -- the reversal,
  generalised.  See section 2.
* `chunkLit:129` with `chunkLit_succ_front:137`, and
  `chunkBad_succ_front:166` -- the end-swapping lemmas.  See section 2.
* `chunkRevAt_chunkAcc_eq_chunkLit:463` -- the reversal produces the
  route's little-endian value.

### 2. THE TWO STRUCTURAL FACTS THAT SHAPED THE PROOF

BOTH ARE DIRECTION MISMATCHES, and each needed its own conversion lemma.
Neither is bookkeeping: without them the inductions do not close.

First, `chunkRevAt` (`E1InteriorChunkFold.lean:1099`) peels a base-`scale`
digit off the BOTTOM of the accumulator, while `chunkAcc` (`:656`) builds
one ONTO the bottom.  The two recursions run in opposite directions, so no
induction on `chunkRevAt` alone lines them up.  `chunkRevGen` exposes the
running little-endian result as a parameter and `chunkRevGen_succ_front`
proves a step may be taken at the FRONT instead of at the end; that single
identity collapses the mismatch to one induction.  `chunkRevAt_eq_gen`
keeps the original definition authoritative -- the generalisation is a
proof device, not a redefinition of what the machine computes.

Second, the route's address list `consecutiveWordIndices` is HEAD-first
while `chunkAcc` and `chunkBad` are LAST-first, so `chunkLit_succ_front`
and `chunkBad_succ_front` convert.  Same class of mismatch, one level up.

### 3. WHAT ITEM 2 TURNED OUT TO NEED (commit `255ef61`)

STRENGTHENING ONLY.  A conjunct was added to two conclusions; nothing was
weakened, nothing renamed, no hypothesis added.

`interiorChunkFold_runsTo` could not be composed more than once in a
single program.  It concluded only about `cOut`, so nothing said that a
second fold leaves the first fold's staged result -- or the caller's own
block index -- alone.  The summary group of item 2 stages four fold
results into holding registers and must reset `iIdx` between reads, so it
needs exactly that.

The ingredients already existed and were being discarded:
`interiorChunkInit_runsTo` (`:1498`) and both loop theorems each carried
the preservation clause, and the headline's proof was binding them as
`_h1Pres`, `_h2Pres`, `_h3Pres` -- underscore-prefixed, i.e. deliberately
unused.  What was MISSING was the fourth:
`interiorChunkEpilogue_runsTo` had no such clause.

`interiorChunkEpilogue_runsTo:1672` now carries it (`:1682`).  The
obligation is discharged from the bank arithmetic: the epilogue writes
only `cOut`, which is `99`, inside the bank `89 .. 99`, so
`ChunkFoldUntouched r` gives `r` distinct from `cOut` directly.
`interiorChunkFold_runsTo:1794` then chains all four (`:1821`).

RECORDED BECAUSE IT GENERALISES: a block simulation theorem that concludes
only about its OUTPUT register is not composable, and the defect does not
show up until a second instance of the same block appears in one program.
The fringe and same-block arms did not surface it because each appears
once.  The interior is the first place a block is instantiated four times.
Items 2 and 3 of the new resume point will instantiate the summary group
and the span blocks repeatedly, so the same question should be asked of
every block written from here on: does its headline say what it LEAVES
ALONE, not only what it computes?

### 4. THE BRIDGE IS NOT VACUOUS, AND THAT IS CHECKED BY EXECUTION

`interiorChunkFold_cOut_eq_routeDecode` carries a per-chunk width premise.
A theorem whose premises no store satisfies proves nothing, so the premise
is discharged concretely:

* `witnessWidth_cell0:579` discharges it on
  `E1InteriorChunkFold.witnessStore`, whose chunks are one bit wide, so
  `wordSize = 1` and the fold's `wordScale = 2` is `2 ^ 1`.
* `witnessCOut_cell0_via_bridge:612` then DERIVES the machine's cell
  through the bridge -- rewriting the `cOut` expression into the route's
  decode and letting the kernel evaluate -- landing on `2`.  That is the
  same `2` that `chunkFoldWitness_path_bothPresent`
  (`E1InteriorChunkFold.lean:1918`) obtained independently by RUNNING the
  machine.  Neither number is asserted.
* `witnessRouteDecode_cell2:560` checks the `none` side: the wholly
  missing cell decodes to `none`, matching the machine's `cOut = 0`.  A
  value-only check has no power over that arm, which is why it is proved
  rather than assumed.

The width premise is NOT discharged in general.  It is sourced on the
`BoundedPayloadWordStore` side and is owed where the fold is composed
against `canonicalRelativeRmmInteriorComponentStore`.  Stating it
explicitly is what keeps that debt visible; see DD-20260719-008.

### 5. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0:

    [251/253] Built RMQ.Core.WordRAM.E1InteriorChunkValue
    [252/253] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

`lake build rmq_e1_machine_validate` exit 0; `lake exe
rmq_e1_machine_validate` exit 0:

    RESULT: PASS (with the whole-query comparison still OPEN)
    VALEXE_EXIT=0

`lake env lean scripts/headline_axiom_check.lean` exit 0.
`design_decision_check.ps1 -Strict -Base d90b062...`: `DESIGN-CHECK:
checked 71 changed files`.
`claim_drift_scan.ps1`: `scan complete (741 hits, 0 strict failures)`,
exit 0.
`paper_topology_lint.ps1`: `PAPER-TOPOLOGY PASS (83 broad documentary
identifiers; 49 paper identifiers resolved)`, exit 0.
`git diff --check` clean; `git diff --check d90b062..HEAD` flags
whitespace SOLELY in `docs/internal/B7_STEP2_WIP.patch`, as inherited.
Hygiene `rg` over the two touched modules: no forbidden tokens, no
`import Mathlib`.  `rg native_decide|Lean.ofReduceBool RMQ RMQExamples`:
no hits.  (The prose word "partial" was reworded out of the new module so
a naive grep stays quiet.)

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkValue` DIRECTLY:

    bitsToNatLE_append                    [propext, Quot.sound]
    bitsToNatLE_lt_two_pow                [propext, Quot.sound]
    chunkLit_succ_front                   [propext, Quot.sound]
    chunkBad_succ_front                   [propext, Quot.sound]
    chunkRevAt_eq_gen                     does not depend on any axioms
    chunkRevGen_succ_front                does not depend on any axioms
    chunkRevGen_chunkAcc                  [propext, Quot.sound]
    chunkFoldValue_eq_route_decode        [propext, Classical.choice, Quot.sound]
    chunkDigit_lt                         [propext, Quot.sound]
    chunkRevAt_chunkAcc_eq_chunkLit       [propext, Quot.sound]
    interiorChunkFold_cOut_eq_routeDecode [propext, Classical.choice, Quot.sound]
    witnessRouteDecode_cell0              does not depend on any axioms
    witnessCOut_agrees_routeDecode_cell0  does not depend on any axioms
    witnessRouteDecode_cell2              does not depend on any axioms

and importing `RMQ.Core.WordRAM.E1InteriorChunkFold` DIRECTLY, to confirm
the strengthening changed nothing:

    interiorChunkFold_runsTo              [propext, Classical.choice, Quot.sound]
    interiorChunkEpilogue_runsTo          [propext, Quot.sound]

Never `sorryAx`.

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  Closure was impossible by construction, for the reason M3d-11 and
M3d-12 both recorded: every row is whole-query scoped and the whole-query
composition is downstream of the interior simulation.

Component-level evidence added: REQ-E1-03 (the interior fold's VALUE is
now tied to the route's own decode, not only its receipt -- the first
value-side interior evidence in the matrix); REQ-E1-01 (the fold's
headline now states what it LEAVES ALONE, which is what makes the block
composable); REQ-E1-05 (`witnessRouteDecode_cell2`, the `none` arm checked
by execution on the route side).

### 7. RESUME POINT (M3d-14)

NOTHING below is implemented.  All file:line verified at HEAD `255ef61`.

0. STANDING, AND NEWLY LEARNED: every block written from here on must
   state a preservation clause in its HEADLINE, not only in its internal
   segment lemmas.  Section 3 records what it costs to discover this late.
   The predicate is `ChunkFoldUntouched` (`E1InteriorChunkFold.lean:928`).

1. THE SUMMARY GROUP `S`
   (`InteriorDirectory.lean:2277` `canonicalRelativeRmmMachineSummaryComputation`,
   `:2300` `canonicalRelativeRmmMachineMinCandidateComputation`).  Four
   reads, in this order: `baseline (block / blocksPerSuper)`,
   `minRel block`, `maxRel block`, `argOffset block`, then the four-way
   `match` into an optional quadruple, then
   `bpRelativeSummaryMinCandidate` (`RelativeSummaryCandidate.lean:15`).
   Design facts established this session and NOT yet implemented:
   * All four reads are `canonicalRelativeRmmMachineReadNatComputation`
     (`InteriorDirectory.lean:2132`), which is
     `table.machineReadComputationAt (machineWordBits shape.bpCode.length)
     base deadAddress i` -- exactly what `interiorChunkFold` simulates, so
     all four are fold instances with different program constants.  They
     SHARE `deadAddress` and `wordSize`; they differ in `base`,
     `entriesLen`, `chunkCount`.  Offsets are
     `canonicalRelativeRmmInteriorComponentOffsets` (`:1614`): `baseline`
     is `0`, `minRel`/`maxRel`/`argOffset` are running sums of the
     preceding tables' word counts.
   * `bpRelativeSummaryMinCandidate` is
     `(baseline + minRel - bpSuperblockSpan blockSize blocksPerSuper,
     blockStartOf blockSize block + argOffset)`.  The superblock span is a
     per-shape constant.  CONFIRM `blockStartOf`'s definition at source
     before relying on a `mulConst` shape for it -- it was read as a
     scaling by `blockSize` but NOT verified at source this session.
   * `maxRel` IS READ AND IS NOT USED by the candidate: only `baseline`,
     `minRel` and `argOffset` appear in `bpRelativeSummaryMinCandidate`'s
     body.  The read is nevertheless charged, because the ROUTE performs
     it (`:2290`).  A machine that skipped it would have a shorter receipt
     and would fail the positional receipt obligation.  Do not remove it.
   * The caller must reset `iIdx` (`85`) between reads.  `iIdx` is
     read-only inside both interior blocks, so only the caller writes it,
     and it survives each fold by the clause landed this session
     (`iIdx = 85` is below the fold's bank, so `ChunkFoldUntouched iIdx`).
   * Register bank: the fold owns `89 .. 99`; the summary group needs its
     own bank at `100` and above, and must claim a DD id.
2. THE SPAN BLOCKS: `o`/`b` read plus option dispatch into the summary
   group (`InteriorDirectory.lean:2311` local, `:2329` global).  The
   `none` arm emits NOTHING -- the block must branch PAST the summary
   group, not run it and discard.
3. THE TWO-SPAN BLOCKS (`:2351` local, `:2376` global): level read, then
   constant-divisor `div`/`mod` by `bpSparseLevelDomain`, then two span
   blocks and `bpCandidateMerge?`.  THE LEVEL READ IS THE UNCONDITIONAL
   HEAD of every two-span append chain; a positional or membership lemma
   assuming otherwise presents as a WHNF HEARTBEAT TIMEOUT, not a type
   error, and raising `maxHeartbeats` would produce a theorem about the
   wrong machine.
4. THE FIVE-BRANCH DISPATCH (`:2444`
   `canonicalRelativeRmmInteriorRangeMinComputation`): count zero gives
   pure none; count within the macro remainder gives the local two-span;
   then a zero middle-macro count gives adjacent macro (`:2400`); a zero
   right count gives left-middle (`:2413`); otherwise cross-macro
   (`:2426`).  Then discharge `hInterior` in
   `crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean:1143`), whose
   four preservation obligations (`fClose`, `fRight`, `mLV`, `mLP`) are
   outside both interior banks by construction.
5. Only then: the whole-query glue via `E1RouteDecomposition`, the derived
   all-size literal, the amended target Prop with its supersession note,
   the validator's whole-query phase, and the doc rows.  All downstream of
   item 4.

ALSO OWED, not on the critical path:
* THE WIDTH PREMISE.  `interiorChunkFold_cOut_eq_routeDecode` owes its
  per-chunk width hypothesis to whoever composes it against
  `canonicalRelativeRmmInteriorComponentStore`.  The fact is a
  `BoundedPayloadWordStore` property; it was NOT located this session and
  should be sourced BEFORE item 1 is composed, not after.
* AN EXECUTED PRESERVATION CHECK FOR THE INTERIOR FOLD.  The clause landed
  this session is proof-side only.  The validator's phase 3h already does
  sentinel-seeded preservation checking for the fringe arm, and records
  that THE SENTINEL SEEDING IS LOAD-BEARING (from a zero-seeded file the
  phase is vacuous, since a block that zeroes a register it does not own
  still "preserves" it).  The interior fold has no such phase.  Worth
  adding when the validator's interior phase is written, for the reason
  phase 3h exists: neither a value check nor a receipt check nor a step
  count has power over a block that scribbles on a register it does not
  own.

### 8. THE M7 DOC ROW, RE-CHECKED -- THE CORRECTED CITATION ALSO DOES NOT HOLD

M3d-12 section 8 refused a coordinator-supplied `Nat.log2` scope precision
because it did not survive checking.  A CORRECTED version was supplied to
this session, re-verified by the coordinator at source.  IT WAS CHECKED
AGAIN HERE AND IT ALSO DOES NOT HOLD.  The doc was again NOT extended.

What the corrected version asserted, and what was found at this HEAD:

* "Runtime `bpSparseLogSpan count` survives at `InteriorRAM.lean:574,
  622, 820, 868`" -- TRUE.  All four read `let span := bpSparseLogSpan
  count` or `let spanMacros := bpSparseLogSpan macroSpanCount`, and
  `bpSparseLogSpan` is `2 ^ Nat.log2 blockCount`
  (`SparseArgMin.lean:598`), a genuine runtime `Nat.log2` on a runtime
  argument.  The enclosing defs are the local and global
  `twoSpanCandidateTraceResult` / `...AtSegments` families
  (`InteriorRAM.lean:559`, `:606`, `:805`, `:852`).
* "`SuccinctFinalRAM.lean:4486` is the ENTRY POINT and itself contains no
  `Nat.log2`" -- TRUE.
* "Those [sites] are reachable from
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultOfSizeGe`,
  guarded by `2 ^ 128 <= shape.size`" -- FALSE, AND THIS IS THE HALF THE
  ROW WOULD REST ON.  `WholeQueryInstr.evalGlobalWordTraceOfSizeGe`
  (`SuccinctFinalRAM.lean:3718`) takes its size hypothesis as
  `(_hsize : 2 ^ 128 <= shape.size)` -- UNDERSCORE-PREFIXED AND UNUSED --
  and its `.lcaClose` arm (`:3732`) dispatches to
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`, the
  SAME interior leg the accepted route uses.  The size-premised family
  therefore reaches exactly the same interior as the accepted route and
  does NOT reach the four sites.  Verified directly at source this
  session, not inferred.
* "and from the `...WithStoreLegacy` mirror" -- NOT AS NAMED.  No
  `...WholeQueryGlobalWordTraceResultOfSizeGe...WithStoreLegacy` exists.
  There ARE `WithStoreLegacy` defs, but in
  `ConcreteDirectoryRAMStoreParam.lean` (`:3624`, `:4578`, `:5307`), a
  different family; that file does contain `bpSparseLogSpan` (6
  occurrences), so a store-parametric Legacy quarantine is real -- but it
  is not the object the row named.
* The delegation cited the accepted whole-query trace as
  `SuccinctFinalRAM.lean:4337`.  At this HEAD `:4337` is a comment line;
  `def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` is at
  `:4426`.  The FROZEN MATRIX carries the same stale `:4337`
  (`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md:17`).  Flagged as a reference
  correction for coordinator adjudication; NOT applied to the frozen text.

WHAT DOES SURVIVE, AND IS WORTH WRITING once a coordinator settles it.
The sentence "no uncharged size-dependent computation on the ACCEPTED
ROUTE" is TRUE and supportable.  The accepted route
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` (`:4426`)
reaches its interior through `...AllSizeStructural`
(`ConcreteDirectoryRAM.lean:1188`), which calls
`canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment` (`:1113`), a
flat-store replay that never mentions `bpSparseLogSpan`.  The four sites
are reached only through `...AtSegmentsAllSizeStructuralLegacy`
(`ConcreteDirectoryRAM.lean:1196`), whose consumers are theorem
statements and `unfold`s, not executed defs.

SO THE CORRECT CONTRAST IS `AllSizeStructural` vs
`AllSizeStructuralLegacy` -- THE SAME LEGACY/NON-LEGACY DISTINCTION the
coordinator already established for
`boundedSummaryRangeScanTraceResultAtSegments` -- AND NOT the `OfSizeGe`
sibling, which is not a counterexample family at all.  A reviewer who
follows the `OfSizeGe` citation finds `_hsize` unused and concludes the
adequacy doc is careless, which is the exact failure mode M3d-12 refused
to ship.

RECOMMENDED NEXT STEP, for the coordinator rather than a worker: approve
the `AllSizeStructural` vs `AllSizeStructuralLegacy` wording, and decide
separately whether the store-parametric `WithStoreLegacy` family in
`ConcreteDirectoryRAMStoreParam.lean` needs its own sentence.  The row is
in any case downstream of M3d-14 items 1-4, none of which are built.

Also noted, not acted on: `B7_WORKLOG.md:1495` states that `Nat.log2` and
`bpSparseLogSpan` no longer occur in "the four bodies".  That is not true
of `InteriorRAM.lean:574/622/820/868`, which still contain live
`bpSparseLogSpan`.  It presumably refers to different bodies.  This does
not affect the doc sentence, because those bodies are off-route, but the
worklog line is inaccurate as written and a future reader may be misled.

## M3d-14 (worker E1-R4w): the width premise was unsatisfiable, and settling it first is what caught that

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`1766727` (M3d-13's yield) to `3ea0528`.  One commit, green.

M3d-13's resume point listed two things "ALSO OWED, not on the critical
path", to be settled BEFORE composing the summary group rather than
discovered mid-proof.  That instruction earned its keep.  One of the two
-- the width premise -- turned out not to be a lookup but a defect, and
the composition it was blocking could never have closed as planned.
NONE of resume items 1-5 are built.  This session is the repair plus the
two verification answers.

### 1. `blockStartOf`, CONFIRMED AT SOURCE (the cheap half)

`RMQ/Core/SuccinctClose/BlockLocal.lean:868`:

    /-- First BP position in a block. -/
    def blockStartOf (blockSize block : Nat) : Nat :=
      block * blockSize

M3d-13 read this as a scaling by `blockSize` but flagged it unverified.
The read is CORRECT, and the argument order is the favourable one: the
runtime quantity is `block` and the multiplier `blockSize` is the
per-shape constant, so a `mulConst` shape against the register holding
`block` is sound.  Nothing further is owed here.

### 2. THE WIDTH PREMISE WAS NOT UNPROVED -- IT WAS FALSE

M3d-13 recorded the premise of `interiorChunkFold_cOut_eq_routeDecode` as
a debt "sourced on the `BoundedPayloadWordStore` side".  It cannot be.
The premise demanded `w.length = wordSize` of EVERY chunk; the store side
supplies only `word_length_le`, an INEQUALITY (`WordStore.lean:552`), and
that is not a gap in the library but a fact about the construction:

* `fixedWidthNatTableMachineWords` (`MachineChunkedTable.lean:15`) is a
  bare `flatMap (chunkPayloadWords wordSize)`.  There is NO padding
  anywhere on the path to the interior store.
* `chunkPayloadWords` (`WordStore.lean:154`) is documented, in the
  repository's own words, "The final word may be shorter."
* The widths are genuinely different quantities.  `superWidth _ shape`
  (`RelativeSummary.lean:1290`) IS `machineWordBits shape.bpCode.length`,
  i.e. `wordSize`.  But `offsetWidth` (`:1299`) is
  `machineWordBits layout.macroSize` and `blockAddressWidth` (`:1308`) is
  `machineWordBits layout.blockCount`, both applying a monotone function
  to strictly smaller arguments.  Seven of the interior component store's
  eight tables are strictly narrower than `wordSize`.

So the bridge was VACUOUS at
`canonicalRelativeRmmInteriorComponentStore`, the one store the interior
composition needs it against.  Composing the summary group on it would
have produced a chain of theorems resting on a hypothesis no one could
ever discharge -- the exact "decorative hypothesis that silently owes
itself to every consumer" failure the standards name.

### 3. THE REPAIR: THE PREMISE WAS OVER-DEMANDING BY ONE INDEX

Exactness is consumed at exactly ONE place.  `bitsToNatLE_append` yields
`2 ^ w.length * bitsToNatLE tail`, and the old hypothesis was used only
to rewrite `2 ^ w.length` into the fold's uniform digit weight
`2 ^ wordSize`.  For the LAST chunk `tail` is empty, that term is
`2 ^ w.length * 0`, and the width does not matter.  Hence:

* `chunkFoldValue_eq_route_decode:311` -- equality only at `j + 1 < n`.
  The induction's `succ` case now derives the head's exactness only when
  `n > 0`, via a `by_cases` on `n = 0` inside a new `hmul` step; the
  `n = 0` branch closes from `chunkLit ... 0 = 0` without any width fact.
* `chunkDigit_lt:451` and `chunkRevAt_chunkAcc_eq_chunkLit:480` -- only
  `w.length <= wordSize`.  The digit bound wants
  `2 ^ w.length <= 2 ^ wordSize` (`Nat.pow_le_pow_right`), never equality.
* `interiorChunkFold_cOut_eq_routeDecode:498` -- carries BOTH, split:
  `hle` (bound, every chunk) and `hexact` (equality, non-final chunks).

STRENGTHENING ONLY: premises weakened, conclusions untouched, nothing
renamed or deleted.  There are no external consumers -- all four
theorems are local to `E1InteriorChunkValue.lean` -- so the repair is
contained.  See DD-20260719-009 (claimed this session; the maximum
OBSERVED was `DD-20260719-008`).

WHY THE MACHINE SIDE HAD TO MOVE AND NOT THE STORE.  The route imposes no
width discipline at all: `fixedWidthNatTableMachineDecode`
(`MachineChunkedTable.lean:215`) is `(collectPayloadWords words).map
bitsToNatLE`, plain concatenation.  It MUST NOT impose one, because the
store's `erases` obligation says the chunks flatten back to the exact
`width`-bit payload -- padding chunks up to `wordSize` would BREAK
`erases`.  Raggedness is designed, not accidental.

BOTH HALVES NOW DISCHARGE AT THE TARGET STORE, which is the whole point:
`hle` is verbatim the store's own `word_length_le` field, and `hexact` is
VACUOUS there, the interior tables being single-chunk --
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`) derives `chunkCount <= 1` from
`width <= machineWordBits shape.bpCode.length`, note the inequality.

### 4. ANTI-VACUITY RE-CHECKED, NOT ASSUMED

A repair that makes a premise easier to satisfy invites the suspicion
that it made it trivially satisfiable.  It did not.  The witness fixture
is a genuine TWO-chunk case (`chunkIters 3 2 0 = 2`), so `hexact` is
still exercised non-vacuously at `j = 0`, and
`witnessCOut_cell0_via_bridge:641` still DERIVES the machine's cell
through the bridge -- rewriting `cOut` into the route's decode and
letting the kernel evaluate -- onto the same `2` that
`chunkFoldWitness_path_bothPresent` (`E1InteriorChunkFold.lean:1918`)
obtains independently by RUNNING the machine.  Neither number is
asserted.

### 5. QUESTION (a), THE M7 DOC ROW: THE CORE CONTRAST HOLDS, TWO SUPPORTING CLAIMS DO NOT

The row was again NOT written.  Unlike M3d-12 and M3d-13, this is not a
flat refusal: the contrast the coordinator asked about DOES hold.  Two
of the sentences that would surround it do not, and one of those is a
fact the coordinator has not yet seen.

CONFIRMED at source this session:

* The four runtime `bpSparseLogSpan` sites survive at
  `InteriorRAM.lean:574, 622, 820, 868`.  Their enclosing defs -- the
  families the row should NAME -- are
  `PayloadLiveBPLocalSparseOffsetTable.twoSpanCandidateTraceResult`
  (`:559`) and `...AtSegments` (`:606`), and
  `PayloadLiveBPGlobalSparseBlockTable.twoSpanCandidateTraceResult`
  (`:805`) and `...AtSegments` (`:852`).  Note the short names are
  DUPLICATED across the two namespaces; any doc text must qualify them.
* `ConcreteDirectoryRAM.lean:1188` is
  `concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural`
  and `:1196` the `...Legacy` twin.  The non-Legacy `:1188` does NOT
  reach the four sites; it routes through
  `canonicalRelativeRmmInteriorRangeMinComputation`
  (`InteriorDirectory.lean:2444`), and `InteriorDirectory.lean` contains
  ZERO occurrences of `bpSparseLogSpan`.  The Legacy `:1196` DOES reach
  all four.  THE CONTRAST IS REAL.
* The accepted route
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`
  (`SuccinctFinalRAM.lean:4426`) reaches its interior via `:1188`.

WHAT DOES NOT HOLD, and would have shipped as an overstatement:

* "The Legacy family's consumers are theorem statements and unfolds, not
  executed defs" is FALSE as a statement about the family.  It is true of
  `:1196` itself -- all ten of its references sit inside theorems.  But
  the `...OfReady` layer beneath it IS consumed by executed defs:
  `concreteBPRelativeRmmInteriorRangeMinTraceResultOfSizeGe`
  (`ConcreteDirectoryRAM.lean:398`), `...AtSegmentsOfSizeGe` (`:495`),
  `crossBlockCloseTraceResultWithRankSeedOfReady` (`:1920`),
  `...AtSegmentsOfReady` (`:2051`), `lcaCloseTraceResultWithRankSeedOfReady`
  (`:3591`), `...AtSegmentsOfReady` (`:3700`).  These are genuine `def`s
  that transitively execute the four sites.  THE DEFENSIBLE PREDICATE IS
  "NOT REACHABLE FROM THE ACCEPTED ROUTE", which is what was actually
  checked and does hold -- not a claim about what kind of syntax the
  consumers are.
* MORE IMPORTANTLY, AND NEW: the accepted route DOES reach
  `bpSparseLogSpan`, at STORE-CONSTRUCTION time.  The chain is
  `concreteBPNativeSuccinctRMQGlobalReadStore` ->
  `canonicalRelativeRmmInteriorComponentStore` ->
  `canonicalRelativeRmmInteriorLocalLevelTable`
  (`InteriorDirectory.lean:1462`) -> `bpSparseLevelTable` ->
  `bpSparseLevelEntries` -> `bpSparseLevelCell`, and
  `SparseLevelTable.lean:55` reads

      def bpSparseLevelCell (domain i : Nat) : Nat :=
        bpSparseLogSpan i + domain * Nat.log2 i

  VERIFIED DIRECTLY AT SOURCE.  A row asserting flatly that the accepted
  route never reaches `bpSparseLogSpan` is therefore FALSE, and a
  reviewer who follows the store-construction path breaks it in one step
  -- the precise failure mode M3d-12 refused to ship.  The defensible
  sentence must be scoped to QUERY time: the accepted route's only
  contact with `bpSparseLogSpan` is the PRECOMPUTED level table, and at
  query time the machine READS and DECODES that cell
  (`InteriorDirectory.lean:2364-2366`, `level := value / domain`,
  `span := value % domain`) and never calls `bpSparseLogSpan`.

* Also found, and relevant to any sentence about the store-parametric
  quarantine: `lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStoreLegacy`
  (`ConcreteDirectoryRAMStoreParam.lean:5307`) is MISNAMED relative to its
  body -- it dispatches to the NON-Legacy
  `crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
  and does not reach the sparse sites at all, while `:3624` does.  Any row
  treating "the `WithStoreLegacy` family" as one uniformly-wired unit is
  inaccurate.

RECOMMENDATION, unchanged in kind from M3d-13 but now with a concrete
sentence to approve.  This remains a coordinator decision, and the
wording it should approve is narrower than the one supplied:

  "On the accepted route, no size-dependent computation is performed
  uncharged AT QUERY TIME.  The route reaches its interior through
  `...AllSizeStructural` (`ConcreteDirectoryRAM.lean:1188`), which
  dispatches to `canonicalRelativeRmmInteriorRangeMinComputation`; that
  path contains no occurrence of `bpSparseLogSpan`.  The four surviving
  runtime `Nat.log2` sites (`InteriorRAM.lean:574, 622, 820, 868`, in
  `PayloadLiveBPLocalSparseOffsetTable`/`PayloadLiveBPGlobalSparseBlockTable`
  `.twoSpanCandidateTraceResult{,AtSegments}`) are reached only through
  `...AtSegmentsAllSizeStructuralLegacy` (`:1196`), which is not
  reachable from the accepted route.  `bpSparseLogSpan` does occur on the
  route's PREPROCESSING side, in `bpSparseLevelCell`
  (`SparseLevelTable.lean:55`), which builds the level table; at query
  time the machine reads and decodes that precomputed cell."

The `OfSizeGe` sibling is confirmed once more NOT to be a counterexample
family: `evalGlobalWordTraceOfSizeGe` (`SuccinctFinalRAM.lean:3718`) takes
`_hsize` UNUSED and dispatches `.lcaClose` to the same accepted leg.

### 6. QUESTION (b), THE FROZEN-ROW ANCHOR: THE CITATION IS STALE

CONFIRMED, and NOT edited -- anchor repair in a frozen row is a
coordinator decision, per the delegation.

`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md:17` cites the accepted
whole-query trace as `RMQ/Core/SuccinctFinalRAM.lean:4337`.  At this HEAD
`:4337` is a line inside a DOC COMMENT, and the comment belongs to a
DIFFERENT definition -- `concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted`,
which begins at `:4340`.  The intended object,
`def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`, is at
`:4426`.  The citation is therefore not merely off by a few lines; it
lands inside the documentation of a neighbouring def, which is the kind
of miss that reads as carelessness to a reviewer.  Note also the matrix
gives the path as `RMQ/Core/SuccinctFinalRAM.lean`, which IS correct at
this HEAD (the file is not under `RMQ/Core/SuccinctFinal/RAM/`).

### 7. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0:

    [275/277] Built RMQ.Core.WordRAM.E1InteriorChunkValue
    [276/277] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

`lake build rmq_e1_machine_validate` exit 0; `lake exe
rmq_e1_machine_validate` exit 0:

    presSentinelNonZero=true   (a zero-seeded file makes this phase vacuous)
    -- phase 5: whole-query comparison --
    RESULT: PASS (with the whole-query comparison still OPEN)
    VALEXE_EXIT=0

Phases 3/3b-3h and 4/4b-4g all present and passing, unchanged from
M3d-13; the whole-query phase remains OPEN because it is downstream of
resume items 1-5, none of which are built.

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkValue` DIRECTLY:

    chunkFoldValue_eq_route_decode        [propext, Classical.choice, Quot.sound]
    interiorChunkFold_cOut_eq_routeDecode [propext, Classical.choice, Quot.sound]
    chunkDigit_lt                         [propext, Quot.sound]
    chunkRevAt_chunkAcc_eq_chunkLit       [propext, Quot.sound]
    witnessWidth_cell0                    [propext, Quot.sound]
    witnessCOut_cell0_via_bridge          [propext, Classical.choice, Quot.sound]
    bitsToNatLE_append                    [propext, Quot.sound]

Never `sorryAx`.  `maxHeartbeats` was NOT raised anywhere.

### 8. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and
weakened none.  No frozen row text was edited.

Component-level evidence CHANGED, and honestly it is a subtraction as
much as an addition: REQ-E1-03's interior value evidence, recorded by
M3d-13, was resting on a theorem that was vacuous at the interior store.
It is now resting on one that is not.  The row is no better off than it
looked yesterday, but it is now as well off as it looked.

### 9. RESUME POINT (M3d-15)

M3d-13's resume items 1-5 stand UNCHANGED and unimplemented; that list
is still the plan and is not restated here.  All file:line below verified
at HEAD `3ea0528`.

What M3d-14 changes about it:

0. THE WIDTH PREMISE IS NO LONGER A BLOCKER, and item 1 may now be
   composed.  When the fold is instantiated against
   `canonicalRelativeRmmInteriorComponentStore`, discharge `hle` from
   `canonicalRelativeRmmInteriorComponentStore_words_bounded`
   (`InteriorDirectory.lean:1711`) and `hexact` VACUOUSLY from
   `chunkCount <= 1` via
   `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
   (`InteriorDirectory.lean:4060`).  Both were located this session; the
   second was not previously recorded.

1. STANDING, AND NEWLY LEARNED, alongside M3d-13's preservation rule: a
   hypothesis stated as a visible debt must name the concrete object it
   is owed against AND be checked satisfiable there AT THE TIME IT IS
   STATED.  Unproved and unsatisfiable look identical at the definition
   site.  This one survived a full session and a coordinator review
   before anyone tried to discharge it.

2. THE ANALOGOUS QUESTION IS OWED OF THE `<= 8` CAP.  `hcap : chunkCount
   <= 8` is the fold's other carried hypothesis.  It was NOT audited this
   session.  Given that the interior is single-chunk, it is presumably
   satisfiable with room to spare -- but "presumably" is exactly what was
   said about the width premise.  Check it at source before composing,
   not after.

3. `blockStartOf` is settled (section 1); no further verification owed.

4. THE M7 DOC ROW has an approvable sentence drafted at section 5.  It
   needs a coordinator decision, not a worker's.  The store-construction
   carve-out is NOT optional -- without it the row is false.

5. THE FROZEN-ROW ANCHOR (`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md:17`,
   `:4337` -> `:4426`) awaits coordinator adjudication (section 6).

6. STILL OWED, carried unchanged from M3d-13: an EXECUTED preservation
   check for the interior fold.  The clause is proof-side only; the
   validator has no interior analogue of phase 3h, and phase 3h's own
   note records that sentinel seeding is load-bearing.

## M3d-15 (worker E1-R4x): the cap audit passed, and it turned up a false vacuity one rung down

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`e90c5d6` (M3d-14's yield) to this commit.  Green.

TASK ZERO was the whole session and it earned that.  M3d-13's resume items
1-5 remain UNBUILT; nothing was composed on the fold, because the audit
that had to precede composition produced a second finding of the same
family as M3d-14's and it needed settling first.

### 1. THE CAP IS SATISFIABLE -- BUT NOT BY THE ROUTE THAT WAS EXPECTED

`hcap : chunkCount <= 8` DISCHARGES at
`canonicalRelativeRmmInteriorComponentStore`, for ALL EIGHT tables,
UNCONDITIONALLY in `shape`.  So does the fold's other carried hypothesis
`hccPos : 0 < chunkCount`, which was audited alongside it: a cap that held
only because the count were always zero would settle nothing, and checking
one without the other is not an audit.

Both are landed as executable Lean, twelve theorems, in the new module
`RMQ/Core/WordRAM/E1InteriorChunkCap.lean` -- so the composition cites a
proof, not a note.  This is the form the standing rule asks for.

THE EXPECTED ROUTE DOES NOT WORK.  The delegation named `chunkCount <= 1`
via `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`), with `interiorChunkCount_le_eight` as the
general fallback.  It is the fallback that is the only route:

* WRONG SHAPE.  `cost_le_one` concludes `(...).cost <= 1`, about the
  route's COST.  `hcap` is about `fixedWidthNatTableMachineChunkCount`.
* HYPOTHESIS UNAVAILABLE.  `cost_le_one` needs
  `width <= machineWordBits shape.bpCode.length`.  For `minRelTable`,
  `maxRelTable` and `argOffsetTable` that is NOT unconditional.  The only
  `relativeWidth` bounds against one word are
  `..._lt_two_machine_of_size_ge_four` (`:3970`) and
  `..._le_machine_of_macroSize_lt_blockCount` (`:4104`).  The
  unconditional bound is `..._le_seven_machine` (`:3855`), against SEVEN.
* AND IT IS FALSE at reachable shapes (section 2).

The five `_le_seven_machine` lemmas (`:3855`, `:3875`, `:3899`, `:4240`,
`:4257`) are hypothesis-free apart from the shape; with the `superWidth`
case they cover all eight tables, and `interiorChunkCount_le_eight` wants
exactly `width <= 7 * wordSize` with no positivity side condition.
Positivity is equally unconditional: every width is `machineWordBits _`,
`2 * _ + 3`, or `Nat.log2 _ + 1`.

This independently corroborates the standing instruction to compose on the
FOLD and not the 7-instruction atom.  The atom's `width <= wordSize`
obligation is precisely the conditional one.

### 2. THE INTERIOR IS NOT SINGLE-CHUNK, AND DD-20260719-009's VACUITY CLAIM DOES NOT HOLD

`machineWordBits n = Nat.log2 n + 1` (`SuccinctRank.lean:38`), so the chunk
counts are COMPUTABLE and there was no need to reason about them.
Evaluating `(size, wordSize, relativeWidth, chunkCount)`:

    (1, 2, 5, 3)   (2, 3, 7, 3)   (4, 4, 7, 2)   (8, 5, 9, 2)
    (16, 6, 9, 2)  (64, 8, 9, 2)  (256, 10, 11, 2)
    (1024, 12, 11, 1)  (4096, 14, 11, 1)  (65536, 18, 13, 1)

Every `shape.size` below roughly `1024` is MULTI-chunk; the smallest are
three-chunk.  Single-chunkness arrives only asymptotically, as
`2 * log2 (log2 size)` falls behind `log2 (2 * size)`.

Two consequences.

FIRST, the cap is not trivial -- `chunkCount` really exceeds one at
reachable shapes -- and the `<= 1` route was worth rejecting on more than
shape grounds, since at `size = 4` it is simply false.

SECOND, AND THIS IS THE FINDING.  DD-20260719-009 discharged the value
bridge's exactness premise at this store by declaring it "VACUOUS there,
because the interior tables are single-chunk", citing `cost_le_one`.  M3d-14
section 2 and resume item 0 say the same.  IT IS NOT VACUOUS.  For
`shape.size < 1024`, `hexact` is a LIVE obligation, at exactly the small
shapes an all-size claim must cover.

Nothing is retracted.  DD-009's CUT -- exactness demanded only of non-final
chunks -- is correct and untouched, and the premise is still satisfiable.
What changes is how it must be discharged: substantively, from
`chunkPayloadWords`'s own structure, which emits chunks of length exactly
`wordSize` except possibly the last.
`chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`) presents the
chunk at index `k` as a `take wordSize` of a `drop`, which is full whenever
a later chunk exists.  Whoever composes the value bridge must use THAT and
must not cite vacuity.  Recorded as DD-20260719-010 (claimed this session;
the maximum OBSERVED was `DD-20260719-009`).

WHY TWO AUDITS FOUND TWO DEFECTS IN THE SAME PLACE.  Satisfiability and
vacuity are the same question from opposite ends.  M3d-14 asked whether a
premise could ever be met and found one that could not.  This session asked
whether a premise was ever exercised and found one believed dead that is
alive.  A `<=` bound answers neither: it says nothing about whether the
quantity is ever large.  The fastest way to settle it was to EVALUATE the
count, which took one `#eval` after a week of prose about it.

### 3. THE FROZEN-ROW ANCHOR: NOTED, NOT EDITED

Reconfirmed independently at this HEAD.
`E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` cites the accepted whole-query
trace as `RMQ/Core/SuccinctFinalRAM.lean:4337`; that line is inside a doc
comment closing at `:4339`, documenting
`concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted` (`:4340`).  The
intended `def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`
is at `:4426`.  The path is correct.

Per the coordinator decision this is a NOTE, not an edit: an EVIDENCE NOTE
was APPENDED after the frozen anchor block, and no frozen requirement text
was touched.

### 4. WHAT WAS NOT DONE, AND WHY

The M7 doc row was NOT written.  It is not blocked -- the coordinator
supplied the query-time scoping and the construction-time carve-out, and
M3d-14 drafted an approvable sentence -- but it sits in resume item 5,
downstream of items 1-4, and this session's budget went to TASK ZERO and
the finding it produced.  Writing a doc row about the accepted route while
that route's interior leg is unbuilt would be writing ahead of the
evidence, which is what M3d-12 and M3d-13 both declined to do.

Resume items 1-5 are otherwise unchanged and are not restated.

### 5. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0 (twice: cap only, then with
positivity), under the `Global\RMQHeavyVerification` mutex:

    [276/278] Built RMQ.Core.WordRAM.E1InteriorChunkCap
    [277/278] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

The new module emits NO warning; its only line in the build log is the
Built line.  The 13 warning lines in the log are pre-existing and elsewhere.

`lake build rmq_e1_machine_validate` exit 0; `lake exe
rmq_e1_machine_validate` exit 0, UNCHANGED from M3d-14 as expected, since
this session added no machine block:

    presSentinelNonZero=true
    presFailures=0
    mutantE_segment_receiptFailures=36   (must be > 0)
    mutantG_scratch_preservationFailures=36   (must be > 0)
    mutantG_isPreservationOnly=true
    wholeQueryComparison=OPEN (interior leg UNBUILT, not blocked; NOT a pass)
    RESULT: PASS (with the whole-query comparison still OPEN)
    VALEXE_EXIT=0

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkCap` DIRECTLY -- all twelve theorems
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`.
`maxHeartbeats` was NOT raised anywhere.

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  None closed, none weakened, no frozen
row text edited.

Component-level evidence is, as in M3d-14, partly a subtraction: REQ-E1-03's
interior value evidence was resting on `hexact` believed vacuous at the
target store.  It is not vacuous.  The evidence is not withdrawn -- the
premise is still satisfiable and the cut is still right -- but it is now
correctly labelled as a live obligation with a named discharge route rather
than a closed one.

### 7. RESUME POINT (M3d-16)

All file:line verified at this commit.

1. THE FOLD'S TWO PREMISES ARE SETTLED.  Compose item 1 (the summary group)
   citing `E1InteriorChunkCap.chunkCount_le_eight_*` and `..._pos_*`, one
   per width.  Do not re-derive them and do not cite `cost_le_one` for
   either.
2. `hexact` IS THE REMAINING PREMISE AND IT IS LIVE.  Before composing the
   VALUE bridge (`interiorChunkFold_cOut_eq_routeDecode`), prove the
   non-final-chunk exactness lemma from
   `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`).  It does
   not exist yet -- the existing length lemmas
   (`chunkPayloadWords_word_length_le`, `:234`;
   `chunkPayloadWords_length_eq_div_add_indicator`, `:390`) are about
   bounds and counts, not per-index exactness.  `hle` is unaffected and
   still discharges verbatim from
   `canonicalRelativeRmmInteriorComponentStore_words_bounded`
   (`InteriorDirectory.lean:1711`).
3. STANDING, AND NEWLY LEARNED, alongside M3d-13's preservation rule and
   M3d-14's satisfiability rule: a premise recorded as VACUOUS at an
   instantiation owes a witness that it is vacuous there, on the same terms
   a premise recorded as owed owes a witness that it is satisfiable.
   "Vacuous because the tables are single-chunk" survived a session, a
   design decision and a coordinator review, and one `#eval` refuted it.
   WHERE A QUANTITY IS COMPUTABLE, EVALUATE IT.
4. Items 2-5 of M3d-13's list are unchanged.  The M7 doc row (section 4)
   has an approved scope and a drafted sentence and needs only the interior
   leg to exist.
5. STILL OWED, carried from M3d-13: an EXECUTED preservation check for the
   interior fold; the validator has no interior analogue of phase 3h.

## M3d-16 (worker E1-R4y): `hexact` discharged substantively; the lemma it needed was already in the tree

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`c9ddbbf` (M3d-15's yield) to this commit.  Green.

Module added: `RMQ/Core/WordRAM/E1InteriorChunkExact.lean`, registered in
`RMQ.lean`.  Nothing else in the tree was edited apart from the worklog,
`DESIGN_DECISIONS.md` and the matrix's evidence section.

### 1. THE RESUME DIRECTION'S NON-EXISTENCE CLAIM IS FALSE, AND IT MATTERED

M3d-16's delegation stated that the intended source for non-final-chunk
exactness, `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`),
"does not exist", and directed that the needed lemma be proved from
scratch.

IT EXISTS, at exactly that file and line:

    theorem chunkPayloadWords_get?_eq_take_drop
        {wordSize : Nat} {payload word : List Bool} {i : Nat}
        (hget : (chunkPayloadWords wordSize payload)[i]? = some word) :
        word = (payload.drop (i * wordSize)).take wordSize

That is exactly the per-index presentation the task needed, and four
modules already cite it (`GenericSelect/DenseWord.lean:38`,
`RankSelectCompressed/Base/ClassLengthEnvelope.lean:2679`,
`RankSelectCompressed/Base/LogChunks.lean:681`,
`RankSelectCompressedSubLogDenseWord.lean:222`).  The new module's proof
CALLS it and compiles, so this is settled by construction, not by grep.

The rest of the same direction is accurate: the two lemmas it named as the
existing alternatives, `chunkPayloadWords_word_length_le` (`:234`) and
`chunkPayloadWords_length_eq_div_add_indicator` (`:390`), really are about
bounds and counts rather than per-index exactness.  DD-20260719-010's
original direction -- use `_get?_eq_take_drop` -- was correct as written;
the "does not exist" gloss added downstream of it was wrong.

WHY THIS IS WORTH A SECTION.  Had the direction been followed literally,
the session would have re-proved a lemma the repository already had, in a
fifth place, and the duplicate would have been indistinguishable from
diligence.  This is the fourth consecutive session in which a supplied
claim did not survive checking, and the second in which the claim was
about what the tree contains rather than about what is true.

### 2. WHAT WAS ACTUALLY MISSING

Only the arithmetic and the flat-index bookkeeping.  Both are landed.

`succ_mul_le_of_succ_lt_chunkCount` is the whole arithmetic content: from
`j + 1 < width / wordSize + (if width % wordSize = 0 then 0 else 1)`, both
arms of the split give `j + 1 <= width / wordSize`, after which
`Nat.div_mul_le_self` gives `(j + 1) * wordSize <= width`.  Factored out
because it is the step a reviewer would otherwise re-derive.

`machineWords_length_eq_of_succ_lt_chunkCount` is the headline: the
machine word at flat index `i * count + j` has length exactly `wordSize`
whenever the table holds cell `i` and `j + 1 < count`.  It goes through
`FixedWidthNatTable.machineWords_cell_slice`
(`MachineChunkedTable.lean:121`) to reach cell `i`'s chunk list, then
`_get?_eq_take_drop`, then the arithmetic above.

`hexact_of_segment_agrees` restates it in the shape the value bridge
states `hexact`, over a `ReadStore` segment.  The guard travels correctly:
the bridge guards on `j + 1 < chunkIters`, and on the valid arm with the
cap in hand `chunkIters` IS the machine chunk count.

### 3. ANTI-VACUITY, APPLIED TO THIS MODULE'S OWN STATEMENT

The standing rule -- where a quantity is computable, EVALUATE it -- is
applied here to what this module CLAIMS, not only to what it consumes,
since that is the direction three consecutive audits found defects in.

`exactFixture_*` executes the claim on the `shape.size = 1` interior row
from M3d-15's evaluation (`wordSize = 2`, width `5`, `chunkCount = 3`),
the most multi-chunk reachable shape.  `exactFixture_chunkCount` confirms
the fixture matches that row.  `exactFixture_nonfinal_lengths` exhibits
the two non-final chunks at length exactly `2`.

`exactFixture_final_length_lt` is the one that matters: the FINAL chunk
has length `1`.  So the `j + 1 < n` guard is LOAD-BEARING -- dropping it
does not weaken the statement, it makes it FALSE at a reachable shape.
That is the check separating a real cut from a hypothesis carried for
appearance.  All four fixture theorems depend on NO axioms.

`cell_exists_of_lt` is DERIVED rather than assumed, from the table's own
`read_exact` field: if `entries[i]?` is `some`, the stored word cannot be
`none`.  Stated that way so the corollary carries no unchecked
existential.

The corollary's one carried premise, `hagree`, is a deliberate parameter:
the segment-to-table mapping is fixed by the interior composition, not by
this module, and writing a concrete layout here would guess something this
module cannot check.  Per the satisfiability rule it does not ship
undischarged -- `segmentStore` / `segmentStore_agrees` exhibit a store
meeting it.

### 4. WHAT WAS NOT DONE

Mission items 2-7 are UNBUILT: the summary group, the span blocks, the
two-span blocks, the five-branch dispatch and `hInterior`, and the whole
closure ladder.  Item 1 was the session.  Nothing was composed on the
fold beyond the premise discharge, and no matrix row moved.

One reconnaissance note on item 2, recorded because it was checked and it
CONFIRMS the delegation rather than correcting it: in
`canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) the `maxRel` read's value IS bound into
the summary tuple at `:2295`, but the min-candidate consumer
(`canonicalRelativeRmmMachineMinCandidateComputation`, `:2300`) maps
through `bpRelativeSummaryMinCandidate` and discards it.  So the
delegation's instruction is right and its reason is the receipt
obligation, not the value: the read must appear in the machine's log
because the route performs it, even though nothing downstream consumes it.

### 5. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0:

    ✔ [277/279] Built RMQ.Core.WordRAM.E1InteriorChunkExact
    ✔ [278/279] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

The new module emits NO warning; its only line in the build log is the
Built line.  The warning lines in the log are pre-existing and elsewhere
(the `unusedSimpArgs` linter at `SuccinctFinalRAM.lean`).

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkExact` DIRECTLY:

    succ_mul_le_of_succ_lt_chunkCount        [propext, Quot.sound]
    machineWords_length_eq_of_succ_lt_chunkCount
                                             [propext, Classical.choice, Quot.sound]
    cell_exists_of_lt                        [propext, Classical.choice, Quot.sound]
    hexact_of_segment_agrees                 [propext, Classical.choice, Quot.sound]
    exactFixture_chunkCount                  does not depend on any axioms
    exactFixture_chunks                      does not depend on any axioms
    exactFixture_nonfinal_lengths            does not depend on any axioms
    exactFixture_final_length_lt             does not depend on any axioms
    segmentStore_agrees                      [propext]

Never `sorryAx`.  `maxHeartbeats` was NOT raised anywhere.

### 6. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  None closed, none weakened, no frozen
row text edited.

REQ-E1-03's interior value evidence is strengthened in the one direction
M3d-15 left it weak: the value bridge's `hexact` premise now has a
substantive discharge route landed as executable Lean with an executed
load-bearing check, rather than a named-but-unbuilt one.  The row does not
move, because it is whole-query scoped and items 2-7 are unbuilt.

### 7. RESUME POINT (M3d-17)

All file:line verified at this commit.

1. THE FOLD'S THREE PREMISES ARE NOW ALL SETTLED.  `hcap`/`hccPos` from
   `E1InteriorChunkCap.chunkCount_le_eight_*` and `..._pos_*`, one per
   width (M3d-15).  `hle` verbatim from
   `canonicalRelativeRmmInteriorComponentStore_words_bounded`
   (`InteriorDirectory.lean:1711`).  `hexact` from
   `E1InteriorChunkExact.hexact_of_segment_agrees`, whose only open
   parameter is `hagree`, the segment-to-table mapping.  Do NOT cite
   `canonicalRelativeRmmMachineReadNatCosted_cost_le_one` for any of the
   three, and do NOT cite vacuity for `hexact`.
2. `hagree` IS THE ONE THING ITEM 2 MUST SUPPLY.  It is
   `∀ a, store.readWord? segment (base + a) =
   (fixedWidthNatTableMachineWords table wordSize)[a]?`.  The interior
   store's segment/offset assignment is
   `canonicalRelativeRmmInteriorComponentOffsets`
   (`InteriorDirectory.lean:1614`, consumed at `:2282`, `:2317`, `:2335`);
   the store's word list is
   `canonicalRelativeRmmInteriorComponentStore_words_toList` (`:1665`;
   note `:1707` is a USE site inside `..._words_size_eq`, not the
   declaration).  Deriving `hagree` from those two is the composition
   step, and it is NOT yet done.  It is stated as a parameter rather than
   guessed; `segmentStore_agrees` shows it is satisfiable, which is not
   the same as showing it holds AT THE INTERIOR STORE.  That distinction
   is the whole content of the satisfiability rule and must not be
   elided.
3. ITEM 2 RECONNAISSANCE, CHECKED: the `maxRel` read at
   `InteriorDirectory.lean:2290` binds its value into the summary tuple
   (`:2295`) but the min-candidate consumer (`:2300`) discards it.  The
   delegation's instruction not to optimise it away is correct, and its
   ground is the POSITIONAL receipt obligation, not the value.
4. STANDING RULES, now four, in the order learned: a premise recorded as
   OWED owes a witness it is SATISFIABLE at the intended instantiation
   (M3d-14); a premise recorded as VACUOUS owes a witness of VACUITY on
   the same terms (M3d-15); where a quantity is COMPUTABLE, EVALUATE it
   (M3d-15); and -- added this session -- a supplied claim about WHAT THE
   TREE CONTAINS is checkable in one grep and must be checked before it
   is acted on (M3d-16, section 1).
5. Items 3-5 of M3d-13's list are unchanged.  The M7 doc row still has an
   approved scope and a drafted sentence and still needs the interior leg
   to exist.
6. STILL OWED, carried from M3d-13 and unchanged: an EXECUTED preservation
   check for the interior fold; the validator has no interior analogue of
   phase 3h.

## M3d-17 (worker E1-R4z): the agreement premise was false at the target store, and the satisfiability witness is what hid it

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`da7556f` (M3d-16's yield) to this commit.  Green.

Mission item 1 -- derive `hexact` AT
`canonicalRelativeRmmInteriorComponentStore` -- IS DONE.  Items 2-7 (the
summary group, the span blocks, the two-span blocks, the five-branch
dispatch, `hInterior`, the closure ladder, the validator's interior
preservation phase) are UNBUILT.  Item 1 was the session, and it was not a
composition: the premise it was supposed to compose could not have held.

### 1. THE GAP THE DELEGATION FLAGGED WAS NOT A GAP -- IT WAS A DEFECT

M3d-16 recorded, unprompted, that `segmentStore_agrees` shows `hagree`
SATISFIABLE and not that it HOLDS at the interior store.  That reading was
right, and the coordinator was right to make closing it the first job.  What
neither anticipated is the answer.

`hagree` was stated UNBOUNDED: agreement at every address `base + a`.  It is
FALSE at `canonicalRelativeRmmInteriorComponentStore` for SEVEN OF ITS EIGHT
TABLES, and the reason is structural.  That store is the CONCATENATION of the
eight tables' machine word lists
(`canonicalRelativeRmmInteriorComponentStore_words_toList`,
`InteriorDirectory.lean:1665`).  Past the end of any one table the store still
answers `some` -- with the NEXT table's word -- while
`(fixedWidthNatTableMachineWords table wordSize)[a]?` has run out and answers
`none`.  Only the last component, `globalLevel`, escapes, and only because
nothing follows it.

EVALUATED FIRST, per the standing rule, before anything was built on it.  A
scratch `#eval` of `(baselineWords, storeWords)` gives

    one-node shape   (2, 31)
    two-node shape   (1, 38)
    four-node shape  (1, 69)
    eight-node shape (1, 133)

so at the smallest shape the unbounded premise is wrong about twenty-nine
addresses, not a boundary one, and larger shapes are worse.  That took one
`#eval` and settled in minutes what the prose could not.

WHY THE SATISFIABILITY WITNESS DID NOT CATCH THIS, and this is the part worth
carrying.  `segmentStore_agrees` is honest and its proof is correct.  It
exhibits a store built to hold ONE table -- and one table is exactly the case
where the unbounded form is fine.  The witness answered the question it was
asked and the question was too weak.  M3d-14's rule says a premise recorded as
OWED owes a witness that it is satisfiable AT THE INTENDED INSTANTIATION; the
words "at the intended instantiation" are where the weight sits, and a witness
constructed FOR the premise rather than FOUND at the target instantiation
satisfies the letter of the rule while defeating its purpose.  This is the
third consecutive session to find a premise unmeetable where it was needed
(M3d-14 the width premise, M3d-15 the false vacuity, this one the agreement),
and the first in which a witness had already been supplied.

### 2. THE REPAIR: BOUNDED, AND STRENGTHENING ONLY

Exactness is consumed at exactly ONE address.  `hexact_of_segment_agrees`
instantiates `hagree` only at `i * chunkCount + j`.  So the premise is bounded
to indices the table actually has:

    (hagree : forall a, a < (fixedWidthNatTableMachineWords table wordSize).length ->
      store.readWord? segment (base + a) =
        (fixedWidthNatTableMachineWords table wordSize)[a]?)

and the bound is supplied INTERNALLY, not pushed to the caller.
`machineWords_index_lt` (new) derives
`i * count + j < (fixedWidthNatTableMachineWords table wordSize).length` from
`List.mul_add_le_flatMap_length_of_constant_length`
(`MachineChunkedTable.lean:98`), which was already in the tree, for a cell the
table holds and a chunk below the count.  Its side condition -- that every
stored cell chunks into exactly `count` words -- is
`chunkPayloadWords_length_eq_chunkCount_of_mem`, extracted from
`machineWords_cell_slice`'s own proof, which establishes it inline.

Premise weakened, conclusion untouched, nothing renamed or deleted.  All
consumers are local, so the repair is contained.  See DD-20260719-012 (claimed
this session; the maximum OBSERVED in `DESIGN_DECISIONS.md` was
`DD-20260719-011`, which matches what the delegation stated -- checked before
claiming, per rule 4).

### 3. WHAT LANDED: `RMQ/Core/WordRAM/E1InteriorChunkStore.lean`

Registered in `RMQ.lean:45`.  No new registers, no new instructions -- this is
addressing arithmetic against the store the route already reads.

* `readWord?_slice` -- the generic fact.  If a store's segment reproduces
  `whole` and `whole = pre ++ mid ++ post`, the store agrees with `mid` at
  base `pre.length`, for indices `mid` has.  Built on
  `getElem?_append_len_add`, proved by induction.
* `HoldsInteriorStore` -- the SETUP hypothesis: the machine's flat store at
  `segment` holds the interior directory.  Witnessed satisfiable by
  `interiorReadStore` / `interiorReadStore_holds`.  See section 5 for what
  that witness does and does not establish -- the caution of section 1
  applies to it too, and is recorded rather than repeated as a mistake.
* `interior_words_toList` and the eight `split_*` -- the store's word list as
  the eight-fold append, in the components' own names, re-associated so each
  component sits in the `pre ++ mid ++ post` position.
* `hagree_baseline`, `hagree_minRel`, `hagree_maxRel`, `hagree_argOffset`,
  `hagree_local`, `hagree_global`, `hagree_localLevel`, `hagree_globalLevel`
  -- THE EIGHT AGREEMENT CLAUSES, each at the offset the ROUTE's own read
  computation uses (`canonicalRelativeRmmInteriorComponentOffsets`,
  `InteriorDirectory.lean:1614`, consumed at `:2282`, `:2317`, `:2335`).  All
  unconditional in `shape`.  So this is agreement with the route's addressing,
  not with a layout invented here.
* `hexact_baseline`, `hexact_minRel`, `hexact_maxRel`, `hexact_argOffset` --
  THE COMPOSITION STEP, and the deliverable.  Each is
  `hexact_of_segment_agrees` instantiated at
  `canonicalRelativeRmmInteriorComponentStore` with its `hagree` parameter
  SUPPLIED rather than assumed.  What remains in each statement -- `hcount`,
  `hvalid`, `hentries` -- are facts about the CALLER's index arithmetic, fixed
  when the summary group's program is written; they are not debts owed to the
  store.
* `machineStore_words_size` -- small but load-bearing.  The offsets are running
  sums of `Array.size` and the splits are running sums of `List.length`;
  without this bridge every offset goal stalls with the two as distinct
  `omega` atoms.

### 4. THE BOUND IS PROVED LOAD-BEARING, AND THE PROOF IS NOT A FIXTURE

`unbounded_agreement_refuted` derives `False` from the unbounded premise at
any shape whose `minRel` table is non-empty: at address
`offsets.baseline + (wordsBaseline shape).length` the baseline table answers
`none` while the store answers with `minRel`'s first word.

RECORDED BECAUSE IT CONSTRAINS FUTURE ANTI-VACUITY WORK.  The numeric fixture
was written FIRST -- `(wordsBaseline probeShape).length = 2` and
`store.words.size = 31` -- and it does not compile.  The interior store's
sizes run through `Nat.log2`, which Lean defines by WELL-FOUNDED RECURSION.
The compiler evaluates it, which is why `#eval` answered instantly, but THE
KERNEL CANNOT REDUCE IT, so both `rfl` and `decide` fail.  `native_decide`
would close it and is forbidden, correctly, since it moves the check out of
the kernel.

So the standing rule "where a quantity is computable, EVALUATE it" has a
boundary that this campaign had not yet hit: `#eval`-computable is not the
same as kernel-computable, and anti-vacuity evidence that must live IN the
tree cannot always be a fixture.  Here the general theorem is strictly
stronger than the fixture would have been -- it covers every reachable shape
rather than one -- so nothing was lost.  Elsewhere it may not be, and the
`#eval` should then be reported as reproduction evidence with the theorem
proved by other means, not smuggled in by `native_decide`.

### 5. WHAT IS STILL OWED, STATED PRECISELY

`HoldsInteriorStore` is a SETUP hypothesis, not a discharged fact, and it is
carried by all twelve clauses.  It is a different kind of object from the
premise this session repaired -- it says the machine was loaded with the
directory the route reads, which is what the interior program's wiring will
establish -- but the distinction must not be used to wave it through.

`interiorReadStore_holds` witnesses it SATISFIABLE.  Applying this session's
own finding to this session's own work: that is the same shape of witness as
`segmentStore_agrees`, constructed FOR the hypothesis rather than found at the
eventual concrete machine store.  It does NOT show that the store the interior
program actually runs against meets it.  Whoever writes item 2 owes that, and
the established E1 pattern for it is INSTANTIATION, not parameterisation:
`concreteBPNativeChunkedRankCloseSeedReadStore`
(`ChargedRankSelectWiring.lean:970`) builds a `ReadStore` by segment dispatch
onto `...store.words[index]?` and proves per-segment projections at `:989`,
`:997`, `:1005`, `:1013`.  `E1RankCanonical.lean:127` and
`E1CrossBlockArm.lean:1143` then put the concrete store directly in the
`RunsTo` slot.  No E1 module has ever carried an agreement hypothesis; the
parameterised form exists only in the route layer
(`ChargedFringeTrace.lean:332`, `ChargedRankSelectTrace.lean:43`).

### 6. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0, under the
`Global\RMQHeavyVerification` mutex:

    [278/280] Built RMQ.Core.WordRAM.E1InteriorChunkStore
    [279/280] Built RMQ
    Build completed successfully.

The new module emits NO warning; its only line in the build log is the Built
line.

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorChunkStore` DIRECTLY -- all nineteen theorems
`[propext]` or `[propext, Classical.choice, Quot.sound]`, never `sorryAx`:

    readWord?_slice                [propext]
    getElem?_append_len_add        [propext]
    machineStore_words_toList      [propext, Classical.choice, Quot.sound]
    machineStore_words_size        [propext, Classical.choice, Quot.sound]
    interiorReadStore_holds        [propext, Classical.choice, Quot.sound]
    interior_words_toList          [propext, Classical.choice, Quot.sound]
    hagree_baseline .. hagree_globalLevel (8)
                                   [propext, Classical.choice, Quot.sound]
    hexact_baseline .. hexact_argOffset (4)
                                   [propext, Classical.choice, Quot.sound]
    unbounded_agreement_refuted    [propext, Classical.choice, Quot.sound]

and importing `RMQ.Core.WordRAM.E1InteriorChunkExact` DIRECTLY, to confirm the
re-cut changed nothing:

    machineWords_index_lt                         [propext, Classical.choice, Quot.sound]
    chunkPayloadWords_length_eq_chunkCount_of_mem [propext, Classical.choice, Quot.sound]
    hexact_of_segment_agrees                      [propext, Classical.choice, Quot.sound]
    machineWords_length_eq_of_succ_lt_chunkCount  [propext, Classical.choice, Quot.sound]

`maxHeartbeats` was NOT raised anywhere.

### 7. MATRIX STATUS AT YIELD

All rows REQ-E1-01..11 remain OPEN.  This session closed none and weakened
none.  No frozen row text was edited.

Component-level evidence for REQ-E1-03 changes in the same double-edged way
M3d-14's and M3d-15's did.  The interior value bridge's `hexact` premise now
has a discharge AT the target store rather than a satisfiability witness away
from it -- that is an addition.  But the premise it was previously recorded
against was unmeetable there, so what the row previously appeared to have was
not real.  As M3d-14 put it: the row is no better off than it looked
yesterday, but it is now as well off as it looks.

### 8. RESUME POINT (M3d-18)

All file:line verified at this commit.

1. THE FOLD'S PREMISES ARE NOW ALL SETTLED AT THE TARGET STORE.  `hcap` /
   `hccPos` from `E1InteriorChunkCap.chunkCount_le_eight_*` and `..._pos_*`,
   one per width (M3d-15).  `hle` verbatim from
   `canonicalRelativeRmmInteriorComponentStore_words_bounded`
   (`InteriorDirectory.lean:1711`).  `hexact` from
   `E1InteriorChunkStore.hexact_baseline` / `_minRel` / `_maxRel` /
   `_argOffset` for the summary group, or from `hexact_of_segment_agrees` plus
   the matching `hagree_*` for the other four tables.  Do NOT cite
   `canonicalRelativeRmmMachineReadNatCosted_cost_le_one` for any of them, and
   do NOT cite vacuity for `hexact`.
2. `HoldsInteriorStore` IS THE ONE THING ITEM 2 MUST SUPPLY, and it must be
   supplied by INSTANTIATION, not by carrying it as a hypothesis.  See
   section 5 for the established pattern and its four precedents.  A witness
   built for the hypothesis is not a discharge -- that is precisely the error
   this session found.
3. THE SUMMARY GROUP `S` (`InteriorDirectory.lean:2277`
   `canonicalRelativeRmmMachineSummaryComputation`, `:2300`
   `canonicalRelativeRmmMachineMinCandidateComputation`) is otherwise
   unchanged from M3d-13's item 1 and is not restated.  Its register bank
   must sit at `100` and above (the fold owns `89 .. 99`) and must claim a DD
   id.  `iIdx` (`85`) is below the fold's bank, so it survives each fold by
   `ChunkFoldUntouched`.
4. THE `maxRel` READ MUST NOT BE OPTIMISED AWAY.  Re-confirmed at source by
   M3d-16: its value is bound into the summary tuple at `:2295` and discarded
   by the min-candidate consumer at `:2300`.  The ground for keeping it is the
   POSITIONAL RECEIPT obligation, not the value.
5. Items 3-5 of M3d-13's list (span blocks `:2311`/`:2329`, two-span blocks
   `:2351`/`:2376` with the level read as the UNCONDITIONAL HEAD of every
   append chain, five-branch dispatch `:2444`, then `hInterior` at
   `E1CrossBlockArm.lean:1143`) are unchanged and unbuilt.
6. STANDING RULES, now five, in the order learned: a premise recorded as OWED
   owes a witness it is SATISFIABLE at the intended instantiation (M3d-14); a
   premise recorded as VACUOUS owes a witness of VACUITY on the same terms
   (M3d-15); where a quantity is COMPUTABLE, EVALUATE it (M3d-15); a supplied
   claim about WHAT THE TREE CONTAINS is checkable in one grep and must be
   checked before it is acted on (M3d-16); and -- added this session -- A
   SATISFIABILITY WITNESS CONSTRUCTED FOR A PREMISE IS NOT A WITNESS AT THE
   TARGET.  It must be FOUND at the intended instantiation, or it can be
   correct, honest, and still hide a premise that is false there.
7. A COROLLARY TO RULE THREE, newly learned: `#eval`-computable is not
   kernel-computable.  Anything whose size runs through `Nat.log2` evaluates
   in the compiler and does NOT reduce in the kernel, so `rfl` and `decide`
   fail on it and `native_decide` is forbidden.  Where that bites, prove the
   fact generally and report the `#eval` as reproduction evidence.
8. STILL OWED, carried from M3d-13 and unchanged: an EXECUTED preservation
   check for the interior fold; the validator has no interior analogue of
   phase 3h.  The M7 doc row still has an approved scope and a drafted
   sentence (M3d-14 section 5) and still needs the interior leg to exist.

## M3d-18 (worker E1-R5a): the store hypothesis is eliminated by instantiation, and the discharge was already in the tree

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`a572f4b` (M3d-17's yield) to `bc3c8f0`.  Green.

Mission item 1 -- instantiate at the concrete interior store, discharging
`HoldsInteriorStore` rather than carrying it -- IS DONE.  Items 2-7 (the
summary group, the span blocks, the two-span blocks, the five-branch
dispatch, `hInterior`, the closure ladder, the validator's interior
preservation phase) are UNBUILT and were not started.

### 1. THE TARGET STORE IS NOT A MATTER OF CHOICE, AND THAT SETTLED IT

M3d-17 left twelve clauses carrying `HoldsInteriorStore store segment shape`
and witnessed it satisfiable by `interiorReadStore` -- a store built FOR the
hypothesis.  It flagged, against its own output, that this is the same shape
of witness that hid the false unbounded `hagree`.  The coordinator ruled:
eliminate by instantiation.

The question "instantiate at WHICH store?" has exactly one answer, and it is
not the implementer's to pick.  `crossBlockArmProgramAt_runsTo`
(`E1CrossBlockArm.lean:1143`) names it in its own `hInterior` premise: the
interior leg's `RunsTo` must hold at
`concreteBPNativeSuccinctRMQGlobalReadStore shape`.  Any other store is
irrelevant to the composition, which is precisely why a store built for the
hypothesis proves nothing.

THE DISCHARGE WAS ALREADY IN THE TREE.  That store answers segment `20` with
`(canonicalRelativeRmmInteriorComponentStore shape).store.words[index]?`
(`Segments.lean:221`), and `concreteBPNativeInteriorTraceSegments`
(`Segments.lean:60`) sets `canonicalComponent := 20`.  The projection
`concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent`
(`Segments.lean:258`) already existed: introduced by commit `b8ae4aa`
("Close U2 uniform reviewer route"), present at the branch base `d90b062`,
checked with `git log -S` rather than assumed.  It was written for the flat
reviewer layout, before the interior work, so it is in no sense a witness
built for this premise.

`holdsInteriorStore_concrete` is that projection plus the `Array`/`List`
bridge.  Three lines.  The whole of M3d-17's residue closed to an existing
fact -- which is the shape a genuine discharge usually has, and is worth
contrasting with the effort a constructed witness demands.

### 2. THE SEGMENT WAS CHECKED, NOT ASSUMED -- AND IT HAD A LIVE TRAP

`concreteBPNativeInteriorTraceSegments` carries a `summary` sub-record with
`baseline := 20`, `minRel := 21`, `maxRel := 22`, `argOffset := 23`.  In the
CANONICAL store those are not the summary tables: segment `21` is the fringe
chunk table (`Segments.lean:224`) and `22` is the select chunk table
(`Segments.lean:228`).  A composition that read the summary group at the
sub-record's per-table segments would silently read the wrong tables for
three of its four reads, and would still typecheck.

It does not arise, and the reason is structural.  The summary group
(`InteriorDirectory.lean:2277`) reads all four tables at OFFSETS --
`offsets.baseline`, `.minRel`, `.maxRel`, `.argOffset` -- into ONE flat
store, and `FlatStoreComputation` (`MachineChunkedTableProgram.lean:66`)
runs over a single `FlatWordStore : address -> word`.  One segment, four
offsets.  The eight delivered `hagree_*_concrete` are stated in exactly that
shape: one segment, the component offsets distinguishing the tables.

RECORDED BECAUSE IT IS A TRAP FOR ITEM 2.  The legacy per-table segments
(`Segments.lean:101`, `..._Legacy`) are the compatibility layout, where they
were correct.  Anyone wiring the interior who reaches for
`interiorSegments.summary.minRel` in the canonical store is reading the
fringe chunk table.

### 3. WHAT LANDED: `RMQ/Core/WordRAM/E1InteriorStoreConcrete.lean`

Registered in `RMQ.lean:46`.  Thirteen theorems, ALL UNCONDITIONAL in
`shape` -- no agreement hypothesis survives.  See DD-20260719-013 (claimed
this session; the maximum OBSERVED in `DESIGN_DECISIONS.md` was
`DD-20260719-012`, which matches what the delegation stated -- checked
before claiming, per rule 4).

* `interiorSegment` (`:67`) -- `concreteBPNativeInteriorTraceSegments.canonicalComponent`,
  named rather than spelled `20` so a layout change moves this module.
* `holdsInteriorStore_concrete` (`:80`) -- THE DISCHARGE, at the store
  `hInterior` names, at the segment the route reads.
* `hagree_baseline_concrete` .. `hagree_globalLevel_concrete`
  (`:93`, `:100`, `:107`, `:114`, `:121`, `:128`, `:135`, `:142`) -- the
  eight agreement clauses with the hypothesis SUPPLIED, not assumed.
* `hexact_baseline_concrete` .. `hexact_argOffset_concrete`
  (`:156`, `:173`, `:190`, `:207`) -- the summary group's four reads.

`E1InteriorChunkStore`'s parameterised forms are RETAINED beneath these as
the general lemmas they instantiate, exactly as `readWord?_slice` is
retained beneath those.  Nothing renamed, nothing deleted, no frozen
identity touched.  No E1 module now carries an agreement hypothesis.

### 4. THIS SESSION'S OUTPUT, JUDGED BY THE FIVE RULES

Rule 1/5 (a premise owes a witness FOUND at the intended instantiation).
`holdsInteriorStore_concrete` is found, not built: the store is named by
`hInterior` and the projection predates the campaign.  Verified by
`git log -S`, not by reading a docstring.

Rule 2 (a VACUOUS premise owes a witness of vacuity).  The inverse duty
applies here: the eight delivered clauses are bounded by
`a < (wordsX shape).length`, and if those lists were empty the clauses would
be vacuously true and worthless.  EVALUATED at an eight-element shape:

    (baseline, minRel, maxRel, argOffset) = (1, 4, 4, 4)
    (local, global, localLevel, globalLevel) = (80, 1, 36, 3)

All eight non-empty, so no delivered clause is vacuous.  `interiorSegment`
evaluates to `20`.  This is `#eval` REPRODUCTION EVIDENCE, not a kernel
proof -- per M3d-17's corollary these sizes run through `Nat.log2` and do
not reduce in the kernel.  The clauses themselves are proved generally; the
`#eval` only rules out vacuity.

Rule 3 (evaluate what is computable).  Done, above.

Rule 4 (check supplied tree claims).  All sixteen file:line anchors in the
delegation were checked before use.  Fourteen were exact.  TWO HAD WRONG
DIRECTORIES and are corrected here for successors:
`ChargedRankSelectWiring.lean` is at
`RMQ/Core/SuccinctClose/RelativeRmmMacro/`, NOT `RMQ/Core/WordRAM/`;
`WordStore.lean` is at `RMQ/Core/SuccinctSpace/`, NOT `RMQ/Core/WordRAM/`.
Line numbers and contents were exact at the corrected paths, so the claims
were sound and only the paths drifted.  The coordinator's item-2 note was
also checked at source: the `maxRel` value IS bound into the summary tuple
at `:2295` and the consumer at `:2300` is `bpRelativeSummaryMinCandidate`,
so the ground for keeping the read is the positional receipt, as stated.

STILL OWED, AND NOT DISGUISED.  `hexact_*_concrete` retain `hcount`,
`hvalid`, `hentries`.  They are facts about the CALLER's index arithmetic,
fixed when the summary group's program is written, and were never debts owed
to the store -- but they ARE premises, and under rule 1 they owe a witness
at the intended instantiation when item 2 lands.  Whoever writes item 2
should not treat "not a debt owed to the store" as "not a debt".

### 5. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0, under the
`Global\RMQHeavyVerification` mutex:

    [279/281] Built RMQ.Core.WordRAM.E1InteriorStoreConcrete
    [280/281] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

The new module emits NO warning; its only line in the build log is the Built
line.  All warnings in the log are pre-existing `unusedSimpArgs` in
`SuccinctFinalRAM.lean`, `E1InteriorChunkFold.lean:529` and
`ReviewerReachabilitySmall.lean`.

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorStoreConcrete` DIRECTLY -- all thirteen
`[propext, Classical.choice, Quot.sound]`, never `sorryAx`:

    holdsInteriorStore_concrete    [propext, Classical.choice, Quot.sound]
    hagree_baseline_concrete .. hagree_globalLevel_concrete (8)
                                   [propext, Classical.choice, Quot.sound]
    hexact_baseline_concrete .. hexact_argOffset_concrete (4)
                                   [propext, Classical.choice, Quot.sound]

`maxHeartbeats` was NOT raised anywhere; the new module contains no
`set_option`.

`lake build rmq_e1_machine_validate` exit 0; `lake exe rmq_e1_machine_validate`
exit 0, RESULT: PASS (with the whole-query comparison still OPEN).  Modeled
counts (reproducible) separated from wall-clock:

    dispatchCases=405   modeledSteps=2430        modeledReads=0
    legCases=90         legModeledSteps=30343    legModeledReads=1080
    selectCases=32      selectModeledSteps=8273  selectModeledReads=475
    composeCases=40     composeModeledSteps=9222 composeModeledReads=322
    mergeCases=36       mergeModeledSteps=431    mergeModeledReads=0
    armCases=36         armModeledSteps=6276     armModeledReads=234
    rangeCases=54       rangeModeledReads=0
    presCases=36        presCheckedRegs=66       presFailures=0
    total wall clock 9881 ms

Mutation evidence, unchanged by this session and re-observed green: 4e
`mutantE_segment_receiptFailures=36` with `mutantE_isReceiptOnly=true`; 4f
`mutantF_blockEnd_mismatches=33`; 4g
`mutantG_scratch_preservationFailures=36` with `mutantG_clobberedRegs=[70]`
and `mutantG_isPreservationOnly=true`.  Phase 5 remains
`wholeQueryComparisonAvailable=false`, interior leg UNBUILT -- consistent
with items 2-7 not being started.

`lake env lean scripts/headline_axiom_check.lean` exit 0.
`claim_drift_scan.ps1`: 744 hits, 0 strict failures, exit 0.
`paper_topology_lint.ps1`: PASS (83 broad documentary identifiers; 49 paper
identifiers resolved), exit 0.  `design_decision_check.ps1 -Strict` exit 0.
`git diff --check` clean on the working tree; the committed-range form flags
whitespace SOLELY in the inherited `docs/internal/B7_STEP2_WIP.patch`, as
the delegation predicted.  Hygiene `rg` over the new module: no
sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib and no
`by_contra`/`norm_num`/`set`.  Tree-wide `native_decide` appears only in
`scripts/axiom_check.lean` (KNOWN RED, externally owned, not touched).

KNOWN RED confirmed still red and untouched:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate`.

### 6. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none and
weakened none.  No frozen row text was edited.

Component-level evidence for REQ-E1-03 improves in a way that, unlike the
last three sessions, is NOT double-edged.  M3d-14, M3d-15 and M3d-17 each
found the previously-recorded evidence unmeetable where it was needed, so
the row was never as well off as it looked.  Here the twelve clauses were
correct as stated and merely conditional; removing the condition strictly
adds.  The row is better off than it was yesterday -- but it is still OPEN,
and the interior leg it needs remains unbuilt.

### 7. RESUME POINT (M3d-19)

All file:line verified at `bc3c8f0`.

1. ITEM 1 IS DONE AND NEEDS NO REVISITING.  The fold's premises are settled
   at the target store AND the store hypothesis is gone.  Use
   `E1InteriorStoreConcrete.hexact_baseline_concrete` / `_minRel_` /
   `_maxRel_` / `_argOffset_` for the summary group and the eight
   `hagree_*_concrete` for the other four tables.  `hcap`/`hccPos` from
   `E1InteriorChunkCap.chunkCount_le_eight_*` / `..._pos_*`; `hle` verbatim
   from `canonicalRelativeRmmInteriorComponentStore_words_bounded`
   (`InteriorDirectory.lean:1711`).  Do NOT cite
   `canonicalRelativeRmmMachineReadNatCosted_cost_le_one` for any of them,
   and do NOT cite vacuity for `hexact`.
2. THE SEGMENT TRAP OF SECTION 2 IS THE FIRST THING ITEM 2 CAN GET WRONG.
   Read at `E1InteriorStoreConcrete.interiorSegment` and the component
   OFFSETS.  Never at `interiorSegments.summary.minRel` / `.maxRel` in the
   canonical store -- those are the fringe and select chunk tables there.
3. THE SUMMARY GROUP `S` (`InteriorDirectory.lean:2277`
   `canonicalRelativeRmmMachineSummaryComputation`, `:2300`
   `canonicalRelativeRmmMachineMinCandidateComputation`) is unchanged from
   M3d-13's item 1 and is not restated.  Its register bank must sit at `100`
   and above (the fold owns `89 .. 99`) and must claim a DD id.  `iIdx`
   (`85`) is below the fold's bank, so it survives each fold by
   `ChunkFoldUntouched`.  Compose on the FOLD uniformly -- the 7-instruction
   atom is WRONG at the small multi-chunk shapes.
4. THE `maxRel` READ MUST NOT BE OPTIMISED AWAY.  Re-confirmed at source
   this session: bound into the summary tuple at `:2295`, discarded by
   `bpRelativeSummaryMinCandidate` at `:2300`.  The ground for keeping it is
   the POSITIONAL RECEIPT obligation, not the value.
5. ITEMS 3-5 UNCHANGED AND UNBUILT: span blocks (`:2311`, `:2329`, the
   `none` arm must branch PAST the summary group); two-span blocks (`:2351`,
   `:2376`, THE LEVEL READ IS THE UNCONDITIONAL HEAD of every append chain
   -- violating that order presents as a whnf heartbeat timeout, NOT a type
   error, and must never be met by raising `maxHeartbeats`); five-branch
   dispatch (`:2444`); then `hInterior` at `E1CrossBlockArm.lean:1143`.  The
   interior has five branches and no scan.
6. ITEMS 6-7 UNCHANGED AND UNBUILT: the closure ladder (full LCA leg at
   canonical-store form; whole-query glue via `E1RouteDecomposition` with
   result agreement on `(...).value` and POSITIONAL receipt equality on
   `(...).trace`; category accounting across ALL branches including
   selects-none and lca-none; the public `List Int` corollary; the DERIVED
   all-size literal step total from the category algebra and the caps
   33/8/8 -- derive, never assert; the amended-target Prop with its
   supersession note; the validator's whole-query phase; docs and matrix
   closure; the ONE consolidated program-layout DD at the glue), and an
   EXECUTED preservation check for the interior fold -- the validator's
   phase 3h is fringe-arm only, confirmed this session in its output, and
   has no interior analogue.
7. STANDING RULES, still five, unchanged in content.  This session adds no
   sixth.  It does add a caution to rule 4: the delegation's file:line
   anchors were sound in line number and content but TWO HAD STALE
   DIRECTORY PATHS (section 4).  Grepping for the basename rather than
   trusting the path costs one command and catches it.
8. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (the route reaches
   `bpSparseLogSpan` at store-construction via `bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do not
   edit frozen requirement text.

## M3d-19 (worker E1-R5b): the summary group, composed on the fold, and the `hexact` residue discharged by the layout's definition

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`7c5ad6a` (M3d-18's yield plus its worklog commit) to this commit.  Green.

Mission item 1 -- the summary group `S` -- IS DONE, in both halves: the
EXECUTION half (`RunsTo`, positional receipt, preservation) and the VALUE
half (each saved cell equals the route's decode).  Items 2-6 (span blocks,
two-span blocks, five-branch dispatch, `hInterior`, the closure ladder, the
validator's interior preservation phase) are UNBUILT and were not started.

### 1. THE ANCHORS WERE RE-VERIFIED, AND THIS TIME THEY ALL HELD

M3d-18 reported two of sixteen delegation anchors had stale DIRECTORY
paths.  All anchors supplied to this session were checked before use and
were exact -- nine in `InteriorDirectory.lean` (`:2277`, `:2295`, `:2300`,
`:2311`, `:2329`, `:2351`, `:2376`, `:2444`, `:1711`),
`E1CrossBlockArm.lean:1143`, `E1InteriorChunkFold.lean:928`, and the
module locations for `Segments.lean`, `SparseLevelTable.lean`,
`BlockLocal.lean`, `MachineChunkedTableProgram.lean`.

One correction of record about the RESUME rather than the tree: the
inventory in section 7 above states its file:line are verified at
`bc3c8f0`, but the branch HEAD at session start was `7c5ad6a`.  Checked
rather than assumed: `git diff --stat bc3c8f0 7c5ad6a` is
`docs/internal/E1_WORKLOG.md | 271 +++++`, a worklog-only commit, so the
code tree is identical and the inventory's line numbers carry unchanged.

### 2. THE SEGMENT TRAP WAS CONFIRMED ABSENT, BY INSPECTION NOT BY TRUST

M3d-18 flagged that `concreteBPNativeInteriorTraceSegments.summary` carries
`minRel := 21` / `maxRel := 22`, which in the canonical store are the
fringe and select chunk tables, and asserted the trap does not arise
because the group reads by offset into one `FlatWordStore`.  Verified here
at source rather than accepted: all four reads in
`canonicalRelativeRmmMachineSummaryComputation` (`:2277`) are calls to
`canonicalRelativeRmmMachineReadNatComputation shape <table> <offset> <index>`
(`:2132`), which is `machineReadComputationAt wordSize base dead i` over a
single flat store.  One segment, four offsets.  The claim was correct.
Nothing in the new module mentions the per-table segments.

### 3. WHAT LANDED: `RMQ/Core/WordRAM/E1InteriorSummaryGroup.lean`

Registered in `RMQ.lean:47`.  Nineteen theorems, register bank `100 .. 104`.
See DD-20260719-014 (claimed this session; maximum OBSERVED was
`DD-20260719-013`, checked before claiming).

* `summaryStage` (`:95`), `summaryStage_runsTo` (`:136`) -- one staged read:
  set `iIdx`, run the eight-capped fold, save `cOut`.  39 instructions.
* `summaryGroup` (`:272`), `summaryGroup_runsTo` (`:307`) -- four stages in
  the route's bind order.  156 instructions.  The receipt is the
  concatenation of the four route event lists; the four cells land in
  `sBase`/`sMin`/`sMax`/`sArg`; preservation holds outside the fold's bank.
* `canonicalSummaryLayout` (`:451`) and the eight cap discharges
  (`:493` .. `:528`), `canonicalSummaryGroup_runsTo` (`:542`) -- the group
  at `concreteBPNativeSuccinctRMQGlobalReadStore shape`, with all eight
  chunk-count premises SUPPLIED from `E1InteriorChunkCap`.
* `hle_concrete` (`:616`) -- the width bound, verbatim from
  `canonicalRelativeRmmInteriorComponentStore_words_bounded`
  (`InteriorDirectory.lean:1711`) through the segment-20 projection.
* `geomRouteDecode` (`:651`), `geomCell_eq_routeDecode` (`:661`) and the
  four per-table bridges (`:681`, `:695`, `:712`, `:726`) -- each saved
  cell IS the route's decode.

### 4. THE TWO FINDINGS THAT CHANGED THE DESIGN

FINDING A: THE HEAD CATEGORY IS NOT UNIFORM ACROSS THE FOUR STAGES.  The
baseline read is at `block / blocksPerSuper` and needs `divConst`, which
charges `.arithmetic`; the other three are at `block` and use `move`,
charging `.registerWrite`.  The first draft of `summaryStageCats` fixed the
head at `registerWrite`.  Both are ONE-ELEMENT logs, so that draft would
have produced a category log of the right LENGTH and the wrong CONTENT in
exactly one slot of four -- invisible to a length check and to a read-count
check, since neither is a memory read.  Caught by reading
`RunsTo.divConst` (`E1MachineCalculus.lean:191`) before composing rather
than after a failure.  The head category is now a parameter.

FINDING B: THREE OF THE FOUR SUMMARY READS ARE MULTI-CHUNK AT EVERY SHAPE
TRIED.  The delegation directed composing on the fold because small shapes
are multi-chunk.  Evaluated, at `stackCartesianShape` inputs of size 8, 16,
64 and 256, the four chunk counts `(baseline, minRel, maxRel, argOffset)`
are `(1, 2, 2, 2)` -- IDENTICAL at all four sizes.  So the single-chunk
atom is unsound for three of this group's four reads not at some small
corner but at every shape evaluated, including size 256.  The direction was
right and its stated reason understates the case.

### 5. THE OWED PREMISES, DISCHARGED RATHER THAN INHERITED

The delegation named this explicitly: `hexact_*_concrete` retain `hcount`,
`hvalid`, `hentries`, and rule 1 applies to them at composition.  They are
discharged by how `canonicalSummaryLayout` is DEFINED, not by an added
hypothesis:

* `chunkCount` is defined to BE the route's
  `fixedWidthNatTableMachineChunkCount` at that table's width, so `hcount`
  is `rfl`.
* `entriesLen` is defined to BE the route's own entry-list length, so
  `hvalid` and `hentries` are the SAME proposition.

This is machine-checked, not argued: the four bridge theorems pass `rfl`
for `hcount` and the same `hvalid` term for both `hvalid` and `hentries`,
and they compile.  What reaches the caller is one `i < entriesLen`
obligation per read -- the route's own validity condition, which the
interior's branch structure supplies at the call site.

Table-to-width correspondence checked at source, not assumed: baseline
carries `superWidth`; minRel, maxRel and argOffset all carry
`relativeWidth` (`E1InteriorChunkCap.lean:127-129`), matching the `hcount`
clauses of the four `hexact_*_concrete` exactly.

### 6. ANTI-VACUITY, APPLIED TO THIS SESSION'S OWN OUTPUT

The four bridges are guarded by `hvalid : i < entriesLen`.  If any entry
list were empty that premise would be unsatisfiable and the bridge
worthless.  EVALUATED -- entry lengths
`(baseline, minRel, maxRel, argOffset)`:

    size   8 : (1,  2,  2,  2)      chunk counts (1, 2, 2, 2)
    size  16 : (1,  3,  3,  3)      chunk counts (1, 2, 2, 2)
    size  64 : (2,  9,  9,  9)      chunk counts (1, 2, 2, 2)
    size 256 : (4, 28, 28, 28)      chunk counts (1, 2, 2, 2)

All sixteen entry lengths non-zero, so no bridge is vacuous; all sixteen
chunk counts in `1 .. 8`, consistent with the eight cap discharges.
`(summaryGroup (canonicalSummaryLayout (sh 8)) 0).length` evaluates to
`156`, agreeing with the kernel-proved `summaryGroup_length`, and
`interiorSegment` to `20`, independently reproducing M3d-18's figure.

Per M3d-17's corollary this is `#eval` REPRODUCTION EVIDENCE, not a kernel
proof: these quantities run through `Nat.log2`, which the compiler
evaluates but the kernel cannot reduce, so `rfl`/`decide` fail on them.
Evaluation FINDS truth; it does not PROVE it.  The theorems themselves are
proved generally.

### 7. A STALE DOCSTRING, RECORDED AND NOT EDITED

`E1InteriorChunkValue.lean:521-524` still justifies its `hexact` premise by
saying it discharges "vacuously, because the interior tables are
single-chunk".  That is out of date twice over: M3d-16 discharged `hexact`
SUBSTANTIVELY via `chunkPayloadWords_get?_eq_take_drop`, and section 6
above shows three of the four summary tables are TWO-chunk at every shape
evaluated, so the single-chunk premise the gloss rests on is false.  The
theorem is correct and unaffected; only its docstring's justification is
wrong.  Recorded rather than edited, since it is another module's text and
the delegation's standing instruction is to report discrepancies.  This is
also why the delegation's "do NOT cite vacuity for hexact" is right.

### 8. VERIFICATION LEDGER

`lake build RMQ RMQPaper RMQExamples` exit 0, under the
`Global\RMQHeavyVerification` mutex:

    [280/282] Built RMQ.Core.WordRAM.E1InteriorSummaryGroup
    [281/282] Built RMQ
    Build completed successfully.
    BUILD_EXIT=0

The new module emits NO warning; its only line in the build log is the
Built line.  All thirteen warnings in the log are pre-existing, in
`BPNavigationRAM.lean`, `ReviewerReachabilityLong/Small/Sparse.lean`,
`SuccinctFinalRAM.lean` and `E1InteriorChunkFold.lean`.

`#print axioms` AFTER a root build, importing
`RMQ.Core.WordRAM.E1InteriorSummaryGroup` DIRECTLY -- all nineteen, never
`sorryAx`:

    summaryStage_runsTo              [propext, Classical.choice, Quot.sound]
    summaryGroup_runsTo              [propext, Classical.choice, Quot.sound]
    canonicalSummaryGroup_runsTo     [propext, Classical.choice, Quot.sound]
    canonicalSummaryLayout_{baseline,minRel,maxRel,argOffset}_{pos,cap} (8)
                                     [propext, Classical.choice, Quot.sound]
    hle_concrete                     [propext, Classical.choice, Quot.sound]
    geomCell_eq_routeDecode          [propext, Classical.choice, Quot.sound]
    geomCell_{baseline,minRel,maxRel,argOffset}_eq_routeDecode (4)
                                     [propext, Classical.choice, Quot.sound]
    summaryGroup_length              [propext]
    summaryStage_length              [propext]

`maxHeartbeats` was NOT raised anywhere; the new module contains no
`set_option`.  Hygiene `rg` over it: no
sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib and
no `by_contra`/`norm_num`/`set` tactic.

### 9. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none and
weakened none.  No frozen row text was edited.

REQ-E1-03's component evidence improves: the summary group is the first of
the interior's five branches to have both an executed simulation and a
value bridge at the canonical store.  The row stays OPEN -- four more
branch families and the dispatch remain unbuilt, and no whole-query
comparison exists.

### 10. RESUME POINT (M3d-20)

All file:line verified at this commit.

1. ITEMS 1 AND 2 OF THE PRIOR INVENTORY ARE DONE.  The summary group has
   `canonicalSummaryGroup_runsTo` (`E1InteriorSummaryGroup.lean:542`) for
   execution and the four `geomCell_*_eq_routeDecode` (`:681`, `:695`,
   `:712`, `:726`) for value.  Consumers owe only `i < entriesLen` per read.
2. THE NEXT BLOCK IS THE MIN-CANDIDATE CONSUMER
   (`canonicalRelativeRmmMachineMinCandidateComputation`,
   `InteriorDirectory.lean:2300`), which maps `bpRelativeSummaryMinCandidate`
   over the group's tuple.  It DISCARDS `maxRel`.  The `maxRel` stage must
   still be present -- the receipt obligation, not the value, is its ground,
   and `geomCell_maxRel_eq_routeDecode` exists deliberately so that a future
   reader does not infer from a missing bridge that the read is optional.
3. THEN THE SPAN BLOCKS (`:2311`, `:2329`) -- the `none` arm must branch PAST
   the summary group -- and the TWO-SPAN BLOCKS (`:2351`, `:2376`), where
   THE LEVEL READ IS THE UNCONDITIONAL HEAD of every append chain; violating
   that order presents as a whnf heartbeat timeout, NOT a type error, and
   must never be met by raising `maxHeartbeats`.  Then the five-branch
   dispatch (`:2444`) and `hInterior` at `E1CrossBlockArm.lean:1143`.
   The interior has five branches and no scan.
4. REGISTER BANK: `100 .. 104` is now TAKEN by the summary group.  The next
   block opens at `105`.  Anything that must survive a summary group must
   satisfy `GroupUntouched` (`:292`): outside `89 .. 99` and distinct from
   `iIdx` and the four saved slots.
5. WHEN COMPOSING THE GROUP MORE THAN ONCE in one program, note the head
   instructions write `iIdx` (`85`), so `iIdx` is NOT preserved across a
   group -- `GroupUntouched` excludes it explicitly.  `sBlock` (`100`) IS
   preserved and is the input.
6. ITEMS 6-7 OF THE PRIOR INVENTORY UNCHANGED AND UNBUILT: the closure
   ladder (full LCA leg at canonical-store form; whole-query glue via
   `E1RouteDecomposition` with result agreement on `(...).value` and
   POSITIONAL receipt equality on `(...).trace`; category accounting across
   ALL branches including selects-none and lca-none; the public `List Int`
   corollary; the DERIVED all-size literal step total from the category
   algebra and the caps 33/8/8 -- derive, never assert; the amended-target
   Prop with its supersession note; the validator's whole-query phase; docs
   and matrix closure; the ONE consolidated program-layout DD at the glue),
   and an EXECUTED preservation check for the interior fold -- the
   validator's phase 3h is fringe-arm only and has no interior analogue.
7. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (`bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do not
   edit frozen requirement text.
8. STANDING RULES, still five, unchanged in content.  This session adds no
   sixth.  It adds one caution to rule 3: when a block's stages differ only
   in their HEAD instruction, check the head's CHARGE CATEGORY, not just its
   effect on registers -- two heads of the same arity and the same log
   length can charge differently, and the resulting error is invisible to
   both length and read-count checks (section 4, finding A).

## M3d-20 (worker E1-R5c): the stale `hexact` gloss repaired, and a content-level obstruction found in the min-candidate consumer

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`190cb9d` to `ff9bee1`.  Green.

Mission item 0 (the coordinator-directed docstring repair) IS DONE.  Items
1-6 are UNBUILT.  Item 1 was not started, deliberately: the design survey
below found a soundness constraint on it that changes its size, and
starting a module that could not land green was the worse trade.  This is
the fifteenth session to make that call.

### 1. THE ANCHORS ALL HELD, INCLUDING THE ONES IN THE DELEGATION

Every anchor supplied was grepped before use, per rule 4.  All were exact:
`E1InteriorChunkValue.lean:521-524`, the seven `InteriorDirectory.lean`
anchors (`:2295`, `:2300`, `:2311`, `:2329`, `:2351`, `:2376`, `:2444`),
and `E1CrossBlockArm.lean:1143`.  No repair was needed this session -- the
first session in three where that is true.

### 2. WHAT LANDED: THE `hexact` JUSTIFICATION, REPAIRED

`E1InteriorChunkValue.lean:521-524` justified the `hexact` premise as
discharging "vacuously, because the interior tables are single-chunk".
The delegation reported both halves false; both halves were CHECKED here
before the rewrite rather than taken on report, and both are indeed false.

* THE DISCHARGE IS SUBSTANTIVE.  Chain, read at source:
  `hexact_*_concrete` (`E1InteriorStoreConcrete.lean:156`, `:173`, `:190`,
  `:207`) -> `hexact_*` (`E1InteriorChunkStore.lean:424`, `:444`, `:464`,
  `:484`) -> `hexact_of_segment_agrees` (`E1InteriorChunkExact.lean:213`)
  -> `machineWords_length_eq_of_succ_lt_chunkCount` (`:90`), resting on
  `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`).
* THE TABLES ARE NOT SINGLE-CHUNK.  `minRel`, `maxRel` and `argOffset` all
  carry `relativeWidth` in `canonicalSummaryLayout`
  (`E1InteriorSummaryGroup.lean:451`) -- verified by reading the layout,
  not from the report -- and `E1InteriorChunkExact.lean:19-21` records
  that width's chunk count as 2 from size 4 to 256.

ONE CORRECTION OF RECORD AGAINST THE DELEGATION'S PHRASING.  It states the
summary tables are two-chunk "at every shape evaluated".  That is true of
the four sizes M3d-19 evaluated (8/16/64/256), but the tree's OWN
evaluation at `E1InteriorChunkExact.lean:19-21` gives chunk count 1 at
sizes 1024, 4096 and 65536.  Across everything evaluated in the tree the
tables are multi-chunk at SMALL shapes and single-chunk at large ones.
The load-bearing point survives and is sharper for it: single-chunk-ness
is SHAPE-DEPENDENT, so vacuity can never be the ground at any shape.  The
docstring was written to that, not to "every shape".

Freshly evaluated here at `shape.size = 8`, the layout's four chunk counts
are `(1, 2, 2, 2)`, reproducing M3d-19's figure independently.  Sizes
16/64/256 were NOT re-evaluated this session -- each `#eval` builds the
whole shape and the 1024 row did not return within budget -- so the
docstring asserts only the size-8 tuple as directly evaluated and rests
the 4..256 range on the in-tree table plus the width correspondence.

The edit is docstring-only: no theorem, statement or proof changed.  Its
citations to `ChunkExact`/`ChunkStore`/`StoreConcrete`/`SummaryGroup` are
forward references in a comment (this module imports only
`E1InteriorChunkFold`), matching existing practice in the other direction.

### 3. THE FINDING THAT RESIZES ITEM 1: `maxRel`'S VALUE IS LOAD-BEARING

The delegation directs that `maxRel` must not be optimised away, and
grounds that in the POSITIONAL RECEIPT obligation, "not the value".  The
receipt ground is real.  BUT THE VALUE GROUND IS ALSO REAL, and a block
built on the delegation's framing alone would be UNSOUND.

`canonicalRelativeRmmMachineSummaryComputation` (`InteriorDirectory.lean:2277`)
ends in

    match baseline, minRel, maxRel, argOffset with
    | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
    | _, _, _, _ => none

so `maxRel = none` forces the WHOLE summary to `none`, hence the
min-candidate to `none`.  `bpRelativeSummaryMinCandidate`
(`RelativeSummaryCandidate.lean:15`) then reads only `summary.1`,
`summary.2.1` and `summary.2.2.2` -- confirmed at source, `maxRel` is
`summary.2.2.1` and is never read.  So `maxRel` is discarded by the
FUNCTION and load-bearing through the OPTION STRUCTURE.

This is precisely the defect class the delegation warns about.  A block
that keeps the `maxRel` READ (satisfying the receipt, and a read-count and
trace-length check) but ignores its VALUE returns `some` wherever the
route returns `none`.  Right shape, wrong content, invisible to every
aggregate check.

THE `none` CASE IS REACHABLE, NOT HYPOTHETICAL.
`machineReadComputationAt` (`MachineChunkedTableProgram.lean:343`) reads
`[deadAddress]` when `i >= entries.length`, and the decode of that is
`none`.  So `none` IS the out-of-range arm -- exactly the `valid` flag the
fold already tracks in `geomCats` (`E1InteriorSummaryGroup.lean:249`).

WHAT THIS DOES AND DOES NOT SETTLE.  `minRel`, `maxRel` and `argOffset`
are all read at the same index `block`, but against THREE DIFFERENT entry
lists (`bpBlockRelativeMinExcessEntries`, `bpBlockRelativeMaxExcessEntries`,
`bpBlockArgMinLocalOffsetEntries`).  If those lengths could differ there
would be a `block` where `minRel` is `some` and `maxRel` is `none`.
M3d-19's recorded anti-vacuity table has them EQUAL at all four sizes
evaluated (`(1,2,2,2)`, `(1,3,3,3)`, `(2,9,9,9)`, `(4,28,28,28)`).  That
is evaluation, not proof, and no lemma asserting the equality was found in
the tree.  So the successor has a genuine fork, and it should be decided
before instructions are written:

  (a) prove `maxRel.entriesLen = minRel.entriesLen` (and `argOffset`'s),
      after which the four-way `none` test collapses to two tests; or
  (b) implement all four tests and prove nothing about the lengths.

(a) is cheaper at runtime and costs a lemma; (b) is unconditional.  Either
is sound; ASSUMING (a)'s equality without proving it is not.

### 4. THE OPTION ENCODING THE BLOCK MUST HIT

The established machine encoding of `Option (Nat x Nat)` is `bestOfRegs`
(`E1FringeFoldBlock.lean:114`): `if bv = 0 then none else some (bv - 1, bp)`
-- a value register shifted by `+1`, a raw position register.  The summary
group's saved cells are shifted the SAME way (`geomRouteDecode`,
`E1InteriorSummaryGroup.lean:651`: `none => 0`, `some v => v + 1`), so the
consumer's arithmetic runs on shifted operands and the route's runs on
unshifted ones.  Written out, with `span := bpSuperblockSpan blockSize
blocksPerSuper`:

    route value 1 = baseline + minRel - span = (sBase - 1) + (sMin - 1) - span
    route value 2 = blockStartOf blockSize block + argOffset
                  = block * blockSize + (sArg - 1)

and the machine must save `value 1 + 1` and `value 2`.  EVERY subtraction
there is Nat-truncated, and the shifts do not cancel by inspection.  This
is a place to check content per position, not to simplify eagerly.
`blockStartOf` is `block * blockSize` and `mulConst` is sound (settled).

### 5. VERIFICATION LEDGER

Under the `Global\RMQHeavyVerification` mutex:

    lake build RMQ RMQPaper RMQExamples      LIB_BUILD_EXIT=0
    lake build rmq_e1_machine_validate       VALIDATOR_BUILD_EXIT=0
    lake exe rmq_e1_machine_validate         VALIDATOR_RUN_EXIT=0

    Build completed successfully.
    [279/282] Built RMQ.Core.WordRAM.E1InteriorChunkValue
    [280/282] Built RMQ.Core.WordRAM.E1InteriorSummaryGroup

Validator: `RESULT: PASS (with the whole-query comparison still OPEN)`,
`wholeQueryComparisonAvailable=false`.  Phase 3h (fringe-arm preservation)
`presFailures=0`, `presSentinelNonZero=true`, and its mutation phase 4g
`mutantG_scratch_preservationFailures=36` with
`mutantG_isPreservationOnly=true` -- the discriminators still bite.  The
interior analogue of 3h remains unbuilt and is still owed.

The edited module emits no warning; the thirteen in the log are all
pre-existing (`SuccinctFinalRAM`, `ReviewerReachability{Small,Long,Sparse}`,
`BPNavigationRAM`, `E1InteriorChunkFold`), matching M3d-19's record.

`#print axioms` after a root build, importing the modules DIRECTLY:

    interiorChunkFold_cOut_eq_routeDecode  [propext, Classical.choice, Quot.sound]
    canonicalSummaryGroup_runsTo           [propext, Classical.choice, Quot.sound]
    geomCell_maxRel_eq_routeDecode         [propext, Classical.choice, Quot.sound]
    hexact_of_segment_agrees               [propext, Classical.choice, Quot.sound]

Never `sorryAx`.  `lake env lean scripts/headline_axiom_check.lean` runs
clean.  `design_decision_check.ps1 -Strict` `DD_EXIT=0` ("no
design-sensitive paths detected"), `claim_drift_scan.ps1` `DRIFT_EXIT=0`,
`paper_topology_lint.ps1` `TOPO_EXIT=0`.  `git diff --check` exit 0; the
committed-range form flags whitespace solely in the inherited
`docs/internal/B7_STEP2_WIP.patch`, the recorded exception.  Hygiene `rg`
over the touched module is clean -- its only `partial` hit is the English
word "partially" in prose at `:42`.  `maxHeartbeats` was not raised
anywhere.

NO DD WAS CLAIMED.  The maximum OBSERVED remains `DD-20260719-014`
(M3d-19).  A docstring repair is not a design decision, and the strict
checker agrees no design-sensitive path was touched.  The consolidated
program-layout DD is still owed at the glue.

KNOWN RED, externally owned, unchanged and not touched:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate` (COMPILE-time failure).

### 6. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none,
weakened none, and edited no frozen row text.  No row's evidence changed:
the repair was to a justification, not to a theorem, so nothing the matrix
cites moved.

### 7. RESUME POINT (M3d-21)

All file:line verified at `ff9bee1`.

1. ITEM 0 IS DONE.  `E1InteriorChunkValue.lean:521-555` now states the real
   discharge route.  Nothing downstream depends on the text.
2. THE NEXT BLOCK IS STILL THE MIN-CANDIDATE CONSUMER
   (`InteriorDirectory.lean:2300`).  Read section 3 BEFORE writing
   instructions: decide the (a)/(b) fork on the entry-length equality
   first, because it determines how many `none` tests the block contains
   and therefore its length, its category log and its receipt.
3. THE ARITHMETIC IT OWES is in section 4, with the shift and the
   Nat-truncation hazards written out.  Registers `100 .. 104` are TAKEN;
   THE NEXT BLOCK OPENS AT `105`.  `iIdx` (`85`) is NOT preserved across a
   summary group; `sBlock` (`100`) IS, and is the input.  Anything that
   must survive a group satisfies `GroupUntouched`
   (`E1InteriorSummaryGroup.lean:292`).
4. THEN THE SPAN BLOCKS (`:2311`, `:2329`) -- the `none` arm must branch
   PAST the summary group; both were re-read this session and both are
   `FlatStoreComputation.pure none` on that arm -- and the TWO-SPAN BLOCKS
   (`:2351`, `:2376`), where THE LEVEL READ IS THE UNCONDITIONAL HEAD of
   every append chain.  Re-confirmed at source: in both two-span
   computations the level-table read is the outermost `bind` and the whole
   span structure sits inside its `some` arm.  Violating that order
   presents as a whnf heartbeat timeout, NOT a type error, and must never
   be met by raising `maxHeartbeats`.
5. THEN the five-branch dispatch (`:2444`) and `hInterior` at
   `E1CrossBlockArm.lean:1143`.  The interior has five branches and no
   scan.  The arm's interior interface is
   `bestOfRegs (regsI mMV) (regsI mMP) = interiorValue`
   (`E1CrossBlockArm.lean:1184`) -- the consumer's output must land in that
   encoding, which is the same shift the summary cells already use.
6. ITEMS 6-7 OF THE PRIOR INVENTORY UNCHANGED AND UNBUILT: the closure
   ladder (full LCA leg at canonical-store form; whole-query glue via
   `E1RouteDecomposition` with result agreement on `(...).value` and
   POSITIONAL receipt equality on `(...).trace`; category accounting across
   ALL branches including selects-none and lca-none; the public `List Int`
   corollary; the DERIVED all-size literal step total from the category
   algebra and the caps 33/8/8 -- derive, never assert; the amended-target
   Prop with its supersession note; the validator's whole-query phase; docs
   and matrix closure; the ONE consolidated program-layout DD at the glue),
   and an EXECUTED preservation check for the interior fold -- the
   validator's phase 3h is fringe-arm only and still has no interior
   analogue.
7. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (`bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do not
   edit frozen requirement text.
8. STANDING RULES, still five.  This session adds no sixth, and adds one
   caution to rule 5: a delegation's GROUND for a premise can be sound but
   INCOMPLETE.  `maxRel` really is owed to the receipt, and acting on that
   ground alone would still have produced an unsound block, because the
   value is owed to the option structure as well (section 3).  When a
   prompt supplies the reason a thing is needed, check whether it is the
   ONLY reason before designing to it.

## M3d-21 (worker E1-R5d): the min-candidate consumer landed with all four presence tests, and the ground for the fourth is now recorded where it can be checked

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`5f5eaa5` to `d82558e`.  Green.

Mission item 1 IS DONE.  Items 2-6 are UNBUILT.  This is the sixteenth
session to land one milestone green rather than start a second it could
not finish.

### 1. THE ANCHORS HELD, WITH TWO PATH CORRECTIONS

Every anchor supplied was grepped before use, per rule 4.  All eight
`InteriorDirectory.lean` line numbers were exact (`:2277`, `:2295`,
`:2300`, `:2311`, `:2329`, `:2351`, `:2376`, `:2444`), as was
`E1CrossBlockArm.lean:1143` (`crossBlockArmProgramAt_runsTo`).

TWO DIRECTORY CORRECTIONS, both harmless to the argument but recorded so
the next session does not repeat the search:

* `MachineChunkedTableProgram.lean` is at `RMQ/Core/SuccinctSpace/`, not
  under the interior path.  `machineReadComputationAt` is at `:343` there,
  and it does read `[deadAddress]` out of range, as the delegation says.
* `RelativeSummaryCandidate.lean` is at
  `RMQ/Core/SuccinctClose/EndpointFringe/PrefixRange/`, not under
  `InteriorCandidate/`.  `bpRelativeSummaryMinCandidate` is at `:15`.

The delegation's soundness argument was checked at source rather than
taken on report, and it holds in full: the route's four-way match is at
`InteriorDirectory.lean:2293-2296`, and `bpRelativeSummaryMinCandidate`
reads `summary.1`, `summary.2.1`, `summary.2.2.2` and never
`summary.2.2.1`.

### 2. WHAT LANDED: `RMQ/Core/WordRAM/E1InteriorMinCandidate.lean`

A 21-instruction READ-FREE block simulating
`canonicalRelativeRmmMachineMinCandidateComputation`, with the
coordinator's ruling implemented as directed: ALL FOUR presence tests,
the `maxRel` test not collapsed.

`minCandidateBlock_runsTo` (`:364`) is the exact simulation.  Its result
clause is the ROUTE'S OWN EXPRESSION:

    bestOfRegs (regs' mMV) (regs' mMP) =
      (summaryOfCells cB cMn cMx cA).map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block)

with `summaryOfCells` (`:161`) written arm-for-arm as the route writes its
match, `mx` binder present and unused on the left exactly as it is there.
The `maxRel` cell therefore appears on BOTH sides of the statement and is
not an argument the theorem could drop.  Receipt is `[]`.

THREE DESIGN POINTS, all recorded at DD-20260719-015:

* `none` IS THE FALLTHROUGH.  The block installs the `none` encoding
  first and conditionally skips the value computation, mirroring
  `| _, _, _, _ => none`.  It therefore needs no unconditional jump and
  no always-nonzero register -- one instruction and one hypothesis less
  than the `brNZ fOne` idiom `candMerge3Mid` uses.
* THE SHIFT IS APPLIED LAST.  The block computes `(cB + cMn) - (span + 2)`
  and only then adds `1`.  Folding both option shifts into the constant is
  valid because `a + k - (b + k) = a - b` holds unconditionally in `Nat`;
  adding the `1` FIRST would give `(b + mn + 1) - span`, which differs
  from `(b + mn - span) + 1` at every `span > b + mn`.  This was the
  hazard section 4 of M3d-20 flagged, and it is real.
* NO REGISTER-REGISTER MULTIPLY EXISTS in the ISA (`mulConst` only), so
  the branchless masking alternative was not available; the masking trick
  that would have worked needs a dominating constant and so a bound
  hypothesis, which would have been a decorative premise.  Branching is
  also the structurally faithful choice.

Registers `105 .. 117`.  THE NEXT BLOCK OPENS AT `118`.

### 3. THE ANTI-VACUITY IS EXECUTED, AND IT TARGETS THE ACTUAL DEFECT

Rule 5 says a witness built FOR a premise defeats its purpose.  The
witness suite here is built against the MUTATION the defect class would
survive, not against the theorem's hypotheses.

`witnessOut` (`:791`) runs the real block, hosted in a real program, on
the empty store.  Four discriminators (`:811`, `:815`, `:818`, `:821`)
each run two fixtures differing in EXACTLY ONE cell and show the outputs
differ.  The `maxRel` pair is the decisive one: at
`(block, cB, cMn, cMx, cA) = (1, 10, 5, 7, 3)` the machine leaves
`(6, 6)`, and at `(1, 10, 5, 0, 3)` it leaves `(0, 0)`.  A block that
dropped the `Q + 5` test would make those two EQUAL while leaving the
trace, the read count and the exit pc untouched.

`witness_maxRel_discriminates` DEPENDS ON NO AXIOMS AT ALL -- it is pure
kernel computation.  That is the strongest form this evidence takes.

Cross-checked independently against the route's own functions:
`witness_route_value` (`:851`) evaluates
`(summaryOfCells 10 5 7 3).map (bpRelativeSummaryMinCandidate 4 2 1)` to
`some (5, 6)` through the REAL `bpSuperblockSpan` and `blockStartOf`, and
`witness_route_value_maxRelAbsent` (`:856`) evaluates the `maxRel`-absent
case to `none`.  The machine's `(6, 6)` is the `bestOfRegs` encoding of
`some (5, 6)`, so the shift arithmetic is confirmed by two independent
computations rather than by the proof alone.

Both arms' read logs are `[]` by kernel reduction (`:826`, `:830`), so the
receipt in the theorem is executed truth and not a modelling choice.  The
two arms charge DIFFERENT category logs (`:863`), so the `if` in
`minCandidateCats` is not decorative.  `witness_instantiates_theorem`
(`:838`) instantiates the main theorem at the witness fixture, discharging
every hypothesis by `rfl` against the hosting fact the witness program
itself supplies.

### 4. TWO DOCSTRINGS THIS SESSION'S OWN OUTPUT FALSIFIED

`E1InteriorSummaryGroup.lean` carried, in two places, the claim that no
consumer inspects `maxRel`'s value -- offered as the reason its bridge is
provided "anyway".  That reading is the INCOMPLETE one M3d-20 identified,
and this session's module is a consumer whose `none`/`some` split is
decided in part by that cell.  The sentences were false as written once
the consumer existed.

Both were repaired to state the option-structure ground ALONGSIDE the
receipt ground: the `summaryGroup` docstring (now `:285`) and
`geomCell_maxRel_eq_routeDecode` (now `:726`).  Docstring-only: no
theorem, statement or proof changed, and no frozen requirement text
edited.  Note that these edits shifted line numbers in that module --
`canonicalSummaryGroup_runsTo` is now `:555`, the four value bridges are
now `:694`, `:708`, `:726`, `:740`, `canonicalSummaryLayout` is `:464`,
`summaryGroup` is `:285` and `GroupUntouched` is `:305`.

### 5. VERIFICATION LEDGER

Under the `Global\RMQHeavyVerification` mutex:

    lake build RMQ RMQPaper RMQExamples      LIB_BUILD_EXIT=0
    lake build rmq_e1_machine_validate       VALIDATOR_BUILD_EXIT=0
    lake exe rmq_e1_machine_validate         VALIDATOR_RUN_EXIT=0

    Build completed successfully.
    [281/283] Built RMQ.Core.WordRAM.E1InteriorMinCandidate

Validator: `RESULT: PASS (with the whole-query comparison still OPEN)`,
`wholeQueryComparisonAvailable=false`.  Phase 3h `presFailures=0`,
`presSentinelNonZero=true`; mutation phase 4g
`mutantG_scratch_preservationFailures=36`, `mutantG_scratch_exitFailures=0`,
`mutantG_clobberedRegs=[70]`, `mutantG_isPreservationOnly=true`.  The
discriminators still bite, unchanged from M3d-20.  The interior analogue
of 3h REMAINS UNBUILT and is still owed.

`#print axioms` after a root build, importing the module DIRECTLY:

    minCandidateBlock_runsTo         [propext, Classical.choice, Quot.sound]
    summaryOfCells_eq_none           [propext, Classical.choice, Quot.sound]
    summaryOfCells_eq_some           [propext, Quot.sound]
    minCandidateBlock_fits           [propext, Quot.sound]
    minCandidateBlock_readFree       [propext]
    witness_instantiates_theorem     [propext, Classical.choice, Quot.sound]
    witness_maxRel_discriminates     does not depend on any axioms

Never `sorryAx`.  `lake env lean scripts/headline_axiom_check.lean` runs
clean.  `design_decision_check.ps1 -Strict` `DD_EXIT=0` ("checked 2
changed files"), `claim_drift_scan.ps1` `DRIFT_EXIT=0` (744 hits, 0 strict
failures, none in this session's files), `paper_topology_lint.ps1`
`TOPO_EXIT=0`.  `git diff --check` exit 0 and the committed-range form
`5f5eaa5..HEAD` exit 0 -- the inherited `B7_STEP2_WIP.patch` whitespace is
outside this range.  Hygiene `rg` over the new module is CLEAN: no
`sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe`,
`implemented_by` or Mathlib.  `maxHeartbeats` was NOT raised anywhere, and
no whnf timeout was encountered.

The thirteen build warnings are all pre-existing and in the same modules
M3d-19 and M3d-20 recorded (`SuccinctFinalRAM` x6, `E1InteriorChunkFold`,
`ReviewerReachability{Small x3, Long, Sparse}`, `BPNavigationRAM`).  The
new module emits NONE.

DD-20260719-015 CLAIMED this session.  The maximum OBSERVED before
claiming was `DD-20260719-014`, verified by scanning the tree.  The
consolidated program-layout DD is still owed at the glue.

KNOWN RED, externally owned, unchanged and not touched:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate` (COMPILE-time failure).

### 6. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none,
weakened none, and edited no frozen row text.  The rows are whole-query
scoped and this session landed a component of the interior leg, so no
row's status could move; the matrix was left untouched rather than
annotated, consistent with the fifteen prior sessions.

### 7. RESUME POINT (M3d-22)

All file:line verified at `d82558e`.

1. ITEM 1 IS DONE.  `E1InteriorMinCandidate.lean:364`
   (`minCandidateBlock_runsTo`) is the min-candidate consumer, 21
   instructions, read-free, exit `Q + 21`.  Its output is already in the
   `bestOfRegs` encoding the arm's interior interface wants
   (`E1CrossBlockArm.lean:1184`).  Registers `105 .. 117` are TAKEN; THE
   NEXT BLOCK OPENS AT `118`.
2. THE NEXT BLOCKS ARE THE SPAN BLOCKS (`InteriorDirectory.lean:2311`,
   `:2329`).  Both were re-read this session and both are
   `FlatStoreComputation.pure none` on the `none` arm, so THE `none` ARM
   MUST BRANCH PAST THE SUMMARY GROUP -- past all 156 instructions of it
   AND past the 21 of the consumer, since the span blocks call the
   consumer, not the group alone.  The composite to jump over is
   therefore 177 instructions.  This was NOT verified by construction
   this session; it is arithmetic on `summaryGroup_length = 156` and
   `minCandidateBlock_length = 21` and should be re-derived, not trusted.
3. THEN THE TWO-SPAN BLOCKS (`:2351`, `:2376`).  THE LEVEL READ IS THE
   UNCONDITIONAL HEAD of every append chain -- re-confirmed at source this
   session, in both computations the level-table read is the outermost
   `bind` and the whole span structure sits inside its `some` arm.
   Violating that order presents as a whnf heartbeat timeout, NOT a type
   error, and must never be met by raising `maxHeartbeats`.
4. THEN the five-branch dispatch (`:2444`) and `hInterior` at
   `E1CrossBlockArm.lean:1143`.  The interior has five branches and no
   scan.
5. ITEMS 6-7 OF THE PRIOR INVENTORY UNCHANGED AND UNBUILT: the closure
   ladder (full LCA leg at canonical-store form; whole-query glue via
   `E1RouteDecomposition` with result agreement on `(...).value` and
   POSITIONAL receipt equality on `(...).trace`; category accounting
   across ALL branches including selects-none and lca-none; the public
   `List Int` corollary; the DERIVED all-size literal step total from the
   category algebra and the caps 33/8/8 -- derive, never assert; the
   amended-target Prop with its supersession note; the validator's
   whole-query phase; docs and matrix closure; the ONE consolidated
   program-layout DD at the glue), and an EXECUTED preservation check for
   the interior fold -- the validator's phase 3h is fringe-arm only.
6. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (`bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do
   not edit frozen requirement text.
7. THE VALUE BRIDGE IS NOT YET WIRED TO THE CONSUMER.  This session's
   theorem is generic in the four cells, which is what lets it compose
   with the group at ANY store.  Connecting it to the ROUTE's decode
   still needs the four `geomCell_*_eq_routeDecode` bridges (now `:694`,
   `:708`, `:726`, `:740` in `E1InteriorSummaryGroup.lean`), each of
   which carries an `i < entriesLen` obligation the caller must supply.
   NOTE THE ASYMMETRY THIS CREATES: the bridges hold only at VALID
   indices, but the consumer's `none` arm is precisely the INVALID-index
   case.  Whoever composes them must supply, for the invalid case, a fact
   that `geomCell = 0` there -- which is NOT one of the four bridges and
   was not found in the tree this session.  Budget for it.
8. STANDING RULES, still five.  This session adds no sixth.  It confirms
   M3d-20's caution to rule 5 from the other side: the delegation's
   ground was incomplete, the coordinator's ruling supplied the missing
   half, and implementing to the ruling rather than to the original
   framing is what made the block sound.  When a prompt supplies a
   reason, check whether it is the ONLY reason -- and when a later
   instruction CORRECTS an earlier one, the correction is the thing to
   build to.

## M3d-22 (worker E1-R5e): Task Zero's premise was false, and the tree contained the disproof; the min-candidate leg is composed

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`88f9605` to `109eb67`.  Green.

MISSION ITEM 1 IS DONE, both halves.  Items 2-6 are UNBUILT.  This is the
seventeenth session to land one milestone green rather than start a second
it could not finish.

### 1. TASK ZERO: THE FACT I WAS SENT TO PROVE IS FALSE

The delegation stated that composing the four `geomCell_*_eq_routeDecode`
bridges with the min-candidate consumer's `none` arm needs a
"`geomCell = 0` at invalid indices" fact, absent from the tree, and told
me to budget for proving it.  Rule 4 says grep before acting.  Two
findings, both checked at source rather than taken on report:

FIRST, THE FACT IS NOT NEEDED.  `geomCell_eq_routeDecode` (`:674`) takes
only `hcap` and `hexact`, and `hexact` constrains NON-FINAL chunks:
`forall j, j + 1 < chunkIters ... i -> ...`.  Out of range
`chunkIters entriesLen chunkCount i = 1` (`chunkIters`,
`E1InteriorChunkFold.lean:135`), so `j + 1 < 1` is uninhabited and the
premise is VACUOUS.  The generic bridge therefore applies at invalid
indices with no store fact at all.

SECOND, THE FACT IS FALSE.  `stageCell`
(`E1InteriorSummaryGroup.lean:221`) is `0` out of range only when
`chunkBad store segment deadAddress 1 <> 0` -- i.e. only when the dead
address is unreadable IN THE STORE.  `chunkFoldWitness_path_dead`
(`E1InteriorChunkFold.lean:1947`), an `rfl`-checked theorem PREDATING
this session, runs the real fold at index `5` past `entriesLen = 3` and
leaves `cOut = 2`, i.e. `some 1`, NOT `0` -- because `witnessStore` holds
a word at the dead address `99`.  Whoever took the delegated route would
have spent the session trying to prove something false of that store, and
the counterexample was already in the file they would have been editing.

So the asymmetry the predecessor flagged for the successor to budget for
does not exist to be budgeted for.  The four bridges are now
UNCONDITIONAL IN THE INDEX (`:737`, `:753`, `:773`, `:789`); the `hvalid`
hypothesis is GONE.  This is a strengthening -- a hypothesis removed, no
statement narrowed -- and the four had no callers, so nothing broke.

Recorded at DD-20260719-016.  New: `chunkIters_of_invalid`
(`E1InteriorChunkFold.lean:1787`), the complement of `chunkIters_pos`
(`:1767`), and `geomCell_eq_routeDecode_of_invalid`
(`E1InteriorSummaryGroup.lean:717`).

### 2. THE COMPOSITION (mission item 1, second half)

`summaryMinCandidate_runsTo` (`E1InteriorMinCandidate.lean:924`): the
summary group followed by the consumer, `156 + 21 = 177` instructions,
exit `Q + 177`.  Receipt is the group's four route event lists in the
route's bind order and NOTHING ELSE -- the consumer is read-free, so
composition adds no event.  Category log is the group's followed by
`minCandidateCats`, whose arm is selected by the ROUTE's own summary
being `some`.  NO VALIDITY HYPOTHESIS AND NO STORE HYPOTHESIS.  That is
the whole point of the unconditional bridges: the `none` arm is reached
at indices the interior's branch structure does not bound in advance, so
a composite carrying `i < entriesLen` per read would have been unusable
on exactly the arm it most needs to cover.

`routeDecodedSummary` (`:898`) is NAMED CAREFULLY and its docstring says
what it is NOT.  It is the summary assembled from the four ROUTE DECODES,
which is what the value bridges deliver.  Equality with the value of
`canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) is a FURTHER step and is NOT claimed.
See section 6 item 2.

### 3. ANTI-VACUITY, EXECUTED, DEPENDING ON NO AXIOMS AT ALL

* `chunkIters_witness_discriminates` (`E1InteriorChunkFold.lean:1968`):
  the count is `1` out of range and `2` at a valid index of the same
  two-chunk table, so `chunkIters_of_invalid` DISCRIMINATES rather than
  reporting a constant.
* `outOfRange_cell_not_always_zero` (`:1982`): the zero claim refuted by
  kernel computation.  This is what makes DD-20260719-016 a real fork
  rather than a preference.
* `summaryMinCandidate_premises_satisfiable`
  (`E1InteriorMinCandidate.lean:1018`) discharges rule 1: `hHost` and
  `hBlock` JOINTLY satisfiable at the intended instantiation, the theorem
  instantiated at the self-hosting leg (`:1004`) with `sBlock` actually
  holding `block`, existential carried to a concrete consequence.

The first two depend on NO AXIOMS -- pure kernel computation.

A LIMIT WORTH STATING.  I did NOT run the composite end-to-end on a
numeric fixture.  The summary group's reads go through `machineWordBits`,
hence `Nat.log2`, which is well-founded recursion the KERNEL cannot
evaluate; `rfl`/`decide` fail on numeric fixtures there.  So the
predecessor's `witness_maxRel_discriminates` model does not extend to the
composite, and the discriminating content stays witnessed at the consumer
level where it is kernel-reachable.

### 4. VERIFICATION LEDGER

Under the `Global\RMQHeavyVerification` mutex:

    lake build RMQ RMQPaper RMQExamples   LIB_BUILD_EXIT=0
    lake build rmq_e1_machine_validate    VALIDATOR_BUILD_EXIT=0
    lake exe rmq_e1_machine_validate      VALIDATOR_RUN_EXIT=0

    [280/283] Built RMQ.Core.WordRAM.E1InteriorSummaryGroup
    [281/283] Built RMQ.Core.WordRAM.E1InteriorMinCandidate
    [282/283] Built RMQ
    Build completed successfully.

0 errors; 13 warnings, all pre-existing and in the modules M3d-19..21
recorded.  The changed modules emit NONE.

Validator: `RESULT: PASS (with the whole-query comparison still OPEN)`,
`wholeQueryComparisonAvailable=false`, `presFailures=0`,
`presSentinelNonZero=true`, `mutantG_scratch_preservationFailures=36`,
`mutantG_scratch_exitFailures=0`, `mutantG_clobberedRegs=[70]`,
`mutantG_isPreservationOnly=true`.  UNCHANGED from M3d-21, as expected:
this session added no machine block, only a composition of two existing
ones.  The interior analogue of phase 3h REMAINS UNBUILT and is still
owed.

`#print axioms` after a root build, importing the modules DIRECTLY:

    chunkIters_of_invalid                    does not depend on any axioms
    chunkIters_witness_discriminates         does not depend on any axioms
    outOfRange_cell_not_always_zero          does not depend on any axioms
    geomCell_eq_routeDecode_of_invalid       [propext, Classical.choice, Quot.sound]
    geomCell_baseline_eq_routeDecode         [propext, Classical.choice, Quot.sound]
    geomCell_minRel_eq_routeDecode           [propext, Classical.choice, Quot.sound]
    geomCell_maxRel_eq_routeDecode           [propext, Classical.choice, Quot.sound]
    geomCell_argOffset_eq_routeDecode        [propext, Classical.choice, Quot.sound]
    summaryMinCandidate_runsTo               [propext, Classical.choice, Quot.sound]
    summaryMinCandidate_hosted_self          [propext, Classical.choice, Quot.sound]
    summaryMinCandidate_premises_satisfiable [propext, Classical.choice, Quot.sound]

Never `sorryAx`.  `lake env lean scripts/headline_axiom_check.lean` runs
clean.  `design_decision_check.ps1 -Strict` `DD_EXIT=0` ("checked 4
changed files"), `claim_drift_scan.ps1` `DRIFT_EXIT=0` (746 hits, 0
strict failures), `paper_topology_lint.ps1` `TOPO_EXIT=0`.
`git diff --check` exit 0.  Hygiene `rg` over the three changed modules is
CLEAN: no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, `implemented_by` or Mathlib.  `maxHeartbeats` was NOT raised
anywhere, and NO whnf timeout was encountered.

DD-20260719-016 CLAIMED.  Maximum OBSERVED before claiming was
`DD-20260719-015`, verified by scanning the tree.  The consolidated
program-layout DD is still owed at the glue.

KNOWN RED, externally owned, unchanged and not touched:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate` (COMPILE-time failure).

### 5. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none,
weakened none, and edited no frozen row text.  The rows are whole-query
scoped and this session landed a component of the interior leg, so no
row's status could move; the matrix was left untouched rather than
annotated, consistent with the sixteen prior sessions.

### 6. RESUME POINT (M3d-23)

All file:line verified at `109eb67`.

1. MISSION ITEM 1 IS DONE.  `summaryMinCandidate_runsTo`
   (`E1InteriorMinCandidate.lean:924`) is the composed leg, 177
   instructions, exit `Q + 177`, no validity and no store hypothesis.
   Registers `105 .. 117` are TAKEN; THE NEXT BLOCK OPENS AT `118`.
2. THE A-TO-B LINK IS THE NEXT NATURAL STEP, AND IT IS SHORT.  Nothing in
   the tree equates `geomRouteDecode` with the run value of
   `canonicalRelativeRmmMachineReadNatComputation`
   (`InteriorDirectory.lean:2132`, a pure alias for
   `machineReadComputationAt`).  This was searched exhaustively this
   session; `geomRouteDecode` has six occurrences tree-wide, all in
   `E1InteriorSummaryGroup.lean`.  The chain, each step verified to
   exist: unfold the alias; unfold `machineReadComputationAt`
   (`MachineChunkedTableProgram.lean:343`); push `.value` through
   `map_run_value` (`:199`, `@[simp]`); apply `readMany_run_value`
   (`:213`, `@[simp]`) which gives `addresses.map (fun a => store a)` --
   THE DECISIVE STEP; unfold `flatWordStoreOfReadStore`
   (`InteriorRAM.lean:170`), which IS `store.readWord? segment a`
   definitionally; identify the address lists -- `chunkAddrs`
   (`E1InteriorChunkFold.lean:123`) against
   `fixedWidthNatTableMachineFootprintAt`
   (`MachineChunkedTableProgram.lean:332`), which at
   `canonicalSummaryLayout` agree BY `rfl` because that layout DEFINES
   `chunkCount` as the route's `fixedWidthNatTableMachineChunkCount` and
   `entriesLen` as the route's entry-list length; then
   `fixedWidthNatTableMachineDecode` (`MachineChunkedTable.lean:215`)
   applies to the same list on both sides.  NO CAP HYPOTHESIS on this
   path -- `chunkAddrs_eq_consecutive`'s `hcap` is a DIFFERENT equation,
   already consumed inside `geomCell_eq_routeDecode`.
   DO NOT USE `interiorReadNat_route_atom`
   (`E1InteriorReadBlock.lean:443`): it is the single-chunk atom and
   carries `0 < width`, `width <= wordSize`, which fail at the interior's
   reachable multi-chunk shapes.  The summary group's own header says so
   at `E1InteriorSummaryGroup.lean:33-40`.
3. THEN THE SPAN BLOCKS (`InteriorDirectory.lean:2311`, `:2329`).  Both
   are `FlatStoreComputation.pure none` on the `none` arm, so THE `none`
   ARM MUST BRANCH PAST the composite -- 177 instructions, now a single
   named object rather than arithmetic on two.  RE-DERIVE, do not trust:
   it is `summaryGroup_length = 156` plus `minCandidateBlock_length = 21`.
4. THEN THE TWO-SPAN BLOCKS (`:2351`, `:2376`).  THE LEVEL READ IS THE
   UNCONDITIONAL HEAD of every append chain.  Violating that order
   presents as a whnf heartbeat timeout, NOT a type error, and must never
   be met by raising `maxHeartbeats`.
5. THEN the five-branch dispatch (`:2444`) and `hInterior` at
   `E1CrossBlockArm.lean:1143`.  The interior has five branches and no
   scan.
6. THE CLOSURE LADDER AND THE OWED PRESERVATION CHECK are unchanged and
   unbuilt: full LCA leg at canonical-store form; whole-query glue via
   `E1RouteDecomposition` with result agreement on `(...).value` and
   POSITIONAL receipt equality on `(...).trace`; category accounting
   across ALL branches including selects-none and lca-none; the public
   `List Int` corollary; the DERIVED all-size literal step total from the
   category algebra and the caps 33/8/8 -- derive, never assert; the
   amended-target Prop with its supersession note; the validator's
   whole-query phase; docs and matrix closure; the ONE consolidated
   program-layout DD at the glue; and an EXECUTED preservation check for
   the interior fold -- the validator's phase 3h is fringe-arm only.
7. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (`bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do
   not edit frozen requirement text.
8. A STALE NAME FOUND IN PASSING, NOT FIXED because it is outside this
   session's scope and touching it would have mixed concerns: the module
   docstring of `E1InteriorChunkStore.lean` at `:31` refers to
   `probeShape_unbounded_agreement_fails`, but the theorem is named
   `unbounded_agreement_refuted` (`:537`).  Prose only; no theorem
   affected.
9. STANDING RULES, still five.  This session adds no sixth.  It supplies
   the sharpest case yet for rule 4, from a direction the prior sessions
   did not hit: the delegation was not merely imprecise about what the
   tree CONTAINS, it was wrong about what is TRUE, and the disproof was
   an existing `rfl`-checked theorem in the very file the work would have
   touched.  A supplied premise gets grepped; so does a supplied
   OBLIGATION.  When a prompt says "if it genuinely is absent, prove it",
   check first whether it is absent BECAUSE IT IS FALSE.

## M3d-23 (worker E1-R5f): the A-to-B link, landed parametrically so it could be executed

Branch `claude/b1-b2-charged-fringe-tables`, base `d90b062`, from HEAD
`abfb681`.  Green.

MISSION ITEM 1 (the A-to-B link) IS DONE.  Items 2-6 are UNBUILT.  This is
the eighteenth session to land one milestone green rather than start a
second it could not finish.

### 1. THE INHERITED CLAIMS, GREPPED BEFORE BUDGETING

Rule 4, applied to the delegation and to the predecessor's inventory.  The
substantive claims held; one count did not.

CONFIRMED AT SOURCE, all at `abfb681`: `map_run_value`
(`MachineChunkedTableProgram.lean:199`) and `readMany_run_value` (`:213`),
both `@[simp]`; `machineReadComputationAt` (`:343`);
`fixedWidthNatTableMachineFootprintAt` (`:332`);
`canonicalRelativeRmmMachineReadNatComputation`
(`InteriorDirectory.lean:2132`), a pure alias; `chunkAddrs`
(`E1InteriorChunkFold.lean:123`); `flatWordStoreOfReadStore`
(`InteriorRAM.lean:170`); `fixedWidthNatTableMachineDecode`
(`MachineChunkedTable.lean:215`); the four bridges unconditional at
`E1InteriorSummaryGroup.lean:737`, `:753`, `:773`, `:789`.

THE WARNING ABOUT `interiorReadNat_route_atom` IS ACCURATE.
`E1InteriorReadBlock.lean:443` does carry `0 < width` and
`width <= wordSize`, and it is the ONLY site in `RMQ/Core/WordRAM` that
touches `machineReadComputationAt ... .run`.  Nothing linked that run value
to `geomRouteDecode`; the gap was real.

ONE COUNT WAS WRONG, harmlessly.  The inventory says `geomRouteDecode` has
"six occurrences tree-wide, all in `E1InteriorSummaryGroup.lean`".  It has
FOURTEEN, in TWO files -- `E1InteriorMinCandidate.lean` carries eight, at
`:64`, `:111`, `:152` and `:901`-`:910`.  The count was taken before that
session's own composition landed and was not refreshed.  It changed no
conclusion: the searched-for equation was genuinely absent.

RE-DERIVED, NOT COPIED, as instructed: `summaryGroup_length = 156`
(`E1InteriorSummaryGroup.lean:299`, by `simp`) and
`minCandidateBlock_length = 21` (`E1InteriorMinCandidate.lean:241`,
`rfl`), so the composite the span blocks must branch past is 177 -- and
`summaryMinCandidate_runsTo` does exit at `Q + 177`.

### 2. THE LINK, AND WHY IT IS PARAMETRIC

`routeDecode_eq_machineReadComputation_value`
(`E1InteriorSummaryGroup.lean:879`) is the core: the option-shifted decode
of `chunkAddrs` IS the option-shifted `.value` of
`machineReadComputationAt`, given only that the geometry's `entriesLen` and
`chunkCount` are the route's own.  It takes `wordSize` as an ORDINARY
PARAMETER and mentions no `shape`.

`geomRouteDecode_eq_readComputation_value` (`:904`) is the shape-level
corollary, and the four `geomCell_*_eq_readComputation_value` (`:935`,
`:951`, `:967`, `:983`) compose it with the four bridges.  ALL THREE
HYPOTHESES ARE `rfl` AT EVERY ONE OF THE FOUR -- the predecessor's
prediction that the address lists agree by `rfl` at
`canonicalSummaryLayout` is confirmed by construction.

THE DECISIVE STEP IS DEFINITIONAL, NOT ARITHMETIC.
`chunkAddrs_eq_machineAddresses` (`:855`) is proved by `subst; subst; rfl`: both
sides split on the same validity test, and the valid arm of `chunkAddrs` IS
`(consecutiveWordIndices (i * count) count).map (base + .)`, which is
exactly `fixedWidthNatTableMachineFootprintAt` unfolded.

NO CAP HYPOTHESIS ENTERS, as predicted.  `chunkAddrs_eq_consecutive`'s
`hcap` relates `chunkAddrs` to what the MACHINE's fold generates and was
already consumed inside `geomCell_eq_routeDecode`.  The link never mentions
the fold.  Nothing in it bounds `width`, so it is not the single-chunk atom
in disguise.

WHY PARAMETRIC IS A FORK AND NOT A PREFERENCE (DD-20260719-017).  The link
is an equation between two `match`es, a shape that can hold because both
sides are constant, so it owes an executed witness.  At shape level it
CANNOT have one: the word size runs through `machineWordBits`, hence
`Nat.log2`, well-founded recursion the kernel cannot evaluate.  M3d-22
established that boundary.  Parametrising the word size moves the SAME
equation into kernel-reachable territory; the shape-level form is an
instance of it, so the fixtures exercise the equation the interior uses
rather than an analogue.

### 3. ANTI-VACUITY, EXECUTED, IN THE MULTI-CHUNK REGIME

The fixture is three entries at width `20`, word size `8`, hence
`fixedWidthNatTableMachineChunkCount 20 8 = 3` chunks per cell -- the
regime where `interiorReadNat_route_atom` does NOT apply.

* `linkWitness_executed` (`:1079`) evaluates BOTH sides at four indices,
  `[2, 3, 0, 6]` on each: a fully present three-chunk cell, a second
  differing in one chunk, a cell with a missing chunk, and the dead path.
* `linkWitness_discriminates_content` (`:1090`) is the right-shape /
  wrong-content guard in the `witness_maxRel_discriminates` model.  Cells
  `0` and `1` have the SAME shape -- three present chunks each -- and
  differ only in stored bits.  The link separates them.
* `linkWitness_chunkCount_load_bearing` (`:1097`) and
  `linkWitness_entriesLen_load_bearing` (`:1103`): a wrong `chunkCount`
  reads a shorter address list, a wrong `entriesLen` diverts the index to
  the dead path, each decoding a different value.  Neither hypothesis is
  decorative.
* `linkWitness_link_instantiated` (`:1070`) discharges rule 1: both
  hypotheses JOINTLY satisfiable at a real instantiation, carried to a
  concrete consequence rather than left existential.

A LIMIT, STATED RATHER THAN GLOSSED.  These fixtures run the link at
concrete parameters, NOT at the canonical store, where `Nat.log2` still
blocks the kernel.  The boundary M3d-22 established has not moved; what
this session shows is that the boundary was a property of the STATEMENT's
shape, not of the equation, and that restating it parametrically recovers
executability without weakening anything.

### 4. VERIFICATION LEDGER

Under the `Global\RMQHeavyVerification` mutex:

    lake build RMQ RMQPaper RMQExamples   Build completed successfully.
    lake build rmq_e1_machine_validate    Build completed successfully.
    lake exe rmq_e1_machine_validate      VALIDATOR_RUN_EXIT=0

    [280/283] Built RMQ.Core.WordRAM.E1InteriorSummaryGroup
    [281/283] Built RMQ.Core.WordRAM.E1InteriorMinCandidate
    [282/283] Built RMQ

0 errors; 13 warnings, ALL pre-existing and none in the changed module.

Validator: `RESULT: PASS (with the whole-query comparison still OPEN)`,
`wholeQueryComparisonAvailable=false`, `presFailures=0`,
`presSentinelNonZero=true`, `mutantG_scratch_preservationFailures=36`,
`mutantG_scratch_exitFailures=0`, `mutantG_clobberedRegs=[70]`,
`mutantG_isPreservationOnly=true`.  UNCHANGED from M3d-22, as expected:
this session added no machine block, only an equation between two existing
descriptions of one read.  THE INTERIOR ANALOGUE OF PHASE 3h REMAINS
UNBUILT AND IS STILL OWED.

`#print axioms` after a root build, importing the module DIRECTLY:

    chunkAddrs_eq_machineAddresses            does not depend on any axioms
    linkWitness_chunkCount_load_bearing       does not depend on any axioms
    linkWitness_entriesLen_load_bearing       does not depend on any axioms
    routeDecode_eq_machineReadComputation_value  [propext, Quot.sound]
    linkWitness_link_instantiated             [propext, Quot.sound]
    linkWitness_executed                      [propext, Quot.sound]
    linkWitness_discriminates_content         [propext, Quot.sound]
    geomRouteDecode_eq_readComputation_value  [propext, Classical.choice, Quot.sound]
    geomCell_baseline_eq_readComputation_value   [propext, Classical.choice, Quot.sound]
    geomCell_minRel_eq_readComputation_value     [propext, Classical.choice, Quot.sound]
    geomCell_maxRel_eq_readComputation_value     [propext, Classical.choice, Quot.sound]
    geomCell_argOffset_eq_readComputation_value  [propext, Classical.choice, Quot.sound]

Never `sorryAx`.  `maxHeartbeats` was NOT raised anywhere, and NO whnf
timeout was encountered.

DD-20260719-017 CLAIMED.  Maximum OBSERVED before claiming was
`DD-20260719-016`, verified by scanning the tree.  The consolidated
program-layout DD is still owed at the glue.

KNOWN RED, externally owned, unchanged and not touched:
`scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`,
`lake exe rmq_succinct_classic_validate` (COMPILE-time failure).

### 5. MATRIX STATUS AT YIELD

All eleven rows REQ-E1-01..11 remain OPEN.  This session closed none,
weakened none, and edited no frozen row text.  The rows are whole-query
scoped and this session landed a component of the interior leg, so no
row's status could move; the matrix was left untouched rather than
annotated, consistent with the seventeen prior sessions.

### 6. RESUME POINT (M3d-24)

All file:line verified at this session's HEAD.

1. MISSION ITEM 1 IS DONE, BOTH HALVES.  The four
   `geomCell_*_eq_readComputation_value`
   (`E1InteriorSummaryGroup.lean:935`, `:951`, `:967`, `:983`) state the
   machine's saved cell as the value of the computation the ROUTE runs,
   with no validity, cap or store hypothesis.  The parametric core they
   rest on is `routeDecode_eq_machineReadComputation_value` (`:879`).
   Registers `105 .. 117` are TAKEN; THE NEXT BLOCK OPENS AT `118`.
2. WHAT IS STILL NOT CLAIMED, AND IS THE NEXT NATURAL STEP.  The four link
   ONE read each.  `routeDecodedSummary` (`E1InteriorMinCandidate.lean:898`)
   equals the value of `canonicalRelativeRmmMachineSummaryComputation`
   (`InteriorDirectory.lean:2277`) is a FURTHER step: that computation is a
   three-deep `FlatStoreComputation.bind` closing over a `map`
   (`:2283`-`:2298`), so the step is `bind_run`
   (`MachineChunkedTableProgram.lean:191`, `@[simp]`) plus the four links,
   with the tuple arm decided by the `match` at `:2294`-`:2296`.  This is
   short and I did not reach it.
3. THEN THE SPAN BLOCKS (`InteriorDirectory.lean:2311`, `:2329`).  Both are
   `FlatStoreComputation.pure none` on the `none` arm, so THE `none` ARM
   MUST BRANCH PAST the composite -- 177 instructions.  RE-DERIVED THIS
   SESSION and confirmed: `summaryGroup_length = 156`
   (`E1InteriorSummaryGroup.lean:299`) plus `minCandidateBlock_length = 21`
   (`E1InteriorMinCandidate.lean:241`), and `summaryMinCandidate_runsTo`
   (`:924`) exits at `Q + 177`.
4. THEN THE TWO-SPAN BLOCKS (`:2351`, `:2376`).  THE LEVEL READ IS THE
   UNCONDITIONAL HEAD of every append chain.  Violating that order presents
   as a whnf heartbeat timeout, NOT a type error, and must never be met by
   raising `maxHeartbeats`.
5. THEN the five-branch dispatch (`:2444`) and `hInterior` at
   `E1CrossBlockArm.lean:1143`.  The interior has five branches and no scan.
6. THE CLOSURE LADDER AND THE OWED PRESERVATION CHECK are unchanged and
   unbuilt: full LCA leg at canonical-store form; whole-query glue via
   `E1RouteDecomposition` with result agreement on `(...).value` and
   POSITIONAL receipt equality on `(...).trace`; category accounting across
   ALL branches including selects-none and lca-none; the public `List Int`
   corollary; the DERIVED all-size literal step total from the category
   algebra and the caps 33/8/8 -- derive, never assert; the amended-target
   Prop with its supersession note; the validator's whole-query phase; docs
   and matrix closure; the ONE consolidated program-layout DD at the glue;
   and an EXECUTED preservation check for the interior fold -- the
   validator's phase 3h is fringe-arm only.
7. THE M7 DOC CLAIM is scoped to QUERY TIME with construction-time
   computation carved out as preprocessing (`bpSparseLevelCell`,
   `SparseLevelTable.lean:55`).  Do not write it until the interior leg
   exists.  The stale frozen-row anchor is a NOTE, already appended; do not
   edit frozen requirement text.
8. THE STALE NAME AT `E1InteriorChunkStore.lean:31` IS STILL THERE, and
   still correctly deferred: the docstring cites
   `probeShape_unbounded_agreement_fails`, but the theorem is
   `unbounded_agreement_refuted` (`:537`).  I did not edit that file, and
   the standing instruction is to fold it in only when already editing it.
   Prose only; no theorem affected.
9. STANDING RULES, still five.  This session adds no sixth.  It sharpens
   rule 3 from a new direction: the boundary M3d-22 hit -- "this quantity
   is computable but the kernel cannot reach it" -- was a property of the
   STATEMENT's shape rather than of the mathematics.  Before accepting that
   a claim cannot be executed, check whether a parametric restatement makes
   it executable without weakening it.  Here it did, and the shape-level
   claim survives as a corollary of the executable one.

### 7. SUPPLEMENT (same session, second commit): the summary TUPLE, and the trap that nearly cost the step

Sections 1-6 above were written at commit `9c66c29`, where the session's
assigned milestone was complete.  Budget remained, so the step section 6
item 2 identified as "short and I did not reach it" was attempted.  It
landed.  ITEM 2 OF THAT RESUME POINT IS THEREFORE SUPERSEDED by this
section; the rest of the resume point stands.

`routeDecodedSummary_eq_summaryComputation_value`
(`E1InteriorMinCandidate.lean:1067`): the summary tuple assembled from the
four route decodes IS the value of
`canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`), at the canonical store and layout, with NO
validity, cap or store hypothesis.

THE LINE NUMBERS IN SECTIONS 1-6 WERE CORRECTED, NOT LEFT.  The refactor
below inserted a definition into `E1InteriorSummaryGroup.lean` and shifted
every theorem after it.  The citations written at `9c66c29` were re-checked
against the file and updated in place; the numbers in sections 1-6 are the
CURRENT ones.

### 7a. THE TRAP: AN INLINE `match` IS NOT A SMALL VERSION OF A NAMED ONE

The step should have been immediate -- `summaryOfCells` inverts the shift
through `cellOpt` (`E1InteriorMinCandidate.lean:153`), and the route's
tuple `match` (`InteriorDirectory.lean:2294`-`:2296`) is the same four-way
split.  It was not.

The links originally stated the option-shift as an INLINE
`match v with | none => 0 | some x => x + 1`.  An inline `match` elaborates
to a FRESH AUXILIARY MATCHER PER DECLARATION.  So the inversion lemma
stated in the consumer was DEFEQ to the goal and STILL DID NOT FIRE --
`simp` saw two different functions.  The symptom is an "unsolved goals"
error whose goal looks character-for-character like something `simp` should
already have closed, which is a misleading symptom: it invites raising
`maxHeartbeats` or piling on `simp` lemmas, neither of which can work.

THE FIX WAS TO NAME THE SHIFT.  `optShift`
(`E1InteriorSummaryGroup.lean:845`) is defined once; the links state their
conclusions with it; `cellOpt_optShift`
(`E1InteriorMinCandidate.lean:1057`) is the `simp` inversion that actually
applies.  The change is DEFINITIONAL -- `optShift v` is defeq to the inline
match it replaced -- so no statement moved, and the four canonical
corollaries and all five anti-vacuity fixtures went through the refactor
unchanged in content.  Recorded at DD-20260719-018, which also records the
general rule: a wrapper CONSUMERS must invert belongs in a named definition
with a named inversion lemma.

`maxHeartbeats` was NOT raised and NO whnf timeout was encountered.  The
proof closes with the four links, the shift inversion,
`FlatStoreExecution.append`'s value projection, and a final `rfl` for the
defeq spellings of the four bases and `blocksPerSuper`.

### 7b. A SCOPE NOTE CORRECTED RATHER THAN LEFT TO ROT

Three places asserted this equality was NOT claimed, and all three were
made false by this session's own work.  All three were corrected:
the `routeDecodedSummary` docstring (`E1InteriorMinCandidate.lean:889`),
now carrying an explicit SUPERSEDED note rather than a silent rewrite;
DD-20260719-017's closing paragraph, superseded in DD-20260719-018 rather
than edited away; and resume item 2 above, superseded by this section.

WHAT IS STILL NOT CLAIMED, and the name again invites over-reading: this is
the tuple's VALUE.  POSITIONAL RECEIPT EQUALITY for the four reads in the
route's bind order is a SEPARATE obligation and is NOT claimed here.  That
is the next step, and it is the one the "right shape, wrong content"
defect class bites hardest -- a receipt list in the right order with a
stale head passes every length and read-count check.

### 7c. VERIFICATION LEDGER (second commit)

Under the `Global\RMQHeavyVerification` mutex, re-run in full after the
refactor:

    lake build RMQ RMQPaper RMQExamples   LIB_BUILD_EXIT=0
    lake build rmq_e1_machine_validate    VALIDATOR_BUILD_EXIT=0
    lake exe rmq_e1_machine_validate      VALIDATOR_RUN_EXIT=0

Validator counts UNCHANGED again, and for the same reason: no machine block
was added.  `RESULT: PASS (with the whole-query comparison still OPEN)`,
`presFailures=0`, `presSentinelNonZero=true`,
`mutantG_scratch_preservationFailures=36`, `mutantG_clobberedRegs=[70]`,
`mutantG_isPreservationOnly=true`.  THE INTERIOR ANALOGUE OF PHASE 3h IS
STILL UNBUILT AND STILL OWED.

`#print axioms`, after a root build, importing the modules DIRECTLY:

    optShift-based links, all twelve       unchanged from section 4
    cellOpt_optShift                       does not depend on any axioms
    routeDecodedSummary_eq_summaryComputation_value
                                           [propext, Classical.choice, Quot.sound]

Never `sorryAx`.  DD-20260719-018 CLAIMED; maximum OBSERVED before claiming
was `DD-20260719-017`, this session's own earlier entry, verified by
scanning the tree.

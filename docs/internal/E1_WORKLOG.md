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
  REQ-E1-02 certificate for the 60-instruction block â€” register bank,
  segments `G..G+4`, immediates, mul/div constants
  (`WS`/`BPS`/`2^c`/`c+1`/`2*c+2`/`2`, variable divisors positive â€” `c`
  needs the route's `bpFringeChunkBits_pos`), branch targets
  `< 2^w` given `28 <= 2^w`, `G+4 < 2^w`, `L < 2^w`, `0 < c`,
  `0 < WS < 2^w`, `0 < BPS < 2^w`, `2^c < 2^w`, `2*c+2 < 2^w`,
  `B+60 < 2^w`.  (Flattening gotcha: `List.mem_append` leaves the
  disjunction grouped per segment; add `or_assoc` to the simp set before
  the 60-way `rcases`.)
- `rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean`): the M3c
  store-swap glue â€” for every shape/base/position the hosted block runs
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
  register NUMERALS (`r â‰  22`), not the abbrevs (`r â‰  sA`) - omega does
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
  eliminates `LB` (not `pc`), breaking later explicit `LB` references â€”
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
  `r <= 8 âˆ¨ 10 <= r <= 16 âˆ¨ 24 <= r <= 26 âˆ¨ 28 <= r` â€” the dense leg
  must keep `rWrd`/samples across a fold); 32-instr
  `rankAtSegmentBlock A G c` (7-instr register-input init `A..A+6`,
  loop `A+7..A+30`, back edge `A+31`); frozen `rankAtSegmentCats`
  (derived `7 + 25 * count`); `rankAtSegmentBlock_runsTo` (inputs: rOne/
  rC/rEight pinned, `rE = bpWordRankEffLimit w limit`,
  `rR = bitsToNatLE w`; receipts positionally equal to the atomic fold
  trace, value in `rVal`); width certificate `rankAtSegmentBlock_fits`
  (32 arms, branch target `A+7`).
- Technique: init-only preservation hypotheses must ALSO be stated on
  register numerals (`r â‰  22 âˆ§ ...`), instantiated with `(by decide)` at
  abbrev call sites â€” same omega-opacity gotcha as loop preservation.
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
  provided in the CONDITION'S orientation (`(10 : Nat) â‰  F1` for address
  preservation, `F1 â‰  F2` for later-write skips over the queried
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
    `(r <= 8 âˆ¨ 28 <= r) âˆ§ r â‰  38` (the legs own `xBPos`).  Entry
    fields arrive as shifted-encode hypotheses
    (`regs0 xSF1 = super.baseOccurrence + 1` etc.); seed presence +
    offset bound are route-side hypotheses for canonical discharge.
  - Width certificates `longLegBlock_fits`/`sparseLegBlock_fits`
    (delegate the rank block; `first`-combinator arms).
- Gotcha: `relativeReadBlock_runsTo`'s value clause uses WordRAM's
  `bitsToNatLE`, the route uses `SuccinctSpace.bitsToNatLE` - convert
  with `funext SuccinctSpace.WordRAMBridge.bitsToNatLE_eq` and
  `rw [â† hfn]` (simp cannot rewrite the unapplied function under
  `Option.map`).
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green; hygiene rg clean.

## M3c-6b: dense-leg preservation strengthened to the pinned bank

- Inherited uncommitted work from the R4g session (cut off mid-commit by
  a usage limit), verified and landed here unchanged.
- `E1DenseSelectBlock.lean`: the register-preservation clauses of
  `denseHeadBlock_runsTo_present` and `denseSelectLegBlock_runsTo` are
  strengthened from `(âˆ€ r, (24 â‰¤ r âˆ§ r â‰¤ 26) âˆ¨ 28 â‰¤ r â†’ regsF r =
  regs0 r)` to `(âˆ€ r, r â‰¤ 8 âˆ¨ (24 â‰¤ r âˆ§ r â‰¤ 26) âˆ¨ 28 â‰¤ r â†’ regsF r =
  regs0 r)`, with the internal `h6bank` hypothesis widened to match.
- WHY (needed downstream, not cosmetic): the top-level select dispatch
  calls the dense leg with the pinned constants (`rOne`, `rZero`, the
  per-shape constant registers) live in `0..8`; without this clause the
  dispatch would have to re-pin them after every leg call.  The proof
  cost was nil - `h6pres`/`h5pres` already covered `r â‰¤ 8`, so only the
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
    those legs preserve only `r â‰¤ 8 âˆ¨ 28 â‰¤ r`, and `rOne = 24` is
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
    `dispatchLocalSlot_runsTo`, `dispatchDenseBase_runsTo` â€” the four
    straight-line segments (all first-try green).
  - `dispatchNoneTail_runsTo`, `dispatchJump_runsTo` (the two tail
    idioms), `selectCloseBlockAt` (the block instantiated at the accepted
    layout/data â€” a large readability win for every later statement).
  - `selectCloseBlock_prefix_runsTo`: the shared in-range prefix
    (prologue, taken range branch, super slot, super entry 4-read) to
    `A + 22`, receipts POSITIONALLY EQUAL to the accepted super
    entry-table read events, four shifted field decodes in the super
    bank, miss indicator in `rA`, pinned constants live, `r â‰¤ 7 âˆ¨ r = 28`
    preserved.
  - `entryFields_of_some`: inversion of the accepted 4-read decode â€” a
    present entry pins each shifted field register to `field + 1`
    (exactly the leg blocks' hypothesis shape, and a zero miss indicator
    for free).  Works for both the super and local tables.
  - `selectCloseBlock_runsTo_outOfRange` and
    `selectCloseBlock_runsTo_superMiss`: the two `none`-answering
    branches, full receipts/value/cats/preservation against
    `bpChunkedSelectTraceResultWithStore`.
- Gotchas (new):
  - `omega` cannot see through the register ABBREVS: `28 â‰¤ xSF1` and
    `r â‰  xSF1` both fail.  Use `by decide` for CLOSED side conditions,
    and put explicit `have nSF1 : xSF1 = 30 := rfl` facts in context when
    the register is universally quantified (omega then treats the abbrev
    as an atom with a known value).
  - `RunsTo.brNZ_taken`'s condition hypothesis is stated on
    `s.regs cond`, so a tactic block there operates on the unreduced
    projection and `rw` fails.  Prove `regsX rOne â‰  0` as a standalone
    `have` and pass it â€” `exact` closes the projection by defeq.
  - `simp only [â† superEntry]` is rejected (`â†` on a definition to be
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
    `_localMiss`, `_sparse`, `_dense` â€” the six control branches, each
    with receipts POSITIONALLY EQUAL to
    `(data.bpChunkedSelectTraceResultWithStore layout (G+4) ST store c
    idx).trace`, the evaluator's optional answer under `decodePacket` in
    `rVal`, the derived `selectCloseCats`, and `r â‰¤ 7 âˆ¨ r = 28`
    preserved.
  - `selectCloseBlock_localPrefix_runsTo` â€” the shared continuation past
    an unmarked super entry (consumed by the last three branches).
  - `selectCloseBlock_runsTo` â€” the combining theorem, case-splitting on
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
  fact set â€” evaluator def, `queryOccurrence`, `hrange`, the raw `.value`
  equations, the marked/unmarked booleans, `entryRead_trace_eq`, and (for
  the sparse leg) `SparseExceptionDirectory.bpChunkedReadTraceResultWithStore`
  â€” and let it unfold, iota-reduce, and rewrite in one pass.  For the
  value goals, prove a `have hval : (route).value = (leg expr).value` by
  the same one-shot `simp` and then `exact` the leg's decode clause.
- Other gotchas: `by_contra` is Mathlib-only and unavailable here (use
  `simpa [relativeSplitSelectEntryIsMarked]` to invert an unmarked
  entry); `by_cases` IS available (core).  `rw` does not close
  `n + 1 - 1 = n` â€” add `omega`.
- Verification at this commit: standalone `lake env lean` exit 0 (11.1s,
  no warnings); `lake build RMQ` exit 0 (14.6s, 233/233).
- NEXT: the canonical-store select form mirroring
  `rankCloseBlock_runsTo_canonical` â€” instantiate `selectCloseBlock_runsTo`
  at `concreteBPNativeSuccinctRMQGlobalReadStore` and discharge
  `hLongSeed`/`hSparseSeed`/`hDenseLen` from the canonical layout facts
  (agreement lemmas listed at `ChargedRankSelectWiring.lean:656`).

## M3c-6g: CANONICAL SELECT FORM COMPLETE (`E1SelectCanonical.lean`)

The inventory in the RESUME POINT section below is now DISCHARGED â€” every
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
  - `canonical_longSeed`, `canonical_sparseSeed` â€” the three seed reads of
    the long-flag rank object and of the sparse-directory rank object are
    PRESENT at the canonical global store, with the in-word offset bound.
    Both are UNCONDITIONAL in the entry (presence does not depend on entry
    contents), so the dispatch's `âˆ€ super, ... â†’ ... â†’` hypotheses are
    discharged by `fun _ _ _ => ...` with no case split.
  - `canonical_denseLen` â€” the dense-leg exact `Nat.min` word length, one
    lemma serving BOTH the `i` and `i + 1` obligations.
  - `selectCloseBlock_runsTo_canonical` â€” the canonical-store dispatch.
- CONFIRMED (the inventory's two flagged unknowns, both now checked):
  - The `hwords` premise IS `rfl` for both select rank objects
    (`longFlagRankData_bitWords_words`, `sparseRankData_bitWords_words`),
    exactly as the constructor chain predicted.
  - `17 + 4 = 21` closes the chunk-segment identification by `rfl`, the
    same trick as `E1RankCanonical.lean:386`.
- CONFIRMED WRONG-GUESS CORRECTION HELD: `hDenseLen` really is the
  three-step `ofChunks` route (`_selectBitWords` â†’
  `selectAlignedBitWords_ofChunks.get_eq_take_drop` â†’ `simp
  [List.length_take, List.length_drop]`), NOT a
  `builtRankData_wordOffset_le` mirror.  Sentinel-free, no case split.
- NEW GOTCHAS (add to the standing list):
  - `sparseExceptionSelectData` needs its two rank-overhead indices given
    EXPLICITLY in a helper's type ascription (`_` will not synthesize
    them); they are
    `sparseExceptionEffectiveFlagRank{Super,Block}Overhead bits target`.
  - The sparse local slot's entry argument has type
    `SparseDenseSelectDenseLocalEntry`, NOT `RelativeSplitSelectEntry` â€”
    the two are easy to confuse since both flow through
    `relativeSplitSelectEntryIsMarked`.
  - `xIdx` is AMBIGUOUS under the dispatch's `open` set; qualify it as
    `E1SelectBridge.xIdx` in any new file that opens `E1SelectDispatch`.
  - Declare the data abbreviation as `private abbrev`, not `private def`,
    so the `rfl` identifications stay reducible.
- Verification at this commit: standalone `lake env lean
  RMQ/Core/WordRAM/E1SelectCanonical.lean` exit 0, NO warnings; `lake
  build RMQ` exit 0.
- NEXT: the close/LCA structural leg (the last risk center) â€”
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
  (`SuccinctFinalRAM.lean:2330`).

## RESUME POINT (M3c-6g: canonical select form) â€” DISCHARGED, see M3c-6g above

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
  (`Segments.lean:79`) BY `rfl` â€” the same `17 + 4 = 21` trick the rank
  template uses at `E1RankCanonical.lean:386`.
- `ST := concreteBPNativeSelectChunkTraceSegment = 22` (`Segments.lean:82`).
- `c := SuccinctClose.bpFringeChunkBits shape.bpCode.length`.
- Target trace object: `concreteBPNativeChunkedSelectCloseGlobalWordTraceResult`
  (`ChargedRankSelectWiring.lean:645`); public alias
  `concreteBPNativeSelectCloseGlobalWordTraceResult`
  (`SuccinctFinalRAM.lean:1342`) is DEFINITIONALLY the same.

DISCHARGING `hDenseLen` (EASIEST â€” do this one first):
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
   `Nat.min wordSize (bits.length - i * wordSize)` â€” the `hDenseLen`
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
    `pos â‰¤ bits.length`, in the `superSampleWords`/`blockSampleWords`
    vocabulary â€” i.e. it composes with the agreement lemmas above by
    plain rewrite, with NO `read_exact` codec detour (unlike the rank
    template, which hand-rolls that upgrade three times at
    `E1RankCanonical.lean:289-357`).  DECISION NEEDED: de-privatize one
    copy and delete the other (preferred â€” it removes a duplication),
    or write a third copy in the new file.  Their shared helper
    `fixedWidthNatTable_word_present_of_entry_present` is likewise
    duplicated (`ReviewerReachabilityLong.lean:293`,
    `ReviewerReachabilitySparse.lean:336`).

(b) OFFSET BOUND.  NO reusable lemma exists (searched
    `wordOffset.*[<=â‰¤].*length` repo-wide: only hypothesis binders in the
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
          some w) : d.wordOffset pos â‰¤ w.length`
    with the body of `builtRankData_wordOffset_le` (`E1RankCanonical.lean:49-122`)
    textually substituted (`builtRelativeSplitBPCloseRankData shape` â†’ `d`,
    `shape.bpCode` â†’ `bits`), then instantiate three times.  All the
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
Structural`, `SuccinctFinalRAM.lean:2330`) â€” the last risk center â€”
then whole-query glue via `E1RouteDecomposition`, then M4 category
algebra + derived literal, M5 target Prop + supersession note, M6
validator `lean_exe`, M7 adequacy doc + matrix closure + final battery.

## STAGE-2 LAYOUT (dense leg tails - implemented in M3c-5c above;
## kept for reference)

`selectFoldBlock_runsTo` interface RE-VERIFIED this session
(`E1SelectBlock.lean:367`): inputs sOne=1, sC=c, sLen(13)=word.length,
sR(17)=bitsToNatLE word / 2^(j*c), sJC(27)=j*c, sOcc(12)=k, sK(18)=count,
`0 < count`; ends LB+36, packet in sVal(9), preserves r<=8 âˆ¨
râˆˆ{10,11,13,14,15,16,24,25,26} âˆ¨ 28<=r.  The dense select call is at
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
none âœ“; fold some off -> sVal = off+1 -> add gives rWI + off + 1 =
packet (wordStart + off) âœ“ (commute by omega).  Second-tail length needs
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
RESUME step 1 is DONE â€” `E1RankTrueBlock.lean` (TRUE-target seeded
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
`seeds+4` coincidence â€” hence M3c-4c).  ATOMIC-BLOCK NOTE: the dense
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
hosted-fold preservation covers `r <= 8 âˆ¨ 28 <= r` (seeded) and the
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
to the decoded option â€” derive small bridge lemmas
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
`obtain âŸ¨regsN, hregsNâŸ© : âˆƒ x, straightRegs store seg regsM = x :=
âŸ¨_, rflâŸ©`; prove per-register value facts by `rw [<- hregsN]` then the
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
  AllSizeStructuralAtSegments` â€” properly CHARGED.  This is the B2
  charged-fringe work: every endpoint-fringe min-excess/argmin is paid for
  by chunk-table reads at the fringe segment, under literal caps.
- SAME-BLOCK branch: `localBPSameBlockCloseDecodedTraceResultWithRankSeed`
  (`ConcreteDirectoryRAM.lean:1559`) â€” still EVENT-SILENT.

The same-block branch is a rank seed plus
`localBPSameBlockCloseSeededTraceResult` (`ConcreteDirectoryRAM.lean:334`),
which is exactly ONE `TraceResult.map` over
`localBPWindowBitsTraceResult` â€” and
`localBPWindowBitsTraceResult_cost` (`ConcreteDirectoryRAM.lean:225`) checks
that this contributes exactly `4` read events, independent of the query
width.  The model's charge for the whole branch is likewise the constant
`rankCost + 4` (`localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le`,
`LocalBPDecoder.lean:1179-1185`).

Inside that single `map`, the value is computed by
`localBPSeededPrefixRangeMinExcess` / `localBPSeededPrefixRangeArgMinPrefixPos`
(`LocalBPDecoder.lean:929-941`), which recurse through
`localBPSeededPrefixRangeArgMinPrefixPosFrom` (`:797-805`) â€” a PER-POSITION
scan, one `localBPSeededBetterPrefixPos` comparison (`:739`) per position,
for `count = rightClose - leftClose + 1` positions.

### Why this blocks E1

Same-block means `leftClose / blockSize = rightClose / blockSize`, so
`count <= blockSize = 2 * (Nat.log2 shape.size + 1)`
(`RelativeSummary.lean:1236-1242`).  That is UNBOUNDED in the size â€” 258 at
`size = 2^128`, 2002 at `2^1000`.  So on this branch the machine must
perform Theta(log n) comparisons while the accepted receipt contains a
CONSTANT 4 window reads.  Under the frozen matrix that is jointly
unsatisfiable:

- REQ-E1-01 forbids an instruction that hides a variable-length scan, so
  each of the `count` comparisons costs at least one charged step;
- REQ-E1-06(c) demands a DERIVED all-size LITERAL total step bound with no
  size hypothesis â€” impossible against a Theta(log n) step count;
- and the obvious repair (fold the window chunk-wise against the fringe
  chunk table, as the cross-block branch does) adds read events, which
  REQ-E1-04 forbids: the read projection must be POSITIONALLY EQUAL to the
  accepted trace, which has exactly those 4 window reads.

The machine does not need more READS here â€” four words already carry the
whole window â€” it needs more STEPS than any literal allows.

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
     comparison + branch category ticks â€” account for them)
  4. rank-seed@right   5a. 4 window reads at seg 0   5b. RIGHT FRINGE FOLD
  then a pure merge, no reads: `bpCandidateClose? (bpCandidateMerge3? ...)`
  (`Candidate.lean:24,28`).

FOLDS AND CAPS â€” two independent caps, so ONE cross-block query runs FOUR
counted loops (two rank-seed folds <=8, two fringe folds <=33):
- fringe fold `bpFringeChunkFoldComputationFrom` (`ChargedFringeTrace.lean:32`),
  iteration count LITERALLY `Nat.min (relHi / c + 1) 33`
  (`ChargedFringeTrace.lean:509` left, `:529` right); one read per
  iteration (`bpFringeChunkFoldCostedFrom_cost`,
  `ChargedFringeChunks.lean:1531`).  NO early exit -> use `RunsTo.iterate`,
  NOT `iterateUntil`.
- word-rank fold cap `bpWordChunkCount c e = Nat.min ((e-1)/c + 1) 8`
  (`ChargedWordChunks.lean:150`) â€” already simulated by
  `rankAtSegmentBlock_runsTo` (`E1RankAtBlock.lean:359`), whose `G + 4`
  lands on segment 21 at `G := 17`.
- address function `bpFringeChunkSlot c v a b = (v*(c+1) + a)*(c+1) + b`
  (`ChargedFringeChunks.lean:360`); offsets `bpFringeChunkStartOff` (`:900`),
  `bpFringeChunkEndOff` (`:904`); `c = bpFringeChunkBits m = Nat.log2 m / 8 + 1`
  (`:42`).

RECEIPT ORDER â€” there is NO route-side flip lemma.  The fold's footprint is
ASCENDING in `j` (`bpFringeChunkFoldComputationFrom_run_footprint`,
`ChargedFringeTrace.lean:141`) while `iterLog` descends.  Reconcile with
`iterLog_congr` (`E1RankBridge.lean:345`) + `iterLog_singleton_desc`
(`E1RankBridge.lean:362`), following the WORKED two-step pattern at
`E1RankTrueBlock.lean:630-641`.

SEGMENTS AND AGREEMENT LEMMAS â€” every segment this leg touches ALREADY has a
per-address lemma, so no pullback plumbing is needed:
  seg 0  window/bp code  `..._bpCode` (`Segments.lean:281`)
  seg 17/18/19 rank seed `..._rankCloseSuper/Block/Word`
                         (`ChargedRankSelectWiring.lean:154/165/176`)
  seg 20 interior        `..._canonicalComponent` (`Segments.lean:258`)
  seg 21 fringe + rank chunk table
                         `..._fringeChunkTable` (`Segments.lean:247`)
Segment 28 (`concreteBPNativeFiniteSmallSameBlockCloseTraceSegment`) is
passed but bound to `_sameBlockSegment` and is INERT â€” no machine code
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

## RESUME POINT (M3d-1b: the fringe fold BLOCK) - NOT IMPLEMENTED

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

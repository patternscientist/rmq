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
  REQ-E1-02 certificate for the 60-instruction block — register bank,
  segments `G..G+4`, immediates, mul/div constants
  (`WS`/`BPS`/`2^c`/`c+1`/`2*c+2`/`2`, variable divisors positive — `c`
  needs the route's `bpFringeChunkBits_pos`), branch targets
  `< 2^w` given `28 <= 2^w`, `G+4 < 2^w`, `L < 2^w`, `0 < c`,
  `0 < WS < 2^w`, `0 < BPS < 2^w`, `2^c < 2^w`, `2*c+2 < 2^w`,
  `B+60 < 2^w`.  (Flattening gotcha: `List.mem_append` leaves the
  disjunction grouped per segment; add `or_assoc` to the simp set before
  the 60-way `rcases`.)
- `rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean`): the M3c
  store-swap glue — for every shape/base/position the hosted block runs
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
  register NUMERALS (`r ≠ 22`), not the abbrevs (`r ≠ sA`) - omega does
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
  eliminates `LB` (not `pc`), breaking later explicit `LB` references —
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
  `r <= 8 ∨ 10 <= r <= 16 ∨ 24 <= r <= 26 ∨ 28 <= r` — the dense leg
  must keep `rWrd`/samples across a fold); 32-instr
  `rankAtSegmentBlock A G c` (7-instr register-input init `A..A+6`,
  loop `A+7..A+30`, back edge `A+31`); frozen `rankAtSegmentCats`
  (derived `7 + 25 * count`); `rankAtSegmentBlock_runsTo` (inputs: rOne/
  rC/rEight pinned, `rE = bpWordRankEffLimit w limit`,
  `rR = bitsToNatLE w`; receipts positionally equal to the atomic fold
  trace, value in `rVal`); width certificate `rankAtSegmentBlock_fits`
  (32 arms, branch target `A+7`).
- Technique: init-only preservation hypotheses must ALSO be stated on
  register numerals (`r ≠ 22 ∧ ...`), instantiated with `(by decide)` at
  abbrev call sites — same omega-opacity gotcha as loop preservation.
- Verification at this commit: standalone `lake env lean` exit 0 (no
  warnings); `lake build RMQ` green.

## RESUME POINT (next session: select-close legs onward)

NEW in this session (commits `69b39a9`, `dae5fa6`, `691f7c0`, + this
one): M3c-2a rank-close canonical glue (`rankCloseBlock_runsTo_canonical`
at the global store, `rankCloseBlock_fits`, `straight_eval`/
`straight_writes` macro lift), M3c-2b `RunsTo.iterateUntil`, M3c-3a
`selectFoldBlock` + `selectFoldBlock_runsTo` (early-exit in-word select
fold fully simulated; see the M3c-3a section for the full select-close
inventory), and `bpChunkRankOfEntry_true_eq` in `E1RankBridge.lean`.

NEXT (select-close remaining machine pieces, in dependency order):

1. TRUE-target rank block (`E1RankTrueBlock.lean`): clone
   `E1RankBlock.lean` (mechanical) for
   `d.bpChunkedRankTraceResultWithStore store G (G+1) (G+2) (G+4) c TRUE
   pos` - consumed twice (long leg seeds at `layout.longFlagRankBase`,
   sparse leg via `sparseDirectory.bpChunkedReadTraceResultWithStore`,
   both at chunk segment 21).  Deltas vs the false block: drop
   `.sub rA rT rA` from the loop body (23 instrs; decode ends at
   `/2` per `bpChunkRankOfEntry_true_eq`, already landed); block length
   59; offsets shift: back edge B+53, epilogue B+54..56, exit jump B+57
   (target B+59+1=B+59? recompute: loop B+30..52, brNZ B+53, fin
   B+54..56, jump B+57 -> B+59, miss B+58, exit B+59); loop pass cats 24
   long; `bpWordRankAccAt`'s true instance for the invariant (check
   whether `bpWordRankAccAt` is already target-parametric - it is:
   `bpWordRankAccAt store seg c TARGET w e n`).  Also needed: an
   ATOMIC-fold variant theorem (loop-only, no seed reads) for the dense
   leg's two `bpChunkedWordRankTraceResultAtSegmentWithStore store 21 c
   false word limit` folds - factor the loop+init as its own hosted
   sub-block so both the seeded blocks and the dense leg consume it, OR
   clone a small `rankAtSegmentBlock` with init from register inputs
   (word value + limit in registers) instead of seed reads.
2. Entry-table read sub-block: the accepted 4-read evaluator
   `readTraceResultRelabeledWithStore` (`GenericSelect/RAMStoreParam.lean:
   258/530`, relabeled segments per
   `concreteBPNativeSelectCloseTraceSegmentLayout`) - inventory its
   trace/value shape first (4 sequential `readWord`s, entry assembled
   from 4 decoded fields, none-propagation per field); machine: 4
   readMems + 4 zero tests, entry fields kept in separate registers
   (marked test `relativeSplitSelectEntryIsMarked` +
   base-position/occurrence arithmetic `RelativeSplit.lean:13-61` are
   plain register arithmetic).
3. Relative-offset read (`bpRelativeOffsetReadTraceResultWithStore`,
   one read + base shift): trivial 3-instr straight segment.
4. Dense two-word leg: compose word read (segment
   `layout.bitWordBase`), two atomic false-rank folds, compare, then
   `selectFoldBlock` on first word (occurrence `beforeFirst +
   localOccurrence`) or second word read + `selectFoldBlock`
   (occurrence `localOccurrence - firstCount`); word-length register
   discharge mirrors `builtRankData_wordOffset_le` (word rows have
   length `wordSize` except the boundary row - find the dense store's
   length characterization when instantiating).
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
`obtain ⟨regsN, hregsN⟩ : ∃ x, straightRegs store seg regsM = x :=
⟨_, rfl⟩`; prove per-register value facts by `rw [<- hregsN]` then the
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

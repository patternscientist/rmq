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

## RESUME POINT (next session: M3c component simulation onward)

DONE so far in M3b (commits `e93e2ae`, `933955e`, this one):
- Register map / packet / skeleton frozen (DD-20260718-006), charged
  invalid guard + REQ-E1-05 public parity landed
  (`E1QueryProgram.lean`, `E1QueryBridge.lean`).
- Whole-query positional decomposition landed
  (`E1RouteDecomposition.lean`): the machine target per valid query is
  select(left) ++ select(right-1) [++ lca [++ rank(answer+1)]] with the
  value pinned per branch.
- Loop backbone `RunsTo.iterate`/`iterLog` landed (M3b-3).

M3c plan (the remaining big grind, REQ-E1-03/04):
1. All simulation lemmas are stated against the canonical store
   `concreteBPNativeSuccinctRMQGlobalReadStore shape`
   (`SuccinctFinalRAM.lean:1374` region) - the same store the accepted
   trace matches (`.._matchesReadStore` theorems).  Machine receipts are
   `readWord seg idx (store.readWord? seg idx)` by construction, so
   positional equality with the component trace reduces to: same
   (segment, index) sequence, plus the component's `matchesReadStore`.
2. Component order (increasing difficulty): (a) rank-close at segment
   (`concreteBPNativeRankCloseWordTraceResultAtSegment`,
   `SuccinctFinalRAM.lean:1506`).  Structure ALREADY INVENTORIED:
   it is `bpChunkedRankTraceResultWithStore`
   (`ChargedRankSelectLeafTrace.lean:154`) = three single-read legs
   (super sample at `base` index `data.superIndex pos`, block sample at
   `base+1` index `data.wordIndex pos`, packed word at `base+2` index
   `data.wordIndex pos`; each leg's trace is one literal
   `readWord` event - `bpChunkReadTraceResult`/`bpWordReadTraceResult`
   are single-event records) followed by the 8-cap word-chunk fold
   `bpChunkedWordRankTraceFromWithStore`
   (`ChargedRankSelectTrace.lean:106`): `bpWordChunkCount c effLimit`
   iterations, iteration `j` reading the chunk table at `base+4` index
   `bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
   (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)`.
   Machine strategy for the fold: keep a remaining-word register
   (decoded word value), extract the next c-bit chunk by
   div/mod-by-`2^c` constant forms; needs arithmetic bridge lemmas
   `bpFringeWindowChunkValue c word j = (bitsToNatLE word / 2^(j*c)) %
   2^c`-shaped plus an affine form of `bpFringeChunkSlot`, then
   `RunsTo.iterate` with the invariant carrying (remaining word,
   slice-length schedule, accumulator).  The count register is
   data-dependent (`bpWordChunkCount`), computed by machine arithmetic
   from the decoded word/limit registers; (b) select-close
   (`concreteBPNativeChunkedSelectCloseGlobalWordTraceResult`, target of
   `SuccinctFinalRAM.lean:1342`) - chunked select tables; (c) the
   all-size structural close/LCA leg
   (`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`,
   `SuccinctFinalRAM.lean:2330`) - same-block vs cross-block split,
   chunked fringe folds (33-cap), interior reads, merges - the risk
   center.  For each: expand the trace into a (segment, index) sequence
   parameterized by inputs/read values; write the generator block
   (registers >= `firstComponentReg`, explicit base, loops via
   `RunsTo.iterate`); prove precondition -> exact receipts + value in a
   register + literal category counts.
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
program consumes them).  No closed row weakened; no frozen identity
touched.  Branch state: M0 `702cfbe`, M1 `18f35d7`, M2 `11b8cf9`, M3a
`d721ca9`, M3b-1 `e93e2ae`, M3b-2 `933955e`, M3b-3 (this commit);
working tree clean at each yield.

Planned milestones: M1 bookkeeping repairs (stale segment-21 doc lines ->
23; 33-cap attribution; simp-arg warnings if cheap). M2 machine core (ISA +
step semantics + width predicate + DD entries). M3 program + simulation
(result agreement, receipt projection, invalid guard). M4 cost categories +
derived literal. M5 amended target Prop + supersession note. M6 validator +
doc discharge. M7 final battery + matrix closure.

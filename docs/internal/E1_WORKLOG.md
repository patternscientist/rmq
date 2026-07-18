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

Planned milestones: M1 bookkeeping repairs (stale segment-21 doc lines ->
23; 33-cap attribution; simp-arg warnings if cheap). M2 machine core (ISA +
step semantics + width predicate + DD entries). M3 program + simulation
(result agreement, receipt projection, invalid guard). M4 cost categories +
derived literal. M5 amended target Prop + supersession note. M6 validator +
doc discharge. M7 final battery + matrix closure.

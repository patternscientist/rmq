# R2 all-size reviewer-machine worklog (EG-CP-ALLSIZE-R1)

Continuation checkpoint for the `codex/eg-cp-allsize-reviewer-machine-r1`
branch. Base `6bf28de` on `codex/eg-cp-final-falsification-gate-r1`; the
frozen R2 coordinator-amendment matrix is the first commit (`c0cd387`).

## Milestones committed (chronological)

1. `c0cd387` matrix freeze; `79d6f58` byte-faithful recovery of the stalled
   worker's 28,780-line tree; `cdd26a5`..`ca2c6cd` interior crash-site repair
   and interior orbit budget (`<= 40`).
2. `6598971`..`024390a` the select tower: thirteen-arm state invariant,
   arithmetic-slot refactor, per-arm consume closers for entry/rank/dense
   arms, public canonical component orbits, and the long-flag rank value
   characterization over the canonical store.
3. `063401f` sparse-flag rank value twin plus the select done projection.
4. `26339b8` relative-directory arms closed with exact content bounds
   (segment 12/16 reads reassemble inside the parenthesis string).
5. `492251c` select consume dispatcher over all thirteen arms.
6. `5fd9284` select done envelope tightened to `close <= 2n+1` (forced: the
   interior range obligation fails at `rightClose = 2n + 2*ws + 3`); per-index
   segment-zero word refinement threads the dense arms.
7. `4bb00dd` LCA foundations: generic consumed witness, window/fringe
   descent and positivity, relaxed window requests-fit clone, the
   thirty-three-chunk fringe budget, block-index bound.
8. `e09e5e3` the eleven-arm canonical LCA invariant and every StartX fits
   lemma; `5aea9f8` all ten consume arms plus the dispatcher; `05f3322` the
   LCA surface (scalars, operands, `<= 129` budget, result fits with `+1`
   slack); `2a43b5c` both towers packaged as `RequestsFitFrom` producers.

## Completed after the two-tower milestone

9. `f911d3e` five-arm whole coupling and the public
   `packedReviewerDriveLogical_210_request_operands_fit` in the validation
   binder shape; `d28de40` the coupled physical controller chain (reachable
   state-machine fits and the reachable-state certificate); `0e85ecb` the
   physical operand closure and the twenty-six-fact public certificate.
10. `cd02789` the dead-address width generalized to every size; the frozen
    `RMQ/Validation/EGCPFinalFalsification.lean` elaborates end-to-end.
11. Gates on the final tree: `lake build RMQ` green (3 m 38 s); strict
    design-decision check green (31 files); claim-drift green (0 strict
    failures); forbidden-token and native-shortcut scans empty; frozen rows
    byte-identical (append-only amendment); `a4d18d7` one recorded replay
    harness repair (stage selector vs the Windows PowerShell 5.1 binder);
    replay stage `R2-ALLSIZE` PASS (seven commissioned REJECTs, SHA-verified
    restoration, terminal clean tree).
12. Matrix amendment closed row-by-row with the validation consumer evidence;
    coordinator acceptance still required.

## Coordinator disposition (2026-08-05, `EG-CP-ALLSIZE-INT-R1`)

13. `368b828` froze the `R2R1` replay-fidelity repair; `a0a0f92` is its
    report-only child (one changed path, the result report).
14. Fresh-blind audit `1182848` (report-only child of `a0a0f92`, one added
    path) returned `LOCAL_RUNG_ACCEPTABLE` with no `P0`/`P1`/`P2` finding and
    three `P3` bookkeeping findings.
15. **Local rung `EG-CP-ALLSIZE-R1` `ACCEPTED`** at exact candidate `a0a0f92`
    and integrated into local `main` by fast-forward. Item 12's "coordinator
    acceptance still required" is now discharged. The three `P3` findings were
    corrected before integration: the audit's branch-audited count (41 -> 40,
    the 41 being the report commit's own distance), its registry remainder
    ("seven outstanding cases" -> four null-target entries plus five already
    runnable), and the superseded pre-repair replay row in the result report.
    Full evidence and the `P3-2` carry-forward obligation on the `M06` mutant
    are in `EG_CP_FINAL_FALSIFICATION_MATRIX.md` section 9.

**This closes the local rung only.** Stage F remains open: `FG-11`, full
`FG-12`, `FG-14`, and `FG-15` must close and be dispositioned by the
coordinator and a fresh-blind auditor before `FEASIBILITY_PASS`, and
`FEASIBILITY_PASS` must precede any Stage A matrix freeze. See the Stage F
progress record in `RMQ_ENDGAME_ROADMAP.md`.

## Load-bearing design facts for a successor

- Fuel-free closure via `PackedReviewerRequestsFitFrom.of_invariant`; orbit
  witnesses (`state = canonicalRun fuel start`) carry exactness; successors
  are built field-wise, never with `.consume` on the left of a tuple.
- Budgets: entry 4, rank 11, wordselect 9, window 4, fringe 33, select 35,
  LCA 129 (`+37/+33/+0/+118/+114/+81/+48` per arm), whole 210.
- The select done value is exactly a close position (`<= 2n+1`); the LCA done
  value carries `NatFits answer /\ NatFits (answer + 1)` for the final rank.
- `let`-bearing protocol definitions must be opened with `simp only [defName]`
  (zeta) before `rw [if_pos ...]` or `cases hresult : ...`; `unfold` alone
  leaves let-variables that block syntactic matching.
- The fringe candidate argument stays `<= 34 * packedFringeChunkBits n`; its
  globalization fits because the fringe table's own footprint dominates the
  chunk budget at every size (40-floor below `c = 2`, cube bound above).

## Stage-F residual repair (2026-08-06, `EG-CP-STAGEF-CLOSE-R2`)

An external audit rejected candidate `cefc4ef` (four repairs: `R1` decisive
provenance/transition, `R2` capstone input boundary, `R3` F12 numeric
estimate, `R4` lifecycle/report accuracy). Clean-history reconstruction on
branch `codex/eg-cp-stagef-close-r2` from accepted local `main` `0f38672`;
the rejected branch is immutable source evidence. Milestones:

21. `8d22684` the corrected contract: round-log records (2026-08-05
    integration; 2026-08-06 rejection), matrix section 10 with exactly the
    two authorized repair amendments, `WDD-20260806-001` (same commit).
22. `c1eada6` the capstone born with the exact-type
    `controller_input_boundary` (fourteen conjuncts), universal header
    liveness, FG-14 instances, runner enactments, portable self-test;
    `DD-20260806-076`/`WDD-20260806-002` (same commit). On-branch probe:
    the M03-style parameter is ill-typed at `ReviewerCapstone.lean:114`.
23. `37764ad` the fixture with the `R1`-strengthened
    `packedReviewerDecisiveCellConnection` (driver prefix decomposition
    `packedReviewerDriveStateAt` + `packedReviewerDriveAux_decompose`;
    invocation fields, transition, and continuation in the conclusion),
    corrected validation consumers, A02 enactment, M03 `ExpectFile`
    follow, axiom entries; `DD-20260806-077`/`WDD-20260806-003` (same
    commit). Probe: weakening the producer back to the rejected form
    fails `egcpStageFDecisiveCellConnection`.
24. `f105971` the deadline calibration in final form (private-definition
    probe; M08/M12 `ExpectFile` follow); `WDD-20260806-004` (same commit).
25. Frozen-tree battery: Windows and Ubuntu `-SelfTestOnly` PASS; exact
    `A01` selector ACCEPT; one full-mode certification run `FULL MODE
    PASS` 16/16 (1430.4 s, deadline 912 s from a genuine 228 s probe);
    both anti-vacuity probes REJECT at their named consumers; builds,
    axiom inventory, scans, frozen-row byte integrity, and detached
    per-commit design re-checks all green.
26. The final documentation commit: this entry, the completed section
    10.8 cells, the Stage-F final record with the `R3` numeric estimate
    (zero remaining focused proof-days) and the `R4` per-commit lifecycle
    table; `WDD-20260806-005` (same commit).

Boundary: repaired local candidate only. Coordinator audit and a separate
fresh-blind audit are requested next; `FEASIBILITY_PASS`, Stage A, public
synchronization, `S1`, and `V1` remain open.

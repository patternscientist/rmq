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

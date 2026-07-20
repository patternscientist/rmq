/-
# The whole-query step literal: REQ-E1-06 conjunct (c), closed

`E1CostLadder.lean` derived the close/LCA leg at `totalSteps <= 10167` and
DELIBERATELY left the other stage slots of `wholeQueryBranchCats_length_le_of`
unfilled, on the stated grounds that plausible figures produce "a number that
reads as derived and is not".  This module fills them, and only them, by the
same method: every numeral below falls out of `unfold`/`rfl` plus `omega` from
the algebra beneath it, and nothing is asserted.

## What was missing and why it is available now

Three of the four open slots (`prologue`, `selectJoin`/`rankJoin`/`output`,
and `rank`) were open because no machine-side stage record existed to describe
them.  `wholeQueryMachineStageCats` (`E1WholeQueryMachineCats.lean:66`) now
supplies one, so those slots are read off a definition rather than guessed.

The `select` slot was open for a different and more interesting reason, and it
is the only one that needed new mathematics: `selectCloseCats`
(`E1SelectDispatch.lean:287`) is a four-level `if`/`match` tree over three
legs, and NOTHING in the tree bounded its length.  It is bounded here.

**The structural risk this could have foundered on does not exist**, and that
is a fact about `bpWordChunkCount`'s DEFINITION rather than a hypothesis
anyone supplies:

```
def bpWordChunkCount (c e : Nat) : Nat := Nat.min ((e - 1) / c + 1) 8
```

(`ChargedWordChunks.lean:150`.)  The cap is INSIDE the definition, so
`bpWordChunkCount_le_eight` (`ChargedWordChunks.lean:153`) is
`Nat.min_le_right` with no side condition on `c`, `e`, `bits` or `shape`.
Every chunk count reachable from `selectCloseCats` is written literally as a
`bpWordChunkCount`, so no sub-log's length depends on an unbounded quantity
and the all-size, no-size-hypothesis property survives intact.

The one recursion below `selectCloseCats` is `selectFoldCats`
(`E1SelectBlock.lean:214`), which is early-exit rather than `iterLog`; its own
`selectFoldCats_length_le` (`:227`) covers it, and its trip count at both call
sites is again a `bpWordChunkCount`.

## The two traps this module is written around

**`210` bounds READS, not steps.**  `E1CostLadder.lean`'s section on
coordinator claims records this explicitly so that no reader infers a
connection from adjacency.  Nothing here is proved against `210`, and the
whole-query literal derived below is not comparable to it.

**The two `33`s.**  Neither appears in this module.  The caps consumed here
are the `8`s of `bpWordChunkCount`, which is the interior adapter's cap, not
the fringe window's.

## Looseness, declared

Every bound here is a worst case over branches that no single query takes
together.  `E1CostLadder.lean`'s own anti-vacuity section measured its bounds
running about six times loose at the validator's fixture shape, and the slots
added here are looser still for the same reason: the select bound assumes the
dense leg on both selects with eight chunk iterations at every level, and the
LCA bound assumes the cross-block arm.  REQ-E1-06 conjunct (c) asks for a
derived literal with no size hypothesis, not a tight one.  A tight bound would
be a different theorem and would have to give up the all-size property.
-/
import RMQ.Core.WordRAM.E1CostLadder
import RMQ.Core.WordRAM.E1WholeQueryAgreement

namespace RMQ
namespace WordRAM
namespace E1WholeQueryCostLiteral

open E1Machine
open E1CostLadder
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.GenericSelect

/-! ## 1. The frozen straight-line logs the select tree rests on

Each is a literal list, so each length is `rfl` and a wrong figure is a build
failure rather than a claim.
-/

theorem selectPrologueCats_length :
    E1SelectDispatch.selectPrologueCats.length = 6 := rfl

theorem selectSuperSlotCats_length :
    E1SelectDispatch.selectSuperSlotCats.length = 2 := rfl

theorem selectLocalSlotCats_length :
    E1SelectDispatch.selectLocalSlotCats.length = 6 := rfl

theorem selectDenseBaseCats_length :
    E1SelectDispatch.selectDenseBaseCats.length = 9 := rfl

theorem longLegSetupCats_length :
    E1SelectLegBlocks.longLegSetupCats.length = 9 := rfl

theorem sparseLegSetupCats_length :
    E1SelectLegBlocks.sparseLegSetupCats.length = 13 := rfl

theorem denseTail1SetupCats_length :
    E1DenseSelectBlock.denseTail1SetupCats.length = 9 := rfl

theorem denseTail2SetupCats_length :
    E1DenseSelectBlock.denseTail2SetupCats.length = 14 := rfl

/-- The packet shift charges three steps on both arms, but they are DIFFERENT
three steps -- `[branch, branch, branch]` when the fold produced no packet and
`[branch, arithmetic, branch]` when it did -- so this is a case split, not a
`rfl`. -/
theorem packetShiftCats_length (p : Option Nat) :
    (E1DenseSelectBlock.packetShiftCats p).length = 3 := by
  cases p <;> rfl

/-! ## 2. The two sparse legs

Both are `rankTrueCloseHitCats` at a chunk count, a setup, a relative read and
one write, so both lengths are EQUATIONS in the count; the `<=` comes from the
cap and nowhere else.
-/

/-- `47 + 24 * count = (34 + 24 * count) + 9 + 3 + 1`. -/
theorem longLegCats_length (count : Nat) (present : Bool) :
    (E1SelectLegBlocks.longLegCats count present).length = 47 + 24 * count := by
  unfold E1SelectLegBlocks.longLegCats
  rw [List.length_append, List.length_append, List.length_append,
    E1RankTrueBlock.rankTrueCloseHitCats_length,
    E1SelectBridge.relativeReadCats_length, longLegSetupCats_length]
  simp only [List.length_cons, List.length_nil]
  omega

/-- `239 = 47 + 24 * 8` at the eight-chunk cap. -/
theorem longLegCats_length_le (c e : Nat) (present : Bool) :
    (E1SelectLegBlocks.longLegCats (bpWordChunkCount c e) present).length
      ≤ 239 := by
  rw [longLegCats_length]
  have h := bpWordChunkCount_le_eight c e
  omega

/-- `51 + 24 * count = (34 + 24 * count) + 13 + 3 + 1`. -/
theorem sparseLegCats_length (count : Nat) (present : Bool) :
    (E1SelectLegBlocks.sparseLegCats count present).length =
      51 + 24 * count := by
  unfold E1SelectLegBlocks.sparseLegCats
  rw [List.length_append, List.length_append, List.length_append,
    E1RankTrueBlock.rankTrueCloseHitCats_length,
    E1SelectBridge.relativeReadCats_length, sparseLegSetupCats_length]
  simp only [List.length_cons, List.length_nil]
  omega

/-- `243 = 51 + 24 * 8` at the eight-chunk cap. -/
theorem sparseLegCats_length_le (c e : Nat) (present : Bool) :
    (E1SelectLegBlocks.sparseLegCats (bpWordChunkCount c e) present).length
      ≤ 243 := by
  rw [sparseLegCats_length]
  have h := bpWordChunkCount_le_eight c e
  omega

/-! ## 3. Composing bounds without transcribing index expressions

`length_append_le` (`E1CostLadder.lean:493`) exists so that route-side index
expressions are never copied into a proof: every index below is inferred by
unification against the goal, so a mismatched instantiation is a unification
failure rather than a silently weaker theorem (DD-20260719-227).

The select tree is built from `::` as well as `++`, so it needs the cons
companion, which did not exist because every block the ladder had reached so
far is an append.  DD-20260719-242.

**Every intermediate bound below is written as an explicit numeral** rather
than left to be inferred.  That is deliberate: with a metavariable in the
`b` slot the arithmetic side condition cannot be discharged, and pinning each
one means each rung of the ladder is separately readable and separately
falsifiable by the kernel.
-/

/-- The cons companion of `length_append_le`, for the same reason. -/
theorem length_cons_le {alpha : Type} {x : alpha} {l : List alpha} {a : Nat}
    (h : l.length ≤ a) : (x :: l).length ≤ a + 1 := by
  rw [List.length_cons]
  omega

/-! ## 4. The dense leg

The widest of the three legs, and the only one whose bound is a `<=` rather
than an `=` at the cap: it branches four ways (missing first word / first-word
select / missing second word / second-word select) and the arms differ.

`433 = 33 + 25 * 16` is the head with both chunk counts capped; `219 = 27*8+3`
is the fold.  The two tails measure `231` and `239`, so the second-word arm is
the wider and `673 = 433 + 1 + 239`.
-/

/-- Both dense tails run their fold at a `bpWordChunkCount`, so both inherit
the same `219`. -/
theorem selectFoldCats_length_le_capped (store : ReadStore) (R c : Nat)
    (word : List Bool) (j k cc ee : Nat) :
    (E1SelectBlock.selectFoldCats store R c word j (bpWordChunkCount cc ee)
      k).length ≤ 219 := by
  have h1 := E1SelectBlock.selectFoldCats_length_le store R c word
    (bpWordChunkCount cc ee) j k
  have h2 := bpWordChunkCount_le_eight cc ee
  omega

/-- The head with both chunk counts capped: `433 = 33 + 25 * (8 + 8)`. -/
theorem denseHeadPresentCats_length_le (c e1 e2 : Nat) :
    (E1DenseSelectBlock.denseHeadPresentCats (bpWordChunkCount c e1)
      (bpWordChunkCount c e2)).length ≤ 433 := by
  rw [E1DenseSelectBlock.denseHeadPresentCats_length]
  have h1 := bpWordChunkCount_le_eight c e1
  have h2 := bpWordChunkCount_le_eight c e2
  omega

theorem denseLegCats_length_le (store : ReadStore) (W G S c WS : Nat)
    (bPos bOcc q : Nat) :
    (E1DenseSelectBlock.denseLegCats store W G S c WS bPos bOcc q).length
      ≤ 673 := by
  unfold E1DenseSelectBlock.denseLegCats
  cases store.readWord? W (bPos / WS) with
  | none => simp [E1DenseSelectBlock.denseHeadMissCats]
  | some w1 =>
      -- `673 = 433 + 240`
      refine Nat.le_trans (length_append_le (b := 240)
        (denseHeadPresentCats_length_le _ _ _) ?_) (by omega)
      -- `240 = 1 + 239`: the presence branch, then the wider tail
      refine Nat.le_trans (length_append_le (a := 1) (b := 239)
        (by simp only [List.length_cons, List.length_nil]; omega) ?_) (by omega)
      split
      · -- first-word select: `231 = 9 + (219 + 3)`
        exact Nat.le_trans (length_append_le
          (Nat.le_of_eq denseTail1SetupCats_length)
          (length_append_le (selectFoldCats_length_le_capped _ _ _ _ _ _ _ _)
            (Nat.le_of_eq (packetShiftCats_length _)))) (by omega)
      · -- second word: `239 = 2 + 237`
        refine Nat.le_trans (length_append_le (a := 2) (b := 237)
          (by simp only [List.length_cons, List.length_nil]; omega) ?_)
          (by omega)
        cases store.readWord? W (bPos / WS + 1) with
        | none => simp only [List.length_cons, List.length_nil]; omega
        | some w2 =>
            -- `237 = 1 + (14 + (219 + 3))`
            exact Nat.le_trans (length_append_le (a := 1)
              (by simp only [List.length_cons, List.length_nil]; omega)
              (length_append_le (Nat.le_of_eq denseTail2SetupCats_length)
                (length_append_le
                  (selectFoldCats_length_le_capped _ _ _ _ _ _ _ _)
                  (Nat.le_of_eq (packetShiftCats_length _))))) (by omega)

/-! ## 5. The select leg

`729`, by the widest path through the four-level tree:

```
  prologue                6
  in-range branch         1
  super slot              2
  entry read             12
  presence branch         1
  arithmetic/branch       2
  local slot              6
  entry read             12
  presence branch         1
  arithmetic/branch       2
  dense base              9
  dense leg             673
  write/branch            2
  ---------------------------
                        729
```

The out-of-range arm charges `9`, the long-leg arm `241` and the sparse-leg
arm `245`, so the maximum is attained on the dense path -- the arm the bound
names, and the reason the figure is `729` exactly rather than a round-up.
-/

theorem selectCloseCats_length_le {bits : List Bool} {target : Bool}
    {rso rbo : Nat}
    (data : SparseExceptionSelectData bits target rso rbo)
    (layout : SparseExceptionSelectTraceSegmentLayout)
    (G ST : Nat) (store : ReadStore) (c idx : Nat) :
    (E1SelectDispatch.selectCloseCats data layout G ST store c idx).length
      ≤ 729 := by
  unfold E1SelectDispatch.selectCloseCats
  split
  · -- `729 = 6 + 723`
    refine Nat.le_trans (length_append_le (b := 723)
      (Nat.le_of_eq selectPrologueCats_length) ?_) (by omega)
    -- `723 = 722 + 1`
    refine Nat.le_trans (length_cons_le (a := 722) ?_) (by omega)
    -- `722 = 2 + 720`
    refine Nat.le_trans (length_append_le (b := 720)
      (Nat.le_of_eq selectSuperSlotCats_length) ?_) (by omega)
    -- `720 = 12 + 708`
    refine Nat.le_trans (length_append_le (b := 708)
      (Nat.le_of_eq E1SelectBridge.entryReadCats_length) ?_) (by omega)
    -- `708 = 707 + 1`
    refine Nat.le_trans (length_cons_le (a := 707) ?_) (by omega)
    cases E1SelectDispatch.superEntry data layout store idx with
    | none => simp only [List.length_cons, List.length_nil]; omega
    | some super =>
        -- `707 = 705 + 1 + 1`
        refine Nat.le_trans (length_cons_le (length_cons_le (a := 705) ?_))
          (by omega)
        split
        · -- the long leg: `241 = 239 + 2`
          exact Nat.le_trans (length_append_le (b := 2)
            (longLegCats_length_le _ _ _)
            (by simp only [List.length_cons, List.length_nil]; omega))
            (by omega)
        · -- `705 = 6 + 699`
          refine Nat.le_trans (length_append_le (b := 699)
            (Nat.le_of_eq selectLocalSlotCats_length) ?_) (by omega)
          -- `699 = 12 + 687`
          refine Nat.le_trans (length_append_le (b := 687)
            (Nat.le_of_eq E1SelectBridge.entryReadCats_length) ?_) (by omega)
          -- `687 = 686 + 1`
          refine Nat.le_trans (length_cons_le (a := 686) ?_) (by omega)
          cases E1SelectDispatch.localEntry data layout store idx super with
          | none => simp only [List.length_cons, List.length_nil]; omega
          | some loc =>
              -- `686 = 684 + 1 + 1`
              refine Nat.le_trans
                (length_cons_le (length_cons_le (a := 684) ?_)) (by omega)
              split
              · -- the sparse leg: `245 = 243 + 2`
                exact Nat.le_trans
                  (length_append_le (b := 2) (sparseLegCats_length_le _ _ _)
                    (by simp only [List.length_cons, List.length_nil]; omega))
                  (by omega)
              · -- the dense leg: `684 = 9 + (673 + 2)`
                exact Nat.le_trans (length_append_le
                  (Nat.le_of_eq selectDenseBaseCats_length)
                  (length_append_le (b := 2)
                    (denseLegCats_length_le _ _ _ _ _ _ _ _ _)
                    (by simp only [List.length_cons, List.length_nil]; omega)))
                  (by omega)
  · -- the out-of-range arm: `9 = 6 + 3`
    exact Nat.le_trans (length_append_le (b := 3)
      (Nat.le_of_eq selectPrologueCats_length)
      (by simp only [List.length_cons, List.length_nil]; omega)) (by omega)

/-! ## 6. The close/LCA leg AT THE ROUTE'S OWN DISPATCHER

`E1CostLadder.lean`'s `closeLcaLegCats_length_le` takes the two-branch
disjunction as a HYPOTHESIS, because when it was written the tree had no
definition dispatching between the same-block and cross-block close legs, and
DD-20260719-230 declined to invent one -- a witness constructed FOR a premise
defeats rule 1.

`wholeQueryLcaRunCats` (`E1WholeQueryAgreement.lean:39`) is now that
dispatcher, and it was written for the AGREEMENT proof rather than for this
premise: it branches on `blockOfClose ... leftClose = blockOfClose ...
rightClose`, the route's own arm selector, the same condition
`lcaCloseTraceResultWithRankSeedAllSizeStructural` dispatches on.  So the
hypothesis is discharged here at a witness FOUND at the target.
DD-20260719-241.

The two arms are the disjuncts plus a shared six-tick prefix (the two select
tests and the two address arithmetic ticks), and on the cross arm a two-tick
terminator.  `sameBlockLcaRunCats` wraps `sameBlockDispatchCats` exactly, that
being `closeDispatchCats ++ sameBlockLegCats` by definition
(`E1CloseCompose.lean:78`).

`2334 = 6 + 2328` and `10179 = 6 + (4 + (10167 + 2))`; the cross arm is the
wider and supplies the bound.
-/

/-- `2334 = 6 + 2328`. -/
theorem sameBlockLcaRunCats_length_le (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (E1Query.sameBlockLcaRunCats shape leftClose rightClose).length
      ≤ 2334 := by
  unfold E1Query.sameBlockLcaRunCats
  have h := sameBlockDispatchCats_length_le shape
    concreteBPNativeFringeChunkTraceSegment
    (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose rightClose
  unfold E1CloseCompose.sameBlockDispatchCats at h
  exact Nat.le_trans (length_append_le (a := 6)
    (by simp only [List.length_cons, List.length_nil]; omega) h) (by omega)

/-- `10179 = 6 + (4 + (10167 + 2))`. -/
theorem crossBlockLcaRunCats_length_le (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (E1Query.crossBlockLcaRunCats shape leftClose rightClose).length
      ≤ 10179 := by
  unfold E1Query.crossBlockLcaRunCats
  exact Nat.le_trans (length_append_le (a := 6)
    (by simp only [List.length_cons, List.length_nil]; omega)
    (length_append_le (Nat.le_of_eq closeDispatchCats_length)
      (length_append_le (b := 2)
        (crossBlockArmCats_withCanonicalInterior_length_le _ _ _ _ _ _ _ _)
        (by simp only [List.length_cons, List.length_nil]; omega))))
    (by omega)

/-- **THE HYPOTHESIS OF `closeLcaLegCats_length_le`, DISCHARGED.**

At the route's own dispatcher the close/LCA leg is bounded outright, with no
disjunction left standing.  `10179` rather than `10167` because the dispatcher
also charges the two select tests, the address arithmetic and, on the cross
arm, the terminator -- work the leg-level bound did not include because at
that level it had not happened yet. -/
theorem wholeQueryLcaRunCats_length_le (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (E1Query.wholeQueryLcaRunCats shape leftClose rightClose).length
      ≤ 10179 := by
  unfold E1Query.wholeQueryLcaRunCats
  split
  · exact Nat.le_trans
      (sameBlockLcaRunCats_length_le shape leftClose rightClose) (by omega)
  · exact crossBlockLcaRunCats_length_le shape leftClose rightClose

/-! ## 7. The remaining stage slots, read off the machine's own record

`wholeQueryMachineStageCats` (`E1WholeQueryMachineCats.lean:66`) fixes each of
these, so none is a guess.  The prologue is `guardAcceptCats ++
[registerWrite]`, and `guardAcceptCats_length` (`E1QueryProgram.lean:588`)
already gives `8`.
-/

/-- `9 = 8 + 1`: the accepting guard, then the valid path's opening write. -/
theorem machine_prologue_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).prologue.length = 9 := rfl

theorem machine_selectJoin_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).selectJoin.length = 2 := rfl

theorem machine_rankJoin_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).rankJoin.length = 2 := rfl

theorem machine_lcaSkippedLeftMiss_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).lcaSkippedLeftMiss.length
      = 2 := rfl

theorem machine_lcaSkippedRightMiss_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).lcaSkippedRightMiss.length
      = 4 := rfl

theorem machine_rankSkipped_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).rankSkipped.length = 0 := rfl

theorem machine_outputSome_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).outputSome.length = 2 := rfl

theorem machine_outputNone_length (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) :
    (E1Query.wholeQueryMachineStageCats shape f).outputNone.length = 2 := rfl

/-- The machine's `select` field IS `selectCloseCats` at the whole-query select
data, so section 5's bound applies with nothing instantiated away. -/
theorem machine_select_length_le (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) (idx : Nat) :
    ((E1Query.wholeQueryMachineStageCats shape f).select idx).length ≤ 729 :=
  selectCloseCats_length_le _ _ _ _ _ _ _

/-- `234 = 30 + 8 * 25 + 4`, from `rankCloseHitCats_length_le` at the
eight-chunk cap.  The machine's `rankRun` field is exactly that log at a
`bpWordChunkCount`, so the ladder's bound applies directly. -/
theorem machine_rankRun_length_le (shape : Cartesian.CartesianShape)
    (f : Nat → Nat → List Category) (pos : Nat) :
    ((E1Query.wholeQueryMachineStageCats shape f).rankRun pos).length ≤ 234 :=
  rankCloseHitCats_length_le _ _

/-! ## 8. THE WHOLE-QUERY STEP LITERAL

```
  prologue        9
  select        729   (twice)
  selectJoin      2
  lca         10179
  rankJoin        2
  rank          234
  output          2
  ------------------
               11886
```

`11886 = 9 + 729 + 2 + 729 + 10179 + 2 + 234 + 2`.

Every summand is derived above and `omega` performs the addition, so the
literal is checked by the kernel rather than transcribed.  It is stated first
with the close/LCA stage still a PARAMETER under a bound, so the summation
does not depend on which dispatcher fills that slot, and only then instantiated
at the route's own.
-/

/-- The summation at the machine's stage record, with the close/LCA stage still
a parameter under a bound. -/
theorem wholeQueryBranchCats_machineStageCats_length_le
    (shape : Cartesian.CartesianShape) (f : Nat → Nat → List Category)
    (lca : Nat) (hf : ∀ i j, (f i j).length ≤ lca) (hlca : 4 ≤ lca)
    (left right : Nat) (br : SuccinctFinal.WholeQueryBranch) :
    (E1Query.wholeQueryBranchCats (E1Query.wholeQueryMachineStageCats shape f)
      left right br).length ≤ 9 + 729 + 2 + 729 + lca + 2 + 234 + 2 := by
  have h := wholeQueryBranchCats_length_le_of
    (E1Query.wholeQueryMachineStageCats shape f) left right br
    9 729 2 lca 2 234 2
    (Nat.le_of_eq (machine_prologue_length shape f))
    (fun i => machine_select_length_le shape f i)
    (Nat.le_of_eq (machine_selectJoin_length shape f))
    hf
    (by rw [machine_lcaSkippedLeftMiss_length]; omega)
    (by rw [machine_lcaSkippedRightMiss_length]; omega)
    (Nat.le_of_eq (machine_rankJoin_length shape f))
    (fun i => machine_rankRun_length_le shape f i)
    (by rw [machine_rankSkipped_length]; omega)
    (Nat.le_of_eq (machine_outputSome_length shape f))
    (Nat.le_of_eq (machine_outputNone_length shape f))
  omega

/-- **REQ-E1-06 CONJUNCT (c), ON EVERY ROUTE BRANCH.**

The whole-query machine's category log is bounded by `11886` on all four
branches, at every shape and every query, with NO size hypothesis. -/
theorem wholeQueryBranchCats_machineS_length_le
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (br : SuccinctFinal.WholeQueryBranch) :
    (E1Query.wholeQueryBranchCats (E1Query.wholeQueryMachineS shape) left right
      br).length ≤ 11886 := by
  have h := wholeQueryBranchCats_machineStageCats_length_le shape
    (E1Query.wholeQueryLcaRunCats shape) 10179
    (fun i j => wholeQueryLcaRunCats_length_le shape i j) (by omega) left right
    br
  unfold E1Query.wholeQueryMachineS
  omega

/-- **THE SAME LITERAL AT THE BRANCH THE ROUTE ACTUALLY TAKES.**

`wholeQueryCats` evaluates `wholeQueryBranch` and charges that branch's log, so
this is the whole-query step bound at the route's own classification. -/
theorem wholeQueryCats_machineS_length_le (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    (E1Query.wholeQueryCats (E1Query.wholeQueryMachineS shape) shape left
      right).length ≤ 11886 :=
  wholeQueryBranchCats_machineS_length_le shape left right _

/-- **AND AS A STATEMENT ABOUT `totalSteps`.**

`cats.length` IS `totalSteps` by `RunsTo`'s own definition, whose last
component is the `steps` field (`E1MachineCalculus.lean:96`).
`RunsTo.steps_le` (`E1CostLadder.lean:679`) states that identity and depends on
NO axioms, so this carries the bound across it rather than proving anything
new.  The `RunsTo` premise is LOAD-BEARING: it is what supplies the `run` whose
steps are bounded, and the statement cannot be made without it. -/
theorem wholeQuery_totalSteps_le {store : ReadStore}
    {program : E1Machine.Program} {s s' : State} {reads : List TraceEvent}
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (h : E1Machine.RunsTo store program s s' reads
      (E1Query.wholeQueryCats (E1Query.wholeQueryMachineS shape) shape left
        right)) :
    (E1Machine.run store program
      (E1Query.wholeQueryCats (E1Query.wholeQueryMachineS shape) shape left
        right).length s).steps ≤ 11886 :=
  E1CostLadder.RunsTo.steps_le h
    (wholeQueryCats_machineS_length_le shape left right)

/-! ## 9. ANTI-VACUITY: what `11886` actually bounds

Every theorem above would still be true if every category log in this
development were `[]`, so the logs were EVALUATED at the validator's own
fixture shape (`Cartesian.stackCartesianShape [3, 1, 4, 1, 5]`,
`E1MachineValidate.lean:334`) in a scratchpad driver, against
`wholeQueryMachineS` -- the real stage record, not a stand-in.

| stage | measured | bound |
|---|---|---|
| `prologue` | `9` | `9` |
| `select 0` | `335` | `729` |
| `select 3` | `387` | `729` |
| `selectJoin` | `2` | `2` |
| `lcaRun 0 4` | `474` | `10179` |
| `lcaRun 1 3` | `410` | `10179` |
| `rankJoin` | `2` | `2` |
| `rankRun 5` | `59` | `234` |
| `outputSome` | `2` | `2` |

and the whole-query log, per branch, against `11886`:

| branch | measured |
|---|---|
| `.full 0 4 3` | `1270` |
| `.full 1 3 2` | `1256` |
| `.lcaNone 0 4` | `1209` |
| `.leftSelectNone` | `737` |
| `.rightSelectNone 0` | `739` |

**The logs are substantial.**  A five-element input already charges four
figures of machine steps on the answering branch.  The bound bounds something.

**Four of the eight slots are EXACT** -- `prologue`, `selectJoin`, `rankJoin`
and `output` are frozen literal lists, so their bounds are their lengths and
no slack enters there at all.

**The slack is concentrated in the three legs, and the LCA slot dominates it.**
`11886` against a measured `1270` is roughly nine times loose at this shape,
somewhat looser than the six times `E1CostLadder.lean`'s own section 12
recorded, and the reason is visible in the table: the close/LCA bound assumes
the CROSS-BLOCK arm with a full interior dispatch, while a five-element shape
takes the same-block arm and charges `474`.  Of the `10616` steps of slack,
`9705` are in that one slot.

This is the price of "all-size, with no size hypothesis", which is what
REQ-E1-06 conjunct (c) asks for.  A tight bound would be a different theorem
and would have to give up the all-size property to get it; the honest
statement is the loose one, said out loud.
-/

end E1WholeQueryCostLiteral
end WordRAM
end RMQ

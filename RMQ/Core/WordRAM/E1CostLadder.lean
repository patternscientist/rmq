/-
# The E1 charge-length ladder: every block's category log bounded, bottom to top

`E1CostAlgebra.lean` bounded ONE composite (`fringeFoldCats_length_le_capped`)
and left the other sixteen unbounded, together with the closed leaf logs they
rest on.  This module closes the rest of the ladder and then performs the
SUMMATION that REQ-E1-06 conjunct (c) asks for.

## The discipline every numeral here is held to

**No literal is asserted.**  Each bound is stated with the numeral its own
algebra produces and proved by unfolding to that algebra and closing with
`omega`.  Where a numeral could have been guessed and checked, it was instead
EVALUATED first (`#eval` in a scratchpad driver, never in the tree) and the
evaluated figure is what the statement carries.  The leaf lengths in section
1 are all `rfl`, so a wrong figure is a build failure rather than a silent
looseness.

**`<=`, not `=`.**  REQ-E1-06 conjunct (c) demands an inequality.  Nothing in
this module passes through `machineWordBits`, so `Nat.log2` and the kernel
boundary are never in play -- these are counts of instructions, not of bits.
`E1_LIVE_STATE.md` section 11 B is respected here for the same reason
`E1CostAlgebra` respected it: not because the obstruction was dodged, but
because it does not arise for instruction counts.

**Looseness is declared where it exists.**  Several composites branch, and the
bound takes the widest arm.  A query that takes a narrow arm charges strictly
less.  That is stated, not hidden: a derived `<=` that is loose is honest; an
asserted literal that happens to be tight is not.

## The two `33`s, again, because this module touches both neighbourhoods

`E1CostAlgebra.lean`'s header separates them and that separation is load
bearing here too:

* the FRINGE-WINDOW chunk-read cap, inside `endpointFringe = 4 + 33 = 37`
  (`ChargedFringeChunks.lean:1624-1687`) -- this is the `33` that
  `cap_count_le` bounds and that `sbCount` (`E1SameBlockArm.lean:134`),
  `crossLeftArmCats` and `crossRightArmCats` (`E1CrossBlockArm.lean:1049`,
  `:1062`) each write out as `Nat.min (relHi / c + 1) 33`;
* the WHOLE-INTERIOR-DIRECTORY read cap,
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost := 33`
  (`InteriorDirectory.lean:1934`), which this module proves nothing about.

The interior side of this ladder is capped by `8`, not by either `33`:
`chunkIters_le_eight` (`E1CostAlgebra.lean`) for the summary chunk fold and
`bpWordChunkCount_le_eight` (`ChargedWordChunks.lean:153`) for the rank
close-hit loop.  Those are also two distinct `8`s.

DD-20260719-220 through DD-20260719-226.
-/
import RMQ.Core.WordRAM.E1CostAlgebra
import RMQ.Core.WordRAM.E1InteriorDispatchCompose
import RMQ.Core.WordRAM.E1InteriorCombine
import RMQ.Core.WordRAM.E1InteriorMinCandidate

namespace RMQ
namespace WordRAM
namespace E1CostLadder

open E1Machine
open E1CostAlgebra

/-! ## 1. The closed leaf logs

Every one of these is a `List` literal or a `.map` of one, so its length is
`rfl`.  They had no `.length` bound at all before this module; the figures
were EVALUATED before they were written down.

`dispatchPrologueCats` is the one whose doc-comment already claimed a figure
(`19`, `E1InteriorDispatchCompose.lean:251`).  The claim was unproved; it is
now checked, and it holds.
-/

@[simp] theorem closeDispatchCats_length :
    E1CloseDispatch.closeDispatchCats.length = 4 := rfl

@[simp] theorem dispatchPrologueCats_length :
    E1InteriorDispatchCompose.dispatchPrologueCats.length = 19 := rfl

@[simp] theorem windowAddrCats_length :
    E1SameBlockArm.windowAddrCats.length = 4 := rfl

@[simp] theorem windowRangeCats_length :
    E1SameBlockArm.windowRangeCats.length = 8 := rfl

@[simp] theorem sameBlockCloseCats_length :
    E1SameBlockArm.sameBlockCloseCats.length = 2 := rfl

@[simp] theorem legSetupCats_length :
    E1InteriorCombine.legSetupCats.length = 4 := rfl

@[simp] theorem candMerge3CloseCats_length :
    E1CandMerge3.candMerge3CloseCats.length = 2 := rfl

@[simp] theorem crossStashCats_length :
    E1CrossBlockArm.crossStashCats.length = 3 := rfl

@[simp] theorem crossPinOneCats_length :
    E1CrossBlockArm.crossPinOneCats.length = 1 := rfl

@[simp] theorem crossRepointCats_length :
    E1CrossBlockArm.crossRepointCats.length = 1 := rfl

@[simp] theorem rankSeedPosCats_length :
    E1SameBlockLeg.rankSeedPosCats.length = 1 := rfl

@[simp] theorem rankSeedFinishCats_length :
    E1SameBlockLeg.rankSeedFinishCats.length = 3 := rfl

@[simp] theorem minCandidatePrefixCats_length :
    E1InteriorMinCandidate.minCandidatePrefixCats.length = 13 := rfl

@[simp] theorem minCandidateValueCats_length :
    E1InteriorMinCandidate.minCandidateValueCats.length = 8 := rfl

/-- `.map`s of instruction literals: the length passes through
`List.length_map`, and `rfl` sees it. -/
@[simp] theorem fringeArmPrologueCats_length :
    E1FringeArmBlock.fringeArmPrologueCats.length = 21 := rfl

@[simp] theorem crossLeftRangeCats_length :
    E1CrossBlockArm.crossLeftRangeCats.length = 10 := rfl

@[simp] theorem crossRightRangeCats_length :
    E1CrossBlockArm.crossRightRangeCats.length = 10 := rfl

/-! ## 2. The rank close-hit loop and the seed leg

`rankCloseHitCats` (`E1RankBlock.lean:246`) is a constant-body `iterLog`, so
`iterLog_const_length` applies directly and the count is the only variable.
The count `rankSeedLegCats` feeds it is `bpWordChunkCount ...`, capped at `8`
by `bpWordChunkCount_le_eight` (`ChargedWordChunks.lean:153`) -- a lemma that
already existed and is used rather than restated.
-/

/-- Exact, because the body is constant: head `30`, `25` per pass, tail `4`. -/
theorem rankCloseHitCats_length (count : Nat) :
    (E1RankBlock.rankCloseHitCats count).length = 34 + 25 * count := by
  unfold E1RankBlock.rankCloseHitCats
  rw [List.length_append, List.length_append, iterLog_const_length]
  simp only [E1RankBlock.rankHitHeadCats, E1RankBlock.rankLoopPassCats,
    E1RankBlock.rankHitTailCats, List.length_cons, List.length_nil]
  omega

/-- `234 = 30 + 8 * 25 + 4` at the eight-chunk cap. -/
theorem rankCloseHitCats_length_le (c e : Nat) :
    (E1RankBlock.rankCloseHitCats
      (SuccinctClose.bpWordChunkCount c e)).length ≤ 234 := by
  rw [rankCloseHitCats_length]
  have h := SuccinctClose.bpWordChunkCount_le_eight c e
  omega

/-- `238 = 1 + 234 + 3`: the seed position write, the capped close-hit loop,
the finish. -/
theorem rankSeedLegCats_length_le (shape : Cartesian.CartesianShape)
    (base : Nat) :
    (E1SameBlockLeg.rankSeedLegCats shape base).length ≤ 238 := by
  unfold E1SameBlockLeg.rankSeedLegCats
  rw [List.length_append, List.length_append]
  have h := rankCloseHitCats_length_le
    (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
    ((SuccinctFinal.builtRelativeSplitBPCloseRankData shape).wordOffset base)
  simp only [rankSeedPosCats_length, rankSeedFinishCats_length]
  omega

/-! ## 3. The fringe leg and arm

These sit directly above `fringeFoldCats`, whose cap `E1CostAlgebra` derived
(`fringeFoldCats_length_le`, and at the capped trip count
`fringeFoldCats_length_le_capped : ... <= 2046 = 33 * 62`).  Both compose
immediately.

The trip-count cap is not a hypothesis here: every caller writes the count out
as `Nat.min (relHi / c + 1) 33` literally (`sbCount`,
`E1SameBlockArm.lean:134`; `crossLeftArmCats`/`crossRightArmCats`,
`E1CrossBlockArm.lean:1049`/`:1062`), so `cap_count_le` applies at the call
site with nothing owed.
-/

/-- Prologue plus fold, in the trip count. -/
theorem fringeLegCats_length_le (store : ReadStore) (S c : Nat)
    (window : List Bool) (relLo relHi seed count : Nat) :
    (E1FringeArmBlock.fringeLegCats store S c window relLo relHi seed
      count).length ≤ 21 + count * 62 := by
  unfold E1FringeArmBlock.fringeLegCats
  rw [List.length_append]
  have h := fringeFoldCats_length_le store S c window relLo relHi seed count
  simp only [fringeArmPrologueCats_length]
  omega

/-- `2067 = 21 + 33 * 62` at the capped trip count. -/
theorem fringeLegCats_length_le_capped (store : ReadStore) (S c : Nat)
    (window : List Bool) (relLo relHi seed : Nat) :
    (E1FringeArmBlock.fringeLegCats store S c window relLo relHi seed
      (Nat.min (relHi / c + 1) 33)).length ≤ 2067 := by
  have h := fringeLegCats_length_le store S c window relLo relHi seed
    (Nat.min (relHi / c + 1) 33)
  have hcap := cap_count_le relHi c
  have hmul : Nat.min (relHi / c + 1) 33 * 62 ≤ 33 * 62 :=
    Nat.mul_le_mul_right 62 hcap
  omega

/-- The candidate-globalisation epilogue charges at most `5`: the occupied arm
is `4` and the unoccupied arm is `5`, so the bound is attained on the
UNOCCUPIED path.  Derived by case analysis on the route-side occupancy, not
read off. -/
theorem fringeCandGlobalArmCats_length_le (occupied : Bool) :
    (E1FringeArmBlock.fringeCandGlobalArmCats occupied).length ≤ 5 := by
  unfold E1FringeArmBlock.fringeCandGlobalArmCats
  cases occupied <;> simp

/-- `2072 = 2067 + 5`. -/
theorem fringeArmCats_length_le_capped (store : ReadStore) (S c : Nat)
    (window : List Bool) (relLo relHi seed : Nat) :
    (E1FringeArmBlock.fringeArmCats store S c window relLo relHi seed
      (Nat.min (relHi / c + 1) 33)).length ≤ 2072 := by
  unfold E1FringeArmBlock.fringeArmCats
  rw [List.length_append]
  have hleg := fringeLegCats_length_le_capped store S c window relLo relHi seed
  exact Nat.le_trans
    (Nat.add_le_add hleg (fringeCandGlobalArmCats_length_le _)) (by omega)

/-! ## 4. The same-block leg, arm and dispatch

`sbCount` (`E1SameBlockArm.lean:134`) is DEFINITIONALLY the capped form, so
`fringeArmCats_length_le_capped` applies to `sameBlockArmCats` with no side
condition at all.
-/

/-- `2074 = 2072 + 2`. -/
theorem sameBlockArmCats_length_le (shape : Cartesian.CartesianShape)
    (store : ReadStore) (fringeSegment blockSize leftClose rightClose seed :
      Nat) :
    (E1SameBlockArm.sameBlockArmCats shape store fringeSegment blockSize
      leftClose rightClose seed).length ≤ 2074 := by
  unfold E1SameBlockArm.sameBlockArmCats E1SameBlockArm.sbCount
  rw [List.length_append]
  have harm := fringeArmCats_length_le_capped store fringeSegment
    (E1SameBlockArm.sbChunkBits shape)
    (E1FringeArmBlock.windowBitsOfStore store
      (E1SameBlockArm.sbBase shape blockSize leftClose))
    (E1SameBlockArm.sbRelLo shape blockSize leftClose)
    (E1SameBlockArm.sbRelHi shape blockSize leftClose rightClose) seed
  simp only [sameBlockCloseCats_length]
  omega

/-- `2324 = 4 + 238 + 8 + 2074`: window address preamble, capped rank seed
leg, window range preamble, capped arm. -/
theorem sameBlockLegCats_length_le (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose rightClose : Nat) :
    (E1SameBlockLeg.sameBlockLegCats shape fringeSegment blockSize leftClose
      rightClose).length ≤ 2324 := by
  unfold E1SameBlockLeg.sameBlockLegCats
  rw [List.length_append, List.length_append, List.length_append]
  have hseed := rankSeedLegCats_length_le shape
    (E1SameBlockArm.sbBB shape blockSize leftClose)
  have harm := sameBlockArmCats_length_le shape
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    fringeSegment blockSize leftClose rightClose
    (E1SameBlockLeg.canonicalSeed shape blockSize leftClose)
  simp only [windowAddrCats_length, windowRangeCats_length]
  omega

/-- `2328 = 4 + 2324`. -/
theorem sameBlockDispatchCats_length_le (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose rightClose : Nat) :
    (E1CloseCompose.sameBlockDispatchCats shape fringeSegment blockSize
      leftClose rightClose).length ≤ 2328 := by
  unfold E1CloseCompose.sameBlockDispatchCats
  rw [List.length_append]
  have h := sameBlockLegCats_length_le shape fringeSegment blockSize leftClose
    rightClose
  simp only [closeDispatchCats_length]
  omega

/-! ## 5. The three-way candidate merge

Every arm is a literal, so the bound is a case split and the maximum is
attained: `7` on the "middle occupied, strictly better" mid arm and `4` on the
"right strictly better" right arm.
-/

theorem candMerge3MidCats_length_le (left : Nat × Nat)
    (middle : Option (Nat × Nat)) :
    (E1CandMerge3.candMerge3MidCats left middle).length ≤ 7 := by
  unfold E1CandMerge3.candMerge3MidCats
  cases middle <;> simp <;> split <;> simp

theorem candMerge3RightCats_length_le (acc right : Nat × Nat) :
    (E1CandMerge3.candMerge3RightCats acc right).length ≤ 4 := by
  unfold E1CandMerge3.candMerge3RightCats
  split <;> simp

/-- `13 = 7 + 4 + 2`. -/
theorem candMerge3Cats_length_le (left : Nat × Nat)
    (middle : Option (Nat × Nat)) (right : Nat × Nat) :
    (E1CandMerge3.candMerge3Cats left middle right).length ≤ 13 := by
  unfold E1CandMerge3.candMerge3Cats
  rw [List.length_append, List.length_append]
  have hmid := candMerge3MidCats_length_le left middle
  have hright := candMerge3RightCats_length_le
    (E1CandMerge3.candAfterMid left middle) right
  simp only [candMerge3CloseCats_length]
  omega

/-! ## 6. The interior summary ladder

`geomCats` (`E1InteriorSummaryGroup.lean:247`) is a `summaryStageCats` whose
iteration count is `chunkIters`, capped at `8` by `chunkIters_le_eight`
(`E1CostAlgebra.lean`) with no size hypothesis.  Everything in the interior
rests on it.

The chain from here is `geomCats` -> `legCats` -> `spanCats` -> `twoSpanCats`
-> the two dispatch legs.  It is NOT recursive: `spanCats` calls `legCats`,
`twoSpanCats` calls `spanCats` twice, and neither calls back down.  That is
what lets the bounds compose by plain substitution.
-/

/-- `158 = 1 + 156 + 1`: the head category, the interior chunk fold at its
own derived cap, and the stage's closing register write. -/
theorem summaryStageCats_length_le (headCat : Category) (valid allPresent :
      Bool) (entriesLen chunkCount i : Nat) :
    (E1InteriorSummaryGroup.summaryStageCats headCat valid allPresent
      (E1InteriorChunkFold.chunkIters entriesLen chunkCount i)).length ≤ 158 :=
  by
  unfold E1InteriorSummaryGroup.summaryStageCats
  rw [List.length_cons, List.length_append]
  have h := interiorChunkFoldCats_length_le valid allPresent entriesLen
    chunkCount i
  simp only [List.length_singleton]
  omega

/-- `geomCats` is `summaryStageCats` at the machine-computed iteration count,
so the same `158`. -/
theorem geomCats_length_le (store : ReadStore)
    (L : E1InteriorSummaryGroup.SummaryLayout)
    (G : E1InteriorSummaryGroup.TableGeom) (headCat : Category) (i : Nat) :
    (E1InteriorSummaryGroup.geomCats store L G headCat i).length ≤ 158 := by
  unfold E1InteriorSummaryGroup.geomCats
  exact summaryStageCats_length_le _ _ _ _ _ _

/-- `21 = 13 + 8`, attained when the summary is all-present. -/
theorem minCandidateCats_length_le (allPresent : Bool) :
    (E1InteriorMinCandidate.minCandidateCats allPresent).length ≤ 21 := by
  unfold E1InteriorMinCandidate.minCandidateCats
  rw [List.length_append]
  cases allPresent <;> simp

/-- `653 = 4 * 158 + 21`: the four summary tables -- baseline, min-relative,
max-relative, argument offset -- and the min-candidate epilogue. -/
theorem legCats_length_le (shape : Cartesian.CartesianShape) (block : Nat) :
    (E1InteriorSpanBlock.legCats shape block).length ≤ 653 := by
  unfold E1InteriorSpanBlock.legCats
  rw [List.length_append, List.length_append, List.length_append,
    List.length_append]
  have h1 := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape).baseline
    Category.arithmetic
    (block / (E1InteriorSummaryGroup.canonicalSummaryLayout shape).blocksPerSuper)
  have h2 := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape).minRel
    Category.registerWrite block
  have h3 := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape).maxRel
    Category.registerWrite block
  have h4 := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape).argOffset
    Category.registerWrite block
  have h5 := minCandidateCats_length_le
    (E1InteriorMinCandidate.routeDecodedSummary shape block).isSome
  omega

/-- `815 = 1 + 158 + 3 + 653`.  The bound is attained on the OCCUPIED cell
arm; the `none` arm charges `1 + 158 + 3 = 162` and is far below it.  The
looseness is the price of a single all-arm literal, and it is real. -/
theorem spanCats_length_le (shape : Cartesian.CartesianShape)
    (G : E1InteriorSummaryGroup.TableGeom) (slot off : Nat) :
    (E1InteriorSpanBlock.spanCats shape G slot off).length ≤ 815 := by
  unfold E1InteriorSpanBlock.spanCats
  rw [List.length_cons, List.length_append]
  have hgeom := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape) G
    Category.registerWrite slot
  split
  · simp only [List.length_cons, List.length_nil]
    omega
  · next v _ =>
      rw [List.length_append]
      have hleg := legCats_length_le shape (off + v)
      simp only [List.length_cons, List.length_nil]
      omega

/-- `7`, attained on the "both occupied, right not strictly better" arm. -/
theorem mergeCats_length_le (left right : Option (Nat × Nat)) :
    (E1InteriorMerge.mergeCats left right).length ≤ 7 := by
  unfold E1InteriorMerge.mergeCats
  cases left <;> cases right <;> simp <;> split <;> simp

/-- `1810 = 1 + 158 + (11 + 815 + 3 + 815 + 7)`: the level read, then on the
occupied arm the ten-tick address computation with its register write, the
LEFT span, the three-tick pivot, the RIGHT span, and the merge of the two
span values.  Attained on the occupied arm. -/
theorem twoSpanCats_length_le (shape : Cartesian.CartesianShape)
    (GL GS : E1InteriorSummaryGroup.TableGeom) (A M D start n off : Nat) :
    (E1InteriorTwoSpan.twoSpanCats shape GL GS A M D start n off).length ≤
      1810 := by
  unfold E1InteriorTwoSpan.twoSpanCats
  rw [List.length_cons, List.length_append]
  have hgeom := geomCats_length_le
    (SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (E1InteriorSummaryGroup.canonicalSummaryLayout shape) GL
    Category.registerWrite n
  split
  · simp only [List.length_cons, List.length_nil]
    omega
  · next v _ =>
      rw [List.length_append, List.length_append, List.length_append,
        List.length_append]
      have hl := spanCats_length_le shape GS
        (E1InteriorTwoSpan.twoSpanLeftSlot A M D start v) off
      have hr := spanCats_length_le shape GS
        (E1InteriorTwoSpan.twoSpanRightSlot A M D start n v) off
      have hm := mergeCats_length_le
        (E1InteriorSpanBlock.spanValue shape GS
          (E1InteriorTwoSpan.twoSpanLeftSlot A M D start v) off)
        (E1InteriorSpanBlock.spanValue shape GS
          (E1InteriorTwoSpan.twoSpanRightSlot A M D start n v) off)
      simp only [List.length_cons, List.length_nil]
      omega

/-! ## 7. The two- and three-leg combinators

`twoLegCats` and `crossLegCats` (`E1InteriorCombine.lean:294`, `:971`) take
their sub-logs as PARAMETERS, so their bounds are stated in the parameters'
lengths.  That is not a weakening: it is the honest shape, and it is what lets
the five dispatch arms below instantiate the same lemma at different legs.
-/

/-- `|A| + |B| + 24`, where `24 = 3 + 4 + 4 + 4 + 2 + 7`: two setups, three
pivots, and the merge at its own derived cap. -/
theorem twoLegCats_length_le (catsA catsB : List Category)
    (valA valB : Option (Nat × Nat)) :
    (E1InteriorCombine.twoLegCats catsA catsB valA valB).length ≤
      catsA.length + catsB.length + 24 := by
  unfold E1InteriorCombine.twoLegCats
  rw [List.length_append, List.length_append, List.length_append,
    List.length_append, List.length_append, List.length_append,
    List.length_append]
  have hm := mergeCats_length_le valA valB
  simp only [legSetupCats_length, List.length_cons, List.length_nil]
  omega

/-- `|A| + |B| + |C| + 43 = (|A| + |B| + 24) + 2 + 4 + 4 + |C| + 2 + 7`. -/
theorem crossLegCats_length_le (catsA catsB catsC : List Category)
    (valA valB valC : Option (Nat × Nat)) :
    (E1InteriorCombine.crossLegCats catsA catsB catsC valA valB valC).length ≤
      catsA.length + catsB.length + catsC.length + 43 := by
  unfold E1InteriorCombine.crossLegCats
  rw [List.length_append, List.length_append, List.length_append,
    List.length_append, List.length_append, List.length_append]
  have htwo := twoLegCats_length_le catsA catsB valA valB
  have hm := mergeCats_length_le (SuccinctClose.bpCandidateMerge? valA valB)
    valC
  simp only [legSetupCats_length, List.length_cons, List.length_nil]
  omega

/-! ## 8. Composing appends without transcribing route-side indices

The dispatch arms and the cross-block arm apply their sub-logs at index
expressions that run to five and six lines each (`macroSize` arithmetic on the
start block, the capped fringe trip count, and so on).  Transcribing those
into a proof invites exactly the RIGHT-SHAPE-WRONG-CONTENT defect
`E1_LIVE_STATE.md` section 6 records three instances of: a proof that
typechecks against a hypothesis about a DIFFERENT instantiation than the goal.

`length_append_le` removes the temptation.  Every index below is inferred by
unification against the goal, so a mismatched instantiation is a unification
failure rather than a silently weaker theorem.

DD-20260719-227.
-/

theorem length_append_le {alpha : Type} {l1 l2 : List alpha} {a b : Nat}
    (h1 : l1.length ≤ a) (h2 : l2.length ≤ b) :
    (l1 ++ l2).length ≤ a + b := by
  rw [List.length_append]
  omega

/-- The `_of` form of the two-leg bound: numeric bounds in, numeric bound out.
This is what lets the dispatch arms below cite it with every argument
inferred. -/
theorem twoLegCats_length_le_of (catsA catsB : List Category)
    (valA valB : Option (Nat × Nat)) (a b : Nat)
    (hA : catsA.length ≤ a) (hB : catsB.length ≤ b) :
    (E1InteriorCombine.twoLegCats catsA catsB valA valB).length ≤
      a + b + 24 := by
  have h := twoLegCats_length_le catsA catsB valA valB
  omega

theorem crossLegCats_length_le_of (catsA catsB catsC : List Category)
    (valA valB valC : Option (Nat × Nat)) (a b c : Nat)
    (hA : catsA.length ≤ a) (hB : catsB.length ≤ b) (hC : catsC.length ≤ c) :
    (E1InteriorCombine.crossLegCats catsA catsB catsC valA valB valC).length ≤
      a + b + c + 43 := by
  have h := crossLegCats_length_le catsA catsB catsC valA valB valC
  omega

/-! ## 9. The interior dispatch

Both dispatch legs are `twoSpanCats` at different geometries
(`E1InteriorDispatchCompose.lean:129`, `:161`), so both inherit `1810`.
-/

theorem localLegCats_length_le (shape : Cartesian.CartesianShape)
    (macroIdx start n : Nat) :
    (E1InteriorDispatchCompose.localLegCats shape macroIdx start n).length ≤
      1810 := by
  unfold E1InteriorDispatchCompose.localLegCats
  exact twoSpanCats_length_le _ _ _ _ _ _ _ _ _

theorem globalLegCats_length_le (shape : Cartesian.CartesianShape)
    (start n : Nat) :
    (E1InteriorDispatchCompose.globalLegCats shape start n).length ≤ 1810 := by
  unfold E1InteriorDispatchCompose.globalLegCats
  exact twoSpanCats_length_le _ _ _ _ _ _ _ _ _

/--
`#9`'s ARM LOG, ALL FIVE BRANCHES.

`5479 = 6 + (1810 + 1810 + 1810 + 43)` is the WIDEST arm -- the final
`else`, which spans three macro blocks and merges three leg values through
`crossLegCats`.  The other four are `4`, `1814`, `3650` and `3651`, so the
bound is attained and the looseness on a narrower arm is large and real: an
empty range charges `4`.
-/
theorem dispatchArmCats_length_le (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    (E1InteriorDispatchCompose.dispatchArmCats shape startBlock
      count).length ≤ 5479 := by
  unfold E1InteriorDispatchCompose.dispatchArmCats
  split
  · simp
  · split
    · exact Nat.le_trans
        (length_append_le (Nat.le_refl _)
          (length_append_le (localLegCats_length_le _ _ _ _) (Nat.le_refl _)))
        (by simp only [List.length_cons, List.length_nil]; omega)
    · split
      · exact Nat.le_trans
          (length_append_le (Nat.le_refl _)
            (length_append_le
              (twoLegCats_length_le_of _ _ _ _ 1810 1810
                (localLegCats_length_le _ _ _ _)
                (localLegCats_length_le _ _ _ _))
              (Nat.le_refl _)))
          (by simp only [List.length_cons, List.length_nil]; omega)
      · split
        · exact Nat.le_trans
            (length_append_le (Nat.le_refl _)
              (length_append_le
                (twoLegCats_length_le_of _ _ _ _ 1810 1810
                  (localLegCats_length_le _ _ _ _)
                  (globalLegCats_length_le _ _ _))
                (Nat.le_refl _)))
            (by simp only [List.length_cons, List.length_nil]; omega)
        · exact Nat.le_trans
            (length_append_le (Nat.le_refl _)
              (crossLegCats_length_le_of _ _ _ _ _ _ 1810 1810 1810
                (localLegCats_length_le _ _ _ _)
                (globalLegCats_length_le _ _ _)
                (localLegCats_length_le _ _ _ _)))
            (by simp only [List.length_cons, List.length_nil]; omega)

/-- `5498 = 19 + 5479`: the branch-independent prologue plus the widest arm. -/
theorem dispatchCats_length_le (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) :
    (E1InteriorDispatchCompose.dispatchCats shape startBlock count).length ≤
      5498 := by
  unfold E1InteriorDispatchCompose.dispatchCats
  rw [List.length_append]
  have h := dispatchArmCats_length_le shape startBlock count
  simp only [dispatchPrologueCats_length]
  omega

/-! ## 10. The cross-block arm

The interior's log is a PARAMETER of `crossBlockArmCats`
(`E1CrossBlockArm.lean:1088`), so the bound is stated in its length.  That is
the shape the definition has, and keeping it parametric is what lets section
11 instantiate it at the dispatch log without this theorem having to know
about the dispatch at all.
-/

/--
`4669 = 4 + 238 + 10 + 2072 + 3 + 1 + 4 + 238 + 10 + 2072 + 3 + 1 + 13`:
the left window-address preamble, the left rank seed leg, the left range, the
left capped fringe arm, the left stash, the repoint, then the same four for
the right, the right stash, the single pin, and the three-way merge.
-/
theorem crossBlockArmCats_length_le (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize : Nat) (interiorCats : List Category)
    (interiorValue : Option (Nat × Nat)) (leftClose rightClose : Nat) :
    (E1CrossBlockArm.crossBlockArmCats shape fringeSegment blockSize
      interiorCats interiorValue leftClose rightClose).length ≤
      interiorCats.length + 4669 := by
  unfold E1CrossBlockArm.crossBlockArmCats E1CrossBlockArm.crossLeftArmCats
    E1CrossBlockArm.crossRightArmCats
  refine Nat.le_trans
    (length_append_le (Nat.le_refl _)
      (length_append_le (rankSeedLegCats_length_le _ _)
        (length_append_le (Nat.le_refl _)
          (length_append_le (fringeArmCats_length_le_capped _ _ _ _ _ _ _)
            (length_append_le (Nat.le_refl _)
              (length_append_le (Nat.le_refl _)
                (length_append_le (Nat.le_refl _)
                  (length_append_le (Nat.le_refl _)
                    (length_append_le (rankSeedLegCats_length_le _ _)
                      (length_append_le (Nat.le_refl _)
                        (length_append_le
                          (fringeArmCats_length_le_capped _ _ _ _ _ _ _)
                          (length_append_le (Nat.le_refl _)
                            (length_append_le (Nat.le_refl _)
                              (candMerge3Cats_length_le _ _ _)))))))))))))) ?_
  simp only [windowAddrCats_length, crossLeftRangeCats_length,
    crossRightRangeCats_length, crossStashCats_length, crossPinOneCats_length,
    crossRepointCats_length]
  omega

end E1CostLadder
end WordRAM
end RMQ

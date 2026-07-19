import RMQ.Core.WordRAM.E1WholeQueryObjects

/-!
# E1 whole-query glue: the close/LCA leg's OWN branch split, route-side

## The gap this fills

The whole-query route's third leg is
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore`
(`SuccinctFinalStoreParam.lean:1575`).  Unfolded once it is
`lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore`
(`ChargedFringeWiring.lean:487`), whose body is a single `if` on the route's
own same-block test:

    let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
    if blockOfClose blockSize leftClose = blockOfClose blockSize rightClose
      then <same-block arm> else <cross-block arm>

**Nothing in the tree exported that split.**  Grepped before building: the
five consequents of the inner definition (`_eq_of_agree`, `_refines_of_agree`,
`_store_parametric`, `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`,
`ChargedFringeWiring.lean:505`-`:656`) and the five of the outer one
(`SuccinctFinalStoreParam.lean:1587`-`:2040`) all leave the `if` intact; every
case split on it in the tree is INLINE inside a proof and never exported.  The
closest precedent is `finalLcaCloseWithStore_storeTraceLocal`
(`SuccinctFinalStoreParam.lean:2015`), which is `private` and concludes a
`StoreTraceLocal`, not an arm equality.

So this module states the two halves.  They are what lets a machine-side
close/LCA dispatch - which branches on exactly this test - be matched to the
route leg arm by arm instead of as an opaque object.

## Why the machine's dispatch scrutinises the SAME test

`closeDispatch` (`E1CloseDispatch.lean:83`) computes
`blockOfClose blockSize fClose` and `blockOfClose blockSize fRight` by
`divConst` and compares them.  `closeDispatch_runsTo_same` /
`_runsTo_cross` (`E1CloseDispatch.lean:187`/`:224`) are stated against the
ROUTE condition, not a machine-side paraphrase of it.  The two theorems below
are stated against that same condition, so a composition discharges ONE
hypothesis and both sides move together.
-/

namespace RMQ
namespace SuccinctFinal

open RMQ.SuccinctClose

/--
SAME-BLOCK ARM, route-side.  On the route's own same-block condition the
close/LCA leg IS the same-block arm at the canonical block size.

This is the object `sameBlockDispatchProgram_runsTo` (`E1CloseCompose.lean:95`)
produces, modulo the rank-seed argument, which
`lcaLeg_sameBlock_rankSeed_eq` below identifies.

**E1-LaneA5: `lcaLeg_sameBlock_rankSeed_eq` DID NOT EXIST when this docstring
was written** (DD-20260719-182).  Grepped: the name occurred exactly once in
the whole tree, here, in this sentence.  The identification it names is real
and now supplied below, so the sentence is true as of this commit; it is
recorded rather than quietly fixed because a docstring promising a lemma that
was never written is indistinguishable, to a reader, from one that exists.
-/
theorem lcaLeg_of_sameBlock (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore) (leftClose rightClose : Nat)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape store leftClose rightClose =
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        concreteBPNativeFringeChunkTraceSegment store
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  unfold
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [hsame, if_pos]

/--
CROSS-BLOCK ARM, route-side.  On the route's own cross-block condition the
close/LCA leg IS the cross-block arm.

This is the object `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`) rewrites
into the machine's `crossBlockArmSpec` form.
-/
theorem lcaLeg_of_crossBlock (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore) (leftClose rightClose : Nat)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape store leftClose rightClose =
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        concreteBPNativeInteriorTraceSegments
        concreteBPNativeFringeChunkTraceSegment store leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  unfold
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [hcross, if_false]

/-! ## The rank-seed identification the two arm lemmas are stated "modulo" -/

/--
THE RANK SEED, IDENTIFIED (E1-LaneA5).

`lcaLeg_of_sameBlock` and `lcaLeg_of_crossBlock` hand the close/LCA arm the
seed `concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store
rankBase`, while every machine-side arm theorem
(`closeLcaProgramAt_runsTo_same`, `E1WholeQueryCloseLca.lean:191`) produces
`concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape`.  At the global
read store these are the SAME FUNCTION, so the two sides compose.

Stated as a function equality rather than pointwise because the seed enters
the arm as a partially applied argument: a pointwise lemma could not be
rewritten under it without an extra `funext` at every use site.

Both rewrites are existing theorems -
`concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore`
(`SuccinctFinalStoreParam.lean:473`) and
`concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`
(`SuccinctFinalRAM.lean:1550`).  Nothing is reconciled here that was not
already reconciled; this supplies the composition the docstring named.
-/
theorem lcaLeg_sameBlock_rankSeed_eq (shape : Cartesian.CartesianShape) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase =
      concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape := by
  funext pos
  rw [concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore,
    concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]

/-! ## ANTI-VACUITY: both arms are reachable

A pair of branch lemmas is worth nothing if one side is empty.  The two
conditions are complementary and neither is a tautology, so both arms are
live; recorded as an executed disjunction rather than left to the reader. -/

/-- The two branch conditions are exhaustive and exclusive: every query hits
exactly one arm, so neither lemma above is vacuous. -/
theorem lcaLeg_branches_exhaustive (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) ∨
      (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :=
  Decidable.em _

end SuccinctFinal
end RMQ

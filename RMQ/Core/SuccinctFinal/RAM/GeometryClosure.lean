import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

/-!
# Geometry closure for the packed cell-probe controller

This module is evidence toward the Stage F row `EG-CP-F03` ("geometry
closure").  It does **not** by itself close that row; see "What this does not
establish" below.

What is proved: the executed whole-query controller cannot distinguish two
inputs of the same size.  Precisely, for two Cartesian shapes of equal `size`
(equivalently, two `List Int` of equal length at the public entry), **one shared
supplied `RMQ.WordRAM.ReadStore`**, and any endpoints, the controller emits the
identical `TraceResult` -- identical ordered event list and identical value.
There is no size threshold and no regime restriction.

Composed with the pre-existing footprint-locality theorem
`RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
(`RMQ/Core/SuccinctRMQClassic.lean:1298`), the shared-store hypothesis weakens to
agreement on the *ordered read footprint alone* -- the addresses the execution
actually probes.  That composite, `queryTraceResultWithStore_length_and_footprint`
below, is the form that speaks to the roadmap's dependency model of `n`,
endpoints and replies to prior probes.

The controller is the fixed five-instruction program
`RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram` over the closed
expression language `RMQ.SuccinctFinal.WholeQueryNatExpr`; it dispatches to
exactly three shape-consuming leaves, handled here in order:

* `L1` select-close -- `SelectLeaf.L1_route_shape_size_only`;
* `L2` LCA-close    -- `L2_route_size_only` (both routes, interior included);
* `L3` rank-close   -- `L3_rankClose_size_only`.

Assembling the three over the controller evaluator gives the row's capstone,
`T4_wholeQuery_size_only` / `T4_wholeQuery_trace_size_only`, and transporting
that across the public `List Int` boundary gives
`queryTraceResultWithStore_size_only` together with the positive factorisation
`queryTraceResultWithStore_factors`.

All results are stated on the store-parametric surface: the supplied
`RMQ.WordRAM.ReadStore` is universally quantified and shared by the two sides.
These are congruences about what the controller *reads and returns*; they say
nothing about its correctness, and nothing here bounds its probe count.

## What this does not establish

Recorded so no reader mistakes the scope (audit A10, 2026-07-26):

* **No inventory.**  `EG-CP-F03`'s minimum evidence is an exhaustive typed
  inventory of every current logical-read source together with universal
  consumers.  This module supplies no such artifact.  A trace congruence does
  not entail one: a content-dependent intermediate can be dead, or can cancel
  before any observable event, and remain invisible to every congruence here.
* **Header words are not typed.**  The frozen row names header words as a
  permitted input.  They are subsumed here into the undifferentiated supplied
  store and are neither identified nor separately accounted.  `EG-CP-F01`/`F02`
  own the schema, but that ownership does not discharge this row's input
  language.
* **The store is not tied to a packed memory.**  The `ReadStore` parameter is an
  arbitrary total function, not `memory xs` of the packed model contract
  (`docs/internal/RMQ_ENDGAME_ROADMAP.md:327-338`).
* **The store-free surface is genuinely content-dependent**, lawfully so, since
  a different input builds a different memory image.  Nothing here may be
  restated over `RMQ.SuccinctClassic.queryTraceResult` or `queryCosted`.
-/

set_option autoImplicit false

namespace RMQ
namespace SuccinctFinal
namespace GeometryClosure

open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## Leaf L1: the select-close leaf

The T1 obligation map.  These are the merged `EG-CP-F03` T1 lemmas, ported
verbatim from `docs/internal/f03_evidence/t1map_obligations.lean` and
`t1map_layer2.lean`.
-/

namespace SelectLeaf

/-! ### Layer-1 lemmas (re-stated here so this file is self-contained). -/

/-- A fixed-width sparse/dense select entry table is read through its layout
and the supplied store alone: the table value itself is definitionally
irrelevant to the emitted trace. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L1. -/
theorem entryRead_table_irrelevant
    {e1 e2 : List RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry}
    {w1 w2 : Nat}
    (t1 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e1 w1)
    (t2 : RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable e2 w2)
    (layout : RMQ.GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (store : RMQ.WordRAM.ReadStore) (i : Nat) :
    t1.readTraceResultRelabeledWithStore layout store i =
      t2.readTraceResultRelabeledWithStore layout store i := rfl

/-- The dense two-word select leaf depends on its bounded payload word store
only through that store's word size, not through the stored bits. Serves Stage
F row `EG-CP-F03` (geometry closure), leaf L1. -/
theorem denseLeaf_bitWords_irrelevant'
    {b1 b2 : List Bool} {w1 w2 : Nat}
    (bw1 : RMQ.SuccinctSpace.BoundedPayloadWordStore b1 w1)
    (bw2 : RMQ.SuccinctSpace.BoundedPayloadWordStore b2 w2)
    (hw : w1 = w2)
    (bitWordSegment rankTableSegment selectTableSegment c : Nat)
    (target : Bool) (store : RMQ.WordRAM.ReadStore)
    (basePosition baseOccurrence q : Nat) :
    RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw1 store
        basePosition baseOccurrence q =
      RMQ.GenericSelect.bpChunkedDenseTwoWordSelectTraceResultWithStore
        bitWordSegment rankTableSegment selectTableSegment c target bw2 store
        basePosition baseOccurrence q := by
  subst hw; rfl

/-- Obligation `O3`: the chunked rank reader consumes its rank data only
through the bit-vector length, the word size and the blocks-per-superblock
stride. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L1 (and reused
for leaf L3). -/
theorem chunkedRank_geometry_only
    {b1 b2 : List Bool} {s1 k1 q1 s2 k2 q2 : Nat}
    (d1 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b1 s1 k1 q1)
    (d2 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b2 s2 k2 q2)
    (hlen : b1.length = b2.length)
    (hword : d1.wordSize = d2.wordSize)
    (hblocks : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : RMQ.WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos =
      d2.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hword, hblocks]

/-- The sparse exception directory reader consumes its directory only through
the flag-vector length, the rank geometry and the local stride. Serves Stage F
row `EG-CP-F03` (geometry closure), leaf L1. -/
theorem sparseDirRead_geometry_only
    {b1 b2 : List Bool} {tg : Bool} {s1 k1 s2 k2 : Nat}
    (d1 : RMQ.GenericSelect.SparseExceptionDirectory b1 tg s1 k1)
    (d2 : RMQ.GenericSelect.SparseExceptionDirectory b2 tg s2 k2)
    (hflag : d1.flagBits.length = d2.flagBits.length)
    (hword : d1.rankData.wordSize = d2.rankData.wordSize)
    (hblocks : d1.rankData.blocksPerSuper = d2.rankData.blocksPerSuper)
    (hstride : d1.localStride = d2.localStride)
    (layout : RMQ.GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (chunkSegment : Nat) (store : RMQ.WordRAM.ReadStore) (c : Nat)
    (base localSlot localOccurrence : Nat) :
    d1.bpChunkedReadTraceResultWithStore layout chunkSegment store c base
        localSlot localOccurrence =
      d2.bpChunkedReadTraceResultWithStore layout chunkSegment store c base
        localSlot localOccurrence := by
  unfold RMQ.GenericSelect.SparseExceptionDirectory.bpChunkedReadTraceResultWithStore
  rw [chunkedRank_geometry_only d1.rankData d2.rankData hflag hword hblocks,
    hstride]

/-- The generic select congruence: two `SparseExceptionSelectData` values with
the same occurrence count and the same geometry scalars emit the same trace
and the same value. Serves Stage F row `EG-CP-F03` (geometry closure), leaf
L1. -/
theorem L1_generic_congr
    {b1 b2 : List Bool} {tg : Bool} {s1 k1 s2 k2 : Nat}
    (D1 : RMQ.GenericSelect.SparseExceptionSelectData b1 tg s1 k1)
    (D2 : RMQ.GenericSelect.SparseExceptionSelectData b2 tg s2 k2)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg)
    (hwordSize : D1.wordSize = D2.wordSize)
    (hsuperStride : D1.superStride = D2.superStride)
    (hlocalStride : D1.localStride = D2.localStride)
    (hlocalSlots : D1.localSlotsPerSuper = D2.localSlotsPerSuper)
    (hlongFlagLen : D1.longFlagBits.length = D2.longFlagBits.length)
    (hlongRankWord : D1.longFlagRankData.wordSize = D2.longFlagRankData.wordSize)
    (hlongRankBlocks :
      D1.longFlagRankData.blocksPerSuper = D2.longFlagRankData.blocksPerSuper)
    (hsparseFlagLen :
      D1.sparseDirectory.flagBits.length = D2.sparseDirectory.flagBits.length)
    (hsparseRankWord :
      D1.sparseDirectory.rankData.wordSize =
        D2.sparseDirectory.rankData.wordSize)
    (hsparseRankBlocks :
      D1.sparseDirectory.rankData.blocksPerSuper =
        D2.sparseDirectory.rankData.blocksPerSuper)
    (hsparseStride :
      D1.sparseDirectory.localStride = D2.sparseDirectory.localStride)
    (layout : RMQ.GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSegment selectTableSegment : Nat)
    (store : RMQ.WordRAM.ReadStore) (c idx : Nat) :
    D1.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx =
      D2.bpChunkedSelectTraceResultWithStore layout chunkSegment
        selectTableSegment store c idx := by
  unfold RMQ.GenericSelect.SparseExceptionSelectData.bpChunkedSelectTraceResultWithStore
  simp only [RMQ.GenericSelect.SparseExceptionSelectData.queryOccurrence,
    entryRead_table_irrelevant D1.superTable D2.superTable,
    entryRead_table_irrelevant D1.localTable D2.localTable,
    chunkedRank_geometry_only D1.longFlagRankData D2.longFlagRankData
      hlongFlagLen hlongRankWord hlongRankBlocks,
    sparseDirRead_geometry_only D1.sparseDirectory D2.sparseDirectory
      hsparseFlagLen hsparseRankWord hsparseRankBlocks hsparseStride,
    denseLeaf_bitWords_irrelevant' D1.bitWords D2.bitWords hwordSize]
  simp only [hcount, hwordSize, hsuperStride, hlocalStride, hlocalSlots]

/-! ### Layer 2: the flag-vector length obligations. -/

/-- The long-superblock flag vector has a length determined by the bit-vector
length and the occurrence count. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L1. -/
theorem longFlagLen_congr
    {b1 b2 : List Bool} {tg : Bool}
    (hlen : b1.length = b2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg) :
    (RMQ.GenericSelect.longSuperFlagBits b1 tg).length =
      (RMQ.GenericSelect.longSuperFlagBits b2 tg).length := by
  rw [RMQ.GenericSelect.longSuperFlagBits_length,
    RMQ.GenericSelect.longSuperFlagBits_length,
    RMQ.GenericSelect.superSlotCount, RMQ.GenericSelect.superSlotCount,
    hlen, hcount]

/-- The sparse exception flag vector has a length determined by the bit-vector
length and the occurrence count. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L1. -/
theorem sparseFlagLen_congr
    {b1 b2 : List Bool} {tg : Bool}
    (hlen : b1.length = b2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount b1 tg =
        RMQ.GenericSelect.occurrenceCount b2 tg) :
    (RMQ.GenericSelect.sparseExceptionEffectiveFlagBits b1 tg).length =
      (RMQ.GenericSelect.sparseExceptionEffectiveFlagBits b2 tg).length := by
  rw [RMQ.GenericSelect.sparseExceptionEffectiveFlagBits_length,
    RMQ.GenericSelect.sparseExceptionEffectiveFlagBits_length,
    RMQ.GenericSelect.sparseExceptionEffectiveLocalSlotCount,
    RMQ.GenericSelect.sparseExceptionEffectiveLocalSlotCount,
    RMQ.GenericSelect.localSlotCount, RMQ.GenericSelect.localSlotCount,
    RMQ.GenericSelect.superSlotCount, RMQ.GenericSelect.superSlotCount,
    hlen, hcount]

/-! ### T1 proper, at the concrete `sparseExceptionSelectData`. -/

/-- **T1.** The concrete select structure `sparseExceptionSelectData` consumes
its bit vector only through its length and its occurrence count -- never
through its content. Serves Stage F row `EG-CP-F03` (geometry closure), leaf
L1. -/
theorem T1_L1_size_only
    (bits1 bits2 : List Bool) (target : Bool)
    (store : RMQ.WordRAM.ReadStore)
    (layout : RMQ.GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (chunkSeg selSeg c idx : Nat)
    (hlen : bits1.length = bits2.length)
    (hcount :
      RMQ.GenericSelect.occurrenceCount bits1 target =
        RMQ.GenericSelect.occurrenceCount bits2 target) :
    (RMQ.GenericSelect.sparseExceptionSelectData bits1
          target).bpChunkedSelectTraceResultWithStore
        layout chunkSeg selSeg store c idx =
      (RMQ.GenericSelect.sparseExceptionSelectData bits2
          target).bpChunkedSelectTraceResultWithStore
        layout chunkSeg selSeg store c idx := by
  have hflagLong := longFlagLen_congr (b1 := bits1) (b2 := bits2) (tg := target)
    hlen hcount
  have hflagSparse := sparseFlagLen_congr (b1 := bits1) (b2 := bits2)
    (tg := target) hlen hcount
  refine L1_generic_congr _ _ hcount ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    layout chunkSeg selSeg store c idx
  · show RMQ.GenericSelect.wordBits bits1.length
      = RMQ.GenericSelect.wordBits bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.superStride bits1.length
      = RMQ.GenericSelect.superStride bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.localStride bits1.length
      = RMQ.GenericSelect.localStride bits2.length
    rw [hlen]
  · show RMQ.GenericSelect.localSlotsPerSuper bits1.length
      = RMQ.GenericSelect.localSlotsPerSuper bits2.length
    rw [hlen]
  · exact hflagLong
  · show RMQ.GenericSelect.longFlagRankWordSize bits1 target
      = RMQ.GenericSelect.longFlagRankWordSize bits2 target
    unfold RMQ.GenericSelect.longFlagRankWordSize
    rw [hflagLong]
  · rfl
  · exact hflagSparse
  · show RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize bits1 target
      = RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize bits2 target
    unfold RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize
    rw [hflagSparse]
  · rfl
  · show RMQ.GenericSelect.localStride bits1.length
      = RMQ.GenericSelect.localStride bits2.length
    rw [hlen]

/-! ### Route corollary: leaf L1 at equal-size Cartesian shapes. -/

/-- **Controller leaf L1 (select-close) is size-only.** For any two Cartesian
shapes of equal `size`, the supplied-store select-close leaf returns the
identical `RMQ.WordRAM.TraceResult`. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L1. -/
theorem L1_route_shape_size_only
    {a b : RMQ.Cartesian.CartesianShape} (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (idx : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        a store idx =
      RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        b store idx := by
  unfold
    RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  have hlen : a.bpCode.length = b.bpCode.length := by
    rw [RMQ.Cartesian.CartesianShape.bpCode_length,
      RMQ.Cartesian.CartesianShape.bpCode_length, h]
  have hcount :
      RMQ.GenericSelect.occurrenceCount a.bpCode false =
        RMQ.GenericSelect.occurrenceCount b.bpCode false := by
    unfold RMQ.GenericSelect.occurrenceCount
    rw [RMQ.SuccinctSpace.bpCode_rankFalse_full,
      RMQ.SuccinctSpace.bpCode_rankFalse_full, h]
  rw [T1_L1_size_only a.bpCode b.bpCode false store _ _ _ _ _ hlen hcount,
    hlen]

end SelectLeaf

/-! ## Leaves L2 and L3: the LCA-close and rank-close leaves

Shape-consuming geometry of the relative-RMM directory: the layout scalars, the
interior component offsets (campaign obligation `T3`), the eight fixed-width
interior tables and their entry counts (campaign obligation `T5` for the
interior), the two dispatcher arms, and the two controller leaves.
-/

/-- Equal-size shapes have balanced-parenthesis codes of equal length. Serves
Stage F row `EG-CP-F03` (geometry closure); this is the base length fact used
by every leaf below. -/
theorem bpLen_congr {a b : CartesianShape} (h : a.size = b.size) :
    a.bpCode.length = b.bpCode.length := by
  rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, h]

/-- The canonical relative-RMM layout (block size, blocks per superblock,
block count, relative width) is a function of `size` alone. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem layout_congr {a b : CartesianShape} (h : a.size = b.size) :
    RelativeRmm.canonicalLayout a = RelativeRmm.canonicalLayout b := by
  unfold RelativeRmm.canonicalLayout
  unfold canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummaryRelativeWidthRaw
    canonicalBPRelativeSummaryBase
  rw [h]

/-- The canonical summary block size is a function of `size` alone; it is the
divisor in the L2 route selector. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L2. -/
theorem blockSizeRaw_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBlockSizeRaw a =
      canonicalBPRelativeSummaryBlockSizeRaw b := by
  unfold canonicalBPRelativeSummaryBlockSizeRaw canonicalBPRelativeSummaryBase
  rw [h]

/-- The local balanced-parenthesis window base is a function of the code
length alone. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem windowBase_congr {a b : CartesianShape} (h : a.size = b.size)
    (blockSize close : Nat) :
    localBPWindowBase a blockSize close = localBPWindowBase b blockSize close := by
  unfold localBPWindowBase
  rw [bpLen_congr h]

/-- The four-word block read of the balanced-parenthesis code addresses words
by code length alone; the replies come from the shared store. Serves Stage F
row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem localBPBlockWords_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (blockSize close : Nat) :
    localBPBlockWordsTraceResultWithStore a store blockSize close =
      localBPBlockWordsTraceResultWithStore b store blockSize close := by
  unfold localBPBlockWordsTraceResultWithStore
  rw [bpLen_congr h]

/-- The decoded local window bits are a function of the code length and the
shared store. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem localBPWindowBits_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (blockSize close : Nat) :
    localBPWindowBitsTraceResultWithStore a store blockSize close =
      localBPWindowBitsTraceResultWithStore b store blockSize close := by
  unfold localBPWindowBitsTraceResultWithStore
  rw [localBPBlockWords_congr h]

/-- The rank-close seed used by both L2 arms depends on the shape only through
the window base. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2.
-/
theorem seed_congr {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat) (blockSize close : Nat) :
    localBPSeedFromRankCloseTraceResult a rankCloseTrace blockSize close =
      localBPSeedFromRankCloseTraceResult b rankCloseTrace blockSize close := by
  unfold localBPSeedFromRankCloseTraceResult
  rw [windowBase_congr h]

/-- The left fringe candidate of the cross-block arm is size-only. Serves
Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem leftFringe_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (fringeSegment blockSize leftClose seed : Nat) :
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose seed =
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]

/-- The right fringe candidate of the cross-block arm is size-only. Serves
Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem rightFringe_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (fringeSegment blockSize rightClose seed : Nat) :
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize rightClose seed =
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize rightClose seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]


/-! ### Generalised qz_mech core: word count of a fixed-width table's machine store. -/

/-- Chunking a payload into machine words yields a word count that depends on
the payload's length only. Serves Stage F row `EG-CP-F03` (geometry closure),
leaf L2 (interior tables). -/
theorem chunkFuel_length_congr (wordSize : Nat) :
    forall (fuel : Nat) (p q : List Bool), p.length = q.length ->
      (chunkPayloadWordsFuel wordSize fuel p).length =
        (chunkPayloadWordsFuel wordSize fuel q).length := by
  intro fuel
  induction fuel with
  | zero => intro p q _; simp [chunkPayloadWordsFuel]
  | succ fuel ih =>
      intro p q hpq
      cases p with
      | nil =>
          cases q with
          | nil => simp [chunkPayloadWordsFuel]
          | cons b r => simp at hpq
      | cons b r =>
          cases q with
          | nil => simp at hpq
          | cons c s =>
              have hdrop :
                  ((b :: r).drop wordSize).length =
                    ((c :: s).drop wordSize).length := by
                simp [List.length_drop, hpq]
              simp only [chunkPayloadWordsFuel, List.length_cons]
              rw [ih _ _ hdrop]

/-- Payload chunking is length-only, in the fuel-free form. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem chunkPayloadWords_length_congr
    (wordSize : Nat) (p q : List Bool) (h : p.length = q.length) :
    (chunkPayloadWords wordSize p).length =
      (chunkPayloadWords wordSize q).length := by
  unfold chunkPayloadWords
  rw [h]
  exact chunkFuel_length_congr wordSize (q.length + 1) p q h

/-- Chunking a list of uniformly sized words multiplies the word count by a
factor fixed by the width and the machine word size. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem flatMap_chunk_length_of_uniform
    (wordSize width : Nat) :
    forall ws : List (List Bool),
      (forall w, List.Mem w ws -> w.length = width) ->
        (ws.flatMap (chunkPayloadWords wordSize)).length =
          ws.length *
            (chunkPayloadWords wordSize (List.replicate width false)).length := by
  intro ws
  induction ws with
  | nil => intro _; simp
  | cons head tail ih =>
      intro huniform
      have hhead : head.length = width := huniform head (List.Mem.head _)
      have htail : forall w, List.Mem w tail -> w.length = width := by
        intro w hw; exact huniform w (List.Mem.tail _ hw)
      have hrep : (List.replicate width false).length = width := by simp
      have hheadlen :
          (chunkPayloadWords wordSize head).length =
            (chunkPayloadWords wordSize (List.replicate width false)).length :=
        chunkPayloadWords_length_congr wordSize head _ (by rw [hhead, hrep])
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih htail, hheadlen, Nat.succ_mul]
      omega

/-- A fixed-width `Nat` table stores exactly one word per entry. Forced by the
table's `read_exact` field, so no inhabitant can have a content-dependent word
count. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem store_words_size_eq_entries_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.store.words.size = entries.length := by
  have key :
      forall i : Nat,
        ((table.store.words.toList)[i]?).isSome = (entries[i]?).isSome := by
    intro i
    have h : ((table.store.words.toList)[i]?).map bitsToNatLE = entries[i]? := by
      simpa using table.read_exact i
    rw [← h]
    cases (table.store.words.toList)[i]? <;> simp
  have hlen : table.store.words.toList.length = table.store.words.size :=
    Array.length_toList
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : ((table.store.words.toList)[entries.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : (entries[table.store.words.toList.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [← key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2

/-- Every word stored by a fixed-width table has exactly the declared width.
Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem store_word_mem_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {bits : List Bool} (hmem : List.Mem bits table.store.words.toList) :
    bits.length = width := by
  rcases List.getElem?_of_mem hmem with ⟨i, hi⟩
  exact table.word_length_of_get? (by simpa using hi)

/-- **Closed form**: a fixed-width table's machine-store word count is
`entries.length` times a function of `wordSize` and `width` only. -/
theorem machineStore_words_size_closed
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (h : 0 < wordSize) :
    (table.machineStore (wordSize := wordSize) h).store.words.size =
      entries.length *
        (chunkPayloadWords wordSize (List.replicate width false)).length := by
  show (fixedWidthNatTableMachineWords table wordSize).toArray.size = _
  rw [List.size_toArray]
  unfold fixedWidthNatTableMachineWords
  rw [flatMap_chunk_length_of_uniform wordSize width table.store.words.toList
    (fun w hw => store_word_mem_length table hw)]
  rw [Array.length_toList, store_words_size_eq_entries_length table]

/-- **Generalised read-computation congruence**: differing widths allowed. -/
theorem machineReadComputationAt_geometry_only
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1)
    (t2 : FixedWidthNatTable e2 w2)
    (hlen : e1.length = e2.length) (hw : w1 = w2)
    (wordSize base deadAddress i : Nat) :
    t1.machineReadComputationAt wordSize base deadAddress i =
      t2.machineReadComputationAt wordSize base deadAddress i := by
  unfold FixedWidthNatTable.machineReadComputationAt
  rw [hlen, hw]


/-! ### Interior directory: the eight table geometries -/

/-- The canonical local machine store is definitionally the local interior
table's machine store. Serves Stage F row `EG-CP-F03` (geometry closure), leaf
L2 (interior). -/
theorem localMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmLocalMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl

/-- The canonical global machine store is definitionally the global interior
table's machine store. Serves Stage F row `EG-CP-F03` (geometry closure), leaf
L2 (interior). -/
theorem globalMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmGlobalMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl

/-- The canonical local-level machine store is definitionally the local-level
interior table's machine store. Serves Stage F row `EG-CP-F03` (geometry
closure), leaf L2 (interior). -/
theorem localLevelMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmLocalLevelMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl


/-! ### Per-table machine word-count congruences. -/

/-- The superblock baseline table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem baselineWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSuperblockBaselineEntries_length, bpSuperblockBaselineEntries_length]
  simp only [RelativeRmm.Layout.superWidth]
  rw [layout_congr h, bpLen_congr h]

/-- The block relative-minimum table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem minRelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockRelativeMinExcessEntries_length, bpBlockRelativeMinExcessEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The block relative-maximum table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem maxRelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockRelativeMaxExcessEntries_length, bpBlockRelativeMaxExcessEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The block arg-min offset table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem argOffsetWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpBlockArgMinLocalOffsetEntries_length, bpBlockArgMinLocalOffsetEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The local sparse offset table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem localTableWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpLocalSparseOffsetEntries_length, bpLocalSparseOffsetEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The global sparse block table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem globalTableWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpGlobalSparseBlockEntries_length, bpGlobalSparseBlockEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The local sparse level table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem localLevelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSparseLevelEntries_length, bpSparseLevelEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The global sparse level table occupies a machine-word count fixed by
`size`. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior).
-/
theorem globalLevelWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  rw [machineStore_words_size_closed, machineStore_words_size_closed,
    bpSparseLevelEntries_length, bpSparseLevelEntries_length]
  rw [layout_congr h, bpLen_congr h]

/-- The whole interior component store has a word count fixed by `size`, hence
so does its dead address. Serves Stage F row `EG-CP-F03` (geometry closure),
leaf L2 (interior). -/
theorem componentStoreWords_congr {a b : CartesianShape} (h : a.size = b.size) :
    (canonicalRelativeRmmInteriorComponentStore a).store.words.size =
      (canonicalRelativeRmmInteriorComponentStore b).store.words.size := by
  rw [canonicalRelativeRmmInteriorComponentStore_words_size_eq,
    canonicalRelativeRmmInteriorComponentStore_words_size_eq]
  simp only []
  rw [baselineWords_congr h, minRelWords_congr h, maxRelWords_congr h,
    argOffsetWords_congr h, localTableWords_congr h, globalTableWords_congr h,
    localLevelWords_congr h, globalLevelWords_congr h]

/-- **Campaign obligation `T3`.** All nine interior component offsets -- the
eight prefix-summed table bases and the dead address -- are functions of
`size` alone. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2
(interior). -/
theorem offsets_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalRelativeRmmInteriorComponentOffsets a =
      canonicalRelativeRmmInteriorComponentOffsets b := by
  unfold canonicalRelativeRmmInteriorComponentOffsets
  simp only [localMachineStore_words_size, globalMachineStore_words_size,
    localLevelMachineStore_words_size]
  rw [baselineWords_congr h, minRelWords_congr h, maxRelWords_congr h,
    argOffsetWords_congr h, localTableWords_congr h, globalTableWords_congr h,
    localLevelWords_congr h, componentStoreWords_congr h]


/-! ### The interior read primitive is geometry-only. -/

/-- The interior machine read of a fixed-width table is geometry-only: it sees
the table through its entry count and width, never through its contents.
Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem readNat_congr {a b : CartesianShape} (h : a.size = b.size)
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (hlen : e1.length = e2.length) (hw : w1 = w2) (base i : Nat) :
    canonicalRelativeRmmMachineReadNatComputation a t1 base i =
      canonicalRelativeRmmMachineReadNatComputation b t2 base i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  rw [bpLen_congr h, offsets_congr h]
  exact machineReadComputationAt_geometry_only t1 t2 hlen hw _ _ _ _


/-! ### Site-specific read congruences (index-parameterised). -/

/-- Read-site congruence for the baseline table, parameterised by base and
index so that no dependently typed table survives the rewrite. Serves Stage F
row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_baseline_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).baselineTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).baselineTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSuperblockBaselineEntries_length, bpSuperblockBaselineEntries_length,
      layout_congr h]
  · simp only [RelativeRmm.Layout.superWidth]; rw [bpLen_congr h]

/-- Read-site congruence for the relative-minimum table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_minRel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).minRelTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).minRelTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockRelativeMinExcessEntries_length,
      bpBlockRelativeMinExcessEntries_length, layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the relative-maximum table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_maxRel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).maxRelTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).maxRelTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockRelativeMaxExcessEntries_length,
      bpBlockRelativeMaxExcessEntries_length, layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the arg-min offset table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_argOffset_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmSummaryTable a).argOffsetTable base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmSummaryTable b).argOffsetTable base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpBlockArgMinLocalOffsetEntries_length,
      bpBlockArgMinLocalOffsetEntries_length, layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the local sparse offset table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_localTable_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorLocalTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorLocalTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpLocalSparseOffsetEntries_length, bpLocalSparseOffsetEntries_length,
      layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the global sparse block table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_globalTable_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorGlobalTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorGlobalTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpGlobalSparseBlockEntries_length, bpGlobalSparseBlockEntries_length,
      layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the local sparse level table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_localLevel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorLocalLevelTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorLocalLevelTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]
  · rw [layout_congr h]

/-- Read-site congruence for the global sparse level table. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem readNat_globalLevel_congr {a b : CartesianShape} (h : a.size = b.size)
    {base1 base2 i1 i2 : Nat} (hbase : base1 = base2) (hi : i1 = i2) :
    canonicalRelativeRmmMachineReadNatComputation a
        (canonicalRelativeRmmInteriorGlobalLevelTable a).table base1 i1 =
      canonicalRelativeRmmMachineReadNatComputation b
        (canonicalRelativeRmmInteriorGlobalLevelTable b).table base2 i2 := by
  subst hbase
  subst hi
  refine readNat_congr h _ _ ?_ ?_ _ _
  · rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]
  · rw [layout_congr h]

/-! ### The interior candidate machinery. -/

/-- The per-block summary computation (baseline, relative min and max, arg-min
offset) is size-only. Serves Stage F row `EG-CP-F03` (geometry closure), leaf
L2 (interior). -/
theorem summaryComputation_congr {a b : CartesianShape} (h : a.size = b.size)
    (block : Nat) :
    canonicalRelativeRmmMachineSummaryComputation a block =
      canonicalRelativeRmmMachineSummaryComputation b block := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb1 : (canonicalRelativeRmmInteriorComponentOffsets a).baseline =
      (canonicalRelativeRmmInteriorComponentOffsets b).baseline := by rw [hO]
  have hb2 : (canonicalRelativeRmmInteriorComponentOffsets a).minRel =
      (canonicalRelativeRmmInteriorComponentOffsets b).minRel := by rw [hO]
  have hb3 : (canonicalRelativeRmmInteriorComponentOffsets a).maxRel =
      (canonicalRelativeRmmInteriorComponentOffsets b).maxRel := by rw [hO]
  have hb4 : (canonicalRelativeRmmInteriorComponentOffsets a).argOffset =
      (canonicalRelativeRmmInteriorComponentOffsets b).argOffset := by rw [hO]
  have hi1 : block / (RelativeRmm.canonicalLayout a).blocksPerSuper =
      block / (RelativeRmm.canonicalLayout b).blocksPerSuper := by rw [hL]
  unfold canonicalRelativeRmmMachineSummaryComputation
  simp only []
  rw [readNat_baseline_congr h hb1 hi1, readNat_minRel_congr h hb2 rfl,
    readNat_maxRel_congr h hb3 rfl, readNat_argOffset_congr h hb4 rfl]

/-- The per-block minimum candidate is size-only. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem minCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineMinCandidateComputation a block =
      canonicalRelativeRmmMachineMinCandidateComputation b block := by
  unfold canonicalRelativeRmmMachineMinCandidateComputation
  simp only []
  rw [summaryComputation_congr h, layout_congr h]

/-- The local sparse span candidate is size-only. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem localSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroIdx localStart level : Nat) :
    canonicalRelativeRmmMachineLocalSpanCandidateComputation a
        macroIdx localStart level =
      canonicalRelativeRmmMachineLocalSpanCandidateComputation b
        macroIdx localStart level := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).localOffset =
      (canonicalRelativeRmmInteriorComponentOffsets b).localOffset := by rw [hO]
  have hi :
      bpLocalSparseCellSlot (RelativeRmm.canonicalLayout a).macroSize
          (RelativeRmm.canonicalLayout a).levelCount macroIdx localStart level =
        bpLocalSparseCellSlot (RelativeRmm.canonicalLayout b).macroSize
          (RelativeRmm.canonicalLayout b).levelCount macroIdx localStart
          level := by rw [hL]
  unfold canonicalRelativeRmmMachineLocalSpanCandidateComputation
  simp only []
  rw [readNat_localTable_congr h hb hi, hL]
  apply congrArg
  funext offset
  cases offset with
  | none => rfl
  | some value => exact minCandidateComputation_congr h _

/-- The global sparse span candidate is size-only. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem globalSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart level : Nat) :
    canonicalRelativeRmmMachineGlobalSpanCandidateComputation a
        macroStart level =
      canonicalRelativeRmmMachineGlobalSpanCandidateComputation b
        macroStart level := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).globalBlock =
      (canonicalRelativeRmmInteriorComponentOffsets b).globalBlock := by rw [hO]
  have hi :
      bpGlobalSparseCellSlot (RelativeRmm.canonicalLayout a).macroSampleCount
          macroStart level =
        bpGlobalSparseCellSlot (RelativeRmm.canonicalLayout b).macroSampleCount
          macroStart level := by rw [hL]
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  simp only []
  rw [readNat_globalTable_congr h hb hi]
  apply congrArg
  funext block
  cases block with
  | none => rfl
  | some value => exact minCandidateComputation_congr h _

/-- The two-span local candidate is size-only. Serves Stage F row `EG-CP-F03`
(geometry closure), leaf L2 (interior). -/
theorem localTwoSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroIdx localStart count : Nat) :
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation a
        macroIdx localStart count =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation b
        macroIdx localStart count := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).localLevel =
      (canonicalRelativeRmmInteriorComponentOffsets b).localLevel := by rw [hO]
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  simp only []
  rw [readNat_localLevel_congr h hb rfl, hL]
  apply congrArg
  funext cell
  cases cell with
  | none => rfl
  | some value =>
      simp only []
      rw [localSpanCandidateComputation_congr h,
        localSpanCandidateComputation_congr h]

/-- The two-span global candidate is size-only. Serves Stage F row `EG-CP-F03`
(geometry closure), leaf L2 (interior). -/
theorem globalTwoSpanCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart macroSpanCount : Nat) :
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation a
        macroStart macroSpanCount =
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation b
        macroStart macroSpanCount := by
  have hL := layout_congr h
  have hO := offsets_congr h
  have hb : (canonicalRelativeRmmInteriorComponentOffsets a).globalLevel =
      (canonicalRelativeRmmInteriorComponentOffsets b).globalLevel := by rw [hO]
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  simp only []
  rw [readNat_globalLevel_congr h hb rfl, hL]
  apply congrArg
  funext cell
  cases cell with
  | none => rfl
  | some value =>
      simp only []
      rw [globalSpanCandidateComputation_congr h,
        globalSpanCandidateComputation_congr h]

/-- The adjacent-macro arm of the interior range minimum is size-only. Serves
Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem adjacentMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart localStart rightCount : Nat) :
    canonicalRelativeRmmMachineAdjacentMacroCandidateComputation a
        macroStart localStart rightCount =
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation b
        macroStart localStart rightCount := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    localTwoSpanCandidateComputation_congr h]

/-- The left-middle-macro arm of the interior range minimum is size-only.
Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem leftMiddleMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (macroStart localStart middleMacroCount : Nat) :
    canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation a
        macroStart localStart middleMacroCount =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation b
        macroStart localStart middleMacroCount := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    globalTwoSpanCandidateComputation_congr h]

/-- The macro-crossing arm of the interior range minimum is size-only. Serves
Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem crossMacroCandidateComputation_congr {a b : CartesianShape}
    (h : a.size = b.size)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    canonicalRelativeRmmMachineCrossMacroCandidateComputation a
        macroStart localStart middleMacroCount rightCount =
      canonicalRelativeRmmMachineCrossMacroCandidateComputation b
        macroStart localStart middleMacroCount rightCount := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    globalTwoSpanCandidateComputation_congr h,
    localTwoSpanCandidateComputation_congr h]

/-- The whole interior range-min computation is size-only. -/
theorem interiorRangeMinComputation_congr {a b : CartesianShape}
    (h : a.size = b.size) (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeMinComputation a startBlock count =
      canonicalRelativeRmmInteriorRangeMinComputation b startBlock count := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  simp only []
  rw [layout_congr h, localTwoSpanCandidateComputation_congr h,
    adjacentMacroCandidateComputation_congr h,
    leftMiddleMacroCandidateComputation_congr h,
    crossMacroCandidateComputation_congr h]

/-- The supplied-store interior range-minimum trace is size-only -- the
executable form of the interior obligation consumed by the L2 cross-block arm.
Serves Stage F row `EG-CP-F03` (geometry closure), leaf L2 (interior). -/
theorem interiorRangeMinWithStore_congr {a b : CartesianShape}
    (h : a.size = b.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore) (startBlock count : Nat) :
    concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a segments store startBlock count =
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b segments store startBlock count := by
  unfold concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  rw [interiorRangeMinComputation_congr h]


/-! ### The L2 cross-block arm. -/

/--
**L2 cross-block arm is size-only.**

For any two Cartesian shapes of equal `size`, the supplied-store cross-block
LCA-close consumer — the `else` branch of the L2 dispatcher
(`ChargedFringeWiring.lean:501-503`) — produces the *identical*
`WordRAM.TraceResult`: same ordered trace of read events and same value.

Universally quantified over both shapes, the rank-close sub-trace, the
interior trace segments, the fringe segment, the read store and both close
positions.  No size threshold, no regime restriction.
-/
theorem L2_crossBlock_size_only {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        a rankCloseTrace segments fringeSegment store leftClose rightClose =
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        b rankCloseTrace segments fringeSegment store leftClose rightClose := by
  unfold
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  simp only [blockSizeRaw_congr h, seed_congr h, leftFringe_congr h,
    interiorRangeMinWithStore_congr h, rightFringe_congr h]


/-! ### The L2 same-block arm and the L2 dispatcher. -/

/-- The seeded same-block close computation is size-only. Serves Stage F row
`EG-CP-F03` (geometry closure), leaf L2. -/
theorem sameBlockSeeded_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose rightClose seed =
      bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose rightClose seed := by
  unfold bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  rw [bpLen_congr h, windowBase_congr h, localBPWindowBits_congr h]

/-- The decoded same-block arm of the L2 dispatcher is size-only. Serves Stage
F row `EG-CP-F03` (geometry closure), leaf L2. -/
theorem sameBlockDecoded_congr {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        a rankCloseTrace fringeSegment store blockSize leftClose rightClose =
      bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        b rankCloseTrace fringeSegment store blockSize leftClose rightClose := by
  unfold bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
  simp only [seed_congr h, sameBlockSeeded_congr h]

/--
**Controller leaf L2 is size-only.**

The whole supplied-store LCA-close dispatcher
(`ChargedFringeWiring.lean:487-503`) — its route selector, its same-block arm
and its cross-block arm — returns the identical `WordRAM.TraceResult` for any
two shapes of equal `size`.
-/
theorem L2_lcaClose_size_only {a b : CartesianShape} (h : a.size = b.size)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (sameBlockSegment leftClose rightClose : Nat) :
    lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose =
      lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankCloseTrace segments fringeSegment store sameBlockSegment
        leftClose rightClose := by
  unfold lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [blockSizeRaw_congr h]
  by_cases hs :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw b) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw b) rightClose
  · simp only [hs, if_pos]
    exact sameBlockDecoded_congr h _ _ _ _ _ _
  · simp only [hs, if_false]
    exact L2_crossBlock_size_only h _ _ _ _ _ _


/-! ### Bonus: the rank-close leaf L3, and the L2 leaf at the controller route. -/

/-- The campaign's O3 obligation, re-proved here (`t1map_obligations.lean:61`). -/
theorem chunkedRank_geometry_only
    {b1 b2 : List Bool} {s1 k1 q1 s2 k2 q2 : Nat}
    (d1 : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b1 s1 k1 q1)
    (d2 : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b2 s2 k2 q2)
    (hlen : b1.length = b2.length)
    (hword : d1.wordSize = d2.wordSize)
    (hblocks : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos =
      d2.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hword, hblocks]

/-- The built rank data's word size is a function of `size` alone. Serves
Stage F row `EG-CP-F03` (geometry closure), leaf L3. -/
theorem rankWordSize_congr {a b : CartesianShape} (h : a.size = b.size) :
    (SuccinctFinal.builtRelativeSplitBPCloseRankData a).wordSize =
      (SuccinctFinal.builtRelativeSplitBPCloseRankData b).wordSize := by
  show SuccinctRank.machineWordBits a.bpCode.length =
    SuccinctRank.machineWordBits b.bpCode.length
  rw [bpLen_congr h]

/-- The built rank data's blocks-per-superblock stride is a function of `size`
alone. Serves Stage F row `EG-CP-F03` (geometry closure), leaf L3. -/
theorem rankBlocksPerSuper_congr {a b : CartesianShape} (h : a.size = b.size) :
    (SuccinctFinal.builtRelativeSplitBPCloseRankData a).blocksPerSuper =
      (SuccinctFinal.builtRelativeSplitBPCloseRankData b).blocksPerSuper := by
  show SuccinctRank.machineWordBits a.bpCode.length =
    SuccinctRank.machineWordBits b.bpCode.length
  rw [bpLen_congr h]

/-- **Controller leaf L3 (rank-close) is size-only.** -/
theorem L3_rankClose_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (rankSegmentBase pos : Nat) :
    SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store rankSegmentBase pos =
      SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store rankSegmentBase pos := by
  unfold SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [bpLen_congr h]
  exact chunkedRank_geometry_only _ _ (bpLen_congr h) (rankWordSize_congr h)
    (rankBlocksPerSuper_congr h) _ _ _ _ _ _ _ _

/-- **Controller leaf L2 at the controller route is size-only.** -/
theorem L2_route_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (leftClose rightClose : Nat) :
    SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store leftClose rightClose =
      SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store leftClose rightClose := by
  have hrank :
      SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          a store SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase =
        SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          b store SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact L3_rankClose_size_only h store _ pos
  unfold
    SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  rw [hrank]
  exact L2_lcaClose_size_only h _ _ _ _ _ _ _


/-! ### Bonus: the whole-query capstone (campaign T4). -/

open RMQ.SuccinctFinal in
/-- **The controller's instruction semantics are size-only.** Every one of the
four `WholeQueryInstr` constructors -- the three shape-consuming leaves and
the shape-free output instruction -- produces the identical trace and state
for two equal-size shapes. Serves Stage F row `EG-CP-F03` (geometry closure),
universal consumer. -/
theorem wholeQueryInstr_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore a store left right state =
      instr.evalGlobalWordTraceWithStore b store left right state := by
  cases instr with
  | selectClose dst idx =>
      simp only [WholeQueryInstr.evalGlobalWordTraceWithStore]
      rw [SelectLeaf.L1_route_shape_size_only h]
  | lcaClose dst leftReg rightReg =>
      cases hl : state.opt leftReg with
      | none =>
          cases hr : state.opt rightReg <;>
            simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
      | some lc =>
          cases hr : state.opt rightReg with
          | none =>
              simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
          | some rc =>
              simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hl, hr]
              rw [L2_route_size_only h]
  | rankCloseIfSome dst guard pos =>
      cases hg : state.opt guard with
      | none => simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]
      | some v =>
          simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]
          rw [L3_rankClose_size_only h]
  | outputPredIfSome dst guard src =>
      cases hg : state.opt guard <;>
        simp only [WholeQueryInstr.evalGlobalWordTraceWithStore, hg]

open RMQ.SuccinctFinal in
/-- **The controller evaluator is size-only for every program**, not just the
fixed five-instruction one: the quantifier ranges over all `WholeQueryProgram`
values and all starting states. Serves Stage F row `EG-CP-F03` (geometry
closure), universal consumer. -/
theorem wholeQueryProgram_congr {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (left right : Nat) :
    forall (program : WholeQueryProgram) (state : WholeQueryState),
      WholeQueryProgram.evalGlobalWordTraceWithStore a store left right
          program state =
        WholeQueryProgram.evalGlobalWordTraceWithStore b store left right
          program state := by
  intro program
  induction program with
  | nil => intro state; rfl
  | cons instr rest ih =>
      intro state
      unfold WholeQueryProgram.evalGlobalWordTraceWithStore
      rw [wholeQueryInstr_congr h]
      apply congrArg
      funext state'
      exact ih state'

/--
**T4 — the literal `EG-CP-F03` geometry-closure statement.**

For all Cartesian shapes `a b` with `a.size = b.size`, all read stores and all
endpoints, the whole-query controller's *ordered logical read footprint* and its
*output value* coincide.  No size threshold, no regime restriction.
-/
theorem T4_wholeQuery_size_only {a b : CartesianShape} (h : a.size = b.size)
    (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        a store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        b store l r
    /\ (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          a store l r).value =
        (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          b store l r).value := by
  have hres :
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          a store l r =
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          b store l r := by
    unfold
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    rw [wholeQueryProgram_congr h]
  refine ⟨?_, ?_⟩
  · unfold
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    rw [hres]
  · rw [hres]

/-- The strictly stronger form actually proved: the entire trace agrees, not
just its read projection and the value. -/
theorem T4_wholeQuery_trace_size_only {a b : CartesianShape}
    (h : a.size = b.size) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        a store l r =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        b store l r := by
  unfold
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  rw [wholeQueryProgram_congr h]


/-! ## The public `List Int` entry

Everything above is stated at `RMQ.Cartesian.CartesianShape`.  This section
transports the capstone across the public boundary
`RMQ.SuccinctClassic.queryTraceResultWithStore`, which is what actually retires
the free-shape gap for the row: it says the whole public route factors through
`(n, store, l, r)`.
-/

/-! ### 7.1 The two boundary facts. -/

/-- `SuccinctClassic.cartesianShape` is `Cartesian.shape`
(`RMQ/Core/SuccinctRMQClassic.lean:20`), so `Cartesian.shape_size`
(`RMQ/Core/Shape.lean:128`) gives its size directly. -/
theorem cartesianShape_size (xs : List Int) :
    (SuccinctClassic.cartesianShape xs).size = xs.length := by
  unfold SuccinctClassic.cartesianShape
  exact Cartesian.shape_size xs

/-- Two equal-length lists have equal-size Cartesian shapes. -/
theorem cartesianShape_size_congr {xs ys : List Int} (h : xs.length = ys.length) :
    (SuccinctClassic.cartesianShape xs).size =
      (SuccinctClassic.cartesianShape ys).size := by
  rw [cartesianShape_size, cartesianShape_size, h]

/-- The public validity guard `RMQ.ValidRange` (`RMQ/Core/Spec.lean:14`) is
`left < right /\ right <= xs.length` — it depends on the list only through its
length, so the guard agrees for equal-length lists. -/
theorem validRange_congr {xs ys : List Int} (h : xs.length = ys.length)
    (l r : Nat) :
    RMQ.ValidRange xs l r <-> RMQ.ValidRange ys l r := by
  unfold RMQ.ValidRange
  rw [h]

/-! ### 7.2 The public corollary. -/

/--
**T4 at the public entry.**

For any two `List Int` of the same length, any supplied read store and any
endpoints, the public guarded query produces the *identical* `TraceResult` —
identical ordered event list and identical value.  Nothing about the lists
beyond their common length can be observed by the executed controller.
-/
theorem queryTraceResultWithStore_size_only
    (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (h : xs.length = ys.length) :
    SuccinctClassic.queryTraceResultWithStore xs store l r =
      SuccinctClassic.queryTraceResultWithStore ys store l r := by
  unfold SuccinctClassic.queryTraceResultWithStore SuccinctClassic.withValidRange
  by_cases hv : RMQ.ValidRange xs l r
  · have hv' : RMQ.ValidRange ys l r := (validRange_congr h l r).mp hv
    rw [if_pos hv, if_pos hv']
    exact T4_wholeQuery_trace_size_only (cartesianShape_size_congr h) store l r
  · have hv' : Not (RMQ.ValidRange ys l r) := fun k => hv ((validRange_congr h l r).mpr k)
    rw [if_neg hv, if_neg hv']

/-- The public ordered logical read footprint
(`RMQ/Core/SuccinctRMQClassic.lean:451-456`) agrees too — immediate, since it is
a projection of the trace. -/
theorem orderedReadFootprintWithStore_size_only
    (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (h : xs.length = ys.length) :
    SuccinctClassic.orderedReadFootprintWithStore xs store l r =
      SuccinctClassic.orderedReadFootprintWithStore ys store l r := by
  unfold SuccinctClassic.orderedReadFootprintWithStore
  rw [queryTraceResultWithStore_size_only xs ys store l r h]

/-- The public costed projection agrees (`:246-249`), so the model cost of the
public query is a function of `(n, store, l, r)` as well. -/
theorem queryCostedWithStore_size_only
    (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (h : xs.length = ys.length) :
    SuccinctClassic.queryCostedWithStore xs store l r =
      SuccinctClassic.queryCostedWithStore ys store l r := by
  unfold SuccinctClassic.queryCostedWithStore
  rw [queryTraceResultWithStore_size_only xs ys store l r h]

/-! ### 7.3 The factorisation, stated positively.

A congruence says "equal length implies equal output".  The row's claim is the
positive form: the public route *factors through* `(n, store, l, r)`.  We give
the factorisation explicitly, with a witness function that mentions no list. -/

/-- The canonical `n`-indexed representative of the public query. -/
def publicQueryOfLength
    (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  SuccinctClassic.queryTraceResultWithStore (List.replicate n (0 : Int)) store l r

/-- **The public route factors through `(n, store, l, r)`.**  Every `List Int`
execution equals the length-indexed representative. -/
theorem queryTraceResultWithStore_factors
    (xs : List Int) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore xs store l r =
      publicQueryOfLength xs.length store l r := by
  unfold publicQueryOfLength
  refine queryTraceResultWithStore_size_only xs _ store l r ?_
  simp

/-- Same, for the ordered read footprint. -/
def publicFootprintOfLength
    (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) :=
  SuccinctClassic.orderedReadFootprintWithStore
    (List.replicate n (0 : Int)) store l r

/-- The public ordered read footprint factors through `(n, store, l, r)` as
well. Serves Stage F row `EG-CP-F03` (geometry closure), public entry. -/
theorem orderedReadFootprintWithStore_factors
    (xs : List Int) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.orderedReadFootprintWithStore xs store l r =
      publicFootprintOfLength xs.length store l r := by
  unfold publicFootprintOfLength
  refine orderedReadFootprintWithStore_size_only xs _ store l r ?_
  simp

/-! ### 7.3 Weakening the shared store to the ordered read footprint.

A shared *whole* store is a stronger hypothesis than the roadmap's dependency
model, which permits only `n`, the endpoints, and the contents returned by
**prior probes** (`docs/internal/RMQ_ENDGAME_ROADMAP.md:327-338`).  Sharing a
total function does not by itself forbid dependence on addresses the execution
never probes.

The gap closes against a theorem that predates this module:
`RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint`
(`RMQ/Core/SuccinctRMQClassic.lean:1298`, exported as the headline
`RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint`),
which says agreement on the ordered read footprint alone already determines the
decoded result, the cost, the ordered trace, repeated reads and failed reads.
Chaining the two gives the composite below.
-/

/--
**Length plus footprint determines the execution.**

Two inputs of equal length, and two stores that agree *only* on the ordered read
footprint of the first -- that is, only at the addresses the execution actually
probes -- produce the identical `TraceResult`.

Neither the input content beyond its length, nor any store value away from the
probed addresses, can be observed by the executed controller.  Serves Stage F
row `EG-CP-F03` (geometry closure): this is the form stated against the
roadmap's dependency model rather than against a shared whole store.
-/
theorem queryTraceResultWithStore_length_and_footprint
    (xs ys : List Int) (storeA storeB : WordRAM.ReadStore) (l r : Nat)
    (hlen : xs.length = ys.length)
    (hagree : SuccinctClassic.storesAgreeOnOrderedReadFootprint xs storeA storeB l r) :
    SuccinctClassic.queryTraceResultWithStore xs storeA l r =
      SuccinctClassic.queryTraceResultWithStore ys storeB l r := by
  rw [SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint
        xs storeA storeB l r hagree]
  exact queryTraceResultWithStore_size_only xs ys storeB l r hlen

/-- The ordered read footprint itself is determined by the length together with
footprint agreement.  Serves Stage F row `EG-CP-F03` (geometry closure). -/
theorem orderedReadFootprintWithStore_length_and_footprint
    (xs ys : List Int) (storeA storeB : WordRAM.ReadStore) (l r : Nat)
    (hlen : xs.length = ys.length)
    (hagree : SuccinctClassic.storesAgreeOnOrderedReadFootprint xs storeA storeB l r) :
    SuccinctClassic.orderedReadFootprintWithStore xs storeA l r =
      SuccinctClassic.orderedReadFootprintWithStore ys storeB l r := by
  unfold SuccinctClassic.orderedReadFootprintWithStore
  rw [queryTraceResultWithStore_length_and_footprint xs ys storeA storeB l r hlen hagree]

/-! ### 7.4 Anti-vacuity for the footprint hypothesis.

`storesAgreeOnOrderedReadFootprint` would be worthless if it forced the two
stores to be equal -- the composite above would then say no more than the
shared-whole-store form it is meant to strengthen.  It does not: the predicate
is satisfied by stores differing at *every* address the execution does not
probe. -/

/-- One address of a read store overwritten. -/
def readStoreUpdate (store : WordRAM.ReadStore) (s i : Nat)
    (w : Option WordRAM.Word) : WordRAM.ReadStore where
  readWord? := fun seg idx => if seg = s ∧ idx = i then w else store.readWord? seg idx

/-- Overwriting any address **outside** the ordered read footprint preserves
footprint agreement.  Anti-vacuity witness for
`queryTraceResultWithStore_length_and_footprint`: its store hypothesis is
strictly weaker than store equality. -/
theorem storesAgreeOnOrderedReadFootprint_readStoreUpdate_off_footprint
    (xs : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (s i : Nat) (w : Option WordRAM.Word)
    (hnot : (s, i) ∉ SuccinctClassic.orderedReadFootprintWithStore xs store l r) :
    SuccinctClassic.storesAgreeOnOrderedReadFootprint xs store
      (readStoreUpdate store s i w) l r := by
  intro seg idx hmem
  by_cases h : seg = s ∧ idx = i
  · exfalso
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    exact hnot hmem
  · simp [readStoreUpdate, h]

/-- The composite applied off the diagonal in *both* arguments at once: the
inputs differ beyond their common length, and the stores differ away from the
probed addresses.  Serves Stage F row `EG-CP-F03` (geometry closure). -/
theorem queryTraceResultWithStore_length_and_footprint_off_diagonal
    (xs ys : List Int) (store : WordRAM.ReadStore) (l r : Nat)
    (s i : Nat) (w : Option WordRAM.Word)
    (hlen : xs.length = ys.length)
    (hnot : (s, i) ∉ SuccinctClassic.orderedReadFootprintWithStore xs store l r) :
    SuccinctClassic.queryTraceResultWithStore xs store l r =
      SuccinctClassic.queryTraceResultWithStore ys (readStoreUpdate store s i w) l r :=
  queryTraceResultWithStore_length_and_footprint xs ys store
    (readStoreUpdate store s i w) l r hlen
    (storesAgreeOnOrderedReadFootprint_readStoreUpdate_off_footprint
      xs store l r s i w hnot)

end GeometryClosure
end SuccinctFinal
end RMQ

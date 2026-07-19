import RMQ.Core.WordRAM.E1InteriorChunkFold
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory

/-! # The chunk fold's two carried premises, discharged at the interior store

`interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1795`) carries BOTH
`hccPos : 0 < chunkCount` and `hccCap : chunkCount <= 8`;
`interiorChunkFold_cOut_eq_routeDecode` (`E1InteriorChunkValue.lean:529`)
carries the cap.  This module discharges BOTH at
`canonicalRelativeRmmInteriorComponentStore` -- the ONE store the interior
composition instantiates the fold against -- for ALL EIGHT of its tables,
UNCONDITIONALLY in `shape`.

The cap and the positivity are audited TOGETHER on purpose.  They fail in
opposite directions and either failure is fatal in the same way: an
unsatisfiable cap would make the fold uninstantiable, and an unsatisfiable
positivity would too, while a cap that held only because the count were
always zero would make the fold's read vacuous.  Checking one without the
other settles nothing.

## Why this module exists at all

Its sibling premise did not survive the same audit.  M3d-14 found that the
fold's width premise, recorded as an unproved debt "sourced on the store
side", was in fact UNSATISFIABLE at this store: it demanded
`w.length = wordSize` of every chunk, and seven of the eight tables are
strictly narrower than `wordSize`.  Everything composed on it would have
rested on a hypothesis nobody could discharge.  An unproved premise and an
unsatisfiable one look identical at the definition site, so the cap is
settled HERE, before composition, rather than discovered mid-proof.

The verdict is favourable -- but NOT for the reason that was expected, and
the difference is recorded because it changes which lemma consumers may cite.

## The expected route does not work; the general one does

The anticipated discharge was `chunkCount <= 1` from
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`).  It fails twice:

1. WRONG SHAPE.  `cost_le_one` concludes `(... ).cost <= 1`, a statement about
   the route's COST, not about `fixedWidthNatTableMachineChunkCount`.  The two
   coincide only on the valid arm of the `i < entries.length` split, after
   unfolding the footprint; `hcap` needs the chunk count itself.
2. HYPOTHESIS UNAVAILABLE.  `cost_le_one` needs
   `width <= machineWordBits shape.bpCode.length`.  For `minRelTable`,
   `maxRelTable` and `argOffsetTable` that bound is NOT unconditional: the
   only `relativeWidth` bounds against ONE machine word are
   `canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four`
   (`:3970`, needs `4 <= shape.size`) and
   `canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount`
   (`:4104`, needs macro crossing).  The unconditional bound is
   `canonicalRelativeRmmRelativeWidth_le_seven_machine` (`:3855`), against
   SEVEN words.

So `interiorChunkCount_le_eight` -- cast as the general fallback -- is the
only route that discharges without side conditions, and it suffices for every
table.  This is the same asymmetry that makes the 37-instruction FOLD, not the
7-instruction atom, the right composition target: the atom's
`width <= wordSize` obligation is exactly the one that is conditional here.

## What this module does NOT establish -- and a correction it forces

It does not claim the interior is single-chunk.  It claims only `<= 8`, which
is all `hcap` asks.  AND THE INTERIOR IS NOT SINGLE-CHUNK.  Evaluating the
route's own chunk count at the relative width -- `wordSize` is
`machineWordBits (2 * size)` and `relativeWidth` is
`2 * machineWordBits (machineWordBits size) + 3`, both computable, since
`machineWordBits n = Nat.log2 n + 1` (`SuccinctRank.lean:38`) -- gives
`(size, wordSize, relativeWidth, chunkCount)`:

    (1, 2, 5, 3)   (2, 3, 7, 3)   (4, 4, 7, 2)   (8, 5, 9, 2)
    (16, 6, 9, 2)  (64, 8, 9, 2)  (256, 10, 11, 2)
    (1024, 12, 11, 1)  (4096, 14, 11, 1)  (65536, 18, 13, 1)

The relative tables are genuinely MULTI-CHUNK for every `shape.size` below
roughly `1024`, and three-chunk at the smallest sizes.  They become
single-chunk only asymptotically, as `2 * log2 (log2 size)` falls behind
`log2 (2 * size)`.

TWO CONSEQUENCES, both load-bearing.

1. THE CAP IS NOT TRIVIAL.  `chunkCount` really does exceed one at reachable
   shapes, so `hcap` constrains a live quantity rather than a constant.  It
   is also why the `<= 1` route was worth rejecting on more than shape
   grounds: at `size = 4` that bound is simply FALSE.

2. `hexact` IS NOT VACUOUS, and the reason recorded for it does not hold.
   DD-20260719-009 discharged the value bridge's exactness premise at this
   store by declaring it "VACUOUS there, because the interior tables are
   single-chunk", citing `cost_le_one`.  For `shape.size < 1024` the tables
   are not single-chunk, so `hexact` is a LIVE obligation at exactly the
   small shapes an all-size claim must cover.  It is still SATISFIABLE -- but
   substantively, not vacuously: `chunkPayloadWords` emits chunks of length
   exactly `wordSize` except possibly the last, and
   `chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`) exposes the
   chunk at index `k` as a `take wordSize` of a `drop`, which is full whenever
   a later chunk exists.  Whoever composes the value bridge must discharge
   `hexact` from THAT, and must not cite vacuity.  See DD-20260719-010.

Nothing here is vacuous: every theorem below is hypothesis-free apart from the
shape itself, so each holds at every `Cartesian.CartesianShape` there is.

See DD-20260719-010 (claimed this session; maximum OBSERVED was
`DD-20260719-009`).
-/

open RMQ
open RMQ.SuccinctClose
open RMQ.WordRAM.E1InteriorChunkFold

namespace RMQ
namespace WordRAM
namespace E1InteriorChunkCap

/-- Baseline (super) table: `superWidth` is exactly one machine word, so the
cap holds with six words to spare. -/
theorem chunkCount_le_eight_superWidth (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        ((RelativeRmm.canonicalLayout shape).superWidth shape)
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 := by
  apply interiorChunkCount_le_eight
  have hpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
  simp [RelativeRmm.Layout.superWidth]
  omega

/-- `minRelTable`, `maxRelTable` and `argOffsetTable` all carry
`relativeWidth`.  This is the case where the `<= wordSize` bound is
unavailable without a side condition. -/
theorem chunkCount_le_eight_relativeWidth (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).relativeWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 :=
  interiorChunkCount_le_eight
    (canonicalRelativeRmmRelativeWidth_le_seven_machine shape)

/-- Interior local sparse offset table. -/
theorem chunkCount_le_eight_offsetWidth (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).offsetWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 :=
  interiorChunkCount_le_eight
    (canonicalRelativeRmmOffsetWidth_le_seven_machine shape)

/-- Interior global sparse block table. -/
theorem chunkCount_le_eight_blockAddressWidth
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).blockAddressWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 :=
  interiorChunkCount_le_eight
    (canonicalRelativeRmmBlockWidth_le_seven_machine shape)

/-- Interior local level/span table. -/
theorem chunkCount_le_eight_localLevelWidth
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize))
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 :=
  interiorChunkCount_le_eight
    (bpSparseLevelLocalWidth_le_seven_machine shape)

/-- Interior global level/span table. -/
theorem chunkCount_le_eight_globalLevelWidth
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount))
        (SuccinctRank.machineWordBits shape.bpCode.length) ≤ 8 :=
  interiorChunkCount_le_eight
    (bpSparseLevelGlobalWidth_le_seven_machine shape)

/-! ## The other carried premise: `0 < chunkCount`

Every one of the eight widths is positive by construction, so the fold's read
is never vacuous at this store.  `superWidth`, `offsetWidth` and
`blockAddressWidth` are `machineWordBits` of something and positive by
`machineWordBits_pos`; `relativeWidth` is `2 * _ + 3`; `bpSparseLevelWidth` is
`Nat.log2 _ + 1`.  None of these needs a side condition, so `hccPos` is
available on exactly the same terms as the cap.

Note this is the half `canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
could not have supplied even if its shape had matched: a COST bound is an
upper bound and says nothing about the count being nonzero.  A zero-width
table would read nothing while the fold still reads once.
-/

theorem chunkCount_pos_superWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        ((RelativeRmm.canonicalLayout shape).superWidth shape)
        (SuccinctRank.machineWordBits shape.bpCode.length) :=
  interiorChunkCount_pos (SuccinctRank.machineWordBits_pos _)

theorem chunkCount_pos_relativeWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).relativeWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) := by
  apply interiorChunkCount_pos
  have h : (RelativeRmm.canonicalLayout shape).relativeWidth
      = 2 * SuccinctRank.machineWordBits
          (SuccinctRank.machineWordBits shape.size) + 3 := rfl
  omega

theorem chunkCount_pos_offsetWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).offsetWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) :=
  interiorChunkCount_pos (SuccinctRank.machineWordBits_pos _)

theorem chunkCount_pos_blockAddressWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (RelativeRmm.canonicalLayout shape).blockAddressWidth
        (SuccinctRank.machineWordBits shape.bpCode.length) :=
  interiorChunkCount_pos (SuccinctRank.machineWordBits_pos _)

theorem chunkCount_pos_localLevelWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize))
        (SuccinctRank.machineWordBits shape.bpCode.length) := by
  apply interiorChunkCount_pos
  have h : bpSparseLevelWidth
      (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
      = Nat.log2 ((bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSize) *
        (Nat.log2 (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSize) + 1)) + 1 := rfl
  omega

theorem chunkCount_pos_globalLevelWidth (shape : Cartesian.CartesianShape) :
    0 < SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount))
        (SuccinctRank.machineWordBits shape.bpCode.length) := by
  apply interiorChunkCount_pos
  have h : bpSparseLevelWidth
      (bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount)
      = Nat.log2 ((bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) *
        (Nat.log2 (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) + 1)) + 1 := rfl
  omega

end E1InteriorChunkCap
end WordRAM
end RMQ

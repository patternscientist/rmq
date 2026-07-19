import RMQ.Core.WordRAM.E1InteriorChunkStore
import RMQ.Core.SuccinctFinal.RAM.Segments

/-! # The interior store clauses, INSTANTIATED at the store the route runs against

`E1InteriorChunkStore` states twelve clauses -- eight `hagree_*`, four
`hexact_*` -- conditional on `HoldsInteriorStore store segment shape`, and
witnesses that hypothesis SATISFIABLE by `interiorReadStore`, a store built
to hold the directory.  M3d-17 recorded, against its own output, that this
is the same shape of witness that hid the false unbounded `hagree`: a store
constructed FOR the hypothesis is not the store the interior program runs
against, so satisfiability there establishes nothing about the target.

THIS MODULE ELIMINATES THE HYPOTHESIS RATHER THAN WITNESSING IT.

## The target is not a matter of choice

`crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean:1143`) fixes it.  Its
`hInterior` premise demands the interior leg's `RunsTo` at
`concreteBPNativeSuccinctRMQGlobalReadStore shape` -- named in the theorem
statement, not selectable by the interior's author.  So that store, at the
segment the interior route reads, is where `HoldsInteriorStore` must hold,
and no other store's behaviour is relevant.

## It holds there, and the tree already knew it

`concreteBPNativeSuccinctRMQGlobalReadStore` answers segment `20` with
`(canonicalRelativeRmmInteriorComponentStore shape).store.words[index]?`
(`Segments.lean:221`), and `concreteBPNativeInteriorTraceSegments`
(`Segments.lean:60`) sets `canonicalComponent := 20`, which is the segment
the interior route's reads are emitted at.  The projection
`concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent`
(`Segments.lean:258`) was ALREADY IN THE TREE, proved before this campaign
reached the interior.  `holdsInteriorStore_concrete` is that projection plus
the `Array`/`List` bridge, and nothing else.

This is a discharge FOUND at the target, not a witness BUILT for the
premise -- the distinction M3d-17's fifth standing rule turns on.  Every
clause below is unconditional: there is no hypothesis left for a convenient
witness to satisfy.

See DD-20260719-013.  The parameterised forms in `E1InteriorChunkStore` are
retained as the general lemmas these instantiate, exactly as
`readWord?_slice` is retained beneath them; what changes is that the
DELIVERED clauses -- the ones the summary group consumes -- carry no
agreement hypothesis, matching every prior E1 module
(`E1RankCanonical.lean:127`, `E1CrossBlockArm.lean:1143`,
`ChargedRankSelectWiring.lean:970`).
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorStoreConcrete

open RMQ.WordRAM.E1InteriorChunkExact
open RMQ.WordRAM.E1InteriorChunkFold
open RMQ.WordRAM.E1InteriorChunkStore

/-- The segment the interior route's reads are emitted at, in the canonical
global store.  Named rather than spelled `20` so that a layout change moves
this module with the layout. -/
abbrev interiorSegment : Nat :=
  concreteBPNativeInteriorTraceSegments.canonicalComponent

/-! ## The discharge -/

/-- THE SETUP HYPOTHESIS, DISCHARGED AT THE TARGET STORE.

`concreteBPNativeSuccinctRMQGlobalReadStore` is the store
`crossBlockArmProgramAt_runsTo`'s `hInterior` names; `interiorSegment` is
where the interior route reads.  There it holds the interior directory --
by the tree's own segment-20 projection, which predates this campaign's
interior work and was written for the flat layout rather than for this
premise. -/
theorem holdsInteriorStore_concrete (shape : Cartesian.CartesianShape) :
    HoldsInteriorStore (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      interiorSegment shape := by
  intro a
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent]
  simp

/-! ## The eight agreement clauses, unconditional

Each is the `E1InteriorChunkStore` clause with its `HoldsInteriorStore`
parameter SUPPLIED by `holdsInteriorStore_concrete` rather than assumed.
No hypothesis remains. -/

theorem hagree_baseline_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsBaseline shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).baseline + a) =
        (wordsBaseline shape)[a]? :=
  hagree_baseline (holdsInteriorStore_concrete shape)

theorem hagree_minRel_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsMinRel shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).minRel + a) =
        (wordsMinRel shape)[a]? :=
  hagree_minRel (holdsInteriorStore_concrete shape)

theorem hagree_maxRel_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsMaxRel shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).maxRel + a) =
        (wordsMaxRel shape)[a]? :=
  hagree_maxRel (holdsInteriorStore_concrete shape)

theorem hagree_argOffset_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsArgOffset shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).argOffset + a) =
        (wordsArgOffset shape)[a]? :=
  hagree_argOffset (holdsInteriorStore_concrete shape)

theorem hagree_local_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsLocal shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).localOffset + a) =
        (wordsLocal shape)[a]? :=
  hagree_local (holdsInteriorStore_concrete shape)

theorem hagree_global_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsGlobal shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock + a) =
        (wordsGlobal shape)[a]? :=
  hagree_global (holdsInteriorStore_concrete shape)

theorem hagree_localLevel_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsLocalLevel shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).localLevel + a) =
        (wordsLocalLevel shape)[a]? :=
  hagree_localLevel (holdsInteriorStore_concrete shape)

theorem hagree_globalLevel_concrete (shape : Cartesian.CartesianShape) :
    ∀ a, a < (wordsGlobalLevel shape).length →
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          ((canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel + a) =
        (wordsGlobalLevel shape)[a]? :=
  hagree_globalLevel (holdsInteriorStore_concrete shape)

/-! ## The four exactness clauses, unconditional

The summary group's four reads.  `hcount`, `hvalid`, `hentries` remain --
they are facts about the CALLER's index arithmetic, fixed when the summary
group's program is written, and were never debts owed to the store.  What
is gone is the store hypothesis. -/

theorem hexact_baseline_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      ((RelativeRmm.canonicalLayout shape).superWidth shape)
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpSuperblockBaselineEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).superSampleCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).baseline
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_baseline (holdsInteriorStore_concrete shape) hcount hvalid hentries

theorem hexact_minRel_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockRelativeMinExcessEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).minRel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_minRel (holdsInteriorStore_concrete shape) hcount hvalid hentries

theorem hexact_maxRel_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockRelativeMaxExcessEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).maxRel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_maxRel (holdsInteriorStore_concrete shape) hcount hvalid hentries

theorem hexact_argOffset_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).relativeWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpBlockArgMinLocalOffsetEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blockCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart (canonicalRelativeRmmInteriorComponentOffsets shape).argOffset
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_argOffset (holdsInteriorStore_concrete shape) hcount hvalid hentries

/-! ## The two SPAN tables' exactness clauses, on the same terms

`E1InteriorSpanBlock.spanBlock` reads the interior's local sparse offset
table and its global sparse block table.  `hexact_local` and
`hexact_global` (`E1InteriorChunkStore.lean`) already carry the store
side; these two discharge the store hypothesis at the concrete store by
`holdsInteriorStore_concrete`, exactly as the four above do.  Only the
width and the entry list differ. -/

theorem hexact_local_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).offsetWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpLocalSparseOffsetEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blockCount
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).macroSampleCount
      (RelativeRmm.canonicalLayout shape).levelCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart
            (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_local (holdsInteriorStore_concrete shape) hcount hvalid hentries

theorem hexact_global_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (RelativeRmm.canonicalLayout shape).blockAddressWidth
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpGlobalSparseBlockEntries shape
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blockCount
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).macroSampleCount
      (RelativeRmm.canonicalLayout shape).globalLevelCount).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart
            (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_global (holdsInteriorStore_concrete shape) hcount hvalid hentries

/-! ## The two LEVEL tables' exactness clauses, on the same terms

`E1InteriorTwoSpan.twoSpanBlock`'s unconditional head is a read of one of
the two level/span tables.  `hexact_localLevel` and `hexact_globalLevel`
(`E1InteriorChunkStore.lean`) carry the store side; these two discharge
the store hypothesis at the concrete store by
`holdsInteriorStore_concrete`, exactly as the six above do. -/

theorem hexact_localLevel_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize))
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpSparseLevelEntries
      (bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSize)).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart
            (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_localLevel (holdsInteriorStore_concrete shape) hcount hvalid hentries

theorem hexact_globalLevel_concrete
    {shape : Cartesian.CartesianShape} {deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount
      (bpSparseLevelWidth
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount))
      (SuccinctRank.machineWordBits shape.bpCode.length))
    (hvalid : i < entriesLen)
    (hentries : i < (bpSparseLevelEntries
      (bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount)).length) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? interiorSegment
          (chunkStart
            (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
            deadAddress entriesLen chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length :=
  hexact_globalLevel (holdsInteriorStore_concrete shape) hcount hvalid hentries

end E1InteriorStoreConcrete
end WordRAM
end RMQ

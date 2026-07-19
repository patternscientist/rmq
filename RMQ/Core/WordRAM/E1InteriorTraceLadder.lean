import RMQ.Core.WordRAM.E1InteriorDispatchCompose

/-!
# THE TRACE LADDER: machine event lists against route read logs

**THE OBLIGATION THIS MODULE DISCHARGES.** `dispatchEvents`
(`E1InteriorDispatchCompose.lean:194`) is built from `twoSpanEvents`
(`E1InteriorTwoSpan.lean:212`), which is built from `spanEvents`
(`E1InteriorSpanBlock.lean:187`).  Until this module, that whole tower was
FREESTANDING: every theorem mentioning any of the three supplied it as a
`RunsTo` receipt argument, and no theorem anywhere equated it to a
computation's `.reads`.  The VALUE side was already route-linked all the
way up (`spanValue_localSpan_eq_routeValue`
`E1InteriorSpanBlock.lean:773`, `twoSpanValue_local_eq_routeValue`
`E1InteriorTwoSpan.lean:1085`, and their global twins); the TRACE side was
not linked at all.

**THE PRECEDENT COPIED IS `minCandidateMachineTrace_eq_routeReads`
(`E1InteriorMinCandidate.lean:1296`)**, which does exactly this one rung
lower -- it equates the composed min-candidate leg's four `geomEvents` to
the min-candidate computation's read log.  That theorem is the BOTTOM of
this ladder and is consumed unchanged at `legEvents_eq_routeReads` below.

**THE LADDER IS BUILT AS THE EXACT TRACE TWIN OF THE VALUE LADDER**, rung
for rung, reusing the value ladder's OWN cell-correspondence lemmas
(`cellOpt_spanCell_localSpan` `E1InteriorSpanBlock.lean:702`,
`cellOpt_levelCell_localLevel` `E1InteriorTwoSpan.lean:981`, and their
global twins).  That reuse is the point: the trace side and the value side
now dispatch on the SAME decoded cell, so a defect that moved one without
the other could not be absorbed by restating either.

**WHY A SEPARATE MODULE.** Every rung's dependencies are already public,
so nothing here required editing `E1InteriorSummaryGroup.lean`,
`E1InteriorSpanBlock.lean`, `E1InteriorTwoSpan.lean` or
`E1InteriorDispatchCompose.lean`.  Keeping the ladder out of those four
means the whole-query modules downstream of them do not recompile while it
is being built, and -- more durably -- it means this module can be read as
one object rather than as four insertions.

**EVERY EQUATION HERE IS POSITIONAL AND HYPOTHESIS-FREE.** Both sides are
lists, so each equation constrains every event in every position; and no
rung carries a validity, cap or store hypothesis, exactly as the value
ladder's rungs do not.  The generic bottom rung carries the same three
alignment hypotheses as `geomRouteDecode_eq_readComputation_value`
(`E1InteriorSummaryGroup.lean:904`), each `rfl` at every instantiation.

**THE SEGMENT AND STORE ARE RECONCILED BY CONSTRUCTION, NOT ASSUMED.**
The machine side is fixed at `(canonicalSummaryLayout shape).segment` with
`concreteBPNativeSuccinctRMQGlobalReadStore shape`; every route object
below is run at
`flatWordStoreOfReadStore (concreteBPNativeSuccinctRMQGlobalReadStore shape)
(canonicalSummaryLayout shape).segment`, which is the same store at the
same segment.  The route objects are `shape`-level rather than parametric
in `segments.canonicalComponent`, so no further reconciliation is owed at
this level.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorTraceLadder

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1Machine
open E1InteriorSummaryGroup (TableGeom SummaryLayout canonicalSummaryLayout
  geomEvents)
open E1InteriorMinCandidate (cellOpt)
open E1InteriorSpanBlock (localSpanGeom globalSpanGeom legEvents spanEvents)
open E1InteriorTwoSpan (twoSpanEvents localLevelGeom globalLevelGeom)
open E1InteriorDispatchCompose (localLegEvents globalLegEvents dispatchEvents)

/-! ## Rung 0 -- ONE STAGED READ

The generic bridge.  Both sides reduce to the same `chunkAddrs` list under
the same store lookup; the map is the injection
`(address, word) ↦ TraceEvent.readWord segment address word`, which is how
the operational read log and the machine's trace vocabulary differ.  It is
a change of spelling, not of content -- the same sentence
`geomEvents_eq_summaryReadReceipt_map` (`E1InteriorMinCandidate.lean:1237`)
makes at the four summary tables, here made generic in `table`, `L` and
`G` so that it also serves the LOCAL and GLOBAL span and level
geometries. -/
theorem geomEvents_eq_readComputation_reads
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (L : SummaryLayout) (G : TableGeom) (i : Nat)
    (hdead : L.deadAddress =
      (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress)
    (hentries : G.entriesLen = entries.length)
    (hchunk : G.chunkCount =
      SuccinctSpace.fixedWidthNatTableMachineChunkCount width
        (SuccinctRank.machineWordBits shape.bpCode.length)) :
    geomEvents store L G i =
      ((canonicalRelativeRmmMachineReadNatComputation shape table G.base i).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore store L.segment)).reads.map
        (fun p => TraceEvent.readWord L.segment p.1 p.2) := by
  rw [E1InteriorSummaryGroup.geomReadComputation_reads shape store table L G i
    hdead hentries hchunk]
  simp [E1InteriorSummaryGroup.geomEvents, E1InteriorChunkFold.chunkRouteEvents,
    List.map_map, Function.comp]

/-! ## Rung 1 -- THE COMPOSED MIN-CANDIDATE LEG

`legEvents` (`E1InteriorSpanBlock.lean:96`) is BY DEFINITION the four
`geomEvents` the precedent's left-hand side names, in the same order, so
this rung is the precedent consumed under its own name.  It is stated
rather than inlined because the span rung dispatches on it. -/
theorem legEvents_eq_routeReads
    (shape : Cartesian.CartesianShape) (block : Nat) :
    legEvents shape block =
      ((canonicalRelativeRmmMachineMinCandidateComputation shape block).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) :=
  E1InteriorMinCandidate.minCandidateMachineTrace_eq_routeReads shape block

/-! ## Rung 2 -- THE SPAN BLOCK

The head read, then -- ON THE `some` ARM ONLY -- the leg.  The route's
span computation is a `bind` of the same head read against the same
`some`/`none` dispatch, and `bind`'s read log is the concatenation of the
two, so the two `match`es are on the SAME scrutinee once
`cellOpt_spanCell_localSpan` has rewritten the machine's decoded cell into
the route's read value.

**THE `none` ARM IS THE LOAD-BEARING ONE.** The machine branches past all
177 of the leg's instructions and contributes nothing after its own read;
the route's `none` arm is `FlatStoreComputation.pure none`, whose read log
is empty.  The equation therefore says the machine emitted NO event where
the route expects none -- which is what makes a spurious leg on that arm
visible to the receipt. -/
theorem spanEvents_localSpan_eq_routeReads
    (shape : Cartesian.CartesianShape) (macroIdx localStart level : Nat) :
    spanEvents shape (localSpanGeom shape)
        (bpLocalSparseCellSlot (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).levelCount
          macroIdx localStart level)
        (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize) =
      ((canonicalRelativeRmmMachineLocalSpanCandidateComputation shape
            macroIdx localStart level).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  unfold E1InteriorSpanBlock.spanEvents
    canonicalRelativeRmmMachineLocalSpanCandidateComputation
  rw [E1InteriorSpanBlock.cellOpt_spanCell_localSpan,
    E1InteriorSpanBlock.localSpanGeom_base]
  have hhead := geomEvents_eq_readComputation_reads shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (canonicalSummaryLayout shape) (localSpanGeom shape)
    (bpLocalSparseCellSlot (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).levelCount macroIdx localStart level)
    rfl rfl rfl
  rw [E1InteriorSpanBlock.localSpanGeom_base] at hhead
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localOffset
        (bpLocalSparseCellSlot (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).levelCount
          macroIdx localStart level)).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append]
      rw [hhead]
      simp
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append]
      rw [hhead, legEvents_eq_routeReads]

/-- `#3`'s span rung, at slot base `0` and block offset `0`.
`Nat.zero_add` is substantive for the same reason it is on the value
side: `Nat.add` recurses on its second argument. -/
theorem spanEvents_globalSpan_eq_routeReads
    (shape : Cartesian.CartesianShape) (macroStart level : Nat) :
    spanEvents shape (globalSpanGeom shape)
        (bpGlobalSparseCellSlot
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          macroStart level)
        0 =
      ((canonicalRelativeRmmMachineGlobalSpanCandidateComputation shape
            macroStart level).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  unfold E1InteriorSpanBlock.spanEvents
    canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  rw [E1InteriorSpanBlock.cellOpt_spanCell_globalSpan,
    E1InteriorSpanBlock.globalSpanGeom_base]
  have hhead := geomEvents_eq_readComputation_reads shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (canonicalSummaryLayout shape) (globalSpanGeom shape)
    (bpGlobalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart level)
    rfl rfl rfl
  rw [E1InteriorSpanBlock.globalSpanGeom_base] at hhead
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorGlobalTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).globalBlock
        (bpGlobalSparseCellSlot
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          macroStart level)).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append]
      rw [hhead]
      simp
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append, Nat.zero_add]
      rw [hhead, legEvents_eq_routeReads]

/-! ## Rung 3 -- THE TWO-SPAN BLOCK

The level read, then -- ON THE `some` ARM ONLY -- the two span blocks'
receipts in the route's bind order.  The route's merge
(`bpCandidateMerge?`) enters through `FlatStoreComputation.map`, which
contributes NO read event, so the `some` arm's log is exactly the two
spans' logs concatenated and the merge is invisible to the receipt -- as
it must be, since it touches no store. -/
theorem twoSpanEvents_local_eq_routeReads
    (shape : Cartesian.CartesianShape) (macroIdx localStart count : Nat) :
    twoSpanEvents shape (localLevelGeom shape) (localSpanGeom shape)
        (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize))
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        localStart count
        (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize) =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroIdx localStart count).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  unfold E1InteriorTwoSpan.twoSpanEvents
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  rw [E1InteriorTwoSpan.cellOpt_levelCell_localLevel,
    E1InteriorTwoSpan.localLevelGeom_base]
  have hhead := geomEvents_eq_readComputation_reads shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalRelativeRmmInteriorLocalLevelTable shape).table
    (canonicalSummaryLayout shape) (localLevelGeom shape) count rfl rfl rfl
  rw [E1InteriorTwoSpan.localLevelGeom_base] at hhead
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
        count).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append]
      rw [hhead]
      simp
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
        FlatStoreExecution.append, hcell, List.map_append,
        E1InteriorTwoSpan.twoSpanLeftSlot_local,
        E1InteriorTwoSpan.twoSpanRightSlot_local]
      rw [hhead, spanEvents_localSpan_eq_routeReads,
        spanEvents_localSpan_eq_routeReads]
      simp

/-- `#5`'s two-span rung, at slot base `0` and block offset `0`. -/
theorem twoSpanEvents_global_eq_routeReads
    (shape : Cartesian.CartesianShape) (macroStart macroSpanCount : Nat) :
    twoSpanEvents shape (globalLevelGeom shape) (globalSpanGeom shape) 0
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        macroStart macroSpanCount 0 =
      ((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation shape
            macroStart macroSpanCount).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  unfold E1InteriorTwoSpan.twoSpanEvents
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  rw [E1InteriorTwoSpan.cellOpt_levelCell_globalLevel,
    E1InteriorTwoSpan.globalLevelGeom_base]
  have hhead := geomEvents_eq_readComputation_reads shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
    (canonicalSummaryLayout shape) (globalLevelGeom shape) macroSpanCount
    rfl rfl rfl
  rw [E1InteriorTwoSpan.globalLevelGeom_base] at hhead
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
        macroSpanCount).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell,
        List.map_append]
      rw [hhead]
      simp
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
        FlatStoreExecution.append, hcell, List.map_append,
        E1InteriorTwoSpan.twoSpanLeftSlot_global,
        E1InteriorTwoSpan.twoSpanRightSlot_global]
      rw [hhead, spanEvents_globalSpan_eq_routeReads,
        spanEvents_globalSpan_eq_routeReads]
      simp

/-! ## Rung 4 -- THE TWO SUB-LEG SHAPES

`localLegEvents` and `globalLegEvents`
(`E1InteriorDispatchCompose.lean:119`, `:153`) are `twoSpanEvents` at the
two canonical instantiations, spelled exactly as rung 3 spells them, so
these are rung 3 under the names `dispatchEvents` uses. -/
theorem localLegEvents_eq_routeReads
    (shape : Cartesian.CartesianShape) (macroIdx start n : Nat) :
    localLegEvents shape macroIdx start n =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroIdx start n).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) :=
  twoSpanEvents_local_eq_routeReads shape macroIdx start n

theorem globalLegEvents_eq_routeReads
    (shape : Cartesian.CartesianShape) (start n : Nat) :
    globalLegEvents shape start n =
      ((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation shape
            start n).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) :=
  twoSpanEvents_global_eq_routeReads shape start n

/-! ## Rung 5 -- THE THREE COMPOSITE ARMS

`#6`, `#7` and `#8` are binds of two-span legs whose combiners
(`bpCandidateMerge?`, `bpCandidateMerge3?`) enter through
`FlatStoreComputation.map` and contribute no read.  Each arm's log is
therefore its legs' logs concatenated, in the route's own bind order --
which is the order `dispatchEvents` concatenates them in. -/
theorem adjacentArm_reads_eq
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    ((canonicalRelativeRmmMachineAdjacentMacroCandidateComputation shape
          macroStart localStart rightCount).run
        (RMQ.SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape).segment)).reads =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroStart localStart
            ((RelativeRmm.canonicalLayout shape).macroSize - localStart)).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads ++
        ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
              (macroStart + 1) 0 rightCount).run
            (RMQ.SuccinctClose.flatWordStoreOfReadStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape).segment)).reads := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  simp [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]

theorem leftMiddleArm_reads_eq
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    ((canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation shape
          macroStart localStart middleMacroCount).run
        (RMQ.SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape).segment)).reads =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroStart localStart
            ((RelativeRmm.canonicalLayout shape).macroSize - localStart)).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads ++
        ((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation shape
              (macroStart + 1) middleMacroCount).run
            (RMQ.SuccinctClose.flatWordStoreOfReadStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape).segment)).reads := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  simp [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]

theorem crossArm_reads_eq
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    ((canonicalRelativeRmmMachineCrossMacroCandidateComputation shape
          macroStart localStart middleMacroCount rightCount).run
        (RMQ.SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape).segment)).reads =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroStart localStart
            ((RelativeRmm.canonicalLayout shape).macroSize - localStart)).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads ++
        (((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation shape
              (macroStart + 1) middleMacroCount).run
            (RMQ.SuccinctClose.flatWordStoreOfReadStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape).segment)).reads ++
          ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
                (macroStart + 1 + middleMacroCount) 0 rightCount).run
              (RMQ.SuccinctClose.flatWordStoreOfReadStore
                (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                (canonicalSummaryLayout shape).segment)).reads) := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  simp [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]

/-! ## Rung 6 -- `#9`'s RECEIPT, AGAINST THE ROUTE'S OWN READ LOG

**THIS IS THE TOP OF THE LADDER AND THE OBLIGATION BLOCKER 2 NAMES.**

`dispatchEvents` is a five-way `if` in the route's own condition order,
and `canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2444`) is the same five-way `if` on the same
conditions.  The five route lemmas `interiorRangeMin_of_count_zero`
(`E1InteriorDispatch.lean:456`) through `interiorRangeMin_of_cross`
(`:516`) are FULL COMPUTATION equalities, so `.reads` follows from them by
congruence -- no separate trace argument is needed at this rung, which is
why the work was all below it.

**THE `count = 0` ARM IS THE ONE WITH TEETH.** The route is
`FlatStoreComputation.pure none`, whose read log is EMPTY, and the machine's
arm emits nothing.  So the receipt separates the correct layout from an
unterminated one that falls through into `twoSpanBlock`'s unconditional
head level read -- the scope note at `dispatchEvents`' own docstring
records exactly this, and it is now backed by an equation rather than by
the docstring.

Positional and hypothesis-free: both sides are lists, and the only
premises consumed are the five branch conditions, which are exhaustive and
mutually exclusive by construction. -/
theorem dispatchEvents_eq_routeReads
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    dispatchEvents shape startBlock count =
      ((canonicalRelativeRmmInteriorRangeMinComputation shape startBlock
            count).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  unfold E1InteriorDispatchCompose.dispatchEvents
  by_cases hc : count = 0
  · subst hc
    rw [if_pos rfl, E1InteriorDispatch.interiorRangeMin_of_count_zero]
    simp [FlatStoreComputation.pure]
  · rw [if_neg hc]
    by_cases hle : count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · rw [if_pos hle,
        E1InteriorDispatch.interiorRangeMin_of_local shape startBlock count
          hc hle]
      exact localLegEvents_eq_routeReads shape _ _ _
    · rw [if_neg hle]
      by_cases hmid : ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
          (RelativeRmm.canonicalLayout shape).macroSize = 0)
      · rw [if_pos hmid,
          E1InteriorDispatch.interiorRangeMin_of_adjacent shape startBlock
            count hc hle hmid,
          adjacentArm_reads_eq, List.map_append,
          localLegEvents_eq_routeReads, localLegEvents_eq_routeReads]
      · rw [if_neg hmid]
        by_cases hright :
            ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize = 0)
        · rw [if_pos hright,
            E1InteriorDispatch.interiorRangeMin_of_leftMiddle shape startBlock
              count hc hle hmid hright,
            leftMiddleArm_reads_eq, List.map_append,
            localLegEvents_eq_routeReads, globalLegEvents_eq_routeReads]
        · rw [if_neg hright,
            E1InteriorDispatch.interiorRangeMin_of_cross shape startBlock
              count hc hle hmid hright,
            crossArm_reads_eq, List.map_append, List.map_append,
            localLegEvents_eq_routeReads, globalLegEvents_eq_routeReads,
            localLegEvents_eq_routeReads, List.append_assoc]

/-! ## Rung 7 -- THE CROSS-BLOCK ARM'S INTERIOR OBJECT, RECONCILED

**THIS IS THE OBLIGATION THE WHOLE-QUERY SCOPE NOTE LISTS AS STANDING**
(`E1WholeQueryProgram.lean`, obligation 2): `crossBlockArmSpec_eq`
(`E1CrossBlockArm.lean:181`) hands the arm its interior as
`concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore …`,
while `crossBlockArm_withCanonicalInterior_runsTo`
(`E1InteriorDispatchCompose.lean:1291`) produces
`⟨dispatchRouteValue …, dispatchEvents …⟩`.  Those are not the same term
and no theorem identified them.

**THE VALUE HALF AND THE SEGMENT ARE DEFINITIONAL; ONLY THE TRACE HALF
NEEDED THE LADDER -- WHICH IS EXACTLY WHAT THE SCOPE NOTE PREDICTED.**

* `…WithStore` (`ConcreteDirectoryRAMStoreParam.lean:3639`) is DEFINED as
  `flatStoreExecutionTraceResultAtSegment segments.canonicalComponent
  ((canonicalRelativeRmmInteriorRangeMinComputation …).run
  (flatWordStoreOfReadStore store segments.canonicalComponent))`, so its
  `.value` IS the run's `.value`, which is `dispatchRouteValue`'s
  definition (`:381`).
* The two segment spellings coincide BY DEFINITION rather than by
  coincidence: `(canonicalSummaryLayout shape).segment` is
  `E1InteriorStoreConcrete.interiorSegment`
  (`E1InteriorSummaryGroup.lean:469`), which is an `abbrev` for
  `concreteBPNativeInteriorTraceSegments.canonicalComponent`
  (`E1InteriorStoreConcrete.lean:67`) -- the machine side was written
  against the segment record from the start.  **The segment/store
  reconciliation the ladder's brief budgeted for is therefore already
  paid**, and this rung records that finding rather than performing work.
* The `.trace` half is `.reads` mapped through the event injection, and
  identifying THAT with `dispatchEvents` is precisely
  `dispatchEvents_eq_routeReads` -- the rung above, and the only part that
  required proof.

So the interior is no longer a hole: the arm's object and the machine's
object are one term. -/
theorem canonicalInterior_traceResult_eq_dispatch
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape concreteBPNativeInteriorTraceSegments
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) startBlock count =
      ⟨E1InteriorDispatchCompose.dispatchRouteValue shape startBlock count,
        dispatchEvents shape startBlock count⟩ := by
  rw [dispatchEvents_eq_routeReads]
  rfl

end E1InteriorTraceLadder
end WordRAM
end RMQ

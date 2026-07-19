import RMQ.Core.WordRAM.E1InteriorStoreConcrete
import RMQ.Core.WordRAM.E1InteriorChunkValue
import RMQ.Core.WordRAM.E1InteriorChunkCap

/-! # E1 amended machine: the interior's SUMMARY GROUP (M3d-19)

`canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) reads FOUR interior tables -- baseline,
minRel, maxRel, argOffset -- and pairs the results into one tuple.  This
module is the machine block that simulates it.

## Four reads, ONE segment, four OFFSETS

The route's four reads are four calls to
`canonicalRelativeRmmMachineReadNatComputation`
(`InteriorDirectory.lean:2132`), each at a different member of
`canonicalRelativeRmmInteriorComponentOffsets`, all against the SAME
`FlatWordStore` -- `FlatStoreComputation` (`MachineChunkedTableProgram.lean:66`)
runs over a single `address -> word`.  So the block reads one segment,
`E1InteriorStoreConcrete.interiorSegment`, at four bases.

THIS IS WORTH STATING BECAUSE THE NEIGHBOURING READING IS WRONG AND STILL
TYPECHECKS.  `concreteBPNativeInteriorTraceSegments.summary` carries
`minRel := 21` and `maxRel := 22`, but in the CANONICAL store segment `21`
is the fringe chunk table and `22` is the select chunk table
(`Segments.lean:224`, `:228`).  Those per-table segments belong to the
LEGACY compatibility layout (`Segments.lean:101`).  A block wiring the
summary group at them would silently fetch the wrong tables for three of
its four reads with no type error.  Nothing below mentions them.

## Composed on the FOLD, not on the atom

`E1InteriorReadBlock.interiorReadNat` is the single-chunk atom, and its
route bridge carries `0 < width` and `width <= wordSize`
(`interiorReadNat_route_atom`, `E1InteriorReadBlock.lean:443`).  Those do
NOT hold across the interior's reachable shapes: the chunk counts run
`(1,3) (2,3) (4,2) ... (1024,1)`, so the small shapes are genuinely
multi-chunk and the atom would be unsound there.  Every stage below runs
`interiorChunkFold` (`E1InteriorChunkFold.lean:346`), whose eight-capped
simulation covers both regimes uniformly.

## Register bank extension (summary group, `100 .. 104`)

The bank below `100` is fully allocated: `40 .. 62` fringe fold, `63 .. 68`
arm, `69 .. 71` same-block, `72 .. 74` dispatch, `75 .. 84` three-way
merge, `85 .. 88` the interior atom, `89 .. 99` the interior chunk fold.
This block opens at `100`.

That placement is what lets a stage's saved cell survive the NEXT stage's
fold: `ChunkFoldUntouched r := r < 89 \/ 99 < r`
(`E1InteriorChunkFold.lean:928`) holds at every register here.  The input
index register `sBlock` survives all four folds for the same reason, and
`iIdx` (`85`) -- which the folds READ and never write -- is reset from it
before each stage.

See DD-20260719-014.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorSummaryGroup

open E1Machine
open RMQ.SuccinctSpace
open E1InteriorReadBlock (iIdx)
open RMQ.WordRAM.E1InteriorChunkFold

/-! ## Registers -/

/-- The block index to summarise (input). -/
abbrev sBlock : Nat := 100
/-- Saved baseline cell, option-shifted. -/
abbrev sBase : Nat := 101
/-- Saved minRel cell, option-shifted. -/
abbrev sMin : Nat := 102
/-- Saved maxRel cell, option-shifted. -/
abbrev sMax : Nat := 103
/-- Saved argOffset cell, option-shifted. -/
abbrev sArg : Nat := 104

/-! ## One stage -/

/--
ONE STAGED READ: set the index, run the eight-capped fold, save the cell.

The head instruction is a parameter because the four stages set `iIdx`
differently -- the baseline read is at `block / blocksPerSuper`, the other
three at `block` -- while everything after it is identical.
-/
def summaryStage (idxInstr : Instr)
    (segment base deadAddress entriesLen chunkCount wordScale save Q : Nat) :
    List Instr :=
  idxInstr ::
    (interiorChunkFold segment base deadAddress entriesLen chunkCount
      wordScale (Q + 1) ++ [Instr.move save cOut])

@[simp] theorem summaryStage_length (idxInstr : Instr)
    (segment base deadAddress entriesLen chunkCount wordScale save Q : Nat) :
    (summaryStage idxInstr segment base deadAddress entriesLen chunkCount
      wordScale save Q).length = 39 := by
  simp [summaryStage]

/-- What a stage leaves alone: the fold's bank, minus the saved slot. -/
abbrev StageUntouched (save r : Nat) : Prop :=
  ChunkFoldUntouched r ∧ r ≠ save

/-- The stage's category log: the index write, the fold's own log, the save.

`headCat` is a parameter because the four stages do NOT charge alike: the
baseline stage's head is `divConst` (`.arithmetic`), the other three are
`move` (`.registerWrite`).  Fixing it at `registerWrite` would have made
the group's category accounting wrong by one in exactly one slot -- and,
since both are single-element logs of the same length, wrong in a way no
length or read-count check would catch. -/
def summaryStageCats (headCat : Category) (valid allPresent : Bool)
    (iters : Nat) : List Category :=
  headCat :: (interiorChunkFoldCats valid allPresent iters ++
    [Category.registerWrite])

/--
EXACT SIMULATION OF ONE SUMMARY STAGE.

The head instruction's own `RunsTo` is supplied by the caller, so this
covers both the `divConst` head of the baseline stage and the `move` head
of the other three without duplicating the fold reasoning.

The receipt is EXACTLY the fold's route events -- the two register writes
emit nothing -- so a stage contributes the route's trace for its read,
positionally, and the group's receipt is their concatenation.
-/
theorem summaryStage_runsTo
    (store : ReadStore) {program : E1Machine.Program} {idxInstr : Instr}
    {segment base deadAddress entriesLen chunkCount wordScale save Q i : Nat}
    {headCat : Category} {regs regsH : RegFile}
    (hHost : HostedAt program Q
      (summaryStage idxInstr segment base deadAddress entriesLen chunkCount
        wordScale save Q))
    (hHead : RunsTo store program ⟨regs, Q, false⟩ ⟨regsH, Q + 1, false⟩
      [] [headCat])
    (hIdx : regsH iIdx = i)
    (hccPos : 0 < chunkCount) (hccCap : chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 39, false⟩
          (chunkRouteEvents store segment base deadAddress entriesLen
            chunkCount i)
          (summaryStageCats headCat (decide (i < entriesLen))
            (decide (chunkBad store segment
              (chunkStart base deadAddress entriesLen chunkCount i)
              (chunkIters entriesLen chunkCount i) = 0))
            (chunkIters entriesLen chunkCount i)) ∧
        regs' save =
          (if chunkBad store segment
                (chunkStart base deadAddress entriesLen chunkCount i)
                (chunkIters entriesLen chunkCount i) = 0 then
            (chunkRevAt wordScale
              (chunkAcc store segment wordScale
                (chunkStart base deadAddress entriesLen chunkCount i)
                (chunkIters entriesLen chunkCount i))
              (chunkIters entriesLen chunkCount i)).2 + 1
          else 0) ∧
        (∀ r, StageUntouched save r → regs' r = regsH r) := by
  -- hosting: head, then the fold, then the save
  have hRest : HostedAt program (Q + 1)
      (interiorChunkFold segment base deadAddress entriesLen chunkCount
        wordScale (Q + 1) ++ [Instr.move save cOut]) := by
    have h := hHost.tail
    simpa [summaryStage] using h
  have hFold : HostedAt program (Q + 1)
      (interiorChunkFold segment base deadAddress entriesLen chunkCount
        wordScale (Q + 1)) := hRest.append_left
  have hSave : HostedAt program (Q + 1 + 37) [Instr.move save cOut] := by
    have h := hRest.append_right
    simpa using h
  obtain ⟨rF, hFoldRun, hFoldOut, hFoldPres⟩ :=
    interiorChunkFold_runsTo store hFold hccPos hccCap regsH i hIdx
  -- the saving move
  have hMove : RunsTo store program ⟨rF, Q + 1 + 37, false⟩
      ⟨rF.write save (rF cOut), Q + 1 + 37 + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.move (by simp) (by simpa using hSave.head)
  refine ⟨rF.write save (rF cOut), ?_, ?_, ?_⟩
  · have hrun := (hHead.trans hFoldRun).trans hMove
    have harith : Q + 1 + 37 + 1 = Q + 39 := by omega
    rw [harith] at hrun
    simpa [summaryStageCats] using hrun
  · rw [RegFile.write_same, hFoldOut]
  · intro r hr
    rw [RegFile.write_other _ _ hr.2, hFoldPres r hr.1]

/-! ## The group -/

/-- One table's read geometry: where its region starts, how many cells it
holds, and how many machine chunks one cell occupies. -/
structure TableGeom where
  base : Nat
  entriesLen : Nat
  chunkCount : Nat

/-- The summary group's layout.  `segment`, `deadAddress` and `wordScale`
are SHARED by all four reads -- one flat store, one dead address, one word
size -- and only the per-table geometry varies.  That is the structural
reason the four-offsets reading is the right one and the four-segments
reading is not. -/
structure SummaryLayout where
  segment : Nat
  deadAddress : Nat
  wordScale : Nat
  blocksPerSuper : Nat
  baseline : TableGeom
  minRel : TableGeom
  maxRel : TableGeom
  argOffset : TableGeom

/-- The decoded cell a stage leaves in its save register, option-shifted
(`0` = `none`, `v + 1` = `some v`), in the fold's own machine terms. -/
def stageCell (store : ReadStore)
    (segment base deadAddress entriesLen chunkCount wordScale i : Nat) :
    Nat :=
  if chunkBad store segment
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i) = 0 then
    (chunkRevAt wordScale
      (chunkAcc store segment wordScale
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i))
      (chunkIters entriesLen chunkCount i)).2 + 1
  else 0

/-- A stage's read geometry, applied to a `TableGeom`. -/
def geomEvents (store : ReadStore) (L : SummaryLayout) (G : TableGeom)
    (i : Nat) : List TraceEvent :=
  chunkRouteEvents store L.segment G.base L.deadAddress G.entriesLen
    G.chunkCount i

/-- A stage's saved cell, applied to a `TableGeom`. -/
def geomCell (store : ReadStore) (L : SummaryLayout) (G : TableGeom)
    (i : Nat) : Nat :=
  stageCell store L.segment G.base L.deadAddress G.entriesLen G.chunkCount
    L.wordScale i

/-- A stage's category log, applied to a `TableGeom`. -/
def geomCats (store : ReadStore) (L : SummaryLayout) (G : TableGeom)
    (headCat : Category) (i : Nat) : List Category :=
  summaryStageCats headCat (decide (i < G.entriesLen))
    (decide (chunkBad store L.segment
      (chunkStart G.base L.deadAddress G.entriesLen G.chunkCount i)
      (chunkIters G.entriesLen G.chunkCount i) = 0))
    (chunkIters G.entriesLen G.chunkCount i)

/--
THE SUMMARY GROUP: four staged reads, in the route's own bind order.

`iIdx` is RESET before each stage rather than relied on across stages.
The baseline read is at `block / blocksPerSuper` and the other three at
`block`, so after stage 1 the index register must be restored; resetting
uniformly before stages 2, 3 and 4 keeps every stage's index premise local
and costs three instructions.

THE `maxRel` STAGE IS NOT OPTIMISABLE AWAY, FOR TWO INDEPENDENT REASONS.

First, the POSITIONAL RECEIPT: the trace below is the concatenation of
four route event lists, and dropping the third would break the receipt
equality.

Second -- and this is the reason a receipt-only reading MISSES -- the
value is load-bearing through the OPTION STRUCTURE.  `maxRel` is bound
into the summary tuple by a four-way match whose sole `some` arm needs
all four components present (`InteriorDirectory.lean:2293-2296`), so
`maxRel = none` forces the whole summary, and hence the min-candidate, to
`none`.  It is true that `bpRelativeSummaryMinCandidate` (`:2300`) never
READS `summary.2.2.1`; it does not follow that the cell may be ignored.
A block that kept this read but discarded its value would return `some`
exactly where the route returns `none` -- with an identical trace, read
count and exit code.

The consumer that depends on this is
`E1InteriorMinCandidate.minCandidateBlock`, whose `maxRel` presence test
is justified at DD-20260719-015.
-/
def summaryGroup (L : SummaryLayout) (Q : Nat) : List Instr :=
  summaryStage (Instr.divConst iIdx sBlock L.blocksPerSuper) L.segment
      L.baseline.base L.deadAddress L.baseline.entriesLen
      L.baseline.chunkCount L.wordScale sBase Q
    ++ summaryStage (Instr.move iIdx sBlock) L.segment L.minRel.base
      L.deadAddress L.minRel.entriesLen L.minRel.chunkCount L.wordScale
      sMin (Q + 39)
    ++ summaryStage (Instr.move iIdx sBlock) L.segment L.maxRel.base
      L.deadAddress L.maxRel.entriesLen L.maxRel.chunkCount L.wordScale
      sMax (Q + 78)
    ++ summaryStage (Instr.move iIdx sBlock) L.segment L.argOffset.base
      L.deadAddress L.argOffset.entriesLen L.argOffset.chunkCount
      L.wordScale sArg (Q + 117)

@[simp] theorem summaryGroup_length (L : SummaryLayout) (Q : Nat) :
    (summaryGroup L Q).length = 156 := by
  simp [summaryGroup]

/-- What the whole group leaves alone: the fold's bank, minus the index
register the stages reset and the four saved slots. -/
abbrev GroupUntouched (r : Nat) : Prop :=
  ChunkFoldUntouched r ∧ r ≠ iIdx ∧ r ≠ sBase ∧ r ≠ sMin ∧ r ≠ sMax ∧
    r ≠ sArg

/--
EXACT SIMULATION OF THE SUMMARY GROUP.

The receipt is the concatenation of the four route event lists in the
route's bind order -- baseline, minRel, maxRel, argOffset -- and the four
decoded cells land in `sBase`, `sMin`, `sMax`, `sArg`.

Every premise is a CHUNK-COUNT fact about one of the four tables.  None is
a store hypothesis: `interiorChunkFold_runsTo` holds at every store, and
the store's contribution enters later, through the value bridge.
-/
theorem summaryGroup_runsTo
    (store : ReadStore) {program : E1Machine.Program} {L : SummaryLayout}
    {Q block : Nat} {regs : RegFile}
    (hHost : HostedAt program Q (summaryGroup L Q))
    (hBlock : regs sBlock = block)
    (hPosB : 0 < L.baseline.chunkCount) (hCapB : L.baseline.chunkCount ≤ 8)
    (hPosMn : 0 < L.minRel.chunkCount) (hCapMn : L.minRel.chunkCount ≤ 8)
    (hPosMx : 0 < L.maxRel.chunkCount) (hCapMx : L.maxRel.chunkCount ≤ 8)
    (hPosA : 0 < L.argOffset.chunkCount)
    (hCapA : L.argOffset.chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 156, false⟩
          (geomEvents store L L.baseline (block / L.blocksPerSuper) ++
            geomEvents store L L.minRel block ++
            geomEvents store L L.maxRel block ++
            geomEvents store L L.argOffset block)
          (geomCats store L L.baseline Category.arithmetic
              (block / L.blocksPerSuper) ++
            geomCats store L L.minRel Category.registerWrite block ++
            geomCats store L L.maxRel Category.registerWrite block ++
            geomCats store L L.argOffset Category.registerWrite block) ∧
        regs' sBase =
          geomCell store L L.baseline (block / L.blocksPerSuper) ∧
        regs' sMin = geomCell store L L.minRel block ∧
        regs' sMax = geomCell store L L.maxRel block ∧
        regs' sArg = geomCell store L L.argOffset block ∧
        (∀ r, GroupUntouched r → regs' r = regs r) := by
  -- hosting: four consecutive stages
  have h1 : HostedAt program Q
      (summaryStage (Instr.divConst iIdx sBlock L.blocksPerSuper) L.segment
        L.baseline.base L.deadAddress L.baseline.entriesLen
        L.baseline.chunkCount L.wordScale sBase Q) :=
    hHost.append_left.append_left.append_left
  have h2 : HostedAt program (Q + 39)
      (summaryStage (Instr.move iIdx sBlock) L.segment L.minRel.base
        L.deadAddress L.minRel.entriesLen L.minRel.chunkCount L.wordScale
        sMin (Q + 39)) := by
    have h := hHost.append_left.append_left.append_right
    simpa using h
  have h3 : HostedAt program (Q + 78)
      (summaryStage (Instr.move iIdx sBlock) L.segment L.maxRel.base
        L.deadAddress L.maxRel.entriesLen L.maxRel.chunkCount L.wordScale
        sMax (Q + 78)) := by
    have h := hHost.append_left.append_right
    simpa using h
  have h4 : HostedAt program (Q + 117)
      (summaryStage (Instr.move iIdx sBlock) L.segment L.argOffset.base
        L.deadAddress L.argOffset.entriesLen L.argOffset.chunkCount
        L.wordScale sArg (Q + 117)) := by
    have h := hHost.append_right
    simpa using h
  -- stage 1: the baseline read, at `block / blocksPerSuper`
  have hHead1 : RunsTo store program ⟨regs, Q, false⟩
      ⟨regs.write iIdx (regs sBlock / L.blocksPerSuper), Q + 1, false⟩ []
      [Category.arithmetic] :=
    RunsTo.divConst (by simp) (by simpa [summaryStage] using h1.head)
  obtain ⟨r1, hRun1, hOut1, hPres1⟩ :=
    summaryStage_runsTo store h1 hHead1
      (i := block / L.blocksPerSuper) (by rw [RegFile.write_same, hBlock])
      hPosB hCapB
  -- `sBlock` survives stage 1: it is outside the fold's bank and is not
  -- the saved slot.
  have hB1 : r1 sBlock = block := by
    rw [hPres1 sBlock ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hBlock]
  -- stage 2: minRel, at `block`
  have hHead2 : RunsTo store program ⟨r1, Q + 39, false⟩
      ⟨r1.write iIdx (r1 sBlock), Q + 39 + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.move (by simp) (by simpa [summaryStage] using h2.head)
  obtain ⟨r2, hRun2, hOut2, hPres2⟩ :=
    summaryStage_runsTo store h2 hHead2 (i := block)
      (by rw [RegFile.write_same, hB1]) hPosMn hCapMn
  have hB2 : r2 sBlock = block := by
    rw [hPres2 sBlock ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hB1]
  -- stage 3: maxRel, at `block` -- KEPT for the positional receipt
  have hHead3 : RunsTo store program ⟨r2, Q + 78, false⟩
      ⟨r2.write iIdx (r2 sBlock), Q + 78 + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.move (by simp) (by simpa [summaryStage] using h3.head)
  obtain ⟨r3, hRun3, hOut3, hPres3⟩ :=
    summaryStage_runsTo store h3 hHead3 (i := block)
      (by rw [RegFile.write_same, hB2]) hPosMx hCapMx
  have hB3 : r3 sBlock = block := by
    rw [hPres3 sBlock ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hB2]
  -- stage 4: argOffset, at `block`
  have hHead4 : RunsTo store program ⟨r3, Q + 117, false⟩
      ⟨r3.write iIdx (r3 sBlock), Q + 117 + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.move (by simp) (by simpa [summaryStage] using h4.head)
  obtain ⟨r4, hRun4, hOut4, hPres4⟩ :=
    summaryStage_runsTo store h4 hHead4 (i := block)
      (by rw [RegFile.write_same, hB3]) hPosA hCapA
  refine ⟨r4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrun := ((hRun1.trans hRun2).trans hRun3).trans hRun4
    have harith : Q + 39 + 39 + 39 + 39 = Q + 156 := by omega
    simpa [geomEvents, geomCats, List.append_assoc, harith] using hrun
  · -- `sBase` survives stages 2, 3 and 4
    rw [hPres4 sBase ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide),
      hPres3 sBase ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide),
      hPres2 sBase ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hOut1]
    rfl
  · rw [hPres4 sMin ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide),
      hPres3 sMin ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hOut2]
    rfl
  · rw [hPres4 sMax ⟨by decide, by decide⟩,
      RegFile.write_other _ _ (by decide), hOut3]
    rfl
  · rw [hOut4]; rfl
  · intro r hr
    obtain ⟨hFold, hIdxNe, hBaseNe, hMinNe, hMaxNe, hArgNe⟩ := hr
    rw [hPres4 r ⟨hFold, hArgNe⟩, RegFile.write_other _ _ hIdxNe,
      hPres3 r ⟨hFold, hMaxNe⟩, RegFile.write_other _ _ hIdxNe,
      hPres2 r ⟨hFold, hMinNe⟩, RegFile.write_other _ _ hIdxNe,
      hPres1 r ⟨hFold, hBaseNe⟩, RegFile.write_other _ _ hIdxNe]

/-! ## The canonical instantiation

The eight chunk-count premises above are stated generally.  This section
DISCHARGES them at the store the composition actually runs against, so
that no consumer of the group inherits them.

Every discharge below cites `E1InteriorChunkCap`, whose lemmas are
unconditional in `shape` and predate this module.  None cites
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`: that is a COST
bound, hence an upper bound only, and supplies neither half -- not the cap
at the within-macro widths, and in particular not `0 < chunkCount`.
-/

/-- The summary group's layout at the canonical interior store.

`chunkCount` is DEFINED here as the route's own
`fixedWidthNatTableMachineChunkCount` at the table's width, and
`entriesLen` as the route's own entry-list length.  Both choices are what
make the `hexact_*_concrete` premises discharge below rather than travel:
`hcount` becomes `rfl`, and `hvalid`/`hentries` become the SAME
proposition. -/
def canonicalSummaryLayout (shape : Cartesian.CartesianShape) :
    SummaryLayout :=
  let layout := RelativeRmm.canonicalLayout shape
  let offsets := canonicalRelativeRmmInteriorComponentOffsets shape
  let wordBits := SuccinctRank.machineWordBits shape.bpCode.length
  { segment := E1InteriorStoreConcrete.interiorSegment
  , deadAddress := offsets.deadAddress
  , wordScale := 2 ^ wordBits
  , blocksPerSuper := layout.blocksPerSuper
  , baseline :=
      { base := offsets.baseline
      , entriesLen :=
          (bpSuperblockBaselineEntries shape layout.blockSize
            layout.blocksPerSuper layout.superSampleCount).length
      , chunkCount :=
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            (layout.superWidth shape) wordBits }
  , minRel :=
      { base := offsets.minRel
      , entriesLen :=
          (bpBlockRelativeMinExcessEntries shape layout.blockSize
            layout.blocksPerSuper layout.blockCount).length
      , chunkCount :=
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            layout.relativeWidth wordBits }
  , maxRel :=
      { base := offsets.maxRel
      , entriesLen :=
          (bpBlockRelativeMaxExcessEntries shape layout.blockSize
            layout.blocksPerSuper layout.blockCount).length
      , chunkCount :=
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            layout.relativeWidth wordBits }
  , argOffset :=
      { base := offsets.argOffset
      , entriesLen :=
          (bpBlockArgMinLocalOffsetEntries shape layout.blockSize
            layout.blockCount).length
      , chunkCount :=
          SuccinctSpace.fixedWidthNatTableMachineChunkCount
            layout.relativeWidth wordBits } }

theorem canonicalSummaryLayout_baseline_pos
    (shape : Cartesian.CartesianShape) :
    0 < (canonicalSummaryLayout shape).baseline.chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_superWidth shape

theorem canonicalSummaryLayout_baseline_cap
    (shape : Cartesian.CartesianShape) :
    (canonicalSummaryLayout shape).baseline.chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_superWidth shape

theorem canonicalSummaryLayout_minRel_pos
    (shape : Cartesian.CartesianShape) :
    0 < (canonicalSummaryLayout shape).minRel.chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_relativeWidth shape

theorem canonicalSummaryLayout_minRel_cap
    (shape : Cartesian.CartesianShape) :
    (canonicalSummaryLayout shape).minRel.chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_relativeWidth shape

theorem canonicalSummaryLayout_maxRel_pos
    (shape : Cartesian.CartesianShape) :
    0 < (canonicalSummaryLayout shape).maxRel.chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_relativeWidth shape

theorem canonicalSummaryLayout_maxRel_cap
    (shape : Cartesian.CartesianShape) :
    (canonicalSummaryLayout shape).maxRel.chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_relativeWidth shape

theorem canonicalSummaryLayout_argOffset_pos
    (shape : Cartesian.CartesianShape) :
    0 < (canonicalSummaryLayout shape).argOffset.chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_relativeWidth shape

theorem canonicalSummaryLayout_argOffset_cap
    (shape : Cartesian.CartesianShape) :
    (canonicalSummaryLayout shape).argOffset.chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_relativeWidth shape

/--
THE SUMMARY GROUP AT THE STORE THE COMPOSITION NAMES.

All eight chunk-count premises are supplied, not assumed.  The store is
`concreteBPNativeSuccinctRMQGlobalReadStore shape` -- the one
`crossBlockArmProgramAt_runsTo`'s `hInterior` premise fixes
(`E1CrossBlockArm.lean:1143`) -- and the segment is the one the interior
route's reads are emitted at.
-/
theorem canonicalSummaryGroup_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {Q block : Nat} {regs : RegFile}
    (hHost : HostedAt program Q (summaryGroup (canonicalSummaryLayout shape) Q))
    (hBlock : regs sBlock = block) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 156, false⟩
          (geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).baseline
              (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).minRel block ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).maxRel block ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).argOffset block)
          (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).baseline Category.arithmetic
              (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).minRel
              Category.registerWrite block ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).maxRel
              Category.registerWrite block ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).argOffset
              Category.registerWrite block) ∧
        regs' sBase =
          geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape)
            (canonicalSummaryLayout shape).baseline
            (block / (canonicalSummaryLayout shape).blocksPerSuper) ∧
        regs' sMin =
          geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape)
            (canonicalSummaryLayout shape).minRel block ∧
        regs' sMax =
          geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape)
            (canonicalSummaryLayout shape).maxRel block ∧
        regs' sArg =
          geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape)
            (canonicalSummaryLayout shape).argOffset block ∧
        (∀ r, GroupUntouched r → regs' r = regs r) :=
  summaryGroup_runsTo _ hHost hBlock
    (canonicalSummaryLayout_baseline_pos shape)
    (canonicalSummaryLayout_baseline_cap shape)
    (canonicalSummaryLayout_minRel_pos shape)
    (canonicalSummaryLayout_minRel_cap shape)
    (canonicalSummaryLayout_maxRel_pos shape)
    (canonicalSummaryLayout_maxRel_cap shape)
    (canonicalSummaryLayout_argOffset_pos shape)
    (canonicalSummaryLayout_argOffset_cap shape)

/-! ## The width bound at the concrete store

`hle` is the value bridge's OTHER premise.  It is not a chunk-count fact
and does not come from the cap module: it is the interior component
store's own `word_length_le` field, transported to the global store by the
segment-20 projection.  Verbatim from
`canonicalRelativeRmmInteriorComponentStore_words_bounded`
(`InteriorDirectory.lean:1711`), as the resume direction requires. -/

theorem hle_concrete (shape : Cartesian.CartesianShape) {a : Nat}
    {w : List Bool}
    (h : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      E1InteriorStoreConcrete.interiorSegment a = some w) :
    w.length ≤ SuccinctRank.machineWordBits shape.bpCode.length := by
  rw [E1InteriorStoreConcrete.holdsInteriorStore_concrete shape a] at h
  exact canonicalRelativeRmmInteriorComponentStore_words_bounded shape
    (List.mem_of_getElem? h)

/-! ## The value bridge, and the premises it settles

`summaryGroup_runsTo` states each saved cell in the fold's own machine
terms (`geomCell`).  This section rewrites all four into the ROUTE's
decode, which is what a consumer needs.

THE PREMISES `hexact_*_concrete` STILL CARRIED ARE DISCHARGED HERE, NOT
PASSED ON.  M3d-18 delivered them retaining `hcount`, `hvalid` and
`hentries`, and recorded -- correctly -- that "not a debt owed to the
store" is not the same as "not a debt".  At the canonical layout they
settle as follows, and the settlement is a consequence of how
`canonicalSummaryLayout` is DEFINED rather than an extra assumption:

* `hcount` is `rfl`.  The layout's `chunkCount` field IS the route's
  `fixedWidthNatTableMachineChunkCount` at that table's width.
* `hentries` and `hvalid` are THE SAME PROPOSITION.  The layout's
  `entriesLen` field IS the route's entry-list length, so the two premises
  coincide and one caller-side index fact supplies both.

What remains is a single `i < entriesLen` obligation per read -- the
route's own validity condition, which the interior's branch structure
supplies at the call site.  Nothing about the store survives.
-/

/-- The route's decode of a table cell, option-shifted the same way the
machine's `cOut` is. -/
def geomRouteDecode (store : ReadStore) (L : SummaryLayout) (G : TableGeom)
    (i : Nat) : Nat :=
  match SuccinctSpace.fixedWidthNatTableMachineDecode
      ((chunkAddrs G.base L.deadAddress G.entriesLen G.chunkCount i).map
        (fun a => store.readWord? L.segment a)) with
  | none => 0
  | some v => v + 1

/-- The bridge, generically: a stage's saved cell IS the route's decode,
given the cap, the width bound, and non-final-chunk exactness. -/
theorem geomCell_eq_routeDecode (shape : Cartesian.CartesianShape)
    (G : TableGeom) (i : Nat)
    (hcap : G.chunkCount ≤ 8)
    (hexact : ∀ j, j + 1 <
      chunkIters G.entriesLen G.chunkCount i → ∀ w,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          E1InteriorStoreConcrete.interiorSegment
          (chunkStart G.base
            (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress
            G.entriesLen G.chunkCount i + j) = some w →
        w.length = SuccinctRank.machineWordBits shape.bpCode.length) :
    geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G i =
      geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G i :=
  E1InteriorChunkValue.interiorChunkFold_cOut_eq_routeDecode
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) hcap
    (fun _ _ _ h => hle_concrete shape h) hexact

/-- Baseline: the summary group's first read, at `block / blocksPerSuper`. -/
theorem geomCell_baseline_eq_routeDecode (shape : Cartesian.CartesianShape)
    {i : Nat}
    (hvalid : i < (canonicalSummaryLayout shape).baseline.entriesLen) :
    geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).baseline i =
      geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).baseline i :=
  geomCell_eq_routeDecode shape _ i
    (canonicalSummaryLayout_baseline_cap shape)
    (E1InteriorStoreConcrete.hexact_baseline_concrete rfl hvalid hvalid)

/-- minRel: the second read. -/
theorem geomCell_minRel_eq_routeDecode (shape : Cartesian.CartesianShape)
    {i : Nat}
    (hvalid : i < (canonicalSummaryLayout shape).minRel.entriesLen) :
    geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).minRel i =
      geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).minRel i :=
  geomCell_eq_routeDecode shape _ i
    (canonicalSummaryLayout_minRel_cap shape)
    (E1InteriorStoreConcrete.hexact_minRel_concrete rfl hvalid hvalid)

/-- maxRel: the third read.  Its value is never READ by
`bpRelativeSummaryMinCandidate`, but the bridge is load-bearing rather
than merely defensive: the route's summary is `none` whenever this cell
is `none` (`InteriorDirectory.lean:2293-2296`), so the consumer's
`none`/`some` split is decided in part HERE.  See DD-20260719-015. -/
theorem geomCell_maxRel_eq_routeDecode (shape : Cartesian.CartesianShape)
    {i : Nat}
    (hvalid : i < (canonicalSummaryLayout shape).maxRel.entriesLen) :
    geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).maxRel i =
      geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).maxRel i :=
  geomCell_eq_routeDecode shape _ i
    (canonicalSummaryLayout_maxRel_cap shape)
    (E1InteriorStoreConcrete.hexact_maxRel_concrete rfl hvalid hvalid)

/-- argOffset: the fourth read. -/
theorem geomCell_argOffset_eq_routeDecode
    (shape : Cartesian.CartesianShape) {i : Nat}
    (hvalid : i < (canonicalSummaryLayout shape).argOffset.entriesLen) :
    geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).argOffset i =
      geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape)
        (canonicalSummaryLayout shape).argOffset i :=
  geomCell_eq_routeDecode shape _ i
    (canonicalSummaryLayout_argOffset_cap shape)
    (E1InteriorStoreConcrete.hexact_argOffset_concrete rfl hvalid hvalid)

end E1InteriorSummaryGroup
end WordRAM
end RMQ

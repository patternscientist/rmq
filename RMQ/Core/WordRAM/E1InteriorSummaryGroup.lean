import RMQ.Core.WordRAM.E1InteriorStoreConcrete
import RMQ.Core.WordRAM.E1InteriorChunkValue

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

THE `maxRel` STAGE IS NOT OPTIMISABLE AWAY.  Its value IS bound into the
summary tuple (`InteriorDirectory.lean:2295`) and then discarded by
`bpRelativeSummaryMinCandidate` (`:2300`), so a value-only reading would
license dropping the read.  It is kept because the block owes the route's
POSITIONAL RECEIPT: the trace below is the concatenation of four route
event lists, and dropping the third would break the receipt equality even
though no consumer inspects the value.
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

end E1InteriorSummaryGroup
end WordRAM
end RMQ

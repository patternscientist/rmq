import RMQ.Core.WordRAM.E1InteriorMinCandidate

/-! # E1 amended machine: the interior's SPAN BLOCKS (#2 and #3)

`canonicalRelativeRmmMachineLocalSpanCandidateComputation`
(`InteriorDirectory.lean:2311`) and its global twin
`canonicalRelativeRmmMachineGlobalSpanCandidateComputation` (`:2329`) have
ONE shape between them:

    FlatStoreComputation.bind (readNat TABLE OFFSET SLOT) fun cell =>
      match cell with
      | some value => MinCandidateComputation shape (BLOCK value)
      | none       => FlatStoreComputation.pure none

They differ in exactly three places: the table, the read offset, and the
map from the decoded cell to the block index -- `macroIdx * macroSize +
value` for the local twin, `value` for the global one.  Both maps are
`off + value` for a caller-supplied `off`, so ONE parametric block covers
both and the two route computations are its instantiations.

## The `none` arm is the load-bearing part

The `some` arm falls into the composed 177-instruction min-candidate leg
(`summaryMinCandidate_runsTo`, `E1InteriorMinCandidate.lean:929`).  The
`none` arm must branch past ALL 177 of them AND emit nothing.

Branching past only the summary group's 156 -- and so falling into the
21-instruction consumer -- is not a hypothetical error.  It is the exact
RIGHT SHAPE, WRONG CONTENT defect this development has hit three times,
and it is invisible to every check that is not a value check: the
consumer is READ-FREE (`minCandidateBlock_readFree`,
`E1InteriorMinCandidate.lean:246`), so the impostor's receipt is the
correct one, POSITIONALLY, and its read count is equal.  It returns
`some` from whatever four cells happen to be sitting in `sBase`, `sMin`,
`sMax`, `sArg` where the route returns `none`.

`spanNoneArm_discriminates` below is the fixture that separates them, and
`spanNoneArm_traces_agree` is the matching NON-ENTAILMENT: it proves the
receipts are equal, hence that no receipt-level check can reject the
impostor.  DD-20260719-050.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorSpanBlock

open E1Machine
open RMQ.SuccinctClose
open E1FringeFoldBlock (bestOfRegs)
open E1CandMerge3 (mMV mMP)
open E1InteriorReadBlock (iIdx)
open E1InteriorSummaryGroup (sBlock sBase sMin sMax sArg TableGeom
  SummaryLayout canonicalSummaryLayout summaryGroup summaryGroup_length
  summaryStage summaryStage_length summaryStageCats summaryStage_runsTo
  geomEvents geomCats geomCell StageUntouched)
open E1InteriorMinCandidate (minCandidateBlock minCandidateBlock_length
  minCandidateCats routeDecodedSummary cellOpt summaryMinCandidate_runsTo)

/-! ## Registers

The interior's first new bank.  `75..84` (merge), `89..99` (chunk fold)
and `105..117` (summary + min-candidate) are taken; this block opens at
`118`.  `pSlot` and `pOff` are INPUTS, supplied by the caller; the rest
are scratch. -/

/-- Input: the slot index the span read addresses. -/
abbrev pSlot : Nat := 118

/-- Input: the additive block offset.  `macroIdx * macroSize` for the
local twin, `0` for the global one. -/
abbrev pOff : Nat := 119

/-- The decoded span cell, option-shifted (`0` = `none`, `v + 1` = `some v`). -/
abbrev pCell : Nat := 120

/-- Scratch: the unshifted cell value. -/
abbrev pT : Nat := 121

/-- Constant `1`: the unshift operand, and the condition register that
makes the `none` arm's jump unconditional. -/
abbrev pOne : Nat := 122

/-! ## The composed min-candidate leg, named

`summaryMinCandidate_runsTo` states its receipt, charge log and value
inline.  Naming them here keeps the span block's own statements readable
and, more importantly, keeps the `none` arm's obligation -- that it
produces NEITHER of them -- expressible. -/

/-- The 177-instruction leg's receipt at block index `block`. -/
def legEvents (shape : Cartesian.CartesianShape) (block : Nat) :
    List TraceEvent :=
  geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).baseline
      (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
    geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).minRel
      block ++
    geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).maxRel
      block ++
    geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).argOffset
      block

/-- The 177-instruction leg's charge log at block index `block`. -/
def legCats (shape : Cartesian.CartesianShape) (block : Nat) :
    List Category :=
  (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).baseline
      Category.arithmetic
      (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
    geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).minRel
      Category.registerWrite block ++
    geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).maxRel
      Category.registerWrite block ++
    geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).argOffset
      Category.registerWrite block) ++
    minCandidateCats (routeDecodedSummary shape block).isSome

/-- The 177-instruction leg's value at block index `block`. -/
def legValue (shape : Cartesian.CartesianShape) (block : Nat) :
    Option (Nat × Nat) :=
  (routeDecodedSummary shape block).map
    (bpRelativeSummaryMinCandidate
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper block)

/-! ## The block -/

/-- The arm selector, at `Q + 40 .. Q + 44`.

`Q + 42`'s target is `Q + 222`, the block's own exit -- past the leg's
177 instructions, not past the group's 156.  That single numeral is the
whole content of the `none` arm's correctness. -/
def spanArms (Q : Nat) : List Instr :=
  [ Instr.brNZ pCell (Q + 43)   -- Q+40  cell present? -> unshift
  , Instr.const mMV 0           -- Q+41  none arm: the result IS none
  , Instr.brNZ pOne (Q + 222)   -- Q+42  none arm: past ALL 177
  , Instr.sub pT pCell pOne     -- Q+43  value := cell - 1
  , Instr.add sBlock pOff pT ]  -- Q+44  block := off + value

@[simp] theorem spanArms_length (Q : Nat) : (spanArms Q).length = 5 := rfl

/-- THE SPAN BLOCK, parametric in the read geometry `G` (222
instructions, exit `Q + 222` on BOTH arms).

One staged read at `G`, then the arm selector, then the composed
min-candidate leg.  `#2` and `#3` are this block at two `TableGeom`s. -/
def spanBlock (L : SummaryLayout) (G : TableGeom)
    (blockSize blocksPerSuper Q : Nat) : List Instr :=
  (Instr.const pOne 1 ::
      summaryStage (Instr.move iIdx pSlot) L.segment G.base L.deadAddress
        G.entriesLen G.chunkCount L.wordScale pCell (Q + 1)) ++
    (spanArms Q ++
      (summaryGroup L (Q + 45) ++
        minCandidateBlock blockSize blocksPerSuper (Q + 45 + 156)))

@[simp] theorem spanBlock_length (L : SummaryLayout) (G : TableGeom)
    (blockSize blocksPerSuper Q : Nat) :
    (spanBlock L G blockSize blocksPerSuper Q).length = 222 := by
  simp [spanBlock]

/-! ## Receipt, charge log and value, as functions of the decoded cell

Each is a `cellOpt` dispatch on the span cell.  `cellOpt` is NAMED rather
than an inline `match`: an inline `match` in a statement elaborates a
fresh auxiliary per declaration, so the inversion lemmas below would be
defeq to their goals and still not fire. -/

/-- The span cell this block decodes at slot `slot`, option-shifted. -/
def spanCell (shape : Cartesian.CartesianShape) (G : TableGeom)
    (slot : Nat) : Nat :=
  geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalSummaryLayout shape) G slot

/-- The block's receipt: the span read, then the leg's reads ONLY on the
`some` arm. -/
def spanEvents (shape : Cartesian.CartesianShape) (G : TableGeom)
    (slot off : Nat) : List TraceEvent :=
  geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) G slot ++
    (match cellOpt (spanCell shape G slot) with
      | none => []
      | some v => legEvents shape (off + v))

/-- The block's charge log.  The two arms differ in LENGTH as well as in
content, so this is not a numeral. -/
def spanCats (shape : Cartesian.CartesianShape) (G : TableGeom)
    (slot off : Nat) : List Category :=
  Category.registerWrite ::
    (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G Category.registerWrite slot ++
      (match cellOpt (spanCell shape G slot) with
        | none => [Category.branch, Category.registerWrite, Category.branch]
        | some v =>
            [Category.branch, Category.arithmetic, Category.arithmetic] ++
              legCats shape (off + v)))

/-- The block's value: the leg's value at `off + v` on the `some` arm,
and `none` on the `none` arm. -/
def spanValue (shape : Cartesian.CartesianShape) (G : TableGeom)
    (slot off : Nat) : Option (Nat × Nat) :=
  match cellOpt (spanCell shape G slot) with
  | none => none
  | some v => legValue shape (off + v)

/-- What the span block leaves alone: everything below `75` and above
`122`, minus the banks the leg writes. -/
abbrev SpanUntouched (r : Nat) : Prop :=
  (r < 75 ∨ 122 < r) ∧ r ≠ sBlock

/-! ## Exact simulation -/

/--
EXACT SIMULATION OF THE SPAN BLOCK, PARAMETRIC IN THE READ GEOMETRY.

Both arms exit at `Q + 222`.  The receipt is the span read's route events
followed, ON THE `some` ARM ONLY, by the leg's four; the `none` arm
contributes nothing after its own read, which is exactly what
`FlatStoreComputation.pure none` (`InteriorDirectory.lean:2327`, `:2344`)
does.

The value lands in the merge bank's middle slot via `bestOfRegs`, which is
the form the merge combiners consume.

NO STORE HYPOTHESIS AND NO VALIDITY HYPOTHESIS.  The only premises are
the hosting, the two caller-supplied inputs, and the read geometry's
chunk-count cap -- the same two facts `summaryStage_runsTo` needs.
-/
theorem spanBlock_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {G : TableGeom} {Q slot off : Nat} {regs : RegFile}
    (hHost : HostedAt program Q
      (spanBlock (canonicalSummaryLayout shape) G
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper Q))
    (hSlot : regs pSlot = slot) (hOff : regs pOff = off)
    (hccPos : 0 < G.chunkCount) (hccCap : G.chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 222, false⟩
          (spanEvents shape G slot off) (spanCats shape G slot off) ∧
        bestOfRegs (regs' mMV) (regs' mMP) = spanValue shape G slot off := by
  -- hosting: the constant and the stage, the arm selector, the leg
  have hPre : HostedAt program Q
      (Instr.const pOne 1 ::
        summaryStage (Instr.move iIdx pSlot)
          (canonicalSummaryLayout shape).segment G.base
          (canonicalSummaryLayout shape).deadAddress G.entriesLen
          G.chunkCount (canonicalSummaryLayout shape).wordScale pCell
          (Q + 1)) := hHost.append_left
  have hRest : HostedAt program (Q + 40)
      (spanArms Q ++
        (summaryGroup (canonicalSummaryLayout shape) (Q + 45) ++
          minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
            (RelativeRmm.canonicalLayout shape).blocksPerSuper
            (Q + 45 + 156))) := by
    have h := hHost.append_right (code₁ := Instr.const pOne 1 ::
      summaryStage (Instr.move iIdx pSlot)
        (canonicalSummaryLayout shape).segment G.base
        (canonicalSummaryLayout shape).deadAddress G.entriesLen
        G.chunkCount (canonicalSummaryLayout shape).wordScale pCell (Q + 1))
    simpa using h
  have hArms : HostedAt program (Q + 40)
      [ Instr.brNZ pCell (Q + 43), Instr.const mMV 0
      , Instr.brNZ pOne (Q + 222), Instr.sub pT pCell pOne
      , Instr.add sBlock pOff pT ] := by
    have h : HostedAt program (Q + 40) (spanArms Q) := hRest.append_left
    simpa [spanArms] using h
  have hLeg : HostedAt program (Q + 45)
      (summaryGroup (canonicalSummaryLayout shape) (Q + 45) ++
        minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 45 + 156)) := by
    have h := hRest.append_right (code₁ := spanArms Q)
    simpa using h
  -- the constant, then the stage's head
  have hStep0 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs, Q, false⟩ ⟨regs.write pOne 1, Q + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (by simp) (by simpa using hPre.head)
  have hStage : HostedAt program (Q + 1)
      (summaryStage (Instr.move iIdx pSlot)
        (canonicalSummaryLayout shape).segment G.base
        (canonicalSummaryLayout shape).deadAddress G.entriesLen
        G.chunkCount (canonicalSummaryLayout shape).wordScale pCell
        (Q + 1)) := hPre.tail
  have hF1 : program[Q + 1]? = some (Instr.move iIdx pSlot) := hStage.head
  have hHead : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs.write pOne 1, Q + 1, false⟩
      ⟨(regs.write pOne 1).write iIdx ((regs.write pOne 1) pSlot),
        Q + 1 + 1, false⟩ [] [Category.registerWrite] :=
    RunsTo.move (s := ⟨regs.write pOne 1, Q + 1, false⟩) rfl hF1
  have hIdx : ((regs.write pOne 1).write iIdx ((regs.write pOne 1) pSlot))
      iIdx = slot := by
    rw [RegFile.write_same, RegFile.write_other _ _ (by decide)]
    exact hSlot
  obtain ⟨regs2, hStageRun, hCell, hStagePres⟩ :=
    summaryStage_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hStage hHead hIdx hccPos hccCap
  have hCell' : regs2 pCell = spanCell shape G slot := hCell
  -- INTO GEOM VOCABULARY, BY DEFEQ, ONCE.  `geomEvents`/`geomCats`/
  -- `spanCell` are one delta step from the stage's own spelling, so these
  -- three ascriptions are free.  Doing it here rather than in a `simp` set
  -- downstream is what keeps the concrete store out of every later
  -- rewrite: unfolding `geomEvents` in a goal forces
  -- `canonicalSummaryLayout`'s projections, and that is a whnf blowup, not
  -- a resource shortage.
  have hStageRun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs.write pOne 1, Q + 1, false⟩ ⟨regs2, Q + 40, false⟩
      (geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G slot)
      (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G Category.registerWrite slot) :=
    hStageRun
  -- the two caller inputs survive the stage
  have hOne2 : regs2 pOne = 1 := by
    rw [hStagePres pOne (by decide)]
    rw [RegFile.write_other _ _ (by decide), RegFile.write_same]
  have hOff2 : regs2 pOff = off := by
    rw [hStagePres pOff (by decide)]
    rw [RegFile.write_other _ _ (by decide),
      RegFile.write_other _ _ (by decide)]
    exact hOff
  cases hc : spanCell shape G slot with
  | zero =>
      -- THE `none` ARM: result `none`, and past ALL 177 instructions
      have hCell0 : regs2 pCell = 0 := by rw [hCell']; exact hc
      have hStep1 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 40, false⟩ ⟨regs2, Q + 41, false⟩ []
          [Category.branch] := by
        have h := RunsTo.brNZ
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2, Q + 40, false⟩) (by simp) (by simpa using hArms.head)
        simpa [hCell0] using h
      have hF41 : program[Q + 41]? = some (Instr.const mMV 0) := by
        have h := hArms.tail.head
        have harith : Q + 40 + 1 = Q + 41 := by omega
        rwa [harith] at h
      have hStep2 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 41, false⟩ ⟨regs2.write mMV 0, Q + 42, false⟩ []
          [Category.registerWrite] := by
        have h := RunsTo.const
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2, Q + 41, false⟩) (by simp) hF41
        simpa using h
      have hF42 : program[Q + 42]? = some (Instr.brNZ pOne (Q + 222)) := by
        have h := hArms.tail.tail.head
        have harith : Q + 40 + 1 + 1 = Q + 42 := by omega
        rwa [harith] at h
      have hOne3 : (regs2.write mMV 0) pOne = 1 := by
        rw [RegFile.write_other _ _ (by decide)]; exact hOne2
      have hStep3 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2.write mMV 0, Q + 42, false⟩
          ⟨regs2.write mMV 0, Q + 222, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2.write mMV 0, Q + 42, false⟩) (by simp) hF42
        simpa [hOne3] using h
      refine ⟨regs2.write mMV 0, ?_, ?_⟩
      · have h := ((hStep0.trans hStageRun').trans hStep1).trans
          (hStep2.trans hStep3)
        simpa [spanEvents, spanCats, hc, List.append_assoc] using h
      · rw [RegFile.write_same]
        simp [spanValue, hc]
  | succ v =>
      -- THE `some` ARM: unshift, form the block index, run the leg
      have hCellS : regs2 pCell = v + 1 := by rw [hCell']; exact hc
      have hStep1 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 40, false⟩ ⟨regs2, Q + 43, false⟩ []
          [Category.branch] := by
        have h := RunsTo.brNZ
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2, Q + 40, false⟩) (by simp) (by simpa using hArms.head)
        simpa [hCellS] using h
      have hF43 : program[Q + 43]? = some (Instr.sub pT pCell pOne) := by
        have h := hArms.tail.tail.tail.head
        have harith : Q + 40 + 1 + 1 + 1 = Q + 43 := by omega
        rwa [harith] at h
      have hStep2 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 43, false⟩
          ⟨regs2.write pT v, Q + 44, false⟩ [] [Category.arithmetic] := by
        have h := RunsTo.sub
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2, Q + 43, false⟩) (by simp) hF43
        simpa [hCellS, hOne2] using h
      have hF44 : program[Q + 44]? = some (Instr.add sBlock pOff pT) := by
        have h := hArms.tail.tail.tail.tail.head
        have harith : Q + 40 + 1 + 1 + 1 + 1 = Q + 44 := by omega
        rwa [harith] at h
      have hOff3 : (regs2.write pT v) pOff = off := by
        rw [RegFile.write_other _ _ (by decide)]; exact hOff2
      have hStep3 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2.write pT v, Q + 44, false⟩
          ⟨(regs2.write pT v).write sBlock (off + v), Q + 45, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.add
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := ⟨regs2.write pT v, Q + 44, false⟩) (by simp) hF44
        simpa [hOff3, RegFile.write_same] using h
      obtain ⟨regs5, hLegRun, hLegVal⟩ :=
        summaryMinCandidate_runsTo shape hLeg
          (regs := (regs2.write pT v).write sBlock (off + v))
          (block := off + v) (by rw [RegFile.write_same])
      have hpc : Q + 45 + 177 = Q + 222 := by omega
      rw [hpc] at hLegRun
      -- the leg's receipt, charge log and value, in the named vocabulary
      have hLegRun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨(regs2.write pT v).write sBlock (off + v), Q + 45, false⟩
          ⟨regs5, Q + 222, false⟩ (legEvents shape (off + v))
          (legCats shape (off + v)) := hLegRun
      have hLegVal' : bestOfRegs (regs5 mMV) (regs5 mMP) =
          legValue shape (off + v) := hLegVal
      refine ⟨regs5, ?_, ?_⟩
      · have h := (((hStep0.trans hStageRun').trans hStep1).trans
          (hStep2.trans hStep3)).trans hLegRun'
        simpa [spanEvents, spanCats, hc, List.append_assoc] using h
      · rw [hLegVal']
        simp [spanValue, hc]

/-! ## THE `none` ARM'S DISCRIMINATOR (DD-20260719-050)

RIGHT SHAPE, WRONG CONTENT, third variety: a result that is `some` where
the route is `none`, with an IDENTICAL receipt and an IDENTICAL read
count.

The impostor is not invented for this section.  It is the single wrong
numeral available at `spanArms`' `Q + 42`: branching to the leg's
consumer at `Q + 45 + 156` -- past the summary group -- instead of to the
block's exit at `Q + 222`.  Skipping only the group is precisely the
dangerous error, because the group is where the four READS are: an arm
that fell into the group would be caught by the receipt, whereas the
consumer is READ-FREE (`minCandidateBlock_readFree`) and leaves the
receipt untouched while overwriting `mMV`/`mMP` from whatever four cells
happen to be sitting in `sBase`, `sMin`, `sMax`, `sArg`.

So this fixture holds everything fixed but that numeral, and runs both. -/

/-- The empty store.  Neither arm may depend on the store, and using the
empty one makes that manifest. -/
def armStore : ReadStore := ⟨fun _ _ => none⟩

/-- THE TWO ARMS, DIFFERING IN ONE NUMERAL.

Index `0` sets the result to `none`; index `1` jumps to `target`; indices
`2 .. 22` are the REAL min-candidate consumer at its own base `2`; index
`23` halts.

`target = 23` is the correct arm -- past the consumer, as `Q + 222` is
past the leg.  `target = 2` is the impostor that lands ON the consumer,
as `Q + 45 + 156` would. -/
def noneArmProgram (target : Nat) : E1Machine.Program :=
  [ Instr.const mMV 0, Instr.brNZ pOne target ] ++
    (minCandidateBlock 4 2 2 ++ [Instr.halt])

/-- `pOne` carries the unconditional-jump condition; the four summary
cells are the STALE ones the impostor would consume. -/
def armRegs (block cB cMn cMx cA : Nat) : RegFile := fun r =>
  if r = pOne then 1
  else if r = sBlock then block
  else if r = sBase then cB
  else if r = sMin then cMn
  else if r = sMax then cMx
  else if r = sArg then cA
  else 0

/-- The arm's value, in the form the merge combiners consume. -/
def armOut (target block cB cMn cMx cA : Nat) : Option (Nat × Nat) :=
  let final :=
    (E1Machine.run armStore (noneArmProgram target) 30
      ⟨armRegs block cB cMn cMx cA, 0, false⟩).final.regs
  bestOfRegs (final mMV) (final mMP)

/-- The arm's receipt. -/
def armReadLog (target block cB cMn cMx cA : Nat) : List TraceEvent :=
  (E1Machine.run armStore (noneArmProgram target) 30
    ⟨armRegs block cB cMn cMx cA, 0, false⟩).readLog

/-- The arm's charge log. -/
def armCatLog (target block cB cMn cMx cA : Nat) : List Category :=
  (E1Machine.run armStore (noneArmProgram target) 30
    ⟨armRegs block cB cMn cMx cA, 0, false⟩).catLog

/-- The correct arm returns `none`, which is the route's value on the
`none` arm (`InteriorDirectory.lean:2327`). -/
theorem armOut_correct : armOut 23 1 10 5 7 3 = none := by rfl

/-- The impostor returns `some`, assembled from four cells the route
never read on this arm. -/
theorem armOut_impostor : armOut 2 1 10 5 7 3 = some (5, 6) := by rfl

/-- THE DISCRIMINATOR: the one numeral is load-bearing, and an arm that
branched past only the group's 156 instructions would be WRONG, not
merely differently spelled. -/
theorem spanNoneArm_discriminates :
    armOut 23 1 10 5 7 3 ≠ armOut 2 1 10 5 7 3 := by decide

/-- THE NON-ENTAILMENT, and the reason this needed a fixture at all: the
two RECEIPTS ARE EQUAL.  A receipt equation -- the whole content of
`minCandidateMachineTrace_eq_routeReads` and of this block's own
`spanEvents` clause -- is FORMALLY INCAPABLE of rejecting the impostor.
Only the value clause rejects it. -/
theorem spanNoneArm_traces_agree :
    armReadLog 23 1 10 5 7 3 = armReadLog 2 1 10 5 7 3 := by rfl

/-- Both receipts are empty, so the read COUNT does not separate them
either. -/
theorem spanNoneArm_traces_empty :
    armReadLog 23 1 10 5 7 3 = [] ∧ armReadLog 2 1 10 5 7 3 = [] :=
  ⟨by rfl, by rfl⟩

/-- What DOES separate them, besides the value: the charge logs differ,
because the impostor executes the consumer's 21 instructions.  Recorded
so the boundary of the previous two theorems is exact -- a POSITIONAL
category check catches this impostor, a receipt check does not. -/
theorem spanNoneArm_catLogs_differ :
    armCatLog 23 1 10 5 7 3 ≠ armCatLog 2 1 10 5 7 3 := by decide

/-- The impostor is not rejected by exit code either: both arms halt. -/
theorem spanNoneArm_both_halt :
    (E1Machine.run armStore (noneArmProgram 23) 30
        ⟨armRegs 1 10 5 7 3, 0, false⟩).final.halted = true ∧
      (E1Machine.run armStore (noneArmProgram 2) 30
        ⟨armRegs 1 10 5 7 3, 0, false⟩).final.halted = true :=
  ⟨by rfl, by rfl⟩

end E1InteriorSpanBlock
end WordRAM
end RMQ

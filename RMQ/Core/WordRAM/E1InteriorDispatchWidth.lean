import RMQ.Core.WordRAM.E1InteriorDispatchCompose

/-!
# Width accounting for the INTERIOR DISPATCH BLOCK (REQ-E1-02)

`crossBlockArmProgramAt_fits` (`E1CrossBlockArm.lean:913`) carries the
interior's instructions as the hypothesis `hinterior`, stated before any
interior existed so that the interior would have to be certified when it
landed.  It landed as `canonicalInteriorDispatchBlock`
(`E1InteriorDispatchCompose.lean:89`, 4204 instructions at `:103`) and was
never certified: before this module the only `FieldsFit` lemmas anywhere
below it were the two LEAVES, `interiorChunkFold_fits`
(`E1InteriorChunkFold.lean:619`) and `minCandidateBlock_fits`
(`E1InteriorMinCandidate.lean:291`).  Every intermediate layer --
`summaryStage`, `summaryGroup`, `spanArms`, `spanBlock`, `mergeBlock`,
`mergeShuttle`, `legSetup`, `twoSpanArms`, `twoSpanBlock`, `twoLegBlock`,
`crossLegBlock` and `interiorDispatchBlock` itself -- had none, so
`hinterior` was an OWED premise with no witness at any instantiation.

This module supplies that chain, PARAMETRICALLY in `w`.  It does not pick a
width.

## The two bundles

`GeomFits` and `LayoutFits` bundle the field bounds of `TableGeom` and
`SummaryLayout`.  Neither structure carries positivity or bound fields of its
own -- unlike `SparseExceptionSelectData`, whose `_pos`/`_le_machine` fields
are free projections -- so every geometry bound here is a genuine side
condition, named rather than assumed away.

Four divisor positivities are load-bearing and cannot be dropped:
`0 < L.blocksPerSuper` (the `divConst` opening `summaryGroup`'s first stage),
`0 < D` (the level `divConst` in `twoSpanArms`), and `0 < blockSize` /
`0 < macroSize` in the dispatch preamble.

## The register bound

`151 < 2 ^ w` throughout.  `151` is `wLeft` (`E1InteriorDispatch.lean:117`),
the global maximum of the WordRAM register map -- nothing above it is defined
-- so this single bound dominates the leaves' own `99 < 2 ^ w` and
`117 < 2 ^ w`.

`reg_bound` exists because register indices are `abbrev`s and therefore
OPAQUE to `omega`; the `try` in it matters, since `simp only` FAILS when it
makes no progress and most goals here carry no register at all.

DD-20260719-261.
-/


namespace RMQ
namespace WordRAM
namespace E1InteriorDispatchWidth

open E1Machine
open E1InteriorSummaryGroup
open E1InteriorChunkFold
open E1InteriorMinCandidate
open E1InteriorSpanBlock
open E1InteriorMerge
open E1InteriorTwoSpan
open E1InteriorCombine
open E1InteriorDispatch

/-- Register indices are `abbrev`s and are OPAQUE to `omega`; every bound on
one has to unfold it first.  The `try` matters: `simp only` FAILS when it
makes no progress, and most goals here carry no register at all. -/
local macro "reg_bound" : tactic =>
  `(tactic|
    ((try simp only [E1InteriorReadBlock.iIdx, E1InteriorChunkFold.cOut,
      E1InteriorSummaryGroup.sBlock, E1InteriorSummaryGroup.sBase,
      E1InteriorSummaryGroup.sMin, E1InteriorSummaryGroup.sMax,
      E1InteriorSummaryGroup.sArg,
      E1InteriorSpanBlock.pSlot, E1InteriorSpanBlock.pOff,
      E1InteriorSpanBlock.pCell, E1InteriorSpanBlock.pT,
      E1InteriorSpanBlock.pOne,
      E1InteriorMerge.qLV, E1InteriorMerge.qLP, E1InteriorMerge.qT,
      E1InteriorMerge.qOne,
      E1CandMerge3.mMV, E1CandMerge3.mMP,
      E1InteriorTwoSpan.tA, E1InteriorTwoSpan.tStart, E1InteriorTwoSpan.tN,
      E1InteriorTwoSpan.tOff, E1InteriorTwoSpan.tCell,
      E1InteriorTwoSpan.tLvl, E1InteriorTwoSpan.tRS, E1InteriorTwoSpan.tT,
      E1InteriorTwoSpan.tOne,
      E1InteriorCombine.uMacro, E1InteriorCombine.uLocal,
      E1InteriorCombine.uMid, E1InteriorCombine.uRight,
      E1InteriorCombine.uT, E1InteriorCombine.uZero,
      E1InteriorCombine.uSV, E1InteriorCombine.uSP,
      E1InteriorCombine.vSV, E1InteriorCombine.vSP,
      E1InteriorDispatch.wOne, E1InteriorDispatch.wT,
      E1InteriorDispatch.wStart, E1InteriorDispatch.wCount,
      E1InteriorDispatch.wRem, E1InteriorDispatch.wLeft,
      E1InteriorDispatch.dispatchJoin,
      E1SameBlockArm.fClose, E1SameBlockArm.fRight]); omega))

def GeomFits (w : Nat) (G : TableGeom) : Prop :=
  G.base < 2 ^ w ∧ G.entriesLen < 2 ^ w ∧ G.chunkCount < 2 ^ w

def LayoutFits (w : Nat) (L : SummaryLayout) : Prop :=
  L.segment < 2 ^ w ∧ L.deadAddress < 2 ^ w ∧
    0 < L.wordScale ∧ L.wordScale < 2 ^ w ∧
    0 < L.blocksPerSuper ∧ L.blocksPerSuper < 2 ^ w ∧
    GeomFits w L.baseline ∧ GeomFits w L.minRel ∧
    GeomFits w L.maxRel ∧ GeomFits w L.argOffset

theorem summaryStage_fits {w : Nat} {idxInstr : Instr}
    {segment base deadAddress entriesLen chunkCount wordScale save Q : Nat}
    (hidx : Instr.FieldsFit w idxInstr)
    (hw : 99 < 2 ^ w) (hQ : Q + 38 < 2 ^ w) (hseg : segment < 2 ^ w)
    (hbase : base < 2 ^ w) (hdead : deadAddress < 2 ^ w)
    (hlen : entriesLen < 2 ^ w) (hcc : chunkCount < 2 ^ w)
    (hscale0 : 0 < wordScale) (hscale : wordScale < 2 ^ w)
    (hsave : save < 2 ^ w) :
    ∀ instr ∈ summaryStage idxInstr segment base deadAddress entriesLen
        chunkCount wordScale save Q,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [summaryStage, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | h | rfl
  · exact hidx
  · exact interiorChunkFold_fits hw (by omega) hseg hbase hdead hlen hcc
      hscale0 hscale instr h
  · exact ⟨hsave, by reg_bound⟩

theorem summaryGroup_fits {w : Nat} {L : SummaryLayout} {Q : Nat}
    (hL : LayoutFits w L) (hreg : 151 < 2 ^ w) (hQ : Q + 155 < 2 ^ w) :
    ∀ instr ∈ summaryGroup L Q, Instr.FieldsFit w instr := by
  obtain ⟨hseg, hdead, hws0, hws, hbps0, hbps, hb, hmn, hmx, hag⟩ := hL
  have hdiv : Instr.FieldsFit w
      (Instr.divConst E1InteriorReadBlock.iIdx sBlock L.blocksPerSuper) :=
    ⟨by reg_bound, by reg_bound, hbps0, hbps⟩
  have hmv : Instr.FieldsFit w
      (Instr.move E1InteriorReadBlock.iIdx sBlock) :=
    ⟨by reg_bound, by reg_bound⟩
  intro instr hmem
  simp only [summaryGroup, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact summaryStage_fits hdiv (by omega) (by omega) hseg hb.1 hdead
      hb.2.1 hb.2.2 hws0 hws (by reg_bound) instr h
  · exact summaryStage_fits hmv (by omega) (by omega) hseg hmn.1 hdead
      hmn.2.1 hmn.2.2 hws0 hws (by reg_bound) instr h
  · exact summaryStage_fits hmv (by omega) (by omega) hseg hmx.1 hdead
      hmx.2.1 hmx.2.2 hws0 hws (by reg_bound) instr h
  · exact summaryStage_fits hmv (by omega) (by omega) hseg hag.1 hdead
      hag.2.1 hag.2.2 hws0 hws (by reg_bound) instr h

theorem spanArms_fits {w Q : Nat} (hreg : 151 < 2 ^ w)
    (hQ : Q + 222 < 2 ^ w) :
    ∀ instr ∈ spanArms Q, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [spanArms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem spanBlock_fits {w : Nat} {L : SummaryLayout} {G : TableGeom}
    {blockSize blocksPerSuper Q : Nat}
    (hL : LayoutFits w L) (hG : GeomFits w G) (hreg : 151 < 2 ^ w)
    (hQ : Q + 222 < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w)
    (hsize : blockSize < 2 ^ w) :
    ∀ instr ∈ spanBlock L G blockSize blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  have hL' := hL
  obtain ⟨hseg, hdead, hws0, hws, hbps0, hbps, -, -, -, -⟩ := hL
  have hmv : Instr.FieldsFit w
      (Instr.move E1InteriorReadBlock.iIdx pSlot) :=
    ⟨by reg_bound, by reg_bound⟩
  intro instr hmem
  simp only [spanBlock, List.mem_cons, List.mem_append] at hmem
  rcases hmem with (rfl | h) | h | h | h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact summaryStage_fits hmv (by omega) (by omega)
      hseg hG.1 hdead hG.2.1 hG.2.2 hws0 hws (by reg_bound) instr h
  · exact spanArms_fits hreg hQ instr h
  · exact summaryGroup_fits hL' hreg (by omega) instr h
  · exact minCandidateBlock_fits w blockSize blocksPerSuper (Q + 45 + 156)
      (by omega) (by omega) hspan hsize instr h


theorem mergeBlock_fits {w Q : Nat} (hreg : 151 < 2 ^ w)
    (hQ : Q + 9 < 2 ^ w) :
    ∀ instr ∈ mergeBlock Q, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [mergeBlock, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem mergeShuttle_fits {w : Nat} (hreg : 151 < 2 ^ w) :
    ∀ instr ∈ mergeShuttle, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [mergeShuttle, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨by reg_bound, by reg_bound⟩

theorem legSetup_fits {w kA kO srcMacro srcStart srcN : Nat}
    (hreg : 151 < 2 ^ w) (hkA : kA < 2 ^ w) (hkO : kO < 2 ^ w)
    (hsm : srcMacro < 2 ^ w) (hss : srcStart < 2 ^ w) (hsn : srcN < 2 ^ w) :
    ∀ instr ∈ legSetup kA kO srcMacro srcStart srcN,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [legSetup, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem twoSpanArms_fits {w M D Q : Nat} (hreg : 151 < 2 ^ w)
    (hQ : Q + 509 < 2 ^ w) (hM : M < 2 ^ w) (hD0 : 0 < D) (hD : D < 2 ^ w) :
    ∀ instr ∈ twoSpanArms M D Q, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [twoSpanArms, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, hD0, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem twoSpanBlock_fits {w : Nat} {L : SummaryLayout} {GL GS : TableGeom}
    {M D blockSize blocksPerSuper Q : Nat}
    (hL : LayoutFits w L) (hGL : GeomFits w GL) (hGS : GeomFits w GS)
    (hreg : 151 < 2 ^ w) (hQ : Q + 509 < 2 ^ w)
    (hM : M < 2 ^ w) (hD0 : 0 < D) (hD : D < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w)
    (hsize : blockSize < 2 ^ w) :
    ∀ instr ∈ twoSpanBlock L GL GS M D blockSize blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  have hL' := hL
  obtain ⟨hseg, hdead, hws0, hws, -, -, -, -, -, -⟩ := hL
  have hmv : Instr.FieldsFit w (Instr.move E1InteriorReadBlock.iIdx tN) :=
    ⟨by reg_bound, by reg_bound⟩
  intro instr hmem
  simp only [twoSpanBlock, List.mem_cons, List.mem_append] at hmem
  rcases hmem with (rfl | h) | h | h | h | rfl | h | h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact summaryStage_fits hmv (by omega) (by omega)
      hseg hGL.1 hdead hGL.2.1 hGL.2.2 hws0 hws (by reg_bound) instr h
  · exact twoSpanArms_fits hreg hQ hM hD0 hD instr h
  · exact spanBlock_fits hL' hGS hreg (by omega) hspan hsize instr h
  · exact mergeShuttle_fits hreg instr h
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact spanBlock_fits hL' hGS hreg (by omega) hspan hsize instr h
  · exact mergeBlock_fits hreg (by omega) instr h


theorem twoLegBlock_fits {w : Nat} {L : SummaryLayout}
    {GL1 GS1 GL2 GS2 : TableGeom}
    {M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat}
    (hL : LayoutFits w L) (hGL1 : GeomFits w GL1) (hGS1 : GeomFits w GS1)
    (hGL2 : GeomFits w GL2) (hGS2 : GeomFits w GS2)
    (hreg : 151 < 2 ^ w) (hQ : Q + 1044 < 2 ^ w)
    (hM1 : M1 < 2 ^ w) (hD10 : 0 < D1) (hD1 : D1 < 2 ^ w)
    (hM2 : M2 < 2 ^ w) (hD20 : 0 < D2) (hD2 : D2 < 2 ^ w)
    (hkA1 : kA1 < 2 ^ w) (hkO1 : kO1 < 2 ^ w)
    (hkA2 : kA2 < 2 ^ w) (hkO2 : kO2 < 2 ^ w)
    (hss2 : srcStart2 < 2 ^ w) (hsn2 : srcN2 < 2 ^ w)
    (hms : macroSize < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w)
    (hsize : blockSize < 2 ^ w) :
    ∀ instr ∈ twoLegBlock L GL1 GS1 GL2 GS2 M1 D1 M2 D2 kA1 kO1 kA2 kO2
        srcStart2 srcN2 macroSize blockSize blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [twoLegBlock, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with (rfl | rfl | rfl) | h | h | (rfl | rfl) | (rfl | rfl) |
    h | h | (rfl | rfl) | h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact legSetup_fits hreg hkA1 hkO1 (by reg_bound) (by reg_bound)
      (by reg_bound) instr h
  · exact twoSpanBlock_fits hL hGL1 hGS1 hreg (by omega) hM1 hD10 hD1
      hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact legSetup_fits hreg hkA2 hkO2 (by reg_bound) hss2 hsn2 instr h
  · exact twoSpanBlock_fits hL hGL2 hGS2 hreg (by omega) hM2 hD20 hD2
      hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact mergeBlock_fits hreg (by omega) instr h

theorem crossLegBlock_fits {w : Nat} {L : SummaryLayout}
    {GL1 GS1 GL2 GS2 GL3 GS3 : TableGeom}
    {M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat}
    (hL : LayoutFits w L) (hGL1 : GeomFits w GL1) (hGS1 : GeomFits w GS1)
    (hGL2 : GeomFits w GL2) (hGS2 : GeomFits w GS2)
    (hGL3 : GeomFits w GL3) (hGS3 : GeomFits w GS3)
    (hreg : 151 < 2 ^ w) (hQ : Q + 1574 < 2 ^ w)
    (hM1 : M1 < 2 ^ w) (hD10 : 0 < D1) (hD1 : D1 < 2 ^ w)
    (hM2 : M2 < 2 ^ w) (hD20 : 0 < D2) (hD2 : D2 < 2 ^ w)
    (hM3 : M3 < 2 ^ w) (hD30 : 0 < D3) (hD3 : D3 < 2 ^ w)
    (hkA1 : kA1 < 2 ^ w) (hkO1 : kO1 < 2 ^ w)
    (hkA2 : kA2 < 2 ^ w) (hkO2 : kO2 < 2 ^ w)
    (hkA3 : kA3 < 2 ^ w) (hkO3 : kO3 < 2 ^ w)
    (hss2 : srcStart2 < 2 ^ w) (hsn2 : srcN2 < 2 ^ w)
    (hms : macroSize < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w)
    (hsize : blockSize < 2 ^ w) :
    ∀ instr ∈ crossLegBlock L GL1 GS1 GL2 GS2 GL3 GS3 M1 D1 M2 D2 M3 D3
        kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2 macroSize blockSize
        blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [crossLegBlock, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | (rfl | rfl) | (rfl | rfl | rfl | rfl) | h | h |
    (rfl | rfl) | h
  · exact twoLegBlock_fits hL hGL1 hGS1 hGL2 hGS2 hreg (by omega) hM1 hD10 hD1
      hM2 hD20 hD2 hkA1 hkO1 hkA2 hkO2 hss2 hsn2 hms hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact legSetup_fits hreg hkA3 hkO3 (by reg_bound) (by reg_bound)
      (by reg_bound) instr h
  · exact twoSpanBlock_fits hL hGL3 hGS3 hreg (by omega) hM3 hD30 hD3
      hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact mergeBlock_fits hreg (by omega) instr h


theorem rangePreamble_fits {w blockSize : Nat} (hreg : 151 < 2 ^ w)
    (hbs0 : 0 < blockSize) (hbs : blockSize < 2 ^ w) :
    ∀ instr ∈ rangePreamble blockSize, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [rangePreamble, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, hbs0, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem indexDecomp_fits {w macroSize : Nat} (hreg : 151 < 2 ^ w)
    (hms0 : 0 < macroSize) (hms : macroSize < 2 ^ w) :
    ∀ instr ∈ indexDecomp macroSize, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [indexDecomp, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, hms0, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem localArmSetup_fits {w macroSize levelSlab : Nat} (hreg : 151 < 2 ^ w)
    (hms : macroSize < 2 ^ w) (hls : levelSlab < 2 ^ w) :
    ∀ instr ∈ localArmSetup macroSize levelSlab, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [localArmSetup, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem dispatchSelector_fits {w Q : Nat} (hreg : 151 < 2 ^ w)
    (hQ : Q + 4204 < 2 ^ w) :
    ∀ instr ∈ dispatchSelector Q, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [dispatchSelector, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact ⟨by reg_bound, by reg_bound⟩
      | exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem dispatchArm0_fits {w Q : Nat} (hreg : 151 < 2 ^ w)
    (hQ : Q + 4204 < 2 ^ w) :
    ∀ instr ∈ dispatchArm0 Q, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [dispatchArm0, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨by reg_bound, by reg_bound⟩

/-- **THE INTERIOR DISPATCH BLOCK FITS** -- all 4204 instructions, at any `w`
meeting the stated bounds. -/
theorem interiorDispatchBlock_fits {w : Nat} {L : SummaryLayout}
    {GLl GSl GLg GSg : TableGeom}
    {macroSize macroSampleCount levelSlab Dl Dg blockSize blocksPerSuper
      Q : Nat}
    (hL : LayoutFits w L) (hGLl : GeomFits w GLl) (hGSl : GeomFits w GSl)
    (hGLg : GeomFits w GLg) (hGSg : GeomFits w GSg)
    (hreg : 151 < 2 ^ w) (hQ : Q + 4204 < 2 ^ w)
    (hms0 : 0 < macroSize) (hms : macroSize < 2 ^ w)
    (hmsc : macroSampleCount < 2 ^ w) (hls : levelSlab < 2 ^ w)
    (hDl0 : 0 < Dl) (hDl : Dl < 2 ^ w) (hDg0 : 0 < Dg) (hDg : Dg < 2 ^ w)
    (hbs0 : 0 < blockSize) (hsize : blockSize < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w) :
    ∀ instr ∈ interiorDispatchBlock L GLl GSl GLg GSg macroSize
        macroSampleCount levelSlab Dl Dg blockSize blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [interiorDispatchBlock, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | (h | rfl) | (h | rfl) | (h | rfl) | h
  · exact rangePreamble_fits hreg hbs0 hsize instr h
  · exact indexDecomp_fits hreg hms0 hms instr h
  · exact localArmSetup_fits hreg hms hls instr h
  · exact dispatchSelector_fits hreg hQ instr h
  · exact dispatchArm0_fits hreg hQ instr h
  · exact twoSpanBlock_fits hL hGLl hGSl hreg (by omega) hms hDl0 hDl
      hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact twoLegBlock_fits hL hGLl hGSl hGLl hGSl hreg (by omega) hms hDl0 hDl
      hms hDl0 hDl hls (by reg_bound) hls (by reg_bound) (by reg_bound)
      (by reg_bound) hms hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact twoLegBlock_fits hL hGLl hGSl hGLg hGSg hreg (by omega) hms hDl0 hDl
      hmsc hDg0 hDg hls (by reg_bound) (by reg_bound) (by reg_bound)
      (by reg_bound) (by reg_bound) hms hspan hsize instr h
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact crossLegBlock_fits hL hGLl hGSl hGLg hGSg hGLl hGSl hreg (by omega)
      hms hDl0 hDl hmsc hDg0 hDg hms hDl0 hDl hls (by reg_bound)
      (by reg_bound) (by reg_bound) hls (by reg_bound) (by reg_bound)
      (by reg_bound) hms hspan hsize instr h

end E1InteriorDispatchWidth
end WordRAM
end RMQ

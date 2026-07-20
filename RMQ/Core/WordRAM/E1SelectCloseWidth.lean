import RMQ.Core.WordRAM.E1SelectDispatch

/-!
# Width accounting for the SELECT-CLOSE DISPATCH BLOCK (REQ-E1-02)

`selectCloseBlock` (`E1SelectDispatch.lean:157`, 405 instructions) is the
block `wholeQuerySelectLeg` runs twice, and before this module it had no
`FieldsFit` lemma of any kind -- only its four LEAVES did
(`entryReadBlock_fits`, `E1SelectBridge.lean:392`;
`denseSelectLegBlock_fits`, `E1DenseSelectBlock.lean:1590`;
`longLegBlock_fits` and `sparseLegBlock_fits`, `E1SelectLegBlocks.lean:615`
and `:638`).  This module supplies the four straight-line segments, the
thirteen inline glue instructions and the composition, PARAMETRICALLY in `w`.

## The register bound

`40 <= 2 ^ w` throughout.  `39` is `xBOcc` (`E1SelectBridge.lean:91`), the
global maximum of the select register map -- nothing above it is defined --
so this single bound dominates the leaves' own `28 <= 2 ^ w` and
`40 <= 2 ^ w`.

`reg_bound` exists because register indices are `abbrev`s and therefore
OPAQUE to `omega`; the `try` in it matters, since `simp only` FAILS when it
makes no progress and several goals here carry no register at all.

## The three divisor positivities

`0 < SS` (`selectSuperSlotSeg`'s `divConst`), `0 < LS`
(`selectLocalSlotSeg`'s), and `0 < c` inside the legs.  None can be dropped:
`Instr.FieldsFit` has a `0 < k` arm on `divConst` with no wildcard.

DD-20260719-302.
-/

namespace RMQ
namespace WordRAM
namespace E1SelectCloseWidth

open E1Machine
open E1RankBlock
open E1SelectBridge
open E1DenseSelectBlock
open E1SelectLegBlocks
open E1SelectDispatch

/-- Register indices are `abbrev`s and are OPAQUE to `omega`; every bound on
one has to unfold it first.  The `try` matters: `simp only` FAILS when it
makes no progress, and several goals here carry no register at all. -/
local macro "reg_bound" : tactic =>
  `(tactic|
    ((try simp only [E1RankBlock.rPos, E1RankBlock.rVal, E1RankBlock.rP,
      E1RankBlock.rA, E1RankBlock.rB, E1RankBlock.rOne, E1RankBlock.rC,
      E1RankBlock.rEight,
      E1SelectBridge.xIdx, E1SelectBridge.xQ,
      E1SelectBridge.xSF1, E1SelectBridge.xSF2, E1SelectBridge.xSF3,
      E1SelectBridge.xSF4,
      E1SelectBridge.xLF1, E1SelectBridge.xLF2, E1SelectBridge.xLF3,
      E1SelectBridge.xLF4,
      E1SelectBridge.xBPos, E1SelectBridge.xBOcc]); omega))

/-! ## The four straight-line segments -/

theorem selectPrologue_fits {w c OC : Nat} (hreg : 40 <= 2 ^ w)
    (hc : c < 2 ^ w) (hOC : OC < 2 ^ w) :
    ∀ instr ∈ selectPrologue c OC, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [selectPrologue, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, hc⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, hOC⟩
  · exact ⟨by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

theorem selectSuperSlotSeg_fits {w SS : Nat} (hreg : 40 <= 2 ^ w)
    (hSSpos : 0 < SS) (hSS : SS < 2 ^ w) :
    ∀ instr ∈ selectSuperSlotSeg SS, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [selectSuperSlotSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨by reg_bound, by reg_bound, hSSpos, hSS⟩
  · exact ⟨by reg_bound, by reg_bound⟩

theorem selectLocalSlotSeg_fits {w LSPS LS : Nat} (hreg : 40 <= 2 ^ w)
    (hLSPS : LSPS < 2 ^ w) (hLSpos : 0 < LS) (hLS : LS < 2 ^ w) :
    ∀ instr ∈ selectLocalSlotSeg LSPS LS, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [selectLocalSlotSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by reg_bound, by reg_bound, hLSPS⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, hLSpos, hLS⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound⟩

theorem selectDenseBaseSeg_fits {w WS : Nat} (hreg : 40 <= 2 ^ w)
    (hWS : WS < 2 ^ w) :
    ∀ instr ∈ selectDenseBaseSeg WS, Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [selectDenseBaseSeg, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, hWS⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩

/-! ## THE SELECT-CLOSE DISPATCH BLOCK FITS -/

/-- **ALL 405 INSTRUCTIONS OF `selectCloseBlock` FIT**, at any `w` meeting
the stated bounds. -/
theorem selectCloseBlock_fits {w : Nat}
    {A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST : Nat}
    {c OC SS LSPS LS DLS WS N2 : Nat}
    {LLen LWS LBPS SLen SWS SBPS : Nat}
    (hreg : 40 <= 2 ^ w) (hA : A + 405 < 2 ^ w)
    (hcpos : 0 < c) (hc : c < 2 ^ w)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hOC : OC < 2 ^ w)
    (hS1 : S1 < 2 ^ w) (hS2 : S2 < 2 ^ w) (hS3 : S3 < 2 ^ w)
    (hS4 : S4 < 2 ^ w)
    (hM1 : M1 < 2 ^ w) (hM2 : M2 < 2 ^ w) (hM3 : M3 < 2 ^ w)
    (hM4 : M4 < 2 ^ w)
    (hGL : GL + 4 < 2 ^ w) (hRL : RL < 2 ^ w)
    (hGS : GS + 4 < 2 ^ w) (hRS : RS < 2 ^ w)
    (hG : G + 4 < 2 ^ w) (hW : W < 2 ^ w) (hST : ST < 2 ^ w)
    (hSSpos : 0 < SS) (hSS : SS < 2 ^ w)
    (hLSPS : LSPS < 2 ^ w)
    (hLSpos : 0 < LS) (hLS : LS < 2 ^ w) (hDLS : DLS < 2 ^ w)
    (hWSpos : 0 < WS) (hWS : WS < 2 ^ w) (hN2 : N2 < 2 ^ w)
    (hLLen : LLen < 2 ^ w) (hLWSpos : 0 < LWS) (hLWS : LWS < 2 ^ w)
    (hLBPSpos : 0 < LBPS) (hLBPS : LBPS < 2 ^ w)
    (hSLen : SLen < 2 ^ w) (hSWSpos : 0 < SWS) (hSWS : SWS < 2 ^ w)
    (hSBPSpos : 0 < SBPS) (hSBPS : SBPS < 2 ^ w) :
    ∀ instr ∈ selectCloseBlock A S1 S2 S3 S4 M1 M2 M3 M4 GL RL GS RS G W ST
        c OC SS LSPS LS DLS WS N2 LLen LWS LBPS SLen SWS SBPS,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [selectCloseBlock, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with h | (rfl | rfl) | h | h | rfl | (rfl | rfl) | h | h |
    rfl | (rfl | rfl) | h | h | (rfl | rfl) | h | (rfl | rfl) | h |
    (rfl | rfl) | rfl
  · exact selectPrologue_fits hreg hc hOC instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact selectSuperSlotSeg_fits hreg hSSpos hSS instr h
  · exact entryReadBlock_fits (by omega) hS1 hS2 hS3 hS4
      (by reg_bound) (by reg_bound) (by reg_bound) (by reg_bound) instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact selectLocalSlotSeg_fits hreg hLSPS hLSpos hLS instr h
  · exact entryReadBlock_fits (by omega) hM1 hM2 hM3 hM4
      (by reg_bound) (by reg_bound) (by reg_bound) (by reg_bound) instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by reg_bound, by reg_bound⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact selectDenseBaseSeg_fits hreg hWS instr h
  · exact denseSelectLegBlock_fits hreg hW hG hST hcpos hpow hlin hWSpos hWS
      hN2 (by omega) instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact longLegBlock_fits hreg hGL hG hRL hLLen hcpos hLWSpos hLWS
      hLBPSpos hLBPS hpow hlin hSS hWS (by omega) instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact sparseLegBlock_fits hreg hGS hG hRS hSLen hcpos hSWSpos hSWS
      hSBPSpos hSBPS hpow hlin hDLS hWS (by omega) instr h
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by omega⟩
  · exact ⟨by reg_bound, by omega⟩

end E1SelectCloseWidth
end WordRAM
end RMQ

import RMQ.Core.WordRAM.Construction.Builder.Interior

/-! # PRE-1 builder: the access half

Program text only (inside the builder firewall). One scan of the BP cells
records the position of every close (`POS`, with the clamp `POS[n] = 2n`) and
the running close count at every word boundary (`RW`). Long-super flags,
effective sparse-exception flags and their prefix counts are computed from
`POS` by constant-size arithmetic per slot, and the 18 access sources are
emitted in payload order: the two final rank tables, the super and local entry
fields, the long-flag rank tables, the long flags, the long relative offsets,
the sparse-flag rank tables, the sparse flags and the sparse relative offsets.

The registers of this phase (159-199) are declared here, after the shared
convention of `Builder/Registers.lean` (0-158).
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-! ## Phase registers: access half -/

/-- Base of the close-position array (`n + 1` cells). -/
abbrev rPOSB : Operand := 159
/-- Base of the word-boundary rank array (`2n / ws + 1` cells). -/
abbrev rRWB : Operand := 160
/-- Base of the long-flag array. -/
abbrev rLFB : Operand := 161
/-- Base of the long-flag prefix-count array. -/
abbrev rLFCB : Operand := 162
/-- Base of the sparse-exception flag array. -/
abbrev rSFB : Operand := 163
/-- Base of the sparse-exception prefix-count array. -/
abbrev rSFCB : Operand := 164
/-- Scan position. -/
abbrev rP : Operand := 165
/-- Scan guard. -/
abbrev rPGO : Operand := 166
/-- Scan count `2n + 1`. -/
abbrev rM2P1 : Operand := 167
/-- Running close count. -/
abbrev rCNT : Operand := 168
/-- Access scratch. -/
abbrev rA1 : Operand := 169
/-- Access scratch. -/
abbrev rA2 : Operand := 170
/-- Access scratch. -/
abbrev rA3 : Operand := 171
/-- Access scratch. -/
abbrev rA4 : Operand := 172
/-- Super index. -/
abbrev rK : Operand := 173
/-- Super-loop guard. -/
abbrev rKGO : Operand := 174
/-- Local index. -/
abbrev rG : Operand := 175
/-- Local-loop guard. -/
abbrev rGGO : Operand := 176
/-- Running long-flag count. -/
abbrev rLCNT : Operand := 177
/-- Running sparse-exception count. -/
abbrev rSCNT : Operand := 178
/-- Base occurrence. -/
abbrev rBOCC : Operand := 179
/-- End occurrence. -/
abbrev rEOCC : Operand := 180
/-- Base position. -/
abbrev rBPOS : Operand := 181
/-- End position. -/
abbrev rEPOS : Operand := 182
/-- Span. -/
abbrev rSPANA : Operand := 183
/-- Flag value. -/
abbrev rFLAG : Operand := 184
/-- Super slot of a local slot. -/
abbrev rSSL : Operand := 185
/-- Super end occurrence. -/
abbrev rSEND : Operand := 186
/-- Liveness of a local entry. -/
abbrev rLIVE : Operand := 187
/-- Access scratch. -/
abbrev rA5 : Operand := 188
/-- Access scratch. -/
abbrev rA6 : Operand := 189

/-! ## Helpers -/

/-- `dst := POS[min occ n]`, the position of occurrence `occ` with the clamp
`2n` beyond the last close (register 1 holds `n`). -/
def posActs (dst occ : Operand) : List Action :=
  minActs rA5 occ rN ++ [.arithmetic .add rADDR rPOSB rA5, .load dst rADDR]

/-- `dst := a ∸ b` as `max a b - b`. -/
def monusActs (dst a b : Operand) : List Action :=
  maxActs rA6 a b ++ [.arithmetic .sub dst rA6 b]

/-! ## The occurrence pass -/

/-- One scan position: record the close count at a word boundary, then read
the cell and, for a close, record its position and count it. -/
def posStepBlock : Block :=
  .seq (acts [.arithmetic .mod rA1 rP rWS])
  (.seq (.ifZero rA1
      (acts [.arithmetic .div rA2 rP rWS, .arithmetic .add rADDR rRWB rA2, .store rADDR rCNT])
      .skip)
  (.seq (acts [.comparison .lt rA1 rP rM2])
    (.ifZero rA1 .skip
      (.seq (acts [.arithmetic .add rADDR rBPB rP, .load rCELL rADDR])
        (.ifZero rCELL
          (acts [.arithmetic .add rADDR rPOSB rCNT, .store rADDR rP,
            .arithmetic .add rCNT rCNT rONE])
          .skip)))))

/-- The occurrence pass over positions `0 .. 2n`, then `POS[n] := 2n`. -/
def posPassBlock : Block :=
  .seq (acts [.constant rCNT 0, .arithmetic .add rM2P1 rM2 rONE])
  (.seq (forSlots rP rPGO rM2P1 posStepBlock)
    (acts [.arithmetic .add rADDR rPOSB rCNT, .store rADDR rM2]))

/-! ## Flags and prefix counts -/

/-- Long flag of super `k`: `[superLongSpan < POS[end - 1] + 1 - POS[k * S]]`
with `end = min (k * S + S) n`; stores the flag and the prefix count. -/
def longFlagBlock : Block :=
  acts ([.arithmetic .mul rBOCC rK rSS, .arithmetic .add rA1 rBOCC rSS] ++
    minActs rEOCC rA1 rN ++
    [.arithmetic .sub rA1 rEOCC rONE] ++ posActs rEPOS rA1 ++ posActs rBPOS rBOCC ++
    [.arithmetic .add rEPOS rEPOS rONE] ++ monusActs rSPANA rEPOS rBPOS ++
    [.comparison .lt rFLAG rLSPAN rSPANA,
      .arithmetic .add rADDR rLFB rK, .store rADDR rFLAG,
      .arithmetic .add rADDR rLFCB rK, .store rADDR rLCNT,
      .arithmetic .add rLCNT rLCNT rFLAG])

/-- All long flags, then the final prefix count. -/
def longFlagsBlock : Block :=
  .seq (acts [.constant rLCNT 0])
  (.seq (forSlots rK rKGO rSUP longFlagBlock)
    (acts [.arithmetic .add rADDR rLFCB rSUP, .store rADDR rLCNT]))

/-- Sparse-exception flag of local slot `g`: its super is short and the span of
its (super-clamped) block exceeds one word; stores the flag and prefix count. -/
def sparseFlagBlock : Block :=
  acts ([.arithmetic .div rSSL rG rLPS, .arithmetic .mod rA1 rG rLPS,
    .arithmetic .mul rA1 rA1 rLSTR, .arithmetic .mul rBOCC rSSL rSS,
    .arithmetic .add rA2 rBOCC rSS] ++ minActs rSEND rA2 rN ++
    [.arithmetic .add rBOCC rBOCC rA1, .arithmetic .add rA2 rBOCC rLSTR] ++
    minActs rEOCC rA2 rSEND ++
    monusActs rA1 rEOCC rONE ++ posActs rEPOS rA1 ++ posActs rBPOS rBOCC ++
    [.arithmetic .add rEPOS rEPOS rONE] ++ monusActs rSPANA rEPOS rBPOS ++
    [.comparison .lt rA3 rWS rSPANA,
      .arithmetic .add rADDR rLFB rSSL, .load rA4 rADDR,
      .arithmetic .sub rA4 rONE rA4, .arithmetic .mul rFLAG rA3 rA4,
      .arithmetic .add rADDR rSFB rG, .store rADDR rFLAG,
      .arithmetic .add rADDR rSFCB rG, .store rADDR rSCNT,
      .arithmetic .add rSCNT rSCNT rFLAG])

/-- All sparse-exception flags, then the final prefix count. -/
def sparseFlagsBlock : Block :=
  .seq (acts [.constant rSCNT 0])
  (.seq (forSlots rG rGGO rLOC sparseFlagBlock)
    (acts [.arithmetic .add rADDR rSFCB rLOC, .store rADDR rSCNT]))

/-! ## Table entries -/

/-- Final rank super entry `RW[slot * ws]`. -/
def rankSuperEntryBlock : Block :=
  acts [.arithmetic .mul rA1 rSLOT rWS, .arithmetic .add rADDR rRWB rA1, .load rENT rADDR]

/-- Final rank block entry `RW[slot] - RW[(slot / ws) * ws]`. -/
def rankBlockEntryBlock : Block :=
  acts [.arithmetic .add rADDR rRWB rSLOT, .load rENT rADDR,
    .arithmetic .div rA1 rSLOT rWS, .arithmetic .mul rA1 rA1 rWS,
    .arithmetic .add rADDR rRWB rA1, .load rA2 rADDR, .arithmetic .sub rENT rENT rA2]

/-- Super field 1: base occurrence `slot * S`. -/
def superOccEntryBlock : Block :=
  acts [.arithmetic .mul rENT rSLOT rSS]

/-- Super field 2: base word index `POS[slot * S] / ws`. -/
def superWordEntryBlock : Block :=
  acts ([.arithmetic .mul rBOCC rSLOT rSS] ++ posActs rBPOS rBOCC ++
    [.arithmetic .div rENT rBPOS rWS])

/-- Super field 3: rank-before flag `LF[slot]`. -/
def superFlagEntryBlock : Block :=
  acts [.arithmetic .add rADDR rLFB rSLOT, .load rENT rADDR]

/-- Super field 4: first offset `POS[slot * S] % ws`. -/
def superOffsetEntryBlock : Block :=
  acts ([.arithmetic .mul rBOCC rSLOT rSS] ++ posActs rBPOS rBOCC ++
    [.arithmetic .mod rENT rBPOS rWS])

/-- Local-slot decoding shared by the four local fields: super slot, local
offset `(g % LPS) * ls`, base occurrence, liveness `[LF[super] = 0] * [base < n]`. -/
def localDecodeActs : List Action :=
  [.arithmetic .div rSSL rSLOT rLPS, .arithmetic .mod rA1 rSLOT rLPS,
    .arithmetic .mul rA1 rA1 rLSTR, .arithmetic .mul rA2 rSSL rSS,
    .arithmetic .add rBOCC rA2 rA1,
    .arithmetic .add rADDR rLFB rSSL, .load rA3 rADDR, .arithmetic .sub rA3 rONE rA3,
    .comparison .lt rA4 rBOCC rN, .arithmetic .mul rLIVE rA3 rA4]

/-- Local field 1: `live * (g % LPS) * ls`. -/
def localOccEntryBlock : Block :=
  acts (localDecodeActs ++ [.arithmetic .mul rENT rLIVE rA1])

/-- Local field 2: `live * (POS[base] / ws - POS[super base] / ws)`. -/
def localWordEntryBlock : Block :=
  acts (localDecodeActs ++ posActs rBPOS rBOCC ++ posActs rEPOS rA2 ++
    [.arithmetic .div rBPOS rBPOS rWS, .arithmetic .div rEPOS rEPOS rWS,
      .arithmetic .sub rENT rBPOS rEPOS, .arithmetic .mul rENT rLIVE rENT])

/-- Local field 3: `live * SF[g]`. -/
def localFlagEntryBlock : Block :=
  acts (localDecodeActs ++ [.arithmetic .add rADDR rSFB rSLOT, .load rENT rADDR,
    .arithmetic .mul rENT rLIVE rENT])

/-- Local field 4: `live * (POS[base] % ws)`. -/
def localOffsetEntryBlock : Block :=
  acts (localDecodeActs ++ posActs rBPOS rBOCC ++
    [.arithmetic .mod rENT rBPOS rWS, .arithmetic .mul rENT rLIVE rENT])

/-- Flag rank super entry `C[slot * w]` for a prefix-count array at `base`. -/
def flagRankEntryBlock (base w : Operand) : Block :=
  acts [.arithmetic .mul rA1 rSLOT w, .arithmetic .add rADDR base rA1, .load rENT rADDR]

/-- The constant zero entry. -/
def zeroEntryBlock : Block :=
  acts [.constant rENT 0]

/-- A raw flag entry `F[slot]`. -/
def flagEntryBlock (base : Operand) : Block :=
  acts [.arithmetic .add rADDR base rSLOT, .load rENT rADDR]

/-- Relative offset entry: `POS[base + slot] - basePos` below the end occurrence, else 0. -/
def relativeOffsetEntryBlock : Block :=
  acts ([.arithmetic .add rA1 rBOCC rSLOT, .comparison .lt rA2 rA1 rEOCC] ++
    posActs rA3 rA1 ++ monusActs rA3 rA3 rBPOS ++ [.arithmetic .mul rENT rA2 rA3])

/-! ## Relative offset flatMaps -/

/-- Long super `k`: its `S` relative offsets at `ws` bits; nothing for a short super. -/
def longRelativeBodyBlock : Block :=
  .seq (acts [.arithmetic .add rADDR rLFB rK, .load rFLAG rADDR])
    (.ifZero rFLAG .skip
      (.seq (acts ([.arithmetic .mul rBOCC rK rSS, .arithmetic .add rA4 rBOCC rSS] ++
          minActs rEOCC rA4 rN ++ posActs rBPOS rBOCC))
        (emitTable rSS rWS relativeOffsetEntryBlock)))

/-- Sparse-exception local slot `g`: its `ls` relative offsets (bounded by the
super end) at the local field width; nothing otherwise. -/
def sparseRelativeBodyBlock : Block :=
  .seq (acts [.arithmetic .add rADDR rSFB rG, .load rFLAG rADDR])
    (.ifZero rFLAG .skip
      (.seq (acts ([.arithmetic .div rSSL rG rLPS, .arithmetic .mod rA1 rG rLPS,
          .arithmetic .mul rA1 rA1 rLSTR, .arithmetic .mul rBOCC rSSL rSS,
          .arithmetic .add rA4 rBOCC rSS] ++ minActs rEOCC rA4 rN ++
          [.arithmetic .add rBOCC rBOCC rA1] ++ posActs rBPOS rBOCC))
        (emitTable rLSTR rLW relativeOffsetEntryBlock)))

/-! ## The access half -/

/-- Occurrence pass, flags, then the 18 access sources in payload order. -/
def accessHalfBlock : Block :=
  .seq posPassBlock (.seq longFlagsBlock (.seq sparseFlagsBlock
  (.seq (emitTable rRSUP rWS rankSuperEntryBlock)
  (.seq (emitTable rRBLK rRBW rankBlockEntryBlock)
  (.seq (emitTable rSUP rWS superOccEntryBlock)
  (.seq (emitTable rSUP rWS superWordEntryBlock)
  (.seq (emitTable rSUP rWS superFlagEntryBlock)
  (.seq (emitTable rSUP rWS superOffsetEntryBlock)
  (.seq (emitTable rLOC rLW localOccEntryBlock)
  (.seq (emitTable rLOC rLW localWordEntryBlock)
  (.seq (emitTable rLOC rLW localFlagEntryBlock)
  (.seq (emitTable rLOC rLW localOffsetEntryBlock)
  (.seq (emitTable rLFR rLFW (flagRankEntryBlock rLFCB rLFW))
  (.seq (emitTable rLFR rLFW zeroEntryBlock)
  (.seq (emitTable rSUP rONE (flagEntryBlock rLFB))
  (.seq (forSlots rK rKGO rSUP longRelativeBodyBlock)
  (.seq (emitTable rSFR rSFW (flagRankEntryBlock rSFCB rSFW))
  (.seq (emitTable rSFR rSFW zeroEntryBlock)
  (.seq (emitTable rSP rONE (flagEntryBlock rSFB))
    (forSlots rG rGGO rLOC sparseRelativeBodyBlock))))))))))))))))))))

end Builder

end RMQ.SuccinctFinal.PackedConstruction

import RMQ.Core.WordRAM.Construction.Builder.Geometry

/-! # PRE-1 builder: interior close tables

Program text only (inside the builder firewall). Stage S2 holds the two
charged sparse-level tables, whose cell for slot `i` of a domain `d` packs the
span `2 ^ Nat.log2 i` and the level `Nat.log2 i` as `2 ^ Nat.log2 i + d *
Nat.log2 i`. Stage S4 appends the summary and sparse offset tables.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-- Entry block of a sparse-level table: `rENT := 2 ^ log2 slot + dom * log2 slot`. -/
def levelEntryBlock (dom : Operand) : Block :=
  .seq (log2Block rLL rSLOT)
    (acts [.arithmetic .shl rLP rONE rLL, .arithmetic .mul rLM dom rLL,
      .arithmetic .add rENT rLP rLM])

/-- The sparse-level table over `regs dom` slots at `regs wid` bits. -/
def levelTableBlock (dom wid : Operand) : Block :=
  emitTable dom wid (levelEntryBlock dom)

/-! ## Block statistics -/

/-- Branch-free `dst := max a b` over the scratch registers 26-28. -/
def maxActs (dst a b : Operand) : List Action :=
  [.comparison .lt rT1 a b, .arithmetic .sub rT2 rONE rT1, .arithmetic .mul rT3 rT1 b,
    .arithmetic .mul rT2 rT2 a, .arithmetic .add dst rT3 rT2]

/-- One sample of a block: fold the current excess into the running minimum,
maximum and leftmost argmin, then, except after the last sample, read the BP
cell at the current position and advance the excess and the position. -/
def sampleBodyBlock : Block :=
  .seq (acts (minActs rMN rMN rEX ++ maxActs rMX rMX rEX ++ [.comparison .lt rT4 rEX rBESTE]))
  (.seq (.ifZero rT4 .skip (acts [.move rBEST rPOS, .move rBESTE rEX]))
  (.seq (acts [.comparison .lt rT4 rOFF rBS2])
    (.ifZero rT4 .skip
      (acts [.arithmetic .add rADDR rBPB rPOS, .load rCELL rADDR,
        .arithmetic .add rEX rEX rCELL, .arithmetic .add rEX rEX rCELL,
        .arithmetic .sub rEX rEX rONE, .arithmetic .add rPOS rPOS rONE]))))

/-- One block: record the start excess, fold its `blockSize + 1` samples, store
the three statistics. -/
def blockBodyBlock : Block :=
  .seq (acts [.arithmetic .add rADDR rESB rBLK, .store rADDR rEX,
      .arithmetic .mul rPOS rBLK rBS2, .move rMN rM2, .constant rMX 0,
      .move rBEST rPOS, .move rBESTE rEX])
  (.seq (forSlots rOFF rOGO rBS1 sampleBodyBlock)
    (acts [.arithmetic .add rADDR rMINB rBLK, .store rADDR rMN,
      .arithmetic .add rADDR rMAXB rBLK, .store rADDR rMX,
      .arithmetic .add rADDR rARGB rBLK, .store rADDR rBEST]))

/-- The excess sweep over all blocks, then the start excess of the position
after the last block. -/
def blockStatsBlock : Block :=
  .seq (acts [.constant rEX 0, .arithmetic .add rBS1 rBS2 rONE])
  (.seq (forSlots rBLK rBGO rBLOCKS blockBodyBlock)
    (acts [.arithmetic .add rADDR rESB rBLOCKS, .store rADDR rEX]))

/-! ## The four summary tables -/

/-- Baseline entry `excess at the start of superblock slot`. -/
def baselineEntryBlock : Block :=
  acts [.arithmetic .mul rT4 rSLOT rBASE, .arithmetic .add rADDR rESB rT4, .load rENT rADDR]

/-- Relative entry `stat[slot] + span - excess at the start of the slot's superblock`. -/
def relativeEntryBlock (statBase : Operand) : Block :=
  acts [.arithmetic .div rT4 rSLOT rBASE, .arithmetic .mul rT4 rT4 rBASE,
    .arithmetic .add rADDR rESB rT4, .load rT5 rADDR,
    .arithmetic .add rADDR statBase rSLOT, .load rENT rADDR,
    .arithmetic .add rENT rENT rSPAN, .arithmetic .sub rENT rENT rT5]

/-- Argmin local offset entry `argPos[slot] - slot * blockSize`. -/
def argOffsetEntryBlock : Block :=
  acts [.arithmetic .add rADDR rARGB rSLOT, .load rENT rADDR,
    .arithmetic .mul rT4 rSLOT rBS2, .arithmetic .sub rENT rENT rT4]

/-- Baseline, minimum, maximum and argmin-offset tables in payload order. -/
def summaryTablesBlock : Block :=
  .seq (acts [.arithmetic .mul rSPAN rBASE rBS2])
  (.seq (emitTable rSSC rWS baselineEntryBlock)
  (.seq (emitTable rBLOCKS rRW (relativeEntryBlock rMINB))
  (.seq (emitTable rBLOCKS rRW (relativeEntryBlock rMAXB))
    (emitTable rBLOCKS rRW argOffsetEntryBlock))))

/-! ## Sparse memos -/

/-- Leftmost-better block selection `dst := if MIN[y] < MIN[x] then y else x`,
keyed by the block-minimum array. -/
def betterActs (dst x y : Operand) : List Action :=
  [.arithmetic .add rADDR rMINB x, .load rKX rADDR,
    .arithmetic .add rADDR rMINB y, .load rKY rADDR,
    .comparison .lt rT6 rKY rKX, .arithmetic .sub rT7 rONE rT6,
    .arithmetic .mul rT6 rT6 y, .arithmetic .mul rT7 rT7 x,
    .arithmetic .add dst rT6 rT7]

/-- One doubling step of a memo row: for index `i < regs count`, if
`(i + 2 * half) * scale <= blockCount`, row `current[i] := better(previous[i],
previous[i + half])`. -/
def memoCellBlock (scale : Operand) : Block :=
  .seq (acts [.arithmetic .add rT6 rMB rSPN, .arithmetic .add rT6 rT6 rSPN,
      .arithmetic .mul rT6 rT6 scale, .comparison .lt rT7 rBLOCKS rT6])
    (.ifZero rT7
      (acts ([.arithmetic .add rADDR rROWP rMB, .load rCX rADDR,
          .arithmetic .add rT6 rMB rSPN, .arithmetic .add rADDR rROWP rT6, .load rCY rADDR] ++
        betterActs rCX rCX rCY ++
        [.arithmetic .add rADDR rROWC rMB, .store rADDR rCX]))
      .skip)

/-- Memo levels `1 .. regs levels`: row `l + 1` from row `l` over `regs count` indices. -/
def memoLevelsBlock (base count scale levels : Operand) : Block :=
  .seq (acts [.arithmetic .sub rLVCNT levels rONE])
    (forSlots rLVL rLVGO rLVCNT
      (.seq (acts [.arithmetic .shl rSPN rONE rLVL, .arithmetic .mul rT6 rLVL count,
          .arithmetic .add rROWP base rT6, .arithmetic .add rROWC rROWP count])
        (forSlots rMB rMBGO count (memoCellBlock scale))))

/-- Local memo: `A[l][b] = bpRangeArgMinBlock b (2 ^ l)` for `b + 2 ^ l <= blockCount`. -/
def localMemoBlock : Block :=
  .seq (forSlots rMB rMBGO rBLOCKS (acts [.arithmetic .add rADDR rAMB rMB, .store rADDR rMB]))
    (memoLevelsBlock rAMB rBLOCKS rONE rOW)

/-- Level 0 of the global memo: the leftmost argmin block of every complete macro. -/
def macroScanBlock : Block :=
  .seq (acts [.arithmetic .add rT6 rMB rONE, .arithmetic .mul rT6 rT6 rMACRO,
      .comparison .lt rT7 rBLOCKS rT6])
    (.ifZero rT7
      (.seq (acts [.arithmetic .mul rMST rMB rMACRO, .move rCX rMST,
          .arithmetic .sub rMM1 rMACRO rONE])
        (.seq (forSlots rJS rJSGO rMM1
            (acts ([.arithmetic .add rCY rMST rJS, .arithmetic .add rCY rCY rONE] ++
              betterActs rCX rCX rCY)))
          (acts [.arithmetic .add rADDR rGMB rMB, .store rADDR rCX])))
      .skip)

/-- Global memo: `G[l][m] = bpRangeArgMinBlock (m * macroSize) (2 ^ l * macroSize)`
for `(m + 2 ^ l) * macroSize <= blockCount`. -/
def globalMemoBlock : Block :=
  .seq (forSlots rMB rMBGO rMACROS macroScanBlock)
    (memoLevelsBlock rGMB rMACROS rMACRO rGLC)

/-! ## Sparse tables -/

/-- Local sparse entry: offset of the memoized argmin block from its macro start,
or 0 when the span leaves the macro or the block range. -/
def localEntryBlock : Block :=
  .seq (acts [.arithmetic .mul rT6 rOW rMACRO,
      .arithmetic .div rMI rSLOT rT6, .arithmetic .mod rT7 rSLOT rT6,
      .arithmetic .div rLV rT7 rMACRO, .arithmetic .mod rLS rT7 rMACRO,
      .arithmetic .shl rSPN rONE rLV,
      .arithmetic .mul rMST rMI rMACRO, .arithmetic .add rSTB rMST rLS,
      .arithmetic .add rT6 rLS rSPN, .comparison .lt rT6 rMACRO rT6,
      .arithmetic .add rT7 rSTB rSPN, .comparison .lt rT7 rBLOCKS rT7,
      .arithmetic .add rT6 rT6 rT7, .constant rENT 0])
    (.ifZero rT6
      (acts [.arithmetic .mul rT7 rLV rBLOCKS, .arithmetic .add rT7 rT7 rSTB,
        .arithmetic .add rADDR rAMB rT7, .load rENT rADDR, .arithmetic .sub rENT rENT rMST])
      .skip)

/-- Global sparse entry: the memoized argmin block, or 0 outside the two guards. -/
def globalEntryBlock : Block :=
  .seq (acts [.arithmetic .div rLV rSLOT rMACROS, .arithmetic .mod rMI rSLOT rMACROS,
      .arithmetic .shl rSPN rONE rLV,
      .arithmetic .add rT6 rMI rSPN, .comparison .lt rT6 rMACROS rT6,
      .arithmetic .mul rSTB rMI rMACRO, .arithmetic .mul rT7 rSPN rMACRO,
      .arithmetic .add rT7 rSTB rT7, .comparison .lt rT7 rBLOCKS rT7,
      .arithmetic .add rT6 rT6 rT7, .constant rENT 0])
    (.ifZero rT6
      (acts [.arithmetic .mul rT7 rLV rMACROS, .arithmetic .add rT7 rT7 rMI,
        .arithmetic .add rADDR rGMB rT7, .load rENT rADDR])
      .skip)

/-- The interior close after the BP code: statistics, memos, then the eight
tables in payload order. -/
def interiorCloseBlock : Block :=
  .seq blockStatsBlock (.seq localMemoBlock (.seq globalMemoBlock
    (.seq summaryTablesBlock
    (.seq (emitTable rLSCNT rOW localEntryBlock)
    (.seq (emitTable rGSCNT rBAW globalEntryBlock)
    (.seq (levelTableBlock rLDOM rLWID) (levelTableBlock rGDOM rGWID)))))))

end Builder

end RMQ.SuccinctFinal.PackedConstruction

import RMQ.Core.WordRAM.Construction.Loop

/-! # PRE-1 builder: the fixed register map

Program text only (inside the builder firewall). Every register the builder
source uses is one of these literal operands. The leaf interface (registers 2
to 8 and key registers 0 and 1) and the halt register 3 are frozen by contract
clause V3-3. Registers 0 and 1 are never written after the header load: 0 is
the zero register read by the header instruction, 1 holds the input length.

Bands: 0-8 header, constants and leaf interface; 9-19 emission helpers;
20-29 arithmetic helpers; 30-99 the size-only geometry bank; 100-199 phase
registers (array bases, cursors, loop state).
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

/-! ## Header, constants and the frozen leaf interface -/

/-- Always 0 (never written). -/
abbrev rZERO : Operand := 0
/-- The input length, loaded by the header instruction. -/
abbrev rN : Operand := 1
/-- The constant 1. -/
abbrev rONE : Operand := 2
/-- The halt value `outBase`. -/
abbrev rOUT : Operand := 3
/-- Leaf interface: index `i`. -/
abbrev rLEAF_I : Operand := 4
/-- Leaf interface: index `j`. -/
abbrev rLEAF_J : Operand := 5
/-- Leaf interface: result `[xs[i] < xs[j]]`. -/
abbrev rLEAF_RES : Operand := 6
/-- Word-leaf scratch. -/
abbrev rLEAF_T1 : Operand := 7
/-- Word-leaf scratch. -/
abbrev rLEAF_T2 : Operand := 8

/-! ## Emission helpers -/

/-- The constant 2. -/
abbrev rTWO : Operand := 9
/-- Address returned by the last emission `reserve`. -/
abbrev rCUR : Operand := 10
/-- The bit being emitted. -/
abbrev rBIT : Operand := 11
/-- Remaining bits of the word being emitted. -/
abbrev rECNT : Operand := 12
/-- Shifted copy of the word being emitted. -/
abbrev rEVAL : Operand := 13
/-- Table slot index. -/
abbrev rSLOT : Operand := 14
/-- Table loop guard `[slot < count]`. -/
abbrev rGO : Operand := 15
/-- Table entry value computed by an entry block. -/
abbrev rENT : Operand := 16

/-! ## Arithmetic helpers -/

/-- `log2` loop: shifted value. -/
abbrev rLX : Operand := 20
/-- `log2` loop guard `[1 < x]`. -/
abbrev rLC : Operand := 21
/-- Level-cell scratch: `log2 slot`. -/
abbrev rLL : Operand := 22
/-- Level-cell scratch: `2 ^ log2 slot`. -/
abbrev rLP : Operand := 23
/-- Level-cell scratch: `domain * log2 slot`. -/
abbrev rLM : Operand := 24
/-- Generic scratch. -/
abbrev rT0 : Operand := 25
/-- Geometry scratch. -/
abbrev rT1 : Operand := 26
/-- Geometry scratch. -/
abbrev rT2 : Operand := 27
/-- Geometry scratch. -/
abbrev rT3 : Operand := 28

/-! ## Size-only geometry bank (interior layout subset) -/

/-- `base = log2 n + 1`. -/
abbrev rBASE : Operand := 30
/-- `macroSize = base * base`. -/
abbrev rMACRO : Operand := 31
/-- `blockCount = n / base`. -/
abbrev rBLOCKS : Operand := 32
/-- `macroSampleCount = blockCount / macroSize + 1`. -/
abbrev rMACROS : Operand := 33
/-- Local level domain `macroSize + 2`. -/
abbrev rLDOM : Operand := 34
/-- Global level domain `macroSampleCount + 2`. -/
abbrev rGDOM : Operand := 35
/-- Local level width `log2 (ldom * (log2 ldom + 1)) + 1`. -/
abbrev rLWID : Operand := 36
/-- Global level width. -/
abbrev rGWID : Operand := 37

/-! ## Size-only geometry bank (access half) -/

/-- `m = 2 * n`, the BP length. -/
abbrev rM2 : Operand := 38
/-- `ws = machineWordBits m`. -/
abbrev rWS : Operand := 39
/-- Select super stride `ws * ws`. -/
abbrev rSS : Operand := 40
/-- `ell = log2 ws + 1`. -/
abbrev rEL : Operand := 41
/-- Select local stride `max 1 (ws / (ell * ell))`. -/
abbrev rLSTR : Operand := 42
/-- Local slots per super `(S + ls - 1) / ls`. -/
abbrev rLPS : Operand := 43
/-- Super long span `S * ws * ell`. -/
abbrev rLSPAN : Operand := 44
/-- Super slot count `(n + S - 1) / S`. -/
abbrev rSUP : Operand := 45
/-- Local slot count `sup * lps`. -/
abbrev rLOC : Operand := 46
/-- Effective sparse slot count `min loc n`. -/
abbrev rSP : Operand := 47
/-- Rank block width `machineWordBits S`. -/
abbrev rRBW : Operand := 48
/-- Local field width `machineWordBits (min m LS)`. -/
abbrev rLW : Operand := 49
/-- Long-flag word size `machineWordBits sup`. -/
abbrev rLFW : Operand := 50
/-- Sparse-flag word size `machineWordBits sp`. -/
abbrev rSFW : Operand := 51
/-- Final rank super slots `m / ws / ws + 1`. -/
abbrev rRSUP : Operand := 52
/-- Final rank block slots `m / ws + 1`. -/
abbrev rRBLK : Operand := 53
/-- Long-flag rank slots `sup / lfw + 1`. -/
abbrev rLFR : Operand := 54
/-- Sparse-flag rank slots `sp / sfw + 1`. -/
abbrev rSFR : Operand := 55

/-! ## Size-only geometry bank (interior layout remainder) -/

/-- Block size `2 * base`. -/
abbrev rBS2 : Operand := 56
/-- Super sample count `blockCount / base + 1`. -/
abbrev rSSC : Operand := 57
/-- Offset width (= level count) `machineWordBits macroSize`. -/
abbrev rOW : Operand := 58
/-- Global level count `machineWordBits macroSampleCount`. -/
abbrev rGLC : Operand := 59
/-- Block address width `machineWordBits blockCount`. -/
abbrev rBAW : Operand := 60
/-- Relative width `2 * (log2 base + 1) + 3`. -/
abbrev rRW : Operand := 61
/-- Local sparse entry count `macroSampleCount * (offsetWidth * macroSize)`. -/
abbrev rLSCNT : Operand := 62
/-- Global sparse entry count `globalLevelCount * macroSampleCount`. -/
abbrev rGSCNT : Operand := 63

/-! ## Size-only geometry bank (microtables) -/

/-- Chunk bits `c = log2 m / 8 + 1`. -/
abbrev rCB : Operand := 64
/-- Fringe rows `2 ^ c * ((c + 1) * (c + 1))`. -/
abbrev rFROWS : Operand := 65
/-- Fringe entry width. -/
abbrev rFWID : Operand := 66
/-- Select-chunk rows `2 ^ c * (c + 1)`. -/
abbrev rSROWS : Operand := 67
/-- Select-chunk entry width `log2 (c + 1) + 1`. -/
abbrev rSWID : Operand := 68

/-! ## Size-only geometry bank (budget, cell and word widths) -/

/-- Raw interior payload bits. -/
abbrev rIBITS : Operand := 69
/-- Fringe table bits. -/
abbrev rFBITS : Operand := 70
/-- Select-chunk table bits. -/
abbrev rCBITS : Operand := 71
/-- `q = (m / ws) * (ell * (ell * ell))`. -/
abbrev rQ : Operand := 72
/-- `r = m / ell`. -/
abbrev rR : Operand := 73
/-- Access overhead budget. -/
abbrev rAO : Operand := 74
/-- Old cell width `packedReviewerCellWidth n`. -/
abbrev rOLDW : Operand := 75
/-- Word width `32 + 8 * oldW`. -/
abbrev rWW : Operand := 76

/-! ## Phase registers: Cartesian stack pass and BP emission -/

/-- Base address of the stack array. -/
abbrev rSTK : Operand := 100
/-- Base address of the leftmost-descendant array. -/
abbrev rLDB : Operand := 101
/-- Base address of the open-count array. -/
abbrev rCNTB : Operand := 102
/-- Stack height. -/
abbrev rSTKH : Operand := 103
/-- Stack-pass index `i`. -/
abbrev rI : Operand := 104
/-- Stack-pass guard `[i < n]`. -/
abbrev rIGO : Operand := 105
/-- Index of the last popped stack entry. -/
abbrev rLAST : Operand := 106
/-- Popped flag. -/
abbrev rPOP : Operand := 107
/-- Array address scratch. -/
abbrev rADDR : Operand := 108
/-- Index at the top of the stack. -/
abbrev rTOP : Operand := 109
/-- Pop guard `[sp ≠ 0 ∧ xs[i] < xs[top]]`. -/
abbrev rWG : Operand := 110
/-- Leftmost-descendant scratch. -/
abbrev rTMP : Operand := 111
/-- Open-count scratch. -/
abbrev rCC : Operand := 112
/-- BP-emission index `j`. -/
abbrev rJ : Operand := 113
/-- BP-emission guard `[j < n]`. -/
abbrev rJGO : Operand := 114

/-! ## Phase registers: interior close (block statistics and summary tables) -/

/-- Base of the block-start excess array (`blockCount + 1` cells). -/
abbrev rESB : Operand := 115
/-- Base of the block minimum-excess array. -/
abbrev rMINB : Operand := 116
/-- Base of the block maximum-excess array. -/
abbrev rMAXB : Operand := 117
/-- Base of the block argmin-position array. -/
abbrev rARGB : Operand := 118
/-- Address of the first BP cell. -/
abbrev rBPB : Operand := 119
/-- Running prefix excess. -/
abbrev rEX : Operand := 120
/-- Block index. -/
abbrev rBLK : Operand := 121
/-- Block-loop guard. -/
abbrev rBGO : Operand := 122
/-- Sample offset inside a block. -/
abbrev rOFF : Operand := 123
/-- Sample-loop guard. -/
abbrev rOGO : Operand := 124
/-- Running minimum excess. -/
abbrev rMN : Operand := 125
/-- Running maximum excess. -/
abbrev rMX : Operand := 126
/-- Best (leftmost minimum) sample position. -/
abbrev rBEST : Operand := 127
/-- Excess at the best sample position. -/
abbrev rBESTE : Operand := 128
/-- Current sample position. -/
abbrev rPOS : Operand := 129
/-- BP cell value. -/
abbrev rCELL : Operand := 130
/-- Interior scratch. -/
abbrev rT4 : Operand := 131
/-- Interior scratch. -/
abbrev rT5 : Operand := 132
/-- Superblock span `blocksPerSuper * blockSize`. -/
abbrev rSPAN : Operand := 133
/-- Samples per block `blockSize + 1`. -/
abbrev rBS1 : Operand := 134

/-! ## Phase registers: interior close (sparse memos and sparse tables) -/

/-- Base of the local memo (`levelCount * blockCount` cells). -/
abbrev rAMB : Operand := 135
/-- Base of the global memo (`globalLevelCount * macroSampleCount` cells). -/
abbrev rGMB : Operand := 136
/-- Memo level index (the filled level is one more). -/
abbrev rLVL : Operand := 137
/-- Memo level-loop guard. -/
abbrev rLVGO : Operand := 138
/-- Memo block or macro index. -/
abbrev rMB : Operand := 139
/-- Memo index-loop guard. -/
abbrev rMBGO : Operand := 140
/-- Half span `2 ^ level`. -/
abbrev rSPN : Operand := 141
/-- Left candidate and running best. -/
abbrev rCX : Operand := 142
/-- Right candidate. -/
abbrev rCY : Operand := 143
/-- Key of the left candidate. -/
abbrev rKX : Operand := 144
/-- Key of the right candidate. -/
abbrev rKY : Operand := 145
/-- Sparse scratch. -/
abbrev rT6 : Operand := 146
/-- Sparse scratch. -/
abbrev rT7 : Operand := 147
/-- Number of memo levels above level 0. -/
abbrev rLVCNT : Operand := 148
/-- Address of the previous memo row. -/
abbrev rROWP : Operand := 149
/-- Address of the current memo row. -/
abbrev rROWC : Operand := 150
/-- Macro start block. -/
abbrev rMST : Operand := 151
/-- `macroSize - 1`. -/
abbrev rMM1 : Operand := 152
/-- Macro scan index. -/
abbrev rJS : Operand := 153
/-- Macro scan guard. -/
abbrev rJSGO : Operand := 154
/-- Table entry: macro index. -/
abbrev rMI : Operand := 155
/-- Table entry: level. -/
abbrev rLV : Operand := 156
/-- Table entry: local start. -/
abbrev rLS : Operand := 157
/-- Table entry: start block. -/
abbrev rSTB : Operand := 158

end Builder

end RMQ.SuccinctFinal.PackedConstruction

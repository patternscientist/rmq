import RMQ.Core.WordRAM.Construction.Builder.Finish

/-! # PRE-1 builder: arrays, metadata and the dense output

Program text only (inside the builder firewall). `arraysBlock` reserves the
access arrays (registers 159-164) and the interior statistics and memo arrays
(115-118, 135, 136) in the layout order of the buffer stage. After the bit
buffer, `metaChain 108` computes the metadata bank (registers 229-336): step
`i` stores one value into register `229 + i` from the geometry bank
(registers 30-76), the long count (177), the sparse-exception count (178) and
metadata registers below `229 + i`, and writes no other register.
`metaEmitBlock` reserves the first output cell into register 3 (the halt value
`outBase`) and stores the 174 metadata words in order, each a bank, count or
metadata register. `repackBlock` appends one word per `W` buffer cells: for word
`i` it reads the cells `buf + (i + 1) W - 1` down to `buf + i W` into a Horner
accumulator and emits it.

The registers of this phase (198, 229-342) are declared here.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

namespace Builder

open Structured

/-! ## Phase registers: arrays and output -/

/-- Array size scratch for the two memo arrays. -/
abbrev rASZ : Operand := 198
/-- The dense word count (metadata register 277). -/
abbrev rDCNT : Operand := 277
/-- Output word index. -/
abbrev rRI : Operand := 337
/-- Output loop guard `[i < dense count]`. -/
abbrev rRIGO : Operand := 338
/-- Buffer read cursor. -/
abbrev rRA : Operand := 339
/-- Horner accumulator. -/
abbrev rACC : Operand := 340
/-- Remaining cells of the current word. -/
abbrev rRJ : Operand := 341
/-- The cell just read. -/
abbrev rRB : Operand := 342

/-! ## Arrays -/

/-- The access arrays (positions, running ranks, long and sparse flags with
their counts) and the interior arrays (excess, minimum, maximum and argmin per
block, then the local and global memo arrays), each with one extra zero cell. -/
def arraysBlock : Block :=
  .seq (reserveArray rPOSB rN) (.seq (reserveArray rRWB rRBLK)
    (.seq (reserveArray rLFB rSUP) (.seq (reserveArray rLFCB rSUP)
    (.seq (reserveArray rSFB rLOC) (.seq (reserveArray rSFCB rLOC)
    (.seq (reserveArray rESB rBLOCKS) (.seq (reserveArray rMINB rBLOCKS)
    (.seq (reserveArray rMAXB rBLOCKS) (.seq (reserveArray rARGB rBLOCKS)
    (.seq (acts [.arithmetic .mul rASZ rOW rBLOCKS]) (.seq (reserveArray rAMB rASZ)
    (.seq (acts [.arithmetic .mul rASZ rGLC rMACROS]) (reserveArray rGMB rASZ)))))))))))))

/-! ## Metadata bank -/

/-- Metadata bank step `i`: it stores register `229 + i` and writes no other
register. -/
def metaStepBlock : Nat → Block
  | 0 => acts [.arithmetic .mul 229 178 42]
  | 1 => acts [.arithmetic .mul 230 52 39]
  | 2 => acts [.arithmetic .mul 231 53 48]
  | 3 => acts [.arithmetic .mul 232 45 39]
  | 4 => acts [.arithmetic .mul 233 46 49]
  | 5 => acts [.arithmetic .mul 234 54 50]
  | 6 => acts [.arithmetic .mul 235 177 40]
  | 7 => acts [.arithmetic .mul 236 235 39]
  | 8 => acts [.arithmetic .mul 237 55 51]
  | 9 => acts [.arithmetic .mul 238 229 49]
  | 10 => acts [.arithmetic .add 239 230 231]
  | 11 => acts [.arithmetic .add 240 239 232]
  | 12 => acts [.arithmetic .add 241 240 232]
  | 13 => acts [.arithmetic .add 242 241 232]
  | 14 => acts [.arithmetic .add 243 242 232]
  | 15 => acts [.arithmetic .add 244 243 233]
  | 16 => acts [.arithmetic .add 245 244 233]
  | 17 => acts [.arithmetic .add 246 245 233]
  | 18 => acts [.arithmetic .add 247 246 233]
  | 19 => acts [.arithmetic .add 248 247 234]
  | 20 => acts [.arithmetic .add 249 248 234]
  | 21 => acts [.arithmetic .add 250 249 45]
  | 22 => acts [.arithmetic .add 251 250 236]
  | 23 => acts [.arithmetic .add 252 251 237]
  | 24 => acts [.arithmetic .add 253 252 237]
  | 25 => acts [.arithmetic .add 254 253 47]
  | 26 => acts [.arithmetic .add 255 254 238]
  | 27 => acts [.arithmetic .add 256 75 38]
  | 28 => acts [.arithmetic .add 257 256 230]
  | 29 => acts [.arithmetic .add 258 256 239]
  | 30 => acts [.arithmetic .add 259 256 240]
  | 31 => acts [.arithmetic .add 260 256 241]
  | 32 => acts [.arithmetic .add 261 256 242]
  | 33 => acts [.arithmetic .add 262 256 243]
  | 34 => acts [.arithmetic .add 263 256 244]
  | 35 => acts [.arithmetic .add 264 256 245]
  | 36 => acts [.arithmetic .add 265 256 246]
  | 37 => acts [.arithmetic .add 266 256 247]
  | 38 => acts [.arithmetic .add 267 256 248]
  | 39 => acts [.arithmetic .add 268 256 249]
  | 40 => acts [.arithmetic .add 269 256 250]
  | 41 => acts [.arithmetic .add 270 256 251]
  | 42 => acts [.arithmetic .add 271 256 252]
  | 43 => acts [.arithmetic .add 272 256 253]
  | 44 => acts [.arithmetic .add 273 256 254]
  | 45 => acts [.arithmetic .add 274 38 255, .arithmetic .add 274 274 69,
      .arithmetic .add 274 274 70, .arithmetic .add 274 274 71]
  | 46 => acts [.arithmetic .add 275 274 75, .arithmetic .sub 275 275 2,
      .arithmetic .div 275 275 75, .arithmetic .add 275 275 2]
  | 47 => acts [.arithmetic .mul 276 275 75]
  | 48 => acts [.arithmetic .add 277 276 76, .arithmetic .sub 277 277 2,
      .arithmetic .div 277 277 76]
  | 49 => acts [.constant 278 174, .arithmetic .add 278 278 277]
  | 50 => acts [.arithmetic .add 279 38 255]
  | 51 => acts [.arithmetic .add 280 279 69]
  | 52 => acts [.arithmetic .add 281 280 70]
  | 53 => acts [.arithmetic .add 282 75 280]
  | 54 => acts [.arithmetic .add 283 75 281]
  | 55 => acts [.arithmetic .add 284 75 279]
  | 56 => acts [.arithmetic .div 285 38 39]
  | 57 => acts [.arithmetic .mod 286 38 39, .comparison .lt 286 0 286, .arithmetic .add 286 285 286]
  | 58 => acts [.arithmetic .add 287 286 38, .arithmetic .add 287 287 2]
  | 59 => acts [.arithmetic .div 288 45 50]
  | 60 => acts [.arithmetic .mod 289 45 50, .comparison .lt 289 0 289,
      .arithmetic .add 289 288 289, .arithmetic .add 289 289 45, .arithmetic .add 289 289 2]
  | 61 => acts [.arithmetic .div 290 47 51]
  | 62 => acts [.arithmetic .mod 291 47 51, .comparison .lt 291 0 291,
      .arithmetic .add 291 290 291, .arithmetic .add 291 291 47, .arithmetic .add 291 291 2]
  | 63 => acts [.arithmetic .mul 292 65 66]
  | 64 => acts [.arithmetic .mul 293 67 68]
  | 65 => acts [.arithmetic .div 294 39 39]
  | 66 => acts [.arithmetic .mod 295 39 39, .comparison .lt 295 0 295, .arithmetic .add 295 294 295]
  | 67 => acts [.arithmetic .div 296 61 39]
  | 68 => acts [.arithmetic .mod 297 61 39, .comparison .lt 297 0 297, .arithmetic .add 297 296 297]
  | 69 => acts [.arithmetic .div 298 58 39]
  | 70 => acts [.arithmetic .mod 299 58 39, .comparison .lt 299 0 299, .arithmetic .add 299 298 299]
  | 71 => acts [.arithmetic .div 300 60 39]
  | 72 => acts [.arithmetic .mod 301 60 39, .comparison .lt 301 0 301, .arithmetic .add 301 300 301]
  | 73 => acts [.arithmetic .div 302 36 39]
  | 74 => acts [.arithmetic .mod 303 36 39, .comparison .lt 303 0 303, .arithmetic .add 303 302 303]
  | 75 => acts [.arithmetic .div 304 37 39]
  | 76 => acts [.arithmetic .mod 305 37 39, .comparison .lt 305 0 305, .arithmetic .add 305 304 305]
  | 77 => acts [.arithmetic .add 306 39 39, .arithmetic .sub 306 306 2, .arithmetic .div 306 306 39]
  | 78 => acts [.arithmetic .add 307 61 39, .arithmetic .sub 307 307 2, .arithmetic .div 307 307 39]
  | 79 => acts [.arithmetic .add 308 58 39, .arithmetic .sub 308 308 2, .arithmetic .div 308 308 39]
  | 80 => acts [.arithmetic .add 309 60 39, .arithmetic .sub 309 309 2, .arithmetic .div 309 309 39]
  | 81 => acts [.arithmetic .add 310 36 39, .arithmetic .sub 310 310 2, .arithmetic .div 310 310 39]
  | 82 => acts [.arithmetic .add 311 37 39, .arithmetic .sub 311 311 2, .arithmetic .div 311 311 39]
  | 83 => acts [.arithmetic .mul 312 57 295]
  | 84 => acts [.arithmetic .mul 313 32 297]
  | 85 => acts [.arithmetic .mul 314 62 299]
  | 86 => acts [.arithmetic .mul 315 63 301]
  | 87 => acts [.arithmetic .mul 316 34 303]
  | 88 => acts [.arithmetic .mul 317 35 305]
  | 89 => acts [.arithmetic .add 318 312 313]
  | 90 => acts [.arithmetic .add 319 318 313]
  | 91 => acts [.arithmetic .add 320 319 313]
  | 92 => acts [.arithmetic .add 321 320 314]
  | 93 => acts [.arithmetic .add 322 321 315]
  | 94 => acts [.arithmetic .add 323 322 316]
  | 95 => acts [.arithmetic .add 324 323 317]
  | 96 => acts [.arithmetic .mul 325 57 39]
  | 97 => acts [.arithmetic .mul 326 32 61]
  | 98 => acts [.arithmetic .mul 327 62 58]
  | 99 => acts [.arithmetic .mul 328 63 60]
  | 100 => acts [.arithmetic .mul 329 34 36]
  | 101 => acts [.arithmetic .add 330 284 325]
  | 102 => acts [.arithmetic .add 331 330 326]
  | 103 => acts [.arithmetic .add 332 331 326]
  | 104 => acts [.arithmetic .add 333 332 326]
  | 105 => acts [.arithmetic .add 334 333 327]
  | 106 => acts [.arithmetic .add 335 334 328]
  | 107 => acts [.arithmetic .add 336 335 329]
  | _ => .skip

/-- The first `k` metadata bank steps in order. -/
def metaChain : Nat → Block
  | 0 => .skip
  | k + 1 => .seq (metaChain k) (metaStepBlock k)

/-! ## Output -/

/-- Emit the listed registers in order, one cell each. -/
def emitRegs : List Operand → Block
  | [] => .skip
  | r :: rest => .seq (emitBit r) (emitRegs rest)

/-- The registers of metadata words 1-173 in order (word 0 is the length, register 1). -/
def metaWordRegs : List Operand :=
  [75, 275, 276, 177, 229, 76, 278, 39, 40, 42, 43, 45, 47, 50, 51, 39, 56, 64, 30, 32, 57, 31, 33,
    58, 59, 61, 58, 60, 34, 35, 36, 37, 0, 312, 318, 319, 320, 321, 322, 323, 324, 75, 38, 39, 286,
    258, 232, 39, 45, 259, 232, 39, 45, 260, 232, 39, 45, 261, 232, 39, 45, 262, 233, 49, 46, 263,
    233, 49, 46, 264, 233, 49, 46, 265, 233, 49, 46, 266, 234, 50, 54, 267, 234, 50, 54, 268, 45,
    50, 289, 269, 236, 39, 235, 270, 237, 51, 55, 271, 237, 51, 55, 272, 47, 51, 291, 273, 238, 49,
    229, 256, 230, 39, 52, 257, 231, 48, 53, 75, 38, 39, 287, 0, 0, 0, 0, 282, 292, 66, 65, 283,
    293, 68, 67, 0, 312, 284, 39, 306, 312, 313, 330, 61, 307, 318, 313, 331, 61, 307, 319, 313,
    332, 61, 307, 320, 314, 333, 58, 308, 321, 315, 334, 60, 309, 322, 316, 335, 36, 310, 323, 317,
    336, 37, 311]

/-- The 174 metadata words: the first cell goes to `rOUT` (the halt value), the
other 173 follow. -/
def metaEmitBlock : Block :=
  .seq (acts [.reserve rOUT, .store rOUT 1]) (emitRegs metaWordRegs)

/-- One Horner step: move the cursor down, read the cell, `acc := 2 acc + cell`. -/
def hornerStepBlock : Block :=
  acts [.arithmetic .sub rRA rRA rONE, .load rRB rRA, .arithmetic .add rACC rACC rACC,
    .arithmetic .add rACC rACC rRB, .arithmetic .sub rRJ rRJ rONE]

/-- Output word `i`: the cells `buf + i W, ..., buf + (i + 1) W - 1` read from the
top down into the accumulator, then one output cell. -/
def repackWordBlock : Block :=
  .seq (acts [.arithmetic .add rRA rRI rONE, .arithmetic .mul rRA rRA rWW,
      .arithmetic .add rRA rRA rBUF, .constant rACC 0, .move rRJ rWW])
    (.seq (.loop rRJ hornerStepBlock) (emitBit rACC))

/-- The dense words, one per `W` buffer cells. -/
def repackBlock : Block := forSlots rRI rRIGO rDCNT repackWordBlock

/-- Metadata bank, metadata words, dense words. -/
def outputBlock : Block := .seq (metaChain 108) (.seq metaEmitBlock repackBlock)

end Builder

end RMQ.SuccinctFinal.PackedConstruction

import RMQ.Core.WordRAM.Construction.Spec.Plan

/-!
# PRE-1 S7: the 174 metadata words from three scalars

Machine-free specification layer (outside the builder firewall). The metadata
bank of the builder holds 108 values, each one arithmetic step over the
size-only geometry bank, the long count `lc` and the sparse-exception flag count
`c` (the sparse count is `c * localStride (2n)`), or over earlier metadata bank
values. `metaWords n lc c` lists the 174 words in emission order, each a bank or
metadata-bank value, and `metaWords_eq` identifies that list with
`metadataOf n lc (c * localStride (2n))`. The payload length and the old cell
count are `mv_pay` and `mv_oldCount` (`pay_eq`, `cellCount_eq`).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.SuccinctSpace
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-! ## Metadata bank values -/

/-- Metadata bank register 229. -/
def mv_sc (n _lc c : Nat) : Nat := c * (GenericSelect.localStride (2 * n))

/-- Metadata bank register 230. -/
def mv_len1 (n _lc _c : Nat) : Nat := (packedRankSuperSlots n) * (packedRankWordSize n)

/-- Metadata bank register 231. -/
def mv_len2 (n _lc _c : Nat) : Nat := (packedRankBlockSlots n) * (packedRankBlockWidth n)

/-- Metadata bank register 232. -/
def mv_len3 (n _lc _c : Nat) : Nat := (packedSuperSlots n) * (packedRankWordSize n)

/-- Metadata bank register 233. -/
def mv_len7 (n _lc _c : Nat) : Nat := (packedLocalSlots n) * (packedLocalWidth n)

/-- Metadata bank register 234. -/
def mv_len11 (n _lc _c : Nat) : Nat := (packedLongFlagRankSlots n) * (packedLongFlagWordSize n)

/-- Metadata bank register 235. -/
def mv_lcS (n lc _c : Nat) : Nat := lc * (GenericSelect.superStride (2 * n))

/-- Metadata bank register 236. -/
def mv_len14 (n lc c : Nat) : Nat := (mv_lcS n lc c) * (packedRankWordSize n)

/-- Metadata bank register 237. -/
def mv_len15 (n _lc _c : Nat) : Nat := (packedSparseRankSlots n) * (packedSparseWordSize n)

/-- Metadata bank register 238. -/
def mv_len18 (n lc c : Nat) : Nat := (mv_sc n lc c) * (packedLocalWidth n)

/-- Metadata bank register 239. -/
def mv_o3 (n lc c : Nat) : Nat := (mv_len1 n lc c) + (mv_len2 n lc c)

/-- Metadata bank register 240. -/
def mv_o4 (n lc c : Nat) : Nat := (mv_o3 n lc c) + (mv_len3 n lc c)

/-- Metadata bank register 241. -/
def mv_o5 (n lc c : Nat) : Nat := (mv_o4 n lc c) + (mv_len3 n lc c)

/-- Metadata bank register 242. -/
def mv_o6 (n lc c : Nat) : Nat := (mv_o5 n lc c) + (mv_len3 n lc c)

/-- Metadata bank register 243. -/
def mv_o7 (n lc c : Nat) : Nat := (mv_o6 n lc c) + (mv_len3 n lc c)

/-- Metadata bank register 244. -/
def mv_o8 (n lc c : Nat) : Nat := (mv_o7 n lc c) + (mv_len7 n lc c)

/-- Metadata bank register 245. -/
def mv_o9 (n lc c : Nat) : Nat := (mv_o8 n lc c) + (mv_len7 n lc c)

/-- Metadata bank register 246. -/
def mv_o10 (n lc c : Nat) : Nat := (mv_o9 n lc c) + (mv_len7 n lc c)

/-- Metadata bank register 247. -/
def mv_o11 (n lc c : Nat) : Nat := (mv_o10 n lc c) + (mv_len7 n lc c)

/-- Metadata bank register 248. -/
def mv_o12 (n lc c : Nat) : Nat := (mv_o11 n lc c) + (mv_len11 n lc c)

/-- Metadata bank register 249. -/
def mv_o13 (n lc c : Nat) : Nat := (mv_o12 n lc c) + (mv_len11 n lc c)

/-- Metadata bank register 250. -/
def mv_o14 (n lc c : Nat) : Nat := (mv_o13 n lc c) + (packedSuperSlots n)

/-- Metadata bank register 251. -/
def mv_o15 (n lc c : Nat) : Nat := (mv_o14 n lc c) + (mv_len14 n lc c)

/-- Metadata bank register 252. -/
def mv_o16 (n lc c : Nat) : Nat := (mv_o15 n lc c) + (mv_len15 n lc c)

/-- Metadata bank register 253. -/
def mv_o17 (n lc c : Nat) : Nat := (mv_o16 n lc c) + (mv_len15 n lc c)

/-- Metadata bank register 254. -/
def mv_o18 (n lc c : Nat) : Nat := (mv_o17 n lc c) + (packedSparseSlots n)

/-- Metadata bank register 255. -/
def mv_acc (n lc c : Nat) : Nat := (mv_o18 n lc c) + (mv_len18 n lc c)

/-- Metadata bank register 256. -/
def mv_a (n _lc _c : Nat) : Nat := (packedReviewerCellWidth n) + (2 * n)

/-- Metadata bank register 257. -/
def mv_b2 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_len1 n lc c)

/-- Metadata bank register 258. -/
def mv_b3 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o3 n lc c)

/-- Metadata bank register 259. -/
def mv_b4 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o4 n lc c)

/-- Metadata bank register 260. -/
def mv_b5 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o5 n lc c)

/-- Metadata bank register 261. -/
def mv_b6 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o6 n lc c)

/-- Metadata bank register 262. -/
def mv_b7 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o7 n lc c)

/-- Metadata bank register 263. -/
def mv_b8 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o8 n lc c)

/-- Metadata bank register 264. -/
def mv_b9 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o9 n lc c)

/-- Metadata bank register 265. -/
def mv_b10 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o10 n lc c)

/-- Metadata bank register 266. -/
def mv_b11 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o11 n lc c)

/-- Metadata bank register 267. -/
def mv_b12 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o12 n lc c)

/-- Metadata bank register 268. -/
def mv_b13 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o13 n lc c)

/-- Metadata bank register 269. -/
def mv_b14 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o14 n lc c)

/-- Metadata bank register 270. -/
def mv_b15 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o15 n lc c)

/-- Metadata bank register 271. -/
def mv_b16 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o16 n lc c)

/-- Metadata bank register 272. -/
def mv_b17 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o17 n lc c)

/-- Metadata bank register 273. -/
def mv_b18 (n lc c : Nat) : Nat := (mv_a n lc c) + (mv_o18 n lc c)

/-- Metadata bank register 274. -/
def mv_pay (n lc c : Nat) : Nat := ((((2 * n) + (mv_acc n lc c)) + (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n)) + (SuccinctClose.bpFringeTableOverhead n)) + (SuccinctClose.bpChunkSelectTableOverhead n)

/-- Metadata bank register 275. -/
def mv_oldCount (n lc c : Nat) : Nat := ((((mv_pay n lc c) + (packedReviewerCellWidth n)) - 1) / (packedReviewerCellWidth n)) + 1

/-- Metadata bank register 276. -/
def mv_oldBits (n lc c : Nat) : Nat := (mv_oldCount n lc c) * (packedReviewerCellWidth n)

/-- Metadata bank register 277. -/
def mv_dcount (n lc c : Nat) : Nat := (((mv_oldBits n lc c) + (wordWidth n)) - 1) / (wordWidth n)

/-- Metadata bank register 278. -/
def mv_wc (n lc c : Nat) : Nat := (174) + (mv_dcount n lc c)

/-- Metadata bank register 279. -/
def mv_ioff (n lc c : Nat) : Nat := (2 * n) + (mv_acc n lc c)

/-- Metadata bank register 280. -/
def mv_foff (n lc c : Nat) : Nat := (mv_ioff n lc c) + (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n)

/-- Metadata bank register 281. -/
def mv_soff (n lc c : Nat) : Nat := (mv_foff n lc c) + (SuccinctClose.bpFringeTableOverhead n)

/-- Metadata bank register 282. -/
def mv_fbase (n lc c : Nat) : Nat := (packedReviewerCellWidth n) + (mv_foff n lc c)

/-- Metadata bank register 283. -/
def mv_sbase (n lc c : Nat) : Nat := (packedReviewerCellWidth n) + (mv_soff n lc c)

/-- Metadata bank register 284. -/
def mv_ib0 (n lc c : Nat) : Nat := (packedReviewerCellWidth n) + (mv_ioff n lc c)

/-- Metadata bank register 285. -/
def mv_q2n (n _lc _c : Nat) : Nat := (2 * n) / (packedRankWordSize n)

/-- Metadata bank register 286. -/
def mv_cc2n (n lc c : Nat) : Nat := (mv_q2n n lc c) + ((if (2 * n) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 287. -/
def mv_aliasWc (n lc c : Nat) : Nat := ((mv_cc2n n lc c) + (2 * n)) + 1

/-- Metadata bank register 288. -/
def mv_qsup (n _lc _c : Nat) : Nat := (packedSuperSlots n) / (packedLongFlagWordSize n)

/-- Metadata bank register 289. -/
def mv_lfwc (n lc c : Nat) : Nat := (((mv_qsup n lc c) + ((if (packedSuperSlots n) % (packedLongFlagWordSize n) = 0 then 0 else 1))) + (packedSuperSlots n)) + 1

/-- Metadata bank register 290. -/
def mv_qsp (n _lc _c : Nat) : Nat := (packedSparseSlots n) / (packedSparseWordSize n)

/-- Metadata bank register 291. -/
def mv_sfwc (n lc c : Nat) : Nat := (((mv_qsp n lc c) + ((if (packedSparseSlots n) % (packedSparseWordSize n) = 0 then 0 else 1))) + (packedSparseSlots n)) + 1

/-- Metadata bank register 292. -/
def mv_fbits (n _lc _c : Nat) : Nat := (packedReviewerFringeCount n) * (packedReviewerFringeWidth n)

/-- Metadata bank register 293. -/
def mv_sbits (n _lc _c : Nat) : Nat := (packedReviewerSelectChunkCount n) * (packedReviewerSelectChunkWidth n)

/-- Metadata bank register 294. -/
def mv_q_39 (n _lc _c : Nat) : Nat := (packedRankWordSize n) / (packedRankWordSize n)

/-- Metadata bank register 295. -/
def mv_cc_39 (n lc c : Nat) : Nat := (mv_q_39 n lc c) + ((if (packedRankWordSize n) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 296. -/
def mv_q_61 (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).relativeWidth) / (packedRankWordSize n)

/-- Metadata bank register 297. -/
def mv_cc_61 (n lc c : Nat) : Nat := (mv_q_61 n lc c) + ((if ((packedInteriorLayout n).relativeWidth) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 298. -/
def mv_q_58 (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).offsetWidth) / (packedRankWordSize n)

/-- Metadata bank register 299. -/
def mv_cc_58 (n lc c : Nat) : Nat := (mv_q_58 n lc c) + ((if ((packedInteriorLayout n).offsetWidth) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 300. -/
def mv_q_60 (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).blockAddressWidth) / (packedRankWordSize n)

/-- Metadata bank register 301. -/
def mv_cc_60 (n lc c : Nat) : Nat := (mv_q_60 n lc c) + ((if ((packedInteriorLayout n).blockAddressWidth) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 302. -/
def mv_q_36 (n _lc _c : Nat) : Nat := (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) / (packedRankWordSize n)

/-- Metadata bank register 303. -/
def mv_cc_36 (n lc c : Nat) : Nat := (mv_q_36 n lc c) + ((if (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 304. -/
def mv_q_37 (n _lc _c : Nat) : Nat := (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) / (packedRankWordSize n)

/-- Metadata bank register 305. -/
def mv_cc_37 (n lc c : Nat) : Nat := (mv_q_37 n lc c) + ((if (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) % (packedRankWordSize n) = 0 then 0 else 1))

/-- Metadata bank register 306. -/
def mv_cd_39 (n _lc _c : Nat) : Nat := (((packedRankWordSize n) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 307. -/
def mv_cd_61 (n _lc _c : Nat) : Nat := ((((packedInteriorLayout n).relativeWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 308. -/
def mv_cd_58 (n _lc _c : Nat) : Nat := ((((packedInteriorLayout n).offsetWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 309. -/
def mv_cd_60 (n _lc _c : Nat) : Nat := ((((packedInteriorLayout n).blockAddressWidth) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 310. -/
def mv_cd_36 (n _lc _c : Nat) : Nat := (((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 311. -/
def mv_cd_37 (n _lc _c : Nat) : Nat := (((SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) + (packedRankWordSize n)) - 1) / (packedRankWordSize n)

/-- Metadata bank register 312. -/
def mv_BW (n lc c : Nat) : Nat := ((packedInteriorLayout n).superSampleCount) * (mv_cc_39 n lc c)

/-- Metadata bank register 313. -/
def mv_MR (n lc c : Nat) : Nat := ((packedInteriorLayout n).blockCount) * (mv_cc_61 n lc c)

/-- Metadata bank register 314. -/
def mv_LT (n lc c : Nat) : Nat := ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) * (mv_cc_58 n lc c)

/-- Metadata bank register 315. -/
def mv_GT (n lc c : Nat) : Nat := ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) * (mv_cc_60 n lc c)

/-- Metadata bank register 316. -/
def mv_LL (n lc c : Nat) : Nat := (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) * (mv_cc_36 n lc c)

/-- Metadata bank register 317. -/
def mv_GL (n lc c : Nat) : Nat := (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) * (mv_cc_37 n lc c)

/-- Metadata bank register 318. -/
def mv_p2 (n lc c : Nat) : Nat := (mv_BW n lc c) + (mv_MR n lc c)

/-- Metadata bank register 319. -/
def mv_p3 (n lc c : Nat) : Nat := (mv_p2 n lc c) + (mv_MR n lc c)

/-- Metadata bank register 320. -/
def mv_p4 (n lc c : Nat) : Nat := (mv_p3 n lc c) + (mv_MR n lc c)

/-- Metadata bank register 321. -/
def mv_p5 (n lc c : Nat) : Nat := (mv_p4 n lc c) + (mv_LT n lc c)

/-- Metadata bank register 322. -/
def mv_p6 (n lc c : Nat) : Nat := (mv_p5 n lc c) + (mv_GT n lc c)

/-- Metadata bank register 323. -/
def mv_p7 (n lc c : Nat) : Nat := (mv_p6 n lc c) + (mv_LL n lc c)

/-- Metadata bank register 324. -/
def mv_ptot (n lc c : Nat) : Nat := (mv_p7 n lc c) + (mv_GL n lc c)

/-- Metadata bank register 325. -/
def mv_q1bits (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).superSampleCount) * (packedRankWordSize n)

/-- Metadata bank register 326. -/
def mv_q2bits (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).blockCount) * ((packedInteriorLayout n).relativeWidth)

/-- Metadata bank register 327. -/
def mv_q5bits (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).macroSampleCount * ((packedInteriorLayout n).levelCount * (packedInteriorLayout n).macroSize)) * ((packedInteriorLayout n).offsetWidth)

/-- Metadata bank register 328. -/
def mv_q6bits (n _lc _c : Nat) : Nat := ((packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount) * ((packedInteriorLayout n).blockAddressWidth)

/-- Metadata bank register 329. -/
def mv_q7bits (n _lc _c : Nat) : Nat := (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) * (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize))

/-- Metadata bank register 330. -/
def mv_ib1 (n lc c : Nat) : Nat := (mv_ib0 n lc c) + (mv_q1bits n lc c)

/-- Metadata bank register 331. -/
def mv_ib2 (n lc c : Nat) : Nat := (mv_ib1 n lc c) + (mv_q2bits n lc c)

/-- Metadata bank register 332. -/
def mv_ib3 (n lc c : Nat) : Nat := (mv_ib2 n lc c) + (mv_q2bits n lc c)

/-- Metadata bank register 333. -/
def mv_ib4 (n lc c : Nat) : Nat := (mv_ib3 n lc c) + (mv_q2bits n lc c)

/-- Metadata bank register 334. -/
def mv_ib5 (n lc c : Nat) : Nat := (mv_ib4 n lc c) + (mv_q5bits n lc c)

/-- Metadata bank register 335. -/
def mv_ib6 (n lc c : Nat) : Nat := (mv_ib5 n lc c) + (mv_q6bits n lc c)

/-- Metadata bank register 336. -/
def mv_ib7 (n lc c : Nat) : Nat := (mv_ib6 n lc c) + (mv_q7bits n lc c)

/-- The metadata bank values in register order `229, 230, ...`. -/
def metaVals (n lc c : Nat) : List Nat :=
  [mv_sc n lc c,
    mv_len1 n lc c,
    mv_len2 n lc c,
    mv_len3 n lc c,
    mv_len7 n lc c,
    mv_len11 n lc c,
    mv_lcS n lc c,
    mv_len14 n lc c,
    mv_len15 n lc c,
    mv_len18 n lc c,
    mv_o3 n lc c,
    mv_o4 n lc c,
    mv_o5 n lc c,
    mv_o6 n lc c,
    mv_o7 n lc c,
    mv_o8 n lc c,
    mv_o9 n lc c,
    mv_o10 n lc c,
    mv_o11 n lc c,
    mv_o12 n lc c,
    mv_o13 n lc c,
    mv_o14 n lc c,
    mv_o15 n lc c,
    mv_o16 n lc c,
    mv_o17 n lc c,
    mv_o18 n lc c,
    mv_acc n lc c,
    mv_a n lc c,
    mv_b2 n lc c,
    mv_b3 n lc c,
    mv_b4 n lc c,
    mv_b5 n lc c,
    mv_b6 n lc c,
    mv_b7 n lc c,
    mv_b8 n lc c,
    mv_b9 n lc c,
    mv_b10 n lc c,
    mv_b11 n lc c,
    mv_b12 n lc c,
    mv_b13 n lc c,
    mv_b14 n lc c,
    mv_b15 n lc c,
    mv_b16 n lc c,
    mv_b17 n lc c,
    mv_b18 n lc c,
    mv_pay n lc c,
    mv_oldCount n lc c,
    mv_oldBits n lc c,
    mv_dcount n lc c,
    mv_wc n lc c,
    mv_ioff n lc c,
    mv_foff n lc c,
    mv_soff n lc c,
    mv_fbase n lc c,
    mv_sbase n lc c,
    mv_ib0 n lc c,
    mv_q2n n lc c,
    mv_cc2n n lc c,
    mv_aliasWc n lc c,
    mv_qsup n lc c,
    mv_lfwc n lc c,
    mv_qsp n lc c,
    mv_sfwc n lc c,
    mv_fbits n lc c,
    mv_sbits n lc c,
    mv_q_39 n lc c,
    mv_cc_39 n lc c,
    mv_q_61 n lc c,
    mv_cc_61 n lc c,
    mv_q_58 n lc c,
    mv_cc_58 n lc c,
    mv_q_60 n lc c,
    mv_cc_60 n lc c,
    mv_q_36 n lc c,
    mv_cc_36 n lc c,
    mv_q_37 n lc c,
    mv_cc_37 n lc c,
    mv_cd_39 n lc c,
    mv_cd_61 n lc c,
    mv_cd_58 n lc c,
    mv_cd_60 n lc c,
    mv_cd_36 n lc c,
    mv_cd_37 n lc c,
    mv_BW n lc c,
    mv_MR n lc c,
    mv_LT n lc c,
    mv_GT n lc c,
    mv_LL n lc c,
    mv_GL n lc c,
    mv_p2 n lc c,
    mv_p3 n lc c,
    mv_p4 n lc c,
    mv_p5 n lc c,
    mv_p6 n lc c,
    mv_p7 n lc c,
    mv_ptot n lc c,
    mv_q1bits n lc c,
    mv_q2bits n lc c,
    mv_q5bits n lc c,
    mv_q6bits n lc c,
    mv_q7bits n lc c,
    mv_ib1 n lc c,
    mv_ib2 n lc c,
    mv_ib3 n lc c,
    mv_ib4 n lc c,
    mv_ib5 n lc c,
    mv_ib6 n lc c,
    mv_ib7 n lc c]

/-- Reference value of metadata bank register `229 + i`. -/
def metaVal (n lc c i : Nat) : Nat := (metaVals n lc c).getD i 0

theorem metaVal_0 (n lc c : Nat) : metaVal n lc c 0 = mv_sc n lc c := rfl
theorem metaVal_1 (n lc c : Nat) : metaVal n lc c 1 = mv_len1 n lc c := rfl
theorem metaVal_2 (n lc c : Nat) : metaVal n lc c 2 = mv_len2 n lc c := rfl
theorem metaVal_3 (n lc c : Nat) : metaVal n lc c 3 = mv_len3 n lc c := rfl
theorem metaVal_4 (n lc c : Nat) : metaVal n lc c 4 = mv_len7 n lc c := rfl
theorem metaVal_5 (n lc c : Nat) : metaVal n lc c 5 = mv_len11 n lc c := rfl
theorem metaVal_6 (n lc c : Nat) : metaVal n lc c 6 = mv_lcS n lc c := rfl
theorem metaVal_7 (n lc c : Nat) : metaVal n lc c 7 = mv_len14 n lc c := rfl
theorem metaVal_8 (n lc c : Nat) : metaVal n lc c 8 = mv_len15 n lc c := rfl
theorem metaVal_9 (n lc c : Nat) : metaVal n lc c 9 = mv_len18 n lc c := rfl
theorem metaVal_10 (n lc c : Nat) : metaVal n lc c 10 = mv_o3 n lc c := rfl
theorem metaVal_11 (n lc c : Nat) : metaVal n lc c 11 = mv_o4 n lc c := rfl
theorem metaVal_12 (n lc c : Nat) : metaVal n lc c 12 = mv_o5 n lc c := rfl
theorem metaVal_13 (n lc c : Nat) : metaVal n lc c 13 = mv_o6 n lc c := rfl
theorem metaVal_14 (n lc c : Nat) : metaVal n lc c 14 = mv_o7 n lc c := rfl
theorem metaVal_15 (n lc c : Nat) : metaVal n lc c 15 = mv_o8 n lc c := rfl
theorem metaVal_16 (n lc c : Nat) : metaVal n lc c 16 = mv_o9 n lc c := rfl
theorem metaVal_17 (n lc c : Nat) : metaVal n lc c 17 = mv_o10 n lc c := rfl
theorem metaVal_18 (n lc c : Nat) : metaVal n lc c 18 = mv_o11 n lc c := rfl
theorem metaVal_19 (n lc c : Nat) : metaVal n lc c 19 = mv_o12 n lc c := rfl
theorem metaVal_20 (n lc c : Nat) : metaVal n lc c 20 = mv_o13 n lc c := rfl
theorem metaVal_21 (n lc c : Nat) : metaVal n lc c 21 = mv_o14 n lc c := rfl
theorem metaVal_22 (n lc c : Nat) : metaVal n lc c 22 = mv_o15 n lc c := rfl
theorem metaVal_23 (n lc c : Nat) : metaVal n lc c 23 = mv_o16 n lc c := rfl
theorem metaVal_24 (n lc c : Nat) : metaVal n lc c 24 = mv_o17 n lc c := rfl
theorem metaVal_25 (n lc c : Nat) : metaVal n lc c 25 = mv_o18 n lc c := rfl
theorem metaVal_26 (n lc c : Nat) : metaVal n lc c 26 = mv_acc n lc c := rfl
theorem metaVal_27 (n lc c : Nat) : metaVal n lc c 27 = mv_a n lc c := rfl
theorem metaVal_28 (n lc c : Nat) : metaVal n lc c 28 = mv_b2 n lc c := rfl
theorem metaVal_29 (n lc c : Nat) : metaVal n lc c 29 = mv_b3 n lc c := rfl
theorem metaVal_30 (n lc c : Nat) : metaVal n lc c 30 = mv_b4 n lc c := rfl
theorem metaVal_31 (n lc c : Nat) : metaVal n lc c 31 = mv_b5 n lc c := rfl
theorem metaVal_32 (n lc c : Nat) : metaVal n lc c 32 = mv_b6 n lc c := rfl
theorem metaVal_33 (n lc c : Nat) : metaVal n lc c 33 = mv_b7 n lc c := rfl
theorem metaVal_34 (n lc c : Nat) : metaVal n lc c 34 = mv_b8 n lc c := rfl
theorem metaVal_35 (n lc c : Nat) : metaVal n lc c 35 = mv_b9 n lc c := rfl
theorem metaVal_36 (n lc c : Nat) : metaVal n lc c 36 = mv_b10 n lc c := rfl
theorem metaVal_37 (n lc c : Nat) : metaVal n lc c 37 = mv_b11 n lc c := rfl
theorem metaVal_38 (n lc c : Nat) : metaVal n lc c 38 = mv_b12 n lc c := rfl
theorem metaVal_39 (n lc c : Nat) : metaVal n lc c 39 = mv_b13 n lc c := rfl
theorem metaVal_40 (n lc c : Nat) : metaVal n lc c 40 = mv_b14 n lc c := rfl
theorem metaVal_41 (n lc c : Nat) : metaVal n lc c 41 = mv_b15 n lc c := rfl
theorem metaVal_42 (n lc c : Nat) : metaVal n lc c 42 = mv_b16 n lc c := rfl
theorem metaVal_43 (n lc c : Nat) : metaVal n lc c 43 = mv_b17 n lc c := rfl
theorem metaVal_44 (n lc c : Nat) : metaVal n lc c 44 = mv_b18 n lc c := rfl
theorem metaVal_45 (n lc c : Nat) : metaVal n lc c 45 = mv_pay n lc c := rfl
theorem metaVal_46 (n lc c : Nat) : metaVal n lc c 46 = mv_oldCount n lc c := rfl
theorem metaVal_47 (n lc c : Nat) : metaVal n lc c 47 = mv_oldBits n lc c := rfl
theorem metaVal_48 (n lc c : Nat) : metaVal n lc c 48 = mv_dcount n lc c := rfl
theorem metaVal_49 (n lc c : Nat) : metaVal n lc c 49 = mv_wc n lc c := rfl
theorem metaVal_50 (n lc c : Nat) : metaVal n lc c 50 = mv_ioff n lc c := rfl
theorem metaVal_51 (n lc c : Nat) : metaVal n lc c 51 = mv_foff n lc c := rfl
theorem metaVal_52 (n lc c : Nat) : metaVal n lc c 52 = mv_soff n lc c := rfl
theorem metaVal_53 (n lc c : Nat) : metaVal n lc c 53 = mv_fbase n lc c := rfl
theorem metaVal_54 (n lc c : Nat) : metaVal n lc c 54 = mv_sbase n lc c := rfl
theorem metaVal_55 (n lc c : Nat) : metaVal n lc c 55 = mv_ib0 n lc c := rfl
theorem metaVal_56 (n lc c : Nat) : metaVal n lc c 56 = mv_q2n n lc c := rfl
theorem metaVal_57 (n lc c : Nat) : metaVal n lc c 57 = mv_cc2n n lc c := rfl
theorem metaVal_58 (n lc c : Nat) : metaVal n lc c 58 = mv_aliasWc n lc c := rfl
theorem metaVal_59 (n lc c : Nat) : metaVal n lc c 59 = mv_qsup n lc c := rfl
theorem metaVal_60 (n lc c : Nat) : metaVal n lc c 60 = mv_lfwc n lc c := rfl
theorem metaVal_61 (n lc c : Nat) : metaVal n lc c 61 = mv_qsp n lc c := rfl
theorem metaVal_62 (n lc c : Nat) : metaVal n lc c 62 = mv_sfwc n lc c := rfl
theorem metaVal_63 (n lc c : Nat) : metaVal n lc c 63 = mv_fbits n lc c := rfl
theorem metaVal_64 (n lc c : Nat) : metaVal n lc c 64 = mv_sbits n lc c := rfl
theorem metaVal_65 (n lc c : Nat) : metaVal n lc c 65 = mv_q_39 n lc c := rfl
theorem metaVal_66 (n lc c : Nat) : metaVal n lc c 66 = mv_cc_39 n lc c := rfl
theorem metaVal_67 (n lc c : Nat) : metaVal n lc c 67 = mv_q_61 n lc c := rfl
theorem metaVal_68 (n lc c : Nat) : metaVal n lc c 68 = mv_cc_61 n lc c := rfl
theorem metaVal_69 (n lc c : Nat) : metaVal n lc c 69 = mv_q_58 n lc c := rfl
theorem metaVal_70 (n lc c : Nat) : metaVal n lc c 70 = mv_cc_58 n lc c := rfl
theorem metaVal_71 (n lc c : Nat) : metaVal n lc c 71 = mv_q_60 n lc c := rfl
theorem metaVal_72 (n lc c : Nat) : metaVal n lc c 72 = mv_cc_60 n lc c := rfl
theorem metaVal_73 (n lc c : Nat) : metaVal n lc c 73 = mv_q_36 n lc c := rfl
theorem metaVal_74 (n lc c : Nat) : metaVal n lc c 74 = mv_cc_36 n lc c := rfl
theorem metaVal_75 (n lc c : Nat) : metaVal n lc c 75 = mv_q_37 n lc c := rfl
theorem metaVal_76 (n lc c : Nat) : metaVal n lc c 76 = mv_cc_37 n lc c := rfl
theorem metaVal_77 (n lc c : Nat) : metaVal n lc c 77 = mv_cd_39 n lc c := rfl
theorem metaVal_78 (n lc c : Nat) : metaVal n lc c 78 = mv_cd_61 n lc c := rfl
theorem metaVal_79 (n lc c : Nat) : metaVal n lc c 79 = mv_cd_58 n lc c := rfl
theorem metaVal_80 (n lc c : Nat) : metaVal n lc c 80 = mv_cd_60 n lc c := rfl
theorem metaVal_81 (n lc c : Nat) : metaVal n lc c 81 = mv_cd_36 n lc c := rfl
theorem metaVal_82 (n lc c : Nat) : metaVal n lc c 82 = mv_cd_37 n lc c := rfl
theorem metaVal_83 (n lc c : Nat) : metaVal n lc c 83 = mv_BW n lc c := rfl
theorem metaVal_84 (n lc c : Nat) : metaVal n lc c 84 = mv_MR n lc c := rfl
theorem metaVal_85 (n lc c : Nat) : metaVal n lc c 85 = mv_LT n lc c := rfl
theorem metaVal_86 (n lc c : Nat) : metaVal n lc c 86 = mv_GT n lc c := rfl
theorem metaVal_87 (n lc c : Nat) : metaVal n lc c 87 = mv_LL n lc c := rfl
theorem metaVal_88 (n lc c : Nat) : metaVal n lc c 88 = mv_GL n lc c := rfl
theorem metaVal_89 (n lc c : Nat) : metaVal n lc c 89 = mv_p2 n lc c := rfl
theorem metaVal_90 (n lc c : Nat) : metaVal n lc c 90 = mv_p3 n lc c := rfl
theorem metaVal_91 (n lc c : Nat) : metaVal n lc c 91 = mv_p4 n lc c := rfl
theorem metaVal_92 (n lc c : Nat) : metaVal n lc c 92 = mv_p5 n lc c := rfl
theorem metaVal_93 (n lc c : Nat) : metaVal n lc c 93 = mv_p6 n lc c := rfl
theorem metaVal_94 (n lc c : Nat) : metaVal n lc c 94 = mv_p7 n lc c := rfl
theorem metaVal_95 (n lc c : Nat) : metaVal n lc c 95 = mv_ptot n lc c := rfl
theorem metaVal_96 (n lc c : Nat) : metaVal n lc c 96 = mv_q1bits n lc c := rfl
theorem metaVal_97 (n lc c : Nat) : metaVal n lc c 97 = mv_q2bits n lc c := rfl
theorem metaVal_98 (n lc c : Nat) : metaVal n lc c 98 = mv_q5bits n lc c := rfl
theorem metaVal_99 (n lc c : Nat) : metaVal n lc c 99 = mv_q6bits n lc c := rfl
theorem metaVal_100 (n lc c : Nat) : metaVal n lc c 100 = mv_q7bits n lc c := rfl
theorem metaVal_101 (n lc c : Nat) : metaVal n lc c 101 = mv_ib1 n lc c := rfl
theorem metaVal_102 (n lc c : Nat) : metaVal n lc c 102 = mv_ib2 n lc c := rfl
theorem metaVal_103 (n lc c : Nat) : metaVal n lc c 103 = mv_ib3 n lc c := rfl
theorem metaVal_104 (n lc c : Nat) : metaVal n lc c 104 = mv_ib4 n lc c := rfl
theorem metaVal_105 (n lc c : Nat) : metaVal n lc c 105 = mv_ib5 n lc c := rfl
theorem metaVal_106 (n lc c : Nat) : metaVal n lc c 106 = mv_ib6 n lc c := rfl
theorem metaVal_107 (n lc c : Nat) : metaVal n lc c 107 = mv_ib7 n lc c := rfl

/-- The 174 metadata words in emission order. -/
def metaWords (n lc c : Nat) : List Nat :=
  [n,
    (packedReviewerCellWidth n),
    mv_oldCount n lc c,
    mv_oldBits n lc c,
    lc,
    mv_sc n lc c,
    (wordWidth n),
    mv_wc n lc c,
    (packedRankWordSize n),
    (GenericSelect.superStride (2 * n)),
    (GenericSelect.localStride (2 * n)),
    (GenericSelect.localSlotsPerSuper (2 * n)),
    (packedSuperSlots n),
    (packedSparseSlots n),
    (packedLongFlagWordSize n),
    (packedSparseWordSize n),
    (packedRankWordSize n),
    ((packedInteriorLayout n).blockSize),
    (packedFringeChunkBits n),
    (packedSummaryBase n),
    ((packedInteriorLayout n).blockCount),
    ((packedInteriorLayout n).superSampleCount),
    ((packedInteriorLayout n).macroSize),
    ((packedInteriorLayout n).macroSampleCount),
    ((packedInteriorLayout n).offsetWidth),
    ((packedInteriorLayout n).globalLevelCount),
    ((packedInteriorLayout n).relativeWidth),
    ((packedInteriorLayout n).offsetWidth),
    ((packedInteriorLayout n).blockAddressWidth),
    (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize),
    (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount),
    (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)),
    (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)),
    0,
    mv_BW n lc c,
    mv_p2 n lc c,
    mv_p3 n lc c,
    mv_p4 n lc c,
    mv_p5 n lc c,
    mv_p6 n lc c,
    mv_p7 n lc c,
    mv_ptot n lc c,
    (packedReviewerCellWidth n),
    (2 * n),
    (packedRankWordSize n),
    mv_cc2n n lc c,
    mv_b3 n lc c,
    mv_len3 n lc c,
    (packedRankWordSize n),
    (packedSuperSlots n),
    mv_b4 n lc c,
    mv_len3 n lc c,
    (packedRankWordSize n),
    (packedSuperSlots n),
    mv_b5 n lc c,
    mv_len3 n lc c,
    (packedRankWordSize n),
    (packedSuperSlots n),
    mv_b6 n lc c,
    mv_len3 n lc c,
    (packedRankWordSize n),
    (packedSuperSlots n),
    mv_b7 n lc c,
    mv_len7 n lc c,
    (packedLocalWidth n),
    (packedLocalSlots n),
    mv_b8 n lc c,
    mv_len7 n lc c,
    (packedLocalWidth n),
    (packedLocalSlots n),
    mv_b9 n lc c,
    mv_len7 n lc c,
    (packedLocalWidth n),
    (packedLocalSlots n),
    mv_b10 n lc c,
    mv_len7 n lc c,
    (packedLocalWidth n),
    (packedLocalSlots n),
    mv_b11 n lc c,
    mv_len11 n lc c,
    (packedLongFlagWordSize n),
    (packedLongFlagRankSlots n),
    mv_b12 n lc c,
    mv_len11 n lc c,
    (packedLongFlagWordSize n),
    (packedLongFlagRankSlots n),
    mv_b13 n lc c,
    (packedSuperSlots n),
    (packedLongFlagWordSize n),
    mv_lfwc n lc c,
    mv_b14 n lc c,
    mv_len14 n lc c,
    (packedRankWordSize n),
    mv_lcS n lc c,
    mv_b15 n lc c,
    mv_len15 n lc c,
    (packedSparseWordSize n),
    (packedSparseRankSlots n),
    mv_b16 n lc c,
    mv_len15 n lc c,
    (packedSparseWordSize n),
    (packedSparseRankSlots n),
    mv_b17 n lc c,
    (packedSparseSlots n),
    (packedSparseWordSize n),
    mv_sfwc n lc c,
    mv_b18 n lc c,
    mv_len18 n lc c,
    (packedLocalWidth n),
    mv_sc n lc c,
    mv_a n lc c,
    mv_len1 n lc c,
    (packedRankWordSize n),
    (packedRankSuperSlots n),
    mv_b2 n lc c,
    mv_len2 n lc c,
    (packedRankBlockWidth n),
    (packedRankBlockSlots n),
    (packedReviewerCellWidth n),
    (2 * n),
    (packedRankWordSize n),
    mv_aliasWc n lc c,
    0,
    0,
    0,
    0,
    mv_fbase n lc c,
    mv_fbits n lc c,
    (packedReviewerFringeWidth n),
    (packedReviewerFringeCount n),
    mv_sbase n lc c,
    mv_sbits n lc c,
    (packedReviewerSelectChunkWidth n),
    (packedReviewerSelectChunkCount n),
    0,
    mv_BW n lc c,
    mv_ib0 n lc c,
    (packedRankWordSize n),
    mv_cd_39 n lc c,
    mv_BW n lc c,
    mv_MR n lc c,
    mv_ib1 n lc c,
    ((packedInteriorLayout n).relativeWidth),
    mv_cd_61 n lc c,
    mv_p2 n lc c,
    mv_MR n lc c,
    mv_ib2 n lc c,
    ((packedInteriorLayout n).relativeWidth),
    mv_cd_61 n lc c,
    mv_p3 n lc c,
    mv_MR n lc c,
    mv_ib3 n lc c,
    ((packedInteriorLayout n).relativeWidth),
    mv_cd_61 n lc c,
    mv_p4 n lc c,
    mv_LT n lc c,
    mv_ib4 n lc c,
    ((packedInteriorLayout n).offsetWidth),
    mv_cd_58 n lc c,
    mv_p5 n lc c,
    mv_GT n lc c,
    mv_ib5 n lc c,
    ((packedInteriorLayout n).blockAddressWidth),
    mv_cd_60 n lc c,
    mv_p6 n lc c,
    mv_LL n lc c,
    mv_ib6 n lc c,
    (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)),
    mv_cd_36 n lc c,
    mv_p7 n lc c,
    mv_GL n lc c,
    mv_ib7 n lc c,
    (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)),
    mv_cd_37 n lc c]

/-! ## Source lengths, payload length and cell count -/

theorem srcLen_finalRankSuperFalse (n lc : Nat) : packedSourceBitLength n lc .finalRankSuperFalse = (packedRankSuperSlots n) * (packedRankWordSize n) := rfl
theorem srcLen_finalRankBlockFalse (n lc : Nat) : packedSourceBitLength n lc .finalRankBlockFalse = (packedRankBlockSlots n) * (packedRankBlockWidth n) := rfl
theorem srcLen_selectSuperBaseOccurrence (n lc : Nat) : packedSourceBitLength n lc .selectSuperBaseOccurrence = (packedSuperSlots n) * (packedRankWordSize n) := rfl
theorem srcLen_selectSuperBaseWordIndex (n lc : Nat) : packedSourceBitLength n lc .selectSuperBaseWordIndex = (packedSuperSlots n) * (packedRankWordSize n) := rfl
theorem srcLen_selectSuperRankBefore (n lc : Nat) : packedSourceBitLength n lc .selectSuperRankBefore = (packedSuperSlots n) * (packedRankWordSize n) := rfl
theorem srcLen_selectSuperFirstOffset (n lc : Nat) : packedSourceBitLength n lc .selectSuperFirstOffset = (packedSuperSlots n) * (packedRankWordSize n) := rfl
theorem srcLen_selectLocalBaseOccurrence (n lc : Nat) : packedSourceBitLength n lc .selectLocalBaseOccurrence = (packedLocalSlots n) * (packedLocalWidth n) := rfl
theorem srcLen_selectLocalBaseWordIndex (n lc : Nat) : packedSourceBitLength n lc .selectLocalBaseWordIndex = (packedLocalSlots n) * (packedLocalWidth n) := rfl
theorem srcLen_selectLocalRankBefore (n lc : Nat) : packedSourceBitLength n lc .selectLocalRankBefore = (packedLocalSlots n) * (packedLocalWidth n) := rfl
theorem srcLen_selectLocalFirstOffset (n lc : Nat) : packedSourceBitLength n lc .selectLocalFirstOffset = (packedLocalSlots n) * (packedLocalWidth n) := rfl
theorem srcLen_selectLongFlagRankSuperTrue (n lc : Nat) : packedSourceBitLength n lc .selectLongFlagRankSuperTrue = (packedLongFlagRankSlots n) * (packedLongFlagWordSize n) := rfl
theorem srcLen_selectLongFlagRankBlockTrue (n lc : Nat) : packedSourceBitLength n lc .selectLongFlagRankBlockTrue = (packedLongFlagRankSlots n) * (packedLongFlagWordSize n) := rfl
theorem srcLen_selectLongFlagBits (n lc : Nat) : packedSourceBitLength n lc .selectLongFlagBits = packedSuperSlots n := rfl
theorem srcLen_selectLongRelative (n lc : Nat) : packedSourceBitLength n lc .selectLongRelative = lc * (GenericSelect.superStride (2 * n)) * (packedRankWordSize n) := rfl
theorem srcLen_selectSparseRankSuperTrue (n lc : Nat) : packedSourceBitLength n lc .selectSparseRankSuperTrue = (packedSparseRankSlots n) * (packedSparseWordSize n) := rfl
theorem srcLen_selectSparseRankBlockTrue (n lc : Nat) : packedSourceBitLength n lc .selectSparseRankBlockTrue = (packedSparseRankSlots n) * (packedSparseWordSize n) := rfl
theorem srcLen_selectSparseFlagBits (n lc : Nat) : packedSourceBitLength n lc .selectSparseFlagBits = packedSparseSlots n := rfl

theorem ws_pos (n : Nat) : 0 < SuccinctRank.machineWordBits (2 * n) := SuccinctRank.machineWordBits_pos _

theorem tableWords_eq (k w ws : Nat) (h : 0 < ws) :
    packedInteriorTableWords k w ws = k * (w / ws + if w % ws = 0 then 0 else 1) := by
  unfold packedInteriorTableWords
  rw [chunkPayloadWords_length_eq_div_add_indicator h, List.length_replicate]

/-- Unfolds the reference payload length and the metadata bank values. -/
syntax "meta_pay_simp" : tactic
macro_rules | `(tactic| meta_pay_simp) => `(tactic| simp only [packedReviewerPayloadLength, packedReviewerAccessLength,
    RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, packedReviewerSourceBitLength, reduceCtorEq, if_false, if_true, srcLen_finalRankSuperFalse, srcLen_finalRankBlockFalse, srcLen_selectSuperBaseOccurrence, srcLen_selectSuperBaseWordIndex, srcLen_selectSuperRankBefore, srcLen_selectSuperFirstOffset, srcLen_selectLocalBaseOccurrence, srcLen_selectLocalBaseWordIndex, srcLen_selectLocalRankBefore, srcLen_selectLocalFirstOffset, srcLen_selectLongFlagRankSuperTrue, srcLen_selectLongFlagRankBlockTrue, srcLen_selectLongFlagBits, srcLen_selectLongRelative, srcLen_selectSparseRankSuperTrue, srcLen_selectSparseRankBlockTrue, srcLen_selectSparseFlagBits, packedRankWordSize, packedBpCodeWordWidth, packedSuperWidth, GenericSelect.wordBits, packedChunkCount, packedLongRelativeSlots, mv_sc, mv_len1, mv_len2, mv_len3, mv_len7, mv_len11, mv_lcS, mv_len14, mv_len15, mv_len18, mv_o3, mv_o4, mv_o5, mv_o6, mv_o7, mv_o8, mv_o9, mv_o10, mv_o11, mv_o12, mv_o13, mv_o14, mv_o15, mv_o16, mv_o17, mv_o18, mv_acc, mv_a, mv_b2, mv_b3, mv_b4, mv_b5, mv_b6, mv_b7, mv_b8, mv_b9, mv_b10, mv_b11, mv_b12, mv_b13, mv_b14, mv_b15, mv_b16, mv_b17, mv_b18, mv_pay, mv_oldCount, mv_oldBits, mv_dcount, mv_wc, mv_ioff, mv_foff, mv_soff, mv_fbase, mv_sbase, mv_ib0, mv_q2n, mv_cc2n, mv_aliasWc, mv_qsup, mv_lfwc, mv_qsp, mv_sfwc, mv_fbits, mv_sbits, mv_q_39, mv_cc_39, mv_q_61, mv_cc_61, mv_q_58, mv_cc_58, mv_q_60, mv_cc_60, mv_q_36, mv_cc_36, mv_q_37, mv_cc_37, mv_cd_39, mv_cd_61, mv_cd_58, mv_cd_60, mv_cd_36, mv_cd_37, mv_BW, mv_MR, mv_LT, mv_GT, mv_LL, mv_GL, mv_p2, mv_p3, mv_p4, mv_p5, mv_p6, mv_p7, mv_ptot, mv_q1bits, mv_q2bits, mv_q5bits, mv_q6bits, mv_q7bits, mv_ib1, mv_ib2, mv_ib3, mv_ib4, mv_ib5, mv_ib6, mv_ib7])

theorem pay_eq (n lc c : Nat) :
    packedReviewerPayloadLength n lc (c * GenericSelect.localStride (2 * n)) = mv_pay n lc c := by
  meta_pay_simp
  omega

theorem cellCount_eq (n lc c : Nat) :
    packedReviewerCellCount n lc (c * GenericSelect.localStride (2 * n)) = mv_oldCount n lc c := by
  unfold packedReviewerCellCount GenericSelect.selectCeilDiv
  rw [pay_eq, mv_oldCount]
  omega

/-! ## Descriptor lemmas -/

/-- Unfolds the reference regular geometry and the metadata bank values. -/
syntax "meta_reg_simp" : tactic
macro_rules | `(tactic| meta_reg_simp) => `(tactic| simp only [regularDescriptor, packedSegmentSource?, RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?, Nat.reduceEqDiff, if_false, if_true, reduceIte, packedReviewerClosedStridedBitAddress, packedReviewerClosedSourceOffset, packedReviewerClosedAccessOffset, packedReviewerClosedSparseRankSuperPrefixLength, packedSourceStride, packedReviewerLegacyWordCount, packedReviewerSourceWordCount, reduceCtorEq, packedSourceWordCount, packedReviewerSourceBitLength, packedSourceBitLength, packedReviewerClosedFringeAddress, packedReviewerClosedSelectChunkAddress, packedReviewerClosedFringeOffset, packedReviewerClosedSelectChunkOffset, packedReviewerClosedInteriorOffset, packedReviewerClosedAccessLength, Nat.zero_mul, Nat.add_zero, List.cons.injEq, and_true, srcLen_finalRankSuperFalse, srcLen_finalRankBlockFalse, srcLen_selectSuperBaseOccurrence, srcLen_selectSuperBaseWordIndex, srcLen_selectSuperRankBefore, srcLen_selectSuperFirstOffset, srcLen_selectLocalBaseOccurrence, srcLen_selectLocalBaseWordIndex, srcLen_selectLocalRankBefore, srcLen_selectLocalFirstOffset, srcLen_selectLongFlagRankSuperTrue, srcLen_selectLongFlagRankBlockTrue, srcLen_selectLongFlagBits, srcLen_selectLongRelative, srcLen_selectSparseRankSuperTrue, srcLen_selectSparseRankBlockTrue, srcLen_selectSparseFlagBits, packedRankWordSize, packedBpCodeWordWidth, packedSuperWidth, GenericSelect.wordBits, packedChunkCount, packedLongRelativeSlots, mv_sc, mv_len1, mv_len2, mv_len3, mv_len7, mv_len11, mv_lcS, mv_len14, mv_len15, mv_len18, mv_o3, mv_o4, mv_o5, mv_o6, mv_o7, mv_o8, mv_o9, mv_o10, mv_o11, mv_o12, mv_o13, mv_o14, mv_o15, mv_o16, mv_o17, mv_o18, mv_acc, mv_a, mv_b2, mv_b3, mv_b4, mv_b5, mv_b6, mv_b7, mv_b8, mv_b9, mv_b10, mv_b11, mv_b12, mv_b13, mv_b14, mv_b15, mv_b16, mv_b17, mv_b18, mv_pay, mv_oldCount, mv_oldBits, mv_dcount, mv_wc, mv_ioff, mv_foff, mv_soff, mv_fbase, mv_sbase, mv_ib0, mv_q2n, mv_cc2n, mv_aliasWc, mv_qsup, mv_lfwc, mv_qsp, mv_sfwc, mv_fbits, mv_sbits, mv_q_39, mv_cc_39, mv_q_61, mv_cc_61, mv_q_58, mv_cc_58, mv_q_60, mv_cc_60, mv_q_36, mv_cc_36, mv_q_37, mv_cc_37, mv_cd_39, mv_cd_61, mv_cd_58, mv_cd_60, mv_cd_36, mv_cd_37, mv_BW, mv_MR, mv_LT, mv_GT, mv_LL, mv_GL, mv_p2, mv_p3, mv_p4, mv_p5, mv_p6, mv_p7, mv_ptot, mv_q1bits, mv_q2bits, mv_q5bits, mv_q6bits, mv_q7bits, mv_ib1, mv_ib2, mv_ib3, mv_ib4, mv_ib5, mv_ib6, mv_ib7])

theorem regDesc_0 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 0 =
      [(packedReviewerCellWidth n), (2 * n), (packedRankWordSize n), mv_cc2n n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_1 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 1 =
      [mv_b3 n lc c, mv_len3 n lc c, (packedRankWordSize n), (packedSuperSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_2 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 2 =
      [mv_b4 n lc c, mv_len3 n lc c, (packedRankWordSize n), (packedSuperSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_3 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 3 =
      [mv_b5 n lc c, mv_len3 n lc c, (packedRankWordSize n), (packedSuperSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_4 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 4 =
      [mv_b6 n lc c, mv_len3 n lc c, (packedRankWordSize n), (packedSuperSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_5 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 5 =
      [mv_b7 n lc c, mv_len7 n lc c, (packedLocalWidth n), (packedLocalSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_6 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 6 =
      [mv_b8 n lc c, mv_len7 n lc c, (packedLocalWidth n), (packedLocalSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_7 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 7 =
      [mv_b9 n lc c, mv_len7 n lc c, (packedLocalWidth n), (packedLocalSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_8 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 8 =
      [mv_b10 n lc c, mv_len7 n lc c, (packedLocalWidth n), (packedLocalSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_9 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 9 =
      [mv_b11 n lc c, mv_len11 n lc c, (packedLongFlagWordSize n), (packedLongFlagRankSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_10 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 10 =
      [mv_b12 n lc c, mv_len11 n lc c, (packedLongFlagWordSize n), (packedLongFlagRankSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_11 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 11 =
      [mv_b13 n lc c, (packedSuperSlots n), (packedLongFlagWordSize n), mv_lfwc n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_12 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 12 =
      [mv_b14 n lc c, mv_len14 n lc c, (packedRankWordSize n), mv_lcS n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_13 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 13 =
      [mv_b15 n lc c, mv_len15 n lc c, (packedSparseWordSize n), (packedSparseRankSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_14 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 14 =
      [mv_b16 n lc c, mv_len15 n lc c, (packedSparseWordSize n), (packedSparseRankSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_15 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 15 =
      [mv_b17 n lc c, (packedSparseSlots n), (packedSparseWordSize n), mv_sfwc n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_16 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 16 =
      [mv_b18 n lc c, mv_len18 n lc c, (packedLocalWidth n), mv_sc n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_17 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 17 =
      [mv_a n lc c, mv_len1 n lc c, (packedRankWordSize n), (packedRankSuperSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_18 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 18 =
      [mv_b2 n lc c, mv_len2 n lc c, (packedRankBlockWidth n), (packedRankBlockSlots n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_19 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 19 =
      [(packedReviewerCellWidth n), (2 * n), (packedRankWordSize n), mv_aliasWc n lc c] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_20 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 20 =
      [0, 0, 0, 0] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_21 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 21 =
      [mv_fbase n lc c, mv_fbits n lc c, (packedReviewerFringeWidth n), (packedReviewerFringeCount n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem regDesc_22 (n lc c : Nat) :
    regularDescriptor n lc (c * GenericSelect.localStride (2 * n)) 22 =
      [mv_sbase n lc c, mv_sbits n lc c, (packedReviewerSelectChunkWidth n), (packedReviewerSelectChunkCount n)] := by
  meta_reg_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

/-- Unfolds the reference interior geometry and the metadata bank values. -/
syntax "meta_int_simp" : tactic
macro_rules | `(tactic| meta_int_simp) => `(tactic| simp only [interiorDescriptor, packedReviewerInteriorComponentWordPrefix, packedReviewerInteriorComponentWordCount, packedReviewerInteriorComponentBitPrefix, packedReviewerInteriorEntryWidth, packedReviewerInteriorEntryCount, packedInteriorOffsets, packedBaselineWords, packedMinRelWords, packedMaxRelWords, packedArgOffsetWords, packedLocalTableWords, packedGlobalTableWords, packedLocalLevelWords, packedGlobalLevelWords, tableWords_eq _ _ _ (ws_pos _), packedReviewerClosedInteriorOffset, packedReviewerClosedAccessLength, packedReviewerClosedAccessOffset, packedReviewerClosedSparseRankSuperPrefixLength, GenericSelect.selectCeilDiv, List.cons.injEq, and_true, Nat.add_zero, srcLen_finalRankSuperFalse, srcLen_finalRankBlockFalse, srcLen_selectSuperBaseOccurrence, srcLen_selectSuperBaseWordIndex, srcLen_selectSuperRankBefore, srcLen_selectSuperFirstOffset, srcLen_selectLocalBaseOccurrence, srcLen_selectLocalBaseWordIndex, srcLen_selectLocalRankBefore, srcLen_selectLocalFirstOffset, srcLen_selectLongFlagRankSuperTrue, srcLen_selectLongFlagRankBlockTrue, srcLen_selectLongFlagBits, srcLen_selectLongRelative, srcLen_selectSparseRankSuperTrue, srcLen_selectSparseRankBlockTrue, srcLen_selectSparseFlagBits, packedRankWordSize, packedBpCodeWordWidth, packedSuperWidth, GenericSelect.wordBits, packedChunkCount, packedLongRelativeSlots, mv_sc, mv_len1, mv_len2, mv_len3, mv_len7, mv_len11, mv_lcS, mv_len14, mv_len15, mv_len18, mv_o3, mv_o4, mv_o5, mv_o6, mv_o7, mv_o8, mv_o9, mv_o10, mv_o11, mv_o12, mv_o13, mv_o14, mv_o15, mv_o16, mv_o17, mv_o18, mv_acc, mv_a, mv_b2, mv_b3, mv_b4, mv_b5, mv_b6, mv_b7, mv_b8, mv_b9, mv_b10, mv_b11, mv_b12, mv_b13, mv_b14, mv_b15, mv_b16, mv_b17, mv_b18, mv_pay, mv_oldCount, mv_oldBits, mv_dcount, mv_wc, mv_ioff, mv_foff, mv_soff, mv_fbase, mv_sbase, mv_ib0, mv_q2n, mv_cc2n, mv_aliasWc, mv_qsup, mv_lfwc, mv_qsp, mv_sfwc, mv_fbits, mv_sbits, mv_q_39, mv_cc_39, mv_q_61, mv_cc_61, mv_q_58, mv_cc_58, mv_q_60, mv_cc_60, mv_q_36, mv_cc_36, mv_q_37, mv_cc_37, mv_cd_39, mv_cd_61, mv_cd_58, mv_cd_60, mv_cd_36, mv_cd_37, mv_BW, mv_MR, mv_LT, mv_GT, mv_LL, mv_GL, mv_p2, mv_p3, mv_p4, mv_p5, mv_p6, mv_p7, mv_ptot, mv_q1bits, mv_q2bits, mv_q5bits, mv_q6bits, mv_q7bits, mv_ib1, mv_ib2, mv_ib3, mv_ib4, mv_ib5, mv_ib6, mv_ib7])

theorem intDesc_baseline (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .baseline =
      [0, mv_BW n lc c, mv_ib0 n lc c, (packedRankWordSize n), mv_cd_39 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_minRel (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .minRel =
      [mv_BW n lc c, mv_MR n lc c, mv_ib1 n lc c, ((packedInteriorLayout n).relativeWidth), mv_cd_61 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_maxRel (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .maxRel =
      [mv_p2 n lc c, mv_MR n lc c, mv_ib2 n lc c, ((packedInteriorLayout n).relativeWidth), mv_cd_61 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_argOffset (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .argOffset =
      [mv_p3 n lc c, mv_MR n lc c, mv_ib3 n lc c, ((packedInteriorLayout n).relativeWidth), mv_cd_61 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_localOffset (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .localOffset =
      [mv_p4 n lc c, mv_LT n lc c, mv_ib4 n lc c, ((packedInteriorLayout n).offsetWidth), mv_cd_58 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_globalBlock (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .globalBlock =
      [mv_p5 n lc c, mv_GT n lc c, mv_ib5 n lc c, ((packedInteriorLayout n).blockAddressWidth), mv_cd_60 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_localLevel (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .localLevel =
      [mv_p6 n lc c, mv_LL n lc c, mv_ib6 n lc c, (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)), mv_cd_36 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

theorem intDesc_globalLevel (n lc c : Nat) :
    interiorDescriptor n lc (c * GenericSelect.localStride (2 * n)) .globalLevel =
      [mv_p7 n lc c, mv_GL n lc c, mv_ib7 n lc c, (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)), mv_cd_37 n lc c] := by
  meta_int_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

/-- Unfolds the reference scalar metadata and the metadata bank values. -/
syntax "meta_scalar_simp" : tactic
macro_rules | `(tactic| meta_scalar_simp) => `(tactic| simp only [scalarMetadataOf, metaWords, List.take_succ_cons, List.take_zero, cellCount_eq, List.cons.injEq, and_true,
    packedInteriorOffsets, packedInteriorComponentWords, packedBaselineWords, packedMinRelWords, packedMaxRelWords,
    packedArgOffsetWords, packedLocalTableWords, packedGlobalTableWords, packedLocalLevelWords, packedGlobalLevelWords,
    tableWords_eq _ _ _ (ws_pos _), GenericSelect.selectCeilDiv, packedRankWordSize, packedBpCodeWordWidth, packedSuperWidth, GenericSelect.wordBits, packedChunkCount, packedLongRelativeSlots, mv_sc, mv_len1, mv_len2, mv_len3, mv_len7, mv_len11, mv_lcS, mv_len14, mv_len15, mv_len18, mv_o3, mv_o4, mv_o5, mv_o6, mv_o7, mv_o8, mv_o9, mv_o10, mv_o11, mv_o12, mv_o13, mv_o14, mv_o15, mv_o16, mv_o17, mv_o18, mv_acc, mv_a, mv_b2, mv_b3, mv_b4, mv_b5, mv_b6, mv_b7, mv_b8, mv_b9, mv_b10, mv_b11, mv_b12, mv_b13, mv_b14, mv_b15, mv_b16, mv_b17, mv_b18, mv_pay, mv_oldCount, mv_oldBits, mv_dcount, mv_wc, mv_ioff, mv_foff, mv_soff, mv_fbase, mv_sbase, mv_ib0, mv_q2n, mv_cc2n, mv_aliasWc, mv_qsup, mv_lfwc, mv_qsp, mv_sfwc, mv_fbits, mv_sbits, mv_q_39, mv_cc_39, mv_q_61, mv_cc_61, mv_q_58, mv_cc_58, mv_q_60, mv_cc_60, mv_q_36, mv_cc_36, mv_q_37, mv_cc_37, mv_cd_39, mv_cd_61, mv_cd_58, mv_cd_60, mv_cd_36, mv_cd_37, mv_BW, mv_MR, mv_LT, mv_GT, mv_LL, mv_GL, mv_p2, mv_p3, mv_p4, mv_p5, mv_p6, mv_p7, mv_ptot, mv_q1bits, mv_q2bits, mv_q5bits, mv_q6bits, mv_q7bits, mv_ib1, mv_ib2, mv_ib3, mv_ib4, mv_ib5, mv_ib6, mv_ib7])

theorem scalar_eq (n lc c : Nat) :
    scalarMetadataOf n lc (c * GenericSelect.localStride (2 * n)) = (metaWords n lc c).take 42 := by
  meta_scalar_simp
  all_goals (repeat' apply And.intro) <;> first | trivial | rfl | omega

/-- **The metadata words.** -/
theorem metaWords_eq (n lc c : Nat) :
    metaWords n lc c = metadataOf n lc (c * GenericSelect.localStride (2 * n)) := by
  have hsplit : metaWords n lc c = (metaWords n lc c).take 42 ++ (metaWords n lc c).drop 42 := (List.take_append_drop _ _).symm
  rw [hsplit, metadataOf, scalar_eq]
  rw [show List.range 23 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] from rfl]
  simp only [interiorComponents, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    regDesc_0, regDesc_1, regDesc_2, regDesc_3, regDesc_4, regDesc_5, regDesc_6, regDesc_7, regDesc_8, regDesc_9, regDesc_10, regDesc_11, regDesc_12, regDesc_13, regDesc_14, regDesc_15, regDesc_16, regDesc_17, regDesc_18, regDesc_19, regDesc_20, regDesc_21, regDesc_22, intDesc_baseline, intDesc_minRel, intDesc_maxRel, intDesc_argOffset, intDesc_localOffset, intDesc_globalBlock, intDesc_localLevel, intDesc_globalLevel, List.append_assoc]
  rfl

end RMQ.SuccinctFinal.PackedConstruction.Spec

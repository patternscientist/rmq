import RMQ.Core.SuccinctFinal.RAM.GeometryClosure

/-!
# EG-CP-F01 evidence: every controller geometry constant in closed form in `n`

Nat-only mirror functions, one per geometry constant, together with checked
equalities against the in-tree definitions at an arbitrary `CartesianShape`.
-/

set_option autoImplicit false

namespace RMQ
namespace SuccinctFinal
namespace HeaderGeometry

open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace

/-! ## Part 0: closed word count of a fixed-width chunking -/

theorem chunkFuel_length_closed {w : Nat} (hw : 0 < w) :
    forall (fuel : Nat) (p : List Bool), p.length <= fuel ->
      (chunkPayloadWordsFuel w fuel p).length = (p.length + w - 1) / w := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hp
      have hnil : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp only [chunkPayloadWordsFuel, List.length_nil]
      exact (Nat.div_eq_of_lt (show 0 + w - 1 < w by omega)).symm
  | succ fuel ih =>
      intro p hp
      cases p with
      | nil =>
          simp only [chunkPayloadWordsFuel, List.length_nil]
          exact (Nat.div_eq_of_lt (show 0 + w - 1 < w by omega)).symm
      | cons b r =>
          have hdroplen : ((b :: r).drop w).length = (r.length + 1) - w := by
            simp [List.length_drop]
          have hdropfuel : ((b :: r).drop w).length <= fuel := by
            rw [hdroplen]
            simp only [List.length_cons] at hp
            omega
          have hstep :
              (chunkPayloadWordsFuel w (fuel + 1) (b :: r)).length =
                1 + (chunkPayloadWordsFuel w fuel ((b :: r).drop w)).length := by
            simp only [chunkPayloadWordsFuel, List.length_cons]
            omega
          rw [hstep, ih _ hdropfuel, hdroplen]
          simp only [List.length_cons]
          have key : (r.length + 1 - w + w - 1) / w = (r.length + 1 - 1) / w := by
            by_cases hge : w <= r.length + 1
            · congr 1
              omega
            · have h1 : r.length + 1 - w + w - 1 = w - 1 := by omega
              rw [h1, Nat.div_eq_of_lt (show w - 1 < w by omega),
                Nat.div_eq_of_lt (show r.length + 1 - 1 < w by omega)]
          rw [key]
          have hrw : r.length + 1 + w - 1 = (r.length + 1 - 1) + w := by omega
          rw [hrw, Nat.add_div_right (r.length + 1 - 1) hw]
          omega

/-- **Closed form for the chunk count.** Splitting a `width`-bit uniform word
into `w`-bit machine cells yields exactly `ceil (width / w)` cells. -/
theorem chunkPayloadWords_replicate_length {w : Nat} (hw : 0 < w) (width : Nat) :
    (chunkPayloadWords w (List.replicate width false)).length =
      (width + w - 1) / w := by
  unfold chunkPayloadWords
  rw [chunkFuel_length_closed hw _ _ (Nat.le_succ _)]
  simp

/-! ## Part 1: the Nat-only mirror -/

namespace Mirror

/-- Summary base `b(n) = log2 n + 1`. -/
def base (n : Nat) : Nat := Nat.log2 n + 1

/-- Raw block size `2 * b(n)`. -/
def blockSize (n : Nat) : Nat := 2 * base n

/-- Blocks per superblock `b(n)`. -/
def blocksPerSuper (n : Nat) : Nat := base n

/-- Block count `n / b(n)`. -/
def blockCount (n : Nat) : Nat := n / base n

/-- Relative width `2 * (log2 (b n) + 1) + 3`. -/
def relativeWidth (n : Nat) : Nat := 2 * (Nat.log2 (base n) + 1) + 3

/-- Superblock sample count. -/
def superSampleCount (n : Nat) : Nat := blockCount n / blocksPerSuper n + 1

/-- The one frozen machine word width `w(n) = log2 (2n) + 1`. -/
def wordSize (n : Nat) : Nat := Nat.log2 (2 * n) + 1

/-- Superblock sample width, equal to `w(n)`. -/
def superWidth (n : Nat) : Nat := wordSize n

/-- Rank block width. -/
def blockWidth (n : Nat) : Nat := Nat.log2 (wordSize n * wordSize n) + 1

/-- Macro block size. -/
def macroSize (n : Nat) : Nat := blocksPerSuper n * blocksPerSuper n

/-- Macro sample count. -/
def macroSampleCount (n : Nat) : Nat := blockCount n / macroSize n + 1

/-- Sparse offset width. -/
def offsetWidth (n : Nat) : Nat := Nat.log2 (macroSize n) + 1

/-- Local sparse level count. -/
def levelCount (n : Nat) : Nat := offsetWidth n

/-- Global sparse level count. -/
def globalLevelCount (n : Nat) : Nat := Nat.log2 (macroSampleCount n) + 1

/-- Block address width. -/
def blockAddressWidth (n : Nat) : Nat := Nat.log2 (blockCount n) + 1

/-- Fringe chunk width. -/
def fringeChunkBits (n : Nat) : Nat := Nat.log2 (2 * n) / 8 + 1

/-- Local charged level-table domain. -/
def levelDomainLocal (n : Nat) : Nat := macroSize n + 2

/-- Global charged level-table domain. -/
def levelDomainGlobal (n : Nat) : Nat := macroSampleCount n + 2

/-- Charged level-table stored width, as a function of the domain. -/
def levelWidth (d : Nat) : Nat := Nat.log2 (d * (Nat.log2 d + 1)) + 1

/-- Machine cells occupied by one stored word of `width` bits. -/
def cells (n width : Nat) : Nat := (width + wordSize n - 1) / wordSize n

/-- The canonical layout record. -/
def layout (n : Nat) : RelativeRmm.Layout where
  blockSize := blockSize n
  blocksPerSuper := blocksPerSuper n
  blockCount := blockCount n
  relativeWidth := relativeWidth n

/-! Per-table machine word counts. -/

def baselineWords (n : Nat) : Nat := superSampleCount n * cells n (superWidth n)

def minRelWords (n : Nat) : Nat := blockCount n * cells n (relativeWidth n)

def maxRelWords (n : Nat) : Nat := blockCount n * cells n (relativeWidth n)

def argOffsetWords (n : Nat) : Nat := blockCount n * cells n (relativeWidth n)

def localWords (n : Nat) : Nat :=
  macroSampleCount n * (levelCount n * macroSize n) * cells n (offsetWidth n)

def globalWords (n : Nat) : Nat :=
  globalLevelCount n * macroSampleCount n * cells n (blockAddressWidth n)

def localLevelWords (n : Nat) : Nat :=
  levelDomainLocal n * cells n (levelWidth (levelDomainLocal n))

def globalLevelWords (n : Nat) : Nat :=
  levelDomainGlobal n * cells n (levelWidth (levelDomainGlobal n))

/-- The nine interior component offsets. -/
def offsets (n : Nat) : CanonicalRelativeRmmInteriorComponentOffsets where
  baseline := 0
  minRel := baselineWords n
  maxRel := baselineWords n + minRelWords n
  argOffset := baselineWords n + minRelWords n + maxRelWords n
  localOffset := baselineWords n + minRelWords n + maxRelWords n + argOffsetWords n
  globalBlock :=
    baselineWords n + minRelWords n + maxRelWords n + argOffsetWords n +
      localWords n
  localLevel :=
    baselineWords n + minRelWords n + maxRelWords n + argOffsetWords n +
      localWords n + globalWords n
  globalLevel :=
    baselineWords n + minRelWords n + maxRelWords n + argOffsetWords n +
      localWords n + globalWords n + localLevelWords n
  deadAddress :=
    baselineWords n + (minRelWords n + (maxRelWords n + (argOffsetWords n +
      (localWords n + (globalWords n + (localLevelWords n +
        globalLevelWords n))))))

end Mirror

/-! ## Part 2: the summary family, definitionally -/

theorem base_closed (s : CartesianShape) :
    canonicalBPRelativeSummaryBase s = Mirror.base s.size := rfl

theorem blockSizeRaw_closed (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw s = Mirror.blockSize s.size := rfl

theorem blocksPerSuperRaw_closed (s : CartesianShape) :
    canonicalBPRelativeSummaryBlocksPerSuperRaw s =
      Mirror.blocksPerSuper s.size := rfl

theorem blockCountRaw_closed (s : CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw s = Mirror.blockCount s.size := rfl

theorem superCountRaw_closed (s : CartesianShape) :
    canonicalBPRelativeSummarySuperCountRaw s =
      Mirror.superSampleCount s.size := rfl

theorem relativeWidthRaw_closed (s : CartesianShape) :
    canonicalBPRelativeSummaryRelativeWidthRaw s =
      Mirror.relativeWidth s.size := rfl

theorem layout_closed (s : CartesianShape) :
    RelativeRmm.canonicalLayout s = Mirror.layout s.size := rfl

/-! ## Part 3: everything that goes through `bpCode.length = 2 * size` -/

theorem bpLen (s : CartesianShape) : s.bpCode.length = 2 * s.size :=
  CartesianShape.bpCode_length s

theorem summarySuperWidth_closed (s : CartesianShape) :
    canonicalBPRelativeSummarySuperWidth s = Mirror.wordSize s.size := by
  unfold canonicalBPRelativeSummarySuperWidth SuccinctRank.machineWordBits
    Mirror.wordSize
  rw [bpLen]

theorem layoutSuperWidth_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).superWidth s = Mirror.superWidth s.size := by
  unfold RelativeRmm.Layout.superWidth SuccinctRank.machineWordBits
    Mirror.superWidth Mirror.wordSize
  rw [bpLen]

theorem rankWordSize_closed (s : CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize s = Mirror.wordSize s.size := by
  unfold builtRelativeSplitBPCloseRankWordSize SuccinctRank.machineWordBits
    Mirror.wordSize
  rw [bpLen]

theorem rankBlocksPerSuper_closed (s : CartesianShape) :
    builtRelativeSplitBPCloseRankBlocksPerSuper s = Mirror.wordSize s.size := by
  unfold builtRelativeSplitBPCloseRankBlocksPerSuper
  exact rankWordSize_closed s

theorem rankBlockWidth_closed (s : CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth s = Mirror.blockWidth s.size := by
  unfold builtRelativeSplitBPCloseRankBlockWidth Mirror.blockWidth
  rw [rankWordSize_closed]
  rfl

theorem fringeChunkBits_closed (s : CartesianShape) :
    bpFringeChunkBits s.bpCode.length = Mirror.fringeChunkBits s.size := by
  unfold bpFringeChunkBits Mirror.fringeChunkBits
  rw [bpLen]

/-! ## Part 4: layout-derived scalars -/

theorem macroSize_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).macroSize = Mirror.macroSize s.size := rfl

theorem superSampleCount_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).superSampleCount =
      Mirror.superSampleCount s.size := rfl

theorem macroSampleCount_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).macroSampleCount =
      Mirror.macroSampleCount s.size := rfl

theorem offsetWidth_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).offsetWidth = Mirror.offsetWidth s.size := rfl

theorem levelCount_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).levelCount = Mirror.levelCount s.size := rfl

theorem globalLevelCount_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).globalLevelCount =
      Mirror.globalLevelCount s.size := rfl

theorem blockAddressWidth_closed (s : CartesianShape) :
    (RelativeRmm.canonicalLayout s).blockAddressWidth =
      Mirror.blockAddressWidth s.size := rfl

/-! ## Part 5: the super/block overhead budgets -/

theorem superOverhead_closed (s : CartesianShape) :
    sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots s.size =
      16 * (s.size / (Nat.log2 s.size + 1)) := rfl

theorem blockOverhead_closed (s : CartesianShape) :
    logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots s.size =
      64 * ((s.size / (Nat.log2 s.size + 1)) *
        (Nat.log2 (Nat.log2 s.size + 1) + 1)) := rfl

/-! ## Part 6: the eight table machine word counts -/

theorem cells_closed (s : CartesianShape) (width : Nat) :
    (chunkPayloadWords (SuccinctRank.machineWordBits s.bpCode.length)
        (List.replicate width false)).length = Mirror.cells s.size width := by
  rw [chunkPayloadWords_replicate_length
    (SuccinctRank.machineWordBits_pos s.bpCode.length) width]
  unfold Mirror.cells Mirror.wordSize SuccinctRank.machineWordBits
  rw [bpLen]

theorem baselineWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmSummaryTable s).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.baselineWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpSuperblockBaselineEntries_length, cells_closed]
  unfold Mirror.baselineWords
  rw [superSampleCount_closed, layoutSuperWidth_closed]

theorem minRelWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmSummaryTable s).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.minRelWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpBlockRelativeMinExcessEntries_length, cells_closed]
  rfl

theorem maxRelWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmSummaryTable s).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.maxRelWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpBlockRelativeMaxExcessEntries_length, cells_closed]
  rfl

theorem argOffsetWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmSummaryTable s).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.argOffsetWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpBlockArgMinLocalOffsetEntries_length, cells_closed]
  rfl

theorem localWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmInteriorLocalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.localWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpLocalSparseOffsetEntries_length, cells_closed]
  rfl

theorem globalWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmInteriorGlobalTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.globalWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpGlobalSparseBlockEntries_length, cells_closed]
  rfl

theorem localLevelWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmInteriorLocalLevelTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.localLevelWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpSparseLevelEntries_length, cells_closed]
  rfl

theorem globalLevelWords_closed (s : CartesianShape) :
    ((canonicalRelativeRmmInteriorGlobalLevelTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size =
      Mirror.globalLevelWords s.size := by
  rw [GeometryClosure.machineStore_words_size_closed,
    bpSparseLevelEntries_length, cells_closed]
  rfl

/-! ## Part 7: the nine interior component offsets -/

theorem globalLevelMachineStore_words_size (s : CartesianShape) :
    (canonicalRelativeRmmGlobalLevelMachineStore s).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalLevelTable s).table.machineStore
        (SuccinctRank.machineWordBits_pos s.bpCode.length)).store.words.size := rfl

theorem componentStoreWords_closed (s : CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore s).store.words.size =
      (Mirror.offsets s.size).deadAddress := by
  rw [canonicalRelativeRmmInteriorComponentStore_words_size_eq]
  simp only []
  rw [baselineWords_closed, minRelWords_closed, maxRelWords_closed,
    argOffsetWords_closed, localWords_closed, globalWords_closed,
    localLevelWords_closed, globalLevelWords_closed]
  rfl

theorem offsets_closed (s : CartesianShape) :
    canonicalRelativeRmmInteriorComponentOffsets s = Mirror.offsets s.size := by
  unfold canonicalRelativeRmmInteriorComponentOffsets
  simp only [GeometryClosure.localMachineStore_words_size,
    GeometryClosure.globalMachineStore_words_size,
    GeometryClosure.localLevelMachineStore_words_size]
  rw [baselineWords_closed, minRelWords_closed, maxRelWords_closed,
    argOffsetWords_closed, localWords_closed, globalWords_closed,
    localLevelWords_closed, componentStoreWords_closed]
  rfl

/-! ## Part 8: word-width facts about `w(n)` -/

theorem log2_two_mul (n : Nat) (hn : 1 <= n) :
    Nat.log2 (2 * n) = Nat.log2 n + 1 := by
  have hhalf : 2 * n / 2 = n := by omega
  rw [Nat.log2]
  simp only [show 2 * n >= 2 by omega, if_true, hhalf]

theorem wordSize_pos (n : Nat) : 1 <= Mirror.wordSize n := by
  unfold Mirror.wordSize
  omega

theorem lt_two_pow_wordSize (n : Nat) : n < 2 ^ Mirror.wordSize n := by
  unfold Mirror.wordSize
  have h : 2 * n < 2 ^ (Nat.log2 (2 * n) + 1) := Nat.lt_log2_self
  omega

theorem wordSize_eq_of_pos (n : Nat) (hn : 1 <= n) :
    Mirror.wordSize n = Nat.log2 n + 2 := by
  unfold Mirror.wordSize
  rw [log2_two_mul n hn]

/-! ## Part 9: the two components with no proved closed form

`builtRelativeSplitFalseSelectLongSuperRelativeTable` and
`builtRelativeSplitFalseSelectSparseExceptionRelativeTable` have payload
lengths that are only **bounded** by `n`-only budgets, never proved equal to
them.  The two budgets themselves are closed in `n`; the payload lengths are
not known to be. -/

theorem longSuperBudget_closed (n : Nat) :
    SuccinctSelect.compactLongSuperRelativeTableOverhead n =
      1 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 1 := rfl

theorem sparseExceptionBudget_closed (n : Nat) :
    SuccinctSelect.sparseExceptionRelativeTableOverhead n =
      512 * (2 * n / (Nat.log2 (Nat.log2 (2 * n) + 1) + 1)) + 512 := rfl

/-- Only an inequality is available for the long-superblock exception table:
its payload length is bounded by an `n`-only budget, not equal to one. -/
theorem longSuperPayload_only_bounded (s : CartesianShape) :
    (SuccinctSelect.builtRelativeSplitFalseSelectLongSuperRelativeTable
        s).payload.length <=
      SuccinctSelect.compactLongSuperRelativeTableOverhead s.size :=
  SuccinctSelect.compactLongSuperRelativeTable_payload_le_overhead s

/-- Only an inequality is available for the sparse-exception table. -/
theorem sparseExceptionPayload_only_bounded (s : CartesianShape) :
    (SuccinctSelect.builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        s).payload.length <=
      SuccinctSelect.sparseExceptionRelativeTableOverhead s.size :=
  SuccinctSelect.builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
    s

/-! ## Part 10: executed numeric witnesses (evaluations, not theorems) -/

section Witnesses

/-- info: [11, 12, 13] -/
#guard_msgs in
#eval [Mirror.wordSize 512, Mirror.wordSize 1024, Mirror.wordSize 2048]

/-- info: [10, 11, 12] -/
#guard_msgs in
#eval [Mirror.base 512, Mirror.base 1024, Mirror.base 2048]

/-- info: [51, 93, 170] -/
#guard_msgs in
#eval [Mirror.blockCount 512, Mirror.blockCount 1024, Mirror.blockCount 2048]

/-- info: [100, 121, 144] -/
#guard_msgs in
#eval [Mirror.macroSize 512, Mirror.macroSize 1024, Mirror.macroSize 2048]

/-- info: [1, 1, 1] -/
#guard_msgs in
#eval [Mirror.cells 512 (Mirror.relativeWidth 512),
  Mirror.cells 1024 (Mirror.relativeWidth 1024),
  Mirror.cells 2048 (Mirror.relativeWidth 2048)]

end Witnesses

section AxiomAudit

#print axioms RMQ.SuccinctFinal.HeaderGeometry.chunkPayloadWords_replicate_length
#print axioms RMQ.SuccinctFinal.HeaderGeometry.layout_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.rankWordSize_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.rankBlockWidth_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.fringeChunkBits_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.offsets_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.componentStoreWords_closed
#print axioms RMQ.SuccinctFinal.HeaderGeometry.lt_two_pow_wordSize
#print axioms RMQ.SuccinctFinal.HeaderGeometry.longSuperPayload_only_bounded
#print axioms RMQ.SuccinctFinal.HeaderGeometry.sparseExceptionPayload_only_bounded

end AxiomAudit

end HeaderGeometry
end SuccinctFinal
end RMQ

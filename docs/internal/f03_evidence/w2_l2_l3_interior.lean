import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

/-!
W2 -- EG-CP-F03 geometry closure for controller leaves L2 (LCA-close) and
L3 (rank-close), plus the interior macro-hierarchy arm.

Everything is stated with fully qualified names in the theorem statements.
-/

namespace W2I

open RMQ.SuccinctSpace

theorem sum_replicate (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
      omega

/-- `read_exact` forces the machine store to have exactly one word per entry. -/
theorem words_size_eq {entries : List Nat} {width : Nat}
    (t : FixedWidthNatTable entries width) :
    t.store.words.size = entries.length := by
  have key : forall i : Nat,
      (t.store.words[i]? = none) <-> (entries[i]? = none) := by
    intro i
    have h := t.read_exact i
    constructor
    · intro hnone; rw [hnone] at h; simpa using h.symm
    · intro hnone
      rw [hnone] at h
      cases hw : t.store.words[i]? with
      | none => rfl
      | some w => rw [hw] at h; simp at h
  rcases Nat.lt_trichotomy t.store.words.size entries.length with hlt | heq | hgt
  · exfalso
    have h1 : Not (entries[t.store.words.size]? = none) := by
      simp only [List.getElem?_eq_none_iff]
      omega
    exact h1 ((key t.store.words.size).mp
      (by simp only [Array.getElem?_eq_none_iff]; omega))
  · exact heq
  · exfalso
    have h1 : Not (t.store.words[entries.length]? = none) := by
      simp only [Array.getElem?_eq_none_iff]
      omega
    exact h1 ((key entries.length).mpr
      (by simp only [List.getElem?_eq_none_iff]; omega))

/-- Every machine word count is `entries.length * chunkCount width wordSize`. -/
theorem machineWords_length {entries : List Nat} {width wordSize : Nat}
    (t : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    (fixedWidthNatTableMachineWords t wordSize).length =
      entries.length * fixedWidthNatTableMachineChunkCount width wordSize := by
  unfold fixedWidthNatTableMachineWords
  have hconst : forall w, w ∈ t.store.words.toList ->
      (chunkPayloadWords wordSize w).length =
        fixedWidthNatTableMachineChunkCount width wordSize := by
    intro w hmem
    have hlen : w.length = width := by
      rcases List.mem_iff_getElem?.mp hmem with ⟨j, hw⟩
      exact t.word_length_of_get? (by simpa [Array.getElem?_toList] using hw)
    simpa [fixedWidthNatTableMachineChunkCount, hlen] using
      chunkPayloadWords_length_eq_div_add_indicator hwordSize w
  rw [List.length_flatMap]
  have hmapeq :
      (t.store.words.toList.map fun w => (chunkPayloadWords wordSize w).length)
        = t.store.words.toList.map
            (fun _ => fixedWidthNatTableMachineChunkCount width wordSize) :=
    List.map_congr_left hconst
  rw [hmapeq, List.map_const', sum_replicate, Array.length_toList,
    words_size_eq]

theorem machineStore_size {entries : List Nat} {width wordSize : Nat}
    (t : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    (t.machineStore hwordSize).store.words.size =
      entries.length * fixedWidthNatTableMachineChunkCount width wordSize := by
  show (fixedWidthNatTableMachineWords t wordSize).toArray.size = _
  rw [List.size_toArray, machineWords_length t hwordSize]

/-- Two tables with the same entry count and field width have machine stores of
the same size, whatever their contents. -/
theorem machineStore_size_congr
    {e1 e2 : List Nat} {w1 w2 wordSize : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (h1 : 0 < wordSize) (h2 : 0 < wordSize)
    (hlen : e1.length = e2.length) (hw : w1 = w2) :
    (t1.machineStore h1).store.words.size =
      (t2.machineStore h2).store.words.size := by
  rw [machineStore_size t1 h1, machineStore_size t2 h2, hlen, hw]

/-- The machine read program depends on the table only through the number of
entries and the field width. -/
theorem machineReadComputationAt_congr
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (hlen : e1.length = e2.length) (hw : w1 = w2)
    (wordSize base deadAddress i : Nat) :
    t1.machineReadComputationAt wordSize base deadAddress i =
      t2.machineReadComputationAt wordSize base deadAddress i := by
  unfold RMQ.SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
  rw [hlen, hw]

end W2I



namespace W2IL

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose

theorem bpCodeLen_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) : a.bpCode.length = b.bpCode.length := by
  rw [Cartesian.CartesianShape.bpCode_length,
    Cartesian.CartesianShape.bpCode_length, h]

theorem layout_congr {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    RelativeRmm.canonicalLayout a = RelativeRmm.canonicalLayout b := by
  unfold RelativeRmm.canonicalLayout canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummaryRelativeWidthRaw
    canonicalBPRelativeSummaryBase
  rw [h]

/-! ### Entry-count and width congruences for the eight tables. -/

theorem baseline_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpSuperblockBaselineEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blocksPerSuper
        (RelativeRmm.canonicalLayout a).superSampleCount).length =
      (bpSuperblockBaselineEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blocksPerSuper
        (RelativeRmm.canonicalLayout b).superSampleCount).length := by
  rw [bpSuperblockBaselineEntries_length, bpSuperblockBaselineEntries_length,
    layout_congr h]

theorem minRel_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpBlockRelativeMinExcessEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blocksPerSuper
        (RelativeRmm.canonicalLayout a).blockCount).length =
      (bpBlockRelativeMinExcessEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blocksPerSuper
        (RelativeRmm.canonicalLayout b).blockCount).length := by
  rw [bpBlockRelativeMinExcessEntries_length,
    bpBlockRelativeMinExcessEntries_length, layout_congr h]

theorem maxRel_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpBlockRelativeMaxExcessEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blocksPerSuper
        (RelativeRmm.canonicalLayout a).blockCount).length =
      (bpBlockRelativeMaxExcessEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blocksPerSuper
        (RelativeRmm.canonicalLayout b).blockCount).length := by
  rw [bpBlockRelativeMaxExcessEntries_length,
    bpBlockRelativeMaxExcessEntries_length, layout_congr h]

theorem argOffset_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpBlockArgMinLocalOffsetEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blockCount).length =
      (bpBlockArgMinLocalOffsetEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blockCount).length := by
  rw [bpBlockArgMinLocalOffsetEntries_length,
    bpBlockArgMinLocalOffsetEntries_length, layout_congr h]

theorem localOffset_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpLocalSparseOffsetEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blockCount
        (RelativeRmm.canonicalLayout a).macroSize
        (RelativeRmm.canonicalLayout a).macroSampleCount
        (RelativeRmm.canonicalLayout a).levelCount).length =
      (bpLocalSparseOffsetEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blockCount
        (RelativeRmm.canonicalLayout b).macroSize
        (RelativeRmm.canonicalLayout b).macroSampleCount
        (RelativeRmm.canonicalLayout b).levelCount).length := by
  rw [bpLocalSparseOffsetEntries_length, bpLocalSparseOffsetEntries_length,
    layout_congr h]

theorem globalBlock_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpGlobalSparseBlockEntries a (RelativeRmm.canonicalLayout a).blockSize
        (RelativeRmm.canonicalLayout a).blockCount
        (RelativeRmm.canonicalLayout a).macroSize
        (RelativeRmm.canonicalLayout a).macroSampleCount
        (RelativeRmm.canonicalLayout a).globalLevelCount).length =
      (bpGlobalSparseBlockEntries b (RelativeRmm.canonicalLayout b).blockSize
        (RelativeRmm.canonicalLayout b).blockCount
        (RelativeRmm.canonicalLayout b).macroSize
        (RelativeRmm.canonicalLayout b).macroSampleCount
        (RelativeRmm.canonicalLayout b).globalLevelCount).length := by
  rw [bpGlobalSparseBlockEntries_length, bpGlobalSparseBlockEntries_length,
    layout_congr h]

theorem localLevel_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpSparseLevelEntries
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout a).macroSize)).length =
      (bpSparseLevelEntries
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout b).macroSize)).length := by
  rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]

theorem globalLevel_len {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (bpSparseLevelEntries
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout a).macroSampleCount)).length =
      (bpSparseLevelEntries
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout b).macroSampleCount)).length := by
  rw [bpSparseLevelEntries_length, bpSparseLevelEntries_length, layout_congr h]




/-! ### Machine-store sizes for the eight component tables. -/

theorem mstore_size_congr
    {e1 e2 : List Nat} {w1 w2 ws1 ws2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (h1 : 0 < ws1) (h2 : 0 < ws2)
    (hel : e1.length = e2.length) (hw : w1 = w2) (hws : ws1 = ws2) :
    (t1.machineStore h1).store.words.size =
      (t2.machineStore h2).store.words.size := by
  rw [W2I.machineStore_size t1 h1, W2I.machineStore_size t2 h2, hel, hw, hws]

theorem summaryBaseline_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).baselineTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  refine mstore_size_congr _ _ _ _ (baseline_len h) ?_ (by rw [bpCodeLen_congr h])
  show RelativeRmm.Layout.superWidth _ a = RelativeRmm.Layout.superWidth _ b
  unfold RelativeRmm.Layout.superWidth
  rw [bpCodeLen_congr h]

theorem summaryMinRel_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).minRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (minRel_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem summaryMaxRel_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).maxRelTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (maxRel_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem summaryArgOffset_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmSummaryTable a).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmSummaryTable b).argOffsetTable.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (argOffset_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem localTable_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (localOffset_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem globalTable_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (globalBlock_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem localLevelTable_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorLocalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorLocalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (localLevel_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])

theorem globalLevelTable_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    ((canonicalRelativeRmmInteriorGlobalLevelTable a).table.machineStore
        (SuccinctRank.machineWordBits_pos a.bpCode.length)).store.words.size =
      ((canonicalRelativeRmmInteriorGlobalLevelTable b).table.machineStore
        (SuccinctRank.machineWordBits_pos b.bpCode.length)).store.words.size := by
  exact mstore_size_congr _ _ _ _ (globalLevel_len h) (by rw [layout_congr h])
    (by rw [bpCodeLen_congr h])


/-! ### The nine component offsets. -/

theorem componentStore_size {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) :
    (canonicalRelativeRmmInteriorComponentStore a).store.words.size =
      (canonicalRelativeRmmInteriorComponentStore b).store.words.size := by
  unfold canonicalRelativeRmmInteriorComponentStore
    canonicalRelativeRmmSummaryMachineStore canonicalRelativeRmmLocalMachineStore
    canonicalRelativeRmmGlobalMachineStore
    canonicalRelativeRmmLocalLevelMachineStore
    canonicalRelativeRmmGlobalLevelMachineStore
  rw [<- Array.length_toList, <- Array.length_toList]
  simp only [SuccinctSpace.BoundedPayloadWordStore.append_words_toList,
    List.length_append, Array.length_toList]
  rw [summaryBaseline_size h, summaryMinRel_size h, summaryMaxRel_size h,
    summaryArgOffset_size h, localTable_size h, globalTable_size h,
    localLevelTable_size h, globalLevelTable_size h]

theorem offsets_congr {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    canonicalRelativeRmmInteriorComponentOffsets a =
      canonicalRelativeRmmInteriorComponentOffsets b := by
  unfold canonicalRelativeRmmInteriorComponentOffsets
    canonicalRelativeRmmLocalMachineStore canonicalRelativeRmmGlobalMachineStore
    canonicalRelativeRmmLocalLevelMachineStore
  simp only [summaryBaseline_size h, summaryMinRel_size h, summaryMaxRel_size h,
    summaryArgOffset_size h, localTable_size h, globalTable_size h,
    localLevelTable_size h, componentStore_size h]


/-! ### The interior computation tree. -/

/-- Any layout field is size-only.  Stated pointwise so that no rewrite ever
touches the layout term itself (the tables are indexed by it). -/
theorem lfield {a b : Cartesian.CartesianShape} (h : a.size = b.size)
    {alpha : Type} (f : RelativeRmm.Layout -> alpha) :
    f (RelativeRmm.canonicalLayout a) = f (RelativeRmm.canonicalLayout b) := by
  rw [layout_congr h]

theorem superWidth_congr {a b : Cartesian.CartesianShape} (h : a.size = b.size) :
    (RelativeRmm.canonicalLayout a).superWidth a =
      (RelativeRmm.canonicalLayout b).superWidth b := by
  unfold RelativeRmm.Layout.superWidth
  rw [bpCodeLen_congr h]

theorem readNat_congr {a b : Cartesian.CartesianShape} (h : a.size = b.size)
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2)
    (hel : e1.length = e2.length) (hw : w1 = w2) (base i : Nat) :
    canonicalRelativeRmmMachineReadNatComputation a t1 base i =
      canonicalRelativeRmmMachineReadNatComputation b t2 base i := by
  unfold canonicalRelativeRmmMachineReadNatComputation
  rw [bpCodeLen_congr h, offsets_congr h]
  exact W2I.machineReadComputationAt_congr t1 t2 hel hw _ _ _ _

theorem summaryComputation_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineSummaryComputation a block =
      canonicalRelativeRmmMachineSummaryComputation b block := by
  unfold canonicalRelativeRmmMachineSummaryComputation
  simp only [lfield h RelativeRmm.Layout.blocksPerSuper, offsets_congr h,
    readNat_congr h (canonicalRelativeRmmSummaryTable a).baselineTable
      (canonicalRelativeRmmSummaryTable b).baselineTable
      (baseline_len h) (superWidth_congr h),
    readNat_congr h (canonicalRelativeRmmSummaryTable a).minRelTable
      (canonicalRelativeRmmSummaryTable b).minRelTable
      (minRel_len h) (lfield h RelativeRmm.Layout.relativeWidth),
    readNat_congr h (canonicalRelativeRmmSummaryTable a).maxRelTable
      (canonicalRelativeRmmSummaryTable b).maxRelTable
      (maxRel_len h) (lfield h RelativeRmm.Layout.relativeWidth),
    readNat_congr h (canonicalRelativeRmmSummaryTable a).argOffsetTable
      (canonicalRelativeRmmSummaryTable b).argOffsetTable
      (argOffset_len h) (lfield h RelativeRmm.Layout.relativeWidth)]

theorem minCandidate_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (block : Nat) :
    canonicalRelativeRmmMachineMinCandidateComputation a block =
      canonicalRelativeRmmMachineMinCandidateComputation b block := by
  unfold canonicalRelativeRmmMachineMinCandidateComputation
  simp only [lfield h RelativeRmm.Layout.blockSize,
    lfield h RelativeRmm.Layout.blocksPerSuper, summaryComputation_congr h]

theorem localSpan_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroIdx localStart level : Nat) :
    canonicalRelativeRmmMachineLocalSpanCandidateComputation a
        macroIdx localStart level =
      canonicalRelativeRmmMachineLocalSpanCandidateComputation b
        macroIdx localStart level := by
  unfold canonicalRelativeRmmMachineLocalSpanCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSize,
    lfield h RelativeRmm.Layout.levelCount, offsets_congr h,
    readNat_congr h (canonicalRelativeRmmInteriorLocalTable a).table
      (canonicalRelativeRmmInteriorLocalTable b).table
      (localOffset_len h) (lfield h RelativeRmm.Layout.offsetWidth),
    minCandidate_congr h]

theorem globalSpan_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroStart level : Nat) :
    canonicalRelativeRmmMachineGlobalSpanCandidateComputation a
        macroStart level =
      canonicalRelativeRmmMachineGlobalSpanCandidateComputation b
        macroStart level := by
  unfold canonicalRelativeRmmMachineGlobalSpanCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSampleCount, offsets_congr h,
    readNat_congr h (canonicalRelativeRmmInteriorGlobalTable a).table
      (canonicalRelativeRmmInteriorGlobalTable b).table
      (globalBlock_len h) (lfield h RelativeRmm.Layout.blockAddressWidth),
    minCandidate_congr h]

theorem localTwoSpan_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroIdx localStart count : Nat) :
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation a
        macroIdx localStart count =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation b
        macroIdx localStart count := by
  unfold canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSize, offsets_congr h,
    readNat_congr h (canonicalRelativeRmmInteriorLocalLevelTable a).table
      (canonicalRelativeRmmInteriorLocalLevelTable b).table
      (localLevel_len h)
      (show bpSparseLevelWidth
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout a).macroSize) =
          bpSparseLevelWidth
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout b).macroSize) by
        rw [lfield h RelativeRmm.Layout.macroSize]),
    localSpan_congr h]

theorem globalTwoSpan_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroStart macroSpanCount : Nat) :
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation a
        macroStart macroSpanCount =
      canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation b
        macroStart macroSpanCount := by
  unfold canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSampleCount, offsets_congr h,
    readNat_congr h (canonicalRelativeRmmInteriorGlobalLevelTable a).table
      (canonicalRelativeRmmInteriorGlobalLevelTable b).table
      (globalLevel_len h)
      (show bpSparseLevelWidth
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout a).macroSampleCount) =
          bpSparseLevelWidth
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout b).macroSampleCount) by
        rw [lfield h RelativeRmm.Layout.macroSampleCount]),
    globalSpan_congr h]

theorem adjacentMacro_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroStart localStart rightCount : Nat) :
    canonicalRelativeRmmMachineAdjacentMacroCandidateComputation a
        macroStart localStart rightCount =
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation b
        macroStart localStart rightCount := by
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSize, localTwoSpan_congr h]

theorem leftMiddleMacro_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (macroStart localStart middleMacroCount : Nat) :
    canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation a
        macroStart localStart middleMacroCount =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation b
        macroStart localStart middleMacroCount := by
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSize, localTwoSpan_congr h,
    globalTwoSpan_congr h]

theorem crossMacro_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    canonicalRelativeRmmMachineCrossMacroCandidateComputation a
        macroStart localStart middleMacroCount rightCount =
      canonicalRelativeRmmMachineCrossMacroCandidateComputation b
        macroStart localStart middleMacroCount rightCount := by
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  simp only [lfield h RelativeRmm.Layout.macroSize, localTwoSpan_congr h,
    globalTwoSpan_congr h]

theorem rangeMinComputation_congr {a b : Cartesian.CartesianShape}
    (h : a.size = b.size) (startBlock count : Nat) :
    canonicalRelativeRmmInteriorRangeMinComputation a startBlock count =
      canonicalRelativeRmmInteriorRangeMinComputation b startBlock count := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  simp only [lfield h RelativeRmm.Layout.macroSize, localTwoSpan_congr h,
    adjacentMacro_congr h, leftMiddleMacro_congr h, crossMacro_congr h]

/-- **The interior obligation, discharged.** -/
theorem interior_congr {a b : Cartesian.CartesianShape} (h : a.size = b.size)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (store : WordRAM.ReadStore) (startBlock count : Nat) :
    ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a segments store startBlock count =
      ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b segments store startBlock count := by
  unfold ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  rw [rangeMinComputation_congr h]

end W2IL



namespace W2

/-! ############################################################
    ## Part 0.  Shared length congruence
    ############################################################ -/

theorem bpCodeLen_congr {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size) : a.bpCode.length = b.bpCode.length := by
  rw [RMQ.Cartesian.CartesianShape.bpCode_length,
    RMQ.Cartesian.CartesianShape.bpCode_length, h]

/-! ############################################################
    ## Part 1.  L3 -- the rank-close leaf
    ############################################################ -/

/-- Restated from `docs/internal/f03_evidence/t1map_obligations.lean` (O3). -/
theorem chunkedRank_geometry_only
    {b1 b2 : List Bool} {s1 k1 q1 s2 k2 q2 : Nat}
    (d1 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b1 s1 k1 q1)
    (d2 : RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData b2 s2 k2 q2)
    (hlen : b1.length = b2.length)
    (hword : d1.wordSize = d2.wordSize)
    (hblocks : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : RMQ.WordRAM.ReadStore)
    (superSegment blockSegment wordSegment chunkSegment c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos =
      d2.bpChunkedRankTraceResultWithStore store superSegment blockSegment
        wordSegment chunkSegment c target pos := by
  unfold RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  simp only [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset,
    RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos,
    hlen, hword, hblocks]

theorem rank_wordSize_eq (shape : RMQ.Cartesian.CartesianShape) :
    (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData shape).wordSize =
      RMQ.SuccinctRank.machineWordBits (2 * shape.size) := by
  show RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize shape = _
  unfold RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize
  rw [RMQ.Cartesian.CartesianShape.bpCode_length]

theorem rank_blocksPerSuper_eq (shape : RMQ.Cartesian.CartesianShape) :
    (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData shape).blocksPerSuper =
      RMQ.SuccinctRank.machineWordBits (2 * shape.size) := by
  show RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlocksPerSuper shape = _
  unfold RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlocksPerSuper
    RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize
  rw [RMQ.Cartesian.CartesianShape.bpCode_length]

/-- **L3.**  The rank-close leaf is size-only, for every store, every rank
segment base and every position.  No threshold, no regime restriction. -/
theorem L3_route_shape_size_only {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (base pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store base pos =
      RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store base pos := by
  unfold RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [bpCodeLen_congr h]
  exact chunkedRank_geometry_only _ _ (bpCodeLen_congr h)
    (by rw [rank_wordSize_eq, rank_wordSize_eq, h])
    (by rw [rank_blocksPerSuper_eq, rank_blocksPerSuper_eq, h])
    _ _ _ _ _ _ _ _

/-! ############################################################
    ## Part 2.  L2 -- layout scalars and the BP window
    ############################################################ -/

theorem summaryBase_congr {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size) :
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBase a =
      RMQ.SuccinctClose.canonicalBPRelativeSummaryBase b := by
  unfold RMQ.SuccinctClose.canonicalBPRelativeSummaryBase
  rw [h]

theorem blockSizeRaw_congr {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size) :
    RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw a =
      RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw b := by
  unfold RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
  rw [summaryBase_congr h]

theorem windowBase_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length) (blockSize close : Nat) :
    RMQ.SuccinctClose.localBPWindowBase a blockSize close =
      RMQ.SuccinctClose.localBPWindowBase b blockSize close := by
  unfold RMQ.SuccinctClose.localBPWindowBase
  rw [hlen]

theorem windowBits_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore) (blockSize close : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
        a store blockSize close =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
        b store blockSize close := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResultWithStore
  rw [hlen]

/-! ## The three chunked fringe consumers -/

theorem sameBlockSeeded_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize leftClose rightClose seed : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose rightClose seed =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose rightClose seed := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseSeededTraceResultAtSegmentWithStore
  rw [windowBits_congr hlen, windowBase_congr hlen, hlen]

theorem leftFringeSeeded_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize leftClose seed =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize leftClose seed := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [windowBits_congr hlen, windowBase_congr hlen, hlen]

theorem rightFringeSeeded_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    (store : RMQ.WordRAM.ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        a store fringeSegment blockSize rightClose seed =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        b store fringeSegment blockSize rightClose seed := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [windowBits_congr hlen, windowBase_congr hlen, hlen]

/-! ## The rank seed -/

theorem seed_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (blockSize close : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
        a rankA blockSize close =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
        b rankB blockSize close := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
  simp only [windowBase_congr hlen, hrank]

/-! ############################################################
    ## Part 3.  The two arms of the L2 dispatcher
    ############################################################ -/

/-- **Same-block arm: unconditional.** -/
theorem sameBlockArm_congr {a b : RMQ.Cartesian.CartesianShape}
    (hlen : a.bpCode.length = b.bpCode.length)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        a rankA fringeSegment store blockSize leftClose rightClose =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        b rankB fringeSegment store blockSize leftClose rightClose := by
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
  simp only [seed_congr hlen hrank, sameBlockSeeded_congr hlen]

/--
**The one residual of L2.**  The interior (macro-hierarchy) replay at a fixed
segment map and a fixed store agrees for two equal-size shapes.

Every other shape-dependent value in the LCA-close leaf is discharged
unconditionally below; this predicate is exactly what is left.
-/
def InteriorArmObligation
    (a b : RMQ.Cartesian.CartesianShape)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (store : RMQ.WordRAM.ReadStore) : Prop :=
  forall startBlock count : Nat,
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a segments store startBlock count =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b segments store startBlock count

/-- **The interior obligation is discharged**, by `W2IL.interior_congr`. -/
theorem interiorArmObligation_of_size {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (store : RMQ.WordRAM.ReadStore) : InteriorArmObligation a b segments store :=
  fun startBlock count => W2IL.interior_congr h segments store startBlock count

/-- **Cross-block arm: reduces to the interior obligation and nothing else.** -/
theorem crossBlockArm_congr {a b : RMQ.Cartesian.CartesianShape}
    (hsize : a.size = b.size)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (hinterior : InteriorArmObligation a b segments store)
    (leftClose rightClose : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        a rankA segments fringeSegment store leftClose rightClose =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        b rankB segments fringeSegment store leftClose rightClose := by
  have hlen : a.bpCode.length = b.bpCode.length := bpCodeLen_congr hsize
  unfold InteriorArmObligation at hinterior
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  simp only [blockSizeRaw_congr hsize, seed_congr hlen hrank,
    leftFringeSeeded_congr hlen, hinterior, rightFringeSeeded_congr hlen]

/-! ############################################################
    ## Part 4.  The L2 dispatcher and the L2 route theorem
    ############################################################ -/

/-- The generic supplied-store LCA-close dispatcher is size-only, given the
interior obligation.  The route selector
`blockOfClose blockSize leftClose = blockOfClose blockSize rightClose` is
discharged here: `blockSize` is `canonicalBPRelativeSummaryBlockSizeRaw`, which
is size-only. -/
theorem lcaClose_congr {a b : RMQ.Cartesian.CartesianShape}
    (hsize : a.size = b.size)
    {rankA rankB : Nat -> RMQ.WordRAM.TraceResult Nat}
    (hrank : forall pos, rankA pos = rankB pos)
    (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : RMQ.WordRAM.ReadStore)
    (hinterior : InteriorArmObligation a b segments store)
    (sameBlockSegment leftClose rightClose : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        a rankA segments fringeSegment store sameBlockSegment
        leftClose rightClose =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
        b rankB segments fringeSegment store sameBlockSegment
        leftClose rightClose := by
  have hlen : a.bpCode.length = b.bpCode.length := bpCodeLen_congr hsize
  unfold RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  simp only [blockSizeRaw_congr hsize, sameBlockArm_congr hlen hrank,
    crossBlockArm_congr hsize hrank segments fringeSegment store hinterior]

/-- **L2.**  The controller's LCA-close leaf is size-only, modulo the single
named interior obligation. -/
theorem L2_route_shape_size_only {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (lc rc : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store lc rc =
      RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store lc rc := by
  unfold RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact lcaClose_congr h
    (fun pos => L3_route_shape_size_only h store _ pos)
    _ _ store
    (interiorArmObligation_of_size h
      RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments store)
    _ lc rc

end W2

/-! ## Statement pins and axiom audit -/

#check @W2.L3_route_shape_size_only
#check @W2.L2_route_shape_size_only
#check @W2.sameBlockArm_congr
#check @W2.crossBlockArm_congr
#check @W2.InteriorArmObligation

#print axioms W2.L3_route_shape_size_only
#print axioms W2.L2_route_shape_size_only
#print axioms W2.sameBlockArm_congr
#print axioms W2.crossBlockArm_congr


namespace W2Verify

/-! ## 1.  Two shapes: equal size, provably different `bpCode`. -/

def shapeL : RMQ.Cartesian.CartesianShape :=
  RMQ.Cartesian.CartesianShape.node
    (RMQ.Cartesian.CartesianShape.node
      RMQ.Cartesian.CartesianShape.empty RMQ.Cartesian.CartesianShape.empty)
    RMQ.Cartesian.CartesianShape.empty

def shapeR : RMQ.Cartesian.CartesianShape :=
  RMQ.Cartesian.CartesianShape.node
    RMQ.Cartesian.CartesianShape.empty
    (RMQ.Cartesian.CartesianShape.node
      RMQ.Cartesian.CartesianShape.empty RMQ.Cartesian.CartesianShape.empty)

theorem sizes_agree : shapeL.size = shapeR.size := by decide

theorem codes_differ : Not (shapeL.bpCode = shapeR.bpCode) := by decide

/-- ...and they really are different shapes. -/
theorem shapes_differ : Not (shapeL = shapeR) := by
  intro h; exact codes_differ (congrArg RMQ.Cartesian.CartesianShape.bpCode h)

/-! ## 2.  Expected types, written independently of the proof file. -/

def ExpectedL3Type : Prop :=
  forall {a b : RMQ.Cartesian.CartesianShape}, a.size = b.size ->
    forall (store : RMQ.WordRAM.ReadStore) (base pos : Nat),
      RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          a store base pos =
        RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          b store base pos

def ExpectedInteriorObligation
    (a b : RMQ.Cartesian.CartesianShape) (store : RMQ.WordRAM.ReadStore) : Prop :=
  forall startBlock count : Nat,
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        a RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments store
        startBlock count =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        b RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments store
        startBlock count

def ExpectedL2Type : Prop :=
  forall {a b : RMQ.Cartesian.CartesianShape}, a.size = b.size ->
    forall (store : RMQ.WordRAM.ReadStore) (lc rc : Nat),
      RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          a store lc rc =
        RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          b store lc rc

def ExpectedInteriorType : Prop :=
  forall {a b : RMQ.Cartesian.CartesianShape}, a.size = b.size ->
    forall (segments : RMQ.SuccinctClose.BPRelativeRmmInteriorTraceSegments)
      (store : RMQ.WordRAM.ReadStore) (startBlock count : Nat),
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
          a segments store startBlock count =
        RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
          b segments store startBlock count

/-! ## 3.  The interior obligation is satisfiable (it is reflexive). -/

theorem interiorObligation_refl (a : RMQ.Cartesian.CartesianShape)
    (store : RMQ.WordRAM.ReadStore) : ExpectedInteriorObligation a a store :=
  fun _ _ => rfl

/-! ## 4.  `bpFringeChunkBits` is manifestly length-only. -/

theorem fringeChunkBits_is_a_function_of_a_Nat :
    RMQ.SuccinctClose.bpFringeChunkBits = fun m => Nat.log2 m / 8 + 1 := rfl

theorem fringeChunkBits_congr {a b : RMQ.Cartesian.CartesianShape}
    (h : a.size = b.size) :
    RMQ.SuccinctClose.bpFringeChunkBits a.bpCode.length =
      RMQ.SuccinctClose.bpFringeChunkBits b.bpCode.length := by
  rw [RMQ.Cartesian.CartesianShape.bpCode_length,
    RMQ.Cartesian.CartesianShape.bpCode_length, h]


/-! ## 5.  Instantiations at the two witness shapes and expected-type pins. -/

/-- L3 at two shapes with equal size and provably different `bpCode`. -/
theorem L3_at_witnesses (store : RMQ.WordRAM.ReadStore) (base pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shapeL store base pos =
      RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shapeR store base pos :=
  W2.L3_route_shape_size_only sizes_agree store base pos

/-- L2 at the same two shapes, given the interior obligation for them. -/
theorem L2_at_witnesses (store : RMQ.WordRAM.ReadStore) (lc rc : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shapeL store lc rc =
      RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shapeR store lc rc :=
  W2.L2_route_shape_size_only sizes_agree store lc rc

/-- The same-block arm, which is unconditional, at the two witness shapes. -/
theorem sameBlockArm_at_witnesses
    (store : RMQ.WordRAM.ReadStore) (fringeSegment blockSize lc rc : Nat) :
    RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shapeL
        (RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shapeL store RMQ.SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase)
        fringeSegment store blockSize lc rc =
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
        shapeR
        (RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shapeR store RMQ.SuccinctFinal.concreteBPNativeRankCloseTraceSegmentBase)
        fringeSegment store blockSize lc rc :=
  W2.sameBlockArm_congr (W2.bpCodeLen_congr sizes_agree)
    (fun pos => W2.L3_route_shape_size_only sizes_agree store _ pos)
    fringeSegment store blockSize lc rc

/-- Expected-type pins: each is inhabited by the theorem VALUE alone. -/
theorem L3_pin : ExpectedL3Type := @W2.L3_route_shape_size_only

theorem L2_pin : ExpectedL2Type := @W2.L2_route_shape_size_only

theorem interior_pin : ExpectedInteriorType := @W2IL.interior_congr

/-! ## 6.  Anti-bypass: the theorems really take only `a.size = b.size`. -/

theorem antibypass_L3
    (a b : RMQ.Cartesian.CartesianShape) (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (base pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        a store base pos =
      RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        b store base pos :=
  W2.L3_route_shape_size_only h store base pos

theorem antibypass_L2
    (a b : RMQ.Cartesian.CartesianShape) (h : a.size = b.size)
    (store : RMQ.WordRAM.ReadStore) (lc rc : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        a store lc rc =
      RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        b store lc rc :=
  W2.L2_route_shape_size_only h store lc rc

end W2Verify

#print axioms W2Verify.L3_at_witnesses
#print axioms W2Verify.L2_at_witnesses
#print axioms W2Verify.sameBlockArm_at_witnesses
#print axioms W2Verify.L3_pin
#print axioms W2Verify.L2_pin
#print axioms W2Verify.interior_pin
#print axioms W2IL.interior_congr
#print axioms W2Verify.codes_differ

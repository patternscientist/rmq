import RMQ.Core.WordRAM.Bitvector.ReaderInterface
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-! # Canonical supplied-store select semantics

Only segment zero is normalized. The entry directories, flag ranks, and
shared chunk tables are read from the existing generic supplied store.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace GenericSelect SuccinctFinal SuccinctFinal.PackedCellProbe

theorem canonical_bitWords_target_eq (bits : List Bool) (target : Bool) :
    (sparseExceptionSelectData bits target).bitWords.store.words =
      (sparseExceptionSelectData bits false).bitWords.store.words := rfl

theorem canonical_select_chunk_geometry (bits : List Bool) (target : Bool) :
    let d := sparseExceptionSelectData bits target
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    0 < c ∧ d.wordSize ≤ 8 * c ∧
      d.longFlagRankData.wordSize ≤ 8 * c ∧
      d.sparseDirectory.rankData.wordSize ≤ 8 * c := by
  let d := sparseExceptionSelectData bits target
  have hmachine : SuccinctRank.machineWordBits bits.length ≤
      8 * SuccinctClose.bpFringeChunkBits (2 * bits.length) :=
    Nat.le_trans (SuccinctRank.machineWordBits_mono_le (by omega))
      (SuccinctClose.machineWordBits_le_8_mul_bpFringeChunkBits (2 * bits.length))
  exact ⟨SuccinctClose.bpFringeChunkBits_pos _,
    Nat.le_trans d.wordSize_le_machine hmachine,
    Nat.le_trans d.longFlagRank_wordSize_le_machine hmachine,
    Nat.le_trans d.sparseDirectory.rank_wordSize_le_machine hmachine⟩

@[simp] theorem genericReadStore_raw (bits : List Bool) (target : Bool) (i : Nat) :
    (genericReadStore bits target).readWord? 0 i =
      ((sparseExceptionSelectData bits target).bitWords.store.words[i]?).map
        (normalize target) := rfl

@[simp] theorem genericReadStore_rankTable (bits : List Bool) (target : Bool) (i : Nat) :
    (genericReadStore bits target).readWord? 21 i =
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words[i]? := rfl

@[simp] theorem genericReadStore_selectTable (bits : List Bool) (target : Bool) (i : Nat) :
    (genericReadStore bits target).readWord? 22 i =
      (SuccinctClose.bpChunkSelectTable
        (SuccinctClose.bpFringeChunkBits (2 * bits.length)) false).store.words[i]? := rfl

private theorem normalized_chunk_rank_value
    {store : WordRAM.ReadStore} {rankSegment c : Nat}
    (hc : 0 < c)
    (hrank : ∀ i, store.readWord? rankSegment i =
      (SuccinctClose.bpFringeChunkTable c).store.words[i]?)
    (target : Bool) (word : List Bool) (limit : Nat)
    (hlen : word.length ≤ 8 * c) :
    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
      store rankSegment c false (normalize target word) limit).value =
      RAM.boolRankPrefix target word limit := by
  have h := congrArg Costed.value
    (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
      (SuccinctClose.bpFringeChunkTable c) hrank c false (normalize target word) limit)
  change (SuccinctClose.bpChunkedWordRankTraceResultAtSegmentWithStore
    store rankSegment c false (normalize target word) limit).value =
    (SuccinctClose.bpChunkedWordRankCosted
    (SuccinctClose.bpFringeChunkTable c) c false (normalize target word) limit).value at h
  rw [h, SuccinctClose.bpChunkedWordRankCosted_value c hc false
    (normalize target word) limit (by simpa using hlen),
    Succinct.ram_boolRankPrefix_eq_rankPrefix, rankPrefix_normalize,
    Succinct.ram_boolRankPrefix_eq_rankPrefix]

private theorem normalized_chunk_select_value
    {store : WordRAM.ReadStore} {rankSegment selectSegment c : Nat}
    (hc : 0 < c)
    (hrank : ∀ i, store.readWord? rankSegment i =
      (SuccinctClose.bpFringeChunkTable c).store.words[i]?)
    (hselect : ∀ i, store.readWord? selectSegment i =
      (SuccinctClose.bpChunkSelectTable c false).store.words[i]?)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (hlen : word.length ≤ 8 * c) :
    (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
      store rankSegment selectSegment c false (normalize target word) occurrence).value =
      RAM.boolSelectInWord target word occurrence := by
  have h := congrArg Costed.value
    (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore_toCosted_of_agree
      (SuccinctClose.bpFringeChunkTable c) (SuccinctClose.bpChunkSelectTable c false)
      hrank hselect c false (normalize target word) occurrence)
  change (SuccinctClose.bpChunkedWordSelectTraceResultAtSegmentsWithStore
    store rankSegment selectSegment c false (normalize target word) occurrence).value =
    (SuccinctClose.bpChunkedWordSelectCosted
    (SuccinctClose.bpFringeChunkTable c) (SuccinctClose.bpChunkSelectTable c false)
    c false (normalize target word) occurrence).value at h
  rw [h, SuccinctClose.bpChunkedWordSelectCosted_value c hc false
    (normalize target word) occurrence (by simpa using hlen),
    Succinct.ram_boolSelectInWord_eq_select, select_normalize,
    Succinct.ram_boolSelectInWord_eq_select]

/-- Normalization transports the complete dense two-word computation, including
its two chunked rank calls and whichever chunked select call is taken. -/
theorem normalized_dense_value
    {bits : List Bool} {wordSize : Nat}
    (bitWords : BoundedPayloadWordStore bits wordSize)
    {store : WordRAM.ReadStore} {wordSegment rankSegment selectSegment c : Nat}
    (hc : 0 < c) (hws : wordSize ≤ 8 * c) (target : Bool)
    (hword : ∀ i, store.readWord? wordSegment i =
      (bitWords.store.words[i]?).map (normalize target))
    (hrank : ∀ i, store.readWord? rankSegment i =
      (SuccinctClose.bpFringeChunkTable c).store.words[i]?)
    (hselect : ∀ i, store.readWord? selectSegment i =
      (SuccinctClose.bpChunkSelectTable c false).store.words[i]?)
    (basePosition baseOccurrence occurrence : Nat) :
    (packedDenseTwoWordSelectRead wordSegment rankSegment selectSegment c false
      store wordSize basePosition baseOccurrence occurrence).value =
      (denseTwoWordSelectCosted target bitWords basePosition baseOccurrence occurrence).value := by
  unfold packedDenseTwoWordSelectRead denseTwoWordSelectCosted
  cases hfirst : (bitWords.store.readWordCosted (basePosition / wordSize)).value with
  | none =>
      have hfirst' : bitWords.store.words[basePosition / wordSize]? = none := hfirst
      simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
        SuccinctClose.bpWordReadTraceResult, hword, hfirst', Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      have hfirst' : bitWords.store.words[basePosition / wordSize]? = some firstWord := hfirst
      have hlen : firstWord.length ≤ 8 * c :=
        Nat.le_trans (bitWords.read_word_length_le hfirst) hws
      have hbefore := normalized_chunk_rank_value hc hrank target firstWord
        (basePosition - basePosition / wordSize * wordSize) hlen
      have hupto := normalized_chunk_rank_value hc hrank target firstWord firstWord.length hlen
      by_cases hchoose : occurrence - baseOccurrence <
          RAM.boolRankPrefix target firstWord firstWord.length -
            RAM.boolRankPrefix target firstWord
              (basePosition - basePosition / wordSize * wordSize)
      · have hsel := normalized_chunk_select_value hc hrank hselect target firstWord
          (RAM.boolRankPrefix target firstWord
            (basePosition - basePosition / wordSize * wordSize) +
              (occurrence - baseOccurrence)) hlen
        simp [-normalize_eq_map, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
          WordRAM.TraceResult.pure, SuccinctClose.bpWordReadTraceResult,
          hword, hfirst', normalize_length, hbefore, hupto, hchoose, hsel,
          Costed.bind, Costed.map, Costed.pure, hfirst]
      · cases hsecond :
          (bitWords.store.readWordCosted (basePosition / wordSize + 1)).value with
        | none =>
            have hsecond' : bitWords.store.words[basePosition / wordSize + 1]? = none := hsecond
            simp [-normalize_eq_map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
              SuccinctClose.bpWordReadTraceResult, hword, hfirst', hsecond',
              normalize_length, hbefore, hupto, hchoose,
              Costed.bind, Costed.pure, hfirst, hsecond]
        | some secondWord =>
            have hsecond' : bitWords.store.words[basePosition / wordSize + 1]? =
                some secondWord := hsecond
            have hlen2 : secondWord.length ≤ 8 * c :=
              Nat.le_trans (bitWords.read_word_length_le hsecond) hws
            have hsel := normalized_chunk_select_value hc hrank hselect target secondWord
              (occurrence - baseOccurrence -
                (RAM.boolRankPrefix target firstWord firstWord.length -
                  RAM.boolRankPrefix target firstWord
                    (basePosition - basePosition / wordSize * wordSize))) hlen2
            simp [-normalize_eq_map, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
              WordRAM.TraceResult.pure, SuccinctClose.bpWordReadTraceResult,
              hword, hfirst', hsecond', normalize_length, hbefore, hupto, hchoose, hsel,
              Costed.bind, Costed.map, Costed.pure, hfirst, hsecond]

private theorem packed_entry_value_of_agree
    {entries : List SparseDenseSelectDenseLocalEntry} {width : Nat}
    (table : FixedWidthSparseDenseSelectDenseLocalEntryTable entries width)
    (layout : SparseDenseEntryTableTraceSegmentBases) (store : WordRAM.ReadStore)
    (h1 : ∀ i, store.readWord? layout.baseOccurrence i =
      table.baseOccurrenceTable.store.words[i]?)
    (h2 : ∀ i, store.readWord? layout.baseWordIndex i =
      table.baseWordIndexTable.store.words[i]?)
    (h3 : ∀ i, store.readWord? layout.rankBefore i =
      table.rankBeforeTable.store.words[i]?)
    (h4 : ∀ i, store.readWord? layout.firstOffset i =
      table.firstOffsetTable.store.words[i]?) (i : Nat) :
    (packedSelectEntryRead layout store i).value = (table.readCosted i).value := by
  change FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
    ((store.readWord? layout.baseOccurrence i).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.baseWordIndex i).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.rankBefore i).map WordRAM.bitsToNatLE)
    ((store.readWord? layout.firstOffset i).map WordRAM.bitsToNatLE) = _
  rw [h1, h2, h3, h4]
  rw [funext WordRAMBridge.bitsToNatLE_eq]
  rfl

/-- The exact scalar supplied-store select expression consumed by the generic
controller refinement. Both flag rank geometries use one block per super. -/
def canonicalSelectRead (bits : List Bool) (target : Bool) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
    21 22 (genericReadStore bits target) c false
    (occurrenceCount bits target) d.superStride d.wordSize
    d.localSlotsPerSuper d.localStride d.longFlagBits.length
    d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
    d.sparseDirectory.rankData.wordSize 1 d.localStride idx

/-- Select constrains only its actual read segments. In particular, a caller
may fill segments 17 through 20 with independent rank data. -/
def SelectStoreAgrees (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore) : Prop :=
  ∀ segment index, segment < 17 ∨ segment = 21 ∨ segment = 22 →
    store.readWord? segment index = (genericReadStore bits target).readWord? segment index

/-- The whole normalized supplied-store controller has the value of the
existing target-aware chunked computation on the same original bit list. The
store is arbitrary away from the segments the select computation reads. -/
theorem selectRead_value_eq_of_agree (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) (hagree : SelectStoreAgrees bits target store) (idx : Nat) :
    let d := sparseExceptionSelectData bits target
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
      21 22 store c false (occurrenceCount bits target) d.superStride d.wordSize
      d.localSlotsPerSuper d.localStride d.longFlagBits.length
      d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
      d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
      (d.bpChunkedSelectCosted c idx).value := by
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  let layout := concreteBPNativeSelectCloseTraceSegmentLayout
  obtain ⟨hc, hbw, _, _⟩ := canonical_select_chunk_geometry bits target
  have hsuper (i : Nat) :
      (packedSelectEntryRead layout.superTable store i).value =
        (d.superTable.readCosted i).value :=
    packed_entry_value_of_agree d.superTable layout.superTable store
      (fun i => hagree 1 i (by omega)) (fun i => hagree 2 i (by omega))
      (fun i => hagree 3 i (by omega)) (fun i => hagree 4 i (by omega)) i
  have hlocal (i : Nat) :
      (packedSelectEntryRead layout.localTable store i).value =
        (d.localTable.readCosted i).value :=
    packed_entry_value_of_agree d.localTable layout.localTable store
      (fun i => hagree 5 i (by omega)) (fun i => hagree 6 i (by omega))
      (fun i => hagree 7 i (by omega)) (fun i => hagree 8 i (by omega)) i
  have hlong (i : Nat) :
      (packedRankRead 9 10 11 21 c true store d.longFlagBits.length
        d.longFlagRankData.wordSize 1 i).value =
        (d.longFlagRankData.bpChunkedRankCosted c true i).value := by
    change (d.longFlagRankData.bpChunkedRankTraceResultWithStore
      store 9 10 11 21 c true i).value = _
    exact congrArg Costed.value
      (d.longFlagRankData.bpChunkedRankTraceResultWithStore_toCosted_of_agree
        (store := store) (superSegment := 9) (blockSegment := 10)
        (wordSegment := 11) (chunkSegment := 21) (c := c) (target := true)
        (fun i => hagree 9 i (by omega)) (fun i => hagree 10 i (by omega))
        (fun i => hagree 11 i (by omega)) (fun i => hagree 21 i (by omega)) i)
  have hrelative (base slot : Nat) :
      (bpRelativeOffsetReadTraceResultWithStore store 12 base slot).value =
        (relativeOffsetReadCosted d.longSuperRelativeTable base slot).value := by
    exact congrArg Costed.value
      (bpRelativeOffsetReadTraceResultWithStore_toCosted_of_agree
        d.longSuperRelativeTable (store := store) (segment := 12)
        (fun i => hagree 12 i (by omega)) base slot)
  have hsparse (base slot occurrence : Nat) :
      (packedSparseDirectoryRead layout.sparseDirectory 21 store c
        d.sparseDirectory.flagBits.length d.sparseDirectory.rankData.wordSize
        1 d.localStride base slot occurrence).value =
        (d.sparseDirectory.bpChunkedReadCosted c base slot occurrence).value := by
    change (d.sparseDirectory.bpChunkedReadTraceResultWithStore
      layout.sparseDirectory 21 store c base slot occurrence).value = _
    exact congrArg Costed.value
      (d.sparseDirectory.bpChunkedReadTraceResultWithStore_toCosted_of_agree
        (layout := layout.sparseDirectory) (chunkSegment := 21) (store := store) (c := c)
        (fun i => hagree 13 i (by omega)) (fun i => hagree 14 i (by omega))
        (fun i => hagree 15 i (by omega)) (fun i => hagree 21 i (by omega))
        (fun i => hagree 16 i (by omega)) base slot occurrence)
  have hdense (base occurrence q : Nat) :
      (packedDenseTwoWordSelectRead 0 21 22 c false store d.wordSize
        base occurrence q).value =
        (bpChunkedDenseTwoWordSelectCosted c target d.bitWords
          base occurrence q).value := by
    exact (normalized_dense_value d.bitWords (store := store) (wordSegment := 0)
      (rankSegment := 21) (selectSegment := 22) (c := c) hc hbw target
      (fun i => hagree 0 i (by omega)) (fun i => hagree 21 i (by omega))
      (fun i => hagree 22 i (by omega)) base occurrence q).trans
        (bpChunkedDenseTwoWordSelectCosted_value_eq c hc target d.bitWords
          hbw base occurrence q).symm
  change (packedSelectCloseRead layout 21 22 store c false
    (occurrenceCount bits target) d.superStride d.wordSize d.localSlotsPerSuper
    d.localStride d.longFlagBits.length d.longFlagRankData.wordSize 1
    d.sparseDirectory.flagBits.length d.sparseDirectory.rankData.wordSize 1
    d.localStride idx).value = (d.bpChunkedSelectCosted c idx).value
  simp only [packedSelectCloseRead,
    SparseExceptionSelectData.bpChunkedSelectCosted,
    SparseExceptionSelectData.queryOccurrence,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    Costed.bind, Costed.pure, hsuper, hlocal]
  by_cases hvalid : idx < occurrenceCount bits target
  · rw [if_pos hvalid, if_pos hvalid]
    cases hsuperValue : (d.superTable.readCosted (selectSuperSlot idx d.superStride)).value with
    | none => rfl
    | some super =>
        by_cases hmark : relativeSplitSelectEntryIsMarked super = true
        · simp only [hmark, ↓reduceIte]
          change (bpRelativeOffsetReadTraceResultWithStore store 12
            (relativeSplitSelectEntryBasePosition d.wordSize super)
            (relativeSplitSelectLongCompactSlot
              (packedRankRead 9 10 11 21 c true store d.longFlagBits.length
                d.longFlagRankData.wordSize 1 (selectSuperSlot idx d.superStride)).value
              (idx - super.baseOccurrence) d.superStride)).value = _
          rw [hlong, hrelative]
        · simp only [hmark]
          cases hlocalValue : (d.localTable.readCosted
            (relativeSplitSelectLocalSlot idx d.superStride
              d.localSlotsPerSuper d.localStride super)).value with
          | none => rfl
          | some loc =>
              by_cases hsmark : relativeSplitSelectEntryIsMarked loc = true
              · simp only [hsmark, ↓reduceIte]
                exact hsparse _ _ _
              · simp only [hsmark]
                exact hdense _ _ _
  · rw [if_neg hvalid, if_neg hvalid]

theorem canonicalSelectRead_value_eq (bits : List Bool) (target : Bool) (idx : Nat) :
    (canonicalSelectRead bits target idx).value =
      ((sparseExceptionSelectData bits target).bpChunkedSelectCosted
        (SuccinctClose.bpFringeChunkBits (2 * bits.length)) idx).value :=
  selectRead_value_eq_of_agree bits target (genericReadStore bits target)
    (fun _ _ _ => rfl) idx

/-- The same all-input semantic endpoint remains true when other store
segments are populated, provided the actual select read segments agree. -/
theorem selectRead_value_of_agree (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) (hagree : SelectStoreAgrees bits target store) (idx : Nat) :
    let d := sparseExceptionSelectData bits target
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
      21 22 store c false (occurrenceCount bits target) d.superStride d.wordSize
      d.localSlotsPerSuper d.localStride d.longFlagBits.length
      d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
      d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
      Succinct.select target bits idx := by
  dsimp only
  rw [selectRead_value_eq_of_agree bits target store hagree]
  obtain ⟨hc, hbw, hlf, hsd⟩ := canonical_select_chunk_geometry bits target
  exact (sparseExceptionSelectData bits target).bpChunkedSelectCosted_exact hc hbw hlf hsd idx

/-- Canonical all-size, both-target select semantics of the actual supplied
store and scalar controller expression, including every invalid occurrence. -/
theorem canonicalSelectRead_value (bits : List Bool) (target : Bool) (idx : Nat) :
    (canonicalSelectRead bits target idx).value = Succinct.select target bits idx := by
  rw [canonicalSelectRead_value_eq]
  obtain ⟨hc, hbw, hlf, hsd⟩ := canonical_select_chunk_geometry bits target
  exact (sparseExceptionSelectData bits target).bpChunkedSelectCosted_exact hc hbw hlf hsd idx

-- The direct consumer pins every scalar of the controller-facing expression.
example (bits : List Bool) (target : Bool) (idx : Nat) :
    let d := sparseExceptionSelectData bits target
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
      21 22 (genericReadStore bits target) c false
      (occurrenceCount bits target) d.superStride d.wordSize
      d.localSlotsPerSuper d.localStride d.longFlagBits.length
      d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
      d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
      Succinct.select target bits idx :=
  canonicalSelectRead_value bits target idx

/-- The all-input value contract rejects replacing the controller by a constant
missing answer. The counterexample belongs to the same quantified domain. -/
theorem constant_none_select_rejected :
    ¬ (∀ (bits : List Bool) (target : Bool) (idx : Nat),
      (WordRAM.TraceResult.pure (none : Option Nat)).value =
        Succinct.select target bits idx) := by
  intro h
  have hbad := h [true] true 0
  change (none : Option Nat) = some 0 at hbad
  cases hbad

end RMQ.PackedBitvector

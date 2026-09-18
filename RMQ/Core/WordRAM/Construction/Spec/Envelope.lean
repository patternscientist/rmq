import RMQ.Core.WordRAM.Construction.Spec.Plan

/-!
# PRE-1 S1: literal all-size envelopes for the emission plan

Machine-free specification layer (outside the builder firewall). The cost and
workspace stages need every size-only loop count of the emission plan bounded
by a literal linear function of `n`, at every size (no `LittleOLinear`, which
is not literal). This module states those envelopes about the reference
quantities themselves:

* the whole payload plan has at most `400000 * (n + 1) - 2` bits, from the
  existing literal overhead envelopes (`packedReviewerCellBound_add_two_le_linearCapacity`);
* every table segment, and therefore every table's entry count (each width is
  positive), and both raw flag vectors are below the same literal bound;
* the old bit string, the dense bit buffer and the emitted word count are below
  literal linear bounds (the dense buffer holds at most `400576 * n + 401726` bits);
* the interior layout counts: `blockCount ≤ n`, `superSampleCount ≤ n + 1`,
  `macroSampleCount ≤ n + 1`, `globalLevelCount ≤ n + 2`, and the local memo
  grid `levelCount * blockCount ≤ 3 * n`;
* the microtable row scans: `bpFringeChunkRowCount c * (c + 1) ≤ 256 * (n + 1)`
  and `bpChunkSelectRowCount c * (c + 1) ≤ 64 * (n + 1)` at `c = bpFringeChunkBits (2 * n)`;
* a halving `log2` loop on `x` runs at most `x + 1` rounds.

The constants are crude on purpose (ruling Q7); nothing here claims tightness.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Spec

open RMQ.Cartesian RMQ.SuccinctSpace
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-! ## Table lengths -/

theorem flattenPayloadWords_map_natToBitsLE_length (width : Nat) :
    ∀ entries : List Nat,
      (flattenPayloadWords (entries.map (natToBitsLE width))).length = entries.length * width
  | [] => by simp [flattenPayloadWords]
  | e :: rest => by
      simp only [List.map_cons, flattenPayloadWords, List.length_append, natToBitsLE_length,
        flattenPayloadWords_map_natToBitsLE_length width rest, List.length_cons, Nat.succ_mul]
      omega

theorem tableBits_length (entries : List Nat) (width : Nat) :
    (tableBits entries width).length = entries.length * width :=
  flattenPayloadWords_map_natToBitsLE_length width entries

theorem entries_length_le_tableBits (entries : List Nat) {width : Nat} (hw : 0 < width) :
    entries.length ≤ (tableBits entries width).length := by
  rw [tableBits_length]
  exact Nat.le_mul_of_pos_right _ hw

theorem length_le_flatten_of_mem {α : Type} :
    ∀ {L : List (List α)} {seg : List α}, seg ∈ L → seg.length ≤ L.flatten.length
  | _ :: _, _, .head _ => by simp
  | _ :: rest, _, .tail _ h => by
      have := length_le_flatten_of_mem h
      simp only [List.flatten_cons, List.length_append]
      omega

/-! ## The whole payload plan -/

/-- **Payload envelope.** The BP code, the 18 access segments, the eight interior
tables and both microtables together have at most `400000 * (n + 1) - 2` bits. -/
theorem planPayload_length_add_two_le (shape : CartesianShape) :
    (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape).length + 2 ≤
      400000 * (shape.size + 1) := by
  rw [planPayload_length]
  have h1 := packedReviewerPayloadLength_le_bound shape
  have h2 := packedReviewerCellBound_add_two_le_linearCapacity shape.size
  unfold packedReviewerCellBound at h2
  omega

theorem accessSegments_length_add_two_le (shape : CartesianShape) :
    ∀ seg ∈ accessSegments shape, seg.length + 2 ≤ 400000 * (shape.size + 1) := by
  intro seg hseg
  have h := planPayload_length_add_two_le shape
  have hm := length_le_flatten_of_mem hseg
  simp only [List.length_append] at h
  omega

theorem interiorSegments_length_add_two_le (shape : CartesianShape) :
    ∀ seg ∈ interiorSegments shape, seg.length + 2 ≤ 400000 * (shape.size + 1) := by
  intro seg hseg
  have h := planPayload_length_add_two_le shape
  have hm := length_le_flatten_of_mem hseg
  simp only [List.length_append] at h
  omega

theorem microtableSegments_length_add_two_le (shape : CartesianShape) :
    (fringeSegment shape).length + 2 ≤ 400000 * (shape.size + 1) ∧
      (selectChunkSegment shape).length + 2 ≤ 400000 * (shape.size + 1) := by
  have h := planPayload_length_add_two_le shape
  simp only [List.length_append] at h
  omega

/-! ## Entry counts (loop bounds of every table emission) -/

theorem entries_le_of_mem_segments {L : List (List Bool)} {entries : List Nat} {width B : Nat}
    (hw : 0 < width) (hmem : tableBits entries width ∈ L)
    (hL : ∀ seg ∈ L, seg.length + 2 ≤ B) : entries.length ≤ B := by
  have h1 := entries_length_le_tableBits entries hw
  have h2 := hL _ hmem
  omega

theorem superFieldWidth_pos (bits : List Bool) : 0 < GenericSelect.superFieldWidth bits :=
  SuccinctRank.machineWordBits_pos _

theorem sparseExceptionRelativeWidth_pos (bits : List Bool) :
    0 < GenericSelect.sparseExceptionRelativeWidth bits :=
  SuccinctRank.machineWordBits_pos _

/-- **Access entry counts.** Every access table's entry list and both raw flag
vectors have at most `400000 * (n + 1)` elements. -/
theorem accessEntryCounts_le (shape : CartesianShape) :
    let b := shape.bpCode
    let ws := SuccinctRank.machineWordBits b.length
    let longBits := GenericSelect.longSuperFlagBits b false
    let longWs := SuccinctRank.machineWordBits longBits.length
    let sparseBits := GenericSelect.sparseExceptionEffectiveFlagBits b false
    let sparseWs := SuccinctRank.machineWordBits sparseBits.length
    let B := 400000 * (shape.size + 1)
    (SuccinctRank.canonicalSuperRankEntries false b ws ws).length ≤ B ∧
    (SuccinctRank.canonicalBlockRankEntries false b ws ws).length ≤ B ∧
    (GenericSelect.superEntries b false).length ≤ B ∧
    (GenericSelect.localEntries b false).length ≤ B ∧
    (SuccinctRank.canonicalSuperRankEntries true longBits longWs 1).length ≤ B ∧
    (SuccinctRank.canonicalBlockRankEntries true longBits longWs 1).length ≤ B ∧
    longBits.length ≤ B ∧
    (GenericSelect.longSuperRelativeEntries b false).length ≤ B ∧
    (SuccinctRank.canonicalSuperRankEntries true sparseBits sparseWs 1).length ≤ B ∧
    (SuccinctRank.canonicalBlockRankEntries true sparseBits sparseWs 1).length ≤ B ∧
    sparseBits.length ≤ B ∧
    (GenericSelect.sparseExceptionRelativeEntries b false).length ≤ B := by
  intro b ws longBits longWs sparseBits sparseWs B
  have hL := accessSegments_length_add_two_le shape
  have hmem : ∀ (k : Nat) (hk : k < (accessSegments shape).length),
      (accessSegments shape)[k] ∈ accessSegments shape := fun k hk => List.getElem_mem hk
  have hpos := SuccinctRank.machineWordBits_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact entries_le_of_mem_segments (hpos _) (hmem 0 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 1 (by simp)) hL
  · have h := entries_le_of_mem_segments (superFieldWidth_pos b) (hmem 2 (by simp)) hL
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences] using h
  · have h := entries_le_of_mem_segments (sparseExceptionRelativeWidth_pos b) (hmem 6 (by simp)) hL
    simpa [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences] using h
  · exact entries_le_of_mem_segments (hpos _) (hmem 10 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 11 (by simp)) hL
  · have h := hL _ (hmem 12 (by simp))
    exact Nat.le_trans (Nat.le_add_right _ 2) h
  · exact entries_le_of_mem_segments (hpos _) (hmem 13 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 14 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 15 (by simp)) hL
  · have h := hL _ (hmem 16 (by simp))
    exact Nat.le_trans (Nat.le_add_right _ 2) h
  · exact entries_le_of_mem_segments (sparseExceptionRelativeWidth_pos b) (hmem 17 (by simp)) hL

/-- The select slot counts (super and local loop bounds). -/
theorem selectSlotCounts_le (shape : CartesianShape) :
    GenericSelect.superSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1) ∧
      GenericSelect.localSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1) := by
  have h := accessEntryCounts_le shape
  simp only [GenericSelect.superEntries_length, GenericSelect.localEntries_length] at h
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- **Interior entry counts.** Every interior table's entry list has at most
`400000 * (n + 1)` elements. -/
theorem interiorEntryCounts_le (shape : CartesianShape) :
    let L := SuccinctClose.RelativeRmm.canonicalLayout shape
    let B := 400000 * (shape.size + 1)
    (SuccinctClose.bpSuperblockBaselineEntries shape L.blockSize L.blocksPerSuper
        L.superSampleCount).length ≤ B ∧
    (SuccinctClose.bpBlockRelativeMinExcessEntries shape L.blockSize L.blocksPerSuper
        L.blockCount).length ≤ B ∧
    (SuccinctClose.bpBlockRelativeMaxExcessEntries shape L.blockSize L.blocksPerSuper
        L.blockCount).length ≤ B ∧
    (SuccinctClose.bpBlockArgMinLocalOffsetEntries shape L.blockSize L.blockCount).length ≤ B ∧
    (SuccinctClose.bpLocalSparseOffsetEntries shape L.blockSize L.blockCount
        L.macroSize L.macroSampleCount L.levelCount).length ≤ B ∧
    (SuccinctClose.bpGlobalSparseBlockEntries shape L.blockSize L.blockCount
        L.macroSize L.macroSampleCount L.globalLevelCount).length ≤ B ∧
    (SuccinctClose.bpSparseLevelEntries (SuccinctClose.bpSparseLevelDomain L.macroSize)).length ≤ B ∧
    (SuccinctClose.bpSparseLevelEntries
        (SuccinctClose.bpSparseLevelDomain L.macroSampleCount)).length ≤ B := by
  intro L B
  have hL := interiorSegments_length_add_two_le shape
  have hmem : ∀ (k : Nat) (hk : k < (interiorSegments shape).length),
      (interiorSegments shape)[k] ∈ interiorSegments shape := fun k hk => List.getElem_mem hk
  have hpos := SuccinctRank.machineWordBits_pos
  have hrel : 0 < L.relativeWidth := by
    show 0 < SuccinctClose.canonicalBPRelativeSummaryRelativeWidthRaw shape
    unfold SuccinctClose.canonicalBPRelativeSummaryRelativeWidthRaw
    omega
  have hlevel : ∀ d, 0 < SuccinctClose.bpSparseLevelWidth d := fun d => by
    unfold SuccinctClose.bpSparseLevelWidth
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact entries_le_of_mem_segments (hpos _) (hmem 0 (by simp)) hL
  · exact entries_le_of_mem_segments hrel (hmem 1 (by simp)) hL
  · exact entries_le_of_mem_segments hrel (hmem 2 (by simp)) hL
  · exact entries_le_of_mem_segments hrel (hmem 3 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 4 (by simp)) hL
  · exact entries_le_of_mem_segments (hpos _) (hmem 5 (by simp)) hL
  · exact entries_le_of_mem_segments (hlevel _) (hmem 6 (by simp)) hL
  · exact entries_le_of_mem_segments (hlevel _) (hmem 7 (by simp)) hL

/-- **Microtable row counts.** -/
theorem microtableRowCounts_le (shape : CartesianShape) :
    (SuccinctClose.bpFringeChunkEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length ≤
        400000 * (shape.size + 1) ∧
      (SuccinctClose.bpChunkSelectEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length ≤
        400000 * (shape.size + 1) := by
  have h := microtableSegments_length_add_two_le shape
  have hf := entries_length_le_tableBits
    (SuccinctClose.bpFringeChunkEntries (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
    (width := SuccinctClose.bpFringeChunkEntryWidth
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
    (by unfold SuccinctClose.bpFringeChunkEntryWidth; omega)
  have hs := entries_length_le_tableBits
    (SuccinctClose.bpChunkSelectEntries (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false)
    (width := SuccinctClose.bpChunkSelectEntryWidth
      (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
    (by unfold SuccinctClose.bpChunkSelectEntryWidth; omega)
  have h1 : (tableBits (SuccinctClose.bpFringeChunkEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
      (SuccinctClose.bpFringeChunkEntryWidth
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length))).length + 2 ≤
      400000 * (shape.size + 1) := h.1
  have h2 : (tableBits (SuccinctClose.bpChunkSelectEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false)
      (SuccinctClose.bpChunkSelectEntryWidth
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length))).length + 2 ≤
      400000 * (shape.size + 1) := h.2
  exact ⟨by omega, by omega⟩

/-! ## Old bit string, dense buffer and emitted words -/

theorem oldBits_le (n lc sc : Nat) :
    packedReviewerCellCount n lc sc * packedReviewerCellWidth n ≤
      packedReviewerPayloadLength n lc sc + 2 * packedReviewerCellWidth n := by
  have h := GenericSelect.selectCeilDiv_mul_le_add (packedReviewerPayloadLength n lc sc)
    (packedReviewerCellWidth n)
  unfold packedReviewerCellCount
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem denseBits_le (bits W : Nat) :
    GenericSelect.selectCeilDiv bits W * W ≤ bits + W :=
  GenericSelect.selectCeilDiv_mul_le_add bits W

theorem wordWidth_le_linear (n : Nat) : wordWidth n ≤ 192 * n + 576 := by
  have h := wordWidth_le_log n
  have hl := Nat.log2_le_self (n + 2)
  omega

/-- **Buffer envelope.** For every input, the dense bit buffer of the plan
(`count * W` bits, both paddings included) is at most `400576 * n + 401726`
bits, and the old bit string is at most `400384 * n + 401150` bits. -/
theorem planBuffer_le (xs : List Int) :
    let shape := SuccinctClassic.cartesianShape xs
    let n := xs.length
    let lc := longCount shape
    let sc := packedReviewerSparseCount shape
    let oldBits := packedReviewerCellCount n lc sc * packedReviewerCellWidth n
    let W := wordWidth n
    oldBits ≤ 400384 * n + 401150 ∧
      GenericSelect.selectCeilDiv oldBits W * W ≤ 400576 * n + 401726 := by
  intro shape n lc sc oldBits W
  have hsize : shape.size = n := packedReviewerCartesianShape_size xs
  have hpay0 := planPayload_length_add_two_le shape
  rw [planPayload_length, hsize] at hpay0
  have hpay : packedReviewerPayloadLength n lc sc + 2 ≤ 400000 * (n + 1) := hpay0
  have hold : oldBits ≤ packedReviewerPayloadLength n lc sc + 2 * packedReviewerCellWidth n :=
    oldBits_le n lc sc
  have hdense := denseBits_le oldBits W
  have hlt := oldWidth_lt_wordWidth n
  have hW := wordWidth_le_linear n
  constructor <;> omega

/-- **Emitted-word envelope.** -/
theorem buildMemory_length_le (xs : List Int) :
    (buildMemory xs).length ≤ 400576 * xs.length + 401900 := by
  have hplan := buildMemory_eq_plan xs
  have hbuf := (planBuffer_le xs).2
  simp only at hplan hbuf
  rw [hplan, List.length_append, metadataOf_length, List.length_map, List.length_range]
  have hWpos := wordWidth_pos xs.length
  have hcount := Nat.le_mul_of_pos_right
    (GenericSelect.selectCeilDiv
      (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
        (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
        packedReviewerCellWidth xs.length) (wordWidth xs.length)) hWpos
  omega

/-! ## Interior layout counts -/

theorem canonicalLayout_blockCount_le (shape : CartesianShape) :
    (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount ≤ shape.size :=
  Nat.div_le_self _ _

theorem canonicalLayout_superSampleCount_le (shape : CartesianShape) :
    (SuccinctClose.RelativeRmm.canonicalLayout shape).superSampleCount ≤ shape.size + 1 := by
  have h := canonicalLayout_blockCount_le shape
  have h2 := Nat.div_le_self (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
    (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
  show (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount /
      (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper + 1 ≤ _
  omega

theorem canonicalLayout_macroSampleCount_le (shape : CartesianShape) :
    (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount ≤ shape.size + 1 := by
  have h := canonicalLayout_blockCount_le shape
  have h2 := Nat.div_le_self (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
    (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
  show (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount /
      (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize + 1 ≤ _
  omega

theorem canonicalLayout_globalLevelCount_le (shape : CartesianShape) :
    (SuccinctClose.RelativeRmm.canonicalLayout shape).globalLevelCount ≤ shape.size + 2 := by
  have h := canonicalLayout_macroSampleCount_le shape
  have h2 := Nat.log2_le_self (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
  show Nat.log2 (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount + 1 ≤ _
  omega

/-- **Local memo grid.** The doubling memo over `levelCount` levels and
`blockCount` blocks has at most `3 * n` cells. -/
theorem canonicalLayout_levelCount_mul_blockCount_le (shape : CartesianShape) :
    (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount *
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount ≤ 3 * shape.size := by
  let base := Nat.log2 shape.size + 1
  show (Nat.log2 (base * base) + 1) * (shape.size / base) ≤ 3 * shape.size
  have hbase : base ≤ 2 ^ base := nat_le_two_pow base
  have hsq : base * base ≤ 2 ^ (2 * base) := by
    have := Nat.mul_le_mul hbase hbase
    rw [← Nat.pow_add] at this
    rw [Nat.two_mul]
    exact this
  have hlog : Nat.log2 (base * base) ≤ 2 * base := by
    have hself := Nat.log2_le_self (base * base)
    by_cases hz : base * base = 0
    · rw [hz, Nat.log2_zero]
      omega
    · have hlt : Nat.log2 (base * base) < 2 * base + 1 := by
        rw [Nat.log2_lt hz, Nat.pow_succ]
        omega
      omega
  have hdiv : base * (shape.size / base) ≤ shape.size := Nat.mul_div_le shape.size base
  have hdiv' : shape.size / base ≤ shape.size := Nat.div_le_self _ _
  calc (Nat.log2 (base * base) + 1) * (shape.size / base)
      ≤ (2 * base + 1) * (shape.size / base) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * (base * (shape.size / base)) + shape.size / base := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    _ ≤ 3 * shape.size := by omega

/-! ## Microtable row scans -/

/-- **Fringe row scan.** Scanning `c + 1` positions for each fringe row costs at
most `256 * (n + 1)` in total, at `c = bpFringeChunkBits (2 * n)`. -/
theorem fringeRows_mul_scan_le (n : Nat) :
    SuccinctClose.bpFringeChunkRowCount (SuccinctClose.bpFringeChunkBits (2 * n)) *
        (SuccinctClose.bpFringeChunkBits (2 * n) + 1) ≤ 256 * (n + 1) := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hrows := SuccinctClose.bpFringeChunkRowCount_le_two_pow c
  have hscan : c + 1 ≤ 2 ^ (c + 1) := nat_le_two_pow _
  have hprod : SuccinctClose.bpFringeChunkRowCount c * (c + 1) ≤ 2 ^ (4 * c + 3) := by
    calc SuccinctClose.bpFringeChunkRowCount c * (c + 1)
        ≤ 2 ^ (3 * c + 2) * 2 ^ (c + 1) := Nat.mul_le_mul hrows hscan
      _ = 2 ^ (4 * c + 3) := by rw [← Nat.pow_add]; congr 1; omega
  have hc : c = Nat.log2 (2 * n) / 8 + 1 := rfl
  have hexp : 4 * c + 3 ≤ Nat.log2 (2 * n) + 7 := by rw [hc]; omega
  have hmono : 2 ^ (4 * c + 3) ≤ 2 ^ (Nat.log2 (2 * n) + 7) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hpow7 : (2 : Nat) ^ 7 = 128 := by decide
  cases n with
  | zero =>
      simp [SuccinctClose.bpFringeChunkRowCount, SuccinctClose.bpFringeChunkBits, Nat.log2_zero]
  | succ m =>
      have hself : 2 ^ Nat.log2 (2 * (m + 1)) ≤ 2 * (m + 1) := Nat.log2_self_le (by omega)
      have hfactor : 2 ^ (Nat.log2 (2 * (m + 1)) + 7) = 128 * 2 ^ Nat.log2 (2 * (m + 1)) := by
        rw [Nat.pow_add, hpow7, Nat.mul_comm]
      rw [hfactor] at hmono
      have hscaled := Nat.mul_le_mul_left 128 hself
      show SuccinctClose.bpFringeChunkRowCount c * (c + 1) ≤ 256 * (m + 1 + 1)
      omega

/-- **Select-chunk row scan.** -/
theorem selectRows_mul_scan_le (n : Nat) :
    SuccinctClose.bpChunkSelectRowCount (SuccinctClose.bpFringeChunkBits (2 * n)) *
        (SuccinctClose.bpFringeChunkBits (2 * n) + 1) ≤ 64 * (n + 1) := by
  let c := SuccinctClose.bpFringeChunkBits (2 * n)
  have hrows := SuccinctClose.bpChunkSelectRowCount_le_two_pow c
  have hscan : c + 1 ≤ 2 ^ (c + 1) := nat_le_two_pow _
  have hprod : SuccinctClose.bpChunkSelectRowCount c * (c + 1) ≤ 2 ^ (3 * c + 2) := by
    calc SuccinctClose.bpChunkSelectRowCount c * (c + 1)
        ≤ 2 ^ (2 * c + 1) * 2 ^ (c + 1) := Nat.mul_le_mul hrows hscan
      _ = 2 ^ (3 * c + 2) := by rw [← Nat.pow_add]; congr 1; omega
  have hc : c = Nat.log2 (2 * n) / 8 + 1 := rfl
  have hexp : 3 * c + 2 ≤ Nat.log2 (2 * n) + 5 := by rw [hc]; omega
  have hmono : 2 ^ (3 * c + 2) ≤ 2 ^ (Nat.log2 (2 * n) + 5) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hpow5 : (2 : Nat) ^ 5 = 32 := by decide
  cases n with
  | zero =>
      simp [SuccinctClose.bpChunkSelectRowCount, SuccinctClose.bpFringeChunkBits, Nat.log2_zero]
  | succ m =>
      have hself : 2 ^ Nat.log2 (2 * (m + 1)) ≤ 2 * (m + 1) := Nat.log2_self_le (by omega)
      have hfactor : 2 ^ (Nat.log2 (2 * (m + 1)) + 5) = 32 * 2 ^ Nat.log2 (2 * (m + 1)) := by
        rw [Nat.pow_add, hpow5, Nat.mul_comm]
      rw [hfactor] at hmono
      have hscaled := Nat.mul_le_mul_left 32 hself
      show SuccinctClose.bpChunkSelectRowCount c * (c + 1) ≤ 64 * (m + 1 + 1)
      omega

/-- A halving `log2` loop on `x` takes at most `x + 1` rounds. -/
theorem log2_rounds_le (x : Nat) : Nat.log2 x + 1 ≤ x + 1 :=
  Nat.succ_le_succ (Nat.log2_le_self x)

end RMQ.SuccinctFinal.PackedConstruction.Spec

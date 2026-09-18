import RMQ.Core.WordRAM.Bitvector.CanonicalLimits
import RMQ.Core.WordRAM.Bitvector.NumericSafety
import RMQ.Core.WordRAM.Bitvector.ReaderInterface

/-! # Numerical bounds for the complete bitvector allocation

Counts are proved from the canonical builders, including the empty sentinel
words. They are not inferred from the serialized payload's bit length.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

private theorem table_words_size {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) : table.store.words.size = entries.length := by
  have heq : table.store.words.toList.map bitsToNatLE = entries := by
    apply List.ext_getElem?
    intro i
    simpa only [List.getElem?_map, Array.getElem?_toList] using table.read_exact i
  have hlen := congrArg List.length heq
  simpa using hlen

private theorem chunks_count (bits : List Bool) {width : Nat} (hw : 0 < width) :
    (chunkPayloadWords width bits).length ≤ bits.length + 1 := by
  rw [chunkPayloadWords_length_eq_div_add_indicator hw]
  have hd := Nat.div_le_self bits.length width
  split <;> omega

private theorem sentinel_count (bits : List Bool) {width : Nat} (hw : 0 < width) :
    (BoundedPayloadWordStore.ofChunksWithSentinel bits hw).store.words.size ≤
      2 * bits.length + 2 := by
  have hc := chunks_count bits hw
  simp only [BoundedPayloadWordStore.ofChunksWithSentinel, List.size_toArray,
    List.length_append, List.length_replicate]
  omega

private theorem localStride_le_wordBits (n : Nat) : localStride n ≤ wordBits n := by
  have hw := wordBits_pos n
  have hd := Nat.div_le_self (wordBits n) (ell n * ell n)
  unfold localStride
  omega

private theorem long_entries_count (bits : List Bool) (target : Bool) :
    (longSuperRelativeEntries bits target).length ≤ bits.length := by
  rw [longSuperRelativeEntries_length]
  have hspan : superStride bits.length ≤ superLongSpan bits.length := by
    unfold superLongSpan
    exact Nat.le_trans (Nat.le_mul_of_pos_right _ (wordBits_pos _))
      (Nat.le_mul_of_pos_right _ (ell_pos _))
  exact Nat.le_trans (Nat.mul_le_mul_left _ hspan)
    (longSuperExceptionCount_mul_superLongSpan_le_length bits target)

private theorem sparse_entries_count (bits : List Bool) (target : Bool) :
    (sparseExceptionRelativeEntries bits target).length ≤ bits.length := by
  rw [sparseExceptionRelativeEntries_length]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (localStride_le_wordBits _))
    (sparseExceptionCount_wordBits_le_length bits target)

private theorem long_rank_counts (bits : List Bool) (target : Bool) :
    (longFlagRankData bits target).superTables.trueTable.store.words.size ≤ bits.length + 1 ∧
    (longFlagRankData bits target).blockTables.trueTable.store.words.size ≤ bits.length + 1 ∧
    (longFlagRankData bits target).bitWords.store.words.size ≤ 2 * bits.length + 2 := by
  have hf := longSuperFlagBits_length_le_length bits target
  constructor
  · rw [table_words_size]
    change (canonicalSuperRankEntries true (longSuperFlagBits bits target)
      (longFlagRankWordSize bits target) (longFlagRankBlocksPerSuper bits target)).length ≤ _
    rw [canonicalSuperRankEntries_length]
    have h1 := Nat.div_le_self (longSuperFlagBits bits target).length
      (longFlagRankWordSize bits target)
    have h2 := Nat.div_le_self ((longSuperFlagBits bits target).length /
      longFlagRankWordSize bits target) (longFlagRankBlocksPerSuper bits target)
    omega
  constructor
  · rw [table_words_size]
    change (canonicalBlockRankEntries true (longSuperFlagBits bits target)
      (longFlagRankWordSize bits target) (longFlagRankBlocksPerSuper bits target)).length ≤ _
    rw [canonicalBlockRankEntries_length]
    have h1 := Nat.div_le_self (longSuperFlagBits bits target).length
      (longFlagRankWordSize bits target)
    omega
  · exact Nat.le_trans (sentinel_count _ (longFlagRankWordSize_pos bits target)) (by omega)

private theorem sparse_rank_counts (bits : List Bool) (target : Bool) :
    (sparseExceptionEffectiveFlagRankData bits target).superTables.trueTable.store.words.size ≤
      bits.length + 1 ∧
    (sparseExceptionEffectiveFlagRankData bits target).blockTables.trueTable.store.words.size ≤
      bits.length + 1 ∧
    (sparseExceptionEffectiveFlagRankData bits target).bitWords.store.words.size ≤
      2 * bits.length + 2 := by
  have hf := sparseExceptionEffectiveFlagBits_length_le_length bits target
  constructor
  · rw [table_words_size]
    change (canonicalSuperRankEntries true (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankWordSize bits target)
      (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)).length ≤ _
    rw [canonicalSuperRankEntries_length]
    have h1 := Nat.div_le_self (sparseExceptionEffectiveFlagBits bits target).length
      (sparseExceptionEffectiveFlagRankWordSize bits target)
    have h2 := Nat.div_le_self ((sparseExceptionEffectiveFlagBits bits target).length /
      sparseExceptionEffectiveFlagRankWordSize bits target)
      (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)
    omega
  constructor
  · rw [table_words_size]
    change (canonicalBlockRankEntries true (sparseExceptionEffectiveFlagBits bits target)
      (sparseExceptionEffectiveFlagRankWordSize bits target)
      (sparseExceptionEffectiveFlagRankBlocksPerSuper bits target)).length ≤ _
    rw [canonicalBlockRankEntries_length]
    have h1 := Nat.div_le_self (sparseExceptionEffectiveFlagBits bits target).length
      (sparseExceptionEffectiveFlagRankWordSize bits target)
    omega
  · exact Nat.le_trans (sentinel_count _
      (sparseExceptionEffectiveFlagRankWordSize_pos bits target)) (by omega)

theorem canonical_directory_count (bits : List Bool) (target : Bool)
    (words : Array (List Bool))
    (hm : words ∈ Experiment.directorySegments (sparseExceptionSelectData bits target)) :
    words.size ≤ 10 * bits.length + 2 := by
  have hs : (superEntries bits target).length ≤ bits.length := by
    simpa [superEntries_length, longSuperFlagBits_length] using
      longSuperFlagBits_length_le_length bits target
  have hl : (localEntries bits target).length ≤ 10 * bits.length := by
    rw [localEntries_length]
    exact Nat.le_trans (Nat.le_mul_of_pos_right _ (localStride_pos _))
      (localSlotCount_mul_localStride_le_const_length bits target)
  have hlong := long_rank_counts bits target
  have hsparse := sparse_rank_counts bits target
  have hlongEntries := long_entries_count bits target
  have hsparseEntries := sparse_entries_count bits target
  simp only [Experiment.directorySegments, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (rw [table_words_size];
       change List.length _ ≤ _;
       simp only [sparseExceptionSelectData, sparseExceptionDirectory,
         SparseDenseSelectDenseLocalEntry.baseOccurrences,
         SparseDenseSelectDenseLocalEntry.baseWordIndices,
         SparseDenseSelectDenseLocalEntry.ranksBefore,
         SparseDenseSelectDenseLocalEntry.firstOffsets, List.length_map];
       omega)
    | (change (longFlagRankData bits target).bitWords.store.words.size ≤ _; omega)
    | (change (sparseExceptionEffectiveFlagRankData bits target).bitWords.store.words.size ≤ _; omega)
    | (change (longFlagRankData bits target).superTables.trueTable.store.words.size ≤ _; omega)
    | (change (longFlagRankData bits target).blockTables.trueTable.store.words.size ≤ _; omega)
    | (change (sparseExceptionEffectiveFlagRankData bits target).superTables.trueTable.store.words.size ≤ _; omega)
    | (change (sparseExceptionEffectiveFlagRankData bits target).blockTables.trueTable.store.words.size ≤ _; omega)

/-- All thirty-nine physical arrays have bounded counts, even when rows are empty. -/
theorem canonical_allSegments_count (bits : List Bool) (words : Array (List Bool))
    (hm : words ∈ Allocation.allSegments bits) : words.size ≤ 64 * (bits.length + 1) := by
  rcases List.mem_append.mp hm with hm | hm
  · simp only [Experiment.allSegments, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with ((rfl | hm) | hm) | (rfl | rfl)
    · have hc := chunks_count bits (wordBits_pos bits.length)
      change (chunkPayloadWords (wordBits bits.length) bits).toArray.size ≤ _
      simpa only [List.size_toArray] using Nat.le_trans hc (by omega)
    · exact Nat.le_trans (canonical_directory_count bits false words hm) (by omega)
    · exact Nat.le_trans (canonical_directory_count bits true words hm) (by omega)
    · rw [table_words_size]
      simpa [SuccinctClose.bpFringeChunkTable] using
        SuccinctClose.bpFringeChunkRowCount_le_linear bits.length
    · rw [table_words_size]
      have hb := SuccinctClose.bpChunkSelectRowCount_le_linear bits.length
      rw [SuccinctClose.bpChunkSelectEntries_length]
      omega
  · exact Nat.le_trans (jacobson_samples_count_le bits words hm) (by omega)

private theorem machine_le_pow (n : Nat) : machineWordBits n ≤ 2 ^ machineWordBits n :=
  Nat.le_of_lt (Nat.lt_two_pow_self (n := machineWordBits n))

private theorem width_le_pow_scale (n : Nat) :
    Experiment.width n ≤ 64 * 2 ^ machineWordBits n := by
  have hm := machine_le_pow n
  have hp := Nat.two_pow_pos (machineWordBits n)
  unfold Experiment.width
  omega

theorem canonical_size_le_envelope (n : Nat) : n ≤ canonicalEnvelope n := by
  have hn := self_lt_two_pow_machineWordBits n
  have hp : 2 ^ machineWordBits n ≤ 2 ^ (9 + 2 * machineWordBits n) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold canonicalEnvelope
  omega

theorem canonical_machine_le_envelope (n : Nat) :
    machineWordBits n ≤ canonicalEnvelope n := by
  exact Nat.le_trans (machine_le_pow n)
    (Nat.pow_le_pow_right (by decide) (by omega))

theorem canonical_width_le_envelope (n : Nat) : Experiment.width n ≤ canonicalEnvelope n := by
  have hp : 2 ^ (6 + machineWordBits n) ≤ 2 ^ (9 + 2 * machineWordBits n) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hw := width_le_pow_scale n
  rw [Nat.pow_add] at hp
  exact Nat.le_trans hw hp

private theorem square_machine_le_envelope (n : Nat) :
    machineWordBits n * machineWordBits n ≤ canonicalEnvelope n := by
  have hm := Nat.mul_le_mul (machine_le_pow n) (machine_le_pow n)
  have hp : 2 ^ (machineWordBits n + machineWordBits n) ≤
      2 ^ (9 + 2 * machineWordBits n) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_add] at hp
  exact Nat.le_trans hm hp

private theorem flagScalars_bound (bits : List Bool) (target : Bool) (value : Nat)
    (hv : value ∈ Experiment.flagScalars (sparseExceptionSelectData bits target)) :
    value ≤ canonicalEnvelope bits.length := by
  have hl := longSuperFlagBits_length_le_length bits target
  have hs := sparseExceptionEffectiveFlagBits_length_le_length bits target
  have hwl := (sparseExceptionSelectData bits target).longFlagRank_wordSize_le_machine
  have hws := (sparseExceptionSelectData bits target).sparseDirectory.rank_wordSize_le_machine
  have hn := canonical_size_le_envelope bits.length
  have hw := canonical_machine_le_envelope bits.length
  simp only [Experiment.flagScalars, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact Nat.le_trans hl hn
  · exact Nat.le_trans hs hn
  · exact Nat.le_trans hwl hw
  · exact Nat.le_trans hws hw

/-- Every scalar word in the exact shared header satisfies the controller envelope. -/
theorem canonical_scalarHeader_bound (bits : List Bool) (value : Nat)
    (hv : value ∈ Allocation.scalarHeader bits) : value ≤ canonicalEnvelope bits.length := by
  have hn := canonical_size_le_envelope bits.length
  have hw := canonical_machine_le_envelope bits.length
  have hwidth := canonical_width_le_envelope bits.length
  have hsquare := square_machine_le_envelope bits.length
  have hf := occurrenceCount_le_length bits false
  have ht := occurrenceCount_le_length bits true
  have hlocal := localStride_le_wordBits bits.length
  have hslots : localSlotsPerSuper bits.length ≤ superStride bits.length :=
    selectLocalSlotsPerSuper_le_superStride (superStride_pos _) (localStride_pos _)
  have hchunk := chunkBits_le_machine bits.length
  simp only [Allocation.scalarHeader, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · simp only [jacobson_wordSize_eq, jacobson_blocksPerSuper_eq,
      sparseExceptionSelectData, superStride, wordBits] at hv hlocal hslots
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> omega
  · exact flagScalars_bound bits false value hv
  · rcases hv with rfl | rfl | rfl
    · exact hw
    · omega
    · omega
  · exact flagScalars_bound bits true value hv

private theorem flatten_length_bound (words : List (List Bool)) (width : Nat)
    (hb : ∀ word ∈ words, word.length ≤ width) :
    words.flatten.length ≤ words.length * width := by
  induction words with
  | nil => simp
  | cons word rest ih =>
    have hh := hb word (by simp)
    have ht := ih (fun word hm => hb word (by simp [hm]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

private theorem flatMap_length_bound (segments : List (Array (List Bool))) (bound : Nat)
    (hb : ∀ words ∈ segments, (Experiment.segmentBits words).length ≤ bound) :
    (segments.flatMap Experiment.segmentBits).length ≤ segments.length * bound := by
  induction segments with
  | nil => simp
  | cons words rest ih =>
    have hh := hb words (by simp)
    have ht := ih (fun word hm => hb word (by simp [hm]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

theorem canonical_body_length (bits : List Bool) :
    (Allocation.body bits).length ≤ 2496 * (bits.length + 1) * Experiment.width bits.length := by
  have h := flatMap_length_bound (Allocation.allSegments bits)
    (64 * (bits.length + 1) * Experiment.width bits.length) (by
      intro words hm
      have hw := flatten_length_bound words.toList (Experiment.width bits.length)
        (fun word hw => Nat.le_of_lt (Allocation.allSegments_word_length_lt bits words hm word hw))
      have hc := Nat.mul_le_mul_right (Experiment.width bits.length)
        (canonical_allSegments_count bits words hm)
      exact Nat.le_trans (by simpa only [Experiment.segmentBits, Array.length_toList] using hw) hc)
  simpa only [Allocation.allSegments_length, Nat.mul_assoc,
    show 2496 = 39 * 64 from rfl] using h

/-- A proof-side bound for all fields and computed positions, including sentinel requests. -/
def canonicalAddressBound (n : Nat) : Nat := (207 + 2560 * (n + 1)) * Experiment.width n

theorem canonicalAddressBound_lt_capacity (n : Nat) :
    canonicalAddressBound n < 2 ^ Experiment.width n := by
  have hn : n + 1 ≤ 2 ^ machineWordBits n := self_lt_two_pow_machineWordBits n
  have hp := Nat.two_pow_pos (machineWordBits n)
  have hfactor : 207 + 2560 * (n + 1) ≤ 4096 * 2 ^ machineWordBits n := by omega
  have hw := width_le_pow_scale n
  have hmul := Nat.mul_le_mul hfactor hw
  have heq : (4096 * 2 ^ machineWordBits n) * (64 * 2 ^ machineWordBits n) =
      2 ^ (18 + 2 * machineWordBits n) := by
    rw [show 18 + 2 * machineWordBits n = (12 + machineWordBits n) +
      (6 + machineWordBits n) by omega, Nat.pow_add]
    simp only [Nat.pow_add, Nat.reducePow]
  have hlt : 2 ^ (18 + 2 * machineWordBits n) < 2 ^ Experiment.width n :=
    Nat.pow_lt_pow_right (by decide) (by unfold Experiment.width; omega)
  rw [heq] at hmul
  exact Nat.lt_of_le_of_lt hmul hlt

private theorem component_lengths (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : Allocation.activeSegment segment) :
    Experiment.componentOffset (Allocation.allSegments bits)
      (Allocation.physicalComponent target segment) ≤ (Allocation.body bits).length ∧
    (Experiment.segmentBits (Allocation.logicalWords bits target segment)).length ≤
      (Allocation.body bits).length := by
  have heq := congrArg List.length (Experiment.components_decompose
    (Allocation.allSegments bits) (Allocation.physicalComponent target segment)
    (by simpa using Allocation.physicalComponent_lt target segment))
  rw [Allocation.logicalWords_view bits target segment hs]
  simp only [List.length_append] at heq
  unfold Experiment.componentOffset Allocation.body
  constructor <;> omega

theorem canonical_logicalWords_count (bits : List Bool) (target : Bool) (segment : Nat)
    (hs : Allocation.activeSegment segment) :
    (Allocation.logicalWords bits target segment).size ≤ 64 * (bits.length + 1) := by
  by_cases hraw : segment = 19
  · subst segment
    rw [Allocation.logicalWords_raw]
    exact Nat.le_trans (jacobson_raw_count_le bits) (by omega)
  · rw [Allocation.logicalWords_component bits target segment hs hraw]
    exact canonical_allSegments_count bits _ (List.getElem_mem _)

private theorem active_position_bound (bits : List Bool) (target : Bool) (segment index : Nat)
    (hs : Allocation.activeSegment segment)
    (hi : index < (Allocation.logicalWords bits target segment).size) :
    207 * Experiment.width bits.length +
      Experiment.componentOffset (Allocation.allSegments bits)
        (Allocation.physicalComponent target segment) +
      index * firstLength (Allocation.logicalWords bits target segment) ≤
        canonicalAddressBound bits.length := by
  have hoff := (component_lengths bits target segment hs).1
  have hbody := canonical_body_length bits
  have hc := canonical_logicalWords_count bits target segment hs
  have hw := Allocation.logicalWords_firstLength_lt bits target segment hs
  have hmul := Nat.mul_le_mul (by omega : index ≤ 64 * (bits.length + 1)) (Nat.le_of_lt hw)
  unfold canonicalAddressBound
  simp only [Nat.add_mul, Nat.mul_assoc] at hbody hmul ⊢
  omega

private theorem addressBound_basic (bits : List Bool) :
    207 * Experiment.width bits.length + (Allocation.body bits).length ≤ canonicalAddressBound bits.length ∧
    Experiment.width bits.length ≤ canonicalAddressBound bits.length ∧
    64 * (bits.length + 1) ≤ canonicalAddressBound bits.length := by
  have hb := canonical_body_length bits
  have hw := width_floor bits.length
  have hc : 64 * (bits.length + 1) ≤ 64 * (bits.length + 1) * Experiment.width bits.length :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold canonicalAddressBound
  simp only [Nat.add_mul, Nat.mul_assoc] at hb hc ⊢
  omega

theorem canonical_bankDescriptor_bound (bits : List Bool) (target : Bool) (segment value : Nat)
    (hs : segment < 23) (hv : value ∈ Allocation.bankDescriptor bits target segment) :
    value ≤ canonicalAddressBound bits.length := by
  by_cases hinactive : segment = 20
  · subst segment
    rw [Allocation.bankDescriptor_eq_selected bits target 20 (by decide)] at hv
    simp [Allocation.selectedDescriptor] at hv
    subst value
    omega
  · have ha : Allocation.activeSegment segment := ⟨hs, hinactive⟩
    rw [Allocation.bankDescriptor_active bits target segment ha] at hv
    have hlength := component_lengths bits target segment ha
    have hfirst := Allocation.logicalWords_firstLength_lt bits target segment ha
    have hcount := canonical_logicalWords_count bits target segment ha
    have hb := addressBound_basic bits
    simp only [Experiment.descriptor, List.mem_cons, List.not_mem_nil, or_false] at hv
    change value = _ ∨ value = _ ∨ value = firstLength _ ∨ value = _ at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega

theorem canonical_memoryWordsFit (bits : List Bool) :
    MemoryWordsFit (Allocation.memory bits) (Experiment.width bits.length) := by
  have bankFit : ∀ (target : Bool) value,
      value ∈ (Allocation.descriptorBank bits target).flatten →
      value < 2 ^ Experiment.width bits.length := by
    intro target value hv
    obtain ⟨entry, he, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨index, hi, hentry⟩ := List.mem_iff_getElem.mp he
    have hs : index < 23 := by simpa using hi
    have hbank : entry = Allocation.bankDescriptor bits target index := by
      simp only [Allocation.bankDescriptor, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hentry.symm
    rw [hbank] at hv
    exact Nat.lt_of_le_of_lt (canonical_bankDescriptor_bound bits target index value hs hv)
      (canonicalAddressBound_lt_capacity bits.length)
  intro value hv
  rcases List.mem_append.mp hv with hv | hv
  · simp only [Allocation.header, List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact Nat.lt_of_le_of_lt (canonical_scalarHeader_bound bits value hv)
        (Controller.SafetyLimits.envelope_lt_capacity (canonicalLimits bits.length))
    · exact bankFit false value hv
    · exact bankFit true value hv
  · exact denseWords_word_lt _ _ (width_pos bits.length) hv

theorem canonical_numericReaderGeometry (bits : List Bool) (target : Bool) (regs : Registers)
    (hm : GenericReaderMetadata bits target regs) :
    NumericReaderGeometry (Allocation.memory bits) (Experiment.width bits.length) regs := by
  have haddr : numericDescriptorAddress regs = 23 + target.toNat * 92 + regs 8192 * 4 := by
    simp only [numericDescriptorAddress, hm.1]
  constructor
  · intro hs
    apply fixed_floor_capacity bits.length
    rw [haddr]
    cases target <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · intro hs bitBase bitLength stride count hbase hlength hstride hcount hindex
    rw [haddr] at hbase hlength hstride hcount
    have h0 := Allocation.memory_descriptor_field bits target (regs 8192) 0 hs (by decide)
    simp only [Nat.add_zero] at h0
    rw [h0] at hbase
    rw [Allocation.memory_descriptor_field bits target (regs 8192) 1 hs (by decide)] at hlength
    rw [Allocation.memory_descriptor_field bits target (regs 8192) 2 hs (by decide)] at hstride
    rw [Allocation.memory_descriptor_field bits target (regs 8192) 3 hs (by decide)] at hcount
    by_cases hinactive : regs 8192 = 20
    · rw [hinactive, Allocation.bankDescriptor_eq_selected bits target 20 (by decide)] at hcount
      simp [Allocation.selectedDescriptor] at hcount
      omega
    · have ha : Allocation.activeSegment (regs 8192) := ⟨hs, hinactive⟩
      rw [Allocation.bankDescriptor_active bits target (regs 8192) ha] at hbase hlength hstride hcount
      simp only [Experiment.descriptor, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.some.injEq] at hbase hlength hstride hcount
      subst bitBase
      subst bitLength
      subst stride
      subst count
      exact ⟨Nat.lt_of_le_of_lt (active_position_bound bits target (regs 8192) (regs 8193) ha hindex)
        (canonicalAddressBound_lt_capacity bits.length),
        Allocation.logicalWords_firstLength_lt bits target (regs 8192) ha⟩

/-- A positive logical count survives even when the entire raw payload is empty. -/
theorem canonical_empty_raw_sentinel (target : Bool) :
    (Allocation.logicalWords [] target 19).size = 1 ∧
    (Allocation.logicalWords [] target 19)[0]? = some [] := by
  simp only [Allocation.logicalWords_raw, jacobson_raw_words_eq]
  simp [BoundedPayloadWordStore.ofChunksWithSentinel, chunkPayloadWords, chunkPayloadWordsFuel]

/-- Independently expanded consumer of the actual numerical allocation. -/
theorem canonical_memoryWordsFit_expectedType (bits : List Bool) :
    ∀ value ∈ Allocation.memory bits, value < 2 ^ Experiment.width bits.length :=
  canonical_memoryWordsFit bits

/-- The expected geometry type retains all four actual descriptor lookups. -/
theorem canonical_numericReaderGeometry_expectedType (bits : List Bool) (target : Bool)
    (regs : Registers) (htarget : regs 3 = target.toNat)
    (hwidth : regs 22 = Experiment.width bits.length) :
    (regs 8192 < 23 → 23 + regs 3 * 92 + regs 8192 * 4 + 3 <
      2 ^ Experiment.width bits.length) ∧
    (regs 8192 < 23 → ∀ bitBase bitLength stride count,
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4]? = some bitBase →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 1]? = some bitLength →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 2]? = some stride →
      (Allocation.memory bits)[23 + regs 3 * 92 + regs 8192 * 4 + 3]? = some count →
      regs 8193 < count →
      bitBase + regs 8193 * stride < 2 ^ Experiment.width bits.length ∧
      stride < Experiment.width bits.length) :=
  canonical_numericReaderGeometry bits target regs ⟨htarget, hwidth⟩

theorem canonical_scalarHeader_bound_expectedType (bits : List Bool) :
    ∀ value ∈ Allocation.scalarHeader bits,
      value ≤ 2 ^ (9 + 2 * machineWordBits bits.length) :=
  canonical_scalarHeader_bound bits

end RMQ.PackedBitvector
